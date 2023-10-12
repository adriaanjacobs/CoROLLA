#include "pass.h"
#include <util.h>
#include <reachability/reachingdefinitions.h>

#include <llvm/IR/Constants.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Operator.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/ADT/STLExtras.h>
#include <llvm/ADT/StringRef.h>

#include <numeric>
#include <optional>

#include <Util/ExtAPI.h>

std::optional<decltype(AllocWrapperDetector::builtinLibcCallToBounds)::value_type::second_type> AllocWrapperDetector::isKnownLibcAllocator(llvm::Function* func) {
    auto it = builtinLibcCallToBounds.find(func->getName());
    if (it != builtinLibcCallToBounds.end() && func->isDeclaration())
        return it->getSecond();
    if (func->isDeclaration() && func->hasFnAttribute(llvm::Attribute::NoAlias)) {
        llvm::outs() << "We should get to know '" << func->getName() << "'!\n";
        assert(!"Add it to the list of known allocation funcs!");
    }

    return std::nullopt;
}

bool AllocWrapperDetector::isWrapperOrLibcCall(llvm::Value* val) {
    if (auto callInst = llvm::dyn_cast<llvm::CallBase>(val)) {
        auto calledFunc = callInst->getCalledFunction();
        return calledFunc && allocFuncs.count(calledFunc);
    }
    return false;
}

bool AllocWrapperDetector::isAllocationSite(llvm::Value* val) {
    return llvm::isa<llvm::AllocaInst, llvm::GlobalVariable>(val) || isWrapperOrLibcCall(val);
}

bool AllocWrapperDetector::isNonWrapperAllocSite(llvm::Value* val) {
    if (auto callInst = llvm::dyn_cast<llvm::CallBase>(val)) {
        auto calledFunc = callInst->getCalledFunction();
        return calledFunc && isKnownLibcAllocator(calledFunc);
    }
    return llvm::isa<llvm::AllocaInst, llvm::GlobalVariable>(val);
}

llvm::StringRef AllocWrapperDetector::getValueDescription(llvm::Value* val) {
    if (isNonWrapperAllocSite(val)) {
        return "allocation site";
    } else if (auto inst = llvm::dyn_cast<llvm::Instruction>(val)) {
        return inst->getOpcodeName();
    } else if (auto arg = llvm::dyn_cast<llvm::Argument>(val)) {
        return "function argument";
    } else if (llvm::isa<llvm::ConstantPointerNull, llvm::ConstantInt>(val)) {
        return "constant pointer value";
    } else if (llvm::isa<llvm::UndefValue>(val)) {
        return "undef value";
    } else HANDLE_UNKOWN_VALUE(val);
}

std::optional<std::pair<llvm::APInt, llvm::APInt>> AllocWrapperDetector::findMinimumAllocBounds(llvm::Value* allocInstr) {
    ASSERT_ELSE_UNKOWN(isNonWrapperAllocSite(allocInstr), allocInstr);
    auto& dataLayout = module.getDataLayout();
    if (auto allocaInstr = llvm::dyn_cast<llvm::AllocaInst>(allocInstr)) {
        auto size = dataLayout.getTypeAllocSize(allocaInstr->getAllocatedType());
        ASSERT_ELSE_UNKOWN(size >= 0, allocInstr); // gcc's `combine_givs` does `alloca(0)` and LLVM is happy with it
        return std::pair{llvm::APInt{64, 0}, llvm::APInt{64, size, true}};
    } else if (auto globalVariable = llvm::dyn_cast<llvm::GlobalVariable>(allocInstr)) {
        auto size = dataLayout.getTypeAllocSize(globalVariable->getType()->getPointerElementType());
        ASSERT_ELSE_UNKOWN(size > 0, allocInstr);
        return std::pair{llvm::APInt{64, 0}, llvm::APInt{64, size, true}};
    } else if (auto callInst = llvm::dyn_cast<llvm::CallBase>(allocInstr)) {
        auto calledFunc = callInst->getCalledFunction();
        assert(calledFunc);
        if (auto it = isKnownLibcAllocator(calledFunc)) {
            if (it.value()) {
                return it.value()(this, callInst);
            } else HANDLE_UNKOWN_VALUE(callInst);
        } else {
            // custom allocation wrapper. we shouldnt need this case if we do good callbase transparancy in isInBounds
            return std::nullopt;
            HANDLE_UNKOWN_VALUE(callInst);
        }
    } else HANDLE_UNKOWN_VALUE(allocInstr);
}

// probably add an argument here that gets filled with the found allocationsites
AllocWrapperDetector::AllocSiteStatus AllocWrapperDetector::reducesToAllocationSite(llvm::Value* val, llvm::DenseSet<llvm::Value*>& allocSites) {
    static thread_local std::vector<const llvm::Value*> passedInstrs;
    const auto size = passedInstrs.size();
    // llvm::outs() << rand() << ": Called findoffset (nested level: " << size << ")\n";
    run_on_destruct resetPassedInstrs([&](){
        assert(size <= passedInstrs.size());
        passedInstrs.erase(passedInstrs.begin() + size, passedInstrs.end());
        assert(passedInstrs.size() == size);
    });

    using enum AllocSiteStatus;

    auto& pointerDetector = MAM.getResult<PointerDetectionAnalysis>(module);
    auto& rds = MAM.getResult<ReachingDefinitionsAnalysis>(module);
    if (pointerDetector.is_confirmed_pointer(val)) {
        val = pointerDetector.strip_pointer_casts(val);
        if (isWrapperOrLibcCall(val)) {
            allocSites.insert(val);
            return ALLOCSITE;
        } else if (auto global = llvm::dyn_cast<llvm::GlobalVariable>(val)) {
            allocSites.insert(val);
            return NULLPTR;
        } else if (auto phiNode = llvm::dyn_cast<llvm::PHINode>(val)) {
            assert(!phiNode->incoming_values().empty());

            bool atLeastOneAllocationSite = false;
            for (auto& incomingUse : phiNode->incoming_values()) {
                auto incomingVal = incomingUse.get();
                if (llvm::is_contained(passedInstrs, incomingVal))
                    return NONE;
                passedInstrs.push_back(incomingVal);
                auto status = reducesToAllocationSite(incomingVal, allocSites);
                if (status == NONE)
                    return NONE;
                if (status == ALLOCSITE)
                    atLeastOneAllocationSite = true;
            }

            return atLeastOneAllocationSite ? ALLOCSITE : NULLPTR;
        } else if (auto selectInst = llvm::dyn_cast<llvm::SelectInst>(val)) {
            auto left = reducesToAllocationSite(selectInst->getTrueValue(), allocSites);
            if (left == NONE)
                return NONE;
            auto right = reducesToAllocationSite(selectInst->getFalseValue(), allocSites);
            if (right == NONE)
                return NONE;
            if (left == ALLOCSITE || right == ALLOCSITE)
                return ALLOCSITE;
            assert(left == NULLPTR && right == NULLPTR);
            return NULLPTR;
        } else if (auto call = llvm::dyn_cast<llvm::CallBase>(val)) {
            // this does not call an allocation function (or one that we haven't identified yet)
            return NONE;
        } else if (llvm::isa<llvm::GEPOperator, llvm::BinaryOperator, llvm::Argument>(val)) {
            // this arithmetic definitely has a non-zero offset because strip_pointer_casts checks for that.
            // non-zero offsets are probably pool allocators, yeet dat
            return NONE;
        } else if (auto load = llvm::dyn_cast<llvm::LoadInst>(val)) {
            if (auto defPtr = rds.findDefForLoad(load))
                return reducesToAllocationSite(defPtr, allocSites);
            return NONE;
        } else if (llvm::isa<llvm::ConstantPointerNull>(val)) {
            return NULLPTR;
        } else HANDLE_UNKOWN_VALUE(val);
    } else if (llvm::isa<llvm::ConstantPointerNull>(val)) {
        return NULLPTR;
    } else if (auto constInt = llvm::dyn_cast<llvm::ConstantInt>(val)) {
        auto intval = constInt->getValue();
        if (intval.isNullValue() || intval == -1)
            return NULLPTR;
        return NONE;
    } else return NONE;
    assert(!"Unreachable!");
}

std::optional<SVF::ExtAPI::extType> AllocWrapperDetector::deriveExtFnTy(llvm::Value* val) {
    using enum SVF::ExtAPI::extType;
    // should not construct the extAPI
    auto extAPI = SVF::ExtAPI::getExtAPI();

    if (auto func = llvm::dyn_cast<llvm::Function>(val)) {
        if (AllocWrapperDetector::isKnownLibcAllocator(func)) {
            auto type = extAPI->get_type(func->getName().str());
            assert(type != EFT_NULL);
            return type;
        } else {
            assert(!func->isDeclaration());
            auto it = allocFuncs.find(func);
            assert(it != allocFuncs.end());
            auto& containedAllocSites = it->getSecond().allocSites;
            assert(!containedAllocSites.empty());

            SVF::ExtAPI::extType accumulated = EFT_NULL;
            
            for (auto allocSite : containedAllocSites) {
                auto fnTy = deriveExtFnTy(allocSite);
                if (!fnTy.has_value())
                    return std::nullopt;
                assert(fnTy != EFT_NULL && fnTy != EFT_NOOP);
                if (accumulated == EFT_NULL)
                    accumulated = fnTy.value();
                else if (accumulated != fnTy) {
                    if (fnTy == EFT_REALLOC && (accumulated == EFT_ALLOC || accumulated == EFT_NOSTRUCT_ALLOC))
                        accumulated = EFT_REALLOC;
                    else if (accumulated == EFT_REALLOC && (fnTy == EFT_ALLOC || fnTy == EFT_NOSTRUCT_ALLOC)) {
                        // realloc wins
                    } else if ((accumulated == EFT_STAT || accumulated == EFT_STAT2) && (fnTy == EFT_ALLOC || fnTy == EFT_NOSTRUCT_ALLOC)) {
                        return std::nullopt; // dont know how to resolve this, it's just an alias
                    } else if ((fnTy == EFT_STAT || fnTy == EFT_STAT2) && (accumulated == EFT_ALLOC || accumulated == EFT_NOSTRUCT_ALLOC)) {
                        return std::nullopt;
                    } else {
                        llvm::outs() << "In wrapper '" << func->getName() << "':\n";
                        llvm::outs() << "accumulated: " << extAPI->extType_toString(accumulated) << "\n";
                        llvm::outs() << "fnTy: " << extAPI->extType_toString(fnTy.value()) << "\n";
                        HANDLE_UNKOWN_VALUE(allocSite);
                    }
                }
            }
            return accumulated;
        }
    } else if (auto global = llvm::dyn_cast<llvm::GlobalVariable>(val)) {
        auto& pointerDetector = MAM.getResult<PointerDetectionAnalysis>(module);

        bool hasLoad = false;
        bool hasStore = false;
        bool allPointers = llvm::all_of(global->uses(), [&](llvm::Use& use) {
            if (auto load = llvm::dyn_cast<llvm::LoadInst>(use.getUser())) {
                hasLoad= true;
                return pointerDetector.is_confirmed_pointer(load);
            } else if (auto store = llvm::dyn_cast<llvm::StoreInst>(use.getUser())) {
                hasStore = true;
                return pointerDetector.is_confirmed_pointer(store->getValueOperand());
            } else return false;
        });

        if (hasLoad && hasStore && allPointers)
            return EFT_STAT2;
        else return EFT_STAT;
    } else if (auto call = llvm::dyn_cast<llvm::CallBase>(val)) {
        auto func = call->getCalledFunction();
        assert(func);
        return deriveExtFnTy(func);
    } else HANDLE_UNKOWN_VALUE(val);
}

AllocWrapperDetector::Detector(llvm::Module& module, llvm::ModuleAnalysisManager& MAM) :
    module{module}, MAM{MAM}, pointerDetector{MAM.getResult<PointerDetectionAnalysis>(module)}
{
    auto& dataLayout = module.getDataLayout();
    auto& context = module.getContext();
    auto& FAM = getFAM(module, MAM);

    for (auto& func : module)
        if (isKnownLibcAllocator(&func))
            allocFuncs[&func] = {}; // allocSites can be empty for built-in functions

#if 1
    if (allocFuncs.size() == 0) {
        llvm::outs() << "In this module, no known allocation functions are visibly called. Probably not all libraries are instrumented!\n";
    } else {
        size_t amountOfWrappers = 0;
        assert(allocFuncs.size() != 0);
        auto& pointerDetector = MAM.getResult<PointerDetectionAnalysis>(module);
        auto& dataLayout = module.getDataLayout();

        while (amountOfWrappers != allocFuncs.size()) {
            amountOfWrappers = allocFuncs.size();

            for (auto& potWrapper : module) {
                auto retType = potWrapper.getReturnType();
                if (retType != llvm::Type::getVoidTy(context) && dataLayout.getTypeSizeInBits(retType) == 64 && allocFuncs.find(&potWrapper) == allocFuncs.end()) {

                    bool hasWeirdSideEffects = [&] {
                        for (auto& bb : potWrapper) {
                            for (auto& inst : bb) {
                                bool instHasWeirdSideEffects = [&] () -> bool {
                                    if (auto call = llvm::dyn_cast<llvm::CallBase>(&inst)) {
                                        auto calledFunc = call->getCalledFunction();
                                        // check if this function has side-effects that SVF should model!
                                        if (!calledFunc)
                                            return true;

                                        if (calledFunc->doesNotReturn())
                                            return false;

                                        if (calledFunc->onlyReadsMemory())
                                            return false;

                                        if (allocFuncs.count(calledFunc))
                                            return false;

                                        if (calledFunc->isDeclaration()) {
                                            auto extAPI = SVF::ExtAPI::getExtAPI();
                                            auto name = calledFunc->getName().str();
                                            auto type = extAPI->get_type(name);
                                            switch (type) {
                                                case EFT_NULL:
                                                case EFT_NOOP:
                                                case EFT_ALLOC:
                                                case EFT_NOSTRUCT_ALLOC:
                                                case EFT_REALLOC:
                                                case EFT_STAT:
                                                case EFT_STAT2:
                                                    return false;
                                                default:
                                                    return true;
                                            }
                                        } else return true;
                                    } else if (auto store = llvm::dyn_cast<llvm::StoreInst>(&inst)) {
                                        auto storedVal = store->getValueOperand();
                                        // TODO: extend this with a small escape analysis to see if 
                                        // SVF will actually see effects from this
                                        if (pointerDetector.is_confirmed_pointer(storedVal) || storedVal->getType()->isPointerTy()) {
                                            if (llvm::isa<llvm::ConstantData>(storedVal))
                                                return false;
                                            return true; // this is information SVF should have!
                                        }
                                        return false;
                                    } else return false;
                                } ();

                                if (instHasWeirdSideEffects)
                                    return true;
                            }
                        }
                        return false;
                    } ();

                    if (hasWeirdSideEffects)
                        continue;

                    llvm::DenseSet<llvm::Value*> retvals;
                    for (auto& bb : potWrapper) {
                        auto terminator = bb.getTerminator();
                        if (auto returnInst = llvm::dyn_cast<llvm::ReturnInst>(terminator)) {
                            assert(returnInst->getReturnValue());
                            retvals.insert(returnInst->getReturnValue());
                        }
                    }

                    bool allOK = true;
                    bool atLeastOneAllocationSite = false;
                    llvm::DenseSet<llvm::Value*> allAllocSitesInWrapper;
                    for (auto retval : retvals) {
                        llvm::DenseSet<llvm::Value*> allocSites;
                        auto status = reducesToAllocationSite(retval, allocSites);
                        if (status == AllocSiteStatus::ALLOCSITE) {
                            atLeastOneAllocationSite = true;
                            assert(!allocSites.empty());
                            allAllocSitesInWrapper.insert(allocSites.begin(), allocSites.end());
                        } else if (status == AllocSiteStatus::NONE) {
                            allOK = false;
                            break;
                        } else assert(status == AllocSiteStatus::NULLPTR);
                    }

                    auto& callSiteInfo = pointerDetector.getCallSiteInfo(&potWrapper);
                    if (allOK && atLeastOneAllocationSite && !retvals.empty() && callSiteInfo.isOnlyDirectlyCalled()) {
                        assert(!allocFuncs.count(&potWrapper));
                        allocFuncs[&potWrapper].allocSites = allAllocSitesInWrapper;
                    }
                }
            }
        }

        llvm::DenseSet<llvm::Function*> wrappersToRemove;
        for (auto& [wrapper, wrapperInfo] : allocFuncs) {
            auto extFnTy = deriveExtFnTy(wrapper);
            if (extFnTy.has_value())
                wrapperInfo.type = extFnTy.value();
            else wrappersToRemove.insert(wrapper);
        }
        for (auto wrapper : wrappersToRemove)
            allocFuncs.erase(wrapper);

        llvm::outs() << "We found " << allocFuncs.size() << " allocation functions in this module: \n";
        for (const auto& [func, _] : allocFuncs) {
            llvm::outs() << "\t'" << func->getName() << "'\n";
        }

        llvm::outs() << "Here are all functions whose name contains alloc/new that we didn't identify: \n";
        for (auto& func : module) {
            if ((func.getName().contains_insensitive("alloc") || func.getName().contains_insensitive("new")) && !allocFuncs.count(&func)) {
                llvm::outs() << "\t'" <<  func.getName() << "'\n";
                // allocFuncs.insert(&func);
            }
        }

        llvm::outs() << "Here are all functions that return 'noalias' that we didn't identify: \n";
        for (auto& func : module) {
            if (!allocFuncs.count(&func) && func.hasRetAttribute(llvm::Attribute::NoAlias))
                llvm::outs() << "\t'" << func.getName() << "'\n";
        }
    }
#endif
}

/* 
    TODO: Also handle pool allocators etc that do not directly return the result of malloc()
    Also, this only identifies allocators that _return_ allocated memory, output arguments are not currently considered 
    Cling detects allocation wrappers at run time. DynPTA & TAT at compile time (but inlines them)
*/
AllocWrapperAnalysis::Result AllocWrapperAnalysis::run(llvm::Module& module, llvm::ModuleAnalysisManager& MAM) {
    return AllocWrapperDetector{module, MAM};
}

llvm::AnalysisKey AllocWrapperAnalysis::Key;

std::pair<llvm::APInt, llvm::APInt> AllocWrapperDetector::findMmapBounds(llvm::CallBase* callInst) { // redis calls this
    return {llvm::APInt{64, 0}, pointerDetector.findMinimumUnsignedValue(callInst->getArgOperand(1), callInst->getFunction())};
}

std::pair<llvm::APInt, llvm::APInt> AllocWrapperDetector::boundsOfReturnedPointeeType(llvm::CallBase* call) {
    auto size = module.getDataLayout().getTypeAllocSize(call->getCalledFunction()->getReturnType()->getPointerElementType());
    ASSERT_ELSE_UNKOWN(size > 0, call);
    return {llvm::APInt{64, 0}, llvm::APInt{64, size, true}};
}

std::pair<llvm::APInt, llvm::APInt> AllocWrapperDetector::boundsOfMallocLike(llvm::CallBase* call) {
    return {llvm::APInt{64, 0}, this->pointerDetector.findMinimumUnsignedValue(call->getArgOperand(0), call->getFunction())}; 
}

static std::pair<llvm::APInt, llvm::APInt> boundsOfCTypeFunc() {
    // [-128, 256]
    return {llvm::APInt{64, 0xFFFFFFFFFFFFFF80, true}, llvm::APInt{64, 256}};
}

const llvm::DenseMap<llvm::StringRef, std::function<std::pair<llvm::APInt, llvm::APInt>(AllocWrapperDetector*,llvm::CallBase*)>> AllocWrapperDetector::builtinLibcCallToBounds {
    {"malloc", [] (AllocWrapperDetector* self, llvm::CallBase* callInst) -> std::pair<llvm::APInt, llvm::APInt> {
        return self->boundsOfMallocLike(callInst);
    }},
    {"calloc", [] (AllocWrapperDetector* self, llvm::CallBase* callInst) -> std::pair<llvm::APInt, llvm::APInt> {
        auto lhOperandSize = self->pointerDetector.findMinimumUnsignedValue(callInst->getArgOperand(0), callInst->getFunction());
        auto rhOperandSize = self->pointerDetector.findMinimumUnsignedValue(callInst->getArgOperand(1), callInst->getFunction());
        auto result = lhOperandSize * rhOperandSize;
        assert(result.getBitWidth() <= 64);
        return {llvm::APInt{64, 0}, result};
    }},
    {"realloc", [] (AllocWrapperDetector* self, llvm::CallBase* callInst) -> std::pair<llvm::APInt, llvm::APInt> {
        return {llvm::APInt{64, 0}, self->pointerDetector.findMinimumUnsignedValue(callInst->getArgOperand(1), callInst->getFunction())};
    }},
    {"mmap", [] (AllocWrapperDetector* self, llvm::CallBase* callInst) -> std::pair<llvm::APInt, llvm::APInt> { 
        return self->findMmapBounds(callInst);
    }},
    {"mmap2", nullptr},
    {"mmap64", [] (AllocWrapperDetector* self, llvm::CallBase* callInst) -> std::pair<llvm::APInt, llvm::APInt> { 
        return self->findMmapBounds(callInst);
    }},
    {"aligned_alloc", nullptr},
    {"alloca", nullptr}, // handled as LLVM alloca instruction

    // from EFT_STAT
    {"__sysv_signal", nullptr},
    {"signal", nullptr},
    {"sigset", nullptr},
    {"__ctype_b_loc", [] (AllocWrapperDetector* self, llvm::CallBase* callInst) -> std::pair<llvm::APInt, llvm::APInt> { 
        return boundsOfCTypeFunc();
    }},
    {"__ctype_tolower_loc", [] (AllocWrapperDetector* self, llvm::CallBase* callInst) -> std::pair<llvm::APInt, llvm::APInt> { 
        return boundsOfCTypeFunc();
    }},
    {"__ctype_toupper_loc", [] (AllocWrapperDetector* self, llvm::CallBase* callInst) -> std::pair<llvm::APInt, llvm::APInt> { 
        return boundsOfCTypeFunc();
    }},
    {"__errno_location", [] (AllocWrapperDetector* self, llvm::CallBase* callInst) -> std::pair<llvm::APInt, llvm::APInt> {
        return self->boundsOfReturnedPointeeType(callInst);
    }},
    {"XKeysymToString", nullptr},
    {"__h_errno_location", nullptr},
    {"__res_state", nullptr},
    {"asctime", nullptr},
    {"bindtextdomain", nullptr},
    {"bind_textdomain_codeset", nullptr},
    {"ctermid", nullptr},
    {"dcgettext", nullptr},
    {"dgettext", nullptr},
    {"dngettext", nullptr},
    {"fdopen", nullptr},
    {"gcry_strerror", nullptr},
    {"gcry_strsource", nullptr},
    {"getgrgid", nullptr},
    {"getgrnam", nullptr},
    {"gethostbyaddr", nullptr},
    {"gethostbyname", nullptr},
    {"gethostbyname2", nullptr},
    {"getmntent", nullptr},
    {"getprotobyname", nullptr},
    {"getprotobynumber", nullptr},
    {"getpwent", nullptr},
    {"getpwnam", [] (AllocWrapperDetector* self, llvm::CallBase* callInst) -> std::pair<llvm::APInt, llvm::APInt> {
        return self->boundsOfReturnedPointeeType(callInst);
    }},
    {"getpwuid", nullptr},
    {"getservbyname", nullptr},
    {"getservbyport", nullptr},
    {"getspnam", nullptr},
    {"gettext", nullptr},
    {"gmtime", [] (AllocWrapperDetector* self, llvm::CallBase* callInst) -> std::pair<llvm::APInt, llvm::APInt> {
        return self->boundsOfReturnedPointeeType(callInst);
    }},
    {"gnu_get_libc_version", nullptr},
    {"gnutls_check_version", nullptr},
    {"localeconv", [] (AllocWrapperDetector* self, llvm::CallBase* callInst) -> std::pair<llvm::APInt, llvm::APInt> {
        // at least in glibc 2.31
        return self->boundsOfReturnedPointeeType(callInst);
    }},
    {"localtime", [] (AllocWrapperDetector* self, llvm::CallBase* callInst) -> std::pair<llvm::APInt, llvm::APInt> {
        return self->boundsOfReturnedPointeeType(callInst);
    }},
    {"ngettext", nullptr},
    {"pango_cairo_font_map_get_default", nullptr},
    {"re_comp", nullptr},
    {"setlocale", [] (AllocWrapperDetector* self, llvm::CallBase* callInst) -> std::pair<llvm::APInt, llvm::APInt> {
        // minimum return value is a string of length 1 + \0 char
        return {llvm::APInt{64, 0}, llvm::APInt{64, 2}};
    }},
    {"tgoto", nullptr},
    {"tparm", nullptr},
    {"zError", nullptr},

    // from ExtAPI
    {"\01_fopen", nullptr},
    {"\01fopen64", nullptr},
    {"\01readdir64", nullptr},
    {"\01tmpfile64", nullptr},
    {"BIO_new_socket", nullptr},
    {"FT_Get_Sfnt_Table", nullptr},
    {"FcFontList", nullptr},
    {"FcFontMatch", nullptr},
    {"FcFontRenderPrepare", nullptr},
    {"FcFontSetCreate", nullptr},
    {"FcFontSort", nullptr},
    {"FcInitLoadConfig", nullptr},
    {"FcObjectSetBuild", nullptr},
    {"FcObjectSetCreate", nullptr},
    {"FcPatternBuild", nullptr},
    {"FcPatternCreate", nullptr},
    {"FcPatternDuplicate", nullptr},
    {"SSL_CTX_new", nullptr},
    {"SSL_get_peer_certificate", nullptr},
    {"SSL_new", nullptr},
    {"SSLv23_client_method", nullptr},
    {"SyGetmem", nullptr},
    {"TLSv1_client_method", nullptr},
    {"Void_ExtendCore", nullptr},
    {"XAddExtension", nullptr},
    {"XAllocClassHint", nullptr},
    {"XAllocSizeHints", nullptr},
    {"XAllocStandardColormap", nullptr},
    {"XCreateFontSet", nullptr},
    {"XCreateImage", nullptr},
    {"XCreateGC", nullptr},
    {"XGetImage", nullptr},
    {"XGetModifierMapping", nullptr},
    {"XGetMotionEvents", nullptr},
    {"XGetVisualInfo", nullptr},
    {"XLoadQueryFont", nullptr},
    {"XListPixmapFormats", nullptr},
    {"XRenderFindFormat", nullptr},
    {"XRenderFindStandardFormat", nullptr},
    {"XRenderFindVisualFormat", nullptr},
    {"XOpenDisplay", nullptr},
    {"XSetIOErrorHandler", nullptr},
    {"XShapeGetRectangles", nullptr},
    {"XShmCreateImage", nullptr},
    {"XcursorImageCreate", nullptr},
    {"XcursorLibraryLoadImages", nullptr},
    {"XcursorShapeLoadImages", nullptr},
    {"XineramaQueryScreens", nullptr},
    {"XkbGetMap", nullptr},
    {"XtAppCreateShell", nullptr},
    {"XtCreateApplicationContext", nullptr},
    {"XtOpenDisplay", nullptr},
    {"alloc", nullptr},
    {"alloc_check", nullptr},
    {"alloc_clear", nullptr},
    {"art_svp_from_vpath", nullptr},
    {"art_svp_vpath_stroke", nullptr},
    {"art_svp_writer_rewind_new", nullptr},
    {"art_vpath_dash", nullptr},
    {"cairo_create", nullptr},
    {"cairo_image_surface_create_for_data", nullptr},
    {"cairo_pattern_create_for_surface", nullptr},
    {"cairo_surface_create_similar", nullptr},
    {"fopen", nullptr},
    {"fopen64", nullptr},
    {"fopencookie", nullptr},
    {"g_scanner_new", nullptr},
    {"gcry_sexp_nth_mpi", nullptr},
    {"gzdopen", nullptr},
    {"iconv_open", nullptr},
    {"jpeg_alloc_huff_table", nullptr},
    {"jpeg_alloc_quant_table", nullptr},
    {"lalloc", nullptr},
    {"lalloc_clear", nullptr},
    {"nhalloc", nullptr},
    {"oballoc", nullptr},
    {"pango_cairo_font_map_create_context", nullptr},
    //This may also point *arg2 to a new string.
    {"pcre_compile", nullptr},
    {"pcre_study", nullptr},
    {"permalloc", nullptr},
    {"png_create_info_struct", nullptr},
    {"png_create_write_struct", nullptr},
    {"popen", nullptr},
    {"pthread_getspecific", nullptr},
    {"readdir", [] (AllocWrapperDetector* self, llvm::CallBase* callInst) -> std::pair<llvm::APInt, llvm::APInt> {
        // https://man7.org/linux/man-pages/man3/readdir.3.html
        return self->boundsOfReturnedPointeeType(callInst);
    }},
    {"readdir64", [] (AllocWrapperDetector* self, llvm::CallBase* callInst) -> std::pair<llvm::APInt, llvm::APInt> {
        // https://man7.org/linux/man-pages/man3/readdir64.3.html
        return self->boundsOfReturnedPointeeType(callInst);
    }},
    {"safe_calloc", nullptr},
    {"safe_malloc", nullptr},
    {"safecalloc", nullptr},
    {"safemalloc", nullptr},
    {"safexcalloc", nullptr},
    {"safexmalloc", nullptr},
    {"savealloc", nullptr},
    {"setmntent", nullptr},
    {"shmat", nullptr},
    {"tempnam", nullptr},
    {"tmpfile", nullptr},
    {"tmpfile64", nullptr},
    {"xalloc", nullptr},
    {"xcalloc", nullptr},
    {"xmalloc", nullptr},
    //C++ functions
    {"_Znwm", [] (AllocWrapperDetector* self, llvm::CallBase* call) -> std::pair<llvm::APInt, llvm::APInt> {
        return self->boundsOfMallocLike(call);
    }},	// new
    {"_ZnwmRKSt9nothrow_t", [] (AllocWrapperDetector* self, llvm::CallBase* call) -> std::pair<llvm::APInt, llvm::APInt> {
        return self->boundsOfMallocLike(call);
    }}, // non-throwing new
    {"_Znam", [] (AllocWrapperDetector* self, llvm::CallBase* call) -> std::pair<llvm::APInt, llvm::APInt> {
        return self->boundsOfMallocLike(call);
    }},	// new []
    {"_ZnamRKSt9nothrow_t", [] (AllocWrapperDetector* self, llvm::CallBase* call) -> std::pair<llvm::APInt, llvm::APInt> {
        return self->boundsOfMallocLike(call);
    }}, // non-throwing new []
    {"_Znaj", nullptr},	// new
    {"_Znwj", nullptr},	// new []
    {"__cxa_allocate_exception", [] (AllocWrapperDetector* self, llvm::CallBase* call) -> std::pair<llvm::APInt, llvm::APInt> {
        return self->boundsOfMallocLike(call);
    }},	// allocate an exception
    {"memalign", nullptr},
    {"valloc", nullptr},
    {"SRE_LockCreate", nullptr},
    {"VOS_MemAlloc", nullptr},
    {"\01mmap64", nullptr},
    //FIXME: this is like realloc but with arg1.
    {"X509_NAME_oneline", nullptr},
    {"X509_verify_cert_error_string", nullptr},
    {"XBaseFontNameListOfFontSet", nullptr},
    {"XGetAtomName", nullptr},
    {"XGetDefault", nullptr},
    {"XGetKeyboardMapping", nullptr},
    {"XListDepths", nullptr},
    {"XListFonts", nullptr},
    {"XSetLocaleModifiers", nullptr},
    {"XcursorGetTheme", nullptr},
    {"__strdup", nullptr},
    {"crypt", nullptr},
    {"ctime", nullptr},
    {"dlerror", nullptr},
    {"gai_strerror", nullptr},
    {"gcry_cipher_algo_name", nullptr},
    {"gcry_md_algo_name", nullptr},
    {"gcry_md_read", nullptr},
    {"getlogin", nullptr},
    {"getpass", nullptr},
    {"gnutls_strerror", nullptr},
    {"gpg_strerror", nullptr},
    {"gzerror", nullptr},
    {"inet_ntoa", nullptr},
    {"initscr", nullptr},
    {"llvm.stacksave", nullptr},
    {"newwin", nullptr},
    {"nl_langinfo", nullptr},
    {"opendir", [] (AllocWrapperDetector* self, llvm::CallBase* callInst) -> std::pair<llvm::APInt, llvm::APInt> {
        return self->boundsOfReturnedPointeeType(callInst);
    }},
    {"sbrk", nullptr},
    {"strdup", nullptr},
    {"strerror", [] (AllocWrapperDetector* self, llvm::CallBase* call) -> std::pair<llvm::APInt, llvm::APInt> {
        if (auto constInt = llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(0)))
            return {llvm::APInt{64, 0}, llvm::APInt{64, strlen(strerror(constInt->getLimitedValue()))}};
        // shortest error string
        return {llvm::APInt{64, 0}, llvm::APInt{64, strlen("I/O error")}};
    }},
    {"strsignal", nullptr},
    {"textdomain", nullptr},
    {"tgetstr", nullptr},
    {"tigetstr", nullptr},
    {"tmpnam", nullptr},
    {"ttyname", nullptr},

    {"getcwd", [] (AllocWrapperDetector* self, llvm::CallBase* call) -> std::pair<llvm::APInt, llvm::APInt> {
        // technically incorrect when arg0 is NULL! Then the size argument (arg2) is ignored
        // but that's a glibc-specific extension I'm hoping no one uses
        return {llvm::APInt{64, 0}, self->pointerDetector.findMinimumUnsignedValue(call->getArgOperand(1), call->getFunction())};
    }},
    {"mem_realloc", nullptr},
    {"realloc_obj", nullptr},
    {"safe_realloc", nullptr},
    {"saferealloc", nullptr},
    {"safexrealloc", nullptr},
    {"xrealloc", nullptr}
};
