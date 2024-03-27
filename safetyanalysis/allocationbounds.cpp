#include <llvm-util/safetyanalysis/allocationbounds.h>
#include <llvm-util/util.h>

#include <optional>

extern const llvm::DenseMap<llvm::StringRef, std::function<std::pair<llvm::APInt, llvm::APInt>(llvm::Module&,llvm::ModuleAnalysisManager&,llvm::CallBase*)>> builtinLibcCallToBounds;

static std::optional<decltype(builtinLibcCallToBounds)::value_type::second_type> isKnownLibcAllocator(llvm::Function* func) {
    auto it = builtinLibcCallToBounds.find(func->getName());
    if (it != builtinLibcCallToBounds.end() && func->isDeclaration())
        return it->getSecond();
    if (func->isDeclaration() && func->hasFnAttribute(llvm::Attribute::NoAlias)) {
        llvm::outs() << "We should get to know '" << func->getName() << "'!\n";
        assert(!"Add it to the list of known allocation funcs!");
    }

    return std::nullopt;
}

bool isNonWrapperAllocSite(llvm::Value* val) {
    if (auto callInst = llvm::dyn_cast<llvm::CallBase>(val)) {
        auto calledFunc = callInst->getCalledFunction();
        return calledFunc && isKnownLibcAllocator(calledFunc);
    }
    return llvm::isa<llvm::AllocaInst, llvm::GlobalVariable>(val);
}

std::optional<std::pair<llvm::APInt, llvm::APInt>> findMinimumAllocBounds(llvm::Value* allocInstr, llvm::Module& module, llvm::ModuleAnalysisManager& MAM) {
    ASSERT_ELSE_UNKOWN(isNonWrapperAllocSite(allocInstr), allocInstr);
    auto& dataLayout = module.getDataLayout();
    if (auto allocaInstr = llvm::dyn_cast<llvm::AllocaInst>(allocInstr)) {
        auto size = dataLayout.getTypeAllocSize(allocaInstr->getAllocatedType());
        ASSERT_ELSE_UNKOWN(size >= 0, allocInstr); // gcc's `combine_givs` does `alloca(0)` and LLVM is happy with it
        return std::pair{llvm::APInt{64, 0}, llvm::APInt{64, size, true}};
    } else if (auto globalVariable = llvm::dyn_cast<llvm::GlobalVariable>(allocInstr)) {
        auto size = dataLayout.getTypeAllocSize(globalVariable->getValueType());
        ASSERT_ELSE_UNKOWN(size > 0, allocInstr);
        return std::pair{llvm::APInt{64, 0}, llvm::APInt{64, size, true}};
    } else if (auto callInst = llvm::dyn_cast<llvm::CallBase>(allocInstr)) {
        auto calledFunc = callInst->getCalledFunction();
        assert(calledFunc);
        if (auto it = isKnownLibcAllocator(calledFunc)) {
            if (it.value()) {
                return it.value()(module, MAM, callInst);
            } else HANDLE_UNKOWN_VALUE(callInst);
        } else {
            // custom allocation wrapper. we shouldnt need this case if we do good callbase transparancy in isInBounds
            return std::nullopt;
            HANDLE_UNKOWN_VALUE(callInst);
        }
    } else HANDLE_UNKOWN_VALUE(allocInstr);
}

std::pair<llvm::APInt, llvm::APInt> findMmapBounds(llvm::CallBase* callInst, llvm::ModuleAnalysisManager& MAM) { // redis calls this
    return {llvm::APInt{64, 0}, findMinimumUnsignedValue(callInst->getArgOperand(1), callInst->getFunction(), MAM)};
}

std::pair<llvm::APInt, llvm::APInt> boundsOfReturnedPointeeType(llvm::CallBase* call) {
    auto size = call->getModule()->getDataLayout().getTypeAllocSize(call->getCalledFunction()->getReturnType()->getPointerElementType());
    ASSERT_ELSE_UNKOWN(size > 0, call);
    return {llvm::APInt{64, 0}, llvm::APInt{64, size, true}};
}

std::pair<llvm::APInt, llvm::APInt> boundsOfMallocLike(llvm::CallBase* call, llvm::ModuleAnalysisManager& MAM) {
    return {llvm::APInt{64, 0}, findMinimumUnsignedValue(call->getArgOperand(0), call->getFunction(), MAM)}; 
}

static std::pair<llvm::APInt, llvm::APInt> boundsOfCTypeFunc() {
    // [-128, 256]
    return {llvm::APInt{64, 0xFFFFFFFFFFFFFF80, true}, llvm::APInt{64, 256}};
}

const decltype(builtinLibcCallToBounds) builtinLibcCallToBounds {
    {"malloc", [] (llvm::Module& module, llvm::ModuleAnalysisManager& MAM, llvm::CallBase* callInst) -> std::pair<llvm::APInt, llvm::APInt> {
        return boundsOfMallocLike(callInst, MAM);
    }},
    {"calloc", [] (llvm::Module& module, llvm::ModuleAnalysisManager& MAM, llvm::CallBase* callInst) -> std::pair<llvm::APInt, llvm::APInt> {
        auto lhOperandSize = findMinimumUnsignedValue(callInst->getArgOperand(0), callInst->getFunction(), MAM);
        auto rhOperandSize = findMinimumUnsignedValue(callInst->getArgOperand(1), callInst->getFunction(), MAM);
        auto result = lhOperandSize * rhOperandSize;
        assert(result.getBitWidth() <= 64);
        return {llvm::APInt{64, 0}, result};
    }},
    {"realloc", [] (llvm::Module& module, llvm::ModuleAnalysisManager& MAM, llvm::CallBase* callInst) -> std::pair<llvm::APInt, llvm::APInt> {
        return {llvm::APInt{64, 0}, findMinimumUnsignedValue(callInst->getArgOperand(1), callInst->getFunction(), MAM)};
    }},
    {"mmap", [] (llvm::Module& module, llvm::ModuleAnalysisManager& MAM, llvm::CallBase* callInst) -> std::pair<llvm::APInt, llvm::APInt> { 
        return findMmapBounds(callInst, MAM);
    }},
    {"mmap2", nullptr},
    {"mmap64", [] (llvm::Module& module, llvm::ModuleAnalysisManager& MAM, llvm::CallBase* callInst) -> std::pair<llvm::APInt, llvm::APInt> { 
        return findMmapBounds(callInst, MAM);
    }},
    {"aligned_alloc", nullptr},
    {"alloca", nullptr}, // handled as LLVM alloca instruction

    // from EFT_STAT
    {"__sysv_signal", nullptr},
    {"signal", nullptr},
    {"sigset", nullptr},
    {"__ctype_b_loc", [] (llvm::Module& module, llvm::ModuleAnalysisManager& MAM, llvm::CallBase* callInst) -> std::pair<llvm::APInt, llvm::APInt> { 
        return boundsOfCTypeFunc();
    }},
    {"__ctype_tolower_loc", [] (llvm::Module& module, llvm::ModuleAnalysisManager& MAM, llvm::CallBase* callInst) -> std::pair<llvm::APInt, llvm::APInt> { 
        return boundsOfCTypeFunc();
    }},
    {"__ctype_toupper_loc", [] (llvm::Module& module, llvm::ModuleAnalysisManager& MAM, llvm::CallBase* callInst) -> std::pair<llvm::APInt, llvm::APInt> { 
        return boundsOfCTypeFunc();
    }},
    {"__errno_location", [] (llvm::Module& module, llvm::ModuleAnalysisManager& MAM, llvm::CallBase* callInst) -> std::pair<llvm::APInt, llvm::APInt> {
        return boundsOfReturnedPointeeType(callInst);
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
    {"getpwnam", [] (llvm::Module& module, llvm::ModuleAnalysisManager& MAM, llvm::CallBase* callInst) -> std::pair<llvm::APInt, llvm::APInt> {
        return boundsOfReturnedPointeeType(callInst);
    }},
    {"getpwuid", nullptr},
    {"getservbyname", nullptr},
    {"getservbyport", nullptr},
    {"getspnam", nullptr},
    {"gettext", nullptr},
    {"gmtime", [] (llvm::Module& module, llvm::ModuleAnalysisManager& MAM, llvm::CallBase* callInst) -> std::pair<llvm::APInt, llvm::APInt> {
        return boundsOfReturnedPointeeType(callInst);
    }},
    {"gnu_get_libc_version", nullptr},
    {"gnutls_check_version", nullptr},
    {"localeconv", [] (llvm::Module& module, llvm::ModuleAnalysisManager& MAM, llvm::CallBase* callInst) -> std::pair<llvm::APInt, llvm::APInt> {
        // at least in glibc 2.31
        return boundsOfReturnedPointeeType(callInst);
    }},
    {"localtime", [] (llvm::Module& module, llvm::ModuleAnalysisManager& MAM, llvm::CallBase* callInst) -> std::pair<llvm::APInt, llvm::APInt> {
        return boundsOfReturnedPointeeType(callInst);
    }},
    {"ngettext", nullptr},
    {"pango_cairo_font_map_get_default", nullptr},
    {"re_comp", nullptr},
    {"setlocale", [] (llvm::Module& module, llvm::ModuleAnalysisManager& MAM, llvm::CallBase* callInst) -> std::pair<llvm::APInt, llvm::APInt> {
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
    {"readdir", [] (llvm::Module& module, llvm::ModuleAnalysisManager& MAM, llvm::CallBase* callInst) -> std::pair<llvm::APInt, llvm::APInt> {
        // https://man7.org/linux/man-pages/man3/readdir.3.html
        return boundsOfReturnedPointeeType(callInst);
    }},
    {"readdir64", [] (llvm::Module& module, llvm::ModuleAnalysisManager& MAM, llvm::CallBase* callInst) -> std::pair<llvm::APInt, llvm::APInt> {
        // https://man7.org/linux/man-pages/man3/readdir64.3.html
        return boundsOfReturnedPointeeType(callInst);
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
    {"_Znwm", [] (llvm::Module& module, llvm::ModuleAnalysisManager& MAM, llvm::CallBase* call) -> std::pair<llvm::APInt, llvm::APInt> {
        return boundsOfMallocLike(call, MAM);
    }},	// new
    {"_ZnwmRKSt9nothrow_t", [] (llvm::Module& module, llvm::ModuleAnalysisManager& MAM, llvm::CallBase* call) -> std::pair<llvm::APInt, llvm::APInt> {
        return boundsOfMallocLike(call, MAM);
    }}, // non-throwing new
    {"_Znam", [] (llvm::Module& module, llvm::ModuleAnalysisManager& MAM, llvm::CallBase* call) -> std::pair<llvm::APInt, llvm::APInt> {
        return boundsOfMallocLike(call, MAM);
    }},	// new []
    {"_ZnamRKSt9nothrow_t", [] (llvm::Module& module, llvm::ModuleAnalysisManager& MAM, llvm::CallBase* call) -> std::pair<llvm::APInt, llvm::APInt> {
        return boundsOfMallocLike(call, MAM);
    }}, // non-throwing new []
    {"_Znaj", nullptr},	// new
    {"_Znwj", nullptr},	// new []
    {"__cxa_allocate_exception", [] (llvm::Module& module, llvm::ModuleAnalysisManager& MAM, llvm::CallBase* call) -> std::pair<llvm::APInt, llvm::APInt> {
        return boundsOfMallocLike(call, MAM);
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
    {"opendir", [] (llvm::Module& module, llvm::ModuleAnalysisManager& MAM, llvm::CallBase* callInst) -> std::pair<llvm::APInt, llvm::APInt> {
        return boundsOfReturnedPointeeType(callInst);
    }},
    {"sbrk", nullptr},
    {"strdup", nullptr},
    {"strerror", [] (llvm::Module& module, llvm::ModuleAnalysisManager& MAM, llvm::CallBase* call) -> std::pair<llvm::APInt, llvm::APInt> {
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

    {"getcwd", [] (llvm::Module& module, llvm::ModuleAnalysisManager& MAM, llvm::CallBase* call) -> std::pair<llvm::APInt, llvm::APInt> {
        // technically incorrect when arg0 is NULL! Then the size argument (arg2) is ignored
        // but that's a glibc-specific extension I'm hoping no one uses
        return {llvm::APInt{64, 0}, findMinimumUnsignedValue(call->getArgOperand(1), call->getFunction(), MAM)};
    }},
    {"mem_realloc", nullptr},
    {"realloc_obj", nullptr},
    {"safe_realloc", nullptr},
    {"saferealloc", nullptr},
    {"safexrealloc", nullptr},
    {"xrealloc", nullptr}
};
