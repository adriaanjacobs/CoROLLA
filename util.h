#pragma once

#if 0
#ifndef BOOST_STACKTRACE_USE_BACKTRACE
    #define BOOST_STACKTRACE_USE_BACKTRACE
#endif

#include <boost/stacktrace.hpp>

#include <source_location>
#include <llvm/Support/raw_ostream.h>
#include <signal.h>

#define dbg_assert(expr) \
    if (!static_cast<bool>(expr)) { \
        llvm::outs().flush();   \
        llvm::errs().flush();   \
        std::cout.flush();  \
        std::cerr.flush();  \
        std::cerr << __FILE__ << ":" << __LINE__ << ": " << __func__ << ": Assertion `" << #expr << "` failed.\n"; \
        std::cerr << "Backtrace: \n";   \
        std::cerr << boost::stacktrace::stacktrace();   \
        std::cerr << std::endl; \
        raise(SIGABRT); \
    }
#endif

#include <functional>
#include <llvm/IR/Operator.h>

struct run_on_destruct {
    std::function<void()> func;
    run_on_destruct(auto func) : func{std::move(func)} {}
    ~run_on_destruct() { func(); }
};

#define HANDLE_UNKOWN_VALUE(val)                                    \
    do {        \
        llvm::outs() << "Unkown value type: \n";      \
        llvm::outs() << "\t" << *val << "\n\n";     \
        llvm::outs() << "Is constant: " << (llvm::isa<llvm::Constant>(val) ? "yes" : "no") << "\n"; \
        llvm::outs() << "Is GlobalVariable: " << (llvm::isa<llvm::GlobalVariable>(val) ? "yes" : "no") << "\n"; \
        llvm::outs() << "Is ConstantData: " << (llvm::isa<llvm::ConstantData>(val) ? "yes" : "no") << "\n"; \
        llvm::outs() << "Is instruction: " << (llvm::isa<llvm::Instruction>(val) ? "yes" : "no") << "\n"; \
        llvm::outs() << "Is operator: " << (llvm::isa<llvm::Operator>(val) ? "yes" : "no") << "\n"; \
        assert(!"Unkown instruction!");     \
    } while (false)

#define ASSERT_ELSE_UNKOWN(cond, val) \
    do {                                                \
        bool condVal = static_cast<bool>(cond);     \
        if (!condVal) {                                \
            HANDLE_UNKOWN_VALUE(val);               \
        }                                           \
    } while (false)

