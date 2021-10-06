#ifndef BOOST_STACKTRACE_USE_BACKTRACE
    #define BOOST_STACKTRACE_USE_BACKTRACE
#endif

#include <boost/stacktrace.hpp>

#include <functional>
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

struct run_on_destruct {
    std::function<void()> func;
    run_on_destruct(auto func) : func{std::move(func)} {}
    ~run_on_destruct() { func(); }
};