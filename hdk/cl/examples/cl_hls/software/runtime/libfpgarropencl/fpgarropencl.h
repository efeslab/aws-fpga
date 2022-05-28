#ifndef LIBFPGARROPENCL_H
#define LIBFPGARROPENCL_H
#include <stddef.h>

#define FPGARR_OPENCL_KERNEL_MAX_ARGS (128)
// #undef DEBUG_FPGARROPENCL
#ifdef __cplusplus
extern "C" {
#endif
typedef enum {KARG_UNKNOWN, KARG_CL_MEM, KARG_4B, KARG_8B} fake_program_args_t;
// fake_program_spec_t acts as the program binary, need to be manually crafted
// for each application
typedef struct {
  size_t nargs;
  fake_program_args_t args[FPGARR_OPENCL_KERNEL_MAX_ARGS];
} fake_program_spec_t;
extern void print_fake_program_spec(fake_program_spec_t *p);
extern int test_argc;
extern char **test_argv;
extern int fpgarropencl_main(int argc, char **argv);
#define REG_STATIC_ARGV(argv) \
  char **test_argv = (char**)(argv);    \
  int test_argc = sizeof(argv) / sizeof(argv[0])
#ifdef __cplusplus
}
#endif

#ifdef __cplusplus
#include <type_traits>
#include <functional>
// CPP helper to construct fake_program_spec_t automatically.
// usage:
// struct fake_progra_spec_t p = FakeProgramSpecBuilder::build(&func_foo);
struct FakeProgramSpecBuilder {
  template <class T>
  static constexpr fake_program_args_t get_args_t() {
    static_assert(sizeof(uint32_t) == 4);
    static_assert(sizeof(uint64_t) == 8);
    if (std::is_pointer<T>::value)
      return KARG_CL_MEM;
    else if (sizeof(T) == 4)
      return KARG_4B;
    else if (sizeof(T) == 8)
      return KARG_8B;
    return KARG_UNKNOWN;
  }
  template <class R, class... Args>
  static constexpr fake_program_spec_t build(R (*f) (Args...)) {
    fake_program_spec_t p = {.nargs = sizeof...(Args),
			     .args = {get_args_t<Args>() ...}};
    return p;
  }
};
#endif
#endif  // LIBFPGARROPENCL_H
