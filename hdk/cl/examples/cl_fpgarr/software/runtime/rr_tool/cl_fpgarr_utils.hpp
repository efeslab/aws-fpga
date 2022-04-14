#ifndef CL_FPGARR_UTILS_H
#define CL_FPGARR_UTILS_H
#include <type_traits>
#include <cstdint>

// constexpr_for is taken from
// https://artificial-mind.net/blog/2020/10/31/constexpr-for
template <auto Start, auto End, auto Inc, class F>
constexpr void constexpr_for(F&& f)
{
  if constexpr (Start < End)
  {
    f(std::integral_constant<decltype(Start), Start>());
    constexpr_for<Start + Inc, End, Inc>(f);
  }
}

// TODO: move to cl_fpgarr_main.cpp this is not utils
struct argoptions_t {
  enum {CFG_UNKNOWN, CFG_RECORD, CFG_VERIF} cfg_type = CFG_UNKNOWN;
  enum {OP_UNKNOWN, OP_ANLYS, OP_COMP, OP_MUTATE} op_type = OP_UNKNOWN;
  bool isVerbose = false;
  union {
    const char *anlys_filepath;
    const char *comp_filepaths[2] = {nullptr, nullptr};
    struct {
      const char *input_filepath;
      const char *output_filepath;
    }; // for OP_MUTATE
  };
  bool enableHBVer2 = false;
};

const char *input_interfaces[] = {"pcis", "sda", "ocl", "bar1"};
const char *output_interfaces[] = {"pcim"};
const char *send_channels[] = {"AW", "W", "AR"};
const char *recv_channels[] = {"B", "R"};
#define ARRAY_LEN(x) (sizeof(x)/sizeof(x[0]))
#endif // CL_FPGARR_UTILS_H
