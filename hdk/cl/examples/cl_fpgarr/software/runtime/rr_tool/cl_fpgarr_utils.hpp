#ifndef CL_FPGARR_UTILS_H
#define CL_FPGARR_UTILS_H
#include <cstdint>
#include <cstring>
#include <type_traits>

// constexpr_for is taken from
// https://artificial-mind.net/blog/2020/10/31/constexpr-for
template <auto Start, auto End, auto Inc, class F>
constexpr void constexpr_for(F &&f) {
  if constexpr (Start < End) {
    f(std::integral_constant<decltype(Start), Start>());
    constexpr_for<Start + Inc, End, Inc>(f);
  }
}

// TODO: move to cl_fpgarr_main.cpp this is not utils
struct argoptions_t {
  enum { CFG_UNKNOWN, CFG_RECORD, CFG_VERIF } cfg_type = CFG_UNKNOWN;
  enum {
    OP_UNKNOWN,
    OP_ANLYS,
    OP_COMP,
    OP_MUTATE,
    OP_PHYTS_SIM
  } op_type = OP_UNKNOWN;
  bool isVerbose = false;
  union {
    const char *anlys_filepath;
    const char *comp_filepaths[2] = {nullptr, nullptr};
    struct {
      const char *input_filepath[2];
      const char *output_filepath;
    };  // for OP_MUTATE
    const char *phyts_sim_filepath;
  };
  bool enableHBVer2 = false;
};

#define ARRAY_LEN(x) (sizeof(x) / sizeof(x[0]))
bool findStringInArray(const char *s, size_t slen, const char *const *arr,
                       size_t arrlen);
#endif  // CL_FPGARR_UTILS_H
