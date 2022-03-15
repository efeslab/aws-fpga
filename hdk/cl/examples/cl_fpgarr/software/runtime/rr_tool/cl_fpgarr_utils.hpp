#ifndef CL_FPGARR_UTILS_H
#define CL_FPGARR_UTILS_H
#include <type_traits>
#include <cstdint>
#include <algorithm>

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

using std::uint8_t;
// src is a pointer to the byte that contains valid data
// dst is a pointer to the byte that I should write valid data
// srcoff and dstoff are the offsets (0~7) from which bit valid data or vacancy
// start
// `src`, `srcoff`, `dst`, `dstoff` will be updated to represent the remaining
// valid data or vacant area upon return
inline void bitscpy(uint8_t *(&src), uint8_t &srcoff, uint8_t *(&dst),
                    uint8_t &dstoff, int bits) {
  int copied_bits = 0;
  // at each iteration, only copy what is left in the current byte of src to
  // what is still vacant in the current byte of dst
  // Also do not copy more than requested
  while (copied_bits < bits) {
    uint8_t src_avail = 8 - srcoff;
    uint8_t dst_avail = 8 - dstoff;
    // how many data to copy in this iteration
    uint8_t copy_len = std::min(
        static_cast<int>(std::min(src_avail, dst_avail)), bits - copied_bits);
    uint8_t copy_data = ((*src) >> srcoff);
    copy_data &= ~((~((uint8_t)0)) << copy_len);
    (*dst) |= copy_data << dstoff;
    copied_bits += copy_len;
    dstoff += copy_len;
    srcoff += copy_len;
    if (dstoff == 8) {
      dstoff = 0;
      ++dst;
    }
    if (srcoff == 8) {
      srcoff = 0;
      ++src;
    }
  }
}

struct argoptions_t {
  enum {CFG_UNKNOWN, CFG_RECORD, CFG_VERIF} cfg_type = CFG_UNKNOWN;
  enum {OP_UNKNOWN, OP_ANLYS, OP_COMP} op_type = OP_UNKNOWN;
  bool isVerbose = false;
  union {
    const char *anlys_filepath;
    const char *comp_filepaths[2] = {nullptr, nullptr};
  };
  bool enableHBVer2 = false;
};

const char *input_interfaces[] = {"pcis", "sda", "ocl", "bar1"};
const char *output_interfaces[] = {"pcim"};
const char *send_channels[] = {"AW", "W", "AR"};
const char *recv_channels[] = {"B", "R"};
#endif // CL_FPGARR_UTILS_H
