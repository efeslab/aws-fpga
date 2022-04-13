#ifndef CL_FPGARR_DECODER_H
#define CL_FPGARR_DECODER_H
// -std=c++17 is required
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <cstring>

#include "cl_fpgarr_trace.hpp"
#include "cl_fpgarr_utils.hpp"

using namespace std;

template <typename BUSCFG>
class Decoder {
 private:
  // determine what type to use logb_valid
  typedef uint16_t logb_valid_t;
  // determine what type to use for loge_valid
  typedef uint32_t loge_valid_t;
  // determine what type to represent the total length of the whole trace
  typedef uint64_t trace_size_t;

  FILE *fp = nullptr;
  const char *filepath = nullptr;
  trace_size_t trace_bits;
  static constexpr int BUFSIZE = 4096;
  ibitstream ibuf;
  size_t ibuf_read_cb(void *p, size_t nbytes) {
    return fread(p, 1, nbytes, fp);
  }

 public:
  Decoder(const char *_filepath)
      : filepath(_filepath),
        ibuf(BUFSIZE, std::bind(&Decoder::ibuf_read_cb, this,
                                std::placeholders::_1, std::placeholders::_2)) {
    fp = fopen(_filepath, "r");
  }
  ~Decoder() {
    if (fp) fclose(fp);
  }

  void parse_trace(VIDITrace<BUSCFG> &T);
};
#include "cl_fpgarr_decoder_impl.hpp"
#endif  // CL_FPGARR_DECODER_H
