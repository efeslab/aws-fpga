#ifndef CL_FPGARR_DECODER_H
#define CL_FPGARR_DECODER_H
// -std=c++17 is required
#include <cassert>
#include <cstdint>
#include <cstdio>

#include "cl_fpgarr_trace.hpp"

template <typename BUSCFG>
class Decoder {
 private:
  // shortcut to trace typedefs
  typedef typename VIDITrace<BUSCFG>::pktsize_t pktsize_t;
  typedef typename VIDITrace<BUSCFG>::logb_valid_t logb_valid_t;
  typedef typename VIDITrace<BUSCFG>::loge_valid_t loge_valid_t;
  typedef typename VIDITrace<BUSCFG>::trace_size_t trace_size_t;

  FILE *fp = nullptr;
  const char *filepath = nullptr;
  trace_size_t trace_bits;
  static constexpr size_t BUFSIZE = 4096;
  ibitstream ibuf;
  size_t ibuf_read_cb(void *p, size_t nbytes) {
    return fread(p, 1, nbytes, fp);
  }

 public:
  Decoder(const char *_filepath)
      : filepath(_filepath),
        ibuf(BUFSIZE, std::bind(&Decoder::ibuf_read_cb, this,
                                std::placeholders::_1, std::placeholders::_2)) {
    fp = fopen(_filepath, "rb");
  }
  ~Decoder() {
    if (fp) fclose(fp);
  }

  void parse_trace(VIDITrace<BUSCFG> &T);
};
#include "cl_fpgarr_decoder_impl.hpp"
#endif  // CL_FPGARR_DECODER_H
