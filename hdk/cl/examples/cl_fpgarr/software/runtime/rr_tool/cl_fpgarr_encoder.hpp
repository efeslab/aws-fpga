#ifndef CL_FPGARR_ENCODER_H
#define CL_FPGARR_ENCODER_H
#include <cstdint>
#include <cstdio>

#include "cl_fpgarr_trace.hpp"

template <typename BUSCFG>
class Encoder {
 private:
  typedef typename VIDITrace<BUSCFG>::trace_size_t trace_size_t;
  FILE *fp = nullptr;
  const char *filepath = nullptr;
  static constexpr size_t BUFSIZE = 4096;
  obitstream obuf;
  size_t obuf_write_cb(void *p, size_t nbytes) {
    return fwrite(p, 1, nbytes, fp);
  }

 public:
  Encoder(const char *_filepath)
      : filepath(_filepath),
        obuf(BUFSIZE,
             std::bind(&Encoder::obuf_write_cb, this, std::placeholders::_1,
                         std::placeholders::_2)) {
    fp = fopen(_filepath, "wb");
  }
  ~Encoder() {
    if (fp) {
      assert(fclose(fp) == 0);
    }
  }

  void export_trace(VIDITrace<BUSCFG> &T) {
    trace_size_t tsize = 0;
    assert(fp && "file to export open failed");
    // place holder for the trace size header
    assert(fwrite(&tsize, sizeof(tsize), 1, fp) == 1);
    static_assert(*std::max_element(BUSCFG::CW.cbegin(), BUSCFG::CW.cend()) <
                  BUFSIZE * 8);
    tsize = T.exportTrace(obuf);
    // need to flush the obitstream buffer since going to fseek fp
    obuf.flush();
    assert(fseek(fp, 0, SEEK_SET) == 0);
    assert(fwrite(&tsize, sizeof(tsize), 1, fp) == 1);
  }
};
#endif  // CL_FPGARR_ENCODER_H
