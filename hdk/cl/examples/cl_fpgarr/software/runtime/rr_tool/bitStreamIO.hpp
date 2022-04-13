#ifndef CL_FPGARR_BITSTREAMIO_H
#define CL_FPGARR_BITSTREAMIO_H
#include <algorithm>
#include <cstdint>
#include <functional>

using std::uint8_t;

class bitstream {
 protected:
  uint8_t *buf = nullptr;
  size_t len = 0;  // len of valid bytes
  uint8_t *p = buf;
  uint8_t off = 0;
  size_t bufsize = 0;

  // src is a pointer to the byte that contains valid data
  // dst is a pointer to the byte that I should write valid data
  // srcoff and dstoff are the offsets (0~7) from which bit valid data or
  // vacancy start `src`, `srcoff`, `dst`, `dstoff` will be updated to represent
  // the remaining valid data or vacant area upon return
  static void bitscpy(uint8_t *(&src), uint8_t &srcoff, uint8_t *(&dst),
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

 public:
  bitstream(size_t _bufsize) : buf(new uint8_t[_bufsize]), bufsize(_bufsize) {}
  ~bitstream() { delete[] buf; }
};

class ibitstream : public bitstream {
 private:
  // read_cb is a callback that allows the BitStreamIO to read nbytes data to
  // the address p
  // return number of bytes successfully read
  typedef std::function<size_t(void *p, size_t nbytes)> read_cb_t;
  read_cb_t read_cb;

 public:
  ibitstream(size_t bufsize, read_cb_t _read_cb)
      : bitstream(bufsize), read_cb(_read_cb) {}
  // ensure the remaining buffer can serve at least Nbits.
  // If necessary, use the read_cb to fetch more data
  void ensureAvailableBits(size_t Nbits) {
    size_t remain_bytes = this->len - (this->p - this->buf);
    size_t remain_bits = remain_bytes * 8 - this->off;
    if (remain_bits < Nbits) {
      memmove(this->buf, this->p, remain_bytes);
      size_t n =
          read_cb(this->buf + remain_bytes, this->bufsize - remain_bytes);
      this->p = this->buf;
      this->len = remain_bytes + n;

      remain_bytes = this->len - (this->p - this->buf);
      remain_bits = remain_bytes * 8 - this->off;
      assert(remain_bits >= Nbits);
    }
  };

  // an easy way to read data from ibitstream, encode the bits as a customizable
  // type T
  template <typename T>
  T getNbits(size_t Nbits) {
    assert(sizeof(T) * 8 >= Nbits);
    ensureAvailableBits(Nbits);
    T ret = 0;
    uint8_t *d = reinterpret_cast<uint8_t *>(&ret);
    uint8_t doff = 0;
    bitscpy(this->p, this->off, d, doff, Nbits);
    return ret;
  }

  void getNbits(void *p, size_t Nbits) {
    uint8_t *dst = reinterpret_cast<uint8_t *>(p);
    uint8_t doff = 0;
    ensureAvailableBits(Nbits);
    bitscpy(this->p, this->off, dst, doff, Nbits);
  }
};
class obitstream : public bitstream {
 private:
  // write_cb is a callback that allows the BitStreamIO to write nbytes data
  // starting from address p
  typedef std::function<size_t(void *p, size_t nbytes)> write_cb_t;
  write_cb_t write_cb;

 public:
  obitstream(size_t bufsize, write_cb_t _write_cb)
      : bitstream(bufsize), write_cb(_write_cb) {}
  // TODO
};
#endif  // CL_FPGARR_BITSTREAMIO_H
