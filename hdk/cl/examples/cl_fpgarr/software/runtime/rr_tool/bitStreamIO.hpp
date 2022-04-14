#ifndef CL_FPGARR_BITSTREAMIO_H
#define CL_FPGARR_BITSTREAMIO_H
#include <algorithm>
#include <cstdint>
#include <cstring>
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
  template <class T>
  static void bitscpy(T *(&src), uint8_t &srcoff, uint8_t *(&dst),
                      uint8_t &dstoff, int bits) {
    // only allow template instantiation with two specific uint8_t type (one
    // normal, one with const qualifier)
    // I think there should be a template because with and without the const
    // qualifier are really different.
    // When updating the src pointer reference, a const pointer can only be
    // updated to another const pointer, while non-const pointer can only be
    // updated to another non-const pointer.
    // Such property can only be expressed with two different types and I have
    // to do a `const_cast` if I want to only have one version of bitscpy.
    // I decided to not do a `const_cast`
    static_assert(std::is_same<T, uint8_t>::value ||
                  std::is_same<T, const uint8_t>::value);
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
      if (dstoff == 0)
        *dst = 0;  // initialize next full-byte to write with zero
      (*dst) |= copy_data << dstoff;  // note this |=, dst should init zero
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
  // bytes to bits
  static size_t Bs2bs(size_t Nbytes) { return Nbytes * 8; }

 public:
  bitstream(size_t _bufsize)
      : buf(new uint8_t[_bufsize](/*zero initialized*/)), bufsize(_bufsize) {}
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
  // Illustration of buf, len, p, off
  // |<--consumed data-->|<-valid data to read->|<---invalid--->|
  // [----------------------------------------------------------]
  // ⌃                   ⌃                      ⌃               ⌃
  // buf                 p                   buf+len         buf+bufsize
  // off represents bit-level offset of the read pointer inside *p
  //
  // ensure the remaining buffer can serve at least Nbits.
  // If necessary, use the read_cb to fetch more data
  void ensureAvailableBits(size_t Nbits) {
    // remain bits are valid data
    size_t remain_bytes = this->len - (this->p - this->buf);
    size_t remain_bits = Bs2bs(remain_bytes) - this->off;
    // the minimum available bits in a full buffer (when off != 0) must greater
    // than requested Nbits
    assert((Nbits < Bs2bs(this->bufsize - 1)) && "Invalid read request Nbits");
    if (remain_bits < Nbits) {
      memmove(this->buf, this->p, remain_bytes);
      size_t n =
          read_cb(this->buf + remain_bytes, this->bufsize - remain_bytes);
      this->p = this->buf;
      this->len = remain_bytes + n;

      remain_bytes = this->len - (this->p - this->buf);
      remain_bits = Bs2bs(remain_bytes) - this->off;
      assert(remain_bits >= Nbits);
    }
  };

  // an easy way to read data from ibitstream, encode the bits as a customizable
  // type T
  template <typename T>
  T getNbits(size_t Nbits) {
    assert(Bs2bs(sizeof(T)) >= Nbits);
    ensureAvailableBits(Nbits);
    T ret = 0;
    uint8_t *d = reinterpret_cast<uint8_t *>(&ret);
    uint8_t doff = 0;
    bitscpy(this->p, this->off, d, doff, Nbits);
    return ret;
  }
  // an generic way to read data from ibitstream to an arbitrary memory address
  void getNbits_ptr(void *p, size_t Nbits) {
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
  ~obitstream() { flush(); }
  // Illustration of buf, len, p, off
  // |<--valid data to write back-->|<-----available buffer---->|
  // [----------------------------------------------------------]
  // ⌃             ⌃                ⌃                           ⌃
  // buf           |                p                        buf+bufsize
  //  flushed ->buf+n<--valid data-->
  //
  // off represents bit-level offset of the write pointer inside *p
  // len is not used
  //
  // ensure the remaining buffer can hold at least Nbits
  // If necessary, use the write_cb to flush current buffer
  void ensureAvailableBits(size_t Nbits) {
    // remain bytes are available buffer including *p
    // remain bits are available empty buffer excluding off bits in *p
    size_t remain_bytes = this->bufsize - (this->p - this->buf);
    size_t remain_bits = Bs2bs(remain_bytes) - this->off;
    // the minimum available bits in an empty buffer (when off != 0) must
    // greater than requested Nbits
    assert((Nbits < Bs2bs(this->bufsize - 1)) && "Invalid write request Nbits");
    if (remain_bits < Nbits) {
      size_t full_bytes = this->p - this->buf;
      size_t n = write_cb(this->buf, full_bytes);
      // + 1 is to copy the partial byte at *p
      memmove(this->buf, this->buf + n, this->p - this->buf - n + 1);
      this->p = this->p - n;

      remain_bytes = this->bufsize - (this->p - this->buf);
      remain_bits = Bs2bs(remain_bytes) - this->off;
      assert(remain_bits >= Nbits);
    }
  }

  // an easy way to write data to obitstream, the bits are encoded as a
  // customizable type T
  template <typename T>
  void putNbits(T t, size_t Nbits) {
    assert(Bs2bs(sizeof(T)) >= Nbits);
    ensureAvailableBits(Nbits);
    uint8_t *src = reinterpret_cast<uint8_t *>(&t);
    uint8_t src_off = 0;
    bitscpy(src, src_off, this->p, this->off, Nbits);
  }
  // an generic way to write data to obitstream from an arbitrary memory address
  void putNbits_ptr(const void *p, size_t Nbits) {
    const uint8_t *src = static_cast<const uint8_t *>(p);
    uint8_t srcoff = 0;
    ensureAvailableBits(Nbits);
    bitscpy(src, srcoff, this->p, this->off, Nbits);
  }
  void flush() {
    if (this->off > 0) {
      // partial byte, flush this byte with zero
      putNbits(uint8_t(0), 8 - this->off);
    }
    size_t full_bytes = this->p - this->buf;
    size_t n = write_cb(this->buf, full_bytes);
    assert(n == full_bytes);
    this->p = this->buf;
  }
};
#endif  // CL_FPGARR_BITSTREAMIO_H
