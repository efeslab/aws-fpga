#ifndef CL_FPGARR_DECODER_H
#define CL_FPGARR_DECODER_H
// -std=c++17 is required
#include <bitset>
#include <cassert>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <vector>

#include "cl_fpgarr_buscfg.hpp"
#include "cl_fpgarr_utils.hpp"
#define PACKET_ALIGNMENT 8
#define NAME_MAX_LEN "7"
#define PROPNAME_MAX_LEN "10"
#define LUBITS_DIST_MAX_DIGITS "7"

using namespace std;

struct ChannelTraceBase {
  int cnt = 0;  // packet counter of current channel
  vector<size_t> loge_cnt_id_vec;
  const char *name;

  ChannelTraceBase(const char *_name) : name(_name) {}
  // p is a pointer to the byte that contains valid data
  // off is the offset (0~7) meaning valid data starts from which bit in that
  // byte
  // both `p` and `off` will be updated to represent the remaining valid data
  // upon return
  // Assumption: loge_valid has been updated before calling this parseOnePkt
  virtual void parseOnePkt(uint8_t *(&p), uint8_t &off, size_t loge_cnt_id) = 0;
  virtual void printPkt(FILE *fp, size_t i,
                        const char *suffix = "\n") const = 0;
  virtual bool comparePkt(size_t pktid,
                          const ChannelTraceBase *other) const = 0;
  virtual void test() = 0;
};

constexpr int GET_ALIGNED_BITS(int x) {
  return (x + PACKET_ALIGNMENT - 1) & (~(PACKET_ALIGNMENT - 1));
}
constexpr int GET_ALIGNED_BYTES(int x) {
  return (x + PACKET_ALIGNMENT - 1) / PACKET_ALIGNMENT;
}

template <size_t BITS>
struct ChannelTrace : public ChannelTraceBase {
  static constexpr const int wb = BITS;  // width in terms of bits
  static constexpr const int wB =
      GET_ALIGNED_BYTES(BITS);  // width in terms of bytes
  typedef array<uint8_t, wB> pkt_t;
  // the content of each packet in this channel
  vector<pkt_t> data;

  ChannelTrace(const char *_name) : ChannelTraceBase(_name) {}
  virtual void test() {
    printf("this is channel %s having %d bits (%d bytes)\n", name, wb, wB);
  }
  virtual void parseOnePkt(uint8_t *(&p), uint8_t &off,
                           size_t loge_cnt_id) override {
    pkt_t pkt = {};  // zero initialized
    uint8_t *d = pkt.data();
    uint8_t doff = 0;
    bitscpy(p, off, d, doff, wb);
    data.push_back(pkt);
    this->loge_cnt_id_vec.push_back(loge_cnt_id);
    ++(this->cnt);
  }

  void printPkt(FILE *fp, size_t i, const char *suffix = "\n") const override {
    const pkt_t &pkt = data[i];
    fprintf(fp, "%" NAME_MAX_LEN "s packet[%ld]: 0x", name, i);
    for (uint8_t i = wB; i > 0; --i) {
      fprintf(fp, "%02x", pkt[i - 1]);
    }
    fputs(suffix, fp);
  }

  bool comparePkt(size_t pktid, const ChannelTraceBase *_other) const override {
    auto *other = dynamic_cast<const decltype(this)>(_other);
    const pkt_t &pkt_a = data[pktid];
    const pkt_t &pkt_b = other->data[pktid];
    return pkt_a == pkt_b;
  }
};

template <typename BUSCFG>
class Decoder {
  // determine what type to use logb_valid
  typedef uint16_t logb_valid_t;
  // determine what type to use for loge_valid
  typedef uint32_t loge_valid_t;
  // determine what type to use for packet(logging unit) size
  typedef uint16_t pktsize_t;
  // the type to count how many packets as finished in each channel
  typedef uint32_t loge_pkt_cnt_t;
  // the type to track packet counters of all channels
  typedef array<loge_pkt_cnt_t, BUSCFG::LOGE_CNT> loge_cnt_t;

  typedef uint64_t trace_size_t;

 public:
  Decoder(const char *_filepath) : filepath(_filepath) {
    channels_init();
    fp = fopen(_filepath, "r");
    parse_trace();
  }
  ~Decoder() {
    if (fp) fclose(fp);
    for (auto it : channels) {
      delete it;
    }
  }

  void gen_report(FILE *fp) {
    dump_parsed_text(fp);
    fputc('\n', fp);
    dump_statistics(fp);
  }

  // return true: equal, false: not equal
  bool gen_compare_report(FILE *fp, Decoder<BUSCFG> &other) {
    size_t hb_mismatch_cnt = 0;
    size_t violation_cnt = 0;
    size_t content_mismatch_cnt = 0;
    size_t pkt_cnt = 0;
    fprintf(fp,
            "Checking whether the happen-before in trace %s is obeyed in "
            "trace %s\n",
            filepath, other.filepath);
    // compare every channel in each trace
    for (uint8_t i = 0; i < BUSCFG::LOGB_CNT; ++i) {
      const auto *cha = channels[i];
      const auto *chb = other.channels[i];
      {  // Sanity Check
        if (cha == nullptr) {
          fprintf(fp, "Invalid channel %d (W%d) from trace file %s\n",
                  i, BUSCFG::CW[i], filepath);
          return false;
        }
        if (chb == nullptr) {
          fprintf(fp, "Invalid channel %d (W%d) from trace file %s\n",
                  i, BUSCFG::CW[i], other.filepath);
          return false;
        }
        if (cha->cnt != chb->cnt) {
          fprintf(fp,
                  "Channel %s packet count mismatches: %d packets from trace "
                  "file %s, %d packets from trace file %s\n",
                  cha->name, cha->cnt, filepath, chb->cnt, other.filepath);
          return false;
        }
      }
      // Compare every packet in the channel
      for (int i = 0; i < cha->cnt; ++i) {
        // compare packet content
        if (!cha->comparePkt(i, chb)) {
          fprintf(fp, "Channel %s packet[%d] content mismatch:\n", cha->name,
                  i);
          fprintf(fp, "From trace file %s, ", filepath);
          cha->printPkt(fp, i);
          fprintf(fp, "From trace file %s, ", other.filepath);
          chb->printPkt(fp, i);
          ++content_mismatch_cnt;
        }
        // compare the happen-before
        // Three cases:
        // 1. Exact match: For the start of each new packet, previous packets
        //   finished in each channel in traceA, have also finished in each
        //   channel in traceB and there are no more packets finished in traceB
        //   that had not finished in traceA.
        // 2. OK match: previous packets finished in traceA have also finished
        //   in traceB, but there are additional packets finished in traceB that
        //   had not finished in traceA.
        // 3. Violation: some of the previous packets finished in traceA have
        //   not finished in traceB.
        // (i.e. For each packet from current channel
        // in each trace, do they have the same number of packets finish before
        // the start of current packet?)
        loge_cnt_t loge_cnt_a = loge_cnt_vec[cha->loge_cnt_id_vec[i]];
        loge_cnt_t loge_cnt_b = other.loge_cnt_vec[chb->loge_cnt_id_vec[i]];
        bool mismatch = false;
        bool violation = false;
        if (loge_cnt_a == loge_cnt_b) {
          // exact match
          continue;
        } else if (loge_cnt_a <= loge_cnt_b) {
          // OK match
          ++hb_mismatch_cnt;
          mismatch = true;
        } else {
          // Violation
          ++violation_cnt;
          violation = true;
        }
        if (mismatch)
          fprintf(fp, "Channel %s packet[%d] happen-before mismatch:\n",
                  cha->name, i);
        if (violation)
          fprintf(fp, "Channel %s packet[%d] happen-before violation:\n",
                  cha->name, i);
        if (mismatch || violation) {
          print_header_loge_names(fp);
          fprintf(fp, "From trace file %s:\n", filepath);
          print_loge_cnt(fp, cha->loge_cnt_id_vec[i]);
          fprintf(fp, "From trace file %s:\n", other.filepath);
          other.print_loge_cnt(fp, chb->loge_cnt_id_vec[i]);
        }
      }
      pkt_cnt += cha->cnt;
    }
    fprintf(fp,
            "Total packets %ld, Total HB mismatches: %ld(%f%%), "
            "Total violations: %ld(%lf%%), Total content mismatches: %ld(%f%%)\n",
            pkt_cnt, hb_mismatch_cnt, (double)hb_mismatch_cnt / pkt_cnt * 100,
            violation_cnt, (double)violation_cnt / pkt_cnt * 100,
            content_mismatch_cnt, (double)content_mismatch_cnt / pkt_cnt * 100);
    return true;
  }

 private:  // utils
  template <size_t bufsize>
  struct BufferMgr {
    uint8_t buf[bufsize];
    size_t len = 0;  // len of valid bytes
    uint8_t *p = buf;
    uint8_t off = 0;
  };
  static constexpr int BUFSIZE = 4096;
  BufferMgr<BUFSIZE> buf;
  void ensureValidBits(size_t Nbits) {
    size_t remain_bytes = buf.len - (buf.p - buf.buf);
    size_t remain_bits = remain_bytes * 8 - buf.off;
    if (remain_bits < Nbits) {
      memmove(buf.buf, buf.p, remain_bytes);
      size_t n = fread(buf.buf + remain_bytes, 1, BUFSIZE - remain_bytes, fp);
      buf.p = buf.buf;
      buf.len = remain_bytes + n;

      remain_bytes = buf.len - (buf.p - buf.buf);
      remain_bits = remain_bytes * 8 - buf.off;
      assert(remain_bits >= Nbits);
    }
  }

  struct Statistics {
    static constexpr int getCWsum() {
      int sum = 0;
      for (auto w : BUSCFG::CW) {
        sum += w;
      }
      return sum;
    }
    static constexpr int CWSUM = getCWsum();
    static constexpr int maxLUBits =
        CWSUM + BUSCFG::OFFSET_WIDTH + BUSCFG::LOGB_CNT + BUSCFG::LOGE_CNT;
    // distribution of the size of the logging units
    array<uint32_t, maxLUBits> LU_bits_dist = {};
    void update_LU_dist(int LU_bits) { LU_bits_dist[LU_bits]++; }
  };
  Statistics stat;

 private:
  std::array<ChannelTraceBase *, BUSCFG::LOGB_CNT> channels;
  FILE *fp = nullptr;
  const char *filepath = nullptr;
  trace_size_t trace_bits;
  // the current packet counter of all channels (waiting to be pushed into
  // loge_pkt_cnt)
  // NOTE: should be zero initialized
  loge_cnt_t cur_loge_cnt = {};
  // the (finished) packet counter of all channels when a packet comes
  vector<loge_cnt_t> loge_cnt_vec;
  // logb_valid_vec contains logb_valid of all logging units in the trace
  vector<bitset<BUSCFG::LOGB_CNT>> logb_valid_vec;
  vector<size_t> start_off;
  vector<size_t> pktsize_vec;

  constexpr void channels_init() {
    constexpr_for<0, BUSCFG::LOGB_CNT, 1>([&](auto i) {
      channels[i] = new ChannelTrace<BUSCFG::CW[i]>(BUSCFG::LOGB_NAMES[i]);
    });
  }

  void update_loge_cnt(loge_valid_t loge_valid) {
    for (uint8_t i = 0; i < BUSCFG::LOGE_CNT; ++i) {
      if (loge_valid & 0x1) {
        ++cur_loge_cnt[i];
      }
      loge_valid >>= 1;
    }
  }

  template <typename T>
  T getNbits(size_t Nbits) {
    uint8_t *(&p) = buf.p;
    uint8_t &off = buf.off;
    assert(sizeof(T) * 8 >= Nbits);
    ensureValidBits(Nbits);
    T ret = 0;
    uint8_t *d = reinterpret_cast<uint8_t *>(&ret);
    uint8_t doff = 0;
    bitscpy(p, off, d, doff, Nbits);
    return ret;
  }

  void parse_trace() {
    assert(fp && "file open failed");
    assert(fread(&trace_bits, sizeof(trace_bits), 1, fp) == 1);

    static_assert(*std::max_element(BUSCFG::CW.cbegin(), BUSCFG::CW.cend()) <
                  BUFSIZE * 8);
    size_t parsed_bits = 0;
    while (parsed_bits < trace_bits) {
      // pktsize is in terms of bits, aligned to PACKET_ALIGNMENT
      pktsize_t pktsize = getNbits<pktsize_t>(BUSCFG::OFFSET_WIDTH);
      // {{{ for debug
      assert((pktsize%8) == 0);
      assert((parsed_bits % 8) == 0);
      start_off.push_back(parsed_bits/8 + 8);
      pktsize_vec.push_back(pktsize);
      // }}} end of debug
      logb_valid_t logb_valid = getNbits<logb_valid_t>(BUSCFG::LOGB_CNT);
      loge_valid_t loge_valid = getNbits<loge_valid_t>(BUSCFG::LOGE_CNT);
      // aligned to PACKET_ALIGNMENT
      pktsize_t alignment_padding_size =
          pktsize - BUSCFG::OFFSET_WIDTH - BUSCFG::LOGB_CNT - BUSCFG::LOGE_CNT;
      update_loge_cnt(loge_valid);
      bitset<BUSCFG::LOGB_CNT> logb_valid_bset;

      // pktbits is in terms of bits, not aligned to PACKET_ALIGNMENT
      pktsize_t pktbits =
          BUSCFG::OFFSET_WIDTH + BUSCFG::LOGB_CNT + BUSCFG::LOGE_CNT;
      for (uint8_t i = 0; i < BUSCFG::LOGB_CNT; ++i) {
        if (logb_valid & (0x1 << i)) {
          ensureValidBits(BUSCFG::CW[i]);
          channels[i]->parseOnePkt(buf.p, buf.off, loge_cnt_vec.size());
          alignment_padding_size -= BUSCFG::CW[i];
          logb_valid_bset.set(i);
          pktbits += BUSCFG::CW[i];
        }
      }
      logb_valid_vec.push_back(logb_valid_bset);
      if (logb_valid_bset.any()) loge_cnt_vec.push_back(cur_loge_cnt);
      assert(alignment_padding_size < 8);
      uint8_t eat_padding = getNbits<uint8_t>(alignment_padding_size);
      parsed_bits += pktsize;

      // update statistics
      assert(pktsize == GET_ALIGNED_BITS(pktbits));
      assert(pktbits < Statistics::maxLUBits);
      stat.update_LU_dist(pktbits);
    }
  }

  void print_loge_cnt(FILE *fp, size_t loge_cnt_id) {
    loge_cnt_t &loge_cnt = loge_cnt_vec[loge_cnt_id];
    for (uint8_t i = 0; i < BUSCFG::LOGE_CNT; ++i) {
      fprintf(fp, "%" NAME_MAX_LEN "d ", loge_cnt[i]);
    }
    fputc('\n', fp);
    if (loge_cnt[15] * 8 < loge_cnt[16])
      fprintf(fp, "BUGGY pcim AW * 2 < W?\n");
  }

  void print_header_loge_names(FILE *fp) {
    for (uint8_t i = 0; i < BUSCFG::LOGE_CNT; ++i) {
      fprintf(fp, "%" NAME_MAX_LEN "s ", BUSCFG::LOGE_NAMES[i]);
    }
    fputc('\n', fp);
  }

  void dump_parsed_text(FILE *fp) {
    fputs("###############################################\n", fp);
    fputs("################### TXT Trace #################\n", fp);
    fputs("###############################################\n", fp);
    // header for LOGE
    print_header_loge_names(fp);
    array<size_t, BUSCFG::LOGB_CNT> channel_idx = {};
    size_t pkt_id = 0;
    size_t loge_cnt_id = 0;
    size_t pktsize_vec_acc = 0;
    for (auto bset : logb_valid_vec) {
      fprintf(fp,
              "file_off %ldB, trace_off %ldB, pktsize_vec_acc %ld (%ldB), "
              "pktsize_vec %ld(%ldB), loge_cnt_id %ld\n",
              start_off[pkt_id], start_off[pkt_id] - 8,
              pktsize_vec_acc, pktsize_vec_acc / 8, pktsize_vec[pkt_id],
              pktsize_vec[pkt_id] / 8, pkt_id);
      pktsize_vec_acc += pktsize_vec[pkt_id];
      if (bset.any()) {
        for (uint8_t i = 0; i < BUSCFG::LOGB_CNT; ++i) {
          if (bset.test(i)) {
            channels[i]->printPkt(fp, channel_idx[i]);
            assert(channels[i]->loge_cnt_id_vec[channel_idx[i]] == loge_cnt_id);
            ++channel_idx[i];
          }
        }
        print_loge_cnt(fp, loge_cnt_id);
        ++loge_cnt_id;
      }
      ++pkt_id;
    }
  }

  void dump_statistics(FILE *fp) {
    fputs("###############################################\n", fp);
    fputs("################### Statistics ################\n", fp);
    fputs("###############################################\n", fp);
    fprintf(fp, "In total %ld logging units\n", logb_valid_vec.size());

    fputs("## logging unit size distribution\n", fp);
    fprintf(fp, "%" PROPNAME_MAX_LEN "s: ", "LU Bits");
    for (uint32_t i = 0; i < Statistics::maxLUBits; ++i) {
      if (stat.LU_bits_dist[i]) {
        fprintf(fp, "%" LUBITS_DIST_MAX_DIGITS "d ", i);
      }
    }
    fputc('\n', fp);
    fprintf(fp, "%" PROPNAME_MAX_LEN "s: ", "LU freq");
    for (uint32_t i = 0; i < Statistics::maxLUBits; ++i) {
      if (stat.LU_bits_dist[i]) {
        fprintf(fp, "%" LUBITS_DIST_MAX_DIGITS "d ", stat.LU_bits_dist[i]);
      }
    }
    fputc('\n', fp);

    fputs("## per logb\n", fp);
    fprintf(fp, "%" PROPNAME_MAX_LEN "s| ", "Prop");
    // header for LOGB
    for (uint8_t i = 0; i < BUSCFG::LOGB_CNT; ++i) {
      fprintf(fp, "%" NAME_MAX_LEN "s| ", BUSCFG::LOGB_NAMES[i]);
    }
    fputc('\n', fp);
    fputs("----------------------------------------------------------\n", fp);
    fprintf(fp, "%" PROPNAME_MAX_LEN "s| ", "logb_cnt");
    for (uint8_t i = 0; i < BUSCFG::LOGB_CNT; ++i) {
      fprintf(fp, "%" NAME_MAX_LEN "d| ", channels[i]->cnt);
    }
    fputc('\n', fp);
  }
};
#endif  // CL_FPGARR_DECODER_H
