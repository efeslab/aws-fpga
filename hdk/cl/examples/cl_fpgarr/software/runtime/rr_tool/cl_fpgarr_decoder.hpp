#ifndef CL_FPGARR_DECODER_H
#define CL_FPGARR_DECODER_H
// -std=c++17 is required
#include <bitset>
#include <cassert>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <vector>
#include <algorithm>

#include "cl_fpgarr_buscfg.hpp"
#include "cl_fpgarr_utils.hpp"
#define PACKET_ALIGNMENT 8
// max length of channel name
#define NAME_MAX_LEN "7"
// max length of the property name
#define PROPNAME_MAX_LEN "10"
#define LUBITS_DIST_MAX_DIGITS "7"
#define ARRAY_LEN(x) (sizeof(x)/sizeof(x[0]))

using namespace std;

struct ChannelTraceBase {
  int cnt = 0;  // packet counter of current channel
  // id refering to vector clock that is defined between logb and loge
  vector<size_t> logb_loge_cnt_id_vec;
  // id refering to vector clock that is defined between loge and loge
  vector<size_t> loge_loge_cnt_id_vec;
  const char *name;
  bool isInput; // whether this channel is an input channel from Shell to APP

  static bool findStringInArray(const char *s, size_t slen, const char *arr[],
                                size_t arrlen) {
    for (size_t i = 0; i < arrlen; ++i) {
      if (strncmp(s, arr[i], std::min(slen, std::strlen(arr[i]))) == 0)
        return true;
    }
    return false;
  }
  ChannelTraceBase(const char *_name) : name(_name) {
    size_t intf_len = std::strchr(_name, '_') - _name;
    size_t ch_len = std::strlen(_name) - intf_len - 1;
    const char *intf_name = _name;
    const char *ch_name = _name + intf_len + 1;
    bool isInputInterface = findStringInArray(
        intf_name, intf_len, input_interfaces, ARRAY_LEN(input_interfaces));
    bool isOutputInterface = findStringInArray(
        intf_name, intf_len, output_interfaces, ARRAY_LEN(output_interfaces));
    bool isSendChannel = findStringInArray(ch_name, ch_len, send_channels,
                                           ARRAY_LEN(send_channels));
    bool isRecvChannel = findStringInArray(ch_name, ch_len, recv_channels,
                                           ARRAY_LEN(recv_channels));
    assert((isInputInterface || isOutputInterface) && "Invalid intf name");
    assert((isSendChannel || isRecvChannel) && "Invalid channel name");
    // four cases:
    // send channel from input interface: input channel
    // recv channel from output interface: input channel
    // recv channel from input interface: output channel
    // send channel from output interface: output channel
    isInput = !(isInputInterface ^ isSendChannel);
  }
  // p is a pointer to the byte that contains valid data
  // off is the offset (0~7) meaning valid data starts from which bit in that
  // byte
  // both `p` and `off` will be updated to represent the remaining valid data
  // upon return
  // loge_cnt_id is the index of the corresponding loge vector clock for this
  // packet.
  virtual void parseOnePkt(uint8_t *(&p), uint8_t &off, size_t loge_cnt_id) = 0;
  void finishOnePkt(size_t loge_cnt_id) {
    loge_loge_cnt_id_vec.push_back(loge_cnt_id);
  }
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
    this->logb_loge_cnt_id_vec.push_back(loge_cnt_id);
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

  void gen_report(FILE *fp, bool verbose=false) {
    if (verbose) {
      dump_parsed_text(fp);
      fputc('\n', fp);
    }
    dump_statistics(fp);
  }

  // enableHBVer2: enable the second definition of happens-before for output
  // channels. i.e. the transaction end-end definition. The Version 1 HB
  // definition is only defined by transaction start-end.
  // return true: equal, false: not equal
  bool gen_compare_report(FILE *fp, Decoder<BUSCFG> &other,
                          bool verbose = false, bool enableHBVer2 = false) {
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
          if (verbose) {
            fprintf(fp, "Channel %s packet[%d] content mismatch:\n", cha->name,
                    i);
            fprintf(fp, "From trace file %s, ", filepath);
            cha->printPkt(fp, i);
            fprintf(fp, "From trace file %s, ", other.filepath);
            chb->printPkt(fp, i);
          }
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
        size_t loge_cnt_vec_idx_a, loge_cnt_vec_idx_b;
        const char *HBVer_str;
        if (enableHBVer2) {
          assert(cha->isInput == chb->isInput && "Input/Output definition mismatches");
          if (cha->isInput) {
            loge_cnt_vec_idx_a = cha->logb_loge_cnt_id_vec[i];
            loge_cnt_vec_idx_b = chb->logb_loge_cnt_id_vec[i];
            HBVer_str = "Start-End";
          } else {
            loge_cnt_vec_idx_a = cha->loge_loge_cnt_id_vec[i];
            loge_cnt_vec_idx_b = chb->loge_loge_cnt_id_vec[i];
            HBVer_str = "End-End";
          }
        } else {
          loge_cnt_vec_idx_a = cha->logb_loge_cnt_id_vec[i];
          loge_cnt_vec_idx_b = chb->logb_loge_cnt_id_vec[i];
            HBVer_str = "Start-End";
        }
        loge_cnt_t loge_cnt_a = loge_cnt_vec[loge_cnt_vec_idx_a];
        loge_cnt_t loge_cnt_b = other.loge_cnt_vec[loge_cnt_vec_idx_b];
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
        if (verbose) {
          if (mismatch)
            fprintf(fp, "Channel %s packet[%d] happen-before[%s] mismatch:\n",
                    cha->name, i, HBVer_str);
          if (violation)
            fprintf(fp, "Channel %s packet[%d] happen-before[%s] violation:\n",
                    cha->name, i, HBVer_str);
          if (mismatch || violation) {
            print_header_loge_names(fp);
            fprintf(fp, "From trace file %s:\n", filepath);
            print_loge_cnt(fp, loge_cnt_vec_idx_a);
            fprintf(fp, "From trace file %s:\n", other.filepath);
            other.print_loge_cnt(fp, loge_cnt_vec_idx_b);
          }
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
  // this is for all LOGB channels, channels that may start new transactions
  std::array<ChannelTraceBase *, BUSCFG::LOGB_CNT> channels;
  // this is a mapping from loge entries to the corresponding logb channel, if
  // the loge channel may start new transactions as well.
  // valid value is [0..BUSCFG::LOGB_CNT)
  static constexpr size_t loge2logb_INVALID = BUSCFG::LOGB_CNT;
  std::array<size_t, BUSCFG::LOGE_CNT> loge2logb_map;
  FILE *fp = nullptr;
  const char *filepath = nullptr;
  trace_size_t trace_bits;
  // the current packet counter of all channels (waiting to be pushed into
  // loge_pkt_cnt)
  // NOTE: should be zero initialized
  loge_cnt_t cur_loge_cnt = {};
  // the (finished) packet counter of all channels when a packet comes
  vector<loge_cnt_t> loge_cnt_vec;
  // logb_valid_vec[i] contains the logb_valid of logging_unit[i] in the trace
  vector<bitset<BUSCFG::LOGB_CNT>> logb_valid_vec;
  // loge_valid_vec[i] contains the loge_valid of logging_unit[i] in the trace
  vector<bitset<BUSCFG::LOGE_CNT>> loge_valid_vec;
  vector<size_t> start_off;
  vector<size_t> pktsize_vec;

  constexpr void channels_init() {
    constexpr_for<0, BUSCFG::LOGB_CNT, 1>([&](auto i) {
      channels[i] = new ChannelTrace<BUSCFG::CW[i]>(BUSCFG::LOGB_NAMES[i]);
    });
    // map loge entries to matching logb channels based on channel names
    constexpr_for<0, BUSCFG::LOGE_CNT, 1>([&](auto i) {
      loge2logb_map[i] = loge2logb_INVALID;
      constexpr_for<0, BUSCFG::LOGB_CNT, 1>([&](auto j){
        if (strcmp(BUSCFG::LOGB_NAMES[j], BUSCFG::LOGE_NAMES[i]) == 0)
          loge2logb_map[i] = j;
      });
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

      // pktbits is in terms of bits, not aligned to PACKET_ALIGNMENT
      pktsize_t pktbits =
          BUSCFG::OFFSET_WIDTH + BUSCFG::LOGB_CNT + BUSCFG::LOGE_CNT;
      // processing logb
      bitset<BUSCFG::LOGB_CNT> logb_valid_bset;
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
      // processing loge
      bitset<BUSCFG::LOGE_CNT> loge_valid_bset;
      bool loge_matches_logb = false;
      for (uint8_t i = 0; i < BUSCFG::LOGE_CNT; ++i) {
        if (loge_valid & (0x1 << i)) {
          loge_valid_bset.set(i);
          if (loge2logb_map[i] != loge2logb_INVALID) {
            channels[loge2logb_map[i]]->finishOnePkt(loge_cnt_vec.size());
            loge_matches_logb = true;
          }
        }
      }
      loge_valid_vec.push_back(loge_valid_bset);
      // maintain loge vector clock
      if (logb_valid_bset.any() || loge_matches_logb) {
        // only commit the loge vector clock if the vector clock from previous
        // logging units is referenced in the above channel packet processing,
        // which is:
        //  1. at least one new transaction started on LOGB channels
        //  OR
        //  2. at least one transaction ended on LOGB channels
        loge_cnt_vec.push_back(cur_loge_cnt);
      }
      // note that the logb and loge processed above only refer to the vector
      // clock excluding this logging unit's loge_valid.
      // We update loge_valid after a packet is processed.
      update_loge_cnt(loge_valid);
      assert(alignment_padding_size < 8);
      uint8_t eat_padding = getNbits<uint8_t>(alignment_padding_size);
      parsed_bits += pktsize;

      // update statistics
      assert(pktsize == GET_ALIGNED_BITS(pktbits));
      assert(pktbits < Statistics::maxLUBits);
      stat.update_LU_dist(pktbits);
    }
    // commit the dangling loge vector clock even if it is not going to be
    // referenced. This is to get access to the total loge packet counter.
    loge_cnt_vec.push_back(cur_loge_cnt);
    for (uint8_t i = 0; i < BUSCFG::LOGB_CNT; ++i) {
      if (channels[i]->logb_loge_cnt_id_vec.size() > channels[i]->loge_loge_cnt_id_vec.size()) {
        // trace ends but some packets do not finish, this happens because the
        // happens-before encoder still caches the last loge
        channels[i]->finishOnePkt(loge_cnt_vec.size());
      }
    }
  }

  void print_loge_cnt(FILE *fp, size_t loge_cnt_id) {
    loge_cnt_t &loge_cnt = loge_cnt_vec[loge_cnt_id];
    for (uint8_t i = 0; i < BUSCFG::LOGE_CNT; ++i) {
      fprintf(fp, "%" NAME_MAX_LEN "d ", loge_cnt[i]);
    }
    fputc('\n', fp);
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
    // per-channel finished packet counter
    array<size_t, BUSCFG::LOGB_CNT> channel_idx = {};
    array<size_t, BUSCFG::LOGE_CNT> loge_cnt = {};
    size_t pkt_id = 0;
    size_t loge_cnt_id = 0;
    size_t pktsize_vec_acc = 0;
    auto logb_bset_it = logb_valid_vec.begin();
    auto loge_bset_it = loge_valid_vec.begin();
    assert(logb_valid_vec.size() == loge_valid_vec.size());
    for (; logb_bset_it != logb_valid_vec.end();
         ++logb_bset_it, ++loge_bset_it) {
      fprintf(fp,
              "file_off %ldB, trace_off %ldB, pktsize_vec_acc %ld (%ldB), "
              "pktsize_vec %ld(%ldB), loge_cnt_id %ld\n",
              start_off[pkt_id], start_off[pkt_id] - 8,
              pktsize_vec_acc, pktsize_vec_acc / 8, pktsize_vec[pkt_id],
              pktsize_vec[pkt_id] / 8, pkt_id);
      pktsize_vec_acc += pktsize_vec[pkt_id];
      assert(logb_bset_it->any() || loge_bset_it->any());
      // process loge first because they represent the ending of packets sent
      // before this cycle
      bool loge_matches_logb = false;
      if (loge_bset_it->any()) {
        for (uint8_t i = 0; i < BUSCFG::LOGE_CNT; ++i) {
          if (loge_bset_it->test(i)) {
            fprintf(fp, "%" NAME_MAX_LEN "s packet[%ld] ends\n", BUSCFG::LOGE_NAMES[i], loge_cnt[i]);
            ++loge_cnt[i];
          }
          if (loge_bset_it->test(i) &&
              (loge2logb_map[i] != loge2logb_INVALID)) {
            size_t loge_idx = loge2logb_map[i];
            loge_matches_logb = true;
            assert(channels[loge_idx]
                       ->loge_loge_cnt_id_vec[channel_idx[loge_idx]] ==
                   loge_cnt_id);
            // only advance per-channel packet counter after that packet is
            // finished
            // Important assumption: one channel cannot start the next packet
            // without finishing the previous packet
            ++channel_idx[loge_idx];
          }
        }
      }
      if (logb_bset_it->any()) {
        for (uint8_t i = 0; i < BUSCFG::LOGB_CNT; ++i) {
          if (logb_bset_it->test(i)) {
            channels[i]->printPkt(fp, channel_idx[i]);
            assert(channels[i]->logb_loge_cnt_id_vec[channel_idx[i]] ==
                   loge_cnt_id);
          }
        }
      }
      if (logb_bset_it->any() || loge_bset_it->any()) {
        print_loge_cnt(fp, loge_cnt_id);
      }
      if (logb_bset_it->any() || loge_matches_logb) {
        // refer to the corresponding logic in parse_trace()
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
    // LOGB customized properties
    fprintf(fp, "%" PROPNAME_MAX_LEN "s| ", "logb_cnt");
    for (uint8_t i = 0; i < BUSCFG::LOGB_CNT; ++i) {
      fprintf(fp, "%" NAME_MAX_LEN "d| ", channels[i]->cnt);
    }
    fputc('\n', fp);

    fputs("## per loge\n", fp);
    fprintf(fp, "%" PROPNAME_MAX_LEN "s| ", "Prop");
    // header for LOGB
    for (uint8_t i = 0; i < BUSCFG::LOGE_CNT; ++i) {
      fprintf(fp, "%" NAME_MAX_LEN "s| ", BUSCFG::LOGE_NAMES[i]);
    }
    fputc('\n', fp);
    fputs("----------------------------------------------------------\n", fp);
    // LOGE customized properties
    fprintf(fp, "%" PROPNAME_MAX_LEN "s| ", "loge_cnt");
    for (uint8_t i = 0; i < BUSCFG::LOGE_CNT; ++i) {
      fprintf(fp, "%" NAME_MAX_LEN "d| ", loge_cnt_vec.back()[i]);
    }
    fputc('\n', fp);
  }
};
#endif  // CL_FPGARR_DECODER_H
