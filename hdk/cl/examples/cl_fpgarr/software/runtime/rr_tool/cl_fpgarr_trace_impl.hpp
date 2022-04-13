#ifndef CL_FPGARR_TRACE_IMPL_H
#define CL_FPGARR_TRACE_IMPL_H
/*
 * Implementation of class ChannelTraceBase
 */
ChannelTraceBase::ChannelTraceBase(const char *_name) : name(_name) {
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
bool ChannelTraceBase::findStringInArray(const char *s, size_t slen,
                                         const char *arr[], size_t arrlen) {
  for (size_t i = 0; i < arrlen; ++i) {
    if (strncmp(s, arr[i], std::min(slen, std::strlen(arr[i]))) == 0)
      return true;
  }
  return false;
}
void ChannelTraceBase::finishOnePkt(size_t loge_cnt_id) {
  loge_loge_cnt_id_vec.push_back(loge_cnt_id);
}

/*
 * Implementation of template class ChannelTrace
 */
template <size_t BITS>
void ChannelTrace<BITS>::parseOnePkt(ibitstream &ibuf, size_t loge_cnt_id) {
  pkt_t pkt = {};  // zero initialized
  uint8_t *d = pkt.data();
  ibuf.getNbits(d, wb);
  data.push_back(pkt);
  this->logb_loge_cnt_id_vec.push_back(loge_cnt_id);
  ++(this->cnt);
}
template <size_t BITS>
void ChannelTrace<BITS>::printPkt(FILE *fp, size_t i,
                                  const char *suffix) const {
  const pkt_t &pkt = data[i];
  fprintf(fp, "%" NAME_MAX_LEN "s packet[%ld]: 0x", name, i);
  for (uint8_t i = wB; i > 0; --i) {
    fprintf(fp, "%02x", pkt[i - 1]);
  }
  fputs(suffix, fp);
}
template <size_t BITS>
bool ChannelTrace<BITS>::comparePkt(size_t pktid,
                                    const ChannelTraceBase *_other) const {
  auto *other = dynamic_cast<const decltype(this)>(_other);
  const pkt_t &pkt_a = data[pktid];
  const pkt_t &pkt_b = other->data[pktid];
  return pkt_a == pkt_b;
}

/*
 * Implementation of template class VIDITrace
 */
template <typename BUSCFG>
constexpr void VIDITrace<BUSCFG>::channels_init() {
  constexpr_for<0, BUSCFG::LOGB_CNT, 1>([&](auto i) {
    channels[i] = new ChannelTrace<BUSCFG::CW[i]>(BUSCFG::LOGB_NAMES[i]);
  });
  // map loge entries to matching logb channels based on channel names
  constexpr_for<0, BUSCFG::LOGE_CNT, 1>([&](auto i) {
    loge2logb_map[i] = loge2logb_INVALID;
    constexpr_for<0, BUSCFG::LOGB_CNT, 1>([&](auto j) {
      if (strcmp(BUSCFG::LOGB_NAMES[j], BUSCFG::LOGE_NAMES[i]) == 0)
        loge2logb_map[i] = j;
    });
  });
}

template <typename BUSCFG>
typename VIDITrace<BUSCFG>::pktsize_t VIDITrace<BUSCFG>::logb_bset_push(
    const logb_bset_t &bset) {
  logb_valid_vec.push_back(bset);
  // update statitics of logging unit size
  // pktbits is in terms of bits, not aligned to PACKET_ALIGNMENT
  pktsize_t pktbits =
      BUSCFG::OFFSET_WIDTH + BUSCFG::LOGB_CNT + BUSCFG::LOGE_CNT;
  for (uint8_t i = 0; i < BUSCFG::LOGB_CNT; ++i) {
    if (bset.test(i)) pktbits += BUSCFG::CW[i];
  }
  assert(pktbits < Statistics::maxLUBits);
  stat.update_LU_dist(pktbits);
  return pktbits;
}

template <typename BUSCFG>
void VIDITrace<BUSCFG>::loge_bset_push(const loge_bset_t &bset) {
  loge_valid_vec.push_back(bset);
}
template <typename BUSCFG>
ChannelTraceBase *VIDITrace<BUSCFG>::getCH(size_t logb_chid) const {
  return channels[logb_chid];
}

template <typename BUSCFG>
void VIDITrace<BUSCFG>::parseOneLOGBChannelPkt(size_t logb_chid,
                                               ibitstream &ibits) {
  getCH(logb_chid)->parseOnePkt(ibits, loge_cnt_vec.size());
}

template <typename BUSCFG>
bool VIDITrace<BUSCFG>::tryFinishOneLOGEChannekPkt(size_t loge_chid) {
  if (loge2logb_map[loge_chid] != loge2logb_INVALID) {
    getCH(loge2logb_map[loge_chid])->finishOnePkt(loge_cnt_vec.size());
    return true;
  } else
    return false;
}

template <typename BUSCFG>
void VIDITrace<BUSCFG>::updateLOGECnt(bool isCommit) {
  if (isCommit) loge_cnt_vec.push_back(cur_loge_cnt);
  loge_bset_t &latest_loge_bset = loge_valid_vec.back();
  for (uint8_t i = 0; i < BUSCFG::LOGE_CNT; ++i) {
    if (latest_loge_bset.test(i)) {
      ++cur_loge_cnt[i];
    }
  }
}

template <typename BUSCFG>
void VIDITrace<BUSCFG>::finishOngoingPkt() {
  for (uint8_t i = 0; i < BUSCFG::LOGB_CNT; ++i) {
    ChannelTraceBase *ch_p = getCH(i);
    if (ch_p->logb_loge_cnt_id_vec.size() > ch_p->loge_loge_cnt_id_vec.size()) {
      ch_p->finishOnePkt(loge_cnt_vec.size());
    }
  }
  // the vector clock being pushed here is referred above
  loge_cnt_vec.push_back(cur_loge_cnt);
}

template <typename BUSCFG>
struct VIDITrace<BUSCFG>::Statistics {
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
  std::array<uint32_t, maxLUBits> LU_bits_dist = {};
  void update_LU_dist(int LU_bits) { LU_bits_dist[LU_bits]++; }
  // begin offsets and the size of each logging unit
  vector<size_t> start_off_vec;
  vector<size_t> pktsize_vec;
};

template <typename BUSCFG>
void VIDITrace<BUSCFG>::print_loge_cnt(FILE *fp, size_t loge_cnt_id) {
  loge_cnt_t &loge_cnt = loge_cnt_vec[loge_cnt_id];
  for (uint8_t i = 0; i < BUSCFG::LOGE_CNT; ++i) {
    fprintf(fp, "%" NAME_MAX_LEN "d ", loge_cnt[i]);
  }
  fputc('\n', fp);
}

template <typename BUSCFG>
void VIDITrace<BUSCFG>::print_header_loge_names(FILE *fp) {
  for (uint8_t i = 0; i < BUSCFG::LOGE_CNT; ++i) {
    fprintf(fp, "%" NAME_MAX_LEN "s ", BUSCFG::LOGE_NAMES[i]);
  }
  fputc('\n', fp);
}

template <typename BUSCFG>
void VIDITrace<BUSCFG>::updateStat(size_t start_off, size_t pktsize) {
  stat.start_off_vec.push_back(start_off);
  stat.pktsize_vec.push_back(pktsize);
}

template <typename BUSCFG>
void VIDITrace<BUSCFG>::dump_parsed_text(FILE *fp) {
  fputs("###############################################\n", fp);
  fputs("################### TXT Trace #################\n", fp);
  fputs("###############################################\n", fp);
  // header for LOGE
  print_header_loge_names(fp);
  // per-channel finished packet counter
  std::array<size_t, BUSCFG::LOGB_CNT> channel_idx = {};
  std::array<size_t, BUSCFG::LOGE_CNT> loge_cnt = {};
  size_t pkt_id = 0;
  size_t loge_cnt_id = 0;
  size_t pktsize_vec_acc = 0;
  auto logb_bset_it = logb_valid_vec.begin();
  auto loge_bset_it = loge_valid_vec.begin();
  assert(logb_valid_vec.size() == loge_valid_vec.size());
  for (; logb_bset_it != logb_valid_vec.end(); ++logb_bset_it, ++loge_bset_it) {
    size_t start_off = stat.start_off_vec[pkt_id];
    size_t pktsize = stat.pktsize_vec[pkt_id];
    fprintf(fp,
            "file_off %ldB, trace_off %ldB, pktsize_vec_acc %ld (%ldB), "
            "pktsize_vec %ld(%ldB), loge_cnt_id %ld\n",
            start_off, start_off - 8, pktsize_vec_acc, pktsize_vec_acc / 8,
            pktsize, pktsize / 8, pkt_id);
    pktsize_vec_acc += pktsize;
    assert(logb_bset_it->any() || loge_bset_it->any());
    // process loge first because they represent the ending of packets sent
    // before this cycle
    bool loge_matches_logb = false;
    if (loge_bset_it->any()) {
      for (uint8_t i = 0; i < BUSCFG::LOGE_CNT; ++i) {
        if (loge_bset_it->test(i)) {
          fprintf(fp, "%" NAME_MAX_LEN "s packet[%ld] ends\n",
                  BUSCFG::LOGE_NAMES[i], loge_cnt[i]);
          ++loge_cnt[i];
        }
        if (loge_bset_it->test(i) && (loge2logb_map[i] != loge2logb_INVALID)) {
          size_t loge_idx = loge2logb_map[i];
          loge_matches_logb = true;
          assert(
              channels[loge_idx]->loge_loge_cnt_id_vec[channel_idx[loge_idx]] ==
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
template <typename BUSCFG>
void VIDITrace<BUSCFG>::dump_statistics(FILE *fp) {
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

template <typename BUSCFG>
void VIDITrace<BUSCFG>::gen_report(FILE *fp, bool verbose) {
  if (verbose) {
    dump_parsed_text(fp);
    fputc('\n', fp);
  }
  dump_statistics(fp);
}

template <typename BUSCFG>
bool VIDITrace<BUSCFG>::gen_compare_report(FILE *fp, VIDITrace<BUSCFG> &other,
                                           bool verbose, bool enableHBVer2) {
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
        fprintf(fp, "Invalid channel %d (W%d) from trace file %s\n", i,
                BUSCFG::CW[i], filepath);
        return false;
      }
      if (chb == nullptr) {
        fprintf(fp, "Invalid channel %d (W%d) from trace file %s\n", i,
                BUSCFG::CW[i], other.filepath);
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
        assert(cha->isInput == chb->isInput &&
               "Input/Output definition mismatches");
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
#endif  // CL_FPGARR_TRACE_IMPL_H
