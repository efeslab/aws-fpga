#ifndef CL_FPGARR_TRACE_IMPL_H
#define CL_FPGARR_TRACE_IMPL_H
/*
 * Implementation of class ChannelTraceBase
 */
ChannelTraceBase::ChannelTraceBase(const char *_name) : name(_name) {
  // assuming channel name are encoded as "{interface_name}_{channel_type}"
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
  tid = F1PktType::getType(intf_name, intf_len, ch_name, ch_len);
}
void ChannelTraceBase::startOnePkt(size_t loge_cnt_id) {
  logb_loge_cnt_id_vec.push_back(loge_cnt_id);
}
void ChannelTraceBase::finishOnePkt(size_t loge_cnt_id) {
  loge_loge_cnt_id_vec.push_back(loge_cnt_id);
}
void ChannelTraceBase::clearHBEncoding() {
  logb_loge_cnt_id_vec.clear();
  loge_loge_cnt_id_vec.clear();
}

/*
 * Implementation of template class ChannelTrace
 */
template <size_t BITS>
void ChannelTrace<BITS>::parseOnePkt(ibitstream &ibuf) {
  pkt_t pkt = {};  // zero initialized
  uint8_t *d = pkt.data();
  ibuf.getNbits_ptr(d, wb);
  data.push_back(pkt);
  ++(this->cnt);
}
template <size_t BITS>
void ChannelTrace<BITS>::printPkt(FILE *fp, size_t i,
                                  const char *suffix) const {
  const pkt_t &pkt = data[i];
  fprintf(fp, "%" NAME_MAX_LEN "s packet[%ld]: ", name, i);
  // struct representation of a pkt content
  F1ChannelPkt_t s_pkt(tid, pkt.data(), wB);
  s_pkt.printPkt(fp);
  fputs(suffix, fp);
}
template <size_t BITS>
void ChannelTrace<BITS>::getDecodedPkt(size_t pktid,
                                       F1ChannelPkt_t &pkt) const {
  assert(pktid <= data.size());
  pkt.refill(tid, data[pktid].data(), wB);
}
template <size_t BITS>
void ChannelTrace<BITS>::exportPkt(obitstream &obits, size_t pktid) const {
  assert(pktid < data.size());
  obits.putNbits_ptr(data[pktid].data(), wb);
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
  constexpr_for<0, BUSCFG::LOGB_CNT, 1>([&](auto i) {
    LOGB_name2id[std::string(BUSCFG::LOGB_NAMES[i])] = i;
  });
  constexpr_for<0, BUSCFG::LOGE_CNT, 1>([&](auto i) {
    LOGE_name2id[std::string(BUSCFG::LOGE_NAMES[i])] = i;
  });
}

template <typename BUSCFG>
typename VIDITrace<BUSCFG>::pktsize_t VIDITrace<BUSCFG>::logb_bset_push(
    const logb_bset_t &bset) {
  logb_valid_vec.push_back(bset);
  pktsize_t pktbits = getLUsize(bset);
  // update statitics of logging unit size
  // pktbits is in terms of bits, not aligned to PACKET_ALIGNMENT
  assert(pktbits < Statistics::maxLUBits);
  stat.update_LU_dist(pktbits);
  return pktbits;
}

template <typename BUSCFG>
typename VIDITrace<BUSCFG>::pktsize_t VIDITrace<BUSCFG>::getLUsize(
    const logb_bset_t &bset) const {
  pktsize_t pktbits =
      BUSCFG::OFFSET_WIDTH + BUSCFG::LOGB_CNT + BUSCFG::LOGE_CNT;
  for (uint8_t i = 0; i < BUSCFG::LOGB_CNT; ++i) {
    if (bset.test(i)) pktbits += BUSCFG::CW[i];
  }
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
  getCH(logb_chid)->parseOnePkt(ibits);
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
void VIDITrace<BUSCFG>::print_loge_cnt(FILE *fp, loge_cnt_t &loge_cnt) {
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
ChannelTraceBase *VIDITrace<BUSCFG>::getLOGBChannelByName(const char *name) {
  return channels[getLOGBChannelIdByName(name)];
}

template <typename BUSCFG>
size_t VIDITrace<BUSCFG>::getLOGBChannelIdByName(const char *name) const {
  auto find_it = LOGB_name2id.find(name);
  assert(find_it != LOGB_name2id.end() && "Invalid Channel name");
  return find_it->second;
}

template <typename BUSCFG>
size_t VIDITrace<BUSCFG>::getLOGEChannelIdByName(const char *name) const {
  auto find_it = LOGE_name2id.find(name);
  assert(find_it != LOGE_name2id.end() && "Invalid Channel name");
  return find_it->second;
}

template <typename BUSCFG>
void VIDITrace<BUSCFG>::cleanEmptyLOGB_LOGE() {
  assert(logb_valid_vec.size() == loge_valid_vec.size());
  // iterator for compaction
  auto logb_bset_nonempty_it = logb_valid_vec.begin();
  auto loge_bset_nonempty_it = loge_valid_vec.begin();
  // iterator for traversal
  auto logb_bset_it = logb_valid_vec.begin();
  auto loge_bset_it = loge_valid_vec.begin();
  for (; logb_bset_it != logb_valid_vec.end(); ++logb_bset_it, ++loge_bset_it) {
    if (logb_bset_it->any() || loge_bset_it->any()) {
      // compact the trace but without overwriting
      if (logb_bset_it != logb_bset_nonempty_it) {
        *logb_bset_nonempty_it = *logb_bset_it;
        *loge_bset_nonempty_it = *loge_bset_it;
      }
      ++logb_bset_nonempty_it;
      ++loge_bset_nonempty_it;
    }
  }
  logb_valid_vec.erase(logb_bset_nonempty_it, logb_valid_vec.end());
  loge_valid_vec.erase(loge_bset_nonempty_it, loge_valid_vec.end());
  assert(logb_valid_vec.size() == loge_valid_vec.size());
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
  std::array<size_t, BUSCFG::LOGB_CNT> channel_start_pktcnt = {};
  std::array<size_t, BUSCFG::LOGB_CNT> channel_finish_pktcnt = {};
  loge_cnt_t loge_cnt = {};
  size_t pkt_id = 0;
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
    if (loge_bset_it->any()) {
      // first pass loge, check vector clock
      for (uint8_t i = 0; i < BUSCFG::LOGE_CNT; ++i) {
        if (loge_bset_it->test(i) && (loge2logb_map[i] != loge2logb_INVALID)) {
          size_t loge_idx = loge2logb_map[i];
          size_t ref_loge_cnt_id =
              getCH(loge_idx)
                  ->loge_loge_cnt_id_vec[channel_finish_pktcnt[loge_idx]];
          loge_cnt_t &ref_loge_cnt = loge_cnt_vec[ref_loge_cnt_id];
          assert(ref_loge_cnt == loge_cnt);
          // only advance per-channel packet counter after that packet is
          // finished
          // Important assumption: one channel cannot start the next packet
          // without finishing the previous packet
          ++channel_finish_pktcnt[loge_idx];
        }
      }
      // second pass loge, update vector clock
      for (uint8_t i = 0; i < BUSCFG::LOGE_CNT; ++i) {
        if (loge_bset_it->test(i)) {
          fprintf(fp, "%" NAME_MAX_LEN "s packet[%d] ends\n",
                  BUSCFG::LOGE_NAMES[i], loge_cnt[i]);
          ++loge_cnt[i];
        }
      }
    }
    if (logb_bset_it->any()) {
      for (uint8_t i = 0; i < BUSCFG::LOGB_CNT; ++i) {
        if (logb_bset_it->test(i)) {
          channels[i]->printPkt(fp, channel_start_pktcnt[i]);
          size_t ref_loge_cnt_id =
              getCH(i)->logb_loge_cnt_id_vec[channel_start_pktcnt[i]];
          loge_cnt_t &ref_loge_cnt = loge_cnt_vec[ref_loge_cnt_id];
          assert(ref_loge_cnt == loge_cnt);
          ++channel_start_pktcnt[i];
        }
      }
    }
    if (logb_bset_it->any() || loge_bset_it->any()) {
      print_loge_cnt(fp, loge_cnt);
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
          print_loge_cnt(fp, loge_cnt_vec[loge_cnt_vec_idx_a]);
          fprintf(fp, "From trace file %s:\n", other.filepath);
          other.print_loge_cnt(fp, loge_cnt_vec[loge_cnt_vec_idx_b]);
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

template <typename BUSCFG>
typename VIDITrace<BUSCFG>::trace_size_t VIDITrace<BUSCFG>::exportTrace(
    obitstream &obits) const {
  auto logb_bset_it = logb_valid_vec.begin();
  auto loge_bset_it = loge_valid_vec.begin();
  assert(logb_valid_vec.size() == loge_valid_vec.size() &&
         "inconsistent trace data structure");
  trace_size_t tsize = 0;
  std::array<size_t, BUSCFG::LOGB_CNT> channel_pktcnt = {};
  for (; logb_bset_it != logb_valid_vec.end(); ++logb_bset_it, ++loge_bset_it) {
    pktsize_t raw_pktbits = getLUsize(*logb_bset_it);
    pktsize_t aligned_pktbits = GET_ALIGNED_BITS(raw_pktbits);
    obits.putNbits(aligned_pktbits, BUSCFG::OFFSET_WIDTH);
    logb_valid_t logb_valid =
        static_cast<logb_valid_t>(logb_bset_it->to_ulong());
    loge_valid_t loge_valid =
        static_cast<loge_valid_t>(loge_bset_it->to_ulong());
    obits.putNbits(logb_valid, BUSCFG::LOGB_CNT);
    obits.putNbits(loge_valid, BUSCFG::LOGE_CNT);
    for (uint8_t i = 0; i < BUSCFG::LOGB_CNT; ++i) {
      if (logb_bset_it->test(i))
        getCH(i)->exportPkt(obits, channel_pktcnt[i]++);
    }
    if (aligned_pktbits > raw_pktbits)  // alignment padding
      obits.putNbits(uint8_t(0), aligned_pktbits - raw_pktbits);
    tsize += aligned_pktbits;
  }
  return tsize;
}

template <typename BUSCFG>
void VIDITrace<BUSCFG>::updateHBEncoding() {
  clearHBEncoding();
  auto logb_bset_it = logb_valid_vec.begin();
  auto loge_bset_it = loge_valid_vec.begin();
  assert(logb_valid_vec.size() == loge_valid_vec.size() &&
         "inconsistent trace data structure");
  // first vector clock is all-zero
  // Then every logging unit pushes a new vector clock.
  // For each logging unit,
  // (1) the loge packets refer to vector clock from the previous logging unit.
  // (2) the logb packets refer to vector clock from current logging unit.
  loge_cnt_vec.push_back(cur_loge_cnt);
  for (; logb_bset_it != logb_valid_vec.end(); ++logb_bset_it, ++loge_bset_it) {
    // process loge first, because they represent the ending of packets sent
    // before this cycle.
    // refer to the vector clock updated by previous logging unit
    for (uint8_t loge_chid = 0; loge_chid < BUSCFG::LOGE_CNT; ++loge_chid) {
      if (loge_bset_it->test(loge_chid)) {
        if (loge2logb_map[loge_chid] != loge2logb_INVALID) {
          getCH(loge2logb_map[loge_chid])
              ->finishOnePkt(loge_cnt_vec.size() - 1);
        }
      }
    }
    // update vector clock
    for (uint8_t i = 0; i < BUSCFG::LOGE_CNT; ++i) {
      if (loge_bset_it->test(i)) {
        ++cur_loge_cnt[i];
      }
    }
    loge_cnt_vec.push_back(cur_loge_cnt);
    // process logb
    // refer to the vector clock updated by current logging unit
    for (uint8_t i = 0; i < BUSCFG::LOGB_CNT; ++i) {
      if (logb_bset_it->test(i)) {
        getCH(i)->startOnePkt(loge_cnt_vec.size() - 1);
      }
    }
  }
  // Clean up the end of trace, where all on-the-fly packets are assumed to
  // finish even if their loge_valid has not been received.
  // Unfinished packets exist because the happens-before encoder still caches
  // the last loge_valid
  // Consider all on-the-fly packets finish in the end
  for (uint8_t i = 0; i < BUSCFG::LOGB_CNT; ++i) {
    ChannelTraceBase *ch_p = getCH(i);
    if (ch_p->logb_loge_cnt_id_vec.size() > ch_p->loge_loge_cnt_id_vec.size()) {
      ch_p->finishOnePkt(loge_cnt_vec.size() - 1);
    }
  }
}

template <typename BUSCFG>
void VIDITrace<BUSCFG>::clearHBEncoding() {
  cur_loge_cnt = loge_cnt_t{};  // zero initalize
  loge_cnt_vec.clear();
  for (uint8_t i = 0; i < BUSCFG::LOGB_CNT; ++i) getCH(i)->clearHBEncoding();
}
#endif  // CL_FPGARR_TRACE_IMPL_H
