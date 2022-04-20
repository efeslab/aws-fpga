#ifndef CL_FPGARR_DECODER_IMPL_H
#define CL_FPGARR_DECODER_IMPL_H

template <typename BUSCFG>
void Decoder<BUSCFG>::parse_trace(VIDITrace<BUSCFG> &T) {
  typedef typename VIDITrace<BUSCFG>::pktsize_t pktsize_t;
  assert(fp && "file open failed");
  assert(fread(&trace_bits, sizeof(trace_bits), 1, fp) == 1);
  // the static_assert is to make sure the buffer is large enough to hold the
  // entire transaction content of each channel
  static_assert(*std::max_element(BUSCFG::CW.cbegin(), BUSCFG::CW.cend()) <
                BUFSIZE * 8);
  T.setFilePath(filepath);
  size_t parsed_bits = 0;
  while (parsed_bits < trace_bits) {
    // pktsize is in terms of bits, aligned to PACKET_ALIGNMENT
    pktsize_t pktsize = ibuf.getNbits<pktsize_t>(BUSCFG::OFFSET_WIDTH);
    // {{{ for debug
    assert((pktsize % 8) == 0);
    assert((parsed_bits % 8) == 0);
    // update statistics
    T.updateStat(/*start_off*/ parsed_bits / 8 + 8, /*pktsize*/ pktsize);
    // }}} end of debug
    logb_valid_t logb_valid = ibuf.getNbits<logb_valid_t>(BUSCFG::LOGB_CNT);
    loge_valid_t loge_valid = ibuf.getNbits<loge_valid_t>(BUSCFG::LOGE_CNT);
    // aligned to PACKET_ALIGNMENT
    pktsize_t alignment_padding_size =
        pktsize - BUSCFG::OFFSET_WIDTH - BUSCFG::LOGB_CNT - BUSCFG::LOGE_CNT;
    // processing logb
    bitset<BUSCFG::LOGB_CNT> logb_valid_bset;
    for (uint8_t i = 0; i < BUSCFG::LOGB_CNT; ++i) {
      if (logb_valid & (0x1 << i)) {
        T.parseOneLOGBChannelPkt(i, ibuf);
        alignment_padding_size -= BUSCFG::CW[i];
        logb_valid_bset.set(i);
      }
    }
    pktsize_t pktbits = T.logb_bset_push(logb_valid_bset);
    // processing loge
    bitset<BUSCFG::LOGE_CNT> loge_valid_bset;
    for (uint8_t i = 0; i < BUSCFG::LOGE_CNT; ++i) {
      if (loge_valid & (0x1 << i)) {
        loge_valid_bset.set(i);
      }
    }
    T.loge_bset_push(loge_valid_bset);
    assert(alignment_padding_size < 8);
    [[maybe_unused]] uint8_t eat_padding = ibuf.getNbits<uint8_t>(alignment_padding_size);
    parsed_bits += pktsize;
    assert(pktsize == GET_ALIGNED_BITS(pktbits));
  }
  // Update HBEncoding
  T.updateHBEncoding();
}
#endif // CL_FPGARR_DECODER_IMPL_H
