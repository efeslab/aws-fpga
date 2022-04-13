#ifndef CL_FPGARR_DECODER_IMPL_H
#define CL_FPGARR_DECODER_IMPL_H
#include "cl_fpgarr_decoder.hpp"

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
    bool loge_matches_logb = false;
    for (uint8_t i = 0; i < BUSCFG::LOGE_CNT; ++i) {
      if (loge_valid & (0x1 << i)) {
        loge_valid_bset.set(i);
        loge_matches_logb |= T.tryFinishOneLOGEChannekPkt(i);
      }
    }
    T.loge_bset_push(loge_valid_bset);
    // maintain loge vector clock
    // note that the logb and loge processed above only refer to the vector
    // clock excluding current logging unit's loge_valid.
    //
    // We update loge_valid after a packet is processed.
    // only commit the loge vector clock if the vector clock from previous
    // logging units is referenced in the above channel packet processing,
    // which is:
    //  1. at least one new transaction started on LOGB channels
    //  OR
    //  2. at least one transaction ended on LOGB channels
    T.updateLOGECnt(logb_valid_bset.any() || loge_matches_logb);
    assert(alignment_padding_size < 8);
    uint8_t eat_padding = ibuf.getNbits<uint8_t>(alignment_padding_size);
    parsed_bits += pktsize;

    // update statistics
    assert(pktsize == GET_ALIGNED_BITS(pktbits));
  }
  // Cleanup on-the-fly packets. Consider them all finish in the end
  T.finishOngoingPkt();
}
#endif // CL_FPGARR_DECODER_IMPL_H
