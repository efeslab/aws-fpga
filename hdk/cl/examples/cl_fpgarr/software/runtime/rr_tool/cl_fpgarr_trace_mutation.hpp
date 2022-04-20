#ifndef CL_FPGARR_TRACE_MUTATION_H
#define CL_FPGARR_TRACE_MUTATION_H
#include <cstdio>
#include <queue>

#include "cl_fpgarr_trace.hpp"

template <typename REC_BUSCFG, typename VLD_BUSCFG>
class VIDITracePCIMOrderMutation {
  typedef VIDITrace<REC_BUSCFG> RTrace_t;
  typedef VIDITrace<VLD_BUSCFG> VTrace_t;
  typedef typename RTrace_t::loge_bset_t Rloge_bset_t;
  typedef typename RTrace_t::logb_bset_t Rlogb_bset_t;
  RTrace_t &record_trace;
  VTrace_t &validate_trace;

 public:
  VIDITracePCIMOrderMutation(RTrace_t &rec_trace, VTrace_t &vld_trace)
      : record_trace(rec_trace), validate_trace(vld_trace) {}

  void mutateRecordTrace() {
    size_t rec_pcim_aw_id = record_trace.getLOGEChannelIdByName("pcim_AW");
    size_t rec_pcim_w_id = record_trace.getLOGEChannelIdByName("pcim_W");
    /* TODO delay pcim_B if necessary
     *
    size_t rec_pcim_b_logb_id = record_trace.getLOGBChannelIdByName("pcim_B");
    size_t rec_pcim_b_loge_id = record_trace.getLOGEChannelIdByName("pcim_B");
    // number of b finished in the mutated record_trace (b should wait if the
    // corresponding aw is delayed)
    size_t b_cnt = 0;
     */
    ChannelTraceBase *vld_pcim_aw_p =
        validate_trace.getLOGBChannelByName("pcim_AW");
    // number of aw finished in the mutated record_trace
    size_t aw_cnt = 0;
    // number of w finished in the mutated record_trace (w itself is not
    // mutated)
    size_t w_cnt = 0;
    // temp buffer to decode pcim_AW packet in the validate_trace
    F1ChannelPkt_t aw_pkt;
    // whether there is an aw under mutation delayed to finish
    // A FIFO for pending AW. Each element represents aw_paired_w_cnt when that
    // aw became pending and was pushed into the FIFO.
    std::queue<size_t> pending_aw;
    // prepare pending_aw
    size_t aw_paired_w_cnt = 0;
    for (int pktid = 0; pktid < vld_pcim_aw_p->cnt; ++pktid) {
        vld_pcim_aw_p->getDecodedPkt(pktid, aw_pkt);
        // delay every AW until one corresponding W is finished
        pending_aw.push(aw_paired_w_cnt + 1);
        aw_paired_w_cnt += aw_pkt.as_AXI_AW.awlen + 1;
    }
    for (Rloge_bset_t &loge_bset : record_trace.loge_valid_vec) {
      if (!pending_aw.empty() && w_cnt >= pending_aw.front()) {
        loge_bset.set(rec_pcim_aw_id);
        pending_aw.pop();
      } else {
        loge_bset.reset(rec_pcim_aw_id);
      }

      // the loge_bset is finalized, check whether there is an aw finished
      if (loge_bset.test(rec_pcim_aw_id)) {
        ++aw_cnt;
      }
      if (loge_bset.test(rec_pcim_w_id)) {
        ++w_cnt;
      }
    }
    if (!pending_aw.empty()) {
      assert(w_cnt >= pending_aw.front());
      Rloge_bset_t supplement_loge;
      Rlogb_bset_t supplement_logb;
      supplement_loge.set(rec_pcim_aw_id);
      record_trace.loge_valid_vec.push_back(supplement_loge);
      record_trace.logb_valid_vec.push_back(supplement_logb);
      printf("Adding a supplement loge at the end\n");
      pending_aw.pop();
    }
    assert(pending_aw.empty());
    record_trace.cleanEmptyLOGB_LOGE();
    record_trace.updateHBEncoding();
  }
};
#endif  // CL_FPGARR_TRACE_MUTATION_H
