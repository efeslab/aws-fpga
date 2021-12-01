#include <utils/log.h>

#include "cl_fpgarr_csrs.h"
#include "cl_fpgarr_csrs_decode.h"

void dump_trace_split_dbg_csr() {
    trace_split_dbg_csr_t d;
    rr_cfg_peek(RR_TRACE_SPLIT_DBG_CSR_P0, &(d.val[0]));
    rr_cfg_peek(RR_TRACE_SPLIT_DBG_CSR_P1, &(d.val[1]));
    rr_cfg_peek(RR_TRACE_SPLIT_DBG_CSR_P2, &(d.val[2]));
    rr_cfg_peek(RR_TRACE_SPLIT_DBG_CSR_P3, &(d.val[3]));
    log_info("Dump of RR_TRACE_SPLIT_DBG_CSR");
    log_info("asm_done %d, asm_wait_body %d, asm_header %d",
            d.asm_done, d.asm_wait_body, d.asm_header);
    log_info("hi_full %d, lo_empty %d, lo_header %d, lo_body %d",
            d.hi_full, d.lo_empty, d.lo_header, d.lo_body);
    log_info("lo_replay_done %d, lo_remain_len %d, lo_valid_off %d",
            d.lo_replay_done, d.lo_remain_len, d.lo_valid_off);
    log_info("rt_replay_axi_cnt %d, replay_axi_total %d, trace_axi_cnt %d",
            d.rt_replay_axi_cnt, d.replay_axi_total, d.trace_axi_cnt);
    log_info("hi_pad_last_oneoff %d, hi_pad_last %d, hi_lo_shift %d",
            d.hi_pad_last_oneoff, d.hi_pad_last, d.hi_lo_shift);
}

void dump_trace_rw_axi_status() {
    trace_rw_axi_status_t d;
    rr_cfg_peek(RR_AXI_STATUS_LO, &(d.val[0]));
    rr_cfg_peek(RR_AXI_STATUS_HI, &(d.val[1]));
    log_info("Dump of RR_AXI_STATUS (trace_rw_axi_status)");
    log_info("bid %d, bvalid %d, bready %d", d.bid, d.bvalid, d.bready);
    log_info("awid %d, awvalid %d, awready %d", d.awid, d.awvalid, d.awready);
    log_info(
        "wvalid %d, wready %d, arvalid %d, arready %d, rvalid %d, rready %d",
        d.wvalid, d.wready, d.arvalid, d.arready, d.rvalid, d.rready);
}
