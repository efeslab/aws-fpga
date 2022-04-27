`ifndef CL_FPGARR_DBG_H
`define CL_FPGARR_DBG_H

parameter DBG_PKT_CNT_WIDTH = 32;
`define DBG_COUNT_AXI(cntname, busname, ch)                                    \
  logic [DBG_PKT_CNT_WIDTH-1:0] cntname;                                       \
  always_ff @(posedge clk)                                                     \
    if (!rstn)                                                                 \
      cntname <= 0;                                                            \
    else if (busname.``ch``valid && busname.``ch``ready)                       \
      cntname <= cntname + 1
`define DBG_COUNT_AXI_AW_EXPECTED_W(cntname, busname)                          \
  logic [DBG_PKT_CNT_WIDTH-1:0] cntname;                                       \
  always_ff @(posedge clk)                                                     \
    if (!rstn)                                                                 \
      cntname <= 0;                                                            \
    else if (busname.awvalid && busname.awready)                               \
      cntname <= cntname + busname.awlen + 1
`endif // CL_FPGARR_DBG_H
