// This file contains modules that mux record/replay related buses
// based on the csr configuration

// rr_axi_XXX_sel are simple combinational axi bus selectors.
// It will only connect one of the two source to the one target
// For source=>target signals (e.g. mstr.awvalid)
// sel 0=>inA, 1=>inB
// For source<=target (e.g. mstr.awready)
// inA = sel? DEFAULT : out
// inB = sel? out : DEFAULT
// NOTE that the DEFAULT is:
//   0 for valid signals, to be silent if not selected
//   1 for ready signals, to drop everything if not selected
//
// rr_axi_mstr_sel selects from two AXI master
`define SRC2TGT_SEL(sel, A, B, O, obj) \
  assign O.obj = sel? B.obj : A.obj
`define TGT2SRC_SEL(sel, A, B, O, obj, DFT) \
  assign A.obj = sel? DFT : O.obj; \
  assign B.obj = sel? O.obj : DFT
module rr_axi_mstr_sel (
  input logic sel,
  rr_axi_bus_t.master inAS,
  rr_axi_bus_t.master inBS,
  rr_axi_bus_t.slave outM
);
// AW Channel
`SRC2TGT_SEL(sel, inAS, inBS, outM, awvalid);
`SRC2TGT_SEL(sel, inAS, inBS, outM, awid);
`SRC2TGT_SEL(sel, inAS, inBS, outM, awaddr);
`SRC2TGT_SEL(sel, inAS, inBS, outM, awlen);
`SRC2TGT_SEL(sel, inAS, inBS, outM, awsize);
`TGT2SRC_SEL(sel, inAS, inBS, outM, awready, 1);
// W  Channel
`SRC2TGT_SEL(sel, inAS, inBS, outM, wvalid);
`SRC2TGT_SEL(sel, inAS, inBS, outM, wid);
`SRC2TGT_SEL(sel, inAS, inBS, outM, wdata);
`SRC2TGT_SEL(sel, inAS, inBS, outM, wstrb);
`SRC2TGT_SEL(sel, inAS, inBS, outM, wlast);
`TGT2SRC_SEL(sel, inAS, inBS, outM, wready, 1);
// AR Channel
`SRC2TGT_SEL(sel, inAS, inBS, outM, arvalid);
`SRC2TGT_SEL(sel, inAS, inBS, outM, arid);
`SRC2TGT_SEL(sel, inAS, inBS, outM, araddr);
`SRC2TGT_SEL(sel, inAS, inBS, outM, arlen);
`SRC2TGT_SEL(sel, inAS, inBS, outM, arsize);
`TGT2SRC_SEL(sel, inAS, inBS, outM, arready, 1);
// B  Channel
`TGT2SRC_SEL(sel, inAS, inBS, outM, bvalid, 0);
`TGT2SRC_SEL(sel, inAS, inBS, outM, bid, 0);
`TGT2SRC_SEL(sel, inAS, inBS, outM, bresp, 0);
`SRC2TGT_SEL(sel, inAS, inBS, outM, bready);
// R  Channel
`TGT2SRC_SEL(sel, inAS, inBS, outM, rvalid, 0);
`TGT2SRC_SEL(sel, inAS, inBS, outM, rid, 0);
`TGT2SRC_SEL(sel, inAS, inBS, outM, rdata, 0);
`TGT2SRC_SEL(sel, inAS, inBS, outM, rresp, 0);
`TGT2SRC_SEL(sel, inAS, inBS, outM, rlast, 0);
`SRC2TGT_SEL(sel, inAS, inBS, outM, rready);
endmodule

module rr_axi_slv_sel (
  input logic sel,
  rr_axi_bus_t.slave inAM,
  rr_axi_bus_t.slave inBM,
  rr_axi_bus_t.master outS
);
// AW Channel
`TGT2SRC_SEL(sel, inAM, inBM, outS, awvalid, 0);
`TGT2SRC_SEL(sel, inAM, inBM, outS, awid, 0);
`TGT2SRC_SEL(sel, inAM, inBM, outS, awaddr, 0);
`TGT2SRC_SEL(sel, inAM, inBM, outS, awlen, 0);
`TGT2SRC_SEL(sel, inAM, inBM, outS, awsize, 0);
`SRC2TGT_SEL(sel, inAM, inBM, outS, awready);
// W  Channel
`TGT2SRC_SEL(sel, inAM, inBM, outS, wvalid, 0);
`TGT2SRC_SEL(sel, inAM, inBM, outS, wid, 0);
`TGT2SRC_SEL(sel, inAM, inBM, outS, wdata, 0);
`TGT2SRC_SEL(sel, inAM, inBM, outS, wstrb, 0);
`TGT2SRC_SEL(sel, inAM, inBM, outS, wlast, 0);
`SRC2TGT_SEL(sel, inAM, inBM, outS, wready);
// AR Channel
`TGT2SRC_SEL(sel, inAM, inBM, outS, arvalid, 0);
`TGT2SRC_SEL(sel, inAM, inBM, outS, arid, 0);
`TGT2SRC_SEL(sel, inAM, inBM, outS, araddr, 0);
`TGT2SRC_SEL(sel, inAM, inBM, outS, arlen, 0);
`TGT2SRC_SEL(sel, inAM, inBM, outS, arsize, 0);
`SRC2TGT_SEL(sel, inAM, inBM, outS, arready);
// B  Channel
`SRC2TGT_SEL(sel, inAM, inBM, outS, bvalid);
`SRC2TGT_SEL(sel, inAM, inBM, outS, bid);
`SRC2TGT_SEL(sel, inAM, inBM, outS, bresp);
`TGT2SRC_SEL(sel, inAM, inBM, outS, bready, 1);
// R  Channel
`SRC2TGT_SEL(sel, inAM, inBM, outS, rvalid);
`SRC2TGT_SEL(sel, inAM, inBM, outS, rid);
`SRC2TGT_SEL(sel, inAM, inBM, outS, rdata);
`SRC2TGT_SEL(sel, inAM, inBM, outS, rresp);
`SRC2TGT_SEL(sel, inAM, inBM, outS, rlast);
`TGT2SRC_SEL(sel, inAM, inBM, outS, rready, 1);
endmodule

module rr_axil_mstr_sel (
  input logic sel,
  rr_axi_lite_bus_t.master inAS,
  rr_axi_lite_bus_t.master inBS,
  rr_axi_lite_bus_t.slave outM
);
// AW Channel
`SRC2TGT_SEL(sel, inAS, inBS, outM, awvalid);
`SRC2TGT_SEL(sel, inAS, inBS, outM, awaddr);
`TGT2SRC_SEL(sel, inAS, inBS, outM, awready, 1);
// W  Channel
`SRC2TGT_SEL(sel, inAS, inBS, outM, wvalid);
`SRC2TGT_SEL(sel, inAS, inBS, outM, wdata);
`SRC2TGT_SEL(sel, inAS, inBS, outM, wstrb);
`TGT2SRC_SEL(sel, inAS, inBS, outM, wready, 1);
// AR Channel
`SRC2TGT_SEL(sel, inAS, inBS, outM, arvalid);
`SRC2TGT_SEL(sel, inAS, inBS, outM, araddr);
`TGT2SRC_SEL(sel, inAS, inBS, outM, arready, 1);
// B  Channel
`TGT2SRC_SEL(sel, inAS, inBS, outM, bvalid, 0);
`TGT2SRC_SEL(sel, inAS, inBS, outM, bresp, 0);
`SRC2TGT_SEL(sel, inAS, inBS, outM, bready);
// R  Channel
`TGT2SRC_SEL(sel, inAS, inBS, outM, rvalid, 0);
`TGT2SRC_SEL(sel, inAS, inBS, outM, rdata, 0);
`TGT2SRC_SEL(sel, inAS, inBS, outM, rresp, 0);
`SRC2TGT_SEL(sel, inAS, inBS, outM, rready);
endmodule

module rr_axil_slv_sel (
  input logic sel,
  rr_axi_lite_bus_t.slave inAM,
  rr_axi_lite_bus_t.slave inBM,
  rr_axi_lite_bus_t.master outS
);
// AW Channel
`TGT2SRC_SEL(sel, inAM, inBM, outS, awvalid, 0);
`TGT2SRC_SEL(sel, inAM, inBM, outS, awaddr, 0);
`SRC2TGT_SEL(sel, inAM, inBM, outS, awready);
// W  Channel
`TGT2SRC_SEL(sel, inAM, inBM, outS, wvalid, 0);
`TGT2SRC_SEL(sel, inAM, inBM, outS, wdata, 0);
`TGT2SRC_SEL(sel, inAM, inBM, outS, wstrb, 0);
`SRC2TGT_SEL(sel, inAM, inBM, outS, wready);
// AR Channel
`TGT2SRC_SEL(sel, inAM, inBM, outS, arvalid, 0);
`TGT2SRC_SEL(sel, inAM, inBM, outS, araddr, 0);
`SRC2TGT_SEL(sel, inAM, inBM, outS, arready);
// B  Channel
`SRC2TGT_SEL(sel, inAM, inBM, outS, bvalid);
`SRC2TGT_SEL(sel, inAM, inBM, outS, bresp);
`TGT2SRC_SEL(sel, inAM, inBM, outS, bready, 1);
// R  Channel
`SRC2TGT_SEL(sel, inAM, inBM, outS, rvalid);
`SRC2TGT_SEL(sel, inAM, inBM, outS, rdata);
`SRC2TGT_SEL(sel, inAM, inBM, outS, rresp);
`TGT2SRC_SEL(sel, inAM, inBM, outS, rready, 1);
endmodule

// rr_logging_bus_switch
// can be configured to blackhole a rr_logging_bus_t
// en 0=>blackhole 1=>passthrough
module rr_logging_bus_switch (
  input logic en,
  rr_logging_bus_t.C in,
  rr_logging_bus_t.P out
);
// parameter check
generate
  if (in.LOGB_CHANNEL_CNT != out.LOGB_CHANNEL_CNT)
    $error("LOGB_CHANNEL_CNT mismatch: in %d, out %d\n",
      in.LOGB_CHANNEL_CNT, out.LOGB_CHANNEL_CNT);
  if (in.LOGB_DATA_WIDTH != out.LOGB_DATA_WIDTH)
    $error("LOGB_DATA_WIDTH mismatch: in %d, out %d\n",
      in.LOGB_DATA_WIDTH, out.LOGB_DATA_WIDTH);
  if (in.LOGE_CHANNEL_CNT != out.LOGE_CHANNEL_CNT)
    $error("LOGE_CHANNEL_CNT mismatch: in %d, out%d\n",
      in.LOGE_CHANNEL_CNT, out.LOGE_CHANNEL_CNT);
endgenerate

genvar i;
generate
  for (i=0; i < in.LOGB_CHANNEL_CNT; i=i+1)
    assign out.logb_valid[i] = en? in.logb_valid[i] : 0;
  for (i=0; i < in.LOGE_CHANNEL_CNT; i=i+1)
    assign out.loge_valid[i] = en? in.loge_valid[i] : 0;
endgenerate
assign out.logb_data = en? in.logb_data : 0;
assign in.logb_almful_hi = en? out.logb_almful_hi : 0;
assign in.logb_almful_lo = en? out.logb_almful_lo : 0;
endmodule
