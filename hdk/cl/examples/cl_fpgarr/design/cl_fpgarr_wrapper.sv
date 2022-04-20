`include "cl_fpgarr_defs.svh"
`include "cl_fpgarr_types.svh"
`include "cl_fpgarr_packing_cfg.svh"

`ifndef CL_NAME
`define CL_NAME unnamed_top_module
`endif
module cl_fpgarr_wrapper #(parameter NUM_DDR=4)
(
  `include "cl_ports.vh"
);
$info("cl_fpgarr_wrapper is INJECTED, it masquerades top module %s", `"`CL_NAME`");

logic clk;
assign clk = clk_main_a0;
logic rstn;
assign rstn = rst_main_n;

// An illustration of the this wrapper
// ?: Conditional connect (i.e. mux)
// +: join and connect to something else
//
//              (AXI interconnect)
//
// *-------*            *---*   cl_pcim  *-----------*   rr_pcim   *-------*
// |       |           /   S| <=?======= |M subord  S| <========== |M      |
// |       |  sh_pcim *     |   ˄        |  logging  |             |       |
// |      S| <========|     |   ‖        *-----------*             |       |
// |       |          *     |   ‖   *-------*      ‖               |       |
// |       |           \   S| <==== |storage| <====+               |       |
// |       |            *---*   ‖   *-------*      ‖               |       |
// |       |                    ‖       ‖          ‖               |       |
// |       |                    ‖  *----˅---*      ‖               |       |
// |       |                    ‖  |replayer|      ‖               |       |
// | Shell |     +====replay?==>?  *--------*      ‖               |  CL   |
// |       |     ‖              ‖       ‖          ‖               |       |
// |       |  *------*          +=======+          ‖               |       |
// |       |  |  rr  |==================record?===>?               |       |
// |       |  | csrs |==replay?=====?              ‖               |       |
// |       |  *--˄---*              ‖              ‖               |       |
// |       |     +========+         ‖              ‖               |       |
// |       |     bar1(hi) ‖         ‖              ‖               |       |
// |       |      *--*    ‖         ‖              ‖               |       |
// |       |     /  M|====+         ‖     *-----------*            |       |
// |      M| ===>|S  |              ˅     |    mstr   |            |       |
// |       |     \  M|==============?===> |M logging S| =========> |S      |
// |       |      *--*       ocl/         *-----------*   rr_xxx   |       |
// *-------*                 sda/                                  *-------*
//                           bar1(lo)/
//                           pcis

////////////////////////////////////////////////////////////////////////////////
// Abstract signals from the Shell
////////////////////////////////////////////////////////////////////////////////
// connect original F1 interfaces to sv interfaces
`AXI_SLV_WIRE2BUS(sh_pcim_bus, cl, sh, _pcim_);
rr_axi_bus_t sh_pcim_bus_q();
rr_axi_register_slice PCIM_AXI_REG_SLC (
  .clk(clk), .rstn(rstn),
  .slv(sh_pcim_bus_q),
  .mstr(sh_pcim_bus)
);
`AXI_MSTR_WIRE2BUS(dma_pcis_bus, sh, cl, _dma_pcis_);
rr_axi_bus_t dma_pcis_bus_q();
rr_axi_register_slice PCIS_AXI_REG_SLC (
  .clk(clk), .rstn(rstn),
  .slv(dma_pcis_bus),
  .mstr(dma_pcis_bus_q)
);
`AXIL_MSTR_WIRE2BUS(sda_bus, sda, cl, _);
rr_axi_lite_bus_t sda_bus_q();
rr_axi_register_slice_lite SDA_AXL_REG_SLC (
  .clk(clk), .rstn(rstn),
  .slv(sda_bus),
  .mstr(sda_bus_q)
);
`AXIL_MSTR_WIRE2BUS(ocl_bus, sh, ocl, _);
rr_axi_lite_bus_t ocl_bus_q();
rr_axi_register_slice_lite OCL_AXL_REG_SLC (
  .clk(clk), .rstn(rstn),
  .slv(ocl_bus),
  .mstr(ocl_bus_q)
);
`AXIL_MSTR_WIRE2BUS(bar1_bus, sh, bar1, _);
rr_axi_lite_bus_t bar1_bus_q();
rr_axi_register_slice_lite BAR1_AXL_REG_SLC (
  .clk(clk), .rstn(rstn),
  .slv(bar1_bus),
  .mstr(bar1_bus_q)
);
// irq_pcim_bus is the pcim bus converted from interrupt requests
rr_axi_bus_t irq_pcim_bus();
// rr_pcim_bus is the pcim bus coming directly out of cl, it is supposed to be
// logged then passed through to an axi interconnect together with the logging
// traffic
rr_axi_bus_t rr_pcim_bus();
// Both rr_pcim_bus and irq_pcim_bus are considered CL pcim traffics that should
// be record and replay.
// rr_irq_pcim_bus merges the above two pcim buses and will be merged later with
// non-CL pcim traffics, that should not be record and replay.
rr_axi_bus_t rr_irq_pcim_bus();
// cl_pcim_bus is the pcim bus coming directly to the Shell.
// Depending on replay or not, I choose between cl_pcim_bus or the replayed pcim
// bus to connect to the CL.
rr_axi_bus_t cl_pcim_bus();
// cl_bar1_bus is the lower 1MB of the bar1 bus connected to the cl
// The higher 1MB of the bar1 bus is reserved for rr_cfg_bus
rr_axi_lite_bus_t cl_bar1_bus();

////////////////////////////////////////////////////////////////////////////////
// CSRs of this fpgarr wrapper
////////////////////////////////////////////////////////////////////////////////
// storage_axi_write_csr is used to configure the storage backend
storage_axi_write_csr_t storage_axi_write_csr;
// storage_axi_read_csr is used to obtain statistics from the storage backend
storage_axi_read_csr_t storage_axi_read_csr;
// rr_mode_csr is used to control the record/replay behaviour
rr_mode_csr_t rr_mode_csr;
`ifdef COUNT_DDR
// ddr_counter_csr is used to count ddr traffics
rr_ddr_counter_csr_t ddr_counter_csr, ddr_counter_csr_q;
`endif
// rr_state_csr is used to expose internal fifo errors
// rr_state_csr_next is connected to fifo signals. Part of them are accumulated
// (bit or) to rr_state_csr at each cycle. Part of them are real-time states
// thus just pass through to the csr.
rr_state_csr_t rr_state_csr, rr_state_csr_next;
always_ff @(posedge clk)
  if (!rstn)
    rr_state_csr <= 0;
  else begin
    rr_state_csr.oneoff <= rr_state_csr.oneoff | rr_state_csr_next.oneoff;
    rr_state_csr.rt <= rr_state_csr_next.rt;
  end
rr_packed2wb_dbg_csr_t wb_record_dbg_csr;
pcim_interconnect_dbg_csr_t pcim_interconnect_dbg_csr;
////////////////////////////////////////////////////////////////////////////////
// LOG AXI bus
// The rr_XXX_record_bus are the axi(l) bus going into each logging module
// Note that the record bus should pick between bus connected to the shell or
// the replay bus according to the configuration.
// After the logging module,
// The rr_XXX_bus are connected to the CL.
//
// XXX_SH2CL_logging_bus:
//  Trace the traffic from the shell (SH) to the user circuit (CL)
//  The essential component of the record part.
// XXX_CL2SH_logging_bus:
//  Trace the traffic from the user circuit (CL) to the shell (SH)
//  Auxiliary logging used to validate the happen-before is successfully
//  preserved across record and replay.
////////////////////////////////////////////////////////////////////////////////
// PCIM bus
rr_axi_bus_t rr_pcim_record_bus();
`AXI_SLV_LOGGING_BUS(rr_pcim_SH2CL_logging_bus, "pcim");
`AXI_MSTR_LOGGING_BUS(rr_pcim_CL2SH_logging_bus, "pcim");
axi_recorder #(
  .ENABLE_B_BUFFER(1),
  .IS_CL_PCIM(1)
) pcim_bus_recorder (
  .clk(clk),
  .sync_rst_n(rstn),
  .S(rr_pcim_record_bus),
  .M(rr_irq_pcim_bus),
  .log_M2S(rr_pcim_CL2SH_logging_bus),
  .log_S2M(rr_pcim_SH2CL_logging_bus),
  .enable_B_buffer(rr_mode_csr.enable_PCIM_B_buffer),
  .enable_PCIM_workaround(rr_mode_csr.enable_PCIM_workaround),
  .B_fifo_almful(rr_state_csr_next.rt.almful.pcimB_buf),
  .B_fifo_overflow(rr_state_csr_next.oneoff.xpm_overflow.pcimB_buf),
  .B_fifo_underflow(rr_state_csr_next.oneoff.xpm_underflow.pcimB_buf)
);
// PCIS bus
rr_axi_bus_t rr_dma_pcis_record_bus();
rr_axi_bus_t rr_dma_pcis_bus();
`AXI_MSTR_LOGGING_BUS(rr_dma_pcis_SH2CL_logging_bus, "pcis");
`AXI_SLV_LOGGING_BUS(rr_dma_pcis_CL2SH_logging_bus, "pcis");
axi_recorder dma_pcis_bus_recorder (
  .clk(clk),
  .sync_rst_n(rstn),
  .M(rr_dma_pcis_record_bus),
  .S(rr_dma_pcis_bus),
  .log_M2S(rr_dma_pcis_SH2CL_logging_bus),
  .log_S2M(rr_dma_pcis_CL2SH_logging_bus),
  .B_fifo_almful(), .B_fifo_overflow(), .B_fifo_underflow() // not used
);
////////////////////////////////////////////////////////////////////////////////
// LOG AXIL bus
////////////////////////////////////////////////////////////////////////////////
// SDA AXIL
rr_axi_lite_bus_t rr_sda_record_bus();
rr_axi_lite_bus_t rr_sda_bus();
`AXIL_MSTR_LOGGING_BUS(rr_sda_SH2CL_logging_bus, "sda");
`AXIL_SLV_LOGGING_BUS(rr_sda_CL2SH_logging_bus, "sda");
axil_recorder sda_bus_recorder (
  .clk(clk),
  .sync_rst_n(rstn),
  .M(rr_sda_record_bus),
  .S(rr_sda_bus),
  .log_M2S(rr_sda_SH2CL_logging_bus),
  .log_S2M(rr_sda_CL2SH_logging_bus)
);
// OCL AXIL
rr_axi_lite_bus_t rr_ocl_record_bus();
rr_axi_lite_bus_t rr_ocl_bus();
`AXIL_MSTR_LOGGING_BUS(rr_ocl_SH2CL_logging_bus, "ocl");
`AXIL_SLV_LOGGING_BUS(rr_ocl_CL2SH_logging_bus, "ocl");
axil_recorder ocl_bus_recorder (
  .clk(clk),
  .sync_rst_n(rstn),
  .M(rr_ocl_record_bus),
  .S(rr_ocl_bus),
  .log_M2S(rr_ocl_SH2CL_logging_bus),
  .log_S2M(rr_ocl_CL2SH_logging_bus)
);
// BAR1 AXIL
rr_axi_lite_bus_t rr_bar1_record_bus();
rr_axi_lite_bus_t rr_bar1_bus();
`AXIL_MSTR_LOGGING_BUS(rr_bar1_SH2CL_logging_bus, "bar1");
`AXIL_SLV_LOGGING_BUS(rr_bar1_CL2SH_logging_bus, "bar1");
axil_recorder bar1_bus_recorder (
  .clk(clk),
  .sync_rst_n(rstn),
  .M(rr_bar1_record_bus),
  .S(rr_bar1_bus),
  .log_M2S(rr_bar1_SH2CL_logging_bus),
  .log_S2M(rr_bar1_CL2SH_logging_bus)
);

////////////////////////////////////////////////////////////////////////////////
// Pack the SH2CL logging bus (for replay)
////////////////////////////////////////////////////////////////////////////////
// the merging tree of rr_logging_bus_t
// Note that there is a benefit to postpone the merge of wide buses.
// This kind of optimization is handled in top_group.
//         merged bus
//              |
//          *-- top ---*
//         /           |
//      *-p2-*         |
//     /      \        |
//    p0      p1       |
//   /  \     / \      |
//  /    \   /   \     |
// sda  ocl bar1 pcim pcis
//////////////////////////
`UNPACKED_LOGGING_BUS_GROUP2(
  p0, rr_sda_SH2CL_logging_bus, rr_ocl_SH2CL_logging_bus);
`UNPACKED_LOGGING_BUS_GROUP2(
  p1, rr_bar1_SH2CL_logging_bus, rr_pcim_SH2CL_logging_bus);
`UNPACKED_LOGGING_BUS_GROUP2(p2, p0, p1);
`UNPACKED_LOGGING_BUS_GROUP2(
  merged_SH2CL_logging_bus, p2, rr_dma_pcis_SH2CL_logging_bus);
`LOGGING_BUS_DUP(merged_SH2CL_logging_bus, unpacked_record_bus);
rr_logging_bus_switch record_switch (
  .en(rr_mode_csr.recordEn),
  .in(merged_SH2CL_logging_bus),
  .out(unpacked_record_bus)
);
// the merging tree of the rr_packed_logging_bus_t is automatically generated
`LOGGING_BUS_UNPACK2PACK(unpacked_record_bus, packed_logging_bus);
rr_logging_bus_unpack2pack #(
  .MERGE_TREE_HEIGHT(record_pkg::MERGE_TREE_HEIGHT),
  .MERGE_TREE_MAX_NODES(record_pkg::MERGE_TREE_MAX_NODES),
  .NODES_PER_LAYER(record_pkg::NODES_PER_LAYER),
  .MERGE_PLAN(record_pkg::MERGE_PLAN),
  .NAME("record_merge_tree")
) top_record_group (
  .clk(clk),
  .rstn(rstn),
  .in(unpacked_record_bus),
  .out(packed_logging_bus)
);
`PACKED_LOGGING_BUS_TO_WBBUS(packed_logging_bus, record_bus);
rr_packed2writeback_bus #(
  .MERGE_TREE_HEIGHT(record_pkg::MERGE_TREE_HEIGHT)
) wb_record_inst(
  .clk(clk), .rstn(rstn), .in(packed_logging_bus), .out(record_bus),
  .fifo_overflow(rr_state_csr_next.oneoff.xpm_overflow.wb_record_inst),
  .fifo_underflow(rr_state_csr_next.oneoff.xpm_underflow.wb_record_inst),
  .fifo_almful_hi(rr_state_csr_next.rt.almful.wb_record_hi),
  .fifo_almful_lo(rr_state_csr_next.rt.almful.wb_record_lo),
  .dbg_csr(wb_record_dbg_csr)
);

////////////////////////////////////////////////////////////////////////////////
// Pack the CL2SH logging bus (for output validation)
////////////////////////////////////////////////////////////////////////////////
`UNPACKED_LOGGING_BUS_GROUP2(
  pv0, rr_sda_CL2SH_logging_bus, rr_ocl_CL2SH_logging_bus);
`UNPACKED_LOGGING_BUS_GROUP2(
  pv1, rr_bar1_CL2SH_logging_bus, rr_pcim_CL2SH_logging_bus);
`UNPACKED_LOGGING_BUS_GROUP2(pv2, pv0, pv1);
`UNPACKED_LOGGING_BUS_GROUP2(
  merged_CL2SH_logging_bus, pv2, rr_dma_pcis_CL2SH_logging_bus);
`LOGGING_BUS_DUP(merged_CL2SH_logging_bus, unpacked_validate_bus);
rr_logging_bus_switch validate_switch (
  .en(rr_mode_csr.outputValidateEn),
  .in(merged_CL2SH_logging_bus),
  .out(unpacked_validate_bus)
);

`ifdef DEBUG_MERGE_TREE_STRUCTURE
// WARN: You need to run the simulation (for a short time) to see the results
dbg_print_rr_logging_bus_CW
  dbg_tree_structure (unpacked_record_bus, unpacked_validate_bus);
`endif
// the merging tree of the rr_packed_logging_bus_t is automatically generated
`LOGGING_BUS_UNPACK2PACK(unpacked_validate_bus, packed_validate_bus);
rr_logging_bus_unpack2pack #(
  .MERGE_TREE_HEIGHT(validate_pkg::MERGE_TREE_HEIGHT),
  .MERGE_TREE_MAX_NODES(validate_pkg::MERGE_TREE_MAX_NODES),
  .NODES_PER_LAYER(validate_pkg::NODES_PER_LAYER),
  .MERGE_PLAN(validate_pkg::MERGE_PLAN),
  .NAME("validate_merge_tree")
) top_validate_group (
  .clk(clk),
  .rstn(rstn),
  .in(unpacked_validate_bus),
  .out(packed_validate_bus)
);
`PACKED_LOGGING_BUS_TO_WBBUS(packed_validate_bus, validate_bus);
rr_packed2writeback_bus #(
  .MERGE_TREE_HEIGHT(validate_pkg::MERGE_TREE_HEIGHT)
) wb_validate_inst(
  .clk(clk), .rstn(rstn), .in(packed_validate_bus), .out(validate_bus),
  .fifo_overflow(rr_state_csr_next.oneoff.xpm_overflow.wb_validate_inst),
  .fifo_underflow(rr_state_csr_next.oneoff.xpm_underflow.wb_validate_inst),
  .fifo_almful_hi(rr_state_csr_next.rt.almful.wb_validate_hi),
  .fifo_almful_lo(rr_state_csr_next.rt.almful.wb_validate_lo),
  .dbg_csr()
);

////////////////////////////////////////////////////////////////////////////////
// Unpack the replay bus
////////////////////////////////////////////////////////////////////////////////
localparam LOGE_PER_AXI = AWSF1_INTF_RRCFG::LOGE_PER_AXI;
localparam AWSF1_NUM_INTERFACES = AWSF1_INTF_RRCFG::NUM_INTF;
parameter int REPLAY_NLOGE = LOGE_PER_AXI * AWSF1_NUM_INTERFACES;
// Declare the rr_replay_bus for all channels
`AXI_SLV_REPLAY_BUS(rr_pcim_replay_bus, REPLAY_NLOGE);
`AXI_MSTR_REPLAY_BUS(rr_dma_pcis_replay_bus, REPLAY_NLOGE);
`AXIL_MSTR_REPLAY_BUS(rr_sda_replay_bus, REPLAY_NLOGE);
`AXIL_MSTR_REPLAY_BUS(rr_ocl_replay_bus, REPLAY_NLOGE);
`AXIL_MSTR_REPLAY_BUS(rr_bar1_replay_bus, REPLAY_NLOGE);
// This is just a reverse of the above rr_logging_bus_t merging tree
`REPLAY_BUS_JOIN2(rp0, rr_sda_replay_bus, rr_ocl_replay_bus);
rr_replay_bus_ungroup2 p0_ungroup(
  .in(rp0),
  .outA(rr_sda_replay_bus),
  .outB(rr_ocl_replay_bus)
);
`REPLAY_BUS_JOIN2(rp1, rr_bar1_replay_bus, rr_pcim_replay_bus);
rr_replay_bus_ungroup2 p1_ungroup(
  .in(rp1),
  .outA(rr_bar1_replay_bus),
  .outB(rr_pcim_replay_bus)
);
`REPLAY_BUS_JOIN2(rp2, rp0, rp1);
rr_replay_bus_ungroup2 p2_ungroup(.in(rp2), .outA(rp0), .outB(rp1));
`REPLAY_BUS_JOIN2(unpacked_replay_bus, rp2, rr_dma_pcis_replay_bus);
rr_replay_bus_ungroup2 top_ungroup(
  .in(unpacked_replay_bus),
  .outA(rp2), .outB(rr_dma_pcis_replay_bus));

assign rr_state_csr_next.rt.almful.replay_bus.almful = unpacked_replay_bus.almful;
assign rr_state_csr_next.rt.almful.replay_bus.rdyrply_almful = unpacked_replay_bus.rdyrply_almful;
////////////////////////////////////////////////////////////////////////////////
// Replay logic
////////////////////////////////////////////////////////////////////////////////
import AWSF1_INTF_RRCFG::PCIS;
import AWSF1_INTF_RRCFG::PCIM;
import AWSF1_INTF_RRCFG::SDA;
import AWSF1_INTF_RRCFG::OCL;
import AWSF1_INTF_RRCFG::BAR1;
// The rt_loge_valid should be ordered to comply with the previous merge trees
// The AWSF1_INTF_ORDER is used.
// i.e.: sda  ocl bar1 pcim pcis
//
// The aggregation of all realtime loge_valid info of all channels
// Note that this is a logical aggregation, not a physically aggregation.
// The loge_valid of each channel should still stay close to each interface and
// get distributed via the crossbar
logic [LOGE_PER_AXI-1:0] rt_loge_valid_agg [AWSF1_NUM_INTERFACES-1:0];
// The distributed realtime loge_valid of all channels. The logically aggregated
// loge_valid above will go through a crossbar and get distributed to all
// channels.
logic [AWSF1_NUM_INTERFACES-1:0] [LOGE_PER_AXI-1:0]
  rt_loge_valid_dist [AWSF1_NUM_INTERFACES-1:0];

// PCIM bus
rr_axi_bus_t pcim_replay_axi_bus();
axi_slv_replayer #(AWSF1_NUM_INTERFACES, LOGE_PER_AXI, PCIM,
  /*DBG_B*/ 1, /*DBG_R*/ 1, /*DBG_RDY*/ 1)
  pcim_bus_replayer (
  .clk(clk), .sync_rst_n(rstn),
  .rbus(rr_pcim_replay_bus),
  .outS(pcim_replay_axi_bus),
  .i_rt_loge_valid(rt_loge_valid_dist[PCIM]),
  .fifo_overflow(rr_state_csr_next.oneoff.xpm_overflow.pcim_replayer),
  .fifo_underflow(rr_state_csr_next.oneoff.xpm_underflow.pcim_replayer)
);
// PCIS bus
rr_axi_bus_t pcis_replay_axi_bus();
axi_mstr_replayer #(AWSF1_NUM_INTERFACES, LOGE_PER_AXI, PCIS,
  /*DBG_AW*/ 0, /*DBG_W*/ 0, /*DBG_AR*/ 0, /*DBG_RDY*/ 1)
  pcis_bus_replayer (
  .clk(clk), .sync_rst_n(rstn),
  .rbus(rr_dma_pcis_replay_bus),
  .outM(pcis_replay_axi_bus),
  .i_rt_loge_valid(rt_loge_valid_dist[PCIS]),
  .fifo_overflow(rr_state_csr_next.oneoff.xpm_overflow.pcis_replayer),
  .fifo_underflow(rr_state_csr_next.oneoff.xpm_underflow.pcis_replayer)
);
// SDA bus
rr_axi_lite_bus_t sda_replay_axil_bus();
axil_mstr_replayer #(AWSF1_NUM_INTERFACES, LOGE_PER_AXI, SDA)
  sda_bus_replayer (
  .clk(clk), .sync_rst_n(rstn),
  .rbus(rr_sda_replay_bus),
  .outM(sda_replay_axil_bus),
  .i_rt_loge_valid(rt_loge_valid_dist[SDA]),
  .fifo_overflow(rr_state_csr_next.oneoff.xpm_overflow.sda_replayer),
  .fifo_underflow(rr_state_csr_next.oneoff.xpm_underflow.sda_replayer)
);
// OCL bus
rr_axi_lite_bus_t ocl_replay_axil_bus();
axil_mstr_replayer #(AWSF1_NUM_INTERFACES, LOGE_PER_AXI, OCL)
  ocl_bus_replayer (
  .clk(clk), .sync_rst_n(rstn),
  .rbus(rr_ocl_replay_bus),
  .outM(ocl_replay_axil_bus),
  .i_rt_loge_valid(rt_loge_valid_dist[OCL]),
  .fifo_overflow(rr_state_csr_next.oneoff.xpm_overflow.ocl_replayer),
  .fifo_underflow(rr_state_csr_next.oneoff.xpm_underflow.ocl_replayer)
);
// BAR1 bus
rr_axi_lite_bus_t bar1_replay_axil_bus();
axil_mstr_replayer #(AWSF1_NUM_INTERFACES, LOGE_PER_AXI, BAR1)
  bar1_bus_replayer (
  .clk(clk), .sync_rst_n(rstn),
  .rbus(rr_bar1_replay_bus),
  .outM(bar1_replay_axil_bus),
  .i_rt_loge_valid(rt_loge_valid_dist[BAR1]),
  .fifo_overflow(rr_state_csr_next.oneoff.xpm_overflow.bar1_replayer),
  .fifo_underflow(rr_state_csr_next.oneoff.xpm_underflow.bar1_replayer)
);
// the distribution crossbar
rr_axi_rt_loge #(.LOGE_PER_AXI(LOGE_PER_AXI)) rt_loge_pcim (
  .in(rr_irq_pcim_bus),
  .o_rt_loge_valid(rt_loge_valid_agg[PCIM])
);
rr_axi_rt_loge #(.LOGE_PER_AXI(LOGE_PER_AXI)) rt_loge_pcis (
  .in(rr_dma_pcis_bus),
  .o_rt_loge_valid(rt_loge_valid_agg[PCIS])
);
rr_axil_rt_loge #(.LOGE_PER_AXI(LOGE_PER_AXI)) rt_loge_sda (
  .in(rr_sda_bus),
  .o_rt_loge_valid(rt_loge_valid_agg[SDA])
);
rr_axil_rt_loge #(.LOGE_PER_AXI(LOGE_PER_AXI)) rt_loge_ocl (
  .in(rr_ocl_bus),
  .o_rt_loge_valid(rt_loge_valid_agg[OCL])
);
rr_axil_rt_loge #(.LOGE_PER_AXI(LOGE_PER_AXI)) rt_loge_bar1 (
  .in(rr_bar1_bus),
  .o_rt_loge_valid(rt_loge_valid_agg[BAR1])
);
rr_rt_loge_crossbar #(
  .LOGE_PER_INTERFACE(LOGE_PER_AXI),
  .NUM_INTERFACES(AWSF1_NUM_INTERFACES),
  .PLACEMENT_VEC(AWSF1_INTF_RRCFG::PLACEMENT_VEC)
) rt_loge_crossbar (
  .clk(clk), .rstn(rstn),
  .rt_loge_in(rt_loge_valid_agg),
  .rt_loge_out(rt_loge_valid_dist)
);
////////////////////////////////////////////////////////////////////////////////
// Process rr_csrs and output configurations to other modules
////////////////////////////////////////////////////////////////////////////////
// flop rstn according to timing report
logic rstn_q = 1'b0;
always_ff @(posedge clk) rstn_q <= rstn;
rr_axi_lite_bus_t rr_cfg_bus();
rr_csrs #(
    .REG_STAGES(CSR_PIPE_DEPTH)
) csrs (
    .clk(clk),
    .rstn(rstn_q),
    .rr_cfg_bus(rr_cfg_bus),
    .storage_axi_write_csr(storage_axi_write_csr),
    .storage_axi_read_csr(storage_axi_read_csr),
    .rr_mode_csr(rr_mode_csr),
    .rr_state_csr(rr_state_csr),
    .wb_record_dbg_csr(wb_record_dbg_csr),
`ifdef COUNT_DDR
    .ddr_counter_csr(ddr_counter_csr_q),
`endif
    .pcim_interconnect_dbg_csr(pcim_interconnect_dbg_csr)
);

rr_axi_bus_t rr_storage_bus();
rr_axi_bus_t rr_validation_bus();
// With TEST_BRIDGE_REC_REP, the packed recording data will be directly used as
// packed replay data (without going to the backend storage)
////////////////////////////////////////////////////////////////////////////////
// Decide which bus to record
// It can be the bus connected to the shell, or the corresponding replay bus
////////////////////////////////////////////////////////////////////////////////
// rr_mode_csr.replayEn decides
// rr_irq_pcim or pcim_replay_axi_bus ?
rr_axi_slv_sel pcim_sel (
  .sel(rr_mode_csr.replayEn),
  .inAM(cl_pcim_bus),
  .inBM(pcim_replay_axi_bus),
  .outS(rr_pcim_record_bus)
);
// dma_pcis_bus_q or pcis_replay_axi_bus ?
rr_axi_mstr_sel pcis_sel (
  .sel(rr_mode_csr.replayEn),
  .inAS(dma_pcis_bus_q),
  .inBS(pcis_replay_axi_bus),
  .outM(rr_dma_pcis_record_bus)
);
// sda_bus_q or sda_replay_axil_bus ?
rr_axil_mstr_sel sda_sel (
  .sel(rr_mode_csr.replayEn),
  .inAS(sda_bus_q),
  .inBS(sda_replay_axil_bus),
  .outM(rr_sda_record_bus)
);
// ocl_bus_q or ocl_replay_axil_bus ?
rr_axil_mstr_sel ocl_sel (
  .sel(rr_mode_csr.replayEn),
  .inAS(ocl_bus_q),
  .inBS(ocl_replay_axil_bus),
  .outM(rr_ocl_record_bus)
);
// cl_bar1_bus or bar1_replay_axil_bus ?
rr_axil_mstr_sel bar1_sel (
  .sel(rr_mode_csr.replayEn),
  .inAS(cl_bar1_bus),
  .inBS(bar1_replay_axil_bus),
  .outM(rr_bar1_record_bus)
);
////////////////////////////////////////////////////////////////////////////////
// Connect packed record and replay bus to the storage backend
////////////////////////////////////////////////////////////////////////////////
// rr_cfg_bus is the higher 1MB of the bar1 bus.
// It expects RW addresses in 0x100000~0x1FFFFF.
rr_stream_bus_t #(.FULL_WIDTH(record_bus.FULL_WIDTH)) packed_replay_bus();

logic storage_backend_irq_req, storage_backend_irq_ack;
assign storage_backend_irq_ack = sh_cl_apppf_irq_ack[15];

rr_storage_backend_axi #(
  .LOGB_CHANNEL_CNT(unpacked_record_bus.LOGB_CHANNEL_CNT),
  .CHANNEL_WIDTHS(unpacked_record_bus.CHANNEL_WIDTHS),
  .LOGE_CHANNEL_CNT(unpacked_record_bus.LOGE_CHANNEL_CNT)
) trace_storage (
  .clk(clk), .rstn(rstn),
  .storage_backend_bus(rr_storage_bus),
  .validate_wb_bus(rr_validation_bus),
  .record_bus(record_bus),
  .replay_bus(packed_replay_bus),
  .validate_bus(validate_bus),
  .csr(storage_axi_write_csr),
  .counter(storage_axi_read_csr),
  .storage_backend_irq_ack,
  .storage_backend_irq_req
);

rr_tracedecoder #(
  .MERGE_TREE_HEIGHT(record_pkg::MERGE_TREE_HEIGHT),
  .MERGE_TREE_MAX_NODES(record_pkg::MERGE_TREE_MAX_NODES),
  .NODES_PER_LAYER(record_pkg::NODES_PER_LAYER),
  .MERGE_PLAN(record_pkg::MERGE_PLAN)
) top_decoder (
  .clk(clk), .rstn(rstn),
  .packed_replay_bus(packed_replay_bus),
  .replay_bus(unpacked_replay_bus)
);


////////////////////////////////////////////////////////////////////////////////
// Interrupt Handling
// Convert cl interrupt requests to cl pcim requests
////////////////////////////////////////////////////////////////////////////////
// irq_req[15] is reserved for rr buffer management (not implemented yet)
localparam CL_IRQ_ENABLED_NUM = 15;
logic [15:0] cl_irq_req, cl_irq_ack;
assign cl_sh_apppf_irq_req = {
  storage_backend_irq_req,
  cl_irq_req[CL_IRQ_ENABLED_NUM-1:0]};
assign cl_irq_ack[15:CL_IRQ_ENABLED_NUM] = 0;
`ifndef CL_DISABLE_IRQ_PCIM
  rr_int_to_pcim #(
      .NUM_INT(CL_IRQ_ENABLED_NUM))
  cl_int_to_pcim(
      .clk(clk),
      .rstn(rstn),
      .offset(storage_axi_write_csr.buf_addr),
      .offset_update(storage_axi_write_csr.int_buf_update),
      .int_req(cl_irq_req[CL_IRQ_ENABLED_NUM-1:0]),
      .int_ack(cl_irq_ack[CL_IRQ_ENABLED_NUM-1:0]),
      .pcim(irq_pcim_bus)
  );
  rr_cl_irq2pcim_interconnect cl_irq_pcim_interconnect (
    .clk(clk), .rstn(rstn),
    .rr_pcim_bus(rr_pcim_bus),
    .irq_pcim_bus(irq_pcim_bus),
    .rr_irq_pcim_bus(rr_irq_pcim_bus)
  );
`else
  assign cl_irq_ack[CL_IRQ_ENABLED_NUM-1:0] =
    sh_cl_apppf_irq_ack[CL_IRQ_ENABLED_NUM-1:0];
  axi_direct_to_axi skip_irq_pcim_inst (
    .axiM(rr_pcim_bus),
    .axiS(rr_irq_pcim_bus)
  );
`endif // CL_DISABLE_IRQ_PCIM

//`define DEBUG_IRQ_PCIM_ADDR
`ifdef DEBUG_IRQ_PCIM_ADDR
always_ff @(posedge clk)
  if (rstn) begin
    if (rr_pcim_bus.awvalid && rr_pcim_bus.awready)
      $display("rr_pcim_bus addr 0x%x", rr_pcim_bus.awaddr);
    if (irq_pcim_bus.awvalid && irq_pcim_bus.awready) begin
      $display("irq_pcim_bus addr 0x%x", irq_pcim_bus.awaddr);
      if (irq_pcim_bus.awaddr == 0)
        $finish();
    end
    if (rr_irq_pcim_bus.awvalid && rr_irq_pcim_bus.awready)
      $display("rr_irq_pcim_bus addr 0x%x", rr_irq_pcim_bus.awaddr);
  end
`endif

// AXI Interconnect for the logging pcim traffic and user pcim traffic
// NOTE: that all Xid field of pcim buses, either from logging or from the cl,
// have to spare 1 bit for this interconnect.
// So instead of 16-bit Xid available in sh_pcim_bus, they only have 15-bit Xid.
rr_storage_pcim_axi_interconnect pcim_interconnect (
  .clk(clk),
  .rstn(rstn),
  .logging_wb_bus(rr_storage_bus),
  .validation_wb_bus(rr_validation_bus),
  .cl_pcim_bus(cl_pcim_bus),
  .sh_pcim_bus(sh_pcim_bus_q),
  .dbg_csr(pcim_interconnect_dbg_csr)
);
// AXI4LITE Interconnect for splitting the bar1 bus for rr configuration
rr_cfg_bar1_interconnect bar1_interconnect (
  .clk(clk),
  .rstn(rstn),
  .from_sh_bar1_bus(bar1_bus_q),
  .to_cl_bar1_bus(cl_bar1_bus),
  .rr_cfg_bus(rr_cfg_bus)
);

////////////////////////////////////////////////////////////////////////////////
// connect the original top module
////////////////////////////////////////////////////////////////////////////////
// the instance name CL is to match the instance name assigned to the top CL
// module by AWS building scripts
`CL_NAME #(NUM_DDR) CL (
  `AXI_CONNECT_BUS2WIRE(rr_pcim_bus, cl, sh, _pcim_),
  `AXI_CONNECT_BUS2WIRE(rr_dma_pcis_bus, sh, cl, _dma_pcis_),
  `AXIL_CONNECT_BUS2WIRE(rr_sda_bus, sda, cl, _),
  `AXIL_CONNECT_BUS2WIRE(rr_ocl_bus, sh, ocl, _),
  `AXIL_CONNECT_BUS2WIRE(rr_bar1_bus, sh, bar1, _),
  .cl_sh_apppf_irq_req(cl_irq_req),
  .sh_cl_apppf_irq_ack(cl_irq_ack),
  .*
);
assign rr_pcim_bus.wid = 0;

////////////////////////////////////////////////////////////////////////////////
// Debug ILA Core
////////////////////////////////////////////////////////////////////////////////
`ifdef DEBUG_ILA
localparam REPLAY_PKT_CNT_WIDTH = 32;
`define DBG_COUNT_AXI(cntname, busname, ch)                                    \
  logic [REPLAY_PKT_CNT_WIDTH-1:0] cntname;                                    \
  always_ff @(posedge clk)                                                     \
    if (!rstn)                                                                 \
      cntname <= 0;                                                            \
    else if (busname.``ch``valid && busname.``ch``ready)                       \
      cntname <= cntname + 1
`DBG_COUNT_AXI(pcis_AW, pcis_replay_axi_bus, aw);       // probe 0
`DBG_COUNT_AXI(pcis_W, pcis_replay_axi_bus, w);         // probe 1
`DBG_COUNT_AXI(pcis_AR, pcis_replay_axi_bus, ar);       // probe 2
`DBG_COUNT_AXI(pcis_R, pcis_replay_axi_bus, r);         // probe 3
`DBG_COUNT_AXI(pcis_B, pcis_replay_axi_bus, b);         // probe 4
`DBG_COUNT_AXI(pcim_AW, pcim_replay_axi_bus, aw);       // probe 5
`DBG_COUNT_AXI(pcim_W, pcim_replay_axi_bus, w);         // probe 6
`DBG_COUNT_AXI(pcim_AR, pcim_replay_axi_bus, ar);       // probe 7
`DBG_COUNT_AXI(pcim_R, pcim_replay_axi_bus, r);         // probe 8
`DBG_COUNT_AXI(pcim_B, pcim_replay_axi_bus, b);         // probe 9
`DBG_COUNT_AXI(ocl_AW, ocl_replay_axil_bus, aw);        // probe 10
`DBG_COUNT_AXI(ocl_W, ocl_replay_axil_bus, w);          // probe 11
`DBG_COUNT_AXI(ocl_AR, ocl_replay_axil_bus, ar);        // probe 12
`DBG_COUNT_AXI(ocl_R, ocl_replay_axil_bus, r);          // probe 13
`DBG_COUNT_AXI(ocl_B, ocl_replay_axil_bus, b);          // probe 14
dbg_fpgarr_wrapper_ila ila (
  .clk(clk),
  .probe0(pcis_AW),
  .probe1(pcis_W),
  .probe2(pcis_AR),
  .probe3(pcis_R),
  .probe4(pcis_B),
  .probe5(pcim_AW),
  .probe6(pcim_W),
  .probe7(pcim_AR),
  .probe8(pcim_R),
  .probe9(pcim_B),
  .probe10(ocl_AW),
  .probe11(ocl_W),
  .probe12(ocl_AR),
  .probe13(ocl_R),
  .probe14(ocl_B)
);
`endif

`ifdef COUNT_DDR
lib_pipe #(.WIDTH($bits(rr_ddr_counter_csr_t)), .STAGES(3))
    PIPE_DDR_COUNTER_A(.clk(clk), .rst_n(1'b1), .in_bus(ddr_counter_csr), .out_bus(ddr_counter_csr_q));
always_ff @(posedge clk) begin
    ddr_counter_csr.a_aw <= CL.ddr_aw_counter_a;
    ddr_counter_csr.a_w <= CL.ddr_w_counter_a;
    ddr_counter_csr.a_ar <= CL.ddr_ar_counter_a;
    ddr_counter_csr.a_r <= CL.ddr_r_counter_a;
    ddr_counter_csr.a_b <= CL.ddr_b_counter_a;
    ddr_counter_csr.b_aw <= CL.ddr_aw_counter_b;
    ddr_counter_csr.b_w <= CL.ddr_w_counter_b;
    ddr_counter_csr.b_ar <= CL.ddr_ar_counter_b;
    ddr_counter_csr.b_r <= CL.ddr_r_counter_b;
    ddr_counter_csr.b_b <= CL.ddr_b_counter_b;
    ddr_counter_csr.c_aw <= CL.ddr_aw_counter_c;
    ddr_counter_csr.c_w <= CL.ddr_w_counter_c;
    ddr_counter_csr.c_ar <= CL.ddr_ar_counter_c;
    ddr_counter_csr.c_r <= CL.ddr_r_counter_c;
    ddr_counter_csr.c_b <= CL.ddr_b_counter_c;
    ddr_counter_csr.d_aw <= CL.ddr_aw_counter_d;
    ddr_counter_csr.d_w <= CL.ddr_w_counter_d;
    ddr_counter_csr.d_ar <= CL.ddr_ar_counter_d;
    ddr_counter_csr.d_r <= CL.ddr_r_counter_d;
    ddr_counter_csr.d_b <= CL.ddr_b_counter_d;
end
`endif

endmodule
`ifdef TEST_REPLAY
  $error("Should not be used with TEST_REPLAY");
`endif

`undef CL_NAME
`define CL_NAME cl_fpgarr_wrapper
