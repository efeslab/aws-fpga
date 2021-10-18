`include "cl_fpgarr_defs.svh"
`include "cl_fpgarr_types.svh"

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
// cl_pcim_bus is the pcim bus coming directly to the Shell. It is combined with
// the storage backend bus in an axi interconnect ip
rr_axi_bus_t cl_pcim_bus();
// cl_bar1_bus is the lower 1MB of the bar1 bus connected to the cl
// The higher 1MB of the bar1 bus is reserved for rr_cfg_bus
rr_axi_lite_bus_t cl_bar1_bus();

// Forward declared CSRs
// These CSRs are parsed directly from the rr_cfg_bus, you have to take care of
// the staging yourself if want to propogate them to somewhere else.
// storage_axi_csr is used to configure the storage backend
storage_axi_csr_t storage_axi_csr;
// rr_mode_csr is used to control the record/replay behaviour
rr_mode_csr_t rr_mode_csr;
// rr_mode_csr_q is the flopped version for timing
rr_mode_csr_t rr_mode_csr_q;

////////////////////////////////////////////////////////////////////////////////
// LOG AXI bus
// The rr_XXX_record_bus are the axi(l) bus going into each logging module
// Note that the record bus should pick between bus connected to the shell or
// the replay bus according to the configuration.
// After the logging module,
// The rr_XXX_bus are connected to the CL.
////////////////////////////////////////////////////////////////////////////////
// PCIM bus
rr_axi_bus_t rr_pcim_record_bus();
// rr_pcim_bus is the pcim bus coming directly out of cl, it is supposed to be
// logged then passed through to an axi interconnect together with the logging
// traffic
rr_axi_bus_t rr_pcim_bus();
`AXI_SLV_LOGGING_BUS(rr_pcim_logging_bus);
axi_slv_recorder pcim_bus_recorder (
  .clk(clk),
  .sync_rst_n(rstn),
  .inM(rr_pcim_record_bus),
  .outS(rr_pcim_bus),
  .axi_log(rr_pcim_logging_bus)
);
// PCIS bus
rr_axi_bus_t rr_dma_pcis_record_bus();
rr_axi_bus_t rr_dma_pcis_bus();
`AXI_MSTR_LOGGING_BUS(rr_dma_pcis_logging_bus);
axi_mstr_recorder dma_pcis_bus_recorder (
  .clk(clk),
  .sync_rst_n(rstn),
  .inS(rr_dma_pcis_record_bus),
  .outM(rr_dma_pcis_bus),
  .axi_log(rr_dma_pcis_logging_bus)
);
////////////////////////////////////////////////////////////////////////////////
// LOG AXIL bus
////////////////////////////////////////////////////////////////////////////////
// SDA AXIL
rr_axi_lite_bus_t rr_sda_record_bus();
rr_axi_lite_bus_t rr_sda_bus();
`AXIL_MSTR_LOGGING_BUS(rr_sda_logging_bus);
axil_mstr_recorder sda_bus_recorder (
  .clk(clk),
  .sync_rst_n(rstn),
  .inS(rr_sda_record_bus),
  .outM(rr_sda_bus),
  .axil_log(rr_sda_logging_bus)
);
// OCL AXIL
rr_axi_lite_bus_t rr_ocl_record_bus();
rr_axi_lite_bus_t rr_ocl_bus();
`AXIL_MSTR_LOGGING_BUS(rr_ocl_logging_bus);
axil_mstr_recorder ocl_bus_recorder (
  .clk(clk),
  .sync_rst_n(rstn),
  .inS(rr_ocl_record_bus),
  .outM(rr_ocl_bus),
  .axil_log(rr_ocl_logging_bus)
);
// BAR1 AXIL
rr_axi_lite_bus_t rr_bar1_record_bus();
rr_axi_lite_bus_t rr_bar1_bus();
`AXIL_MSTR_LOGGING_BUS(rr_bar1_logging_bus);
axil_mstr_recorder bar1_bus_recorder (
  .clk(clk),
  .sync_rst_n(rstn),
  .inS(rr_bar1_record_bus),
  .outM(rr_bar1_bus),
  .axil_log(rr_bar1_logging_bus)
);

////////////////////////////////////////////////////////////////////////////////
// Pack the logging bus
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
`LOGGING_BUS_JOIN2(p0, rr_sda_logging_bus, rr_ocl_logging_bus);
rr_logging_bus_group2 p0_group(
  .inA(rr_sda_logging_bus),
  .inB(rr_ocl_logging_bus),
  .out(p0)
);
`LOGGING_BUS_JOIN2(p1, rr_bar1_logging_bus, rr_pcim_logging_bus);
rr_logging_bus_group2 p1_group(
  .inA(rr_bar1_logging_bus),
  .inB(rr_pcim_logging_bus),
  .out(p1)
);
`LOGGING_BUS_JOIN2(p2, p0, p1);
rr_logging_bus_group2 p2_group(.inA(p0), .inB(p1), .out(p2));
`LOGGING_BUS_JOIN2(merged_logging_bus, p2, rr_dma_pcis_logging_bus);
rr_logging_bus_group2 logging_group(
  .inA(p2),
  .inB(rr_dma_pcis_logging_bus),
  .out(merged_logging_bus)
);
`LOGGING_BUS_DUP(merged_logging_bus, unpacked_record_bus);
rr_logging_bus_switch record_switch (
  .en(rr_mode_csr_q.recordEn),
  .in(merged_logging_bus),
  .out(unpacked_record_bus)
);
// the merging tree of the rr_packed_logging_bus_t is automatically generated
`LOGGING_BUS_UNPACK2PACK(unpacked_record_bus, packed_logging_bus);
rr_logging_bus_unpack2pack top_group(
  .clk(clk),
  .rstn(rstn),
  .in(unpacked_record_bus),
  .out(packed_logging_bus)
);
`PACKED_LOGGING_BUS_TO_WBBUS(packed_logging_bus, record_bus);
rr_packed2writeback_bus wb_inst(
  .clk(clk), .rstn(rstn), .in(packed_logging_bus), .out(record_bus));

////////////////////////////////////////////////////////////////////////////////
// Unpack the replay bus
////////////////////////////////////////////////////////////////////////////////
localparam REPLAY_NLOGE = unpacked_record_bus.LOGE_CHANNEL_CNT;
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

////////////////////////////////////////////////////////////////////////////////
// Replay logic
////////////////////////////////////////////////////////////////////////////////
// The rt_loge_valid should be ordered to comply with the previous merge trees
// i.e.: sda  ocl bar1 pcim pcis
enum int { SDA=0, OCL, BAR1, PCIM, PCIS } AWSF1_INTF_ORDER;
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
axi_slv_replayer #(AWSF1_NUM_INTERFACES) pcim_bus_replayer (
  .clk(clk), .sync_rst_n(rstn),
  .rbus(rr_pcim_replay_bus),
  .outS(pcim_replay_axi_bus),
  .o_rt_loge_valid(rt_loge_valid_agg[PCIM]),
  .i_rt_loge_valid(rt_loge_valid_dist[PCIM])
);
// PCIS bus
rr_axi_bus_t pcis_replay_axi_bus();
axi_mstr_replayer #(AWSF1_NUM_INTERFACES) pcis_bus_replayer (
  .clk(clk), .sync_rst_n(rstn),
  .rbus(rr_dma_pcis_replay_bus),
  .outM(pcis_replay_axi_bus),
  .o_rt_loge_valid(rt_loge_valid_agg[PCIS]),
  .i_rt_loge_valid(rt_loge_valid_dist[PCIS])
);
// SDA bus
rr_axi_lite_bus_t sda_replay_axil_bus();
axil_mstr_replayer #(AWSF1_NUM_INTERFACES) sda_bus_replayer (
  .clk(clk), .sync_rst_n(rstn),
  .rbus(rr_sda_replay_bus),
  .outM(sda_replay_axil_bus),
  .o_rt_loge_valid(rt_loge_valid_agg[SDA]),
  .i_rt_loge_valid(rt_loge_valid_dist[SDA])
);
// OCL bus
rr_axi_lite_bus_t ocl_replay_axil_bus();
axil_mstr_replayer #(AWSF1_NUM_INTERFACES) ocl_bus_replayer (
  .clk(clk), .sync_rst_n(rstn),
  .rbus(rr_ocl_replay_bus),
  .outM(ocl_replay_axil_bus),
  .o_rt_loge_valid(rt_loge_valid_agg[OCL]),
  .i_rt_loge_valid(rt_loge_valid_dist[OCL])
);
// BAR1 bus
rr_axi_lite_bus_t bar1_replay_axil_bus();
axil_mstr_replayer #(AWSF1_NUM_INTERFACES) bar1_bus_replayer (
  .clk(clk), .sync_rst_n(rstn),
  .rbus(rr_bar1_replay_bus),
  .outM(bar1_replay_axil_bus),
  .o_rt_loge_valid(rt_loge_valid_agg[BAR1]),
  .i_rt_loge_valid(rt_loge_valid_dist[BAR1])
);
// the distribution crossbar
rr_rt_loge_crossbar #(
  .LOGE_PER_INTERFACE(LOGE_PER_AXI),
  .NUM_INTERFACES(AWSF1_NUM_INTERFACES),
  .PLACEMENT_VEC(AWSF1_PLACEMENT_VEC)
) rt_loge_crossbar (
  .clk(clk), .rstn(rstn),
  .rt_loge_in(rt_loge_valid_agg),
  .rt_loge_out(rt_loge_valid_dist)
);
////////////////////////////////////////////////////////////////////////////////
// Process rr_csrs and output configurations to other modules
////////////////////////////////////////////////////////////////////////////////
rr_axi_lite_bus_t rr_cfg_bus();
rr_csrs csrs (
    .clk(clk),
    .rstn(rstn),
    .rr_cfg_bus(rr_cfg_bus),
    .storage_axi_csr(storage_axi_csr),
    .rr_mode_csr(rr_mode_csr)
);

rr_axi_bus_t rr_storage_bus();
// With TEST_BRIDGE_REC_REP, the packed recording data will be directly used as
// packed replay data (without going to the backend storage)
////////////////////////////////////////////////////////////////////////////////
// Decide which bus to record
// It can be the bus connected to the shell, or the corresponding replay bus
////////////////////////////////////////////////////////////////////////////////
// I need rr_mode_csr to synchronously arrive at all channels
lib_pipe #(.WIDTH($bits(rr_mode_csr_t)), .STAGES(4)) rr_mode_csr_pipe (
  .clk(clk), .rst_n(rstn),
  .in_bus(rr_mode_csr),
  .out_bus(rr_mode_csr_q)
);
// rr_mode_csr.replayEn decides
// cl_pcim or pcim_replay_axi_bus ?
rr_axi_slv_sel pcim_sel (
  .sel(rr_mode_csr_q.replayEn),
  .inAM(cl_pcim_bus),
  .inBM(pcim_replay_axi_bus),
  .outS(rr_pcim_record_bus)
);
// dma_pcis_bus_q or pcis_replay_axi_bus ?
rr_axi_mstr_sel pcis_sel (
  .sel(rr_mode_csr_q.replayEn),
  .inAS(dma_pcis_bus_q),
  .inBS(pcis_replay_axi_bus),
  .outM(rr_dma_pcis_record_bus)
);
// sda_bus_q or sda_replay_axil_bus ?
rr_axil_mstr_sel sda_sel (
  .sel(rr_mode_csr_q.replayEn),
  .inAS(sda_bus_q),
  .inBS(sda_replay_axil_bus),
  .outM(rr_sda_record_bus)
);
// ocl_bus_q or ocl_replay_axil_bus ?
rr_axil_mstr_sel ocl_sel (
  .sel(rr_mode_csr_q.replayEn),
  .inAS(ocl_bus_q),
  .inBS(ocl_replay_axil_bus),
  .outM(rr_ocl_record_bus)
);
// cl_bar1_bus or bar1_replay_axil_bus ?
rr_axil_mstr_sel bar1_sel (
  .sel(rr_mode_csr_q.replayEn),
  .inAS(cl_bar1_bus),
  .inBS(bar1_replay_axil_bus),
  .outM(rr_bar1_record_bus)
);
`ifndef TEST_BRIDGE_REC_REP
////////////////////////////////////////////////////////////////////////////////
// Connect packed record and replay bus to the storage backend
////////////////////////////////////////////////////////////////////////////////
// TODO: Storage backend is not implemented yet.
// TODO: convert rr_stream_bus_t to logging_wb_bus via mjc's module
// TODO: need an integration test
// rr_cfg_bus is the higher 1MB of the bar1 bus.
// It expects RW addresses in 0x100000~0x1FFFFF.
rr_stream_bus_t #(.FULL_WIDTH(record_bus.FULL_WIDTH)) packed_replay_bus();

rr_storage_backend_axi #(
  .LOGB_CHANNEL_CNT(unpacked_record_bus.LOGB_CHANNEL_CNT),
  .CHANNEL_WIDTHS(top_group.SHUFFLED_CHANNEL_WIDTHS),
  .LOGE_CHANNEL_CNT(unpacked_record_bus.LOGE_CHANNEL_CNT)
) trace_storage (
  .clk(clk), .rstn(rstn),
  .storage_backend_bus(rr_storage_bus),
  .record_bus(record_bus),
  .replay_bus(packed_replay_bus),
  .csr(storage_axi_csr)
);

rr_tracedecoder top_decoder(
  .clk(clk), .rstn(rstn),
  .packed_replay_bus(packed_replay_bus),
  .replay_bus(unpacked_replay_bus)
);
`else
// TESTING replay trace decoding
rr_tracedecoder top_decoder(
  .clk(clk), .rstn(rstn),
  .packed_replay_bus(record_bus),
  .replay_bus(unpacked_replay_bus)
);
// placeholder for rr_storage_bus dummy signals
assign rr_storage_bus.awvalid = 0;
assign rr_storage_bus.wvalid = 0;
assign rr_storage_bus.arvalid = 0;
assign rr_storage_bus.bready = 1;
assign rr_storage_bus.rready = 1;
`endif

// AXI Interconnect for the logging pcim traffic and user pcim traffic
// NOTE: that all Xid field of pcim buses, either from logging or from the cl,
// have to spare 1 bit for this interconnect.
// So instead of 16-bit Xid available in sh_pcim_bus, they only have 15-bit Xid.
rr_storage_pcim_axi_interconnect pcim_interconnect (
  .clk(clk),
  .rstn(rstn),
  .logging_wb_bus(rr_storage_bus),
  .cl_pcim_bus(cl_pcim_bus),
  .sh_pcim_bus(sh_pcim_bus_q)
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
  .*
);
endmodule

`undef CL_NAME
`define CL_NAME cl_fpgarr_wrapper
