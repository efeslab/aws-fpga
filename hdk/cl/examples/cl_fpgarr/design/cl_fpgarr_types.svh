`ifndef CL_FPGARR_TYPES
`define CL_FPGARR_TYPES

////////////////////////////////////////////////////////////////////////////////
// structures to track all info you need to start an AXI(lite) transaction for
// each channel.
////////////////////////////////////////////////////////////////////////////////
// RR
// record inputs from axi master:
// used in pcis
typedef struct packed {
   // AW Channel: 91b
   //    awid   16b
   //    awaddr 64b
   //    awlen  8b
   //    awsize 3b
   logic [15:0] awid;
   logic [63:0] awaddr;
   logic [7:0] awlen;
   logic [2:0] awsize;
} axi_rr_AW_t;
parameter AXI_RR_AW_WIDTH = $bits(axi_rr_AW_t);
typedef struct packed {
   // W  Channel: 593b
   //    wid   16b
   //    wdata 512b
   //    wstrb 64b
   //    wlast 1b
   logic [15:0] wid;
   logic [511:0] wdata;
   logic [63:0] wstrb;
   logic wlast;
} axi_rr_W_t;
parameter AXI_RR_W_WIDTH = $bits(axi_rr_W_t);
typedef struct packed {
   // AR Channel: 91b
   //    arid   16b
   //    araddr 64b
   //    arlen  8b
   //    arsize 3b
   logic [15:0] arid;
   logic [63:0] araddr;
   logic [7:0] arlen;
   logic [2:0] arsize;
} axi_rr_AR_t;
parameter AXI_RR_AR_WIDTH = $bits(axi_rr_AR_t);

parameter AXI_RR_MSTR_WIDTH =
   AXI_RR_AW_WIDTH + AXI_RR_W_WIDTH + AXI_RR_AR_WIDTH;

// RR
// record inputs from axi slave:
// used in pcim
typedef struct packed {
   // B  Channel: 18b
   //    bid   16b
   //    bresp 2b
   logic [15:0] bid;
   logic [1:0] bresp;
} axi_rr_B_t;
parameter AXI_RR_B_WIDTH = $bits(axi_rr_B_t);
typedef struct packed {
   // R  Channel: 531b
   //    rid   16b
   //    rdata 512b
   //    rresp 2b
   //    rlast 1b
   logic [15:0] rid;
   logic [511:0] rdata;
   logic [1:0] rresp;
   logic rlast;
} axi_rr_R_t;
parameter AXI_RR_R_WIDTH = $bits(axi_rr_R_t);

parameter AXI_RR_SLV_WIDTH = AXI_RR_B_WIDTH + AXI_RR_R_WIDTH;


// RR
// record inputs from axi lite master:
// used in: sh_ocl, sh_bar1, sda_cl
typedef struct packed {
   // AW Channel: 32b
   //    awaddr 32b
   logic [31:0] awaddr;
} axil_rr_AW_t;
parameter AXIL_RR_AW_WIDTH = $bits(axil_rr_AW_t);
typedef struct packed {
   // W  Channel: 36b
   //    wdata 32b
   //    wstrb 4b
   logic [31:0] wdata;
   logic [3:0] wstrb;
} axil_rr_W_t;
parameter AXIL_RR_W_WIDTH = $bits(axil_rr_W_t);
typedef struct packed {
   // AR Channel: 32b
   //    araddr 32b
   logic [31:0] araddr;
} axil_rr_AR_t;
parameter AXIL_RR_AR_WIDTH = $bits(axil_rr_AR_t);
parameter AXIL_RR_MSTR_WIDTH =
   AXIL_RR_AW_WIDTH + AXIL_RR_W_WIDTH + AXIL_RR_AR_WIDTH;

// RR
// record inputs from axi slave:
// used in: ???
typedef struct packed {
   // B  Channel:
   //    bresp 2b
   logic [1:0] bresp;
} axil_rr_B_t;
parameter AXIL_RR_B_WIDTH = $bits(axil_rr_B_t);
typedef struct packed {
   // R ChanneL: 34b
   //    rdata 32b
   //    rresp 2b
   logic [31:0] rdata;
   logic [1:0] rresp;
} axil_rr_R_t;
parameter AXIL_RR_R_WIDTH = $bits(axil_rr_R_t);
parameter AXIL_RR_SLV_WIDTH = AXIL_RR_B_WIDTH + AXIL_RR_R_WIDTH;

`define AXI_MSTR_GET_LOGB_CHANNEL_NAMES(intfname)                              \
  {RR_CHANNEL_NAME_BITS'({intfname, "_AR"}),                                   \
   RR_CHANNEL_NAME_BITS'({intfname, "_W"}),                                    \
   RR_CHANNEL_NAME_BITS'({intfname, "_AW"})}
`define AXI_SLV_GET_LOGB_CHANNEL_NAMES(intfname)                               \
  {RR_CHANNEL_NAME_BITS'({intfname, "_B"}),                                    \
   RR_CHANNEL_NAME_BITS'({intfname, "_R"})}
`define AXI_GET_LOGE_CHANNEL_NAMES(intfname)                                   \
  {RR_CHANNEL_NAME_BITS'({intfname, "_R"}),                                    \
   RR_CHANNEL_NAME_BITS'({intfname, "_B"}),                                    \
   RR_CHANNEL_NAME_BITS'({intfname, "_AR"}),                                   \
   RR_CHANNEL_NAME_BITS'({intfname, "_W"}),                                    \
   RR_CHANNEL_NAME_BITS'({intfname, "_AW"})}
`define AXI_MSTR_LOGGING_BUS(name, intfname)                                   \
  rr_logging_bus_t #(                                                          \
    .LOGB_CHANNEL_CNT(3),                                                      \
    .CHANNEL_WIDTHS({                                                          \
      {AXI_RR_AR_WIDTH}, {AXI_RR_W_WIDTH},                                     \
      {AXI_RR_AW_WIDTH}}),                                                     \
    .LOGE_CHANNEL_CNT(5),                                                      \
    .LOGB_CHANNEL_NAMES(`AXI_MSTR_GET_LOGB_CHANNEL_NAMES(intfname)),           \
    .LOGE_CHANNEL_NAMES(`AXI_GET_LOGE_CHANNEL_NAMES(intfname))) name()
`define AXI_SLV_LOGGING_BUS(name, intfname)                                    \
  rr_logging_bus_t #(                                                          \
    .LOGB_CHANNEL_CNT(2),                                                      \
    .CHANNEL_WIDTHS({                                                          \
      {AXI_RR_B_WIDTH}, {AXI_RR_R_WIDTH}}),                                    \
    .LOGE_CHANNEL_CNT(5),                                                      \
    .LOGB_CHANNEL_NAMES(`AXI_SLV_GET_LOGB_CHANNEL_NAMES(intfname)),            \
    .LOGE_CHANNEL_NAMES(`AXI_GET_LOGE_CHANNEL_NAMES(intfname))) name()
`define AXIL_MSTR_LOGGING_BUS(name, intfname)                                  \
  rr_logging_bus_t #(                                                          \
    .LOGB_CHANNEL_CNT(3),                                                      \
    .CHANNEL_WIDTHS({                                                          \
      {AXIL_RR_AR_WIDTH}, {AXIL_RR_W_WIDTH},                                   \
      {AXIL_RR_AW_WIDTH}}),                                                    \
    .LOGE_CHANNEL_CNT(5),                                                      \
    .LOGB_CHANNEL_NAMES(`AXI_MSTR_GET_LOGB_CHANNEL_NAMES(intfname)),           \
    .LOGE_CHANNEL_NAMES(`AXI_GET_LOGE_CHANNEL_NAMES(intfname))) name()
`define AXIL_SLV_LOGGING_BUS(name, intfname)                                   \
  rr_logging_bus_t #(                                                          \
    .LOGB_CHANNEL_CNT(2),                                                      \
    .CHANNEL_WIDTHS({                                                          \
      {AXIL_RR_B_WIDTH}, {AXIL_RR_R_WIDTH}}),                                  \
    .LOGE_CHANNEL_CNT(5),                                                      \
    .LOGB_CHANNEL_NAMES(`AXI_SLV_GET_LOGB_CHANNEL_NAMES(intfname)),            \
    .LOGE_CHANNEL_NAMES(`AXI_GET_LOGE_CHANNEL_NAMES(intfname))) name()
`define LOGGING_BUS_JOIN2(name, inA, inB)                                      \
  rr_logging_bus_t #(                                                          \
    .LOGB_CHANNEL_CNT(inA.LOGB_CHANNEL_CNT + inB.LOGB_CHANNEL_CNT),            \
    /*{MSB, LSB }*/                                                            \
    .CHANNEL_WIDTHS({inB.CHANNEL_WIDTHS, inA.CHANNEL_WIDTHS}),                 \
    .LOGE_CHANNEL_CNT(inA.LOGE_CHANNEL_CNT + inB.LOGE_CHANNEL_CNT),            \
    .LOGB_CHANNEL_NAMES({inB.LOGB_CHANNEL_NAMES, inA.LOGB_CHANNEL_NAMES}),    \
    /*{inB.LOGB_CHANNEL_NAMES, inA.LOGB_CHANNEL_NAMES}), */ \
    .LOGE_CHANNEL_NAMES({inB.LOGE_CHANNEL_NAMES, inA.LOGE_CHANNEL_NAMES})) \
    /*{inB.LOGE_CHANNEL_NAMES, inA.LOGE_CHANNEL_NAMES})) */ \
    name()
`define UNPACKED_LOGGING_BUS_GROUP2(name, _inA, _inB)                          \
  `LOGGING_BUS_JOIN2(name, _inA, _inB);                                        \
  rr_logging_bus_group2 name``_group(                                          \
    .inA(_inA), .inB(_inB), .out(name))
`define LOGGING_BUS_DUP(src, dup)                                              \
  rr_logging_bus_t #(                                                          \
    .LOGB_CHANNEL_CNT(src.LOGB_CHANNEL_CNT),                                   \
    .CHANNEL_WIDTHS(src.CHANNEL_WIDTHS),                                       \
    .LOGE_CHANNEL_CNT(src.LOGE_CHANNEL_CNT),                                   \
    .LOGB_CHANNEL_NAMES(src.LOGB_CHANNEL_NAMES),                               \
    .LOGE_CHANNEL_NAMES(src.LOGE_CHANNEL_NAMES)) dup()
`define LOGGING_BUS_UNPACK2PACK(unpackedname, packedname) \
  rr_packed_logging_bus_t #(\
    .LOGB_CHANNEL_CNT(unpackedname.LOGB_CHANNEL_CNT), \
    .LOGE_CHANNEL_CNT(unpackedname.LOGE_CHANNEL_CNT), \
    .LOGB_DATA_WIDTH(unpackedname.LOGB_DATA_WIDTH)) packedname()
`define PACKED_LOGGING_BUS_TO_WBBUS(plog_bus, wbbus) \
  rr_stream_bus_t #( \
    .FULL_WIDTH(plog_bus.LOGB_CHANNEL_CNT + plog_bus.LOGE_CHANNEL_CNT + \
      plog_bus.LOGB_DATA_WIDTH)) wbbus()
// about the replay part
`define REPLAY_BUS_JOIN2(name, outA, outB) \
  rr_replay_bus_t #( \
    .LOGB_CHANNEL_CNT(outA.LOGB_CHANNEL_CNT + outB.LOGB_CHANNEL_CNT), \
    .CHANNEL_WIDTHS({outB.CHANNEL_WIDTHS, outA.CHANNEL_WIDTHS}), \
    .LOGE_CHANNEL_CNT(outA.LOGE_CHANNEL_CNT)) name()
`define AXI_MSTR_REPLAY_BUS(name, NLOGE) \
  rr_replay_bus_t #( \
    .LOGB_CHANNEL_CNT(3), \
    .CHANNEL_WIDTHS({{AXI_RR_AR_WIDTH}, {AXI_RR_W_WIDTH}, {AXI_RR_AW_WIDTH}}), \
    .LOGE_CHANNEL_CNT(NLOGE)) name()
`define AXI_SLV_REPLAY_BUS(name, NLOGE) \
  rr_replay_bus_t #( \
    .LOGB_CHANNEL_CNT(2), \
    .CHANNEL_WIDTHS({{AXI_RR_B_WIDTH}, {AXI_RR_R_WIDTH}}), \
    .LOGE_CHANNEL_CNT(NLOGE)) name()
`define AXIL_MSTR_REPLAY_BUS(name, NLOGE) \
  rr_replay_bus_t #( \
    .LOGB_CHANNEL_CNT(3), \
    .CHANNEL_WIDTHS({ \
      {AXIL_RR_AR_WIDTH}, {AXIL_RR_W_WIDTH}, {AXIL_RR_AW_WIDTH}}), \
    .LOGE_CHANNEL_CNT(NLOGE)) name()
`define AXIL_SLV_REPLAY_BUS(name, NLOGE) \
  rr_replay_bus_t #( \
    .LOGB_CHANNEL_CNT(2), \
    .CHANNEL_WIDTHS({{AXIL_RR_B_WIDTH}, {AXIL_RR_R_WIDTH}}), \
    .LOGE_CHANNEL_CNT(NLOGE)) name()

typedef struct packed {
  logic [63:0] buf_addr;
  logic [63:0] buf_size;
  logic write_buf_update;
  logic record_force_finish;
  logic read_buf_update;
  // logic replay_start;
  logic [63:0] replay_bits;
  logic validate_buf_update;
} storage_axi_write_csr_t;

typedef struct packed {
    logic [63:0] record_bits;
    logic [63:0] validate_bits;
    logic [63:0] rt_replay_bits;
    logic [31:0] trace_fifo_assert;
} storage_axi_read_csr_t;

// rr_mode_csr_t is a interpretation of the RR_MODE csr
// NOTE: do not forget to sync with the cl_fpgarr.{c,h} (the software lib)
typedef struct packed {
  logic recordEn;             // bit 0
  logic replayEn;             // bit 1
  logic outputValidateEn;     // bit 2
} rr_mode_csr_t;

typedef struct packed {
  struct packed {
    logic wb_record_inst;    // bit 0
    logic pcim_replayer;     // bit 1
    logic pcis_replayer;     // bit 2
    logic sda_replayer;      // bit 3
    logic ocl_replayer;      // bit 4
    logic bar1_replayer;     // bit 5
    logic wb_validate_inst;  // bit 6
    logic pcimB_buf;         // bit 7
  } xpm_overflow;
  struct packed {
    logic wb_record_inst;    // bit 8
    logic pcim_replayer;     // bit 9
    logic pcis_replayer;     // bit 10
    logic sda_replayer;      // bit 11
    logic ocl_replayer;      // bit 12
    logic bar1_replayer;     // bit 13
    logic wb_validate_inst;  // bit 14
    logic pcimB_buf;         // bit 15
  } xpm_underflow;
  struct packed {
    logic wb_record_hi;      // bit 16
    logic wb_record_lo;      // bit 17
    logic wb_validate_hi;    // bit 18
    logic wb_validate_lo;    // bit 19
    logic pcimB_buf;         // bit 20
  } almful;
} rr_state_csr_t;
`endif
// template
////////////////////////////////////////////////////////////////////////////////
//////////////////////////     garbage      ////////////////////////////////////
//////////////////////////   end of garbage ////////////////////////////////////
