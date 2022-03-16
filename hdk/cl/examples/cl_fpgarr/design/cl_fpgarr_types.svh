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
    .LOGE_CHANNEL_CNT(outA.LOGE_CHANNEL_CNT), \
    .NUM_AXI_INTF(outA.NUM_AXI_INTF + outB.NUM_AXI_INTF)) name()
`define AXI_MSTR_REPLAY_BUS(name, NLOGE) \
  rr_replay_bus_t #( \
    .LOGB_CHANNEL_CNT(3), \
    .CHANNEL_WIDTHS({{AXI_RR_AR_WIDTH}, {AXI_RR_W_WIDTH}, {AXI_RR_AW_WIDTH}}), \
    .LOGE_CHANNEL_CNT(NLOGE), .NUM_AXI_INTF(1)) name()
`define AXI_SLV_REPLAY_BUS(name, NLOGE) \
  rr_replay_bus_t #( \
    .LOGB_CHANNEL_CNT(2), \
    .CHANNEL_WIDTHS({{AXI_RR_B_WIDTH}, {AXI_RR_R_WIDTH}}), \
    .LOGE_CHANNEL_CNT(NLOGE), .NUM_AXI_INTF(1)) name()
`define AXIL_MSTR_REPLAY_BUS(name, NLOGE) \
  rr_replay_bus_t #( \
    .LOGB_CHANNEL_CNT(3), \
    .CHANNEL_WIDTHS({ \
      {AXIL_RR_AR_WIDTH}, {AXIL_RR_W_WIDTH}, {AXIL_RR_AW_WIDTH}}), \
    .LOGE_CHANNEL_CNT(NLOGE), .NUM_AXI_INTF(1)) name()
`define AXIL_SLV_REPLAY_BUS(name, NLOGE) \
  rr_replay_bus_t #( \
    .LOGB_CHANNEL_CNT(2), \
    .CHANNEL_WIDTHS({{AXIL_RR_B_WIDTH}, {AXIL_RR_R_WIDTH}}), \
    .LOGE_CHANNEL_CNT(NLOGE), .NUM_AXI_INTF(1)) name()

typedef struct packed {
  logic [63:0] buf_addr;
  logic [63:0] buf_size;
  logic write_buf_update;
  logic record_force_finish;
  logic read_buf_update;
  // logic replay_start;
  logic [63:0] replay_bits;
  logic validate_buf_update;
  logic [31:0] on_the_fly_balance;
  logic int_buf_update;
} storage_axi_write_csr_t;

typedef struct packed {
  logic [31:0] replay_axi_total;                // bit 71-102
  logic [7:0] lo_valid_off;                     // bit 63-70
  logic hi_lo_shift;                            // bit 62
  logic hi_pad_last;                            // bit 61
  logic hi_pad_last_oneoff;                     // bit 60
  logic [3:0] trace_axi_cnt;                    // bit 56-59
  // FIXME: reorder to prevent CSR boundary cutoff
  logic [31:0] rt_replay_axi_cnt;               // bit 24-55
  logic [15:0] lo_remain_len;                   // bit 8-23
  logic lo_replay_done;                         // bit 7
  logic lo_body;                                // bit 6
  logic lo_header;                              // bit 5
  logic lo_empty;                               // bit 4
  logic hi_full;                                // bit 3
  logic asm_wait_header;                        // bit 2
  logic asm_wait_body;                          // bit 1
  logic asm_done;                               // bit 0
} trace_split_dbg_csr_t;

typedef struct packed {
    logic [63:0] record_in_pkt_cnt;
    logic [63:0] record_out_pkt_cnt;
    logic [63:0] record_in_bits_cnt;
    logic [63:0] record_out_bits_cnt;
    logic [63:0] wb_aw_trans_cnt;
    logic [63:0] wb_w_trans_cnt;
    logic [63:0] wb_b_trans_cnt;
    logic [63:0] record_in_fifo_out_pkt_cnt;
    logic [63:0] record_in_fifo_out_orig_bits_cnt;
    logic [63:0] record_in_fifo_out_aligned_bits_cnt;
    logic [63:0] axi_status;
    logic [31:0] replay_ar_trans_cnt;
    logic [31:0] replay_r_trans_cnt;
    logic [31:0] replay_in_fifo_in_cnt;
    logic [31:0] replay_in_fifo_out_cnt;
    logic [31:0] replay_out_fifo_in_cnt;
    logic [31:0] replay_out_fifo_out_cnt;
    trace_split_dbg_csr_t trace_split_dbg_csr;
} rr_trace_rw_cnts_t;

typedef struct packed {
    logic [63:0] rt_record_unhandled_size;
    logic [63:0] rt_current_record_unhandled_size;
    logic [63:0] rt_leftover_size;
    logic [63:0] rt_record_curr;
} rr_trace_merge_cnts_t;

typedef struct packed {
    logic [63:0] record_bits;
    logic [63:0] validate_bits;
    logic [63:0] rt_replay_bits;
    logic [31:0] trace_fifo_assert;
    rr_trace_rw_cnts_t trace_rw_cnts;
    rr_trace_merge_cnts_t trace_merge_cnts;
} storage_axi_read_csr_t;

// rr_mode_csr_t is a interpretation of the RR_MODE csr
// NOTE: do not forget to sync with the cl_fpgarr.{c,h} (the software lib)
typedef struct packed {
  logic outputValidateEn;     // bit 2
  logic replayEn;             // bit 1
  logic recordEn;             // bit 0
} rr_mode_csr_t;

typedef struct packed {
  struct packed {
    struct packed {
      logic wb_record_inst;         // bit 39
      logic pcim_replayer;          // bit 38
      logic pcis_replayer;          // bit 37
      logic sda_replayer;           // bit 36
      logic ocl_replayer;           // bit 35
      logic bar1_replayer;          // bit 34
      logic wb_validate_inst;       // bit 33
      logic pcimB_buf;              // bit 32
    } xpm_overflow;
    struct packed {
      logic wb_record_inst;         // bit 31
      logic pcim_replayer;          // bit 30
      logic pcis_replayer;          // bit 29
      logic sda_replayer;           // bit 28
      logic ocl_replayer;           // bit 27
      logic bar1_replayer;          // bit 26
      logic wb_validate_inst;       // bit 25
      logic pcimB_buf;              // bit 24
    } xpm_underflow;
  } oneoff;
  struct packed {
    struct packed {
      logic wb_record_hi;           // bit 23
      logic wb_record_lo;           // bit 22
      logic wb_validate_hi;         // bit 21
      logic wb_validate_lo;         // bit 20
      logic pcimB_buf;              // bit 19
      struct packed {
        logic [13:0] almful;        // bit 5-18
        logic [4:0] rdyrply_almful; // bit 0-4
      } replay_bus; // end is 0-40
    } almful;
  } rt;
} rr_state_csr_t;

typedef struct packed {
  struct packed {
    logic [63:0] bits_non_aligned;
    logic [31:0] fifo_wr_cnt;
  } fifo_wr_dbg;
  struct packed {
    logic [31:0] pcim_R;
    logic [31:0] sda_AW;
    logic [31:0] bar1_W;
    logic [31:0] ocl_AR;
    logic [31:0] pcis_AW;
    logic [31:0] ocl_AW;
    logic [31:0] ocl_W;
    logic [31:0] bar1_AW;
    logic [31:0] pcis_W;
    logic [31:0] pcis_B;
    logic [31:0] pcis_AR;
    logic [31:0] sda_AR;
    logic [31:0] sda_W;
    logic [31:0] bar1_AR;
  } chpkt_cnt;
} rr_packed2wb_dbg_csr_t;

typedef struct packed {
  // 161 bits, each need 6 CSRs to cover
  logic pc_asserted;
  logic [159:0] pc_status;
} pchk_report_t;
typedef struct packed {
   pchk_report_t logging_wb_pchk;
   pchk_report_t validation_wb_pchk;
   pchk_report_t cl_pcim_pchk;
   pchk_report_t sh_pcim_pchk;
} pcim_interconnect_dbg_csr_t;
`endif
// template
////////////////////////////////////////////////////////////////////////////////
//////////////////////////     garbage      ////////////////////////////////////
//////////////////////////   end of garbage ////////////////////////////////////
