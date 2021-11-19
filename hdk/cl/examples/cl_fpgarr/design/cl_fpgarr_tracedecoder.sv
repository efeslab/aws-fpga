`include "cl_fpgarr_defs.svh"

// High level design notes:
// 1. Since I want to make individual replay channel to be asynchronous. That
// means each replay channel has its own valid/ready signal and one full channel
// does not impact other channels as long as the rr logging unit does not have
// new packets for this channel to replay. So there is no place to put a shared
// loge_valid in each interface, since the channels inside each interface are
// asynchronous. As a result, I should duplicate the loge_valid for each channel
// at the very beginning of trace decoding.
//

////////////////////////////////////////////////////////////////////////////////
// Interface for replay bus packing (only used in this file)
////////////////////////////////////////////////////////////////////////////////
`define PACKED_REPLAY_BUS_JOIN2(inA, inB, name) \
  rr_packed_replay_bus_t #( \
    .LOGB_CHANNEL_CNT(inA.LOGB_CHANNEL_CNT + inB.LOGB_CHANNEL_CNT), \
    .CHANNEL_WIDTHS({inB.CHANNEL_WIDTHS, inA.CHANNEL_WIDTHS}), \
    .LOGE_CHANNEL_CNT(inA.LOGE_CHANNEL_CNT)) name()
`define PACKED_REPLAY_BUS_DUP(in, name) \
  rr_packed_replay_bus_t #( \
    .LOGB_CHANNEL_CNT(in.LOGB_CHANNEL_CNT), \
    .CHANNEL_WIDTHS(in.CHANNEL_WIDTHS), \
    .LOGE_CHANNEL_CNT(in.LOGE_CHANNEL_CNT)) name()
// rr_packed_replay_bus_t holds the packed logb_data
// This is used in the demarshaller tree.
// LOGE_CHANNEL_CNT are the number of loge_valid to track for all channels (i.e.
// channel count). This is not aggregated in the demarshaller tree.
interface rr_packed_replay_bus_t #(
   parameter int LOGB_CHANNEL_CNT,
   parameter bit [LOGB_CHANNEL_CNT-1:0]
     [RR_CHANNEL_WIDTH_BITS-1:0] CHANNEL_WIDTHS,
   parameter int LOGE_CHANNEL_CNT
);
`DEF_SUM_WIDTH(GET_LOGB_DATA_WIDTH, CHANNEL_WIDTHS, 0, LOGB_CHANNEL_CNT)
// This LOGB_DATA_WIDTH does not include logb_valid
parameter int LOGB_DATA_WIDTH = GET_LOGB_DATA_WIDTH();
logic valid;
logic [LOGB_CHANNEL_CNT-1:0] logb_valid;
logic [LOGB_DATA_WIDTH-1:0] logb_data;
logic [LOGE_CHANNEL_CNT-1:0] loge_valid;
logic almful;

modport P(output valid, logb_valid, logb_data, loge_valid, input almful);
modport C(input valid, logb_valid, logb_data, loge_valid, output almful);
endinterface

module rr_packed_replay_bus_pipe (
  input wire clk,
  input wire rstn,
  rr_packed_replay_bus_t.C in,
  rr_packed_replay_bus_t.P out
);
// parameter check
if (in.LOGB_DATA_WIDTH != out.LOGB_DATA_WIDTH)
  $error("LOGB_DATA_WIDTH mismatch: in %d, out %d\n",
    in.LOGB_DATA_WIDTH, out.LOGB_DATA_WIDTH);
if (in.LOGB_CHANNEL_CNT != out.LOGB_CHANNEL_CNT)
  $error("LOGB_CHANNEL_CNT mismatch: in %d, out %d\n",
    in.LOGB_CHANNEL_CNT, out.LOGB_CHANNEL_CNT);
if (in.LOGE_CHANNEL_CNT != out.LOGE_CHANNEL_CNT)
  $error("LOGE_CHANNEL_CNT mismatch: in %d, out %d\n",
    in.LOGE_CHANNEL_CNT, out.LOGE_CHANNEL_CNT);
always_ff @(posedge clk) begin
  if (!rstn)
    out.valid <= 0;
  else
    out.valid <= in.valid;
  out.logb_valid <= in.logb_valid;
  out.loge_valid <= in.loge_valid;
  out.logb_data <= in.logb_data;
  in.almful <= out.almful;
end
endmodule

// The SHUFFLED_CHANNEL_WIDTHS is the channel widths config used in the replay
// bus.
// The CHANNEL_WIDTHS is the original config without shuffling.
// The input is one valid-ready channel for packed trace data of all channels
// The output should be N valid-ready channels containing unpacked data, one for
// each channel.
// Each channel also has a copy of the loge_valid of all other channels
// Those N valid-ready output channels then grouped by axi(s) interfaces and
// passed to the cl and do the final happen-before check there.
module rr_tracedecoder #(
  parameter int MERGE_TREE_HEIGHT,
  parameter int MERGE_TREE_MAX_NODES,
  parameter int NODES_PER_LAYER [0:MERGE_TREE_HEIGHT-1],
  parameter int MERGE_PLAN
    [0:MERGE_TREE_HEIGHT-1] [0:MERGE_TREE_MAX_NODES-1][0:1]
) (
  input wire clk,
  input wire rstn,
  rr_stream_bus_t.C packed_replay_bus,
  rr_replay_bus_t.P replay_bus
);

localparam int SHUFFLE_PLAN [0:MERGE_TREE_MAX_NODES-1] [0:1] = MERGE_PLAN[0];
localparam int LOGB_CHANNEL_CNT = replay_bus.LOGB_CHANNEL_CNT;
localparam bit [LOGB_CHANNEL_CNT-1:0] [RR_CHANNEL_WIDTH_BITS-1:0]
  CHANNEL_WIDTHS = replay_bus.CHANNEL_WIDTHS;
`DEF_GET_OFFSET(GET_OFFSET, CHANNEL_WIDTHS)
`DEF_SUM_WIDTH(GET_LOGB_DATA_WIDTH, CHANNEL_WIDTHS, 0, LOGB_CHANNEL_CNT)
// the LOGB_DATA_WIDTH only considers logb_data
parameter LOGB_DATA_WIDTH = GET_LOGB_DATA_WIDTH();
//
// Idea:
// Use a tree structure (from root to leaf) to distribute the unpacked logging
// data to each channel (individual logb and corresponding loge of all other
// channels)
// For each step in the distribution tree:
// 1. duplicate all loge
// 2. split logb and logb_data to two part: A_logb(_data) and B_logb(_data)
// 3. I need to reuse the MERGE_PLAN configuration and build a reverse tree?
//    Maybe try fifo this time(NO, lazy, no significant benefit).


// parameter check
localparam LOGE_CHANNEL_CNT = replay_bus.LOGE_CHANNEL_CNT;
if (LOGB_CHANNEL_CNT + LOGE_CHANNEL_CNT + LOGB_DATA_WIDTH !=
    packed_replay_bus.FULL_WIDTH)
  $error("Trace Decode FULL_WIDTH mismatch: logb W%d, loge W%d, ",
         LOGB_CHANNEL_CNT, LOGE_CHANNEL_CNT,
         "logb_data W%d, packed_replay_bus W%d\n",
         LOGB_DATA_WIDTH, packed_replay_bus.FULL_WIDTH);

////////////////////////////////////////////////////////////////////////////////
// Convert the shuffled rr_replay_bus to the unshuffled one
// According to the SHUFFLE_PLAN
// The shuffled rr_replay_bus is the output of the demarshaller tree structure
// This generate creates the leaf nodes of the demarshaller tree.
// Note that the loge_valid are never shuffled, so I just leave it be.
////////////////////////////////////////////////////////////////////////////////
genvar i;
generate
  for (i=0; i < LOGB_CHANNEL_CNT; i=i+1) begin: packed_replay_gen
    // connect shuffled replay bus at index i to the unshuffled replay_bus
    // at index IDX
    localparam IDX = SHUFFLE_PLAN[i][0];
    localparam IDX2 = SHUFFLE_PLAN[i][1];
    if (IDX != IDX2)
      $error("Invalid Channel Shuffle Plan at %d, plan is (%d, %d)\n",
        i, IDX, IDX2);
    rr_packed_replay_bus_t #(
      .LOGB_CHANNEL_CNT(1),
      .CHANNEL_WIDTHS(CHANNEL_WIDTHS[IDX]),
      .LOGE_CHANNEL_CNT(LOGE_CHANNEL_CNT)) bus();
    `ifdef DEBUG_MERGE_TREE_STRUCTURE
    $info("decoder converting packed_replay_gen[%d] to replay_bus[%d] (W%d)\n",
      i, IDX, CHANNEL_WIDTHS[IDX]);
    `endif
    assign replay_bus.valid[IDX] = bus.valid;
    assign replay_bus.logb_valid[IDX] = bus.logb_valid[0];
    assign replay_bus.logb_data[GET_OFFSET(IDX) +: CHANNEL_WIDTHS[IDX]] =
      bus.logb_data;
    assign replay_bus.loge_valid[IDX] = bus.loge_valid;
    assign bus.almful = replay_bus.almful[IDX];
  end
endgenerate

////////////////////////////////////////////////////////////////////////////////
// Constructing a binary merge tree to demarshal all logb_data
////////////////////////////////////////////////////////////////////////////////
`define TREE_DEMARSHALLER2(_in, _outA, _outB) \
  `PACKED_REPLAY_BUS_JOIN2(_outA, _outB, _in); \
  rr_trace_demarshaller2 split (.clk(clk), .rstn(rstn), \
    .in(_in), .outA(_outA), .outB(_outB))
`undef TREE_QUEUE
// define new interface for _in, then wire from _in to _out
`define TREE_QUEUE(_in, _out) \
  `PACKED_REPLAY_BUS_DUP(_out, _in); \
  rr_packed_replay_bus_pipe q(.clk(clk), .rstn(rstn), .in(_in), .out(_out))

genvar h;
generate
for (h=1; h < MERGE_TREE_HEIGHT; h=h+1) begin: tree_gen
  for (i=0; i < NODES_PER_LAYER[h]; i=i+1) begin: level_gen
    localparam LID = MERGE_PLAN[h][i][0];
    localparam RID = MERGE_PLAN[h][i][1];
    if (LID != RID) begin: split_or_q
      // split
      if (h==1) begin: node
        // prbus stands for packed replay bus
        `TREE_DEMARSHALLER2(prbus,
          packed_replay_gen[LID].bus,
          packed_replay_gen[RID].bus);
        `ifdef DEBUG_MERGE_TREE_STRUCTURE
        $info("Decoder Layer %d, splitting Node %d(W%d) to Leaf %d(W%d) and Leaf %d(W%d).\n",
           h, i, prbus.LOGB_DATA_WIDTH,
           LID, packed_replay_gen[LID].bus.LOGB_DATA_WIDTH,
           RID, packed_replay_gen[RID].bus.LOGB_DATA_WIDTH);
        `endif
      end
      else begin: node
        `TREE_DEMARSHALLER2(prbus,
          tree_gen[h-1].level_gen[LID].split_or_q.node.prbus,
          tree_gen[h-1].level_gen[RID].split_or_q.node.prbus);
        `ifdef DEBUG_MERGE_TREE_STRUCTURE
        $info("Decoder Layer %d, splitting Node %d(W%d) to Leaf %d(W%d) and Leaf %d(W%d).\n",
          h, i, prbus.LOGB_DATA_WIDTH,
          LID, tree_gen[h-1].level_gen[LID].split_or_q.node.prbus.LOGB_DATA_WIDTH,
          RID, tree_gen[h-1].level_gen[RID].split_or_q.node.prbus.LOGB_DATA_WIDTH);
        `endif
      end
    end
    else begin: split_or_q
      // queue
      if (h==1) begin: node
        `TREE_QUEUE(prbus, packed_replay_gen[LID].bus);
        `ifdef DEBUG_MERGE_TREE_STRUCTURE
        $info("Decoder Layer %d, Node %d(W%d), queue Leaf %d(W%d).\n",
          h, i, prbus.LOGB_DATA_WIDTH, LID,
          packed_replay_gen[LID].bus.LOGB_DATA_WIDTH);
        `endif
      end
      else begin: node
        `TREE_QUEUE(prbus,
          tree_gen[h-1].level_gen[LID].split_or_q.node.prbus);
        `ifdef DEBUG_MERGE_TREE_STRUCTURE
        $info("Decoder Layer %d, Node %d(W%d), queue Leaf %d(W%d).\n",
          h, i, prbus.LOGB_DATA_WIDTH, LID,
          tree_gen[h-1].level_gen[LID].split_or_q.node.prbus.LOGB_DATA_WIDTH);
        `endif
      end
    end
  end
end
endgenerate

// convert input rr_stream_bus_t (packed_replay_bus) to
// rr_packed_replay_bus_t (top of the tree)
// rr_stream_bus_t:
// from LSB to MSB:
// logb_valid, loge_valid, packed_logb_data
`undef TREE_TOP
`define TREE_TOP \
  tree_gen[MERGE_TREE_HEIGHT-1].level_gen[0].split_or_q.node.prbus

lib_pipe #(
  .WIDTH(1), .STAGES(MERGETREE_OUT_QUEUE_NSTAGES)
) valid_pipe (
  .clk(clk), .rst_n(rstn),
  .in_bus(packed_replay_bus.valid && packed_replay_bus.ready),
  .out_bus(`TREE_TOP.valid)
);
lib_pipe #(
  .WIDTH(LOGB_CHANNEL_CNT), .STAGES(MERGETREE_OUT_QUEUE_NSTAGES)
) logb_valid_pipe (
  .clk(clk), .rst_n(rstn),
  .in_bus(packed_replay_bus.data[0 +: LOGB_CHANNEL_CNT]),
  .out_bus(`TREE_TOP.logb_valid)
);
lib_pipe #(
  .WIDTH(LOGE_CHANNEL_CNT), .STAGES(MERGETREE_OUT_QUEUE_NSTAGES)
) loge_valid_pipe (
  .clk(clk), .rst_n(rstn),
  .in_bus(packed_replay_bus.data[LOGB_CHANNEL_CNT +: LOGE_CHANNEL_CNT]),
  .out_bus(`TREE_TOP.loge_valid)
);
lib_pipe #(
  .WIDTH(LOGB_DATA_WIDTH), .STAGES(MERGETREE_OUT_QUEUE_NSTAGES)
) logb_data_pipe (
  .clk(clk), .rst_n(rstn),
  .in_bus(packed_replay_bus.data[
    LOGB_CHANNEL_CNT + LOGE_CHANNEL_CNT +: LOGB_DATA_WIDTH]),
  .out_bus(`TREE_TOP.logb_data)
);
// for almful
logic packed_replay_bus_almful;
lib_pipe #(
  .WIDTH(1), .STAGES(MERGETREE_OUT_QUEUE_NSTAGES)
) almful_pipe (
  .clk(clk), .rst_n(rstn),
  .in_bus(`TREE_TOP.almful),
  .out_bus(packed_replay_bus_almful)
);
assign packed_replay_bus.ready = !packed_replay_bus_almful;
endmodule

// The input packed replay will be demarshalled to two subtree/leaves
// The lower LOGB_LEFT_CNT will go to the left subtree.
// The higher LOGB_RIGHT_CNT will go to the rigth subtree.
// The LOGE_CHANNEL_CNT does not aggregate, loge_valid is duplicated and goes to
// both subtrees.
// Note that the logb_valid and loge_valid are equally important. There are
// "valid" data to distribute from the root packed replay bus to subtrees even
// there is no logb packets to replay, since you still need to care loge_valid.
module rr_trace_demarshaller2 (
  input wire clk,
  input wire rstn,
  rr_packed_replay_bus_t.C in,
  rr_packed_replay_bus_t.P outA,
  rr_packed_replay_bus_t.P outB
);
localparam int LOGB_CHANNEL_CNT = in.LOGB_CHANNEL_CNT;
localparam bit [LOGB_CHANNEL_CNT-1:0]
  [RR_CHANNEL_WIDTH_BITS-1:0] CHANNEL_WIDTHS = in.CHANNEL_WIDTHS;
localparam LOGE_CHANNEL_CNT = in.LOGE_CHANNEL_CNT;
localparam LOGB_LEFT_CNT = outA.LOGB_CHANNEL_CNT;
localparam LOGB_RIGHT_CNT = outB.LOGB_CHANNEL_CNT;
`DEF_SUM_WIDTH(GET_LOGB_DATA_WIDTH, CHANNEL_WIDTHS, 0, LOGB_CHANNEL_CNT)
`DEF_SUM_WIDTH(GET_LEFT_WIDTH, CHANNEL_WIDTHS, 0, LOGB_LEFT_CNT)
`DEF_SUM_WIDTH(GET_RIGHT_WIDTH, CHANNEL_WIDTHS, LOGB_LEFT_CNT, LOGB_CHANNEL_CNT)
localparam LOGB_DATA_WIDTH = GET_LOGB_DATA_WIDTH();
localparam LEFT_WIDTH = GET_LEFT_WIDTH();
localparam RIGHT_WIDTH = GET_RIGHT_WIDTH();
localparam OFFSET_WIDTH = $clog2(LOGB_DATA_WIDTH+1);
function automatic [OFFSET_WIDTH-1:0] get_len_L
  (logic [LOGB_LEFT_CNT-1:0] logb_valid);
  get_len_L = 0;
  for (int i=0; i < LOGB_LEFT_CNT; i=i+1)
    if (logb_valid[i])
      get_len_L += OFFSET_WIDTH'(CHANNEL_WIDTHS[i]);
endfunction

// parameter check
generate
  if (LEFT_WIDTH != outA.LOGB_DATA_WIDTH)
    $error("LEFT LOGB_DATA_WIDTH mismatch: from parameter %d, out.A %d\n",
      LEFT_WIDTH, outA.LOGB_DATA_WIDTH);
  if (RIGHT_WIDTH != outB.LOGB_DATA_WIDTH)
    $error("RIGHT LOGB_DATA_WIDTH mismatch: from parameter %d, out.B %d\n",
      RIGHT_WIDTH, outB.LOGB_DATA_WIDTH);
  if (LOGB_CHANNEL_CNT != LOGB_LEFT_CNT + LOGB_RIGHT_CNT)
    $error("LOGB_CHANNEL_CNT mismatch: total %d, left %d, right %d\n",
      LOGB_CHANNEL_CNT, LOGB_LEFT_CNT, LOGB_RIGHT_CNT);
  if (LOGE_CHANNEL_CNT != outA.LOGE_CHANNEL_CNT)
    $error("LOGE_CHANNEL_CNT mismatch: from parameter %d, outA %d\n",
      LOGE_CHANNEL_CNT, outA.LOGE_CHANNEL_CNT);
  if (LOGE_CHANNEL_CNT != outB.LOGE_CHANNEL_CNT)
    $error("LOGE_CHANNEL_CNT mismatch: from paramete %d, outB %d\n",
      LOGE_CHANNEL_CNT, outB.LOGE_CHANNEL_CNT);
endgenerate

// register the input replay bus via a normal skidbuf (unlike recording, no need
// to synchronize timing here)
rr_packed_replay_bus_t #(
  .LOGB_CHANNEL_CNT(LOGB_CHANNEL_CNT),
  .CHANNEL_WIDTHS(CHANNEL_WIDTHS),
  .LOGE_CHANNEL_CNT(LOGE_CHANNEL_CNT)) in_q();
rr_packed_replay_bus_pipe in_pipe (
  .clk(clk), .rstn(rstn), .in(in), .out(in_q)
);
// decouple get_len_L from indexed part-select
logic [OFFSET_WIDTH-1:0] len_L;
always_ff @(posedge clk)
  if (!rstn)
    len_L <= 0;
  else
    len_L <= get_len_L(in.logb_valid[0 +: LOGB_LEFT_CNT]);

// in_q is almful if any of the two output is almful
assign in_q.almful = outA.almful || outB.almful;
// Duplicate valid and loge_valid
assign outA.valid = in_q.valid;
assign outB.valid = in_q.valid;
assign outA.loge_valid = in_q.loge_valid;
assign outB.loge_valid = in_q.loge_valid;
////// The de-marshaller
// The left subtree
logic [LOGB_LEFT_CNT-1:0] logb_valid_L;
assign logb_valid_L = in_q.logb_valid[0 +: LOGB_LEFT_CNT];
assign outA.logb_valid = logb_valid_L;
assign outA.logb_data = in_q.logb_data[0 +: LEFT_WIDTH];
// The right subtree
logic [LOGB_RIGHT_CNT-1:0] logb_valid_R;
assign logb_valid_R = in_q.logb_valid[LOGB_LEFT_CNT +: LOGB_RIGHT_CNT];
assign outB.logb_valid = logb_valid_R;
assign outB.logb_data = in_q.logb_data[len_L +: RIGHT_WIDTH];
endmodule
