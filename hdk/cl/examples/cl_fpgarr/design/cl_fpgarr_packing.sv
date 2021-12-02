`include "cl_fpgarr_types.svh"
`include "cl_fpgarr_packing_cfg.svh"

////////////////////////////////////////////////////////////////////////////////
// Interface for logb bus packing (only used in this file)
// this is a one-direction pipeline, almful is maintained separately
////////////////////////////////////////////////////////////////////////////////
`define PACKED_LOGB_BUS_JOIN2(inA, inB, name)\
  rr_packed_logb_bus_t #(inA.FULL_WIDTH + inB.FULL_WIDTH) name()
`define PACKED_LOGB_BUS_DUP(in, name)\
  rr_packed_logb_bus_t #(in.FULL_WIDTH) name()
interface rr_packed_logb_bus_t #(
   parameter FULL_WIDTH
);
parameter OFFSET_WIDTH = $clog2(FULL_WIDTH+1);
//NOTE: data and len are only meaningful when any_valid is true
logic any_valid;
logic [FULL_WIDTH-1:0] data;
logic [OFFSET_WIDTH-1:0] len;
modport P (output any_valid, data, len);
modport C (input any_valid, data, len);
endinterface

module rr_packed_logb_bus_pipe (
   input wire clk,
   input wire rstn,
   rr_packed_logb_bus_t.C in,
   rr_packed_logb_bus_t.P out
);
// parameter check
if (in.FULL_WIDTH != out.FULL_WIDTH)
   $error("FULL_WIDTH mismatches: in %d, out %d\n", in.FULL_WIDTH, out.FULL_WIDTH);
always_ff @(posedge clk) begin
  if (!rstn)
    out.any_valid <= 0;
  else
    out.any_valid <= in.any_valid;
  out.data <= in.data;
  out.len <= in.len;
end
endmodule

module rr_logging_bus_marshaller2 #(
   parameter FULL_WIDTH_A,
   parameter FULL_WIDTH_B
) (
   input wire clk,
   input wire rstn,
   rr_packed_logb_bus_t.C inA,
   rr_packed_logb_bus_t.C inB,
   rr_packed_logb_bus_t.P out
);

// parameter check
generate
   if (inA.FULL_WIDTH + inB.FULL_WIDTH != out.FULL_WIDTH)
      $error("FULL_WIDTH mismatches: inA %d, inB %d, out %d\n",
         inA.FULL_WIDTH, inB.FULL_WIDTH, out.FULL_WIDTH);
endgenerate

// Data packing!
// TODO: workaround vcs. If I do not require the FULL_WIDTH_X parameterization
// but instead use inX.FULL_WIDTH, the following interface instantiation will
// break (the .FULL_WIDTH will always be zero)
// Don't believe? Uncomment the following and see it yourself
//   $info("inA.FULL_WIDTH %d before\n", inA.FULL_WIDTH);
//   rr_packed_logb_bus_t #(inA.FULL_WIDTH) test();
//   $info("inA.FULL_WIDTH %d after, bus WIDTH %d\n",
//     inA.FULL_WIDTH, test.FULL_WIDTH);
rr_packed_logb_bus_t #(FULL_WIDTH_A) inA_q();
rr_packed_logb_bus_t #(FULL_WIDTH_B) inB_q();

rr_packed_logb_bus_pipe inA_pipe (
   .clk(clk),
   .rstn(rstn),
   .in(inA),
   .out(inA_q)
);
rr_packed_logb_bus_pipe inB_pipe (
   .clk(clk),
   .rstn(rstn),
   .in(inB),
   .out(inB_q)
);

assign out.any_valid = inA_q.any_valid || inB_q.any_valid;
logic [inA.OFFSET_WIDTH-1:0] valid_len_A;
logic [inB.OFFSET_WIDTH-1:0] valid_len_B;
always_comb begin
   valid_len_A = inA_q.any_valid? inA_q.len: 0;
   valid_len_B = inB_q.any_valid? inB_q.len: 0;
   out.len = out.OFFSET_WIDTH'(valid_len_A) + out.OFFSET_WIDTH'(valid_len_B);
   out.data = 'bx;
   // do not use "if" to avoid latches
`ifdef SIMULATION_AVOID_X
   out.data[0 +: inA.FULL_WIDTH] = inA_q.any_valid ? inA_q.data : 0;
   out.data[valid_len_A +: inB.FULL_WIDTH] = inB_q.any_valid ? inB_q.data : 0;
   out.data[out.len +: PACKET_ALIGNMENT] = 0;
`else
   out.data[0 +: inA.FULL_WIDTH] = inA_q.data;
   out.data[valid_len_A +: inB.FULL_WIDTH] = inB_q.data;
`endif
end
`ifdef SIMULATION_AVOID_X
  logic [2*FULL_WIDTH_A-1:0] check_A;
  logic [2*FULL_WIDTH_B-1:0] check_B;
  logic [2*out.FULL_WIDTH-1:0] check_O;
  always_ff @(posedge clk)
    if (rstn) begin
      if (inA_q.any_valid) begin
        check_A[0 +: FULL_WIDTH_A] = inA_q.data;
        check_A[inA_q.len +: FULL_WIDTH_A] = 0;
        noxA: assert(!$isunknown(check_A[0 +: FULL_WIDTH_A]));
      end
      if (inB_q.any_valid) begin
        check_B[0 +: FULL_WIDTH_B] = inB_q.data;
        check_B[inB_q.len +: FULL_WIDTH_B] = 0;
        noxB: assert(!$isunknown(check_B[0 +: FULL_WIDTH_B]));
      end
      if (out.any_valid) begin
        check_O[0 +: out.FULL_WIDTH] = out.data;
        check_O[out.len +: out.FULL_WIDTH] = 0;
        noxO: assert(!$isunknown(check_O[0 +: out.FULL_WIDTH]));
      end
    end
`endif
endmodule

module rr_logging_bus_unpack2pack #(
  parameter int MERGE_TREE_HEIGHT,
  parameter int MERGE_TREE_MAX_NODES,
  parameter int NODES_PER_LAYER [0:MERGE_TREE_HEIGHT-1],
  parameter int MERGE_PLAN
    [0:MERGE_TREE_HEIGHT-1] [0:MERGE_TREE_MAX_NODES-1][0:1],
  parameter string NAME
) (
   input wire clk,
   input wire rstn,
   rr_logging_bus_t.C in,
   rr_packed_logging_bus_t.P out
);

localparam int SHUFFLE_PLAN [0:MERGE_TREE_MAX_NODES-1] [0:1] = MERGE_PLAN[0];

// parameter check
generate
  if (in.LOGB_CHANNEL_CNT != out.LOGB_CHANNEL_CNT)
    $error("LOGB_CHANNEL_CNT mismatches: in %d, out %d\n",
      in.LOGB_CHANNEL_CNT, out.LOGB_CHANNEL_CNT);
  if (in.LOGB_CHANNEL_CNT != MERGE_TREE_MAX_NODES)
    $error("LOGB_CHANNEL_CNT mismatches: in %d, MERGE_TREE_MAX_NODES %d\n",
      in.LOGB_CHANNEL_CNT, MERGE_TREE_MAX_NODES);
  if (in.LOGE_CHANNEL_CNT != out.LOGE_CHANNEL_CNT)
    $error("LOGE_CHANNEL_CNT mismatches: in %d, out %d\n",
      in.LOGE_CHANNEL_CNT, out.LOGE_CHANNEL_CNT);
  if (in.LOGB_DATA_WIDTH != out.LOGB_DATA_WIDTH)
    $error("LOGB_DATA_WIDTH mismatches: in %d, out %d\n",
      in.LOGB_DATA_WIDTH, out.LOGB_DATA_WIDTH);
  if (MERGE_TREE_MAX_NODES != in.LOGB_CHANNEL_CNT)
    $error("MERGE_TREE_MAX_NODES mismatches: max nodes %d, LOGB %d\n",
      MERGE_TREE_MAX_NODES, in.LOGB_CHANNEL_CNT);
endgenerate
localparam LOGB_CHANNEL_CNT = in.LOGB_CHANNEL_CNT;
localparam bit [LOGB_CHANNEL_CNT-1:0]
  [RR_CHANNEL_WIDTH_BITS-1:0] CHANNEL_WIDTHS = in.CHANNEL_WIDTHS;
`DEF_GET_OFFSET(GET_OFFSET, CHANNEL_WIDTHS)
localparam LOGE_CHANNEL_CNT = in.LOGE_CHANNEL_CNT;

////////////////////////////////////////////////////////////////////////////////
// Extract rr_packed_logb_bus_t from rr_logging_bus_t
////////////////////////////////////////////////////////////////////////////////
genvar i;
generate
for (i=0; i < LOGB_CHANNEL_CNT; i=i+1) begin: packed_logb_gen
  localparam IDX = SHUFFLE_PLAN[i][0];
  localparam IDX2 = SHUFFLE_PLAN[i][1];
  localparam WIDTH = CHANNEL_WIDTHS[IDX];
  if (IDX != IDX2)
    $error("Invalid Channel Shuffle Plan at %d, plan is (%d, %d)\n",
      i, IDX, IDX2);
  rr_packed_logb_bus_t #(WIDTH) bus();
  `ifdef DEBUG_MERGE_TREE_STRUCTURE
  $info("Elaboration LOGB CHANNEL %d (W%d), as merge-tree leaf %d\n",
    IDX, WIDTH, i);
  `endif
  assign bus.any_valid = in.logb_valid[IDX];
  assign bus.data = in.logb_data[GET_OFFSET(IDX) +: WIDTH];
  assign bus.len = in.logb_valid[IDX]? bus.OFFSET_WIDTH'(WIDTH) : 0;
end
endgenerate

// expose the shuffled CHANNEL_WIDTHS outside. This is useful when decoding the
// trace buffer.
function automatic bit [LOGB_CHANNEL_CNT-1:0]
  [RR_CHANNEL_WIDTH_BITS-1:0] GET_SHUFFLED_CHANNEL_WIDTHS();
  for (int i=0; i < LOGB_CHANNEL_CNT; i=i+1) begin
    GET_SHUFFLED_CHANNEL_WIDTHS[i] = CHANNEL_WIDTHS[SHUFFLE_PLAN[i][0]];
  end
endfunction
parameter bit [LOGB_CHANNEL_CNT-1:0] [RR_CHANNEL_WIDTH_BITS-1:0]
  SHUFFLED_CHANNEL_WIDTHS = GET_SHUFFLED_CHANNEL_WIDTHS();


////////////////////////////////////////////////////////////////////////////////
// Constructing a binary merge tree to marshal all logb_data
////////////////////////////////////////////////////////////////////////////////
`define TREE_MARSHALLER2(_inA, _inB, _out) \
   `PACKED_LOGB_BUS_JOIN2(_inA, _inB, _out);\
   rr_logging_bus_marshaller2 #(\
     .FULL_WIDTH_A(_inA.FULL_WIDTH), \
     .FULL_WIDTH_B(_inB.FULL_WIDTH)  \
   ) merge (.clk(clk), .rstn(rstn), .inA(_inA), .inB(_inB), .out(_out))
`define TREE_QUEUE(_in, _out) \
   `PACKED_LOGB_BUS_DUP(_in, _out); \
   rr_packed_logb_bus_pipe q(.clk(clk), .rstn(rstn), .in(_in), .out(_out))

// The aggregation/merge tree is controlled by cl_fpgarr_packing_cfg.svh
// There is an interesting macro MERGE_PLAN, which is organized in terms of
// layer (nodes in the tree with the same height), node (define the operation of
// an intermediate node in tree) and plan (merge two subtree or queue one
// subtree).
// Note that the height 0 layer of the MERGE_PLAN is reserved to specify the
// initial shuffleing of all channels, used above. The real merging structure
// starts from height 1.
// For more details, see cl_fpgarr_packing_cfg.svh and cl_fpgarr_treegen.py
genvar h; // height of the aggregation tree
generate
for (h=1; h < MERGE_TREE_HEIGHT; h=h+1) begin: tree_gen
  for (i=0; i < NODES_PER_LAYER[h]; i=i+1) begin: level_gen
    localparam LID = MERGE_PLAN[h][i][0];
    localparam RID = MERGE_PLAN[h][i][1];
    if (LID != RID) begin: agg_or_q
      // merge
      if (h==1) begin: node
         // can find two buses to merge, use marshaller2
         // plogb stands for packed logb
         `TREE_MARSHALLER2(
            packed_logb_gen[LID].bus,
            packed_logb_gen[RID].bus,
            plogb);
         `ifdef DEBUG_MERGE_TREE_STRUCTURE
         $info("Tree %s, Layer %d, Node %d(W%d), merging Leaf %d (W%d) and Leaf %d (W%d).\n",
            NAME, h, i, plogb.FULL_WIDTH,
            LID, packed_logb_gen[LID].bus.FULL_WIDTH,
            RID, packed_logb_gen[RID].bus.FULL_WIDTH);
         `endif
      end
      else begin: node
         `TREE_MARSHALLER2(
            tree_gen[h-1].level_gen[LID].agg_or_q.node.plogb,
            tree_gen[h-1].level_gen[RID].agg_or_q.node.plogb,
            plogb);
         `ifdef DEBUG_MERGE_TREE_STRUCTURE
         $info("Tree %s, Layer %d, Node %d(W%d), merging Leaf %d (W%d) and Leaf %d (W%d).\n",
            NAME, h, i, plogb.FULL_WIDTH,
            LID, tree_gen[h-1].level_gen[LID].agg_or_q.node.plogb.FULL_WIDTH,
            RID, tree_gen[h-1].level_gen[RID].agg_or_q.node.plogb.FULL_WIDTH);
         `endif
      end
    end
    else begin: agg_or_q
      // queue
      if (h==1) begin: node
         // trivially queue the signal to next level of tree
         `TREE_QUEUE(packed_logb_gen[LID].bus, plogb);
         `ifdef DEBUG_MERGE_TREE_STRUCTURE
         $info("Tree %s, Layer %d, Node %d(W%d), queue Leaf %d(W%d)\n",
            NAME, h, i, plogb.FULL_WIDTH,
            LID, packed_logb_gen[LID].bus.FULL_WIDTH);
         `endif
      end
      else begin: node
         `TREE_QUEUE(
            tree_gen[h-1].level_gen[LID].agg_or_q.node.plogb, plogb);
         `ifdef DEBUG_MERGE_TREE_STRUCTURE
         $info("Tree %s, Layer %d, Node %d(W%d), queue Leaf %d(W%d)\n",
            NAME, h, i, plogb.FULL_WIDTH,
            LID, tree_gen[h-1].level_gen[LID].agg_or_q.node.plogb.FULL_WIDTH);
         `endif
      end
    end
  end
end
endgenerate

// output packed_logb_bus, register MERGETREE_QUEUE_NSTAGES more stages for
// timing
`undef TREE_TOP
`define TREE_TOP tree_gen[MERGE_TREE_HEIGHT-1].level_gen[0].agg_or_q.node.plogb
lib_pipe #(
  .WIDTH(1),
  .STAGES(MERGETREE_OUT_QUEUE_NSTAGES)
) plogb_any_valid_pipe (
  .clk(clk), .rst_n(rstn),
  .in_bus(`TREE_TOP.any_valid),
  .out_bus(out.plogb.any_valid)
);
lib_pipe #(
  .WIDTH(out.LOGB_DATA_WIDTH),
  .STAGES(MERGETREE_OUT_QUEUE_NSTAGES)
) plogb_data_pipe (
  .clk(clk), .rst_n(rstn),
  .in_bus(`TREE_TOP.data),
  .out_bus(out.plogb.data)
);
lib_pipe #(
  .WIDTH(out.LOGB_OFFSET_WIDTH),
  .STAGES(MERGETREE_OUT_QUEUE_NSTAGES)
) plogb_len_pipe (
  .clk(clk), .rst_n(rstn),
  .in_bus(`TREE_TOP.len),
  .out_bus(out.plogb.len)
);

localparam QUEUE_NSTAGES = (MERGE_TREE_HEIGHT - 1) + MERGETREE_OUT_QUEUE_NSTAGES;
// Queue logb_valid and loge_valid for the correct number of cycles
// i.e. the stages of the tree itself plus the stages queued for the output of
// the tree
generate
for (i=0; i < in.LOGB_CHANNEL_CNT; i=i+1) begin: logb_gen
  // shuffle logb_valid together with logb_data according to the SHUFFLE_PLAN
  localparam IDX = SHUFFLE_PLAN[i][0];
  lib_pipe #(
    .WIDTH(1),
    .STAGES(QUEUE_NSTAGES)
  ) logb_valid_pipe (
    .clk(clk), .rst_n(rstn),
    .in_bus(in.logb_valid[IDX]),
    .out_bus(out.logb_valid[i])
  );
end
for (i=0; i < in.LOGE_CHANNEL_CNT; i=i+1) begin: loge_gen
  // loge_valid are never shuffled
  // because loge_valid are not packed in the merge tree
  lib_pipe #(
    .WIDTH(1),
    .STAGES(QUEUE_NSTAGES)
  ) logge_valid_pipe (
    .clk(clk), .rst_n(rstn),
    .in_bus(in.loge_valid[i]),
    .out_bus(out.loge_valid[i])
  );
end
endgenerate

// As a result, I ignore almful of all pipeline stages in the merge tree and chose to maintain
// the logb_almful signal of input unpacked logger buses myself.
lib_pipe #(.WIDTH(1), .STAGES(QUEUE_NSTAGES)) in_logb_almful_hi_pipe (
   .clk(clk), .rst_n(rstn),
   .in_bus(out.logb_almful_hi),
   .out_bus(in.logb_almful_hi));
lib_pipe #(.WIDTH(1), .STAGES(QUEUE_NSTAGES)) in_logb_almful_lo_pipe (
   .clk(clk), .rst_n(rstn),
   .in_bus(out.logb_almful_lo),
   .out_bus(in.logb_almful_lo));
endmodule
