`include "cl_fpgarr_types.svh"

////////////////////////////////////////////////////////////////////////////////
// Interface for logb bus packing (only used in this file)
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
logic ready;
modport P (output any_valid, data, len, input ready);
modport C (input any_valid, data, len, output ready);
endinterface

module rr_packed_logb_bus_sbuf (
   input wire clk,
   input wire rstn,
   rr_packed_logb_bus_t.C in,
   rr_packed_logb_bus_t.P out
);
// parameter check
generate
  if (in.FULL_WIDTH != out.FULL_WIDTH)
     $error("FULL_WIDTH mismatches: in %d, out %d\n", in.FULL_WIDTH, out.FULL_WIDTH);
endgenerate
transkidbuf #(.DATA_WIDTH(in.FULL_WIDTH + in.OFFSET_WIDTH)) sbuf (
   .clk(clk),
   .rstn(rstn),
   .in_valid(in.any_valid),
   .in_data({in.data, in.len}),
   .in_ready(in.ready),
   .out_valid(out.any_valid),
   .out_data({out.data, out.len}),
   .out_ready(out.ready)
);
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

rr_packed_logb_bus_sbuf inA_sbuf (
   .clk(clk),
   .rstn(rstn),
   .in(inA),
   .out(inA_q)
);
assign inA_q.ready = out.ready;
rr_packed_logb_bus_sbuf inB_sbuf (
   .clk(clk),
   .rstn(rstn),
   .in(inB),
   .out(inB_q)
);
assign inB_q.ready = out.ready;

assign out.any_valid = inA_q.any_valid || inB_q.any_valid;
logic [inA.OFFSET_WIDTH-1:0] valid_len_A;
logic [inB.OFFSET_WIDTH-1:0] valid_len_B;
always_comb begin
   valid_len_A = inA_q.any_valid? inA_q.len: 0;
   valid_len_B = inB_q.any_valid? inB_q.len: 0;
   out.len = out.OFFSET_WIDTH'(valid_len_A) + out.OFFSET_WIDTH'(valid_len_B);
   if (inA_q.any_valid)
      out.data[0 +: inA.FULL_WIDTH] = inA_q.data;
   if (inB_q.any_valid)
      out.data[valid_len_A +: inB.FULL_WIDTH] = inB_q.data;
end
endmodule

module rr_logging_bus_unpack2pack (
   input wire clk,
   input wire rstn,
   rr_logging_bus_t.C in,
   rr_packed_logging_bus_t.P out
);
// parameter check
generate
  if (in.LOGB_CHANNEL_CNT != out.LOGB_CHANNEL_CNT)
     $error("LOGB_CHANNEL_CNT mismatches: in %d, out %d\n",
       in.LOGB_CHANNEL_CNT, out.LOGB_CHANNEL_CNT);
  if (in.LOGE_CHANNEL_CNT != out.LOGE_CHANNEL_CNT)
     $error("LOGE_CHANNEL_CNT mismatches: in %d, out %d\n",
       in.LOGE_CHANNEL_CNT, out.LOGE_CHANNEL_CNT);
  if (in.FULL_WIDTH != out.FULL_WIDTH)
     $error("FULL_WIDTH mismatches: in %d, out %d\n", in.FULL_WIDTH, out.FULL_WIDTH);
endgenerate
localparam LOGB_CHANNEL_CNT = in.LOGB_CHANNEL_CNT;
localparam bit [LOGB_CHANNEL_CNT-1:0] [RR_CHANNEL_WIDTH_BITS-1:0] CHANNEL_WIDTHS = in.CHANNEL_WIDTHS;
`DEF_GET_OFFSET(CHANNEL_WIDTHS)

////////////////////////////////////////////////////////////////////////////////
// Extract rr_packed_logb_bus_t from rr_logging_bus_t
////////////////////////////////////////////////////////////////////////////////
genvar i;
generate
for (i=0; i < in.LOGB_CHANNEL_CNT; i=i+1) begin: packed_logb_gen
   rr_packed_logb_bus_t #(CHANNEL_WIDTHS[i]) bus();
   $info("Elaboration LOGB CHANNEL %d, width %d\n", i, bus.FULL_WIDTH);
   assign bus.any_valid = in.logb_valid[i];
   assign bus.data = in.logb_data[GET_OFFSET(i) +: CHANNEL_WIDTHS[i]];
   assign bus.len = in.logb_valid[i]? bus.OFFSET_WIDTH'(CHANNEL_WIDTHS[i]) : 0;
end
endgenerate


////////////////////////////////////////////////////////////////////////////////
// Constructing a binary merge tree to marshall all logb_data
////////////////////////////////////////////////////////////////////////////////
// the height of the aggregation packing tree
// It is also the number of stages other signals should be queued
localparam AGG_TREE_HEIGHT = $clog2(in.LOGB_CHANNEL_CNT);

`define TREE_MARSHALLER2(_inA, _inB, _out) \
   `PACKED_LOGB_BUS_JOIN2(_inA, _inB, _out);\
   rr_logging_bus_marshaller2 #(\
     .FULL_WIDTH_A(_inA.FULL_WIDTH), \
     .FULL_WIDTH_B(_inB.FULL_WIDTH)  \
   ) merge (.clk(clk), .rstn(rstn), .inA(_inA), .inB(_inB), .out(_out))
`define TREE_QUEUE(_in, _out) \
   `PACKED_LOGB_BUS_DUP(_in, _out); \
   rr_packed_logb_bus_sbuf q(.clk(clk), .rstn(rstn), .in(_in), .out(_out))

// An example of the aggregation tree
// h=3               0       LEVEL_OUTN=1, PREV_LEVEL_OUTN=2
//                  /  \
//                 /    \
//                /      \
// h=2           0        1  LEVEL_OUTN=2, PREV_LEVEL_OUTN=3
//             /   \      |
//            /     \     |
// h=1       0       1    2  LEVEL_OUTN=3, PREV_LEVEL_OUTN=5
//          / \     / \   |
// h=0     0   1   2   3  4  LEVEL_OUTN=5, PREV_LEVEL_OUTN=9
//        / \ / \ / \ / \ |
// init   0 1 2 3 4 5 6 7 8  LOGB_CHANNEL_CNT=9
genvar h; // height of the aggregation tree
generate
for (h=0; h < AGG_TREE_HEIGHT; h=h+1) begin: tree_gen
   // LEVEL_OUTN: how many output packed_logb_bus this level should output
   localparam int LEVEL_OUTN = $ceil(LOGB_CHANNEL_CNT/$pow(2,h+1));
   localparam int PREV_LEVEL_OUTN = $ceil(LOGB_CHANNEL_CNT/$pow(2,h));
   // deal with leaf nodes
   for (i=0; i < LEVEL_OUTN; i=i+1) begin: level_gen
      if (2*i + 1 < PREV_LEVEL_OUTN) begin: agg_or_q
         if (h==0) begin: node
            // can find two buses to merge, use marshaller2
            // plogb stands for packed logb
            `TREE_MARSHALLER2(
               packed_logb_gen[2*i].bus,
               packed_logb_gen[2*i+1].bus,
               plogb);
            $info("Layer %d, Node %d(W%d), merging Leaf %d (W%d) and Leaf %d (W%d).\n",
               h, i, plogb.FULL_WIDTH,
               2*i, packed_logb_gen[2*i].bus.FULL_WIDTH,
               2*i+1, packed_logb_gen[2*i+1].bus.FULL_WIDTH);
         end
         else begin: node
            `TREE_MARSHALLER2(
               tree_gen[h-1].level_gen[2*i].agg_or_q.node.plogb,
               tree_gen[h-1].level_gen[2*i+1].agg_or_q.node.plogb,
               plogb);
            $info("Layer %d, Node %d(W%d), merging Leaf %d (W%d) and Leaf %d (W%d).\n",
               h, i, plogb.FULL_WIDTH,
               2*i, tree_gen[h-1].level_gen[2*i].agg_or_q.node.plogb.FULL_WIDTH,
               2*i+1, tree_gen[h-1].level_gen[2*i+1].agg_or_q.node.plogb.FULL_WIDTH);
         end
      end
      else begin: agg_or_q
         if (h==0) begin: node
            // trivially queue the signal to next level of tree
            `TREE_QUEUE(packed_logb_gen[2*i].bus, plogb);
            $info("Layer %d, Node %d(W%d), queue Leaf %d(W%d)\n",
               h, i, plogb.FULL_WIDTH,
               2*i, packed_logb_gen[2*i].bus.FULL_WIDTH);
         end
         else begin: node
            `TREE_QUEUE(
               tree_gen[h-1].level_gen[2*i].agg_or_q.node.plogb, plogb);
            $info("Layer %d, Node %d(W%d), queue Leaf %d(W%d)\n",
               h, i, plogb.FULL_WIDTH,
               2*i, tree_gen[h-1].level_gen[2*i].agg_or_q.node.plogb.FULL_WIDTH);
         end
      end
   end
end
endgenerate

// output packed_logb_bus
assign out.plogb.any_valid =
   tree_gen[AGG_TREE_HEIGHT-1].level_gen[0].agg_or_q.node.plogb.any_valid;
assign out.plogb.data =
   tree_gen[AGG_TREE_HEIGHT-1].level_gen[0].agg_or_q.node.plogb.data;
assign out.plogb.len =
   tree_gen[AGG_TREE_HEIGHT-1].level_gen[0].agg_or_q.node.plogb.len;
assign tree_gen[AGG_TREE_HEIGHT-1].level_gen[0].agg_or_q.node.plogb.ready = out.ready;

// Queue logb_valid and loge_valid for the correct number of cycles
generate
for (i=0; i < in.LOGB_CHANNEL_CNT; i=i+1) begin: logb_gen
   transkidbuf_pipeline #(
      .DATA_WIDTH(0),
      .PIPE_DEPTH(AGG_TREE_HEIGHT),
      .PASS_LAST_STALL(1)) sbuf_p (
      .clk(clk), .rstn(rstn),
      .in_valid(in.logb_valid[i]),
      .in_data(),
      .in_ready(),
      .out_valid(out.logb_valid[i]),
      .out_data(),
      .out_ready(out.ready)
   );
end
for (i=0; i < in.LOGE_CHANNEL_CNT; i=i+1) begin: loge_gen
   transkidbuf_pipeline #(
      .DATA_WIDTH(0),
      .PIPE_DEPTH(AGG_TREE_HEIGHT),
      .PASS_LAST_STALL(1)) sbuf_p (
      .clk(clk), .rstn(rstn),
      .in_valid(in.loge_valid[i]),
      .in_data(),
      .in_ready(),
      .out_valid(out.loge_valid[i]),
      .out_data(),
      .out_ready(out.ready)
   );
end
endgenerate

// when multiple transkidbufs(_pipeline) are instantiated with PASS_STALL==1,
// their in_ready signals are trivially one cycle off in-sync with out_ready.
// For more info, see transkidbuf.sv assertion "trivial_in_ready"
// As a result, I ignore in_ready of all transkidbuf instantiations and maintain
// the ready signal of input packed logger buses myself.
(* dont_touch = "true" *) logic in_ready_piped;
lib_pipe #(.WIDTH(1), .STAGES(AGG_TREE_HEIGHT)) in_ready_pipe(
   .clk(clk), .rst_n(rstn), .in_bus(out.ready), .out_bus(in_ready_piped));
assign in.ready = in_ready_piped;
endmodule

module rr_logging_bus_packer2 (
   rr_logging_bus_t.C inA,
   rr_logging_bus_t.C inB,
   rr_logging_bus_t.P out
);
// From here localparams for the out logging bus
localparam LOGB_CHANNEL_CNT = out.LOGB_CHANNEL_CNT;
localparam LOGE_CHANNEL_CNT = out.LOGE_CHANNEL_CNT;
localparam bit [LOGB_CHANNEL_CNT-1:0] [RR_CHANNEL_WIDTH_BITS-1:0] CHANNEL_WIDTHS = out.CHANNEL_WIDTHS;
function automatic bit
   check_CHANNEL_WIDTHS();
   int j=0;
      for (int i=0; i < inA.LOGB_CHANNEL_CNT; i=i+1) begin
         bit [RR_CHANNEL_WIDTH_BITS-1:0] out_width = out.CHANNEL_WIDTHS[j];
         bit [RR_CHANNEL_WIDTH_BITS-1:0] in_width = inA.CHANNEL_WIDTHS[i];
         if (out_width != in_width) begin
            $error("CHANNEL_WIDTHS mismatch out@%d(%d) != inA[%d](%d)", j,
               out_width, i, in_width);
            return 0;
         end
         j = j + 1;
      end
      for (int i=0; i < inB.LOGB_CHANNEL_CNT; i=i+1) begin
         bit [RR_CHANNEL_WIDTH_BITS-1:0] out_width = out.CHANNEL_WIDTHS[j];
         bit [RR_CHANNEL_WIDTH_BITS-1:0] in_width = inB.CHANNEL_WIDTHS[i];
         if (out_width != in_width) begin
            $error("CHANNEL_WIDTHS mismatch out@%d(%d) != inB[%d](%d)", j,
               out_width, i, in_width);
            return 0;
         end
         j = j + 1;
      end
   return 1;
endfunction
// parameter check
generate
   if (inA.LOGB_CHANNEL_CNT + inB.LOGB_CHANNEL_CNT != LOGB_CHANNEL_CNT) 
      $error("LOGB mismatches: inA %d, inB %d, out %d\n",
         inA.LOGB_CHANNEL_CNT, inB.LOGB_CHANNEL_CNT, LOGB_CHANNEL_CNT
      );
   if (inA.LOGE_CHANNEL_CNT + inB.LOGE_CHANNEL_CNT != LOGE_CHANNEL_CNT) 
      $error("LOGE mismatches: inA %d, inB %d, out %d\n",
         inA.LOGE_CHANNEL_CNT, inB.LOGE_CHANNEL_CNT, LOGE_CHANNEL_CNT
      );
   if (inA.FULL_WIDTH + inB.FULL_WIDTH != out.FULL_WIDTH)
      $error("FULL_WIDTH mismatches: inA %d, inB %d, out %d\n",
         inA.FULL_WIDTH, inB.FULL_WIDTH, out.FULL_WIDTH);
endgenerate
initial begin
   assert(check_CHANNEL_WIDTHS());
end
// end of parameter check
assign inA.ready = out.ready;
assign inB.ready = out.ready;
assign out.logb_valid[0 +: inA.LOGB_CHANNEL_CNT] = inA.logb_valid;
assign out.logb_valid[inA.LOGB_CHANNEL_CNT +: inB.LOGB_CHANNEL_CNT] = inB.logb_valid;
assign out.logb_data[0 +: inA.FULL_WIDTH] = inA.logb_data;
assign out.logb_data[inA.FULL_WIDTH +: inB.FULL_WIDTH] = inB.logb_data;
assign out.loge_valid[0 +: inA.LOGE_CHANNEL_CNT] = inA.loge_valid;
assign out.loge_valid[inA.LOGE_CHANNEL_CNT +: inB.LOGE_CHANNEL_CNT] = inB.loge_valid;
endmodule