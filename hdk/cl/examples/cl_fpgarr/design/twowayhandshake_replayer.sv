// LOGE_CHANNEL_CNT is the total number of loge of all channels from all
// interfaces
`ifdef FORMAL
`include "formal/properties.sv"
`endif
`include "cl_fpgarr_defs.svh"
`include "cl_fpgarr_packing_cfg.svh"

// The packet counter to enforce happen-before, whose width depends on the
// number of on-the-fly packets.
//
// More detailed explanation:
// The counter should be wide enough to guarantee that the rt_loge_cnt can be
// compared with loge_cnt.
// e.g. given 8 bit, imagine you put all representable integers [0..255] on
// a circle, then any two intergers whose difference is always < 128 (always on
// the same half-circle) can be compared.
// In this packet counter case, the max difference of rt_loge_cnt and loge_cnt
// happens when the replay fifo is full (i.e. almful takes effect).
// In this case, assuming the channel whose replay fifo is full is CHA, then the
// next packet to replay in CHA will see AT MOST "fifo-size" + "almful
// propagation" number of packets finishes (i.e. rt_loge) at another channel.
// So the max number number of on-the-fly packets is defined by the following
// formula:
// 1. size of the fifo
// 2. almful propagation delay due to the register pipeline
// 3. almful propagation delay due to the decoder merge tree
localparam ON_THE_FLY_CNT =
  REPLAY_FIFO_DEPTH +
  REPLAYER_PIPE_DEPTH +
  record_pkg::MERGE_TREE_HEIGHT - 1 + MERGETREE_OUT_QUEUE_NSTAGES;
localparam PKT_CNT_WIDTH = $clog2(2 * ON_THE_FLY_CNT);


// this replayer is to replay the valid signal
module twowayhandshake_replayer #(
  // these low numbers is to ease the proof
  parameter DATA_WIDTH=16,
  parameter LOGE_CHANNEL_CNT=2
) (
  input wire clk,
  input wire rstn,
  // the replay bus
  input wire in_valid,
  input wire logb_valid,
  input wire [DATA_WIDTH-1:0] logb_data,
  input wire [LOGE_CHANNEL_CNT-1:0] loge_valid,
  output reg in_ready,
  // the runtime loge_valid to check
  // This does not need a ready backpressure
  input wire [LOGE_CHANNEL_CNT-1:0] rt_loge_valid,
  // out channel
  output logic out_valid,
  input logic out_ready,
  output logic [DATA_WIDTH-1:0] out_data
);

////////////////////////////////////////////////////////////////////////////////
// state machine
//                  /--\ +- flow
//                  |  |
//           load   |  v   fill
//  -------   +    ------   +    ------
// |       | ---> |      | ---> |      |
// | Empty |      | Busy |      | Full |
// |       | <--- |      | <--- |      |
//  -------    -   ------    -   ------
//          unload         flush

typedef enum logic [1:0] { EMPTY, BUSY, FULL } FSM_t;
FSM_t state;
FSM_t state_next;
logic r_logb_valid;
logic [DATA_WIDTH-1:0] r_logb_data;
logic [LOGE_CHANNEL_CNT-1:0] r_loge_valid;
// registered output
logic o_logb_valid;
logic [DATA_WIDTH-1:0] o_logb_data;
logic [LOGE_CHANNEL_CNT-1:0] o_loge_valid;

always @(posedge clk)
if (!rstn)
  state <= EMPTY;
else
  state <= state_next;

logic insert_replay;
assign insert_replay = in_valid && in_ready;
logic remove_replay, remove_logb_done, remove_loge_done;
// finish replay a logb (need to wait for CL)
assign remove_logb_done = out_valid && out_ready;
// no logb to replay, just track the loge (1 cycle, fast path)
assign remove_loge_done = (state != EMPTY) && !o_logb_valid;
assign remove_replay = remove_logb_done || remove_loge_done;

always_comb
  case (state)
    EMPTY: begin
      if (insert_replay) // load
        state_next = BUSY;
      else
        state_next = EMPTY;
    end
    BUSY: begin
      if (insert_replay && !remove_replay) // fill
        state_next = FULL;
      else if (!insert_replay && remove_replay) // unload
        state_next = EMPTY;
      else
        // (insert_replay && remove_replay) || (!insert_replay && !remove_replay)
        // flow or idle
        state_next = BUSY;
    end
    FULL: begin
      if (!insert_replay && remove_replay)
        state_next = BUSY;
      else
        state_next = FULL;
    end
    default:
      state_next = state;
  endcase

// register buffer for replay_data
always @(posedge clk)
if (!rstn) begin
  r_logb_valid <= 0;
  r_logb_data <= 0;
  r_loge_valid <= 0;
end
else if ((state == BUSY) && (state_next == FULL)) begin
  r_logb_valid <= logb_valid;
  r_logb_data <= logb_data;
  r_loge_valid <= loge_valid;
end

// output register
always @(posedge clk)
if (!rstn) begin
  o_logb_data <= 0;
  o_loge_valid <= 0;
end
else if (state_next == BUSY)  begin
  if (state == FULL) begin
    o_logb_data <= r_logb_data;
    o_loge_valid <= r_loge_valid;
  end
  else if (insert_replay) begin // shifting from load or flow
    o_logb_data <= logb_data;
    o_loge_valid <= loge_valid;
  end
end
//// logb_valid is special, I need o_logb_valid_next to generate out_valid
logic o_logb_valid_next;
always_comb
  if (state_next == BUSY)
    if (state == FULL)
      o_logb_valid_next = r_logb_valid;
    else if (insert_replay)
      o_logb_valid_next = logb_valid;
    else
      o_logb_valid_next = o_logb_valid;
  else
      o_logb_valid_next = o_logb_valid;
always_ff @(posedge clk)
  if (!rstn)
    o_logb_valid <= 0;
  else
    o_logb_valid <= o_logb_valid_next;

////////////////////////////////////////////////////////////////////////////////
// Happen-before enforcement:
// Only allow replay if runtime packet counter >= replay packet counter
////////////////////////////////////////////////////////////////////////////////
// rt_sub_loge_cnt maintains the value of
// "runtime packet counter - replay packet counter" without considering what is
// going to be put in the output registers
// rt_sub_loge_cnt_next maintains similar thing but takes the output register
// into consideration.
// Such design is to decouple the packet counter calculation from output and
// register the `out_valid` to improve timing.
//
// It is OK to replay if runtime packet counter >= replay packet counter:
// In an unpacked logging bus, when logb_valid and loge_valid happen at the same
// time, the loge_valid is not counted towards to the replay packet counter of
// the logb_valid at the same cycle.
// But during the conversion from unpacked logging bus to a packed writeback
// bus, the loge_valid is counted towards to the replay packet counter of the
// logb_valid at the same cycle. This is to only encode loge_valid when there
// are some logb_valid to record.
logic [PKT_CNT_WIDTH-1:0] rt_sub_loge_cnt [LOGE_CHANNEL_CNT-1:0];
logic [PKT_CNT_WIDTH-1:0] rt_sub_loge_cnt_next [LOGE_CHANNEL_CNT-1:0];
logic [LOGE_CHANNEL_CNT-1:0] rt_sub_loge_cnt_sign;
generate
for (genvar i=0; i < LOGE_CHANNEL_CNT; i=i+1) begin: rt_sub_loge_gen
  always_comb
    if (state_next == BUSY) begin
      if (state == FULL) begin
        rt_sub_loge_cnt_next[i] = rt_sub_loge_cnt[i] + rt_loge_valid[i] - r_loge_valid[i];
      end
      else if (insert_replay) begin
        rt_sub_loge_cnt_next[i] = rt_sub_loge_cnt[i] + rt_loge_valid[i] - loge_valid[i];
      end
      else
        rt_sub_loge_cnt_next[i] = rt_sub_loge_cnt[i] + rt_loge_valid[i];
    end
    else
      rt_sub_loge_cnt_next[i] = rt_sub_loge_cnt[i] + rt_loge_valid[i];
  always_ff @(posedge clk)
    if (!rstn)
      rt_sub_loge_cnt[i] <= 0;
    else
      rt_sub_loge_cnt[i] <= rt_sub_loge_cnt_next[i];
  // sign is 0 --> runtime cnt - replay cnt is positive or zero,
  // runtime cnt >= replay cnt, thus OK to replay
  // else, should wait for the happen-before to be enforced
  assign rt_sub_loge_cnt_sign[i] = rt_sub_loge_cnt_next[i][PKT_CNT_WIDTH-1];
end
endgenerate
assign ok_to_replay = !(|rt_sub_loge_cnt_sign);

////////////////////////////////////////////////////////////////////////////////
// The replay logic
////////////////////////////////////////////////////////////////////////////////
// do something about ok_to_replay
always_ff @(posedge clk)
  if (!rstn)
    out_valid <= 0;
  else
    out_valid <= (state_next != EMPTY) && o_logb_valid_next && ok_to_replay;
assign out_data = o_logb_data;
always @(posedge clk)
if (!rstn)
  in_ready <= 0;
else
  in_ready <= (state_next != FULL);

`ifdef FORMAL
  `ifdef TWOWAYHANDSHAKE_REPLAYER_SELF
    `define ASSUME assume
    `define ASSERT assert
  `else
    `define ASSUME assert
    `define ASSERT assume
  `endif
  ////////////////////////////////////////////////////////////////////////////
  // Init (assumption)
  ////////////////////////////////////////////////////////////////////////////
  // {{{
  // reset properties
  `ifndef JASPERGOLD
  reg f_past_valid = 0;
  always @(posedge clk) begin
    if (!f_past_valid)
      `ASSUME(!rstn);
    f_past_valid <= 1;
  end
  `endif
  // }}} reset
  ////////////////////////////////////////////////////////////////////////////
  // Input AXI Stream (assumption)
  ////////////////////////////////////////////////////////////////////////////
  // {{{
  in_rst_am: `ASSUME property(RESET_CLEARS_VALID(clk, rstn, in_valid));
  in_held_am: `ASSUME property(HELD_VALID_DATA(clk, rstn, in_valid, in_ready,
    {logb_valid, logb_data, loge_valid}));
  `ifndef JASPERGOLD
  always @(posedge clk)
  if (f_past_valid)
  if ($past(!rstn))
      `ASSUME(!in_valid);
  else if ($past(in_valid && !in_ready && rstn) && rstn)
      `ASSUME(in_valid && $stable({logb_valid, logb_data, loge_valid}));
  `endif // JASPERGOLD
  // }}}
  ////////////////////////////////////////////////////////////////////////////
  // Output AXI Stream (correctness)
  ////////////////////////////////////////////////////////////////////////////
  // {{{
  out_rst_as: `ASSERT property(RESET_CLEARS_VALID(clk, rstn, out_valid));
  out_held_as: `ASSERT property(HELD_VALID_DATA(clk, rstn, out_valid, out_ready, out_data));
  // }}}
  ////////////////////////////////////////////////////////////////////////////
  // Packet Counting Properties
  ////////////////////////////////////////////////////////////////////////////
  // {{{
  localparam F_CNTWIDTH=DATA_WIDTH;
  reg [F_CNTWIDTH-1:0] in_logb_cnt;
  reg [F_CNTWIDTH-1:0] out_cnt;
  reg [PKT_CNT_WIDTH-1:0] in_loge_cnt [LOGE_CHANNEL_CNT-1:0];
  always @(posedge clk)
    if (!rstn) begin
      in_logb_cnt <= 0;
      out_cnt <= 0;
      for (int i=0; i < LOGE_CHANNEL_CNT; i=i+1)
        in_loge_cnt[i] <= 0;
    end
    else begin
      if (in_valid && in_ready) begin
        in_logb_cnt <= in_logb_cnt + logb_valid;
        for (int i=0; i < LOGE_CHANNEL_CNT; i=i+1)
          in_loge_cnt[i] <= in_loge_cnt[i] + loge_valid[i];
      end
      if (out_valid && out_ready)
        out_cnt <= out_cnt + F_CNTWIDTH'(1);

      // respect the on the fly packets does not cause cnt overflow
      for (int i=0; i < LOGE_CHANNEL_CNT; i=i+1) begin
        localparam bit [PKT_CNT_WIDTH-1:0] OTF = ON_THE_FLY_CNT;
        // runtime cnt ∈  replay cnt + [-OTF, OTF]
        on_the_fly: `ASSUME(
          (OTF+loge_cnt[i] >= rt_loge_cnt[i]) &&
          (OTF+rt_loge_cnt[i] >= loge_cnt[i])
        );
      end
    end
  // }}}

  // sequence ordering
  always @(posedge clk)
    if (rstn) begin
      if (in_valid && logb_valid)
        input_inorder: `ASSUME(logb_data == in_logb_cnt);
      if (out_valid)
        output_inorder: `ASSERT(out_data == out_cnt);

      for (int i=0; i < LOGE_CHANNEL_CNT; i=i+1) begin: loge_as
        if (state == BUSY)
          loge_match_BUSY_as: `ASSERT(
            in_loge_cnt[i] == o_loge_valid[i] + loge_cnt[i]);
        else if (state == FULL)
          loge_match_FULL_as: `ASSERT(
            in_loge_cnt[i] == o_loge_valid[i] + r_loge_valid[i]+ loge_cnt[i]);
        else // state == EMPTY
          loge_match_EMPTY_as: `ASSERT(in_loge_cnt[i] == loge_cnt[i]);
      end
    end

  // proof
  always @(posedge clk)
  if (rstn) begin
    if (state == EMPTY) begin
      `ASSERT(in_logb_cnt == out_cnt);
    end
    else if (state == BUSY) begin
      `ASSERT(out_cnt + o_logb_valid == in_logb_cnt);
      if (o_logb_valid)
        `ASSERT(o_logb_data == out_cnt);
    end
    else if (state == FULL) begin
      `ASSERT(out_cnt + o_logb_valid + r_logb_valid == in_logb_cnt);
      if (o_logb_valid)
        `ASSERT(o_logb_data == out_cnt);
      if (r_logb_valid)
        `ASSERT(r_logb_data + o_logb_valid == in_logb_cnt);
    end
    `ASSERT(state != 'b11);
  end

  check_trace: cover property (@(posedge clk)
    disable iff (!rstn)
    (insert_replay && remove_replay) [*3]
  );

  ////////////////////////////////////////////////////////////////////////////////
  // Old code to verify the equivalence of the two ways of enforcing happen
  // before
  ////////////////////////////////////////////////////////////////////////////////
  // Maintain runtime packet counter
  logic [PKT_CNT_WIDTH-1:0] rt_loge_cnt [LOGE_CHANNEL_CNT-1:0];
  always @(posedge clk)
    if (!rstn) begin
      for (int i=0; i < LOGE_CHANNEL_CNT; i=i+1)
        rt_loge_cnt[i] <= 0;
    end
    else begin
      for (int i=0; i < LOGE_CHANNEL_CNT; i=i+1) begin
        rt_loge_cnt[i] <= rt_loge_cnt[i] + rt_loge_valid[i];
      end
    end

  // Maintain replay packet counter
  logic [PKT_CNT_WIDTH-1:0] loge_cnt [LOGE_CHANNEL_CNT-1:0];
  wire [PKT_CNT_WIDTH-1:0] loge_cnt_next [LOGE_CHANNEL_CNT-1:0];
  genvar i;
  generate
    for (i=0; i < LOGE_CHANNEL_CNT; i=i+1)
      assign loge_cnt_next[i] = loge_cnt[i] + o_loge_valid[i];
  endgenerate
  always @(posedge clk)
    if (!rstn) begin
      for (int i=0; i < LOGE_CHANNEL_CNT; i=i+1)
        loge_cnt[i] <= 0;
    end
    else begin
      // unload, flow, flush
      if (remove_replay)
        for (int i=0; i < LOGE_CHANNEL_CNT; i=i+1)
          loge_cnt[i] <= loge_cnt_next[i];
    end

  // Compare the replay packet counters with runtime packet counters
  // OK to replay if replay counter <= runtime counter
  // It is OK to replay if runtime packet counter >= replay packet counter
  // In an unpacked logging bus, when logb_valid and loge_valid happen at the same
  // time, the loge_valid is not counted towards to the replay packet counter of
  // the logb_valid at the same cycle.
  // But during the conversion from unpacked logging bus to a packed writeback
  // bus, the loge_valid is counted towards to the replay packet counter of the
  // logb_valid at the same cycle. This is to only encode loge_valid when there
  // are some logb_valid to record.
  // So the replay packet counter should be loge_cnt_next, which is only valid if
  // in_valid.
  // the two's complement of replay packet counter
  wire [PKT_CNT_WIDTH-1:0] loge_cnt_neg [LOGE_CHANNEL_CNT-1:0];
  wire [PKT_CNT_WIDTH-1:0] pkt_cnt_sub [LOGE_CHANNEL_CNT-1:0];
  logic [LOGE_CHANNEL_CNT-1:0] pkt_cnt_sub_sign;
  logic old_ok_to_replay;
  generate 
    for (i=0; i < LOGE_CHANNEL_CNT; i=i+1) begin
      assign loge_cnt_neg[i] = ~loge_cnt_next[i] + PKT_CNT_WIDTH'(1);
      assign pkt_cnt_sub[i] = rt_loge_cnt[i] + loge_cnt_neg[i];
      // sign is 0 --> runtime cnt - replay cnt is positive or zero,
      // runtime cnt >= replay cnt, thus OK to replay
      // else, should wait for the happen-before to be enforced
      assign pkt_cnt_sub_sign[i] = pkt_cnt_sub[i][PKT_CNT_WIDTH-1];
    end
  endgenerate
  logic old_ok_to_replay;
  assign old_ok_to_replay = !(|pkt_cnt_sub_sign);

  logic old_out_valid;
  assign old_out_valid = (state != EMPTY) && o_logb_valid && old_ok_to_replay;

  equ_check: `ASSERT property (@(posedge clk)
    disable iff (!rstn)
    out_valid == old_out_valid
  );
`endif
endmodule

module twowayhandshake_ready_replayer #(
  // the total number of loge_valid from all channels
  parameter LOGE_CHANNEL_CNT = 5,
  parameter NUM_RDYRPLY = 1,
  parameter int LOGE_IDX [NUM_RDYRPLY-1:0] = {0}
) (
  input wire clk,
  input wire rstn,
  // parsed from the replay trace
  input wire in_valid,
  input wire [LOGE_CHANNEL_CNT-1:0] in_loge_valid,
  output wire in_ready,
  // from all replayers at runtime
  input wire [LOGE_CHANNEL_CNT-1:0] rt_loge_valid,
  // the generated ready signal
  output logic o_ready [NUM_RDYRPLY-1:0]
);

// parameter check
generate
if (NUM_RDYRPLY <= 0)
  $error("Invalid NUM_RDYRPLY %d", NUM_RDYRPLY);
for (genvar i=0; i < NUM_RDYRPLY; i=i+1)
  if (LOGE_IDX[i] < 0 || LOGE_IDX[i] >= LOGE_CHANNEL_CNT)
    $error("Invalid LOGE_IDX[%d] %d given LOGE_CHANNEL_CNT %d",
      i, LOGE_IDX[i], LOGE_CHANNEL_CNT);
endgenerate
// IDEA:
// 1. ok to take in the loge_valid of a logging unit if
//   "runtime packet counter >= replay packet counter" holds for ALL channels
//   (including the LOGE_IDX channel that I need to generate ready)
//   This is maintained by the `ok_to_replay_ready_sub`, which tells whether
//   "rt_loge_cnt - loge_cnt >= 0", rt_loge_cnt includes the current cycle
//   rt_loge_valid
logic [PKT_CNT_WIDTH-1:0] rt_sub_loge_cnt [LOGE_CHANNEL_CNT-1:0];
logic [PKT_CNT_WIDTH-1:0] ok_to_replay_ready_sub [LOGE_CHANNEL_CNT-1:0];
logic [LOGE_CHANNEL_CNT-1:0] ok_to_replay_ready;
// 2. I can assert the ready for the LOGE_IDX channel if
//   "runtime packet counter < replay packet counter" holds for the LOGE_IDX
//   channel
//   This is maintained by the `rt_sub_loge_cnt`, which tells whether
//   "rt_loge_cnt - loge_cnt >= 0", rt_loge_cnt and loge_cnt both exclude
//   current cycle rt_loge_valid and loge_valid, thus the ready can be
//   registered (i.e. loge_valid is taken at cyc 1, ready is asserted at cyc 2).
logic [PKT_CNT_WIDTH-1:0] rt_sub_loge_cnt_next [LOGE_CHANNEL_CNT-1:0];
logic [LOGE_CHANNEL_CNT-1:0] rt_sub_loge_cnt_sign;

generate
for (genvar i = 0; i < LOGE_CHANNEL_CNT; i=i+1) begin
  always_comb
    if (in_valid && in_ready)
      rt_sub_loge_cnt_next[i] = ok_to_replay_ready_sub[i] - in_loge_valid[i];
    else
      rt_sub_loge_cnt_next[i] = ok_to_replay_ready_sub[i];
  always_ff @(posedge clk)
    if (!rstn)
      rt_sub_loge_cnt[i] <= 0;
    else
      rt_sub_loge_cnt[i] <= rt_sub_loge_cnt_next[i];

  // sign is 0 --> runtime cnt - replay cnt is positive or zero,
  // runtime cnt >= replay cnt, thus OK to replay
  // else, should wait for the happen-before to be enforced
  // sign is 1 --> runtime cnt - replay cnt is negative
  // runtime cnt < replay cnt, thus OK to assert ready
  assign rt_sub_loge_cnt_sign[i] = rt_sub_loge_cnt_next[i][PKT_CNT_WIDTH-1];
  assign ok_to_replay_ready_sub[i] = rt_sub_loge_cnt[i] + rt_loge_valid[i];
  assign ok_to_replay_ready[i] = ok_to_replay_ready_sub[i][PKT_CNT_WIDTH-1];
end
endgenerate

assign in_ready = !(|ok_to_replay_ready);

generate
for (genvar i=0; i < NUM_RDYRPLY; i=i+1)
  always_ff @(posedge clk)
    if (!rstn)
      o_ready[i] <= 0;
    else
      o_ready[i] <= rt_sub_loge_cnt_sign[LOGE_IDX[i]];
endgenerate

`ifdef FORMAL
  `ifdef TWOWAYHANDSHAKE_READY_REPLAYER_SELF
    `define ASSUME assume
    `define ASSERT assert
  `else
    `define ASSUME assert
    `define ASSERT assume
  `endif
  ////////////////////////////////////////////////////////////////////////////
  // Input (assumption)
  ////////////////////////////////////////////////////////////////////////////
  // {{{
  in_rst_am: `ASSUME property(RESET_CLEARS_VALID(clk, rstn, in_valid));
  in_held_am: `ASSUME property(HELD_VALID_DATA(clk, rstn, in_valid, in_ready,
    in_loge_valid));
  logic o_valid [NUM_RDYRPLY-1:0];
  for (genvar i=0; i < NUM_RDYRPLY; i=i+1)
    cyclic_as: `ASSUME property (
      (o_valid[i] & o_ready[i]) == rt_loge_valid[LOGE_IDX[i]]
    );
  // }}}
  ////////////////////////////////////////////////////////////////////////////
  // Packet Counting Properties
  ////////////////////////////////////////////////////////////////////////////
  // {{{
  localparam F_CNTWIDTH = 32;
  reg [F_CNTWIDTH-1:0] in_loge_cnt [LOGE_CHANNEL_CNT-1:0];
  reg [F_CNTWIDTH-1:0] rt_loge_cnt [LOGE_CHANNEL_CNT-1:0];
  localparam bit [PKT_CNT_WIDTH-1:0] OTF = ON_THE_FLY_CNT;
  for (genvar i=0; i < LOGE_CHANNEL_CNT; i=i+1)
  always_ff @(posedge clk)
    if (!rstn) begin
      in_loge_cnt[i] <= 0;
      rt_loge_cnt[i] <= 0;
    end
    else begin
      if (in_valid && in_ready)
        in_loge_cnt[i] <= in_loge_cnt[i] + in_loge_valid[i];
      rt_loge_cnt[i] <= rt_loge_cnt[i] + rt_loge_valid[i];
      on_the_fly: `ASSUME(
        (OTF+in_loge_cnt[i] >= rt_loge_cnt[i]) &&
        (OTF+rt_loge_cnt[i]) >= in_loge_cnt[i]
      );
    end
  // }}}
  ////////////////////////////////////////////////////////////////////////////
  // Properties to prove
  ////////////////////////////////////////////////////////////////////////////
  // {{{
  for (genvar i=0; i < NUM_RDYRPLY; i=i+1)
    o_ready_as: `ASSERT property(@(posedge clk)
     disable iff (!rstn)
      o_ready[i] == (rt_loge_cnt[i] < in_loge_cnt[i])
    );
  // }}}
`endif // FORMAL
endmodule
