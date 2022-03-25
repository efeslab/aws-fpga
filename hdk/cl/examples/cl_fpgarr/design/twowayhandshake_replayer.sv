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
  parameter LOGE_CHANNEL_CNT=2,
  parameter DEBUG=0
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
// loge_valid-only packets are aggregated and not buffered at all
// only logb_valid will be buffered together with their corresponding
// vector clock (i.e. loge_cnt)
logic [DATA_WIDTH-1:0] r_logb_data;
logic [PKT_CNT_WIDTH-1:0] r_loge_cnt [LOGE_CHANNEL_CNT-1:0];
// registered output
logic [DATA_WIDTH-1:0] o_logb_data;
logic [PKT_CNT_WIDTH-1:0] o_loge_cnt [LOGE_CHANNEL_CNT-1:0];
logic [PKT_CNT_WIDTH-1:0] o_loge_cnt_next [LOGE_CHANNEL_CNT-1:0];

logic insert_replay, remove_replay;
assign insert_replay = in_valid && in_ready && logb_valid;
assign remove_replay = out_valid && out_ready;
////////////////////////////////////////////////////////////////////////////////
// Vector clock forward declarement
// loge_cnt aggregates all incoming loge_valid (i.e. the replay packet counter)
// rt_loge_cnt aggregates all incoming real-time loge_valid (i.e. runtime packet
// counter)
// Only allow replay a valid if runtime packet counter >= replay packet counter
// In the following state machine, only logb_valid (a transaction begin/valid
// to replay) will be buffered. All loge_valid will be consumed immediately.
////////////////////////////////////////////////////////////////////////////////
logic [PKT_CNT_WIDTH-1:0] rt_loge_cnt [LOGE_CHANNEL_CNT-1:0];
wire [PKT_CNT_WIDTH-1:0] rt_loge_cnt_next [LOGE_CHANNEL_CNT-1:0];
logic [PKT_CNT_WIDTH-1:0] loge_cnt [LOGE_CHANNEL_CNT-1:0];
wire [PKT_CNT_WIDTH-1:0] loge_cnt_next [LOGE_CHANNEL_CNT-1:0];

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
always @(posedge clk)
if (!rstn)
  state <= EMPTY;
else
  state <= state_next;

// register buffer for logb replay_data
always @(posedge clk)
if (!rstn) begin
  r_logb_data <= 0;
  for (int i=0; i < LOGE_CHANNEL_CNT; i=i+1)
    r_loge_cnt[i] <= 0;
end
else if ((state == BUSY) && (state_next == FULL)) begin
  r_logb_data <= logb_data;
  for (int i=0; i < LOGE_CHANNEL_CNT; i=i+1)
    r_loge_cnt[i] <= loge_cnt_next[i];
end

// output register
always @(posedge clk)
if (!rstn) begin
  o_logb_data <= 0;
end
else if (state_next == BUSY)  begin
  if (state == FULL) begin
    o_logb_data <= r_logb_data;
  end
  else if (insert_replay) begin // shifting from load or flow
    o_logb_data <= logb_data;
  end
end
// calculate o_loge_cnt_next in a special way to improve timing
// i.e. to calculate the ok_to_replay_next, thus out_valid
for (genvar i=0; i < LOGE_CHANNEL_CNT; i=i+1) begin: o_loge_cnt_gen
  always_comb
    if (state_next == BUSY) begin
      if (state == FULL)
        o_loge_cnt_next[i] = r_loge_cnt[i];
      else if (insert_replay)
        o_loge_cnt_next[i] = loge_cnt_next[i];
      else
        o_loge_cnt_next[i] = o_loge_cnt[i];
    end
    else
      o_loge_cnt_next[i] = o_loge_cnt[i];
  always_ff @(posedge clk)
    if (!rstn)
        o_loge_cnt[i] <= 0;
    else
        o_loge_cnt[i] <= o_loge_cnt_next[i];
end

////////////////////////////////////////////////////////////////////////////////
// Happen-before enforcement:
// Only allow replay if runtime packet counter >= replay packet counter
////////////////////////////////////////////////////////////////////////////////
// rt_sub_loge_cnt maintains the value of
// "runtime packet counter - replay packet counter"
// The design mainly aims to register the `out_valid`, thus improve timing.
//
// It is OK to replay if runtime packet counter >= replay packet counter:
// In an unpacked logging bus, when logb_valid and loge_valid happen at the same
// time, the loge_valid is not counted towards to the replay packet counter of
// the logb_valid at the same cycle.
// But during the conversion from unpacked logging bus to a packed writeback
// bus, the loge_valid is counted towards to the replay packet counter of the
// logb_valid at the same cycle. This is to only encode loge_valid when there
// are some logb_valid to record.

// Maintain runtime packet counter
for (genvar i=0; i < LOGE_CHANNEL_CNT; i=i+1) begin: rt_loge_cnt_gen
  assign rt_loge_cnt_next[i] = rt_loge_cnt[i] + rt_loge_valid[i];
  always_ff @(posedge clk)
    if (!rstn)
      rt_loge_cnt[i] <= 0;
    else
      rt_loge_cnt[i] <= rt_loge_cnt_next[i];
end

// Maintain replay packet counter
genvar i;
generate
  for (i=0; i < LOGE_CHANNEL_CNT; i=i+1)
    assign loge_cnt_next[i] = loge_cnt[i] + loge_valid[i];
endgenerate
always @(posedge clk)
  if (!rstn) begin
    for (int i=0; i < LOGE_CHANNEL_CNT; i=i+1)
      loge_cnt[i] <= 0;
  end
  else begin
    // aggregate the vector clock right after taking in any replay packet
    if (in_valid && in_ready)
      for (int i=0; i < LOGE_CHANNEL_CNT; i=i+1)
        loge_cnt[i] <= loge_cnt_next[i];
  end
wire [PKT_CNT_WIDTH-1:0] o_loge_cnt_neg [LOGE_CHANNEL_CNT-1:0];
wire [PKT_CNT_WIDTH-1:0] rt_sub_loge_cnt [LOGE_CHANNEL_CNT-1:0];
logic [LOGE_CHANNEL_CNT-1:0] rt_sub_loge_cnt_sign;
`ifdef FORMAL
wire [LOGE_CHANNEL_CNT-1:0] test_sub_equal;
`endif

// calculate ok_to_replay_next for the out_valid, xxx_next is to improve timing
logic ok_to_replay_next;
generate
  for (genvar i=0; i < LOGE_CHANNEL_CNT; i=i+1) begin
    assign o_loge_cnt_neg[i] = ~o_loge_cnt_next[i] + PKT_CNT_WIDTH'(1);
    assign rt_sub_loge_cnt[i] = rt_loge_cnt_next[i] + o_loge_cnt_neg[i];
    `ifdef FORMAL
    assign test_sub_equal[i] = (rt_loge_cnt_next[i] - o_loge_cnt_next[i]) == rt_sub_loge_cnt[i];
    `endif
    // sign is 0 --> runtime cnt - replay cnt is positive or zero,
    // runtime cnt >= replay cnt, thus OK to replay
    // else, should wait for the happen-before to be enforced
    assign rt_sub_loge_cnt_sign[i] = rt_sub_loge_cnt[i][PKT_CNT_WIDTH-1];
  end
endgenerate
assign ok_to_replay_next = !(|rt_sub_loge_cnt_sign);

////////////////////////////////////////////////////////////////////////////////
// The replay logic
////////////////////////////////////////////////////////////////////////////////
// I want out_valid to be a simple register (not a wire) because it will be used
// in the application with high fan-outs.
// Its most complex dependency is the `ok_to_replay`, which is a wire-or over
// many addition exprs.
// To register out_valid, I need to pervasively tract the XXX_next version of
// its dependencies.
always_ff @(posedge clk)
  if (!rstn)
    out_valid <= 0;
  else if (out_valid && !out_ready)
    // do nothing, keep the out_valid high
    // This is to buffer historical vector clock decision.
    // once a transaction to replay can be replay, then use this register and
    // ignore vector clocks (because they may overflow due to loge_valid
    // aggregation)
    ;
  else
    out_valid <= (state_next != EMPTY) && ok_to_replay_next;
assign out_data = o_logb_data;
assign in_ready = (state != FULL) || !logb_valid;

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
    end

  // proof
  // NOTE: some following properties cannot be proved in reasonable time
  // But I think that is fine as they were "proof" statements
  always @(posedge clk)
  if (rstn) begin
    if (state == EMPTY) begin
      `ASSERT(in_logb_cnt == out_cnt);
    end
    else if (state == BUSY) begin
      `ASSERT(out_cnt + 1 == in_logb_cnt);
      `ASSERT(o_logb_data == out_cnt);
    end
    else if (state == FULL) begin
      `ASSERT(out_cnt + 2 == in_logb_cnt);
      `ASSERT(o_logb_data == out_cnt);
      `ASSERT(r_logb_data + 1 == in_logb_cnt);
    end
    `ASSERT(state != 'b11);
  end

  check_trace: cover property (@(posedge clk)
    disable iff (!rstn)
    (insert_replay && remove_replay) [*3]
  );

  sub_equ_check: `ASSERT property (@(posedge clk)
    disable iff (!rstn)
    &test_sub_equal
  );
`endif

// The following debug code is out-dated
`ifdef DEBUG_ILA
if (DEBUG) begin
  if (LOGE_CHANNEL_CNT != 25)
    $error("Invalid Debug Parameter: LOGE_CHANNEL_CNT %d", LOGE_CHANNEL_CNT);
  logic state_empty, state_busy, state_full;
  assign state_empty = (state == EMPTY);
  assign state_busy = (state == BUSY);
  assign state_full = (state == FULL);
  // probe 0: state_empty
  // probe 1: state_busy
  // probe 2: state_full
  // probe 3: o_logb_valid
  // probe 4: o_loge_valid[24:0]
  // probe 5: rt_loge_valid[24:0]
  // probe 6: rt_sub_loge_cnt[0][6:0] (to test longer PKT_CNT_WIDTH, this will be 8bit)
  // ...
  // probe 30: rt_sub_loge_cnt[24]
  dbg_valid_replayer_ila ila (
    .clk(clk),
    .probe0(state_empty),
    .probe1(state_busy),
    .probe2(state_full),
    .probe3(o_logb_valid),
    .probe4(o_loge_valid),
    .probe5(rt_loge_valid),
    .probe6({1'b0,rt_sub_loge_cnt[0]}),
    .probe7({1'b0,rt_sub_loge_cnt[1]}),
    .probe8({1'b0,rt_sub_loge_cnt[2]}),
    .probe9({1'b0,rt_sub_loge_cnt[3]}),
    .probe10({1'b0,rt_sub_loge_cnt[4]}),
    .probe11({1'b0,rt_sub_loge_cnt[5]}),
    .probe12({1'b0,rt_sub_loge_cnt[6]}),
    .probe13({1'b0,rt_sub_loge_cnt[7]}),
    .probe14({1'b0,rt_sub_loge_cnt[8]}),
    .probe15({1'b0,rt_sub_loge_cnt[9]}),
    .probe16({1'b0,rt_sub_loge_cnt[10]}),
    .probe17({1'b0,rt_sub_loge_cnt[11]}),
    .probe18({1'b0,rt_sub_loge_cnt[12]}),
    .probe19({1'b0,rt_sub_loge_cnt[13]}),
    .probe20({1'b0,rt_sub_loge_cnt[14]}),
    .probe21({1'b0,rt_sub_loge_cnt[15]}),
    .probe22({1'b0,rt_sub_loge_cnt[16]}),
    .probe23({1'b0,rt_sub_loge_cnt[17]}),
    .probe24({1'b0,rt_sub_loge_cnt[18]}),
    .probe25({1'b0,rt_sub_loge_cnt[19]}),
    .probe26({1'b0,rt_sub_loge_cnt[20]}),
    .probe27({1'b0,rt_sub_loge_cnt[21]}),
    .probe28({1'b0,rt_sub_loge_cnt[22]}),
    .probe29({1'b0,rt_sub_loge_cnt[23]}),
    .probe30({1'b0,rt_sub_loge_cnt[24]})
  );
end
`endif
endmodule

module twowayhandshake_ready_replayer #(
  // the total number of loge_valid from all channels
  parameter LOGE_CHANNEL_CNT = 5,
  parameter NUM_RDYRPLY = 1,
  parameter int LOGE_IDX [NUM_RDYRPLY-1:0] = {0},
  parameter DEBUG = 0
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
`ifdef DEBUG_ILA
if (DEBUG) begin
  if (LOGE_CHANNEL_CNT != 25)
    $error("Invalid Debug Parameter: LOGE_CHANNEL_CNT %d", LOGE_CHANNEL_CNT);
  // probe 0: in_valid
  // probe 1: in_ready
  // probe 2: in_loge_valid[24:0]
  // probe 3: rt_loge_valid[24:0]
  // probe 4: rt_sub_loge_cnt_sign[24:0]
  // probe 5: ok_to_replay_ready[24:0]
  // probe 6: rt_sub_loge_cnt[0][6:0] (to test longer PKT_CNT_WIDTH, this will be 8bit)
  // ...
  // probe 30: rt_sub_loge_cnt[24]
  dbg_ready_replayer_ila ila (
    .clk(clk),
    .probe0(in_valid),
    .probe1(in_ready),
    .probe2(in_loge_valid),
    .probe3(rt_loge_valid),
    .probe4(rt_sub_loge_cnt_sign),
    .probe5(ok_to_replay_ready),
    .probe6({1'b0,rt_sub_loge_cnt[0]}),
    .probe7({1'b0,rt_sub_loge_cnt[1]}),
    .probe8({1'b0,rt_sub_loge_cnt[2]}),
    .probe9({1'b0,rt_sub_loge_cnt[3]}),
    .probe10({1'b0,rt_sub_loge_cnt[4]}),
    .probe11({1'b0,rt_sub_loge_cnt[5]}),
    .probe12({1'b0,rt_sub_loge_cnt[6]}),
    .probe13({1'b0,rt_sub_loge_cnt[7]}),
    .probe14({1'b0,rt_sub_loge_cnt[8]}),
    .probe15({1'b0,rt_sub_loge_cnt[9]}),
    .probe16({1'b0,rt_sub_loge_cnt[10]}),
    .probe17({1'b0,rt_sub_loge_cnt[11]}),
    .probe18({1'b0,rt_sub_loge_cnt[12]}),
    .probe19({1'b0,rt_sub_loge_cnt[13]}),
    .probe20({1'b0,rt_sub_loge_cnt[14]}),
    .probe21({1'b0,rt_sub_loge_cnt[15]}),
    .probe22({1'b0,rt_sub_loge_cnt[16]}),
    .probe23({1'b0,rt_sub_loge_cnt[17]}),
    .probe24({1'b0,rt_sub_loge_cnt[18]}),
    .probe25({1'b0,rt_sub_loge_cnt[19]}),
    .probe26({1'b0,rt_sub_loge_cnt[20]}),
    .probe27({1'b0,rt_sub_loge_cnt[21]}),
    .probe28({1'b0,rt_sub_loge_cnt[22]}),
    .probe29({1'b0,rt_sub_loge_cnt[23]}),
    .probe30({1'b0,rt_sub_loge_cnt[24]})
  );
end
`endif
endmodule
