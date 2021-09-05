////////////////////////////////////////////////////////////////////////////////
// Design Doc of the channel splitting module
////////////////////////////////////////////////////////////////////////////////
//
//              |------------| ==> |-------|
//              |            |     | logb  | for the start of each transaction
//              |            | <== |-------|
// (from shell) |            |
// M_valid ==>  |            | ==> |-------| (to cl)
// M_data  ==>  |   split    |     |  out  | for passing through to cl
// M_ready <==  |            | <== |-------|
//              |            |
//              |            | ==> |-------|
//              |            |     | loge  | for the end of each transaction
//              |            | <== |-------|
//              |------------|
//
// Use: should be put right after the shell interface
//      each splitted axi interface should be registered/pipelined multiple
//      steps until meets timing. (note that centralizing multiple shell
//      interfaces from different super logic region (SLR) is expensive. But
//      I need to make sure the pipeline stages of the splitted-out recording
//      channel of all shell interfaces are equal, so that packets came at the
//      same cycle still get out of the pipeline at the same cycle.
// Requirements:
// 1. I need to log the start and end of each transaction. To accommodate
//    backpressures from both logging and cl, the dependency/propogation chain
//    is:
//    in_valid -> logb_valid -> out_valid -> out_ready -> loge_valid ->
//    loge_ready -> in_ready
//    As a result, this module should only passthrough valid and ready after
//    the logging is complete.
//
//    However, this will introduce new problems because the difference of
//    "shell thinks a transaction is complete" versus "cl thinks a transaction
//    is complete" matters.
//    e.g. BVALID depends on AWREADY and WREADY. If cl thinks AWREADY and
//    WREADY are both asserted (out_valid && !loge_ready), cl will assert
//    BVALID.
//    It is possible that shell does not agree (!loge_ready => !in_ready),
//    then shell will find the asserted BVALID violates the spec.
//
//    TODO: how to fix this? do I need to formal verify the workaround?
//    Idea: I need to follow the design philosophy that when valid is
//    asserted, all resources has to be reserved to make sure there is no
//    stall upon stall. So I need to guarantee that whenever the start of
//    a transaction has been logged, the end of that transaction can also be
//    logged without stall. In this way, I want to guarantee:
//    (in_valid && in_ready) <==> (out_valid && out_ready)
//    A easy way to achieve this is to guarantee !(loge_valid && !loge_ready),
//    i.e. stall at loge never happens
//    To implement this, we need to tweak the shell-side loge skid buffer.
//    Recall that to synchronize pipeline stages of all interfaces according to
//    the global clock, the skidbuffer of each stage will propogate the stall
//    signal regardless of status of the buffer register. Normally for
//    a skidbuffer in_ready<=!r_valid, i.e. the skidbuffer is ready to receive
//    data whenever its internal buffer is not used, regardless of out_ready.
//    But in our case, to propogate the stall signal synchronous to the global
//    clock, in_ready <= !r_valid && out_ready, i.e. even though the internal
//    buffer is not used, a transkid_buffer will refuse to receive data
//    whenever its downstream cannot receive data.
//    I can tweak the last stage (shell-side) of the loge skid buffer to be a
//    "normal" skid buffer instead of "transparent". Note here exists an
//    invariant that after logging the start of a transaction and before
//    wanting to log the end of a transaction, the skid buffer will be idle.
//    So a success logging of the start of a transaction guarantees an
//    available "normal" skid buffer when I want to log the end of this
//    transaction later.
//
//    Such workaround could work with the above AWREADY, WREADY, BVALID
//    example. More generally, in the case of logging buffer stall, this
//    workaround will make the time to complete a transaction shorter than
//    reality. In the worst case, a transaction which is perceived to be
//    multi-cycle by cl, could be perceived to start and end at the same cycle
//    in the log (this is also acceptable behaviour according to the AXI spec).
//
// 2. When a transaction finished on the output side while there is no new
//    transaction from the input side, the ready signal of output side should
//    be deasserted.
// 3. It is allowed that any ready signal on the output side can drop anytime
//    they want. ready signals is also allowed to be dependent on valid.
//
// Implementation:
// each splitted-out interface x has a state register (is_stall_x@clk)
// is_stall_x == 0:
//   wire M_valid, M_data to valid_x and data_x
// is_stall == 1:
//   wire 0 to valid_x
//   wire M_data to data_x
// M_ready:
//   = &(is_stall_x?1:ready_x)
// is_stall_x:
//   0 --> 1: valid_x && ready_x && !(M_valid && M_ready)
//   1 --> 0: M_valid && M_ready
//
// New thoughts if I want to record distributed synchronized clock counter and
//   packet counter.
// 1. For requirement 1, I can make analogy to the distributed atomic
//    reduction argument learned in summer school
// 2. It also requires formal confirmation for the dispatch module (i.e. stall
//    any input channel whenever any of the output channel is stalled)
//
// The following logger for twowayhandshake implements the above splitting
// feature
module twowayhandshake_logger #(
  parameter DATA_WIDTH=32
) (
  input wire clk,
  input wire rstn,
  // input channel
  input wire in_valid,
  output wire in_ready,
  input wire [DATA_WIDTH-1:0] in_data,
  // the following two logging channel are synchronized, aligned by clock
  // counters(TODO: make sure this assumption hold)
  // logging channel (transaction start)
  output wire logb_valid,
  input wire logb_ready,
  output wire [DATA_WIDTH-1:0] logb_data,
  // logging channel (transaction end)
  // loge_valid && loge_ready propogates the information that one transaction
  // has finished
  output wire loge_valid,
  input wire loge_ready,
  // out channel
  output wire out_valid,
  input wire out_ready,
  output wire [DATA_WIDTH-1:0] out_data
);

  //////////////////////////////////////////////////////////////////////////////
  // Declaration
  //////////////////////////////////////////////////////////////////////////////
  // {{
  // whether the logging channel or output channel is stalled
  reg stall_logb, stall_loge, stall_out;
  // internal log ready and output ready (considering the stall)
  // stall_x => x is always ready, !stall_x => refer to x_ready
  // i_x_ready = stall_x || x_ready;
  wire i_logb_ready, i_loge_ready, i_out_ready;
  // }}
  always @(posedge clk)
  if (!rstn) begin
    stall_logb <= 0;
    stall_loge <= 0;
    stall_out <= 0;
  end
  else begin
    if (stall_logb)
      // stalled, clear when input transaction finished
      stall_logb <= !(in_valid && in_ready);
    else
      // not stalled yet, stall when log transaction finished but input hasn't
      stall_logb <= (logb_valid && logb_ready) && !(in_valid && in_ready);
    if (stall_loge)
      stall_loge <= !(in_valid && in_ready);
    else
      stall_loge <= (loge_valid && loge_ready) && !(in_valid && in_ready);
    if (stall_out)
      stall_out <= !(in_valid && in_ready);
    else
      stall_out <= (out_valid && out_ready) && !(in_valid && in_ready);
  end

  // input channel
  assign in_ready = i_logb_ready && i_loge_ready && i_out_ready;
  // logging channel (transaction start)
  // stall_x => x is always not valid, !stall_x => refer to in_valid
  assign logb_valid = !stall_logb && in_valid;
  assign i_logb_ready = stall_logb || logb_ready;
  assign logb_data = in_data;
  // logging channel (transaction end)
  assign loge_valid = !stall_loge && (stall_out? 1 : out_valid && out_ready);
  assign i_loge_ready = stall_loge || loge_ready;
  // output channel
  assign out_valid = stall_out ? 0 : (
    stall_logb ? in_valid : (in_valid && logb_valid && logb_ready)
    );
  assign i_out_ready = stall_out || out_ready;
  assign out_data = in_data;

`ifdef FORMAL
  ////////////////////////////////////////////////////////////////////////////
  // Init (assumption)
  ////////////////////////////////////////////////////////////////////////////
  // {{{
  // reset properties
  reg f_past_valid = 0;
  always @(posedge clk) begin
    if (!f_past_valid)
      assume(!rstn);
    f_past_valid <= 1;
  end
  // }}} reset

  ////////////////////////////////////////////////////////////////////////////
  // Input AXI Stream (assumption)
  ////////////////////////////////////////////////////////////////////////////
  // {{{
  always @(posedge clk)
  if (!f_past_valid || !rstn)
  begin
      assume(!in_valid);
  end
  else if ($past(in_valid && !in_ready && rstn))
      assume(in_valid && $stable(in_data));
  // }}} Input AXI Stream

  ////////////////////////////////////////////////////////////////////////////
  // Output AXI Stream (correctness)
  ////////////////////////////////////////////////////////////////////////////
  // {{{
  always @(posedge clk)
  if (!rstn)
      assert(!out_valid);
  else begin // f_past_valid
      if ($past(out_valid && !out_ready && rstn))
          // Following any stall, valid must remain and data must be stable
          assert(out_valid && $stable(out_data));
      // output might wait for log, no need to enforce the following property
      // (performance property?)
      //if ($past(out_ready && rstn) && !stall_output) begin
      //    assert(out_valid == in_valid);
      //    // in_valid |-> out_data == in_data
      //    assert(!in_valid || (out_data == in_data));
      //end
  end
  // }}} Output AXI Stream

  ////////////////////////////////////////////////////////////////////////////
  // Log AXI Stream (correctness)
  ////////////////////////////////////////////////////////////////////////////
  // {{{
  always @(posedge clk)
  if (!rstn)
    assert(!logb_valid);
  else begin // f_past_valid
    // logb
    // logb_valid should hold if previous cycle transaction is unfinished
    if ($past(logb_valid && !logb_ready && rstn))
      assert(logb_valid && $stable(logb_data));
    // Log should always sync with input (performance?)
    if ($past(logb_ready && rstn) && !stall_logb) begin
      assert(logb_valid == in_valid);
      assert(!in_valid || (logb_data == in_data));
    end
    // loge
    // loge_valid should hold if previous cycle transaction is unfinished
    if ($past(loge_valid && !loge_ready && rstn))
      assert(loge_valid);
    assert(!stall_loge); // loge is the last step, should never stall
  end
  // }}} Log AXI Stream
  
  ////////////////////////////////////////////////////////////////////////////
  // Packet Counting Properties
  ////////////////////////////////////////////////////////////////////////////
  // {{{
  localparam F_CNTWIDTH=32;
  reg [F_CNTWIDTH-1:0] in_cnt;
  reg [F_CNTWIDTH-1:0] out_cnt;
  reg [F_CNTWIDTH-1:0] logb_cnt;
  reg [F_CNTWIDTH-1:0] loge_cnt;
  always @(posedge clk)
  if (!rstn) begin
      in_cnt <= 0;
      out_cnt <= 0;
      logb_cnt <= 0;
      loge_cnt <= 0;
  end
  else begin
      if (in_valid && in_ready)
        in_cnt <= in_cnt + 1;
      if (out_valid && out_ready)
        out_cnt <= out_cnt + 1;
      if (logb_valid && logb_ready)
        logb_cnt <= logb_cnt + 1;
      if (loge_valid && loge_ready)
        loge_cnt <= loge_cnt + 1;
  end

  // packet counter consistency
  always @(posedge clk)
  if (rstn) begin
      // logb can finish at most one transaction more than the output channel
      // if out_cnt + 1 == logb_cnt, everything is waiting for the output
      // channel to complete
      if (out_cnt + 1 == logb_cnt) begin
        assert(out_valid);
        assert(stall_logb);
      end
      else
        assert(out_cnt == logb_cnt);

      // Same as above, loge can wait for out but not vice versa.
      if (loge_cnt + 1 == out_cnt) begin
        assert(loge_valid);
        assert(stall_out);
      end
      else
        assert(loge_cnt == out_cnt);
      ////////////////////////////////////////
      // properties about counter and stall //
      ////////////////////////////////////////
      // when logb is stalled, logb can only be 1 step ahead of input
      if (stall_logb)
        assert(logb_cnt == in_cnt + 1);
      // when output is stalled, logb has to be stalled too. output and logb
      // should be at the same step
      if (stall_out) begin
        assert(out_cnt == logb_cnt);
        assert(stall_logb);
      end
      // the input channel should be synced with at least one of the out
      // channels.
      assert((in_cnt == logb_cnt) || (in_cnt == out_cnt) || (in_cnt == loge_cnt));
  end
  // }}}

  ////////////////////////////////////////////////////////////////////////////
  // Performance related properties
  ////////////////////////////////////////////////////////////////////////////
  // {{{
  always @(posedge clk)
  if (rstn) begin
    // in_valid => (logb_valid || out_valid || loge_valid)
    // there should not be any cycle wasted (no output channel asserts valid)
    // when the input channel asserts valid
    assert(!in_valid || (logb_valid || out_valid || loge_valid));
  end
  // }}}

  ////////////////////////////////////////////////////////////////////////////
  // Proof (intermediate, invariant properties)
  ////////////////////////////////////////////////////////////////////////////
  // {{{
  always @(posedge clk)
  if (rstn) begin
    assert(!stall_out || stall_logb); // stall_out => stall_logb
    assert(!stall_out || in_valid); // stall_out => in_valid
    assert(!stall_logb || in_valid); // stall_logb => in_valid
  end
  // }}}
`endif // FORMAL
endmodule
