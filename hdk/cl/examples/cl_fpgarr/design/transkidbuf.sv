////////////////////////////////////////////////////////////////////////////////
// Transparent skid buffer
////////////////////////////////////////////////////////////////////////////////
// Parameters
// PASS_STALL:
//   Does the stall signal (!out_ready) propogate from output to input
//   regardless of the buffer state (EMPTY?)
`include "formal/properties.sv"
module transkidbuf #(
  parameter DATA_WIDTH=32,
  parameter PASS_STALL=0
) (
  input wire clk,
  input wire rstn,
  // input channel
  input wire in_valid,
  input wire [DATA_WIDTH-1:0] in_data,
  output reg in_ready,
  // output channel
  output reg out_valid,
  output reg [DATA_WIDTH-1:0] out_data,
  input wire out_ready
);

wire insert, remove;
assign insert = in_valid && in_ready;
assign remove = out_valid && out_ready;

// From http://fpgacpu.ca/fpga/Pipeline_Skid_Buffer.html
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
// 
// reg load    = 1'b0; // Empty datapath inserts data into output register.
// reg flow    = 1'b0; // New inserted data into output register as the old data is removed.
// reg fill    = 1'b0; // New inserted data into buffer register. Data not removed from output register.
// reg flush   = 1'b0; // Move data from buffer register into output register. Remove old data. No new data inserted.
// reg unload  = 1'b0; // Remove data from output register, leaving the datapath empty.
localparam NSTATES=3; //EMPTY, BUSY, FULL
localparam NSTATEBITS=$clog2(NSTATES);
localparam [NSTATEBITS-1:0] EMPTY = 'd0;
localparam [NSTATEBITS-1:0] BUSY = 'd1;
localparam [NSTATEBITS-1:0] FULL = 'd2;
reg [NSTATEBITS-1:0] state;
reg [NSTATEBITS-1:0] state_next;

always @(posedge clk)
if (!rstn)
  state <= EMPTY;
else
  state <= state_next;

always @(*) begin
  case (state)
    EMPTY:
      if (insert && !remove)
        state_next = BUSY;
      else
        state_next = EMPTY;
    BUSY:
      if (insert && !remove)
        state_next = FULL;
      else if (!insert && remove)
        state_next = EMPTY;
      else // (insert && remove) || (!insert && !remove)
        state_next = BUSY;
    FULL:
      if (!insert && remove)
        state_next = BUSY;
      else
        state_next = FULL;
    default:
      state_next = state;
  endcase
end

// register buffer
reg [DATA_WIDTH-1:0] r_data;
always @(posedge clk)
if (!rstn) begin
  r_data <= 0;
end
else if ((state == BUSY) && (state_next == FULL))
  r_data <= in_data;

// output chanenl register
always @(posedge clk)
if (!rstn)
  out_data <= 0;
else if (state_next == BUSY) begin
  if (state == FULL)
    out_data <= r_data;
  else if (insert)
    out_data <= in_data;
end

always @(posedge clk)
if (!rstn)
  out_valid <= 0;
else
  out_valid <= (state_next != EMPTY);

always @(posedge clk)
if (!rstn)
  in_ready <= 0;
else
  in_ready <= (state_next != FULL) && (!PASS_STALL || out_ready);

`ifdef FORMAL
  `ifdef TRANSKIDBUF_SELF
    `define ASSUME assume
    `define ASSERT assert
  `else
    // for module composition
    `define ASSUME assert
    `define ASSERT assume
  `endif
  ////////////////////////////////////////////////////////////////////////////
  // Init (assumption)
  ////////////////////////////////////////////////////////////////////////////
  // {{{
  // reset properties
  `ifdef TRANSKIDBUF_SELF
  `ifndef JASPERGOLD
  reg f_past_valid = 0;
  always @(posedge clk) begin
    if (!f_past_valid)
      assume(!rstn);
    f_past_valid <= 1;
  end
  `endif
  `endif
  // }}} reset

  // Input AXI (assumption)
  `ASSUME property(RESET_CLEARS_VALID(clk, rstn, in_valid));
  `ASSUME property(HELD_VALID_DATA(clk, rstn, in_valid, in_ready, in_data));

  // Output AXI (correctness)
  `ASSERT property(RESET_CLEARS_VALID(clk, rstn, out_valid));
  `ASSERT property(HELD_VALID_DATA(clk, rstn, out_valid, out_ready, out_data));

  `ifndef TRY_SVA_LIVE
  // sequence inorder behavior input model (assumption)
  localparam F_CNTWIDTH=DATA_WIDTH;
  reg [F_CNTWIDTH-1:0] in_cnt;
  reg [F_CNTWIDTH-1:0] out_cnt;
  function automatic [F_CNTWIDTH-1:0] get_in_cnt();
    get_in_cnt = in_cnt;
  endfunction
  function automatic [F_CNTWIDTH-1:0] get_out_cnt();
    get_out_cnt = out_cnt;
  endfunction
  always @(posedge clk)
  if (!rstn) begin
    in_cnt <= 0;
    out_cnt <= 0;
  end
  else begin
    if (in_valid && in_ready) begin
      in_cnt <= in_cnt + 1;
      `ASSUME(in_data == in_cnt);
    end
    if (out_valid && out_ready) begin
      out_cnt <= out_cnt + 1;
    end
  end

  // sequence inorder behavior property to verify (correctness)
  always @(posedge clk)
  if (rstn)
    if (out_valid && out_ready)
      `ASSERT(out_data == out_cnt);

  `ifdef TRANSKIDBUF_SELF
  // sequence inorder behavior proof
  always @(posedge clk)
  if (rstn) begin
    if (state == EMPTY) begin
      `ASSERT(out_cnt == in_cnt);
    end
    else if (state == BUSY) begin
      `ASSERT(out_cnt + 1 == in_cnt);
      `ASSERT(out_data + 1 == in_cnt);
    end
    else if (state == FULL) begin
      `ASSERT(out_cnt + 2 == in_cnt);
      `ASSERT(out_data + 2 == in_cnt);
      `ASSERT(r_data + 1 == in_cnt);
    end
    `ASSERT(state != 'b11);
  end
  `endif // end of inorder proof

  `ifdef TRANSKIDBUF_SELF
  // sanity check, example trace
  check_trace: cover property (@(posedge clk)
    disable iff (!rstn)
    (!out_valid && !in_valid)
    ##1 in_valid && out_ready [*3]
    ##1 in_valid && !out_ready [*3]
    ##[1:$] (out_cnt == 'd10)
  );
  `endif // sanity check
  `else
    // I wanted to try some SVA properties without assuming the in_data
    // But it is not working, even in jaspergold
    // SVA sequence property
    int in_cnt = 0;
    int out_cnt = 0;
    always @(posedge clk)
    if (!rstn) begin
      in_cnt = 0;
      out_cnt = 0;
    end
    else begin
      if (in_valid && in_ready)
        in_cnt <= in_cnt + 1;
      if (out_valid && out_ready)
        out_cnt <= out_cnt + 1;
    end
    property liveness;
      @(posedge clk)
      disable iff (!rstn)
      !out_ready |=> ##[0:$] out_ready;
    endproperty
    as_live: `ASSUME property(liveness);
    property p_inorder;
      int data, tag;
      @(posedge clk) 
      disable iff (!rstn)
      ((in_valid && in_ready), tag=in_cnt, data=in_data) |-> ##[1:$] (out_valid && out_ready && (tag == out_cnt) && (data == out_data));
    endproperty
    ap_inorder: assert property (p_inorder);
    sanity_check: cover property (@(posedge clk)
      disable iff (!rstn)
      ((in_cnt == 'd5) && in_valid && in_ready && in_cnt != in_data)
      ##[1:$]
      ((out_cnt == 'd10) && out_valid && out_ready && out_cnt == out_data)
    );
  `endif
`endif // FORMAL
endmodule