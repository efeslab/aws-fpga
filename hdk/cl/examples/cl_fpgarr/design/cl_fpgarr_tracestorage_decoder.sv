`include "cl_fpgarr_defs.svh"

// This tracestorage_decoder is to parse the logging data retrieved from the
// DRAM during replay
// rr_trace_split is the original mjc's implementation which has timing issues
// rr_parse_replay_trace is gefei's reimplementation which improves timing a bit
module rr_trace_split #(
    parameter WIDTH = 2500,
    parameter AXI_WIDTH = 512,
    parameter OFFSET_WIDTH = 32,
    parameter AXI_ADDR_WIDTH = 64,
    parameter int LOGB_CHANNEL_CNT = 25,
    parameter int LOGE_CHANNEL_CNT = 25,
    parameter bit [LOGB_CHANNEL_CNT-1:0]
      [RR_CHANNEL_WIDTH_BITS-1:0] SHUFFLED_CHANNEL_WIDTHS) (
    input clk,
    input sync_rst_n,

    input logic [AXI_WIDTH-1:0] replay_in_fifo_out,
    output logic replay_in_fifo_rd_en,
    input logic replay_in_fifo_full,
    input logic replay_in_fifo_almfull,
    input logic replay_in_fifo_empty,

    output logic [WIDTH-1:0] replay_out_fifo_in,
    output logic [OFFSET_WIDTH-1:0] replay_out_fifo_in_width,
    output logic replay_out_fifo_wr_en,
    input logic replay_out_fifo_full,
    input logic replay_out_fifo_almfull,
    input logic replay_out_fifo_empty
);

    localparam NSTAGES = (WIDTH - 1) / AXI_WIDTH + 1;
    localparam EXT_WIDTH = NSTAGES * AXI_WIDTH;

    `DEF_SUM_WIDTH(GET_FULL_WIDTH, SHUFFLED_CHANNEL_WIDTHS, 0, LOGB_CHANNEL_CNT)
    localparam FULL_WIDTH = GET_FULL_WIDTH() + LOGB_CHANNEL_CNT + LOGE_CHANNEL_CNT;
    `DEF_GET_LEN(GET_LEN, LOGB_CHANNEL_CNT, $clog2(FULL_WIDTH+1),
       SHUFFLED_CHANNEL_WIDTHS)

    logic [AXI_WIDTH-1:0] replay_current_in;
    logic replay_current_in_valid;

    logic [AXI_WIDTH*2-1:0] replay_leftover;
    logic [AXI_WIDTH*3/PACKET_ALIGNMENT-1:0][PACKET_ALIGNMENT-1:0] replay_leftover_next_assigned;
    logic [AXI_WIDTH*3/PACKET_ALIGNMENT-1:0][PACKET_ALIGNMENT-1:0] replay_leftover_next_unassigned;
    logic [OFFSET_WIDTH-1:0] replay_leftover_size;
    logic [OFFSET_WIDTH-1:0] replay_total_size, replay_total_size_tmp, replay_total_size_reg;
    logic [OFFSET_WIDTH-1:0] replay_left_size, replay_left_size_tmp, replay_left_size_reg;
    logic [OFFSET_WIDTH-1:0] replay_shift_size;
    logic replay_is_first_packet, replay_leftover_do_step;

    assign replay_current_in = replay_in_fifo_out;
    assign replay_current_in_valid = replay_in_fifo_rd_en;
    assign replay_in_fifo_rd_en = ~replay_in_fifo_empty && ~replay_out_fifo_almfull
                                  && replay_leftover_size - replay_shift_size <= AXI_WIDTH;

    // *replay_leftover* should pass output whenever the next output size is less than
    // the size of the current leftover buffer, i.e., there are enough stuff to output.
    always_comb begin
        if (replay_leftover_size >= AXI_WIDTH) begin
            // If leftover size is larger than or equal to AXI_WIDTH, we can output anyway.
            replay_leftover_do_step = 1;
        end else if (replay_left_size <= replay_leftover_size && replay_left_size > 0) begin
            // If leftover size is larger than the size of the remaining bits of the current
            // transaction, we can always output.
            replay_leftover_do_step = 1;
        end else begin
            // Otherwise, we cannot output anyway. If the size of the remaining bits in the
            // current transaction is larger than what's remaining in the leftover buffer,
            // we must wait for more data to be inserted to the leftover buffer, because all
            // outputs other than the last one in a transaction should have AXI_WIDTH bits.
            replay_leftover_do_step = 0;
        end
    end

    // *replay_total_size* is the number of bits in the whole transaction. It's calculated when
    // the first few bits of a transaction is decoded, and used until the next transaction.
    assign replay_total_size_tmp = replay_leftover[0 +: OFFSET_WIDTH];
    assign replay_total_size = replay_is_first_packet ? replay_total_size_tmp : replay_total_size_reg;
    always_ff @(posedge clk) begin
        if (~sync_rst_n) begin
            replay_total_size_reg <= 0;
        end else begin
            if (replay_is_first_packet) begin
                replay_total_size_reg <= replay_total_size_tmp;
            end
        end
    end

    // *replay_left_size* is the number of bits left in a transaction. When handling the first
    // packet of a transaction, it equals replay_total_size. Then it is decreased by AXI_WIDTH
    // until there's nothing left in the packet.
    assign replay_left_size_tmp = replay_total_size_tmp;
    assign replay_left_size = replay_is_first_packet ? replay_total_size_tmp : replay_left_size_reg;
    always_ff @(posedge clk) begin
        if (~sync_rst_n) begin
            replay_left_size_reg <= 0;
        end else begin
            if (replay_leftover_do_step) begin
                if (replay_left_size <= AXI_WIDTH) begin
                    // In this case, replay_left_size_reg is not used, we assign it to 0 to ease
                    // debugging. We can remove the following line if there's a timing issue.
                    replay_left_size_reg <= 0;
                end else begin
                    replay_left_size_reg <= replay_left_size - AXI_WIDTH;
                end
            end else begin
                replay_left_size_reg <= replay_left_size;
            end
        end
    end

    // *replay_shift_size* is the size of the next valid output from *replay_leftover*. The
    // *replay_leftover* register will be shifted by *replay_shift_size* after/while outputing.
    // *replay_leftover_do_step* ensures that there are enough bits to output in *replay_leftover*.
    always_comb begin
        if (replay_leftover_do_step) begin
            if (replay_left_size > AXI_WIDTH) begin
                replay_shift_size = AXI_WIDTH;
            end else begin
                replay_shift_size = replay_left_size;
            end
        end else begin
            // If there are not enough bits for output, we must set it to 0, because this variable
            // will be used when calculating the value of *replay_is_first_packet*, which is used to
            // determine whether a new transaction begins (and whether the previous one ends).
            replay_shift_size = 0;
        end
    end

    // *replay_is_first_packet* is determined under the following to facts:
    // 1. The previous packet is finishing in the current cycle, which means there are
    //    less than or equal to AXI_WIDTH bits left.
    // 2. There will be enough bits for width calculation, which means there are more than
    //    LOGB_CHANNEL_CNT + LOGE_CHANNEL_CNT bits in replay_leftover buffer in the next
    //    cycle.
    always_ff @(posedge clk) begin
        if (~sync_rst_n) begin
            replay_is_first_packet <= 0;
        end else begin
            // A packet is the first one, if the previous one finishes and there's enough data to
            // decode the packet size.
            if (replay_left_size <= AXI_WIDTH && replay_leftover_size >= replay_left_size) begin
                if (replay_current_in_valid) begin
                    if (replay_leftover_size + AXI_WIDTH - replay_shift_size >= OFFSET_WIDTH) begin
                        replay_is_first_packet <= 1;
                    end else if (replay_leftover_do_step) begin
                        replay_is_first_packet <= 0;
                    end
                end else begin
                    if (replay_leftover_size - replay_shift_size >= OFFSET_WIDTH) begin
                        replay_is_first_packet <= 1;
                    end else if (replay_leftover_do_step) begin
                        replay_is_first_packet <= 0;
                    end
                end
            end else if (replay_leftover_do_step) begin
                replay_is_first_packet <= 0;
            end
        end
    end

    always_comb begin
        replay_leftover_next_assigned = replay_leftover;
        for (int i = 0; i < AXI_WIDTH/PACKET_ALIGNMENT; i++) begin
            replay_leftover_next_assigned[`GET_FORCE_ALIGNED_FRAME(replay_leftover_size) + i]
                                            = replay_current_in[i*PACKET_ALIGNMENT +: PACKET_ALIGNMENT];
        end
        replay_leftover_next_unassigned = {AXI_WIDTH'(0), replay_leftover};
    end
    always_ff @(posedge clk) begin
        if (~sync_rst_n) begin
            replay_leftover_size <= 0;
        end else begin
            if (replay_leftover_do_step || replay_current_in_valid) begin
                if (replay_current_in_valid) begin
                    replay_leftover_size <= replay_leftover_size + AXI_WIDTH - replay_shift_size;
                    for (int i = 0; i < AXI_WIDTH*2/PACKET_ALIGNMENT; i++) begin
                        replay_leftover[i*PACKET_ALIGNMENT +: PACKET_ALIGNMENT] <=
                            replay_leftover_next_assigned[`GET_FORCE_ALIGNED_FRAME(replay_shift_size) + i];
                    end
                end else begin
                    replay_leftover_size <= replay_leftover_size - replay_shift_size;
                    for (int i = 0; i < AXI_WIDTH*2/PACKET_ALIGNMENT; i++) begin
                        replay_leftover[i*PACKET_ALIGNMENT +: PACKET_ALIGNMENT] <=
                            replay_leftover_next_unassigned[`GET_FORCE_ALIGNED_FRAME(replay_shift_size) + i];
                    end
                end
            end
        end
    end

    always_ff @(posedge clk) begin
        if (sync_rst_n) begin
            assert(`IS_ALIGNED_SIZE(replay_leftover_size));
            assert(`IS_ALIGNED_SIZE(replay_left_size));
            assert(`IS_ALIGNED_SIZE(replay_shift_size));
            assert(`IS_ALIGNED_SIZE(replay_total_size));
        end
    end

    logic [AXI_WIDTH-1:0] replay_split_out;
    logic [OFFSET_WIDTH-1:0] replay_split_out_total_size, replay_split_out_total_size_q, replay_split_out_total_size_qq;
    logic [OFFSET_WIDTH-1:0] replay_split_out_curr_size, replay_split_out_cumulated_size;
    logic [$clog2(NSTAGES):0] replay_curr;
    logic replay_out_curr_valid, replay_out_total_valid, replay_out_total_valid_q;

    always_ff @(posedge clk) begin
        if (~sync_rst_n) begin
            replay_split_out_total_size <= 0;
            replay_split_out_total_size_q <= 0;
            replay_split_out_total_size_qq <= 0;
            replay_split_out_curr_size <= 0;
            replay_split_out_cumulated_size <= 0;
            replay_curr <= 0;
            replay_out_curr_valid <= 0;
        end else begin
            if (replay_is_first_packet && replay_leftover_do_step) begin
                replay_split_out_total_size <= replay_total_size;
                replay_split_out_curr_size <= replay_shift_size;
                replay_split_out_cumulated_size <= replay_shift_size;
                replay_curr <= 0;
            end else if (replay_leftover_do_step) begin
                replay_split_out_cumulated_size <= replay_split_out_cumulated_size + replay_shift_size;
                replay_split_out_curr_size <= replay_shift_size;
                replay_curr <= replay_curr + 1;
            end

            if (replay_leftover_do_step) begin
                replay_split_out <= replay_leftover[0 +: AXI_WIDTH];
                replay_out_curr_valid <= 1;
            end else begin
                replay_out_curr_valid <= 0;
            end

            replay_split_out_total_size_q <= replay_split_out_total_size;
            replay_split_out_total_size_qq <= replay_split_out_total_size_q;
        end
    end

    always_ff @(posedge clk) begin
        if (~sync_rst_n) begin
            replay_out_total_valid <= 0;
            replay_out_total_valid_q <= 0;
        end else begin
            if (replay_split_out_total_size > 0 && replay_out_curr_valid &&
                replay_split_out_cumulated_size >= replay_split_out_total_size) begin
                replay_out_total_valid <= 1;
            end else begin
                replay_out_total_valid <= 0;
            end

            replay_out_total_valid_q <= replay_out_total_valid;
        end
    end
    assign replay_out_fifo_wr_en = replay_out_total_valid_q;

    logic [EXT_WIDTH-1:0] replay_out_fifo_in_wrap;
    logic [AXI_WIDTH-1:0] replay_handled [NSTAGES-1:0];

    // *replay_out_fifo_in* is 2 cycles behind *replay_split_out*;
    assign replay_out_fifo_in = WIDTH'(replay_out_fifo_in_wrap);
    assign replay_out_fifo_in_width = replay_split_out_total_size_qq;
    always_ff @(posedge clk) begin
        for (int i = 0; i < NSTAGES; i++) begin
            replay_out_fifo_in_wrap[i*AXI_WIDTH +: AXI_WIDTH] <= replay_handled[i];
        end
    end

    // *replay_handled* is 1 cycle behind replay_split_out;
    always_ff @(posedge clk) begin
        if (~sync_rst_n) begin
            for (int i = 0; i < NSTAGES; i++) begin
                replay_handled[i] <= 0;
            end
        end else begin
            if (replay_out_curr_valid) begin
                replay_handled[replay_curr] <= replay_split_out;
            end
        end
    end

endmodule

// rr_parse_replay_trace converts the format of trace, that comes in the unit of
// AXI_WIDTH, to another format of trace, that comes out in the unit of
// LOGGING_UNIT_WIDTH. LOGGING_UNIT_WIDTH consists of four parts (LSB to MSB):
// [0 +: OFFSET_WIDTH] the length of this logging unit
// [. +: LOGB_CHANNEL_CNT] the logb_valid
// [. +: LOGE_CHANNEL_CNT] the loge_valid
// [. +: LOGB_DATA_WIDTH] the logb_data
module rr_parse_replay_trace #(
    parameter LOGGING_UNIT_WIDTH,
    parameter OFFSET_WIDTH,
    parameter AXI_WIDTH = 512,
    parameter AXI_ADDR_WIDTH = 64,
    parameter int LOGB_CHANNEL_CNT,
    parameter int LOGE_CHANNEL_CNT,
    parameter bit [LOGB_CHANNEL_CNT-1:0]
      [RR_CHANNEL_WIDTH_BITS-1:0] SHUFFLED_CHANNEL_WIDTHS) (
    input clk,
    input sync_rst_n,

    input logic [AXI_WIDTH-1:0] replay_in_fifo_out,
    output logic replay_in_fifo_rd_en,
    input logic replay_in_fifo_full,
    input logic replay_in_fifo_almfull,
    input logic replay_in_fifo_empty,

    // LSB->MSB: data then offset width
    output logic [LOGGING_UNIT_WIDTH-1:0] replay_out_fifo_in,
    output logic replay_out_fifo_wr_en,
    input logic replay_out_fifo_full,
    input logic replay_out_fifo_almfull,
    input logic replay_out_fifo_empty
);

// highlevel structure
// Two component:
// 1. shifting buffer, [2*AXI_WIDTH-1:0], managed by two FSM
//    LO_FSM for the [0 +: AXI_WIDTH]
//    HI_FSM for the [AXI_WIDTH +: AXI_WIDTH]
// 2. assemble buffer, [LOGGING_UNIT_WIDTH-1:0], managed by ASM_FSM
// AXI_OFFSET_WIDTH is used to index inside the LO part of the shifting buffer
// AXI_ALIGNED_OFFSET_WIDTH is used to index inside the LO part of the shifting
// buffer (in terms of alignment units)
// ALIGNED_OFFSET_WIDTH is used to describe the length of a logging unit (in
// terms of alignment units)
localparam AXI_OFFSET_WIDTH = $clog2(AXI_WIDTH);
localparam SHIFTBUF_WIDTH = 2*AXI_WIDTH;
localparam NUM_ALIGNED = SHIFTBUF_WIDTH / PACKET_ALIGNMENT;
localparam PACKET_ALIGNMENT_WIDTH = $clog2(PACKET_ALIGNMENT);
localparam ALIGNED_OFFSET_WIDTH = OFFSET_WIDTH - PACKET_ALIGNMENT_WIDTH;
localparam AXI_ALIGNED_WIDTH = AXI_WIDTH / PACKET_ALIGNMENT;
localparam AXI_ALIGNED_OFFSET_WIDTH = AXI_OFFSET_WIDTH - PACKET_ALIGNMENT_WIDTH;

// parameter check
generate
    if (OFFSET_WIDTH != $clog2(LOGGING_UNIT_WIDTH+1))
        $error("WIDTH mismatch: OFFSET_WIDTH %d, LOGGING_UNIT_WIDTH %d\n",
            OFFSET_WIDTH, LOGGING_UNIT_WIDTH);
    // one assumption is that the logging unit is longer than an AXI transfer
    if (AXI_OFFSET_WIDTH >= OFFSET_WIDTH)
        $error("Invalid AXI_OFFSET_WIDTH %d OR Invalid OFFSET_WIDTH %d\n",
            AXI_OFFSET_WIDTH, OFFSET_WIDTH);
    if ((LOGGING_UNIT_WIDTH % PACKET_ALIGNMENT) != 0)
        $error("Invalid alignment: LOGGING_UNIT_WIDTH %d, PACKET_ALIGNMENT %d\n",
            LOGGING_UNIT_WIDTH, PACKET_ALIGNMENT);
    if ((AXI_WIDTH % PACKET_ALIGNMENT) != 0)
        $error("Invalid alignment: AXI_WIDTH %d, PACKET_ALIGNMENT %d\n",
            AXI_WIDTH, PACKET_ALIGNMENT);
    if (AXI_ALIGNED_OFFSET_WIDTH != $clog2(AXI_WIDTH/PACKET_ALIGNMENT))
        $error("Failed sanity check: AXI_ALIGNED_OFFSET_WIDTH might be wrong\n");
    if (ALIGNED_OFFSET_WIDTH != $clog2(LOGGING_UNIT_WIDTH/PACKET_ALIGNMENT))
        $error("Failed sanity check: ALIGNED_OFFSET_WIDTH might be wrong\n");
endgenerate

logic [2*AXI_WIDTH-1:0] shift_buf;
logic [NUM_ALIGNED-1:0] [PACKET_ALIGNMENT-1:0] shift_buf_aligned;
genvar i;
generate
for (i=0; i < NUM_ALIGNED; ++i)
    assign shift_buf_aligned[i] =
        shift_buf[i*PACKET_ALIGNMENT +: PACKET_ALIGNMENT];
endgenerate
// HI_FSM declaration
// EMPTY: init state
// FULL: Have valid data starting from hi_valid_off, can be used by or shift to
// the lo
/// {{{
typedef enum { HI_EMPTY, HI_FULL} HI_FSM_t;
(* fsm_encoding = "one_hot" *) HI_FSM_t hi_fsm, hi_fsm_next;
logic hi_in; // read data in to the hi buffer
assign hi_in = replay_in_fifo_rd_en;
logic hi_full; // single bit reg shortcut for hi_fsm == HI_FULL
/// }}}

// LO_FSM declaration
// EMPTY: init state
// HEADER: have valid data (header of a logging unit) starting from
// lo_valid_off, which may output to the assemble buffer
// BODY: have valid data (body of a logging unit) from lo_valid_off, which
// may output to the assemble buffer
/// {{{
typedef enum { LO_EMPTY, LO_HEADER, LO_BODY } LO_FSM_t;
(* fsm_encoding = "one_hot" *) LO_FSM_t lo_fsm, lo_fsm_next;
logic lo_empty; // single bit reg shortcut for lo_fsm == LO_EMPTY
logic [AXI_ALIGNED_OFFSET_WIDTH-1:0] lo_valid_off;
logic hi_lo_shift;  // transfer one axi unit from HI to LO
// output from the lo buffer to the ASM buffer
// lo_out should be paired with asm_ready
logic lo_out;
logic [AXI_WIDTH-1:0] lo_out_data;
assign lo_out_data = shift_buf_aligned[lo_valid_off +: AXI_ALIGNED_WIDTH];
// the remaining len of the valid data of the current loging unit waiting to be
// transmitted to the assemble buffer
// Only valid if
// 1. HI_FULL && LO_HEADER (decoded from the trace)
// 2. LO_BODY (from a register)
// NOTE that in the following usage, lo_remain_len is only used when lo_out,
// which guarantees lo_remain_len has valid data.
logic [ALIGNED_OFFSET_WIDTH-1:0] lo_remain_len;
// all LO (valid) data has been transmitted to the ASM buffer
// only valid when lo_out
logic lo_exhaust;
assign lo_exhaust =
    (lo_remain_len + ALIGNED_OFFSET_WIDTH'(lo_valid_off)) >=
    ALIGNED_OFFSET_WIDTH'(AXI_ALIGNED_WIDTH);
// Whether the output of LO contains the remaining of the logging unit
// only valid when lo_out
// Note that I assume only output when HI and LO have continuous valid data
logic lo_valid_satisfied;
assign lo_valid_satisfied =
    lo_remain_len <= AXI_ALIGNED_WIDTH;
/// }}}

// ASM_FSM
// WAIT_HEADER: init state, wait for the header of a logging unit to come
// WAIT_BODY: Have the header, wait for the rest of the logging unit
// DONE: Have the entire logging unit, enqueue to the output
// FULL: Have the entire logging unit, but also buffers the next header.
// NOTE: due to the backpressure design, FULL is unnecessary thus not
// implemented
/// {{{
typedef enum { ASM_WAIT_HEADER, ASM_WAIT_BODY, ASM_DONE } ASM_FSM_t;
(* fsm_encoding = "one_hot" *) ASM_FSM_t asm_fsm, asm_fsm_next;
localparam NUM_AXI = (LOGGING_UNIT_WIDTH - 1)/AXI_WIDTH + 1;
logic [NUM_AXI * AXI_WIDTH-1:0] trace_data;
logic [NUM_AXI-1:0] [AXI_WIDTH-1:0] trace_data_per_axi;
generate
   for (i=0; i < NUM_AXI; i=i+1) begin
      assign trace_data[i*AXI_WIDTH +: AXI_WIDTH] = trace_data_per_axi[i];
   end
endgenerate
// trace_axi_cnt is the total number of axi units assembled in the buffer
// trace_axi_cnt and trace_len are both valid when WAIT_BODY or DONE
logic [$clog2(NUM_AXI+1)-1:0] trace_axi_cnt;
logic [OFFSET_WIDTH-1:0] trace_len;
// ASM buffer can take in a new [AXI_WIDTH-1:0]. Make this register to improve
// timing, the combinational path breaks here.
// NOTE: asm_ready and the FULL state are currently not implemented
// reg asm_ready=1;
// buffer part of the trace (must be a header) during ASM_FULL
// logic [AXI_WIDTH-1:0] r_ptrace;
// buffer the length of the whole logging unit starting with the r_ptrace
// logic [OFFSET_WIDTH-1:0] r_ptrace_len;
logic asm_out;

// the almful backpressure has been propogated to the input of the shift buffer
assign replay_out_fifo_wr_en = asm_out;
assign replay_out_fifo_in = trace_data[0 +: LOGGING_UNIT_WIDTH];
/// }}}

// HI_FSM definition
//                  /--\ +- flow
//                  |  |
//           load   |  v
//  -------    +   ------
// |       | ---> |      |
// | EMPTY |      | FULL |
// |       | <--- |      |
//  -------    -   ------
//          unload
always_ff @(posedge clk)
    if (!sync_rst_n)
        hi_fsm <= HI_EMPTY;
    else
        hi_fsm <= hi_fsm_next;
always_comb begin
    case (hi_fsm)
        HI_EMPTY:
            if (hi_in)
                // load
                hi_fsm_next = HI_FULL;
            else
                hi_fsm_next = HI_EMPTY;
        HI_FULL:
            if (hi_lo_shift && !hi_in)
                // unload
                hi_fsm_next = HI_EMPTY;
            else
                // Note that HI_FULL && !hi_lo_shift |-> !hi_in
                // So this else branch actually represents
                // (!hi_lo_shift && !hi_in) || (hi_lo_shift && hi_in)
                // i.e. stall or flow
                hi_fsm_next = HI_FULL;
         default:
            hi_fsm_next = HI_EMPTY; // avoid latch
    endcase
end
// FIFO read in logic
assign replay_in_fifo_rd_en =
    !replay_in_fifo_empty && // has data
    !replay_out_fifo_almfull && // rate limit
    (!hi_full || hi_lo_shift);
// HI_FSM other states
always_ff @(posedge clk)
    if (!sync_rst_n) begin
        hi_full <= 0;
    end
    else begin
        case (hi_fsm)
            HI_EMPTY:
                if (hi_in)
                    hi_full <= 1;
                else
                    hi_full <= 0;
            HI_FULL:
                if (hi_lo_shift && !hi_in)
                    hi_full <= 0;
                else
                    hi_full <= 1;
            default: begin
                hi_full <= 0;
           end
        endcase
    end

// LO_FSM definition
//                  /--\ +- header_flow
//                  |  |
//           load   |  v     extend
//  -------   +    --------    +   ------
// |       | ---> |        | ---> |      | ---\
// | EMPTY |      | HEADER |      | BODY |    | +- body_flow
// |       | <xx- |        | <--- |      | <--/
//  -------        --------   +-   ------
//     ˄                     reload  |
//     |                             |
//      ------xxxxxxxxxxxxxxxxxx-----
always_ff @(posedge clk)
    if (!sync_rst_n)
        lo_fsm <= LO_EMPTY;
    else
        lo_fsm <= lo_fsm_next;
always_comb begin
    case (lo_fsm)
        LO_EMPTY:
            if (hi_lo_shift)
                // load
                lo_fsm_next = LO_HEADER;
            else
                lo_fsm_next = LO_EMPTY;
        LO_HEADER:
            // NOTE: I know there will be duplicated terms like hi_lo_shift and
            // lo_valid_satisfied both means HI_FULL. But I prefer simpler code
            // and count on the compiler optimizations.
            if (hi_lo_shift)
                // hi_lo_shift && LO_HEADER |->
                // HI_FULL && lo_out && lo_exhaust
                if (lo_valid_satisfied)
                    // header_flow (lo_exhaust)
                    lo_fsm_next = LO_HEADER;
                else
                    // extend
                    lo_fsm_next = LO_BODY;
            else if (lo_out && !lo_exhaust)
                // lo_out && LO_HEADER |-> HI_FULL && lo_out && !lo_exhaust
                // header_flow (!lo_exhaust)
                lo_fsm_next = LO_HEADER;
            else
                // !lo_out ==> stall
                lo_fsm_next = LO_HEADER;
        LO_BODY:
           if (hi_lo_shift)
               // i.e. HI_FULL && lo_out && lo_exhaust
               if (lo_valid_satisfied)
                   // reload (lo_exhaust)
                   lo_fsm_next = LO_HEADER;
               else
                   // body_flow (lo_exhaust)
                   lo_fsm_next = LO_BODY;
           else if (lo_out && !lo_exhaust)
               // i.e. HI_FULL && lo_out && !lo_exhaust
               // reload (!lo_exhaust)
               lo_fsm_next = LO_HEADER;
           else
               // !lo_out ==> stall
               lo_fsm_next = LO_BODY;
         default:
            lo_fsm_next = LO_EMPTY; // avoid latch
    endcase
end
// Only output from the shift buffer if
// The remaining valid data are across HI and LO so the boundary across HI and
// LO must have "continuous" valid data.
// Note that in the case of last packet resides in LO and it contains a complete
// logging unit, I assume an additional zero AXI_WIDTH to be padded.
assign lo_out =
    hi_full && !lo_empty;
// shift data from HI to LO when HI has valid data and either
// 1. the LO is initially empty
// OR
// 2. all of the LO is output to the assemble buffer
assign hi_lo_shift =
    hi_full &&
        (lo_empty ||
        (lo_out && lo_exhaust));
// LO_FSM other states
// lo_valid_off is valid when LO_HEADER or LO_BODY
always_ff @(posedge clk)
    if (!sync_rst_n)
        lo_valid_off <= 0;
    else
        case (lo_fsm)
            LO_EMPTY:
                // here omit an if (hi_lo_shift) // load
                // since even if !hi_lo_shift (stall), lo_valid_off is not valid
                // in LO_EMPTY, so no harm to save a if
                lo_valid_off <= 0;
            default:
                // unified LO_HEADER and LO_BODY
                if (hi_lo_shift)
                    if (lo_valid_satisfied)
                        // LO_HEADER |-> header_flow (lo_exhaust)
                        // LO_BODY |-> reload (lo_exhaust)
                        lo_valid_off <=
                            lo_remain_len[0 +: AXI_ALIGNED_OFFSET_WIDTH] +
                            lo_valid_off - AXI_ALIGNED_WIDTH;
                    else
                        // LO_HEADER |-> extend
                        // LO_BODY |-> body_flow (lo_exhaust)
                        lo_valid_off <= lo_valid_off;
                else if (lo_out && !lo_exhaust)
                    // LO_HEADER |-> header_flow (!lo_exhaust)
                    // LO_BODY |-> reload (!lo_exhaust)
                    lo_valid_off <=
                        lo_valid_off +
                        lo_remain_len[0 +: AXI_ALIGNED_OFFSET_WIDTH];
                else
                    // LO_HEADER/LO_BODY |-> stall
                    lo_valid_off <= lo_valid_off;
        endcase

always_ff @(posedge clk)
    if (!sync_rst_n)
        lo_empty <= 1;
    else
        case (lo_fsm)
            LO_EMPTY:
                if (hi_lo_shift)
                    lo_empty <= 0;
                else
                    lo_empty <= 1;
            default:
                lo_empty <= 0;
        endcase
reg [ALIGNED_OFFSET_WIDTH-1:0] lo_remain_len_reg;
always_comb
    case (lo_fsm)
        LO_HEADER:
            lo_remain_len =
                lo_out_data[PACKET_ALIGNMENT_WIDTH +: ALIGNED_OFFSET_WIDTH];
        LO_BODY:
            lo_remain_len = lo_remain_len_reg;
        default:
            lo_remain_len = 0;
    endcase
// note that lo_remain_len_reg is only valid when LO_BODY
always_ff @(posedge clk)
    // no need to reset
    // init lo_fsm invalidates lo_remain_len_reg
    case (lo_fsm)
        LO_HEADER:
            if (hi_lo_shift && !lo_valid_satisfied)
                // extend
                lo_remain_len_reg <= lo_remain_len - AXI_ALIGNED_WIDTH;
            else
                lo_remain_len_reg <= lo_remain_len_reg;
        LO_BODY:
            if (hi_lo_shift && !lo_valid_satisfied)
                // body_flow (lo_exhaust)
                lo_remain_len_reg <= lo_remain_len_reg - AXI_ALIGNED_WIDTH;
            else
                lo_remain_len_reg <= lo_remain_len_reg;
        default:
            lo_remain_len_reg <= lo_remain_len_reg;
    endcase

// shift_buffer
always_ff @(posedge clk) begin
    // no need to reset shift_buffer since all control signals have reset (other
    // state machine)
    if (hi_in)
        shift_buf[AXI_WIDTH +: AXI_WIDTH] <= replay_in_fifo_out;
    if (hi_lo_shift)
        shift_buf[0 +: AXI_WIDTH] <= shift_buf[AXI_WIDTH +: AXI_WIDTH];
end

// LO_FSM output data / ASM_FSM input data
logic asm_valid;
logic [AXI_WIDTH-1:0] asm_data_in;
logic [OFFSET_WIDTH-1:0] asm_valid_len_in;
always_ff @(posedge clk) begin
   if (!sync_rst_n)
      asm_valid <= 0;
   else
      asm_valid <= lo_out;
   asm_data_in <= lo_out_data;
   asm_valid_len_in <=
       // MSB: logging unit length in terms of alignment units
       {lo_remain_len,
       // LSB: padding lower bits to make the length in terms of bits
       {PACKET_ALIGNMENT_WIDTH{1'b0}}};
end

// ASM_FSM definition
//                     +
//      ---------- full_load ---------    --
//     |                              |  |  |
//     |           +- body_cont       |  |  | +-
//     |             /--\             |  |  | full reload
//     |      part   |  |             |  |  |
//     |      load   |  v    finish   ˅  |  ˅     fill
//  --------   +    ------     +     ----------    +     ------
// |        | ---> |      | ------> |          | -----> |      |
// | WAIT   |      | WAIT |         |   DONE   |        | FULL |
// | HEADER |      | BODY | <------ |          | <----- |      |
//  --------        ------     +-    ----------    -     ------
//     ˄               ˄      part     |       drain_full  |
//     |      -        |     reload    |                   |
//      -- exhaust ----|---------------                    |
//                     *----------- drain_part ------------*
//                                      -
// NOTE: due to the backpressure design, in DONE state, you can always output
// stuff so the FULL state is not implemented.
// There is a register barrier between shift buffer and assemble buffer
// to improve timing
// input: lo_remain_len (only come with the HEADER)
//        lo_out_data
// output: asm_out
always_ff @(posedge clk)
    if (!sync_rst_n)
        asm_fsm <= ASM_WAIT_HEADER;
    else
        asm_fsm <= asm_fsm_next;
always_comb begin
    case (asm_fsm)
        ASM_WAIT_HEADER:
            if (asm_valid)
                if (asm_valid_len_in <= AXI_WIDTH)
                    asm_fsm_next = ASM_DONE;        // full load
                else
                    asm_fsm_next = ASM_WAIT_BODY;   // part load
            else
                asm_fsm_next = ASM_WAIT_HEADER;     // stall
        ASM_WAIT_BODY:
            if (asm_valid)
                if (trace_len <= (trace_axi_cnt+1) * AXI_WIDTH)
                    asm_fsm_next = ASM_DONE;        // finish
                else
                    asm_fsm_next = ASM_WAIT_BODY;   // body_cont
            else
                asm_fsm_next = ASM_WAIT_BODY;       // stall
        ASM_DONE:
            if (asm_valid)
                if (asm_valid_len_in <= AXI_WIDTH)
                    asm_fsm_next = ASM_DONE;        // full reload
                else
                    asm_fsm_next = ASM_WAIT_BODY;   // part reload
            else
                asm_fsm_next = ASM_WAIT_HEADER;     // exhaust
            // due to the backpressure design, no stall
        default:
           asm_fsm_next = ASM_WAIT_HEADER; // avoid latch
    endcase
end
// ASM_FSM other states
always_ff @(posedge clk)
    if (!sync_rst_n) begin
        trace_axi_cnt <= 0;
        trace_len <= 0;
    end
    else begin
       case (asm_fsm)
          ASM_WAIT_BODY:
             // body_cont or finish
             trace_axi_cnt <= trace_axi_cnt + asm_valid;
          default:
             if (asm_valid) begin
                // full/part load, full/part reload
                trace_len <= asm_valid_len_in;
                trace_axi_cnt <= 1;
             end
       endcase
    end
always_ff @(posedge clk)
    //  no need to reset trace_data since all control signals have reset
    case (asm_fsm)
        ASM_WAIT_BODY:
            if (asm_valid)
               // body_cont or finish
               trace_data_per_axi[trace_axi_cnt] <= asm_data_in;
        default:
            if (asm_valid)
               // full/part load, full/part reload
               trace_data_per_axi[0] <= asm_data_in;
    endcase
always_comb
    case (asm_fsm)
        ASM_DONE:
            asm_out = 1;
        default:
            asm_out = 0;
    endcase
`ifdef TEST_REPLAY
`DEF_GET_LEN(GET_LEN, LOGB_CHANNEL_CNT, OFFSET_WIDTH, SHUFFLED_CHANNEL_WIDTHS)
// debug related
logic [AXI_WIDTH-1:0] hi_buf;
assign hi_buf = shift_buf[AXI_WIDTH +: AXI_WIDTH];
logic [AXI_WIDTH-1:0] lo_buf;
assign lo_buf = shift_buf[0 +: AXI_WIDTH];
`endif
endmodule