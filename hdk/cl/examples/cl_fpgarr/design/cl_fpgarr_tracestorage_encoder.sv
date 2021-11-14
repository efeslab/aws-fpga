`include "cl_fpgarr_defs.svh"

// This tracestorage_encoder file is to prepare the record logging data for
// writeback to DRAM
module rr_trace_merge #(
    parameter WIDTH = 2500,
    parameter AXI_WIDTH = 512,
    parameter OFFSET_WIDTH = 32,
    parameter AXI_ADDR_WIDTH = 64,
    parameter int LOGB_CHANNEL_CNT = 25,
    parameter int LOGE_CHANNEL_CNT = 25) (
    input clk,
    input sync_rst_n,

    input logic [WIDTH-1:0] record_in_fifo_out,
    input logic [OFFSET_WIDTH-1:0] record_in_fifo_out_width,
    output logic record_in_fifo_rd_en,
    input logic record_in_fifo_full,
    input logic record_in_fifo_almfull,
    input logic record_in_fifo_empty,

    output logic [AXI_WIDTH-1:0] record_out_fifo_in_qq,
    output logic record_out_fifo_wr_en_qq,
    output logic [OFFSET_WIDTH-1:0] record_out_fifo_in_size_qq,
    input logic record_out_fifo_full,
    input logic record_out_fifo_almfull,
    input logic record_out_fifo_empty,

    input logic record_finish,
    input logic record_din_valid
);

    localparam NSTAGES = (WIDTH - 1) / AXI_WIDTH + 1;
    localparam EXT_WIDTH = NSTAGES * AXI_WIDTH;

    // The width has to be aligned
    initial assert(WIDTH % PACKET_ALIGNMENT == 0);
    always_ff @(posedge clk) begin
        if (sync_rst_n && record_in_fifo_rd_en)
            assert(record_in_fifo_out_width % PACKET_ALIGNMENT == 0);
    end

    logic [EXT_WIDTH-1:0] record_in_fifo_out_wrap;
    assign record_in_fifo_out_wrap = EXT_WIDTH'(record_in_fifo_out);

    logic [AXI_WIDTH-1:0] record_out_fifo_in, record_out_fifo_in_q;
    logic record_out_fifo_wr_en, record_out_fifo_wr_en_q;
    logic [OFFSET_WIDTH-1:0] record_out_fifo_in_size, record_out_fifo_in_size_q;
    always_ff @(posedge clk) begin
        if (~sync_rst_n) begin
            record_out_fifo_wr_en_q <= 0;
            record_out_fifo_wr_en_qq <= 0;
        end else begin
            record_out_fifo_in_q <= record_out_fifo_in;
            record_out_fifo_in_qq <= record_out_fifo_in_q;
            record_out_fifo_wr_en_q <= record_out_fifo_wr_en;
            record_out_fifo_wr_en_qq <= record_out_fifo_wr_en_q;
            record_out_fifo_in_size_q <= record_out_fifo_in_size;
            record_out_fifo_in_size_qq <= record_out_fifo_in_size_q;
        end
    end

    logic [OFFSET_WIDTH-1:0] record_unhandled_size;
    logic [AXI_WIDTH-1:0] record_unhandled [NSTAGES-1:0];
    logic [AXI_WIDTH-1:0] current_record_unhandled;
    logic [OFFSET_WIDTH-1:0] current_record_unhandled_size;
    logic [AXI_WIDTH-1:0] record_leftover;
    logic [AXI_WIDTH*2/PACKET_ALIGNMENT-1:0][PACKET_ALIGNMENT-1:0] record_leftover_next;
    logic [$clog2(AXI_WIDTH):0] record_leftover_size;
    logic [$clog2(NSTAGES):0] record_curr;
    logic do_record_finish;

    assign record_in_fifo_rd_en = ~record_in_fifo_empty && ~record_out_fifo_almfull && record_unhandled_size <= AXI_WIDTH;
    always_comb begin
        record_leftover_next = {'hx, record_leftover};
        for (int i = 0; i < AXI_WIDTH/PACKET_ALIGNMENT; i++) begin
            record_leftover_next[`GET_FORCE_ALIGNED_FRAME(record_leftover_size) + i]
                                            = current_record_unhandled[i * PACKET_ALIGNMENT +: PACKET_ALIGNMENT];
        end
    end

    always_ff @(posedge clk) begin
        if (~sync_rst_n) begin
            record_unhandled_size <= 0;
            record_leftover_size <= 0;
            record_curr <= NSTAGES - 1;
            do_record_finish <= 0;
            record_out_fifo_in <= 0;
            record_out_fifo_wr_en <= 0;
            current_record_unhandled_size <= 0;
            record_out_fifo_in_size <= 0;
        end else begin
            if (record_finish) begin
                do_record_finish <= 1;
            end

            if (record_in_fifo_rd_en) begin
                record_curr <= 0;
                record_unhandled_size <= record_in_fifo_out_width;
                for (int i = 0; i < NSTAGES; i++) begin
                    record_unhandled[i] <= record_in_fifo_out_wrap[i*AXI_WIDTH+:AXI_WIDTH];
                end
            end else if (record_curr + 1 < NSTAGES) begin
                record_curr <= record_curr + 1;
                if (record_unhandled_size >= AXI_WIDTH) begin
                    record_unhandled_size <= record_unhandled_size - AXI_WIDTH;
                end else begin
                    record_unhandled_size <= 0;
                end
            end
            else if (do_record_finish && record_in_fifo_empty && ~record_din_valid && record_leftover_size > 0) begin
                record_curr <= 0;
                record_unhandled_size <= AXI_WIDTH - record_leftover_size;
                record_unhandled[0] <= {AXI_WIDTH{1'h0}};
                do_record_finish <= 0;
            end

            if (record_unhandled_size >= AXI_WIDTH) begin
                current_record_unhandled_size <= AXI_WIDTH;
            end else begin
                current_record_unhandled_size <= record_unhandled_size;
            end
            // This may not matter, but I do not want any buffer overflow.
            assert(record_curr < NSTAGES);
            current_record_unhandled <= record_unhandled[record_curr];

            if (record_leftover_size + current_record_unhandled_size >= AXI_WIDTH) begin
                record_leftover <= record_leftover_next[AXI_WIDTH/PACKET_ALIGNMENT +: AXI_WIDTH/PACKET_ALIGNMENT];
                record_leftover_size <= record_leftover_size + current_record_unhandled_size - AXI_WIDTH;
                record_out_fifo_in <= record_leftover_next[0 +: AXI_WIDTH/PACKET_ALIGNMENT];
                record_out_fifo_in_size <= AXI_WIDTH;
                record_out_fifo_wr_en <= 1;
            end else if (do_record_finish && record_in_fifo_empty && ~record_din_valid) begin
                if (record_leftover_size > 0) begin
                    record_out_fifo_wr_en <= 1;
                    record_out_fifo_in <= record_leftover;
                    record_out_fifo_in_size <= record_leftover_size;
                    do_record_finish <= 0;
                    record_leftover_size <= 0;
                end
            end else begin
                record_leftover <= record_leftover_next[0 +: AXI_WIDTH/PACKET_ALIGNMENT];
                record_leftover_size <= record_leftover_size + current_record_unhandled_size;
                record_out_fifo_wr_en <= 0;
            end
        end
    end
endmodule

