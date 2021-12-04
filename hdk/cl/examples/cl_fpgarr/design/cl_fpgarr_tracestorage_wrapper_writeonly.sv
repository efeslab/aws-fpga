`include "cl_fpgarr_defs.svh"

module rr_trace_writeonly #(
    parameter WIDTH = 2500,
    parameter AXI_WIDTH = 512,
    parameter OFFSET_WIDTH = 32,
    parameter AXI_ADDR_WIDTH = 64,
    parameter ALMFULL_THRESHOLD = 100,
    parameter int LOGB_CHANNEL_CNT = 25,
    parameter int LOGE_CHANNEL_CNT = 25,
    parameter bit [LOGB_CHANNEL_CNT-1:0]
      [RR_CHANNEL_WIDTH_BITS-1:0] SHUFFLED_CHANNEL_WIDTHS) (
    input clk,
    input sync_rst_n,

    input logic record_din_valid,
    output logic record_din_ready,
    input logic record_finish,
    input logic [WIDTH-1:0] record_din,
    input logic [OFFSET_WIDTH-1:0] record_din_width,

    rr_axi_bus_t.slave axi_out,

    input logic [AXI_ADDR_WIDTH-1:0] write_buf_addr,
    input logic [AXI_ADDR_WIDTH-1:0] write_buf_size,
    input logic write_buf_update,

    output logic write_interrupt,

    // The number of recorded bits, will used by the software
    output logic [63:0] record_bits,
    output logic [1:0] overflowed,
    output logic [1:0] underflowed
);

    localparam NSTAGES = (WIDTH - 1) / AXI_WIDTH + 1;
    localparam EXT_WIDTH = NSTAGES * AXI_WIDTH;

    localparam ALIGNED_WIDTH = `GET_ALIGNED_SIZE(WIDTH + OFFSET_WIDTH);
    // parameter check
    generate
      if (OFFSET_WIDTH < $clog2(ALIGNED_WIDTH+1))
         $error("WIDTH mismatch: OFFSET_WIDTH %d, ALIGNED_WIDTH %d\n",
            OFFSET_WIDTH, ALIGNED_WIDTH);
      if (ALIGNED_WIDTH < WIDTH)
         $error("Invalid ALIGNED_WIDTH %d (WIDTH %d)\n",
            ALIGNED_WIDTH, WIDTH);
      if (2**$clog2(PACKET_ALIGNMENT) != PACKET_ALIGNMENT)
         $error("PACKET_ALIGNMENT (%d) has to be a power of 2\n",
            PACKET_ALIGNMENT);
    endgenerate

    logic [WIDTH-1:0] record_in_fifo_out;
    logic [ALIGNED_WIDTH-1:0] record_in_fifo_out_aligned;
    logic [OFFSET_WIDTH-1:0] record_in_fifo_out_width;
    logic [OFFSET_WIDTH-1:0] record_in_fifo_out_width_aligned;
    logic record_in_fifo_rd_en;
    logic record_in_fifo_full, record_in_fifo_almfull, record_in_fifo_empty;

    merged_fifo #(
        .WIDTH(WIDTH+OFFSET_WIDTH),
        .ALMFULL_THRESHOLD(ALMFULL_THRESHOLD))
    mfifo_inst_record_in(
        .clk(clk),
        .rst(~sync_rst_n),
        .din({record_din,record_din_width}),
        .dout({record_in_fifo_out,record_in_fifo_out_width}),
        .wr_en(record_din_valid & record_din_ready),
        .rd_en(record_in_fifo_rd_en),
        .full(record_in_fifo_full),
        .almfull(record_in_fifo_almfull),
        .empty(record_in_fifo_empty)
    );
    // align the logging unit as well as its length
    // The length of the logging unit is concat with the content before given to
    // the trace_merge (record) module
    // Note that the padding for the alignment comes from the "potentionally"
    // uninitialized part of the logb_data
    // TODO: remove the $clog2(PACKET_ALIGNMENT) lower bits, which is always 0
    assign record_in_fifo_out_aligned = ALIGNED_WIDTH'(
        // MSB: logging data  LSB: aligned_width
        {record_in_fifo_out, record_in_fifo_out_width_aligned}
    );
    assign record_in_fifo_out_width_aligned = `GET_ALIGNED_SIZE_W(
       OFFSET_WIDTH, record_in_fifo_out_width + OFFSET_WIDTH);

    logic [AXI_WIDTH-1:0] record_out_fifo_out, record_out_fifo_in_qq;
    logic record_out_fifo_rd_en, record_out_fifo_wr_en_qq;
    logic [OFFSET_WIDTH-1:0] record_out_fifo_in_size_qq, record_out_fifo_out_size;
    logic record_out_fifo_full, record_out_fifo_almfull, record_out_fifo_empty;

    rr_trace_merge #(
        .WIDTH(ALIGNED_WIDTH),
        .AXI_WIDTH(AXI_WIDTH),
        .OFFSET_WIDTH(OFFSET_WIDTH),
        .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
        .LOGB_CHANNEL_CNT(LOGB_CHANNEL_CNT),
        .LOGE_CHANNEL_CNT(LOGE_CHANNEL_CNT))
    trace_merge(
        .clk(clk),
        .sync_rst_n(sync_rst_n),
        .record_in_fifo_out(record_in_fifo_out_aligned),
        .record_in_fifo_out_width(record_in_fifo_out_width_aligned),
        .record_in_fifo_rd_en(record_in_fifo_rd_en),
        .record_in_fifo_full(record_in_fifo_full),
        .record_in_fifo_almfull(record_in_fifo_almfull),
        .record_in_fifo_empty(record_in_fifo_empty),
        .record_out_fifo_in_qq(record_out_fifo_in_qq),
        .record_out_fifo_wr_en_qq(record_out_fifo_wr_en_qq),
        .record_out_fifo_in_size_qq(record_out_fifo_in_size_qq),
        .record_out_fifo_full(record_out_fifo_full),
        .record_out_fifo_almfull(record_out_fifo_almfull),
        .record_out_fifo_empty(record_out_fifo_empty),
        .record_finish(record_finish),
        .record_din_valid(record_din_valid)
    );

    merged_fifo #(
        .WIDTH(AXI_WIDTH+OFFSET_WIDTH),
        .ALMFULL_THRESHOLD(ALMFULL_THRESHOLD))
    mfifo_inst_record_out(
        .clk(clk),
        .rst(~sync_rst_n),
        .din({record_out_fifo_in_size_qq, record_out_fifo_in_qq}),
        .dout({record_out_fifo_out_size, record_out_fifo_out}),
        .wr_en(record_out_fifo_wr_en_qq),
        .rd_en(record_out_fifo_rd_en),
        .full(record_out_fifo_full),
        .almfull(record_out_fifo_almfull),
        .empty(record_out_fifo_empty)
    );

    always_ff @(posedge clk) begin
        if (~sync_rst_n) begin
            record_din_ready <= 0;
        end else begin
            record_din_ready <= ~record_in_fifo_almfull && ~record_out_fifo_almfull;
        end
    end

    logic [AXI_ADDR_WIDTH-1:0] write_buf_curr, write_buf_end;
    logic write_buf_write_en;
    always_ff @(posedge clk) begin
        if (~sync_rst_n) begin
            write_buf_curr <= 0;
            write_buf_end <= 0;
        end else if (write_buf_update) begin
            write_buf_curr <= write_buf_addr;
            write_buf_end <= write_buf_addr + write_buf_size;
        end else if (write_buf_write_en) begin
            write_buf_curr <= write_buf_curr + AXI_WIDTH/8;
        end

        write_interrupt <= (write_buf_curr == write_buf_end);
    end

    logic axi_aw_transmitted, axi_w_transmitted, axi_write_transmitted;
    logic axi_aw_working, axi_w_working, axi_write_working;
    assign axi_aw_transmitted = axi_out.awready & axi_out.awvalid;
    assign axi_w_transmitted = axi_out.wready & axi_out.wvalid;
    assign axi_aw_working = axi_out.awvalid & ~axi_out.awready;
    assign axi_w_working = axi_out.wvalid & ~axi_out.wready;
    assign axi_write_working = axi_aw_working | axi_w_working;

    // Transaction control
    logic axi_aw_handled, axi_w_handled;
    always_ff @(posedge clk) begin
        if (~sync_rst_n) begin
            axi_aw_handled <= 0;
            axi_w_handled <= 0;
        end else begin
            if (axi_aw_transmitted & axi_w_transmitted) begin
                axi_aw_handled <= 0;
            end else if (axi_aw_transmitted & ~axi_w_transmitted & ~axi_w_handled) begin
                axi_aw_handled <= 1;
            end else if (axi_aw_handled & axi_w_transmitted) begin
                axi_aw_handled <= 0;
            end

            if (axi_aw_transmitted & axi_w_transmitted) begin
                axi_w_handled <= 0;
            end else if (axi_w_transmitted & ~axi_aw_transmitted & ~axi_aw_handled) begin
                axi_w_handled <= 1;
            end else if (axi_w_handled & axi_aw_transmitted) begin
                axi_w_handled <= 0;
            end
        end
    end

    assign axi_write_transmitted = (axi_aw_transmitted | axi_aw_handled) & (axi_w_transmitted | axi_w_handled);
    assign write_buf_write_en = axi_write_transmitted;

    // Valid control
    always_ff @(posedge clk) begin
        if (~sync_rst_n) begin
            axi_out.awvalid <= 0;
            axi_out.wvalid <= 0;
        end else begin
            if (axi_aw_working) begin
                axi_out.awvalid <= 1;
            end else if (axi_w_working) begin
                axi_out.awvalid <= 0;
            end else begin
                if (write_buf_write_en)
                    axi_out.awvalid <= ~record_out_fifo_empty && write_buf_curr + AXI_WIDTH/8 < write_buf_end;
                else
                    axi_out.awvalid <= ~record_out_fifo_empty && write_buf_curr < write_buf_end;
            end

            if (axi_w_working) begin
                axi_out.wvalid <= 1;
            end else if (axi_aw_working) begin
                axi_out.wvalid <= 0;
            end else begin
                axi_out.wvalid <= ~record_out_fifo_empty && write_buf_curr < write_buf_end;
            end
        end
    end

    always_ff @(posedge clk) begin
        if (~sync_rst_n) begin
            axi_out.wdata <= 0;
        end else begin
            if (~axi_aw_working & ~axi_w_working & ~record_out_fifo_empty)
                axi_out.wdata <= record_out_fifo_out;
        end
    end

    assign record_out_fifo_rd_en = ~axi_aw_working & ~axi_w_working & ~record_out_fifo_empty & (write_buf_curr != write_buf_end);

    always_ff @(posedge clk) begin
        if (~sync_rst_n) begin
            record_bits <= 0;
        end else begin
            if (write_buf_update) begin
                record_bits <= 0;
            end else if (record_out_fifo_rd_en) begin
                record_bits <= record_bits + record_out_fifo_out_size;
            end
        end
    end

    logic [PCIM_INTERCONNECT_AXI_ID_WIDTH-1:0] tid;
    always_ff @(posedge clk) begin
        if (~sync_rst_n) begin
            tid <= 0;
        end else begin
            if (axi_write_transmitted) begin
                tid <= MAX_PCIM_AWID_WIDTH'(tid + 1);
            end
        end
    end

    // AW extras
    assign axi_out.awid = tid;
    assign axi_out.awaddr = write_buf_curr;
    assign axi_out.awlen = 0;
    assign axi_out.awsize = 3'b110; // 3'b110 means 64 bytes

    // W extras
    assign axi_out.wid = tid;
    assign axi_out.wstrb = -1;
    assign axi_out.wlast = 1;

    // B
    assign axi_out.bready = 1;

    // AR
    assign axi_out.arvalid = 0;

    // R
    assign axi_out.rready = 1;

`ifdef WRITEBACK_DEBUG
    // Debugging info for AXI write
    always_ff @(posedge clk) begin
        if (axi_out.awvalid & axi_out.awready)
            $display("[validate_writeback]: axi write addr 0x%x", axi_out.awaddr);
        if (axi_out.wvalid & axi_out.wready)
            $display("[validate_writeback]: axi write data 0x%x", axi_out.wdata);
    end

    always_ff @(posedge clk) begin
        if (axi_out.awvalid & axi_out.awready & (axi_out.awaddr == 0))
            $stop;
    end

    always_ff @(posedge clk) begin
        if (record_in_fifo_rd_en)
            $display("[validate_bus]: width\t%d (aligned to %d)\tcalculated width\t%d\tdata\t%x",
                record_in_fifo_out_width, record_in_fifo_out_width_aligned,
                GET_LEN(record_in_fifo_out[0 +: LOGB_CHANNEL_CNT]), record_in_fifo_out);
    end
`endif

    logic record_in_fifo_overflowed, record_out_fifo_overflowed;
    always_ff @(posedge clk) begin
        if (~sync_rst_n) begin
            record_in_fifo_overflowed <= 0;
            record_out_fifo_overflowed <= 0;
        end else begin
            if (record_in_fifo_full && record_din_valid && record_din_ready) begin
                record_in_fifo_overflowed <= 1;
                assert(0);
            end
            if (record_out_fifo_full && record_out_fifo_wr_en_qq) begin
                record_out_fifo_overflowed <= 1;
                assert(0);
            end
        end
    end
    assign overflowed = {record_in_fifo_overflowed, record_out_fifo_overflowed};

    logic record_in_fifo_underflowed, record_out_fifo_underflowed;
    always_ff @(posedge clk) begin
        if (~sync_rst_n) begin
            record_in_fifo_underflowed <= 0;
            record_out_fifo_underflowed <= 0;
        end else begin
            if (record_in_fifo_empty && record_in_fifo_rd_en) begin
                record_in_fifo_underflowed <= 1;
                assert(0);
            end
            if (record_out_fifo_empty && record_out_fifo_rd_en) begin
                record_out_fifo_underflowed <= 1;
                assert(0);
            end
        end
    end
    assign underflowed = {record_in_fifo_underflowed, record_out_fifo_underflowed};
`ifdef DEBUG_INTERCONNECT
pcim_dbg_cnt dbg_cnt (
    .clk(clk), .rstn(sync_rst_n),
    .bus(axi_out)
);
`endif
endmodule
