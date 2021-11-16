`include "cl_fpgarr_defs.svh"

module test_rr_parse_replay_trace_tb;
// TEST configuration
`define PKT_GEN_RULE_BALANCE ($urandom() % 2)
`define PKT_GEN_RULE_SMALL   (($urandom() % 10) == 0)
`define PKT_GEN_RULE_LARGE   ($urandom() % 10)
// TODO: Remember to test all three gen rules
`define PKT_GEN_RULE `PKT_GEN_RULE_BALANCE
localparam int TEST_BURST_LEN = 200;
localparam int NUM_BURST = 3;
// end of TEST configuration

`ifdef TEST_REPLAY

    localparam period = 4ns;
    localparam halfperiod = 2ns;

    localparam int LOGB_CHANNEL_CNT = 14;
    localparam int LOGE_CHANNEL_CNT = 25;
    localparam bit [LOGB_CHANNEL_CNT-1:0] [RR_CHANNEL_WIDTH_BITS-1:0] CHANNEL_WIDTHS = {
        RR_CHANNEL_WIDTH_BITS'(32),
        RR_CHANNEL_WIDTH_BITS'(36),
        RR_CHANNEL_WIDTH_BITS'(32),
        RR_CHANNEL_WIDTH_BITS'(32),
        RR_CHANNEL_WIDTH_BITS'(36),
        RR_CHANNEL_WIDTH_BITS'(32),
        RR_CHANNEL_WIDTH_BITS'(32),
        RR_CHANNEL_WIDTH_BITS'(36),
        RR_CHANNEL_WIDTH_BITS'(32),
        RR_CHANNEL_WIDTH_BITS'(531),
        RR_CHANNEL_WIDTH_BITS'(18),
        RR_CHANNEL_WIDTH_BITS'(91),
        RR_CHANNEL_WIDTH_BITS'(593),
        RR_CHANNEL_WIDTH_BITS'(91)
    };

    function automatic int GET_FULL_WIDTH;
        GET_FULL_WIDTH = 0;
        for (int i = 0; i < LOGB_CHANNEL_CNT; i++)
            GET_FULL_WIDTH += CHANNEL_WIDTHS[i];
        GET_FULL_WIDTH += LOGB_CHANNEL_CNT;
        GET_FULL_WIDTH += LOGE_CHANNEL_CNT;
    endfunction

    localparam WIDTH = GET_FULL_WIDTH();
    localparam OFFSET_WIDTH = $clog2(WIDTH+1);
    localparam AXI_WIDTH = 512;
    localparam AXI_ADDR_WIDTH = 64;

    function automatic bit [LOGB_CHANNEL_CNT-1:0]
      [RR_CHANNEL_WIDTH_BITS-1:0] GET_SHUFFLED_CHANNEL_WIDTHS();
      for (int i=0; i < LOGB_CHANNEL_CNT; i=i+1) begin
        GET_SHUFFLED_CHANNEL_WIDTHS[i] = CHANNEL_WIDTHS[record_pkg::SHUFFLE_PLAN[i][0]];
      end
    endfunction
    localparam bit [LOGB_CHANNEL_CNT-1:0] [RR_CHANNEL_WIDTH_BITS-1:0]
      SHUFFLED_CHANNEL_WIDTHS = GET_SHUFFLED_CHANNEL_WIDTHS();

    function automatic bit [WIDTH-1:0] GET_RANDOM_PKT;
        logic [OFFSET_WIDTH-1:0] k;
        GET_RANDOM_PKT = WIDTH'(0);
        k = LOGB_CHANNEL_CNT + LOGE_CHANNEL_CNT;
        for (int i = 0; i < LOGB_CHANNEL_CNT; i++) begin
            if (`PKT_GEN_RULE) begin
                GET_RANDOM_PKT[i] = 1;
                for (int j = k; j < k + SHUFFLED_CHANNEL_WIDTHS[i]; j++) begin
                    GET_RANDOM_PKT[j] = 1;
                end
                k = k + SHUFFLED_CHANNEL_WIDTHS[i];
            end
        end
    endfunction
    `DEF_GET_LEN(GET_LEN, LOGB_CHANNEL_CNT, OFFSET_WIDTH, SHUFFLED_CHANNEL_WIDTHS)

    logic clk;
    logic sync_rst_n;
    logic [1:0] cfg_max_payload;

    logic [WIDTH-1:0] record_din;
    logic [OFFSET_WIDTH-1:0] record_din_width;
    logic record_din_ready, record_din_valid;

    logic [WIDTH-1:0] replay_dout;
    logic [OFFSET_WIDTH-1:0] replay_dout_width;
    logic replay_dout_ready, replay_dout_valid;

    logic finish;
    logic record_finish;
    logic [AXI_ADDR_WIDTH-1:0] read_addr, read_size, buf_addr, buf_size;
    logic write_buf_update, read_buf_update;

    logic write_interrupt, read_interrupt;
    logic [63:0] record_bits, replay_bits;
    logic [63:0] record_bits_old;
    localparam bit [63:0] FAKE_INIT_REPLAY_BITS = 64'hffffffff;

    // for record replay cross-check
    logic [2*WIDTH-1:0] record_trace [NUM_BURST*TEST_BURST_LEN-1:0];
    logic [2*WIDTH-1:0] replay_trace [NUM_BURST*TEST_BURST_LEN-1:0];
    logic [OFFSET_WIDTH-1:0] record_len;
    logic [OFFSET_WIDTH-1:0] replay_len;
    int record_curr, replay_curr;
    int len;

    logic replay_dout_valid_ready_q;
    // end of record replay cross-check

    rr_axi_bus_t axi_bus();

    rr_trace_rw #(
        .WIDTH(WIDTH),
        .AXI_WIDTH(AXI_WIDTH),
        .OFFSET_WIDTH(OFFSET_WIDTH),
        .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
        .LOGB_CHANNEL_CNT(LOGB_CHANNEL_CNT),
        .LOGE_CHANNEL_CNT(LOGE_CHANNEL_CNT),
        .SHUFFLED_CHANNEL_WIDTHS(SHUFFLED_CHANNEL_WIDTHS))
    rr_trace_rw_inst(
        .clk(clk),
        .sync_rst_n(sync_rst_n),
        .cfg_max_payload(cfg_max_payload),
        .record_din_valid(record_din_valid),
        .record_din_ready(record_din_ready),
        .record_finish(record_finish),
        .record_din(record_din),
        .record_din_width(record_din_width),
        .replay_dout_valid(replay_dout_valid),
        .replay_dout_ready(replay_dout_ready),
        .replay_dout(replay_dout),
        .replay_dout_width(replay_dout_width),
        .axi_out(axi_bus),
        .write_buf_addr(buf_addr),
        .write_buf_size(buf_size),
        .write_buf_update(write_buf_update),
        .read_buf_addr(read_addr),
        .read_buf_size(read_size),
        .read_buf_update(read_buf_update),
        .write_interrupt(write_interrupt),
        .read_interrupt(read_interrupt),
        .record_bits(record_bits),
        .replay_bits(replay_bits)
    );

    always begin
        clk = 1;
        #halfperiod;
        clk = 0;
        #halfperiod;
    end

    logic [WIDTH-1:0] tmp_packet;
    logic [OFFSET_WIDTH-1:0] tmp_packet_len;

    always @(posedge clk) begin
        sync_rst_n <= 0;
        cfg_max_payload <= 0;
        finish <= 0;
        record_din <= 0;
        record_din_width <= 0;
        record_din_valid <= 0;
        record_finish <= 0;
        replay_dout_ready <= 1;
        axi_bus.awready <= 1;
        axi_bus.wready <= 1;
        axi_bus.arready <= 0;
        axi_bus.rvalid <= 0;
        replay_bits <= FAKE_INIT_REPLAY_BITS;
        #period;
        for (int i = 0; i < 100; i++) begin
            #period;
        end

        sync_rst_n <= 1;
        #period;
        for (int i = 0; i < 200; i++) begin
            #period;
        end

        write_buf_update <= 1;
        buf_addr <= 64'h10000000;
        buf_size <= 1024;
        #period;
        write_buf_update <= 0;
        #period;

        for (int i = 0; i < TEST_BURST_LEN; i++) begin
            tmp_packet = GET_RANDOM_PKT();
            tmp_packet_len = GET_LEN(tmp_packet[0 +: LOGB_CHANNEL_CNT]);
            record_din <= tmp_packet;
            record_din_width <= tmp_packet_len;
            record_din_valid <= 1;
            #period;
            while (~record_din_ready) begin
              #period;
            end
        end

        record_din_valid <= 0;
        #period;

        for (int i = 0; i < TEST_BURST_LEN; i++) begin
            tmp_packet = GET_RANDOM_PKT();
            tmp_packet_len = GET_LEN(tmp_packet[0 +: LOGB_CHANNEL_CNT]);
            record_din <= tmp_packet;
            record_din_width <= tmp_packet_len;
            record_din_valid <= 1;
            #period;
            while (~record_din_ready) begin
              #period;
            end
        end
        record_din <= 'hx;
        record_din_width <= 'hx;
        record_din_valid <= 0;

        replay_dout_ready <= 0;
        #period;
        replay_dout_ready <= 1;
        #period;
        for (int i = 0; i < TEST_BURST_LEN; i++) begin
            tmp_packet = GET_RANDOM_PKT();
            tmp_packet_len = GET_LEN(tmp_packet[0 +: LOGB_CHANNEL_CNT]);
            record_din <= tmp_packet;
            record_din_width <= tmp_packet_len;
            record_din_valid <= 1;
            #period;
            while (~record_din_ready) begin
              #period;
            end
        end
        record_din <= 'hx;
        record_din_width <= 'hx;
        record_din_valid <= 0;

        record_bits_old <= record_bits;
        #(period * 50);
        while (record_bits_old != record_bits) begin
            record_bits_old <= record_bits;
            #(period * 50);
        end
        record_finish <= 1;
        #period;
        record_finish <= 0;
        #(period * 100);
        replay_bits <= record_bits;


        for (int i = 0; i < 20; i++) begin
            #period;
        end

        finish <= 1;
        #period;

        finish <= 0;
        #period;

        for (int i = 0; i < 200; i++) begin
            #period;
        end
        $display("Record %d packets", record_curr);
        $display("Replay %d packets", replay_curr);

        $finish;
    end

    initial begin
        record_curr = 0;
        replay_curr = 0;
        for (int i = 0; i < 128; i++) begin
            record_trace[i] = 0;
            replay_trace[i] = 0;
        end
        replay_dout_valid_ready_q = 0;
    end

    always @(posedge clk) begin
        replay_dout_valid_ready_q <= replay_dout_valid && replay_dout_ready;
    end

    always @(posedge clk) begin
        if (replay_dout_valid && replay_dout_ready) begin
            $display("[wb_tb@%t]: #%d replay width %d (+width %d aligned to %d) data %x",
                $time, replay_curr,
                GET_LEN(replay_dout[0 +: LOGB_CHANNEL_CNT]),
                GET_LEN(replay_dout[0 +: LOGB_CHANNEL_CNT]) + OFFSET_WIDTH'(OFFSET_WIDTH),
                replay_dout_width, replay_dout);
        end

        // FIXME: should be record_din_valid && record_din_ready
        // But need to fix the trace_rw record_in_fifo wr_en signal first
        if (record_din_valid & record_din_ready) begin
            record_trace[record_curr][0 +: WIDTH] <= record_din;
            record_trace[record_curr][WIDTH +: WIDTH] <= 0;
            record_curr <= record_curr + 1;
            $display("[wb_tb]: #%d record width %d  data %x",
                record_curr, record_din_width, record_din);
        end

        if (replay_dout_valid && replay_dout_ready) begin
            replay_trace[replay_curr][0 +: WIDTH] <= replay_dout;
            replay_trace[replay_curr][WIDTH +: WIDTH] <= 0;
            replay_curr <= replay_curr + 1;
        end

        if (replay_dout_valid_ready_q) begin
            assert(replay_curr <= record_curr);

            record_len = GET_LEN(
                record_trace[replay_curr-1][0 +: LOGB_CHANNEL_CNT]);
            replay_len = GET_LEN(
                replay_trace[replay_curr-1][0 +: LOGB_CHANNEL_CNT]);
            if (record_len != replay_len)
                $display("replay width mismatch: record %d, replay %d",
                    record_len, replay_len);
            record_trace[replay_curr-1][replay_len +: WIDTH] = 0;
            replay_trace[replay_curr-1][replay_len +: WIDTH] = 0;
            if (record_trace[replay_curr-1] != replay_trace[replay_curr-1]) begin
                $display("#################################################");
                $display("WARNING: replay data mismatch:");
                $display("\trecord %x\n\treplay %x",
                    record_trace[replay_curr-1][0 +: WIDTH],
                    replay_trace[replay_curr-1][0 +: WIDTH]);
                $display("#################################################");
            end
        end

    end
`else
    $error("TEST_REPLAY should be defined to run this test\n");
`endif
endmodule




