`include "cl_fpgarr_defs.svh"

module test_writeback_tb;

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
    localparam OFFSET_WIDTH = $clog2(WIDTH-1) + 1;
    localparam AXI_WIDTH = 512;
    localparam AXI_ADDR_WIDTH = 64;

    function automatic bit [LOGB_CHANNEL_CNT-1:0]
      [RR_CHANNEL_WIDTH_BITS-1:0] GET_SHUFFLED_CHANNEL_WIDTHS();
      for (int i=0; i < LOGB_CHANNEL_CNT; i=i+1) begin
        GET_SHUFFLED_CHANNEL_WIDTHS[i] = CHANNEL_WIDTHS[SHUFFLE_PLAN[i][0]];
      end
    endfunction
    localparam bit [LOGB_CHANNEL_CNT-1:0] [RR_CHANNEL_WIDTH_BITS-1:0]
      SHUFFLED_CHANNEL_WIDTHS = GET_SHUFFLED_CHANNEL_WIDTHS();

    function automatic bit [WIDTH-1:0] GET_RANDOM_PKT;
        logic [OFFSET_WIDTH-1:0] k;
        GET_RANDOM_PKT = WIDTH'(0);
        k = LOGB_CHANNEL_CNT + LOGE_CHANNEL_CNT;
        for (int i = 0; i < LOGB_CHANNEL_CNT; i++) begin
            if ($urandom() % 2) begin
                GET_RANDOM_PKT[i] = 1;
                for (int j = k; j < k + SHUFFLED_CHANNEL_WIDTHS[i]; j++) begin
                    GET_RANDOM_PKT[j] = 1;
                end
                k = k + SHUFFLED_CHANNEL_WIDTHS[i];
            end
        end
    endfunction

    function automatic bit [OFFSET_WIDTH-1:0] GET_LEN (logic [WIDTH-1:0] packet);
        logic [LOGB_CHANNEL_CNT-1:0] logb_bitmap;
        logb_bitmap = packet[0 +: LOGB_CHANNEL_CNT];
        GET_LEN = LOGB_CHANNEL_CNT + LOGE_CHANNEL_CNT;
        for (int i = 0; i < LOGB_CHANNEL_CNT; i = i + 1) begin
            if (logb_bitmap[i])
                GET_LEN += OFFSET_WIDTH'(SHUFFLED_CHANNEL_WIDTHS[i]);
        end
    endfunction

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
    logic [AXI_ADDR_WIDTH-1:0] buf_addr, buf_size;
    logic write_buf_update, read_buf_update;

    logic write_interrupt, read_interrupt;

    rr_axi_bus_t axi_bus();

    rr_trace_rw #(
        .WIDTH(WIDTH),
        .AXI_WIDTH(AXI_WIDTH),
        .OFFSET_WIDTH(OFFSET_WIDTH),
        .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
        .LOGB_CHANNEL_CNT(LOGB_CHANNEL_CNT),
        .LOGE_CHANNEL_CNT(LOGE_CHANNEL_CNT),
        .CHANNEL_WIDTHS(CHANNEL_WIDTHS))
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
        .read_interrupt(read_interrupt)
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
        replay_dout_ready <= 1;
        axi_bus.awready <= 1;
        axi_bus.wready <= 1;
        axi_bus.arready <= 0;
        axi_bus.rvalid <= 0;
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

        for (int i = 0; i < 5; i++) begin
            tmp_packet = GET_RANDOM_PKT();
            tmp_packet_len = GET_LEN(tmp_packet);
            $display("[wb_tb]: record width %d data %x", tmp_packet_len, tmp_packet);
            record_din <= tmp_packet;
            record_din_width <= tmp_packet_len;
            record_din_valid <= 1;
            #period;
        end

        record_din_valid <= 0;
        #period;

        for (int i = 0; i < 5; i++) begin
            tmp_packet = GET_RANDOM_PKT();
            tmp_packet_len = GET_LEN(tmp_packet);
            $display("[wb_tb]: record width %d data %x", tmp_packet_len, tmp_packet);
            record_din <= tmp_packet;
            record_din_width <= tmp_packet_len;
            record_din_valid <= 1;
            #period;
        end

        record_din <= 0;
        record_din_valid <= 0;
        #period;

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

        $finish;
    end

    logic [WIDTH-1:0] record_trace [127:0];
    logic [WIDTH-1:0] replay_trace [127:0];
    int record_curr, replay_curr;
    int len;

    logic replay_dout_valid_q;

    initial begin
        record_curr = 0;
        replay_curr = 0;
        for (int i = 0; i < 128; i++) begin
            record_trace[i] = 0;
            replay_trace[i] = 0;
        end
        replay_dout_valid_q = 0;
    end

    always @(posedge clk) begin
        replay_dout_valid_q <= replay_dout_valid;
    end

    always @(posedge clk) begin
        if (replay_dout_valid) begin
            $display("[wb_tb]: replay width %d data %x", replay_dout_width, replay_dout);
        end

        if (record_din_valid) begin
            record_trace[record_curr] <= record_din;
            record_curr <= record_curr + 1;
        end

        if (replay_dout_valid) begin
            replay_trace[replay_curr] <= replay_dout;
            replay_curr <= replay_curr + 1;
        end

        if (replay_dout_valid_q) begin
            assert(replay_curr <= record_curr);
            assert(GET_LEN(record_trace[replay_curr-1]) == GET_LEN(replay_trace[replay_curr-1]));
        end

    end

`endif

endmodule




