module test_writeback_tb;

    localparam period = 4ns;
    localparam halfperiod = 2ns;

    localparam WIDTH = 1500;
    localparam OFFSETWIDTH = $clog2(WIDTH-1) + 1;
    localparam AXI_WIDTH = 512;
    localparam AXI_ADDR_WIDTH = 64;

    logic clk;
    logic sync_rst_n;
    logic [1:0] cfg_max_payload;
    logic [WIDTH-1:0] din;
    logic [OFFSETWIDTH-1:0] din_width;
    logic din_ready, din_valid;
    logic [AXI_WIDTH-1:0] test_out;
    logic finish;
    logic [AXI_ADDR_WIDTH-1:0] buf_addr, buf_size;
    logic buf_update;
    logic interrupt;

    rr_axi_bus_t axi_bus();

    rr_writeback #(
        .WIDTH(WIDTH),
        .AXI_WIDTH(AXI_WIDTH),
        .OFFSETWIDTH(OFFSETWIDTH))
    rr_writeback_inst(
        .clk(clk),
        .sync_rst_n(sync_rst_n),
        .cfg_max_payload(cfg_max_payload),
        .din_valid(din_valid),
        .din_ready(din_ready),
        .din_width(din_width),
        .finish(finish),
        .din(din),
        .buf_addr(buf_addr),
        .buf_size(buf_size),
        .buf_update(buf_update),
        .axi_out(axi_bus)
    );

    always begin
        clk = 1;
        #halfperiod;
        clk = 0;
        #halfperiod;
    end

    always @(posedge clk) begin
        sync_rst_n <= 0;
        cfg_max_payload <= 0;
        finish <= 0;
        din <= 0;
        din_width <= 0;
        din_valid <= 0;
        axi_bus.awready <= 1;
        axi_bus.wready <= 1;
        #period;
        for (int i = 0; i < 100; i++) begin
            #period;
        end

        sync_rst_n <= 1;
        #period;
        for (int i = 0; i < 200; i++) begin
            #period;
        end

        buf_update <= 1;
        buf_addr <= 0;
        buf_size <= 1024;
        #period;
        buf_update <= 0;
        #period;

        din <= {0, 513'(-1)};
        din_width <= 513;
        din_valid <= 1;
        #period;

        din <= {0};
        din_width <= 233;
        din_valid <= 1;
        #period;

        din_valid <= 0;
        #period;

        din <= {0, 1023'(-1)};
        din_width <= 1023;
        din_valid <= 1;
        #period;

        din <= 0;
        din_width <= 233;
        din_valid <= 1;
        #period;

        din <= -1;
        din_width <= 1000;
        din_valid <= 1;
        #period;

        din <= 0;
        din_width <= 1000;
        din_valid <= 1;
        #period;

        din <= -1;
        din_width <= 1000;
        din_valid <= 1;
        #period;

        din <= 0;
        din_valid <= 0;
        #period;

        finish <= 1;
        #period;

        finish <= 0;
        #period;

        for (int i = 0; i < 200; i++) begin
            #period;
        end

        $finish;
    end
endmodule




