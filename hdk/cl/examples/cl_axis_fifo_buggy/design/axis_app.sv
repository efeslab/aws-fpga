module axis_app #(
    parameter ADDR_WIDTH,
    parameter DATA_WIDTH
) (
    input wire clk,
    input wire rstn,
    axi_bus_W_t.master pcis_write_bus,
    axi_lite_bus_t.master sh_ocl_bus,
    axi_bus_t.slave ddr_mstr_bus
);

//// pcis write to axis
axis_bus_t #(.DATA_WIDTH(DATA_WIDTH), .USER_WIDTH(0)) axis_in();
axis_bus_t #(.DATA_WIDTH(DATA_WIDTH), .USER_WIDTH(0)) axis_out();
axi_bus_W_t ddr_w_bus();
pcis_w_to_axis pcis2axis_inst(
    .clk(clk), .rstn(rstn),
    .pcis_write_bus(pcis_write_bus),
    .axis(axis_in)
);
axis_fifo_wrapper #(
    .ADDR_WIDTH(ADDR_WIDTH),
    .DATA_WIDTH(DATA_WIDTH),
    .USER_WIDTH(1)
) axis_fifo_inst (
    .clk(clk), .rst(!rstn),
    .s_axis_tdata(axis_in.tdata),
    .s_axis_tvalid(axis_in.tvalid),
    .s_axis_tready(axis_in.tready),
    .s_axis_tlast(axis_in.tlast),
    .s_axis_tuser(axis_in.tuser),
    .m_axis_tdata(axis_out.tdata),
    .m_axis_tvalid(axis_out.tvalid),
    .m_axis_tready(axis_out.tready),
    .m_axis_tlast(axis_out.tlast),
    .m_axis_tuser(axis_out.tuser),
    .status_overflow(),
    .status_bad_frame(),
    .status_good_frame()
);

axis_to_ddr_w axis2ddrw_inst(
    .clk(clk), .rstn(rstn),
    .axis(axis_out),
    .ddr_w_bus(ddr_w_bus)
);

// disable read of the ddr_mstr_bus
assign ddr_mstr_bus.arvalid = 0;
assign ddr_mstr_bus.rready = 1;
// write of ddr_mstr_bus
assign ddr_mstr_bus.awid = {10'h0, ddr_w_bus.awid};
assign ddr_mstr_bus.awaddr = ddr_w_bus.awaddr;
assign ddr_mstr_bus.awlen = ddr_w_bus.awlen;
assign ddr_mstr_bus.awsize = ddr_w_bus.awsize;
assign ddr_mstr_bus.awvalid = ddr_w_bus.awvalid;
assign ddr_w_bus.awready = ddr_mstr_bus.awready;
assign ddr_mstr_bus.wid = 0; // not used
assign ddr_mstr_bus.wdata = ddr_w_bus.wdata;
assign ddr_mstr_bus.wstrb = ddr_w_bus.wstrb;
assign ddr_mstr_bus.wlast = ddr_w_bus.wlast;
assign ddr_mstr_bus.wvalid = ddr_w_bus.wvalid;
assign ddr_w_bus.wready = ddr_mstr_bus.wready;
assign ddr_w_bus.bvalid = ddr_mstr_bus.bvalid;
assign ddr_w_bus.bid = ddr_mstr_bus.bid[5:0];
assign ddr_mstr_bus.bready = ddr_w_bus.bready;
//// sh_ocl_bus
// TODO disable everything
assign sh_ocl_bus.awready = 1;
assign sh_ocl_bus.wready = 1;
assign sh_ocl_bus.bvalid = 0;
assign sh_ocl_bus.arready = 1;
assign sh_ocl_bus.rvalid = 0;
endmodule

module pcis_w_to_axis (
    input wire clk,
    input wire rstn,
    axi_bus_W_t.master pcis_write_bus,
    axis_bus_t.slave axis
);

// W processing
localparam PCIS_W_WIDTH = 512;
localparam AXIS_BURST = PCIS_W_WIDTH / axis.DATA_WIDTH;
logic [$clog2(AXIS_BURST)-1:0] burst_idx;

typedef enum {IDLE, TRANS} W_state_t;
W_state_t W_state, W_state_next;
logic [511:0] buf_wdata = 512'h0;
logic buf_wlast = 0;

// W_state transition
always_comb
    case (W_state)
        IDLE:
            if (pcis_write_bus.wvalid && pcis_write_bus.wready)
                W_state_next = TRANS;
            else
                W_state_next = IDLE;
        TRANS:
            if (burst_idx == (AXIS_BURST-1) && (axis.tvalid && axis.tready))
                W_state_next = IDLE;
            else
                W_state_next = TRANS;
        default:
            W_state_next = W_state;
    endcase
always_ff @(posedge clk)
    if (!rstn)
        W_state <= IDLE;
    else
        W_state <= W_state_next;

// W buffer management
always_ff @(posedge clk)
    if ((W_state == IDLE) && (W_state_next == TRANS)) begin
        buf_wdata <= pcis_write_bus.wdata;
        buf_wlast <= pcis_write_bus.wlast;
    end

// axis
always_ff @(posedge clk)
    if (!rstn)
        burst_idx <= 0;
    else if (W_state == TRANS && axis.tvalid && axis.tready)
        burst_idx <= burst_idx + 1;
assign axis.tdata = buf_wdata[burst_idx * axis.DATA_WIDTH +: axis.DATA_WIDTH];
assign axis.tlast = (burst_idx == (AXIS_BURST-1))? buf_wlast : 0;
assign axis.tuser = 0;
assign axis.tvalid = (W_state == TRANS);

// AW and B processing
typedef enum {AW_IDLE, AW_WAIT_W, AW_SENDB} AW_state_t;
AW_state_t AW_state, AW_state_next;
logic [7:0] awlen_remain;
logic [5:0] buf_awid;
// AW_state transition
always_comb
    case (AW_state)
        AW_IDLE:
            if (pcis_write_bus.awvalid && pcis_write_bus.awready)
                AW_state_next = AW_WAIT_W;
            else
                AW_state_next = AW_IDLE;
        AW_WAIT_W:
            if (awlen_remain == 0 && pcis_write_bus.wvalid && pcis_write_bus.wready)
                AW_state_next = AW_SENDB;
            else
                AW_state_next = AW_WAIT_W;
        AW_SENDB:
            if (pcis_write_bus.bvalid && pcis_write_bus.bready)
                AW_state_next = AW_IDLE;
            else
                AW_state_next = AW_SENDB;
        default:
            AW_state_next = AW_state;
    endcase
always_ff @(posedge clk)
    if (!rstn)
        AW_state <= AW_IDLE;
    else
        AW_state <= AW_state_next;
// AW buffer management
always_ff @(posedge clk)
    if ((AW_state == AW_IDLE) && AW_state_next == AW_WAIT_W) begin
        awlen_remain <= pcis_write_bus.awlen;
        buf_awid <= pcis_write_bus.awid;
    end
    else if ((AW_state == AW_WAIT_W) &&
        pcis_write_bus.wvalid && pcis_write_bus.wready)
        awlen_remain <= awlen_remain - 1;
assign pcis_write_bus.awready = (AW_state == AW_IDLE);
assign pcis_write_bus.wready = (W_state == IDLE) && (AW_state == AW_WAIT_W);
assign pcis_write_bus.bid = buf_awid;
assign pcis_write_bus.bvalid = (AW_state == AW_SENDB);
assign pcis_write_bus.bresp = 0; // OK
endmodule

module axis_to_ddr_w (
    input wire clk,
    input wire rstn,
    axis_bus_t.master axis,
    axi_bus_W_t.slave ddr_w_bus
);
// do not care write responses
assign ddr_w_bus.bready = 1;

localparam WDATA_WIDTH = 512;
localparam AXIS_BURST = WDATA_WIDTH / axis.DATA_WIDTH;
logic [$clog2(AXIS_BURST)-1:0] burst_idx;
logic [511:0] ddr_wdata = 0;
logic [63:0] ddr_base_addr = 0;

typedef enum {WAIT_AW, WAIT_W} state_t;
state_t state, state_next;
always_comb
    case (state)
        WAIT_AW:
            if (ddr_w_bus.awvalid && ddr_w_bus.awready)
                state_next = WAIT_W;
            else
                state_next = WAIT_AW;
        WAIT_W:
            if (ddr_w_bus.wvalid && ddr_w_bus.wready)
                state_next = WAIT_AW;
            else
                state_next = WAIT_W;
        default:
            state_next = state;
    endcase
always_ff @(posedge clk)
    if (!rstn)
        state <= WAIT_AW;
    else
        state <= state_next;
//// axis, ignore tkeep, tlast, tuser
assign axis.tready = (state == WAIT_W);
always_ff @(posedge clk)
    if (!rstn) begin
        burst_idx <= 0;
        ddr_wdata <= 0;
    end
    else if (axis.tvalid && axis.tready) begin
        burst_idx <= burst_idx + 1;
        ddr_wdata[burst_idx * axis.DATA_WIDTH +: axis.DATA_WIDTH] <= axis.tdata;
    end
//// ddr_w
// AW
assign ddr_w_bus.awvalid = (state == WAIT_AW);
assign ddr_w_bus.awid = 0;
assign ddr_w_bus.awlen = 0;
assign ddr_w_bus.awsize = 3'b110;
always_ff @(posedge clk)
    if (!rstn)
        ddr_base_addr <= 0;
    else if (ddr_w_bus.awvalid && ddr_w_bus.awready)
        ddr_base_addr <= ddr_base_addr + WDATA_WIDTH / 8;
assign ddr_w_bus.awaddr = ddr_base_addr;
// W
always_ff @(posedge clk)
    if (!rstn)
        ddr_w_bus.wvalid <= 0;
    else if (burst_idx == (AXIS_BURST-1) && axis.tvalid && axis.tready)
        ddr_w_bus.wvalid <= 1;
    else if (state == WAIT_W && state_next == WAIT_AW)
        ddr_w_bus.wvalid <= 0;
assign ddr_w_bus.wstrb = 64'hffffffffffffffff;
assign ddr_w_bus.wlast = 1;
assign ddr_w_bus.wdata = ddr_wdata;
endmodule
