typedef struct packed {
    logic [31:0] ddr_wait_cyc;
    logic [63:0] writeback_base_addr;
    logic writeback_base_addr_update;
    logic allow_ddr_w;
    logic app_done;
} axis_app_csrs_t;

module axis_app #(
    parameter ADDR_WIDTH,
    parameter DATA_WIDTH
) (
    input wire clk,
    input wire rstn,
    axi_bus_W_t.master pcis_write_bus,
    axi_lite_bus_t.master sh_ocl_bus,
    axi_bus_t.slave ddr_mstr_bus,
    output logic irq_req,
    input logic irq_ack
);

//// pcis write to axis
axis_bus_t #(.DATA_WIDTH(DATA_WIDTH), .USER_WIDTH(1)) axis_pcis();
axis_bus_t #(.DATA_WIDTH(DATA_WIDTH), .USER_WIDTH(1)) axis_ocl();
axis_bus_t #(.DATA_WIDTH(DATA_WIDTH), .USER_WIDTH(1)) axis_fifo_in();
axis_bus_t #(.DATA_WIDTH(DATA_WIDTH), .USER_WIDTH(1)) axis_fifo_out();

// counter unit is 32bit, one 512-bit axi transaction is 16 unit
logic [31:0] pcis_w_cnt;
logic [31:0] ocl_w_cnt;
logic [31:0] ddr_w_cnt;

pcis_w_to_axis pcis2axis_inst(
    .clk(clk), .rstn(rstn),
    .pcis_write_bus(pcis_write_bus),
    .axis(axis_pcis)
);
axis_app_csrs_t csrs;
ocl_csr ocl_csr_inst(
    .clk(clk), .rstn(rstn),
    .sh_ocl_bus(sh_ocl_bus),
    .axis(axis_ocl),
    .ddr_wait_cyc(/*not used YET TODO*/),
    .ocl_w_cnt(ocl_w_cnt),
    .csrs(csrs)
);
axis_mstr_arbiter2 axis_arb_inst(
    .clk(clk), .rstn(rstn),
    .axisA(axis_ocl), .axisB(axis_pcis), .axisO(axis_fifo_in)
);

logic status_empty;
`ifdef LOSSCHECK
axis_fifo_wrapper_losscheck #(
    .ASSERT_ON(1)
`else
axis_fifo_wrapper #(
    .ADDR_WIDTH(ADDR_WIDTH),
    .DATA_WIDTH(DATA_WIDTH),
    .USER_WIDTH(1)
`endif
) axis_fifo_inst (
    .clk(clk), .rst(!rstn),
    .s_axis_tdata(axis_fifo_in.tdata),
    .s_axis_tkeep(axis_fifo_in.tkeep),
    .s_axis_tvalid(axis_fifo_in.tvalid),
    .s_axis_tready(axis_fifo_in.tready),
    .s_axis_tlast(axis_fifo_in.tlast),
    .s_axis_tuser(axis_fifo_in.tuser),
    .m_axis_tdata(axis_fifo_out.tdata),
    .m_axis_tkeep(axis_fifo_out.tkeep),
    .m_axis_tvalid(axis_fifo_out.tvalid),
    .m_axis_tready(axis_fifo_out.tready),
    .m_axis_tlast(axis_fifo_out.tlast),
    .m_axis_tuser(axis_fifo_out.tuser),
    .status_overflow(),
    .status_bad_frame(),
    .status_good_frame(),
    .status_empty(status_empty)
);
logic flush;
assign flush = csrs.app_done &&
                 !axis_pcis.tvalid &&
                 !axis_ocl.tvalid &&
                 status_empty &&
                 !axis_fifo_out.tvalid;
axi_bus_W_t ddr_w_bus();
axis_to_ddr_w #(DATA_WIDTH) axis2ddrw_inst(
    .clk(clk), .rstn(rstn),
    .axis(axis_fifo_out),
    .ddr_w_bus(ddr_w_bus),
    .csrs(csrs),
    .flush(flush)
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
//// handle done logic
// maintain counter
always_ff @(posedge clk)
    if (!rstn) begin
        pcis_w_cnt <= 0;
        ddr_w_cnt <= 0;
    end
    else begin
        if (pcis_write_bus.wvalid && pcis_write_bus.wready)
            pcis_w_cnt <= pcis_w_cnt + 16;
        if (ddr_w_bus.wvalid && ddr_w_bus.wready)
            ddr_w_cnt <= ddr_w_cnt + 16;
    end
// set interrupt
logic irq_requested = 0, irq_requested_past = 0;
always_ff @(posedge clk)
    if (!rstn)
        irq_requested <= 0;
    else if (flush && !ddr_w_bus.awvalid && !ddr_w_bus.wvalid)
        irq_requested <= 1;
always_ff @(posedge clk)
    irq_requested_past <= irq_requested;
assign irq_req = !irq_requested_past && irq_requested;
/////// debug related
logic [31:0] axis_fifo_out_cnt;
logic [31:0] axis_fifo_in_cnt;
always_ff @(posedge clk)
    if (!rstn) begin
        axis_fifo_in_cnt <= 0;
        axis_fifo_out_cnt <= 0;
    end else begin
        if (axis_fifo_in.tvalid && axis_fifo_in.tready)
            axis_fifo_in_cnt <= axis_fifo_in_cnt + 1;
        if (axis_fifo_out.tvalid && axis_fifo_out.tready)
            axis_fifo_out_cnt <= axis_fifo_out_cnt + 1;
    end
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
    end

// axis
always_ff @(posedge clk)
    if (!rstn)
        burst_idx <= 0;
    else if (W_state == TRANS && axis.tvalid && axis.tready)
        burst_idx <= burst_idx + 1;
assign axis.tdata = buf_wdata[burst_idx * axis.DATA_WIDTH +: axis.DATA_WIDTH];
assign axis.tkeep = {axis.KEEP_WIDTH{1'b1}};
assign axis.tlast = (burst_idx == (AXIS_BURST-1))? 1 : 0;
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

module axis_to_ddr_w #(
    parameter AXIS_DATA_WIDTH
) (
    input wire clk,
    input wire rstn,
    axis_bus_t.master axis,
    axi_bus_W_t.slave ddr_w_bus,
    input axis_app_csrs_t csrs,
    input logic flush
);
// do not care write responses
assign ddr_w_bus.bready = 1;

if (AXIS_DATA_WIDTH != axis.DATA_WIDTH)
    $error("AXIS_DATA_WIDTH mismatches, param %d, intf %d",
        AXIS_DATA_WIDTH, axis.DATA_WIDTH);
localparam WDATA_WIDTH = 512;
localparam AXIS_BURST = WDATA_WIDTH / AXIS_DATA_WIDTH;
logic [$clog2(AXIS_BURST)-1:0] burst_idx;
logic [511:0] ddr_wdata = 0;
logic [63:0] ddr_base_addr = 0;

//
// IDLE --allow_ddr_w-->WAIT_AW----->WAIT_W
//  ⌃                                  |
//  |                                  |
//  *-------flush/!allow_ddr_w---------*
//
typedef enum {WAIT_AW, WAIT_W, IDLE} state_t;
state_t state, state_next;
logic flush_handled;
always_comb
    case (state)
        WAIT_AW:
            if (ddr_w_bus.awvalid && ddr_w_bus.awready)
                state_next = WAIT_W;
            else
                state_next = WAIT_AW;
        WAIT_W:
            if (ddr_w_bus.wvalid && ddr_w_bus.wready)
                if ((flush && flush_handled) || !csrs.allow_ddr_w)
                    state_next = IDLE;
                else
                    state_next = WAIT_AW;
            else
                state_next = WAIT_W;
        IDLE:
            if (flush)
                state_next = IDLE;
            else if (csrs.allow_ddr_w)
                state_next = WAIT_AW;
            else
                state_next = IDLE;
        default:
            state_next = state;
    endcase
always_ff @(posedge clk)
    if (!rstn)
        state <= IDLE;
    else
        state <= state_next;

logic tready_prepare;
logic [15:0] tready_prepare_counter;
assign tready_prepare = (state == WAIT_W);
assign axis.tready = tready_prepare && tready_prepare_counter == 0;

always_ff @(posedge clk) begin
    if (!rstn) begin
        tready_prepare_counter <= 0;
    end else begin
        if (axis.tready && axis.tvalid) begin
            tready_prepare_counter <= csrs.ddr_wait_cyc;
        end else if (tready_prepare && axis.tvalid) begin
            tready_prepare_counter <= tready_prepare_counter - 1;
        end else begin
            tready_prepare_counter <= csrs.ddr_wait_cyc;
        end
    end
end

//// axis, ignore tkeep, tlast, tuser
//assign axis.tready = (state == WAIT_W);
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
    else if (csrs.writeback_base_addr_update)
        ddr_base_addr <= csrs.writeback_base_addr;
    else if (ddr_w_bus.awvalid && ddr_w_bus.awready)
        ddr_base_addr <= ddr_base_addr + WDATA_WIDTH / 8;
assign ddr_w_bus.awaddr = ddr_base_addr;

// W
always_ff @(posedge clk)
    if (!rstn) begin
        ddr_w_bus.wvalid <= 0;
        flush_handled <= 0;
    end
    else if (burst_idx == (AXIS_BURST-1) && axis.tvalid && axis.tready)
        ddr_w_bus.wvalid <= 1;
    else if (flush && !flush_handled) begin
        ddr_w_bus.wvalid <= (burst_idx != 0);
        flush_handled <= 1;
    end
    else if (state == WAIT_W && state_next != WAIT_W)
        ddr_w_bus.wvalid <= 0;
assign ddr_w_bus.wstrb = 64'hffffffffffffffff;
assign ddr_w_bus.wlast = 1;
assign ddr_w_bus.wdata = ddr_wdata;
endmodule

module ocl_csr (
    input wire clk,
    input wire rstn,
    axi_lite_bus_t.master sh_ocl_bus,
    axis_bus_t.slave axis,
    output logic [31:0] ddr_wait_cyc,
    output logic [31:0] ocl_w_cnt,
    output axis_app_csrs_t csrs
);
//// ocl read always return zero
typedef enum {R_IDLE, R_RESP} R_state_t;
R_state_t Rstate, Rstate_next;
always_comb
    case (Rstate)
        R_IDLE:
            if (sh_ocl_bus.arvalid && sh_ocl_bus.arready)
                Rstate_next = R_RESP;
            else
                Rstate_next = R_IDLE;
        R_RESP:
            if (sh_ocl_bus.rvalid && sh_ocl_bus.rready)
                Rstate_next = R_IDLE;
            else
                Rstate_next = R_RESP;
        default:
            Rstate_next = Rstate;
    endcase
always_ff @(posedge clk)
    if (!rstn)
        Rstate <= R_IDLE;
    else
        Rstate <= Rstate_next;
assign sh_ocl_bus.arready = (Rstate == R_IDLE);
assign sh_ocl_bus.rvalid = (Rstate == R_RESP);
assign sh_ocl_bus.rdata = 0;
assign sh_ocl_bus.rresp = 0; // OK

//// ocl write
typedef enum {W_IDLE, W_WAIT_W, W_AXIS, W_RESP} W_state_t;
W_state_t Wstate, Wstate_next;
logic awaddr_need_axis;
logic [31:0] buf_awaddr;
logic [31:0] buf_wdata;
always_comb
    case (Wstate)
        W_IDLE:
            if (sh_ocl_bus.awvalid && sh_ocl_bus.awready)
                Wstate_next = W_WAIT_W;
            else
                Wstate_next = W_IDLE;
        W_WAIT_W:
            if (sh_ocl_bus.wvalid && sh_ocl_bus.wready)
                if (awaddr_need_axis)
                    Wstate_next = W_AXIS;
                else
                    Wstate_next = W_RESP;
            else
                Wstate_next = W_WAIT_W;
        W_AXIS:
            if (axis.tvalid && axis.tready)
                Wstate_next = W_RESP;
            else
                Wstate_next = W_AXIS;
        W_RESP:
            if (sh_ocl_bus.bvalid && sh_ocl_bus.bready)
                Wstate_next = W_IDLE;
            else
                Wstate_next = W_RESP;
        default:
            Wstate_next = Wstate;
    endcase
always_ff @(posedge clk)
    if (!rstn)
        Wstate <= W_IDLE;
    else
        Wstate <= Wstate_next;
assign sh_ocl_bus.awready = (Wstate == W_IDLE);
assign sh_ocl_bus.wready = (Wstate == W_WAIT_W);
assign sh_ocl_bus.bvalid = (Wstate == W_RESP);
assign sh_ocl_bus.bresp = 0; // OK
assign axis.tdata = buf_wdata;
assign axis.tkeep = {axis.KEEP_WIDTH{1'b1}};
assign axis.tlast = 1;
assign axis.tuser = 0;
assign axis.tvalid = (Wstate == W_AXIS);
// csr address parsing
typedef enum {
    DDR_WAIT_CYC = 0,
    DONE,
    INJECT,
    ALLOW_DDR_W,
    ALLOW_DDR_W_INTVL, // 0 is disable
    WRITEBACK_BASE_ADDR_LO,
    WRITEBACK_BASE_ADDR_HI,
    TOTAL_CSR_NUM
} csr_t;
`define CSR_ADDR(idx) (idx << 2)
always_ff @(posedge clk)
    if (!rstn)
        buf_awaddr <= 0;
    else if (sh_ocl_bus.awvalid && sh_ocl_bus.awready) begin
        buf_awaddr <= sh_ocl_bus.awaddr;
        awaddr_need_axis <= (sh_ocl_bus.awaddr == `CSR_ADDR(INJECT));
    end
logic [31:0] allow_ddr_w_intvl_csr;
logic [31:0] allow_ddr_w_intvl_clkcnt = 0;
always_ff @(posedge clk)
    if (!rstn) begin
        csrs.ddr_wait_cyc <= 0;
        csrs.app_done <= 0;
        csrs.allow_ddr_w <= 0;
        ocl_w_cnt <= 0;
        buf_wdata <= 0;
    end
    else if (sh_ocl_bus.wvalid && sh_ocl_bus.wready)
        case (buf_awaddr)
            `CSR_ADDR(DDR_WAIT_CYC):
                csrs.ddr_wait_cyc <= sh_ocl_bus.wdata;
            `CSR_ADDR(DONE):
                csrs.app_done <= 1;
            `CSR_ADDR(ALLOW_DDR_W):
                csrs.allow_ddr_w <= sh_ocl_bus.wdata[0];
            `CSR_ADDR(ALLOW_DDR_W_INTVL):
                allow_ddr_w_intvl_csr <= sh_ocl_bus.wdata;
            `CSR_ADDR(INJECT): begin
                ocl_w_cnt <= ocl_w_cnt + 1;
                buf_wdata <= sh_ocl_bus.wdata;
             end
            `CSR_ADDR(WRITEBACK_BASE_ADDR_LO):
                csrs.writeback_base_addr[31:0] <= sh_ocl_bus.wdata;
            `CSR_ADDR(WRITEBACK_BASE_ADDR_HI):
                csrs.writeback_base_addr[63:32] <= sh_ocl_bus.wdata;
        endcase
    else if ((allow_ddr_w_intvl_csr != 0) &&
             (allow_ddr_w_intvl_csr == allow_ddr_w_intvl_clkcnt))
        // flip csrs_allow_ddr_w
        csrs.allow_ddr_w <= !csrs.allow_ddr_w;

always_ff @(posedge clk)
    if (!rstn)
        csrs.writeback_base_addr_update <= 0;
    else if (sh_ocl_bus.wvalid && sh_ocl_bus.wready && buf_awaddr == `CSR_ADDR(WRITEBACK_BASE_ADDR_HI))
        csrs.writeback_base_addr_update <= 1;
    else
        csrs.writeback_base_addr_update <= 0;

always_ff @(posedge clk)
    if (!rstn)
        allow_ddr_w_intvl_clkcnt <= 0;
    else if (allow_ddr_w_intvl_clkcnt >= allow_ddr_w_intvl_csr)
        allow_ddr_w_intvl_clkcnt <= 0;
    else
        allow_ddr_w_intvl_clkcnt <= allow_ddr_w_intvl_clkcnt + 1;
endmodule

// arbiter two axis with respect to their `tlast`
// axisA has a higher priority than axisB
module axis_mstr_arbiter2 (
    input wire clk,
    input wire rstn,
    axis_bus_t.master axisA,
    axis_bus_t.master axisB,
    axis_bus_t.slave axisO
);
if (axisA.DATA_WIDTH != axisB.DATA_WIDTH ||
    axisA.DATA_WIDTH != axisO.DATA_WIDTH)
    $error("DATA_WIDTH mismtaches, axisA %d, axisB %d, axisO %d",
        axisA.DATA_WIDTH, axisB.DATA_WIDTH, axisO.DATA_WIDTH);
if (axisA.USER_WIDTH != axisB.USER_WIDTH ||
    axisA.USER_WIDTH != axisO.USER_WIDTH)
    $error("USER_WIDTH mismatches, axisA %d, axisB %d, axisO %d",
        axisA.USER_WIDTH, axisB.USER_WIDTH, axisO.USER_WIDTH);
typedef enum {IDLE, FWDA, FWDB} state_t;
// IDLE -> tvalid && tready && !tlast -> FWDA/FWDB
//      -> else -> IDLE
state_t state, state_next;
// fowarding state transition
always_comb
    case (state)
        IDLE:
            if (axisO.tvalid && axisO.tready && !axisO.tlast)
                if (axisA.tvalid)
                    state_next = FWDA;
                else
                    state_next = FWDB;
            else
                state_next = IDLE;
        FWDA:
            if (axisO.tvalid && axisO.tready && axisO.tlast)
                state_next = IDLE;
            else
                state_next = FWDA;
        FWDB:
            if (axisO.tvalid && axisO.tready && axisO.tlast)
                state_next = IDLE;
            else
                state_next = FWDB;
        default:
            state_next = state;
    endcase
always_ff @(posedge clk)
    if (!rstn)
        state <= IDLE;
    else
        state <= state_next;
`define ASSIGN_AXIS(from, to)                       \
    to.tvalid = from.tvalid;                        \
    to.tdata = from.tdata;                          \
    to.tkeep = from.tkeep;                          \
    to.tlast = from.tlast;                          \
    to.tuser = from.tuser;                          \
    from.tready = to.tready
always_comb
    case (state)
        IDLE:
            if (axisA.tvalid) begin
                `ASSIGN_AXIS(axisA, axisO);
                axisB.tready = 0;
            end else begin
                `ASSIGN_AXIS(axisB, axisO);
                axisA.tready = 0;
            end
        FWDA: begin
            `ASSIGN_AXIS(axisA, axisO);
            axisB.tready = 0;
        end
        FWDB: begin
            `ASSIGN_AXIS(axisB, axisO);
            axisA.tready = 0;
        end
        default: begin
            `ASSIGN_AXIS(axisA, axisO);
            axisB.tready = 0;
        end
    endcase
endmodule
