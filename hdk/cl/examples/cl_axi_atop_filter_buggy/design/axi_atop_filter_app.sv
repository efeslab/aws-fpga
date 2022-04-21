typedef struct packed {
    logic [63:0] pcim_base_addr;
    logic [31:0] totalB; // total bytes to echo
    logic startWB; // start write back (from DDR to PCIM)
    logic [31:0] maxPendingAR; // the writeback path, how many on-the-fly ddr
                               // read requests are allowed. min is 1
    logic [31:0] maxPendingAW; // the writeback path, how many on-the-fly pcim
                               // write requests are allowed. min is 1
} app_csrs_t;

module axi_atop_filter_app (
    input wire clk,
    input wire rstn,
    input logic [1:0] sh_cl_cfg_max_payload,
    axi_lite_bus_t.master sh_ocl_bus,
    axi_bus_t.slave ddr_mstr_bus,
    axi_bus_t.slave pcim_mstr_bus,
    output logic irq_req,
    input logic irq_ack
);

axi_bus_t axi_W();
AXI_BUS #(.AXI_ADDR_WIDTH(64), .AXI_DATA_WIDTH(512), .AXI_ID_WIDTH(6), .AXI_USER_WIDTH(1)) axi_atop_in();
AXI_BUS #(.AXI_ADDR_WIDTH(64), .AXI_DATA_WIDTH(512), .AXI_ID_WIDTH(6), .AXI_USER_WIDTH(1)) axi_atop_out();

// R2W state control
logic [31:0] issuedR_Bytes;
logic [31:0] oneR_Bytes;
logic [7:0] burst_len;
logic [31:0] pendingAR;
logic [31:0] pendingAW;
AXI_R2W axi_R2W_inst (
    .clk(clk), .rstn(rstn),
    .burst_len(burst_len),
    .issueR(
        csrs.startWB &&
        (issuedR_Bytes < csrs.totalB) &&
        (pendingAR < csrs.maxPendingAR) &&
        (pendingAW < csrs.maxPendingAW)
    ),
    .axi_R(ddr_mstr_bus),
    .axi_W(axi_W)
);
// maxPendingAR
logic ddr_ar_issued;
logic ddr_ar_finished;
assign ddr_ar_issued = ddr_mstr_bus.arvalid && ddr_mstr_bus.arready;
assign ddr_ar_finished =
    ddr_mstr_bus.rvalid && ddr_mstr_bus.rready && ddr_mstr_bus.rlast;
always_ff @(posedge clk)
    if (!rstn)
        pendingAR <= 0;
    else
        pendingAR <= pendingAR + ddr_ar_issued - ddr_ar_finished;
// maxPendingAW
logic axi_W_aw_issued;
logic axi_W_aw_finished;
assign axi_W_aw_issued = axi_W.awvalid && axi_W.awready;
assign axi_W_aw_finished = axi_W.bvalid && axi_W.bready;
always_ff @(posedge clk)
    if (!rstn)
        pendingAW <= 0;
    else
        pendingAW <= pendingAW + axi_W_aw_issued - axi_W_aw_finished;

localparam WDATA_WIDTH = 512;
always_ff @(posedge clk)
    if (!rstn)
        oneR_Bytes <= 0;
    else
        case (sh_cl_cfg_max_payload)
            2'b00: // 128B
                oneR_Bytes <= 128;
            2'b01: // 256B
                oneR_Bytes <= 256;
            2'b10: // 512B
                oneR_Bytes <= 512;
            2'b11: // reserved
                oneR_Bytes <= 0;
        endcase
always_ff @(posedge clk)
    if (!rstn)
        issuedR_Bytes <= 0;
    else if (ddr_mstr_bus.arvalid && ddr_mstr_bus.arready)
        issuedR_Bytes <= issuedR_Bytes + oneR_Bytes;
always_ff @(posedge clk)
    if (!rstn)
        burst_len <= 0;
    else
        case (sh_cl_cfg_max_payload)
            2'b00: // 128B
                burst_len <= 1;
            2'b01: // 256B
                burst_len <= 3;
            2'b10: // 512B
                burst_len <= 7;
            2'b11: // reserved
                burst_len <= 0;
        endcase
//// aws AXI (axi_W) -> pulp AXI (axi_atop_in)
// AW
assign axi_atop_in.aw_id = axi_W.awid[5:0];
assign axi_atop_in.aw_addr = axi_W.awaddr;
assign axi_atop_in.aw_len = axi_W.awlen;
assign axi_atop_in.aw_size = axi_W.awsize;
assign axi_atop_in.aw_burst = 2'b01; // INCR
assign axi_atop_in.aw_lock = 0; // normal access
assign axi_atop_in.aw_cache = 4'b0011; // 001x non-cacheable 1: system
assign axi_atop_in.aw_prot = 3'b010; // [2] Data access,
                                     // [1] Non-secure access,
                                     // [0] Unpriviledged access
assign axi_atop_in.aw_qos = 4'b0; // not participating in any QOS
assign axi_atop_in.aw_region = 4'b0; // no region I guess?
assign axi_atop_in.aw_atop = 6'b0; // no atomic operation
assign axi_atop_in.aw_user = 0;
assign axi_atop_in.aw_valid = axi_W.awvalid;
assign axi_W.awready = axi_atop_in.aw_ready;
// W
assign axi_atop_in.w_data = axi_W.wdata;
assign axi_atop_in.w_strb = axi_W.wstrb;
assign axi_atop_in.w_last = axi_W.wlast;
assign axi_atop_in.w_user = 0;
assign axi_atop_in.w_valid = axi_W.wvalid;
assign axi_W.wready = axi_atop_in.w_ready;
// B
assign axi_W.bid[5:0] = axi_atop_in.b_id;
assign axi_W.bresp = axi_atop_in.b_resp;
//assign axi_W.buser = ??? // disabled skip
assign axi_W.bvalid = axi_atop_in.b_valid;
assign axi_atop_in.b_ready = axi_W.bready;
// AR
assign axi_atop_in.ar_id = axi_W.arid[5:0];
assign axi_atop_in.ar_addr = axi_W.araddr;
assign axi_atop_in.ar_len = axi_W.arlen;
assign axi_atop_in.ar_size = axi_W.arsize;
assign axi_atop_in.ar_burst = 2'b01; // INCR
assign axi_atop_in.ar_lock = 0; // normal access
assign axi_atop_in.ar_cache = 4'b0011; // 001x non-cacheable 1: system
assign axi_atop_in.ar_prot = 3'b010; // [2] Data access,
                                     // [1] Non-secure access,
                                     // [0] Unpriviledged access
assign axi_atop_in.ar_qos = 4'b0; // not participating in any QOS
assign axi_atop_in.ar_region = 4'b0; // no region I guess?
assign axi_atop_in.ar_user = 0;
assign axi_atop_in.ar_valid = axi_W.arvalid;
assign axi_W.arready = axi_atop_in.ar_ready;
// R
assign axi_W.rid[5:0] = axi_atop_in.r_id;
assign axi_W.rdata = axi_atop_in.r_data;
assign axi_W.rresp = axi_atop_in.r_resp;
assign axi_W.rlast = axi_atop_in.r_last;
//assign axi_W.ruser = ??? // disabled skip
assign axi_W.rvalid = axi_atop_in.r_valid;
assign axi_atop_in.r_ready = axi_W.rready;

axi_atop_filter_intf #(
    .AXI_ID_WIDTH(6),
    .AXI_ADDR_WIDTH(64),
    .AXI_DATA_WIDTH(512),
    .AXI_USER_WIDTH(1),
    .AXI_MAX_WRITE_TXNS(32)
) axi_atop_filter_inst (
    .clk_i(clk),
    .rst_ni(rstn),
    .slv(axi_atop_in),
    .mst(axi_atop_out)
);

app_csrs_t csrs;
axi_atop_ocl_csr ocl_csr_inst(
    .clk(clk), .rstn(rstn),
    .sh_ocl_bus(sh_ocl_bus),
    .csrs(csrs)
);

//// pulp AXI (axi_atop_out) -> aws AXI (pcim_mstr_bus)
// AW
assign pcim_mstr_bus.awid = axi_atop_out.aw_id;
assign pcim_mstr_bus.awaddr = axi_atop_out.aw_addr + csrs.pcim_base_addr;
assign pcim_mstr_bus.awlen = axi_atop_out.aw_len;
assign pcim_mstr_bus.awsize = axi_atop_out.aw_size;
`ifndef TEST_BUGGY_AXI_ATOP_FILTER
assign pcim_mstr_bus.awvalid = axi_atop_out.aw_valid;
assign axi_atop_out.aw_ready = pcim_mstr_bus.awready;
`else
// testing buggy behavior
// aw_ready/valid are passed through only if w_valid is seen after a w_last
logic aw_pass;
assign pcim_mstr_bus.awvalid = aw_pass ? axi_atop_out.aw_valid : 0;
assign axi_atop_out.aw_ready = aw_pass ? pcim_mstr_bus.awready : 0;

always_ff @(posedge clk)
    if (!rstn)
        aw_pass <= 0;
    else if (pcim_mstr_bus.wvalid && pcim_mstr_bus.wready && pcim_mstr_bus.wlast)
        aw_pass <= 0;
    else if (pcim_mstr_bus.wvalid && pcim_mstr_bus.wready)
        aw_pass <= 1;
`endif
// W
assign pcim_mstr_bus.wid = 0;
assign pcim_mstr_bus.wdata = axi_atop_out.w_data;
assign pcim_mstr_bus.wstrb = axi_atop_out.w_strb;
assign pcim_mstr_bus.wlast = axi_atop_out.w_last;
assign pcim_mstr_bus.wvalid = axi_atop_out.w_valid;
assign axi_atop_out.w_ready = pcim_mstr_bus.wready;
// B
assign axi_atop_out.b_id = pcim_mstr_bus.bid;
assign axi_atop_out.b_resp = pcim_mstr_bus.bresp;
assign axi_atop_out.b_user = 0;
assign axi_atop_out.b_valid = pcim_mstr_bus.bvalid;
assign pcim_mstr_bus.bready = axi_atop_out.b_ready;
// AR
assign pcim_mstr_bus.arid = axi_atop_out.ar_id;
assign pcim_mstr_bus.araddr = axi_atop_out.ar_addr + csrs.pcim_base_addr;
assign pcim_mstr_bus.arlen = axi_atop_out.ar_len;
assign pcim_mstr_bus.arsize = axi_atop_out.ar_size;
assign pcim_mstr_bus.arvalid = axi_atop_out.ar_valid;
assign axi_atop_out.ar_ready = pcim_mstr_bus.arready;
// R
assign axi_atop_out.r_id = pcim_mstr_bus.rid;
assign axi_atop_out.r_data = pcim_mstr_bus.rdata;
assign axi_atop_out.r_resp = pcim_mstr_bus.rresp;
assign axi_atop_out.r_last = pcim_mstr_bus.rlast;
assign axi_atop_out.r_user = 0;
assign axi_atop_out.r_valid = pcim_mstr_bus.rvalid;
assign pcim_mstr_bus.rready = axi_atop_out.r_ready;

logic [31:0] completedW_Bytes;
always_ff @(posedge clk)
    if (!rstn)
        completedW_Bytes <= 0;
    else if (pcim_mstr_bus.bvalid && pcim_mstr_bus.bready)
        completedW_Bytes <= completedW_Bytes + oneR_Bytes;

// manage interrupt
logic irq_requested = 0, irq_requested_past = 0;
always_ff @(posedge clk)
    if (!rstn)
        irq_requested <= 0;
    else if (completedW_Bytes == csrs.totalB && csrs.startWB)
        irq_requested <= 1;
always_ff @(posedge clk)
    irq_requested_past <= irq_requested;
assign irq_req = !irq_requested_past && irq_requested;

endmodule

module axi_atop_ocl_csr (
    input wire clk,
    input wire rstn,
    axi_lite_bus_t.master sh_ocl_bus,
    output app_csrs_t csrs
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
typedef enum {W_IDLE, W_WAIT_W, W_RESP} W_state_t;
W_state_t Wstate, Wstate_next;
logic [31:0] buf_awaddr;
always_comb
    case (Wstate)
        W_IDLE:
            if (sh_ocl_bus.awvalid && sh_ocl_bus.awready)
                Wstate_next = W_WAIT_W;
            else
                Wstate_next = W_IDLE;
        W_WAIT_W:
            if (sh_ocl_bus.wvalid && sh_ocl_bus.wready)
                Wstate_next = W_RESP;
            else
                Wstate_next = W_WAIT_W;
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
// csr address parsing
typedef enum {
    PCIM_BASE_ADDR_LO = 0,
    PCIM_BASE_ADDR_HI,
    TOTAL_BYTES,
    START_WB,
    MAX_PENDING_AR,
    MAX_PENDING_AW,
    TOTAL_CSR_NUM
} csr_t;
`define CSR_ADDR(idx) (idx << 2)
always_ff @(posedge clk)
    if (!rstn)
        buf_awaddr <= 0;
    else if (sh_ocl_bus.awvalid && sh_ocl_bus.awready) begin
        buf_awaddr <= sh_ocl_bus.awaddr;
    end
always_ff @(posedge clk)
    if (!rstn) begin
        csrs.pcim_base_addr <= 0;
        csrs.startWB <= 0;
        csrs.totalB <= 0;
        csrs.maxPendingAR <= 1;
        csrs.maxPendingAW <= 1;
    end
    else if (sh_ocl_bus.wvalid && sh_ocl_bus.wready)
        case (buf_awaddr)
            `CSR_ADDR(PCIM_BASE_ADDR_LO):
                csrs.pcim_base_addr[0 +: 32] <= sh_ocl_bus.wdata;
            `CSR_ADDR(PCIM_BASE_ADDR_HI):
                csrs.pcim_base_addr[32 +: 32] <= sh_ocl_bus.wdata;
            `CSR_ADDR(TOTAL_BYTES):
                csrs.totalB <= sh_ocl_bus.wdata;
            `CSR_ADDR(START_WB):
                csrs.startWB <= sh_ocl_bus.wdata[0];
            `CSR_ADDR(MAX_PENDING_AR):
                csrs.maxPendingAR <= sh_ocl_bus.wdata;
            `CSR_ADDR(MAX_PENDING_AW):
                csrs.maxPendingAW <= sh_ocl_bus.wdata;
        endcase
endmodule

module AXI_R2W (
    input wire clk,
    input wire rstn,
    input logic [7:0] burst_len,
    // if asserted, will issue R and convert its responses to W
    // Note that deasserting R will not abort on-going transactions
    input logic issueR,
    // the axi bus to issue read commands
    axi_bus_t.slave axi_R,
    // the axi bus to issue write commands
    axi_bus_t.slave axi_W
);
localparam WDATA_WIDTH = 512;
// next address to issue R or W
logic [63:0] addr;
typedef enum {
    IDLE, // wait for issueR
    ISSUE_AR_AW, // issue both AW and AR
    ISSUE_AR, // AW finished earlier, continue issuing AR
    ISSUE_AW  // AR finished earlier, continue issuing AW
} state_t;
// axi_R.R will be directly connected to axi_W.W
state_t state, state_next;
always_comb begin
    state_next = state;
    case (state)
        IDLE:
            if (issueR)
                state_next = ISSUE_AR_AW;
        ISSUE_AR_AW:
            // implies axi_R.arvalid and axi_W.awvalid
            if (axi_R.arready && axi_W.awready)
                state_next = IDLE;
            else if (!axi_R.arready && axi_W.awready)
                state_next = ISSUE_AR;
            else if (axi_R.arready && !axi_W.awready)
                state_next = ISSUE_AW;
        ISSUE_AR:
            // implies axi_R.arvalid
            if (axi_R.arready)
                state_next = IDLE;
        ISSUE_AW:
            // implies axi_W.awvalid
            if (axi_W.awready)
                state_next = IDLE;
    endcase
end
always_ff @(posedge clk)
    if (!rstn) state <= IDLE;
    else state <= state_next;
// manage axi_R.AR
assign axi_R.arid = 0;
assign axi_R.araddr = addr;
assign axi_R.arlen = burst_len;
assign axi_R.arsize = 3'b110; // 64B
assign axi_R.arvalid = (state == ISSUE_AR_AW) || (state == ISSUE_AR);
// manage axi_W.AW
assign axi_W.awid = 0;
assign axi_W.awaddr = addr;
assign axi_W.awlen = burst_len;
assign axi_W.awsize = 3'b110; // 64B
assign axi_W.awvalid = (state == ISSUE_AR_AW) || (state == ISSUE_AW);
// manage addr
always_ff @(posedge clk)
    if (!rstn) addr <= 0;
    else if (state != IDLE && state_next == IDLE)
        addr <= addr + (burst_len + 1) * WDATA_WIDTH / 8;
// connect axi_R.R to axi_W.W
assign axi_W.wid = 0;
assign axi_W.wdata = axi_R.rdata;
assign axi_W.wstrb = 64'hffffffffffffffff;
assign axi_W.wlast = axi_R.rlast;
assign axi_W.wvalid = axi_R.rvalid;
assign axi_R.rready = axi_W.wready;
// ignore axi_W.B
assign axi_W.bready = 1;
//// MISC
// disable axi_R write
assign axi_R.awvalid = 0;
assign axi_R.wvalid = 0;
assign axi_R.bready = 1;
// disable axi_W read
assign axi_W.arvalid = 0;
assign axi_W.rready = 1;
endmodule
