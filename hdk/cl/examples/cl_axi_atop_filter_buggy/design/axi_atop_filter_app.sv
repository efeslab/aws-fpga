typedef struct packed {
    logic [63:0] pcim_base_addr;
    logic [31:0] totalB; // total bytes to echo
    logic startWB; // start write back (from DDR to PCIM)
    logic apply_bugfix; // determine which version axi_top_filter code to use
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

// R2W state control
logic [31:0] issuedR_Bytes;
logic [31:0] oneR_Bytes;
logic [7:0] burst_len;
AXI_R2W axi_R2W_inst (
    .clk(clk), .rstn(rstn),
    .burst_len(burst_len),
    .issueR(csrs.startWB && issuedR_Bytes < csrs.totalB),
    .W_base_addr(csrs.pcim_base_addr),
    .axi_R(ddr_mstr_bus),
    .axi_W(axi_W)
);

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
axi_bus_t axi_W_buggy();
axi_bus_t axi_W_fixed();
aws_axi_slv_sel axi_W_sel_inst (
    .sel(csrs.apply_bugfix),
    .inAM(axi_W_buggy),
    .inBM(axi_W_fixed),
    .outS(axi_W)
);
AXI_BUS #(.AXI_ADDR_WIDTH(64), .AXI_DATA_WIDTH(512), .AXI_ID_WIDTH(6), .AXI_USER_WIDTH(1)) axi_atop_in_buggy();
AXI_BUS #(.AXI_ADDR_WIDTH(64), .AXI_DATA_WIDTH(512), .AXI_ID_WIDTH(6), .AXI_USER_WIDTH(1)) axi_atop_in_fixed();
AXI_BUS #(.AXI_ADDR_WIDTH(64), .AXI_DATA_WIDTH(512), .AXI_ID_WIDTH(6), .AXI_USER_WIDTH(1)) axi_atop_out_buggy();
AXI_BUS #(.AXI_ADDR_WIDTH(64), .AXI_DATA_WIDTH(512), .AXI_ID_WIDTH(6), .AXI_USER_WIDTH(1)) axi_atop_out_fixed();

aws_AXI_to_pulp_AXI_mstr atop_in_buggy_inst (
    .aws_axi_M(axi_W_buggy),
    .pulp_axi_M(axi_atop_in_buggy)
);
aws_AXI_to_pulp_AXI_mstr atop_in_fixed_inst (
    .aws_axi_M(axi_W_fixed),
    .pulp_axi_M(axi_atop_in_fixed)
);

axi_atop_filter_intf #(
    .AXI_ID_WIDTH(6),
    .AXI_ADDR_WIDTH(64),
    .AXI_DATA_WIDTH(512),
    .AXI_USER_WIDTH(1),
    .AXI_MAX_WRITE_TXNS(32)
) axi_atop_filter_buggy_inst (
    .clk_i(clk),
    .rst_ni(rstn),
    .slv(axi_atop_in_buggy),
    .mst(axi_atop_out_buggy)
);

axi_atop_filter_fixed_intf #(
    .AXI_ID_WIDTH(6),
    .AXI_ADDR_WIDTH(64),
    .AXI_DATA_WIDTH(512),
    .AXI_USER_WIDTH(1),
    .AXI_MAX_WRITE_TXNS(32)
) axi_atop_filter_fixed_inst (
    .clk_i(clk),
    .rst_ni(rstn),
    .slv(axi_atop_in_fixed),
    .mst(axi_atop_out_fixed)
);

axi_bus_t pcim_out_buggy();
axi_bus_t pcim_out_fixed();
pulp_AXI_to_aws_AXI_mstr atop_out2pcim_buggy_inst (
    .pulp_axi_M(axi_atop_out_buggy),
    .aws_axi_M(pcim_out_buggy)
);
pulp_AXI_to_aws_AXI_mstr atop_out2pcim_fixed_inst (
    .pulp_axi_M(axi_atop_out_fixed),
    .aws_axi_M(pcim_out_fixed)
);
aws_axi_mstr_sel pcim_mstr_sel_inst (
    .sel(csrs.apply_bugfix),
    .inAS(pcim_out_buggy),
    .inBS(pcim_out_fixed),
    .outM(pcim_mstr_bus)
);

app_csrs_t csrs;
axi_atop_ocl_csr ocl_csr_inst(
    .clk(clk), .rstn(rstn),
    .sh_ocl_bus(sh_ocl_bus),
    .csrs(csrs)
);

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
    APPLY_BUGFIX,
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
        csrs.totalB <= 0;
        csrs.startWB <= 0;
        csrs.apply_bugfix <= 0;
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
                csrs.startWB <= 1;
            `CSR_ADDR(APPLY_BUGFIX):
                // disallow updating apply_bugfix when writeback has started
                csrs.apply_bugfix <=
                    csrs.startWB ?  csrs.apply_bugfix : sh_ocl_bus.wdata[0];
        endcase
endmodule

module AXI_R2W (
    input wire clk,
    input wire rstn,
    input logic [7:0] burst_len,
    // if asserted, will issue R and convert its responses to W
    // Note that deasserting R will not abort on-going transactions
    input logic issueR,
    input logic [63:0] W_base_addr,
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
    else state <= state_next; // manage axi_R.AR
assign axi_R.arid = 0;
assign axi_R.araddr = addr;
assign axi_R.arlen = burst_len;
assign axi_R.arsize = 3'b110; // 64B
assign axi_R.arvalid = (state == ISSUE_AR_AW) || (state == ISSUE_AR);
// manage axi_W.AW
assign axi_W.awid = 0;
assign axi_W.awaddr = addr + W_base_addr;
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

module aws_AXI_to_pulp_AXI_mstr (
    axi_bus_t.master aws_axi_M,
    AXI_BUS.Master pulp_axi_M
);
assign pulp_axi_M.aw_id = aws_axi_M.awid[5:0];
assign pulp_axi_M.aw_addr = aws_axi_M.awaddr;
assign pulp_axi_M.aw_len = aws_axi_M.awlen;
assign pulp_axi_M.aw_size = aws_axi_M.awsize;
assign pulp_axi_M.aw_burst = 2'b01; // INCR
assign pulp_axi_M.aw_lock = 0; // normal access
assign pulp_axi_M.aw_cache = 4'b0011; // 001x non-cacheable 1: system
assign pulp_axi_M.aw_prot = 3'b010; // [2] Data access,
                                     // [1] Non-secure access,
                                     // [0] Unpriviledged access
assign pulp_axi_M.aw_qos = 4'b0; // not participating in any QOS
assign pulp_axi_M.aw_region = 4'b0; // no region I guess?
assign pulp_axi_M.aw_atop = 6'b0; // no atomic operation
assign pulp_axi_M.aw_user = 0;
assign pulp_axi_M.aw_valid = aws_axi_M.awvalid;
assign aws_axi_M.awready = pulp_axi_M.aw_ready;
// W
assign pulp_axi_M.w_data = aws_axi_M.wdata;
assign pulp_axi_M.w_strb = aws_axi_M.wstrb;
assign pulp_axi_M.w_last = aws_axi_M.wlast;
assign pulp_axi_M.w_user = 0;
assign pulp_axi_M.w_valid = aws_axi_M.wvalid;
assign aws_axi_M.wready = pulp_axi_M.w_ready;
// B
assign aws_axi_M.bid[5:0] = pulp_axi_M.b_id;
assign aws_axi_M.bresp = pulp_axi_M.b_resp;
//assign aws_axi_M.buser = ??? // disabled skip
assign aws_axi_M.bvalid = pulp_axi_M.b_valid;
assign pulp_axi_M.b_ready = aws_axi_M.bready;
// AR
assign pulp_axi_M.ar_id = aws_axi_M.arid[5:0];
assign pulp_axi_M.ar_addr = aws_axi_M.araddr;
assign pulp_axi_M.ar_len = aws_axi_M.arlen;
assign pulp_axi_M.ar_size = aws_axi_M.arsize;
assign pulp_axi_M.ar_burst = 2'b01; // INCR
assign pulp_axi_M.ar_lock = 0; // normal access
assign pulp_axi_M.ar_cache = 4'b0011; // 001x non-cacheable 1: system
assign pulp_axi_M.ar_prot = 3'b010; // [2] Data access,
                                     // [1] Non-secure access,
                                     // [0] Unpriviledged access
assign pulp_axi_M.ar_qos = 4'b0; // not participating in any QOS
assign pulp_axi_M.ar_region = 4'b0; // no region I guess?
assign pulp_axi_M.ar_user = 0;
assign pulp_axi_M.ar_valid = aws_axi_M.arvalid;
assign aws_axi_M.arready = pulp_axi_M.ar_ready;
// R
assign aws_axi_M.rid[5:0] = pulp_axi_M.r_id;
assign aws_axi_M.rdata = pulp_axi_M.r_data;
assign aws_axi_M.rresp = pulp_axi_M.r_resp;
assign aws_axi_M.rlast = pulp_axi_M.r_last;
//assign aws_axi_M.ruser = ??? // disabled skip
assign aws_axi_M.rvalid = pulp_axi_M.r_valid;
assign pulp_axi_M.r_ready = aws_axi_M.rready;
endmodule

module pulp_AXI_to_aws_AXI_mstr (
    AXI_BUS.Slave pulp_axi_M,
    axi_bus_t.slave aws_axi_M
);
// AW
assign aws_axi_M.awid = pulp_axi_M.aw_id;
assign aws_axi_M.awaddr = pulp_axi_M.aw_addr;
assign aws_axi_M.awlen = pulp_axi_M.aw_len;
assign aws_axi_M.awsize = pulp_axi_M.aw_size;
assign aws_axi_M.awvalid = pulp_axi_M.aw_valid;
assign pulp_axi_M.aw_ready = aws_axi_M.awready;
// W
assign aws_axi_M.wid = 0;
assign aws_axi_M.wdata = pulp_axi_M.w_data;
assign aws_axi_M.wstrb = pulp_axi_M.w_strb;
assign aws_axi_M.wlast = pulp_axi_M.w_last;
assign aws_axi_M.wvalid = pulp_axi_M.w_valid;
assign pulp_axi_M.w_ready = aws_axi_M.wready;
// B
assign pulp_axi_M.b_id = aws_axi_M.bid;
assign pulp_axi_M.b_resp = aws_axi_M.bresp;
assign pulp_axi_M.b_user = 0;
assign pulp_axi_M.b_valid = aws_axi_M.bvalid;
assign aws_axi_M.bready = pulp_axi_M.b_ready;
// AR
assign aws_axi_M.arid = pulp_axi_M.ar_id;
assign aws_axi_M.araddr = pulp_axi_M.ar_addr;
assign aws_axi_M.arlen = pulp_axi_M.ar_len;
assign aws_axi_M.arsize = pulp_axi_M.ar_size;
assign aws_axi_M.arvalid = pulp_axi_M.ar_valid;
assign pulp_axi_M.ar_ready = aws_axi_M.arready;
// R
assign pulp_axi_M.r_id = aws_axi_M.rid;
assign pulp_axi_M.r_data = aws_axi_M.rdata;
assign pulp_axi_M.r_resp = aws_axi_M.rresp;
assign pulp_axi_M.r_last = aws_axi_M.rlast;
assign pulp_axi_M.r_user = 0;
assign pulp_axi_M.r_valid = aws_axi_M.rvalid;
assign aws_axi_M.rready = pulp_axi_M.r_ready;
endmodule
