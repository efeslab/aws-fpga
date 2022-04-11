typedef struct packed {
    logic [63:0] pcim_base_addr;
} app_csrs_t;

module axi_atop_filter_app (
    input wire clk,
    input wire rstn,
    axi_bus_t.master pcis_bus,
    axi_lite_bus_t.master sh_ocl_bus,
    axi_bus_t.slave pcim_mstr_bus
);

AXI_BUS #(.AXI_ADDR_WIDTH(64), .AXI_DATA_WIDTH(512), .AXI_ID_WIDTH(6), .AXI_USER_WIDTH(1)) axi_atop_in();
AXI_BUS #(.AXI_ADDR_WIDTH(64), .AXI_DATA_WIDTH(512), .AXI_ID_WIDTH(6), .AXI_USER_WIDTH(1)) axi_atop_out();

//// aws AXI (pcis_bus) -> pulp AXI (axi_atop_in)
// AW
assign axi_atop_in.aw_id = pcis_bus.awid[5:0];
assign axi_atop_in.aw_addr = pcis_bus.awaddr;
assign axi_atop_in.aw_len = pcis_bus.awlen;
assign axi_atop_in.aw_size = pcis_bus.awsize;
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
assign axi_atop_in.aw_valid = pcis_bus.awvalid;
assign pcis_bus.awready = axi_atop_in.aw_ready;
// W
assign axi_atop_in.w_data = pcis_bus.wdata;
assign axi_atop_in.w_strb = pcis_bus.wstrb;
assign axi_atop_in.w_last = pcis_bus.wlast;
assign axi_atop_in.w_user = 0;
assign axi_atop_in.w_valid = pcis_bus.wvalid;
assign pcis_bus.wready = axi_atop_in.w_ready;
// B
assign pcis_bus.bid[5:0] = axi_atop_in.b_id;
assign pcis_bus.bresp = axi_atop_in.b_resp;
//assign pcis_bus.buser = ??? // disabled skip
assign pcis_bus.bvalid = axi_atop_in.b_valid;
assign axi_atop_in.b_ready = pcis_bus.bready;
// AR
assign axi_atop_in.ar_id = pcis_bus.arid[5:0];
assign axi_atop_in.ar_addr = pcis_bus.araddr;
assign axi_atop_in.ar_len = pcis_bus.arlen;
assign axi_atop_in.ar_size = pcis_bus.arsize;
assign axi_atop_in.ar_burst = 2'b01; // INCR
assign axi_atop_in.ar_lock = 0; // normal access
assign axi_atop_in.ar_cache = 4'b0011; // 001x non-cacheable 1: system
assign axi_atop_in.ar_prot = 3'b010; // [2] Data access,
                                     // [1] Non-secure access,
                                     // [0] Unpriviledged access
assign axi_atop_in.ar_qos = 4'b0; // not participating in any QOS
assign axi_atop_in.ar_region = 4'b0; // no region I guess?
assign axi_atop_in.ar_user = 0;
assign axi_atop_in.ar_valid = pcis_bus.arvalid;
assign pcis_bus.arready = axi_atop_in.ar_ready;
// R
assign pcis_bus.rid[5:0] = axi_atop_in.r_id;
assign pcis_bus.rdata = axi_atop_in.r_data;
assign pcis_bus.rresp = axi_atop_in.r_resp;
assign pcis_bus.rlast = axi_atop_in.r_last;
//assign pcis_bus.ruser = ??? // disabled skip
assign pcis_bus.rvalid = axi_atop_in.r_valid;
assign axi_atop_in.r_ready = pcis_bus.rready;

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
assign pcim_mstr_bus.awvalid = axi_atop_out.aw_valid;
assign axi_atop_out.aw_ready = pcim_mstr_bus.awready;
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
    end
    else if (sh_ocl_bus.wvalid && sh_ocl_bus.wready)
        case (buf_awaddr)
            `CSR_ADDR(PCIM_BASE_ADDR_LO):
                csrs.pcim_base_addr[0 +: 32] <= sh_ocl_bus.wdata;
            `CSR_ADDR(PCIM_BASE_ADDR_HI):
                csrs.pcim_base_addr[32 +: 32] <= sh_ocl_bus.wdata;
        endcase
endmodule
