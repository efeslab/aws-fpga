module rr_writeback #(
   parameter WIDTH,
   parameter OFFSETWIDTH) (
   input clk,
   input sync_rst_n,
   // cfg_max_payload: see https://github.com/aws/aws-fpga/blob/master/hdk/docs/AWS_Shell_Interface_Specification.md#pcim-interface----axi-4-for-outbound-pcie-transactions-cl-is-master-shell-is-slave-512-bit
   input logic [1:0] cfg_max_payload,
   input logic [WIDTH-1:0] din,
   input logic [OFFSETWIDTH-1:0] offset,
   axi_bus_t.slave axi_out
);
// TODO: write log back to axi
endmodule
