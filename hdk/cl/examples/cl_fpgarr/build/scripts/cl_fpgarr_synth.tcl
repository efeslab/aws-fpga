# synthesis related tcl commands required by cl_fpgarr
# This should be sourced in the application synth_${CL_MODULE}.tcl
read_bd [ list \
  $CL_FPGARR_ROOT/ip/rr_pcim_axi_interconnect/rr_pcim_axi_interconnect.bd \
  $CL_FPGARR_ROOT/ip/rr_cfg_axil_interconnect/rr_cfg_axil_interconnect.bd \
  $CL_FPGARR_ROOT/ip/rr_pcim_pchk_interconnect/rr_pcim_pchk_interconnect.bd \
  $CL_FPGARR_ROOT/ip/rr_irq_pcim_interconnect/rr_irq_pcim_interconnect.bd
]

read_ip [ list \
  $CL_FPGARR_ROOT/ip/fifo_128x128/fifo_128x128.xci \
  $CL_FPGARR_ROOT/ip/dbg_trace_split_ila/dbg_trace_split_ila.xci \
  $CL_FPGARR_ROOT/ip/dbg_valid_replayer_ila/dbg_valid_replayer_ila.xci \
  $CL_FPGARR_ROOT/ip/dbg_ready_replayer_ila/dbg_ready_replayer_ila.xci \
  $CL_FPGARR_ROOT/ip/dbg_fpgarr_wrapper_ila/dbg_fpgarr_wrapper_ila.xci \
  $CL_FPGARR_ROOT/ip/dbg_fpgarr_pcim_interconnect_ila/dbg_fpgarr_pcim_interconnect_ila.xci
]
