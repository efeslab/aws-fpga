# fpgarr project
#-y ${CL_FPGARR_ROOT}/design
+incdir+${CL_FPGARR_ROOT}/design
${CL_FPGARR_ROOT}/design/cl_fpgarr_pkg.sv
${CL_FPGARR_ROOT}/design/cl_fpgarr_utils.sv
${CL_FPGARR_ROOT}/design/cl_fpgarr_axi_rr.sv
${CL_FPGARR_ROOT}/design/cl_fpgarr_axil_rr.sv
${CL_FPGARR_ROOT}/design/twowayhandshake_logger.sv
${CL_FPGARR_ROOT}/design/twowayhandshake_replayer.sv
${CL_FPGARR_ROOT}/design/transkidbuf.sv
${CL_FPGARR_ROOT}/design/transkidbuf_pipeline.sv
${CL_FPGARR_ROOT}/design/axichannel_logger.sv
${CL_FPGARR_ROOT}/design/axichannel_replayer.sv
${CL_FPGARR_ROOT}/design/cl_fpgarr_packing.sv
${CL_FPGARR_ROOT}/design/cl_fpgarr_happenbefore_encoder.sv
${CL_FPGARR_ROOT}/design/cl_fpgarr_csrs.sv
${CL_FPGARR_ROOT}/design/cl_fpgarr_tracedecoder.sv
${CL_FPGARR_ROOT}/design/cl_fpgarr_chgrouping.sv
${CL_FPGARR_ROOT}/design/cl_fpgarr_rr_sel.sv
${CL_FPGARR_ROOT}/design/cl_fpgarr_rt_loge_crossbar.sv

## fpgarr tracestorage files
${CL_FPGARR_ROOT}/design/cl_fpgarr_tracestorage_axi.sv
${CL_FPGARR_ROOT}/design/cl_fpgarr_tracestorage_wrapper.sv
${CL_FPGARR_ROOT}/design/cl_fpgarr_tracestorage_wrapper_writeonly.sv
${CL_FPGARR_ROOT}/design/cl_fpgarr_tracestorage_encoder.sv
${CL_FPGARR_ROOT}/design/cl_fpgarr_tracestorage_decoder.sv
${CL_FPGARR_ROOT}/design/merged_fifo.sv

### fifo_128x128 by mjc
${CL_FPGARR_ROOT}/ip/fifo_128x128/sim/fifo_128x128.v
${CL_FPGARR_ROOT}/ip/fifo_128x128/hdl/fifo_generator_v13_2_rfs.v
${CL_FPGARR_ROOT}/ip/fifo_128x128/simulation/fifo_generator_vlog_beh.v

### parameterized fifo
${CL_FPGARR_ROOT}/design/lib/xpm_fifo_sync_wrapper.sv

# start of rr_pcim_axi_interconnect
${CL_FPGARR_ROOT}/design/cl_fpgarr_pcim_interconnect.sv
${CL_FPGARR_ROOT}/ip/rr_pcim_axi_interconnect/sim/rr_pcim_axi_interconnect.v
${CL_FPGARR_ROOT}/ip/rr_pcim_axi_interconnect/ip/rr_pcim_axi_interconnect_xbar_0/sim/rr_pcim_axi_interconnect_xbar_0.v
${CL_FPGARR_ROOT}/ip/rr_pcim_axi_interconnect/ip/rr_pcim_axi_interconnect_s00_regslice_0/sim/rr_pcim_axi_interconnect_s00_regslice_0.v
${CL_FPGARR_ROOT}/ip/rr_pcim_axi_interconnect/ip/rr_pcim_axi_interconnect_s01_regslice_0/sim/rr_pcim_axi_interconnect_s01_regslice_0.v
${CL_FPGARR_ROOT}/ip/rr_pcim_axi_interconnect/ip/rr_pcim_axi_interconnect_s02_regslice_0/sim/rr_pcim_axi_interconnect_s02_regslice_0.v
${CL_FPGARR_ROOT}/ip/rr_pcim_axi_interconnect/ip/rr_pcim_axi_interconnect_m00_regslice_0/sim/rr_pcim_axi_interconnect_m00_regslice_0.v
## start of rr_pcim_pchk_interconnect (only for debugging in simulation)
${CL_FPGARR_ROOT}/ip/rr_pcim_pchk_interconnect/sim/rr_pcim_pchk_interconnect.v
${CL_FPGARR_ROOT}/ip/rr_pcim_pchk_interconnect/ip/rr_pcim_pchk_interconnect_xbar_0/sim/rr_pcim_pchk_interconnect_xbar_0.v
${CL_FPGARR_ROOT}/ip/rr_pcim_pchk_interconnect/ip/rr_pcim_pchk_interconnect_s00_regslice_0/sim/rr_pcim_pchk_interconnect_s00_regslice_0.v
${CL_FPGARR_ROOT}/ip/rr_pcim_pchk_interconnect/ip/rr_pcim_pchk_interconnect_s01_regslice_0/sim/rr_pcim_pchk_interconnect_s01_regslice_0.v
${CL_FPGARR_ROOT}/ip/rr_pcim_pchk_interconnect/ip/rr_pcim_pchk_interconnect_s02_regslice_0/sim/rr_pcim_pchk_interconnect_s02_regslice_0.v
${CL_FPGARR_ROOT}/ip/rr_pcim_pchk_interconnect/ip/rr_pcim_pchk_interconnect_m00_regslice_0/sim/rr_pcim_pchk_interconnect_m00_regslice_0.v
${CL_FPGARR_ROOT}/ip/rr_pcim_pchk_interconnect/ip/rr_pcim_pchk_interconnect_s00_pchk_0/sim/rr_pcim_pchk_interconnect_s00_pchk_0.sv
${CL_FPGARR_ROOT}/ip/rr_pcim_pchk_interconnect/ip/rr_pcim_pchk_interconnect_s01_pchk_0/sim/rr_pcim_pchk_interconnect_s01_pchk_0.sv
${CL_FPGARR_ROOT}/ip/rr_pcim_pchk_interconnect/ip/rr_pcim_pchk_interconnect_s02_pchk_0/sim/rr_pcim_pchk_interconnect_s02_pchk_0.sv
${CL_FPGARR_ROOT}/ip/rr_pcim_pchk_interconnect/ip/rr_pcim_pchk_interconnect_m00_pchk_0/sim/rr_pcim_pchk_interconnect_m00_pchk_0.sv
## start of rr_irq_pcim_interconnect (to convert interrupt requests to pcim requests)
${CL_FPGARR_ROOT}/ip/rr_irq_pcim_interconnect/sim/rr_irq_pcim_interconnect.v
${CL_FPGARR_ROOT}/ip/rr_irq_pcim_interconnect/ip/rr_irq_pcim_interconnect_xbar_1/sim/rr_irq_pcim_interconnect_xbar_1.v
${CL_FPGARR_ROOT}/ip/rr_irq_pcim_interconnect/ip/rr_irq_pcim_interconnect_m00_regslice_0/sim/rr_irq_pcim_interconnect_m00_regslice_0.v
${CL_FPGARR_ROOT}/ip/rr_irq_pcim_interconnect/ip/rr_irq_pcim_interconnect_s00_regslice_0/sim/rr_irq_pcim_interconnect_s00_regslice_0.v
${CL_FPGARR_ROOT}/ip/rr_irq_pcim_interconnect/ip/rr_irq_pcim_interconnect_s01_regslice_0/sim/rr_irq_pcim_interconnect_s01_regslice_0.v
# start of rr_cfg_axil_interconnect
${CL_FPGARR_ROOT}/ip/rr_cfg_axil_interconnect/sim/rr_cfg_axil_interconnect.v
${CL_FPGARR_ROOT}/ip/rr_cfg_axil_interconnect/ip/rr_cfg_axil_interconnect_xbar_2/sim/rr_cfg_axil_interconnect_xbar_2.v
#../../ip/rr_pcim_axi_interconnect/ip/
# ila
${CL_FPGARR_ROOT}/ip/dbg_trace_split_ila/sim/dbg_trace_split_ila.v
${CL_FPGARR_ROOT}/ip/dbg_valid_replayer_ila/sim/dbg_valid_replayer_ila.v
${CL_FPGARR_ROOT}/ip/dbg_ready_replayer_ila/sim/dbg_ready_replayer_ila.v
${CL_FPGARR_ROOT}/ip/dbg_fpgarr_wrapper_ila/sim/dbg_fpgarr_wrapper_ila.v
# fpgarr top module
${CL_FPGARR_ROOT}/design/cl_fpgarr_wrapper.sv
