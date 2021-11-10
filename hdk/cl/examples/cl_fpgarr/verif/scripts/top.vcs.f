# Amazon FPGA Hardware Development Kit
#
# Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
#
# Licensed under the Amazon Software License (the "License"). You may not use
# this file except in compliance with the License. A copy of the License is
# located at
#
#    http://aws.amazon.com/asl/
#
# or in the "license" file accompanying this file. This file is distributed on
# an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
# implied. See the License for the specific language governing permissions and
# limitations under the License.

+define+VCS_SIM

+libext+.v
+libext+.sv
+libext+.svh

-y ${CL_ROOT}/design
-y ${SH_LIB_DIR}
-y ${SH_INF_DIR}
-y ${HDK_SHELL_DESIGN_DIR}/sh_ddr/sim

+incdir+${CL_ROOT}/../common/design
+incdir+${CL_ROOT}/design
+incdir+${CL_ROOT}/verif/sv
+incdir+${CL_ROOT}/verif/tests
+incdir+${SH_LIB_DIR}
+incdir+${SH_INF_DIR}
+incdir+${HDK_COMMON_DIR}/verif/include
+incdir+${CL_ROOT}/design/axi_crossbar_0
+incdir+${SH_LIB_DIR}/../ip/cl_axi_interconnect/ipshared/7e3a/hdl
+incdir+${HDK_SHELL_DESIGN_DIR}/sh_ddr/sim
+incdir+${HDK_SHELL_DESIGN_DIR}/ip/src_register_slice/hdl

${HDK_SHELL_DESIGN_DIR}/ip/cl_axi_interconnect/ipshared/9909/hdl/axi_data_fifo_v2_1_vl_rfs.v
${HDK_SHELL_DESIGN_DIR}/ip/cl_axi_interconnect/ipshared/c631/hdl/axi_crossbar_v2_1_vl_rfs.v
${HDK_SHELL_DESIGN_DIR}/ip/cl_axi_interconnect/ip/cl_axi_interconnect_xbar_0/sim/cl_axi_interconnect_xbar_0.v
${HDK_SHELL_DESIGN_DIR}/ip/cl_axi_interconnect/ip/cl_axi_interconnect_s00_regslice_0/sim/cl_axi_interconnect_s00_regslice_0.v
${HDK_SHELL_DESIGN_DIR}/ip/cl_axi_interconnect/ip/cl_axi_interconnect_s01_regslice_0/sim/cl_axi_interconnect_s01_regslice_0.v
${HDK_SHELL_DESIGN_DIR}/ip/cl_axi_interconnect/ip/cl_axi_interconnect_m00_regslice_0/sim/cl_axi_interconnect_m00_regslice_0.v
${HDK_SHELL_DESIGN_DIR}/ip/cl_axi_interconnect/ip/cl_axi_interconnect_m01_regslice_0/sim/cl_axi_interconnect_m01_regslice_0.v
${HDK_SHELL_DESIGN_DIR}/ip/cl_axi_interconnect/ip/cl_axi_interconnect_m02_regslice_0/sim/cl_axi_interconnect_m02_regslice_0.v
${HDK_SHELL_DESIGN_DIR}/ip/cl_axi_interconnect/ip/cl_axi_interconnect_m03_regslice_0/sim/cl_axi_interconnect_m03_regslice_0.v
${HDK_SHELL_DESIGN_DIR}/ip/cl_axi_interconnect/sim/cl_axi_interconnect.v
${HDK_SHELL_DESIGN_DIR}/ip/dest_register_slice/hdl/axi_register_slice_v2_1_vl_rfs.v
${HDK_SHELL_DESIGN_DIR}/ip/axi_clock_converter_0/hdl/axi_clock_converter_v2_1_vl_rfs.v
${HDK_SHELL_DESIGN_DIR}/ip/axi_clock_converter_0/hdl/fifo_generator_v13_2_rfs.v
${HDK_SHELL_DESIGN_DIR}/ip/axi_clock_converter_0/sim/axi_clock_converter_0.v
${HDK_SHELL_DESIGN_DIR}/ip/dest_register_slice/sim/dest_register_slice.v
${HDK_SHELL_DESIGN_DIR}/ip/src_register_slice/sim/src_register_slice.v
${HDK_SHELL_DESIGN_DIR}/ip/axi_register_slice/sim/axi_register_slice.v
${HDK_SHELL_DESIGN_DIR}/ip/axi_register_slice_light/sim/axi_register_slice_light.v

${CL_ROOT}/ip/fifo_128x128/sim/fifo_128x128.v
${CL_ROOT}/ip/fifo_128x128/hdl/fifo_generator_v13_2_rfs.v
${CL_ROOT}/ip/fifo_128x128/simulation/fifo_generator_vlog_beh.v

+define+DISABLE_VJTAG_DEBUG
${CL_ROOT}/design/axil_slave.sv
${CL_ROOT}/design/cl_dram_dma_defines.vh
${CL_ROOT}/design/cl_tst_scrb.sv
${CL_ROOT}/design/cl_tst.sv
${CL_ROOT}/design/cl_int_tst.sv
${CL_ROOT}/design/cl_dram_dma_pkg.sv
${CL_ROOT}/design/cl_dma_pcis_slv.sv
${CL_ROOT}/design/cl_pcim_mstr.sv
${CL_ROOT}/design/cl_ila.sv
${CL_ROOT}/design/cl_vio.sv
${CL_ROOT}/design/cl_int_slv.sv
${CL_ROOT}/design/cl_ocl_slv.sv
${CL_ROOT}/design/cl_sda_slv.sv
${CL_ROOT}/design/cl_dram_dma_axi_mstr.sv
${CL_ROOT}/design/cl_dram_dma.sv

# fpgarr project
${CL_ROOT}/design/cl_fpgarr_pkg.sv
${CL_ROOT}/design/cl_fpgarr_utils.sv
${CL_ROOT}/design/cl_fpgarr_axi_rr.sv
${CL_ROOT}/design/cl_fpgarr_axil_rr.sv
${CL_ROOT}/design/twowayhandshake_logger.sv
${CL_ROOT}/design/twowayhandshake_replayer.sv
${CL_ROOT}/design/transkidbuf.sv
${CL_ROOT}/design/transkidbuf_pipeline.sv
${CL_ROOT}/design/axichannel_logger.sv
${CL_ROOT}/design/axichannel_replayer.sv
${CL_ROOT}/design/cl_fpgarr_packing.sv
${CL_ROOT}/design/cl_fpgarr_happenbefore_encoder.sv
${CL_ROOT}/design/cl_fpgarr_csrs.sv
${CL_ROOT}/design/cl_fpgarr_tracedecoder.sv
${CL_ROOT}/design/cl_fpgarr_chgrouping.sv
${CL_ROOT}/design/cl_fpgarr_rr_sel.sv
${CL_ROOT}/design/cl_fpgarr_rt_loge_crossbar.sv

## fpgarr tracestorage files
${CL_ROOT}/design/cl_fpgarr_tracestorage_axi.sv
${CL_ROOT}/design/cl_fpgarr_tracestorage_wrapper.sv
${CL_ROOT}/design/cl_fpgarr_tracestorage_encoder.sv
${CL_ROOT}/design/cl_fpgarr_tracestorage_decoder.sv
${CL_ROOT}/design/cl_fpgarr_pcim_interconnect.sv
${CL_ROOT}/design/merged_fifo.sv

## fpgarr 3rd-party lib
### parameterized bram fifo
${CL_ROOT}/design/lib/ram_fifo_ft.sv
${CL_ROOT}/design/lib/bram_1w1r.sv
${CL_ROOT}/design/lib/ft_fifo_p.v

# start of rr_pcim_axi_interconnect
${CL_ROOT}/ip/rr_pcim_axi_interconnect/sim/rr_pcim_axi_interconnect.v
${CL_ROOT}/ip/rr_pcim_axi_interconnect/ip/rr_pcim_axi_interconnect_xbar_0/sim/rr_pcim_axi_interconnect_xbar_0.v
${CL_ROOT}/ip/rr_pcim_axi_interconnect/ip/rr_pcim_axi_interconnect_s00_regslice_0/sim/rr_pcim_axi_interconnect_s00_regslice_0.v
${CL_ROOT}/ip/rr_pcim_axi_interconnect/ip/rr_pcim_axi_interconnect_s01_regslice_0/sim/rr_pcim_axi_interconnect_s01_regslice_0.v
${CL_ROOT}/ip/rr_pcim_axi_interconnect/ip/rr_pcim_axi_interconnect_m00_regslice_0/sim/rr_pcim_axi_interconnect_m00_regslice_0.v
# start of rr_cfg_axil_interconnect
${CL_ROOT}/ip/rr_cfg_axil_interconnect/sim/rr_cfg_axil_interconnect.v
${CL_ROOT}/ip/rr_cfg_axil_interconnect/ip/rr_cfg_axil_interconnect_xbar_2/sim/rr_cfg_axil_interconnect_xbar_2.v
#../../ip/rr_pcim_axi_interconnect/ip/
# fpgarr top module
${CL_ROOT}/design/cl_fpgarr_wrapper.sv

# simulation top module
-f ${HDK_COMMON_DIR}/verif/tb/filelists/tb.${SIMULATOR}.f
${TEST_NAME}

+define+WRITEBACK_DEBUG
