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

-f ${HDK_COMMON_DIR}/verif/tb/filelists/tb.${SIMULATOR}.f
${TEST_NAME}

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

${CL_ROOT}/design/cl_id_defines.vh
${CL_ROOT}/design/cl_dram_dma_defines.vh
${CL_ROOT}/design/cl_dram_dma_pkg.sv
${CL_ROOT}/design/cl_dma_pcis_slv.sv
${CL_ROOT}/design/hls_accel_wrapper.sv
${CL_ROOT}/design/cl_dram_dma.sv
${CL_ROOT}/design/cl_ocl_slv_reg.sv

${CL_ROOT}/design/hls_accel/verilog/rendering_coloringFB.v
${CL_ROOT}/design/hls_accel/verilog/rendering_control_s_axi.v
${CL_ROOT}/design/hls_accel/verilog/rendering_dataflow_in_loop_TRIANGLES_fragment_color_V_memcore.v
${CL_ROOT}/design/hls_accel/verilog/rendering_dataflow_in_loop_TRIANGLES_fragment_color_V.v
${CL_ROOT}/design/hls_accel/verilog/rendering_dataflow_in_loop_TRIANGLES_fragment_x_V_memcore.v
${CL_ROOT}/design/hls_accel/verilog/rendering_dataflow_in_loop_TRIANGLES_fragment_x_V.v
${CL_ROOT}/design/hls_accel/verilog/rendering_dataflow_in_loop_TRIANGLES.v
${CL_ROOT}/design/hls_accel/verilog/rendering_dataflow_parent_loop_proc.v
${CL_ROOT}/design/hls_accel/verilog/rendering_fifo_w12_d2_S.v
${CL_ROOT}/design/hls_accel/verilog/rendering_fifo_w12_d4_S.v
${CL_ROOT}/design/hls_accel/verilog/rendering_fifo_w16_d2_S.v
${CL_ROOT}/design/hls_accel/verilog/rendering_fifo_w1_d2_S.v
${CL_ROOT}/design/hls_accel/verilog/rendering_fifo_w8_d2_S.v
${CL_ROOT}/design/hls_accel/verilog/rendering_frame_buffer_V.v
${CL_ROOT}/design/hls_accel/verilog/rendering_gmem_m_axi.v
${CL_ROOT}/design/hls_accel/verilog/rendering_mac_mulsub_9s_9s_18ns_18_4_1.v
${CL_ROOT}/design/hls_accel/verilog/rendering_mul_8ns_10ns_17_1_1.v
${CL_ROOT}/design/hls_accel/verilog/rendering_mul_9s_9s_16_1_1.v
${CL_ROOT}/design/hls_accel/verilog/rendering_mul_9s_9s_18_1_1.v
${CL_ROOT}/design/hls_accel/verilog/rendering_projection.v
${CL_ROOT}/design/hls_accel/verilog/rendering_rasterization1.v
${CL_ROOT}/design/hls_accel/verilog/rendering_rasterization2.v
${CL_ROOT}/design/hls_accel/verilog/rendering_udiv_16ns_8ns_8_20_1.v
${CL_ROOT}/design/hls_accel/verilog/rendering_urem_16ns_8ns_8_20_1.v
${CL_ROOT}/design/hls_accel/verilog/rendering.v
${CL_ROOT}/design/hls_accel/verilog/rendering_zculling.v
${CL_ROOT}/design/hls_accel/verilog/rendering_zculling_z_buffer_V.v
