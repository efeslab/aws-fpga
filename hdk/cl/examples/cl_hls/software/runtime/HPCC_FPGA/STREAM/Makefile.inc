HLS_DESIGN_DIR := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
HLS_DESIGN_OBJ := $(foreach obj, main.cpp.o libstream_aws_fpgarr.a libhpcc_fpga_base.a, $(HLS_DESIGN_DIR)/build/$(obj))
include $(HLS_DESIGN_DIR)/../Makefile.fpgarr.inc
HLS_DESIGN_COMPILER := $(CXX)
#CXXFLAGS += -I$(XILINX_XRT)/include
HLS_DESIGN_USE_OPENCL := 1
# 250MHz
HLS_DESIGN_AGFI_ID := agfi-0d62ee31a2aea95f1
