HLS_DESIGN_DIR := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
HLS_DESIGN_SRC := $(wildcard $(HLS_DESIGN_DIR)*.cpp)
HLS_DESIGN_OBJ := $(HLS_DESIGN_SRC:.cpp=.o)
HLS_DESIGN_HEADER := $(wildcard $(HLS_DESIGN_DIR)*.h)
HLS_DESIGN_ALL_FILES := $(HLS_DEISNG_SRC) $(HLS_DESING_HEADER)
HLS_DESIGN_COMPILER = $(CXX)
CXXFLAGS += -I$(XILINX_XRT)/include
HLS_DESIGN_USE_OPENCL := 1
# 250MHz
HLS_DESIGN_AGFI_ID := TODO