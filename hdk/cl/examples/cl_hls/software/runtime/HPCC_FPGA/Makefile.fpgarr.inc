CMAKE ?= /usr/bin/cmake
HLS_DESIGN_SRC :=
HLS_DESIGN_HEADER :=
HLS_DESIGN_ALL_FILES := $(HLS_DEISNG_SRC) $(HLS_DESING_HEADER)
CMAKE_TARGET := fpgarr_gen
$(HLS_DESIGN_OBJ):
	mkdir -p $(HLS_DESIGN_DIR)/build && cd $(HLS_DESIGN_DIR)/build && $(CMAKE) ..  -DHPCC_FPGA_CONFIG=../configs/AWSF1.cmake && make $(CMAKE_TARGET)
