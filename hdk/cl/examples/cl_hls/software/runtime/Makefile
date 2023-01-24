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

INCLUDES = -I$(SDK_DIR)/userspace/include

CC = gcc
CXX = g++
CMAKE ?= /usr/bin/cmake
CFLAGS = -DCONFIG_LOGLEVEL=4 -g $(INCLUDES)

LDLIBS = -lfpga_mgmt

ALL_HLS_DESIGN = 3d_rendering bnn digit_recognition face_detection spam_filter optical_flow sssp sha256 mobilenet
# hide the following applications for artifact eval
# nbody_2CU2Pipe HPCC/STREAM

# For HLS testing lib
LIB_SRC = test_common.c
LIB_HEADER = test_common.h
LIB_ALL_FILES = $(LIB_SRC) $(LIB_HEADER)
LIB_OBJ = $(LIB_SRC:.c=.o)


CFLAGS += -I.

# For HLS
CXXFLAGS = $(CFLAGS) -I$(XILINX_HLS)/include
LDLIBS += -lminizip -lz -lcrypto

HLS_GEN_DIR=../../gen

ifdef HLS_DESIGN
# {{{
BIN = $(HLS_DESIGN)_hw.elf
CFLAGS += -I$(HLS_DESIGN)
CXXFLAGS += -I$(HLS_DESIGN)
include $(HLS_DESIGN)/Makefile.inc
APP_AGFI_ID=$(HLS_DESIGN_AGFI_ID)
include ${CL_FPGARR_ROOT}/software/include/Makefile.include.common

# For HLS OpenCL
ifneq ($(HLS_DESIGN_USE_OPENCL),)
    include $(CL_FPGARR_OPENCL_ROOT)/Makefile.inc
    CFLAGS += -I$(LIBFPGARROPENCL_PATH)
    LDFLAGS += $(LIBFPGARROPENCL_PATH)/libfpgarropencl.a
    # ignore the test_common framework for OpenCL app
    LIB_OBJ=
endif
all: $(BIN)
$(BIN): $(HLS_DESIGN_OBJ) $(LIBFPGARR_OBJ) $(LIB_OBJ)
	$(HLS_DESIGN_COMPILER) -o $@ $(HLS_DESIGN_OBJ) $(LIBFPGARR_OBJ) $(LIB_OBJ) $(LDFLAGS) $(LDLIBS)
.PHONY: test
CMDLINE = $(HLS_DESIGN_TEST_ENV) ./$(BIN) $(HLS_DESIGN_TEST_ARGS)
test: $(BIN) $(AUTOMATE_TEST_OUT_DIR)
	for i in `seq -w 1 $(NUM_TEST)`; do                                        \
	    $(call singlelineish,$(call run_all_rr_mode,$(HLS_DESIGN)_$${i}))      \
	done
clean:
	rm -rf $(HLS_DESIGN_OBJ) $(LIBFPGARR_OBJ) $(LIB_OBJ)
#}}}
else
all: $(ALL_HLS_DESIGN)
	@for i in $^; do $(MAKE) HLS_DESIGN=$$i; done
test_all: $(ALL_HLS_DESIGN)
	# This cannot be paralleled so do not use $(MAKE)
	@for i in $^; do make HLS_DESIGN=$$i test; done
clean: $(ALL_HLS_DESIGN)
	@for i in $^; do $(MAKE) HLS_DESIGN=$$i clean; done
	rm *.elf
endif

check_env:
ifndef SDK_DIR
    $(error SDK_DIR is undefined. Try "source sdk_setup.sh" to set the software environment)
endif

help:
	@echo "Available HLS_DESIGN: $(ALL_HLS_DESIGN)"

include ${CL_FPGARR_ROOT}/software/include/Makefile.rules.common
