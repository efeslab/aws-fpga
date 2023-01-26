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
CFLAGS = -DCONFIG_LOGLEVEL=4 -g $(INCLUDES)

LDLIBS = -lfpga_mgmt

LIB_SRC = test_common.c
LIB_HEADER = test_common.h
LIB_ALL_FILES = $(LIB_SRC) $(LIB_HEADER)
LIB_OBJ = $(LIB_SRC:.c=.o)


APP_AGFI_ID=agfi-0fa94e30b488273e0
APP_AGFI_ID_LOSSCHECK=agfi-04d184e6f1ac13f7a
include ${CL_FPGARR_ROOT}/software/include/Makefile.include.common

CFLAGS += -I.
# For HLS
CXXFLAGS = $(CFLAGS) -I$(XILINX_HLS)/include
LDLIBS += -lpthread


BIN=axis_fifo_hw.elf
all: $(BIN)
$(BIN): $(LIBFPGARR_OBJ) $(LIB_OBJ)
	$(CC) -o $@ $(CFLAGS) $(LIBFPGARR_OBJ) $(LIB_OBJ)$ $(LDFLAGS) $(LDLIBS)
.PHONY: bug_delayed_start bug_dma_alignment correct_run
BUFFER_ALIGNMENT?=4096
DELAYED_START?=delayed_start
CMDLINE = ./$(BIN) ${BUFFER_ALIGNMENT} ${DELAYED_START}
TESTID=$(BIN)_${BUFFER_ALIGNMENT}_${DELAYED_START}

bug_delayed_start: $(BIN) $(COMMON_TEST_DEPS)
	$(eval BUFFER_ALIGNMENT=4096)
	$(eval DELAYED_START=delayed_start)
	$(call run_all_rr_mode,$(TESTID))

bug_dma_alignment: $(BIN) $(COMMON_TEST_DEPS)
	$(eval BUFFER_ALIGNMENT=8)
	$(eval DELAYED_START=imm_start)
	$(call run_all_rr_mode,$(TESTID))

correct_run: $(BIN)
	$(eval BUFFER_ALIGNMENT=4096)
	$(eval DELAYED_START=imm_start)
	$(LOAD_AFI) > /dev/null
	$(call RR_NONE, $(CMDLINE)) 2>&1

load_instrumented:
	$(call LOAD_AFI_TPL, $(APP_AGFI_ID_LOSSCHECK))

replay_delayed_start: $(BIN) $(COMMON_TEST_DEPS)
	$(eval BUFFER_ALIGNMENT=4096)
	$(eval DELAYED_START=delayed_start)
	$(call RR_REPLAY, RR_RECORD_PATH=$(AUTOMATE_TEST_OUT_DIR)/$(TESTID)_record.dump $(CMDLINE)) 2>&1

clean:
	rm -rf *.elf $(LIBFPGARR_OBJ) $(LIB_OBJ)

check_env:
ifndef SDK_DIR
    $(error SDK_DIR is undefined. Try "source sdk_setup.sh" to set the software environment)
endif

include ${CL_FPGARR_ROOT}/software/include/Makefile.rules.common
