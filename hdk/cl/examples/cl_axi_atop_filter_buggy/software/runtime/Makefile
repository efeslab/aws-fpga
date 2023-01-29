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


BIN=axi_atop_filter_hw.elf
APP_NAME=axi_atop_filter
APP_BUGGY_AGFI_ID=agfi-08e2007692a1ae9f4
APP_FIXED_AGFI_ID=agfi-04a0ebace9cc20b1b
APP_AGFI_ID=$(APP_BUGGY_AGFI_ID)
include ${CL_FPGARR_ROOT}/software/include/Makefile.include.common
CFLAGS += -I.
# For HLS
CXXFLAGS = $(CFLAGS) -I$(XILINX_HLS)/include
LDLIBS += -lpthread

all: $(BIN)
$(BIN): $(LIBFPGARR_OBJ) $(LIB_OBJ)
	$(CC) -o $@ $(CFLAGS) $(LIBFPGARR_OBJ) $(LIB_OBJ)$ $(LDFLAGS) $(LDLIBS)
.PHONY: test record mutate replay_mutation load_buggy load_fixed
CMDLINE = ./$(BIN)
record_replay: $(BIN) $(COMMON_TEST_DEPS)
	$(call run_all_rr_mode,$(APP_NAME))
load_buggy:
	$(call CLR_LOAD_AFI_TPL,$(APP_BUGGY_AGFI_ID))
load_fixed:
	$(call CLR_LOAD_AFI_TPL,$(APP_FIXED_AGFI_ID))

ORIG_REC_DUMP=$(AUTOMATE_TEST_OUT_DIR)/$(APP_NAME)_record.dump
ORIG_VAL_REC_DUMP=$(AUTOMATE_TEST_OUT_DIR)/$(APP_NAME)_validate_record.dump
MUT_REC_DUMP=$(AUTOMATE_TEST_OUT_DIR)/$(APP_NAME)_record_mutated.dump
$(MUT_REC_DUMP): $(AUTOMATE_TEST_OUT_DIR)
	${RR_TOOL} -r -a $(ORIG_REC_DUMP) -d > $(ORIG_REC_DUMP).txt
	${RR_TOOL} -m $(ORIG_REC_DUMP) -m $(ORIG_VAL_REC_DUMP) -o $(MUT_REC_DUMP)
	${RR_TOOL} -r -a $(MUT_REC_DUMP) -d > $(MUT_REC_DUMP).txt
mutate: $(MUT_REC_DUMP)
replay_mutation: $(MUT_REC_DUMP)
	$(call RR_REPLAY, RR_RECORD_PATH=$(MUT_REC_DUMP) $(CMDLINE) 2>&1)

clean:
	rm -rf *.elf $(LIBFPGARR_OBJ) $(LIB_OBJ)

check_env:
ifndef SDK_DIR
    $(error SDK_DIR is undefined. Try "source sdk_setup.sh" to set the software environment)
endif
include ${CL_FPGARR_ROOT}/software/include/Makefile.rules.common
