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


include ${CL_FPGARR_ROOT}/software/runtime/libfpgarr/Makefile.inc
CFLAGS += -I$(LIBFPGARR_PATH) -I.
LIBFPGARR_OBJ = $(LIBFPGARR_SRC:.c=.o)
RR_TOOL=${CL_FPGARR_ROOT}/software/runtime/rr_tool/rr_tool.opt.elf

# For HLS
CXXFLAGS = $(CFLAGS) -I$(XILINX_HLS)/include
LDLIBS += -lpthread

#### Helper functions
RUN_RR = sudo RR_MODE=$(1) $(2)
RR_NONE = $(call RUN_RR,none,$(1))
RR_RECORDV = $(call RUN_RR,recordv,$(1))
RR_REPLAYV = $(call RUN_RR,replayv,$(1))
LOAD_AFI_TPL = sudo fpga-load-local-image -S 0 -I $(1)
AUTOMATE_TEST_OUT_DIR?=/mnt/output

BIN=axi_atop_filter_hw.elf
APP_NAME=axi_atop_filter
APP_BUGGY_AGFI_ID=agfi-08e2007692a1ae9f4
APP_FIXED_AGFI_ID=agfi-04a0ebace9cc20b1b
all: $(BIN)
$(BIN): $(LIBFPGARR_OBJ) $(LIB_OBJ)
	$(CC) -o $@ $(CFLAGS) $(LIBFPGARR_OBJ) $(LIB_OBJ)$ $(LDFLAGS) $(LDLIBS)
.PHONY: test
LOAD_BUGGY_AFI = $(call LOAD_AFI_TPL, $(APP_BUGGY_AGFI_ID))
LOAD_FIXED_AFI = $(call LOAD_AFI_TPL, $(APP_FIXED_AGFI_ID))
CMDLINE = ./$(BIN)
test: $(BIN)
	$(LOAD_BUGGY_AFI); \
	$(call RR_NONE, $(CMDLINE)) 2>&1 | tee $(AUTOMATE_TEST_OUT_DIR)/$(APP_NAME)_none.log; \
	$(LOAD_BUGGY_AFI); \
	$(call RR_RECORDV, $(CMDLINE)) 2>&1 | tee $(AUTOMATE_TEST_OUT_DIR)/$(APP_NAME)_recordv.log; \
	$(LOAD_BUGGY_AFI); \
	$(call RR_REPLAYV, $(CMDLINE)) 2>&1 | tee $(AUTOMATE_TEST_OUT_DIR)/$(APP_NAME)_replayv.log; \
	$(RR_TOOL) -v --hbver2 -c validate_record.dump -c validate_replay.dump > $(AUTOMATE_TEST_OUT_DIR)/$(APP_NAME)_diff.txt 2>&1; \
	for dump in record.dump validate_record.dump validate_replay.dump; do \
	  mv $${dump} ${AUTOMATE_TEST_OUT_DIR}/$(BIN)_$${dump}; \
	done
load_buggy:
	sudo fpga-clear-local-image -S 0
	$(LOAD_BUGGY_AFI)
load_fixed:
	sudo fpga-clear-local-image -S 0
	$(LOAD_FIXED_AFI)
clean:
	rm -rf *.elf $(LIBFPGARR_OBJ) $(LIB_OBJ)

check_env:
ifndef SDK_DIR
    $(error SDK_DIR is undefined. Try "source sdk_setup.sh" to set the software environment)
endif

f1setup:
	sudo mkfs.ext4 /dev/nvme0n1
	sudo mount /dev/nvme0n1 /mnt
	sudo mkdir /mnt/output
	sudo chown -R ubuntu:ubuntu /mnt/output
help:
	@echo "Available APP_NAME: $(ALL_APP_NAME)"
