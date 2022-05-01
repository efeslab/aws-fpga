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
CFLAGS = -DCONFIG_LOGLEVEL=4 -std=gnu11 -g -Wall -Werror $(INCLUDES)

LDLIBS = -lfpga_mgmt

SRC = test_dram_dma_common.c test_dram_dma_retention.c test_dram_dma.c test_dram_dma_hwsw_cosim.c
OBJ = $(SRC:.c=.o)

include ${CL_FPGARR_ROOT}/software/runtime/libfpgarr/Makefile.inc
CFLAGS += -I$(LIBFPGARR_PATH)


all: test_dram_dma check_env retention

test_dram_dma: $(OBJ) $(LIBFPGARR_ALL_FILES)
	$(CC) $(CFLAGS) -o test_dram_dma test_dram_dma.o test_dram_dma_common.o $(LIBFPGARR_SRC) $(LDFLAGS) $(LDLIBS)

retention: $(OBJ)
	$(CC) $(CFLAGS) -o test_dram_dma_retention test_dram_dma_retention.o test_dram_dma_common.o $(LDFLAGS) $(LDLIBS)

cosim: $(OBJ) $(LIBFPGARR_ALL_FILES)
	$(CC) $(CFLAGS) -o test_dram_dma_hwsw_cosim test_dram_dma_hwsw_cosim.o test_dram_dma_common.o $(LIBFPGARR_SRC) $(LDFLAGS) $(LDLIBS)

clean:
	rm -f *.o test_dram_dma_retention test_dram_dma test_dram_dma_hwsw_cosim

check_env:
ifndef SDK_DIR
    $(error SDK_DIR is undefined. Try "source sdk_setup.sh" to set the software environment)
endif

RUN_RR = sudo RR_MODE=$(1) $(2)
RR_NONE = $(call RUN_RR,none,$(1))
RR_RECORDV = $(call RUN_RR,recordv,$(1))
RR_REPLAYV = $(call RUN_RR,replayv,$(1))
# 250MHz
LOAD_AFI = sudo fpga-clear-local-image -S 0; sudo fpga-load-local-image -S 0 -I agfi-0eb4759660bb582b2
NUM_TEST?=10
AUTOMATE_TEST_OUT_DIR?=/mnt/output
BIN=test_dram_dma
CMDLINE=./$(BIN) -S 0
RR_TOOL=${CL_FPGARR_ROOT}/software/runtime/rr_tool/rr_tool.opt.elf
test: $(BIN)
	for i in `seq -w 1 $(NUM_TEST)`; do \
	    $(LOAD_AFI); \
	    $(call RR_NONE, $(CMDLINE)) 2>&1 | tee $(AUTOMATE_TEST_OUT_DIR)/$(BIN)_$${i}_none.log; \
			sudo fpga-describe-local-image -S 0 -M | tee $(AUTOMATE_TEST_OUT_DIR)/$(BIN)_$${i}_none_describe_local.log; \
	    $(LOAD_AFI); \
	    $(call RR_RECORDV, $(CMDLINE)) 2>&1 | tee $(AUTOMATE_TEST_OUT_DIR)/$(BIN)_$${i}_recordv.log; \
	    $(LOAD_AFI); \
	    $(call RR_REPLAYV, $(CMDLINE)) 2>&1 | tee $(AUTOMATE_TEST_OUT_DIR)/$(BIN)_$${i}_replayv.log; \
	    $(RR_TOOL) -v --hbver2 -c validate_record.dump -c validate_replay.dump >$(AUTOMATE_TEST_OUT_DIR)/$(BIN)_$${i}_diff.txt 2>&1; \
	    for dump in record.dump validate_record.dump validate_replay.dump; do \
	      mv $${dump} $(AUTOMATE_TEST_OUT_DIR)/$(BIN)_$${i}_$${dump}; \
	    done \
	done
