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
CFLAGS = -DCONFIG_LOGLEVEL=4 -std=gnu11 -g -Wall -Werror $(INCLUDES)

LDLIBS = -lfpga_mgmt

SRC = test_common.c test_3d_rendering.c
OBJ = $(SRC:.c=.o)

include ${CL_FPGARR_ROOT}/software/runtime/libfpgarr/Makefile.inc
CFLAGS += -I$(LIBFPGARR_PATH)

all: rendering bnn $(BIN)

rendering: $(OBJ) $(LIBFPGARR_ALL_FILES)
	$(CC) $(CFLAGS) -o test_3d_rendering test_3d_rendering.o test_common.o $(LIBFPGARR_SRC) $(LDFLAGS) $(LDLIBS)

clean:
	rm -f *.o test_3d_rendering outputs.txt

check_env:
ifndef SDK_DIR
    $(error SDK_DIR is undefined. Try "source sdk_setup.sh" to set the software environment)
endif
