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

ifndef VIVADO_TOOL_VERSION
$(error Environment variable VIVADO_TOOL_VERSION not set. please source hdk_setup.sh)
else
$(info VIVADO_TOOL_VERSION = $(VIVADO_TOOL_VERSION))
endif

export TEST ?= test_null
export C_TEST ?= test_null

export SCRIPTS_DIR = $(shell dirname $(realpath $(firstword $(MAKEFILE_LIST))))
export CL_ROOT = $(realpath $(SCRIPTS_DIR)/../..)
export SDK_DIR = $(AWS_FPGA_REPO_DIR)/sdk

export C_COMMON_DIR        = $(HDK_COMMON_DIR)/software
export C_SDK_USR_INC_DIR   = $(SDK_DIR)/userspace/include
export C_SDK_USR_UTILS_DIR = $(SDK_DIR)/userspace/utils
export C_INC_DIR  = $(CL_ROOT)/software/runtime
export C_SRC_DIR  = $(CL_ROOT)/software/runtime

export TEST_NAME =  $(CL_ROOT)/verif/tests/$(TEST).sv

ifdef HLS_DESIGN
  export HLS_DESIGN_ROOT = $(CL_ROOT)/design/hls_accel/$(HLS_DESIGN)
endif
ifeq ($(C_TEST),test_null)
  ifndef HLS_DESIGN
    export C_TEST_NAME = $(HDK_COMMON_DIR)/software/src/$(C_TEST).c
  else
    # HLS runs will include Makefile.inc
    export C_TEST_NAME =
  endif
else
  export C_TEST_NAME = $(C_SRC_DIR)/$(C_TEST).c
endif

export SIM_ROOT = $(CL_ROOT)/verif/sim/$(SIMULATOR)

ifeq ($(C_TEST),test_null)
  ifdef HLS_DESIGN
    export SIM_DIR = $(SIM_ROOT)/test_$(HLS_DESIGN)
  else
    ifeq ($(AXI_MEMORY_MODEL), 1)
      ifeq ($(ECC_DIRECT), 1)
          export SIM_DIR = $(SIM_ROOT)/$(TEST)_sv_fast_ecc_direct
      else
        ifeq ($(ECC_RAND), 1)
          export SIM_DIR = $(SIM_ROOT)/$(TEST)_sv_fast_ecc_rnd
        else
          ifeq ($(DDR_BKDR), 1)
           export SIM_DIR = $(SIM_ROOT)/$(TEST)_sv_fast_bkdr
          else
           export SIM_DIR = $(SIM_ROOT)/$(TEST)_sv_fast
          endif
        endif
      endif
    else
     ifeq ($(ECC_DIRECT), 1)
          export SIM_DIR = $(SIM_ROOT)/$(TEST)_sv_ecc_direct
      else
        ifeq ($(ECC_RAND), 1)
          export SIM_DIR = $(SIM_ROOT)/$(TEST)_sv_ecc_rnd
        else
          ifeq ($(DDR_BKDR), 1)
           export SIM_DIR = $(SIM_ROOT)/$(TEST)_sv_bkdr
          else
           export SIM_DIR = $(SIM_ROOT)/$(TEST)_sv
          endif
        endif
      endif
    endif
  endif
else
  export SIM_DIR = $(SIM_ROOT)/$(C_TEST)_c
endif

export XILINX_IP   = $(HDK_SHELL_DESIGN_DIR)/ip
export SH_LIB_DIR  = $(HDK_SHELL_DESIGN_DIR)/lib
export SH_INF_DIR  = $(HDK_SHELL_DESIGN_DIR)/interfaces
export SH_SH_DIR   = $(HDK_SHELL_DESIGN_DIR)/sh_ddr/sim

SV_TEST_LIST = test_hello_world
C_FILES      = $(C_SDK_USR_UTILS_DIR)/sh_dpi_tasks.c $(C_COMMON_DIR)/src/fpga_pci_sv.c

# setup fpgarr
include ${CL_FPGARR_ROOT}/software/runtime/libfpgarr/Makefile.inc
C_FILES += $(LIBFPGARR_SRC)
VCS_OPT = -CFLAGS "-I$(LIBFPGARR_PATH)"
VCS_OPT += -CFLAGS "-I$(XILINX_HLS)/include"
# setup libfpgarropencl
include ${CL_ROOT}/software/runtime/libfpgarropencl/Makefile.inc
C_FILES += $(LIBFPGARROPENCL_SRC)
VCS_OPT += -CFLAGS "-I$(LIBFPGARROPENCL_INCLUDE) -I$(XILINX_XRT)/include"
ifdef HLS_DESIGN
  include ${C_SRC_DIR}/$(HLS_DESIGN)/Makefile.inc
  C_FILES += $(HLS_DESIGN_SRC)
  ifneq ($(HLS_DESIGN_USE_OPENCL),1)
    C_FILES += $(C_SRC_DIR)/test_common.c
  endif
  VCS_OPT += -CFLAGS "-DRR_POLLING_INTERVAL=100"
  VCS_OPT += -CFLAGS "-I$(C_SRC_DIR)/$(HLS_DESIGN)"
  VCS_OPT += -CXXFLAGS "-lminizip" -CXXFLAGS "-lz" -CXXFLAGS "-lstdc++" -CXXFLAGS "-lcrypto"
  VCS_OPT += -CFLAGS "-lminizip" -CFLAGS "-lz" -CFLAGS "-lcrypto"
endif

ifeq ($(XCHK), 1)
  all:	make_sim_dir compile_chk run
else
  all:	make_sim_dir compile run
endif

include $(HDK_COMMON_DIR)/verif/tb/scripts/Makefile.common.inc
