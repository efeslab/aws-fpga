# This file contains the default configuration for the Intel PAC D5005 board
# using USM for the use with single precision floating point values.
# To use this configuration file, call cmake with the parameter
#
#     cmake [...] -DHPCC_FPGA_CONFIG="path to this file"
#


set(USE_MPI No CACHE BOOL "" FORCE)
set(USE_SVM No CACHE BOOL "" FORCE)
set(USE_HBM Yes CACHE BOOL "" FORCE)
set(FPGA_BOARD_NAME "p520_hpc_m210h" CACHE STRING "" FORCE)
set(AOC_FLAGS "-fpc -fp-relaxed -no-interleaving=default" CACHE STRING "" FORCE)

# STREAM specific options
# Defaults to a total of ~12GB data
set(DEFAULT_ARRAY_LENGTH 536870912 CACHE STRING "" FORCE)
set(VECTOR_COUNT 8 CACHE STRING "" FORCE)
set(GLOBAL_MEM_UNROLL 1 CACHE STRING "" FORCE)
set(NUM_REPLICATIONS 32 CACHE STRING "" FORCE)
set(DEVICE_BUFFER_SIZE 4096 CACHE STRING "" FORCE)
set(INTEL_CODE_GENERATION_SETTINGS ${CMAKE_SOURCE_DIR}/settings/settings.gen.intel.stream_kernels_single.s10mxhbm.py CACHE FILEPATH "" FORCE)

# Set the data type since optional vector types are used
set(DATA_TYPE float CACHE STRING "" FORCE)
set(HOST_DATA_TYPE cl_${DATA_TYPE} CACHE STRING "" FORCE)
if (VECTOR_COUNT GREATER 1)
    set(DEVICE_DATA_TYPE ${DATA_TYPE}${VECTOR_COUNT} CACHE STRING "" FORCE)
else()
    set(DEVICE_DATA_TYPE ${DATA_TYPE} CACHE STRING "" FORCE)
endif()
