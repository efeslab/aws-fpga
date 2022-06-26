# This file contains the default configuration for the Nallatech 520N board
# for the use with single precision floating point values.
# To use this configuration file, call cmake with the parameter
#
#     cmake [...] -DHPCC_FPGA_CONFIG="path to this file"
#


set(USE_MPI No CACHE BOOL "" FORCE)
set(USE_SVM No CACHE BOOL "" FORCE)
set(USE_HBM No CACHE BOOL "" FORCE)
set(FPGA_BOARD_NAME "p520_hpc_sg280l" CACHE STRING "" FORCE)
set(AOC_FLAGS "-fpc -fp-relaxed -no-interleaving=default" CACHE STRING "" FORCE)

# allow custom kernels to synthesize current non pivoting version
set(USE_CUSTOM_KERNEL_TARGETS Yes CACHE BOOL "" FORCE)

# LINPACK specific options
set(DEFAULT_MATRIX_SIZE 1024 CACHE STRING "Default matrix size" FORCE)
set(GLOBAL_MEM_UNROLL 16 CACHE STRING "Unrolling factor that is used for all loops in the kernels" FORCE)
set(LOCAL_MEM_BLOCK_LOG 10 CACHE STRING "Used to define the width and height of the block stored in local memory" FORCE)
set(REGISTER_BLOCK_LOG 4 CACHE STRING "Size of the block that will be manipulated in registers" FORCE)

