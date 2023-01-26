HLS_DESIGN_DIR := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
HLS_DESIGN_SRC := $(wildcard $(HLS_DESIGN_DIR)*.cpp)
HLS_DESIGN_OBJ := $(HLS_DESIGN_SRC:.cpp=.o)
HLS_DESIGN_HEADER := $(wildcard $(HLS_DESIGN_DIR)*.h)

GENERATED_INPUT := $(HLS_DESIGN_DIR)random_passwords.txt
GENERATE_SCRIPT := $(HLS_DESIGN_DIR)generate_random_passwords.py
HLS_DESIGN_ALL_FILES := $(HLS_DEISNG_SRC) $(HLS_DESING_HEADER) $(GENERATED_INPUT)
HLS_DESIGN_COMPILER = $(CXX)
HLS_DESIGN_TEST_ENV :=
HLS_DESIGN_INPUT := $(GENERATED_INPUT)
# -B 30: replayv stalls easily.
# -B 1: less likely to stall
# may need some debugging later.
# The first guess is that the app issued PCIs 32 AW with burst of 8 while
# only 32W transferred. Stall due to insufficient buffer.
# A newer guess is that the replayer fifo is filled up by interleaving
# replayable packets as well as pure "loge" packets. Such optimizations can be
# applied to "twowayhandshake_replayer.sv"
HLS_DESIGN_TEST_ARGS := -f $(GENERATED_INPUT) -B 1
# 250 MHz
HLS_DESIGN_AGFI_ID := agfi-086380e95f307c702

$(GENERATED_INPUT): $(GENERATE_SCRIPT)
	cd $(HLS_DESIGN_DIR) && python2 $(GENERATE_SCRIPT) 500
