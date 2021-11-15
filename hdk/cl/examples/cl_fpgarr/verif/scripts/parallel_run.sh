# Usage: Change the bellow configurations and run `${SHELL} ${0}` in the same
# dir as this file locates

# Configurations
SIMDIR=../sim/vcs
NUM_RUNS=2
NJOBS=80
TESTBENCH=test_rr_parse_replay_trace_tb
TESTBENCH_DIR=${SIMDIR}/${TESTBENCH}_sv
seq 1 ${NUM_RUNS} | parallel -a - -j ${NJOBS} ${TESTBENCH_DIR}/simv \
  -l ${TESTBENCH_DIR}/parallel_job-{1}.log \
  +ntb_random_seed_automatic \
  +vpdfile+${TESTBENCH_DIR}/parallel_job-{1}.vpd
