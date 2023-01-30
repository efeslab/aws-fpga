# Introduction
This is the testing case study (S5.3), which is based on an unchanged buggy implementation of `axi_atop_filter` from [pulp-platform](https://github.com/pulp-platform/axi/commit/a8a3a2a322602399bfa3b6bda2e1f754994751f4).

The `design` directory contains the [verilog implementation](design/axi_atop_filter) of `axi_atop_filter` and a simple echo server application built upon it.

The following experiments are expected to take < 20min

# Experiments

(0) Get a command-line access to the `aws` server

(1) Go to the corresponding software directory
```bash
# assuming we were at the git repo root dir aws-fpga
cd hdk/cl/examples/cl_axi_atop_filter/software/runtime
```

(2) Flash a prebuilt FPGA image of the buggy implementation
```bash
make load_buggy
```

(3) Run the application with different record/replay configurations
```bash
make record_replay
```
We are very unlikely to trigger the bug now because the problematic corner case is rare (yet valid according to the protocol specification).

(4) Check the expected output messages and files
```bash
# check the stdout of the executions without any record/replay, where incorrect values are all zero.
# Everything looks good!
less /mnt/output/axi_atop_filter_none.log
# check the stdout of the executions with recording and validation enabled
less /mnt/output/axi_atop_filter_recordv.log
# check the recorded trace was replayed successfully on the actual FPGA
less /mnt/output/axi_atop_filter_diff.txt
```

(5) Mutate the recorded trace to test the corner case
```bash
# do the mutation
make mutate
# check what has been mutated
# Basically for each write operation, the address transaction (AW) is reordered after the first write-data transaction (W)
vimdiff /mnt/output/axi_atop_filter_record.dump.txt /mnt/output/axi_atop_filter_record_mutated.dump.txt
```

(6) Replay the mutated trace
```bash
make replay_mutation
```
The replay is expected to enter a deadlock state, where VIDI would report the trace to only be replayed to a certain amount and not making any progress.
Then use `ctrl+c` to abort the replay.

(7) Flash a prebuilt FPGA image with the bug fixed and replay again
```bash
make load_fixed
make replay_mutation
```
The replay is expected to finish soon. We can then conclude the bugfix does handle the corner case correctly.
