# Introduction
This is the debugging case study (S5.1), which is based on the [Frame FIFO bug](https://github.com/alexforencich/verilog-axis/commit/3d90e80da8e60daf5727e003d3b059e9b21b41da) presented in a prior [bug survey](https://github.com/efeslab/hardware-bugbase/tree/bugs/d4-buffer-overflow-frame-fifo).

The `design` directory contains the [verilog implementation](design/axis_fifo.v) of the buggy Frame FIFO.

# Experiments

## Setup

### The correct run
Let us first run this application without triggering the bug.
```make
make correct_run
```
### Bug1: Unaligned DMA access

```make
make bug_dma_alignment
```

### Bug2: Delayed Start
1. run
```make
make bug_delayed_start
```
2. check output
3. check losscheck results in vivado ILA
  a. setup remote ILA access on the F1 VM
  ```
  # in one terminal
  sudo /opt/xilinx/HWSRVR/bin/hw_server
  # in another terminal
  sudo fpga-start-virtual-jtag -P 10201 -S 0
  ```
  b. open vivado in the dev server
  ```bash
  vivado -mode tcl -source losscheck.jtag.ila.tcl
  ```
