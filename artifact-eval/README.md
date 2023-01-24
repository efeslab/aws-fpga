# Artifact for ASPLOS'23 submission "Vidi: Record Replay for Reconfigurable Hardware"

This repository consists of both the hardware and software components of Vidi, an FPGA record/replay framework.
Note that this artifact was developed based on a fork of the official AWS EC2 FPGA Development Kit repository and they share most of the setup process and workflow in common.
So feel free to explore the rest of the official aws-fpga documentation for FAQ/troubleshooting, alternative setup options, latest updates, etc.

To reproduce the major results in the paper, this repository involves two type of experiments: in simulation and deployed on AWS F1 instances. Each requires a different set of dependencies and setup.

## Dependencies
### Hardware Dependencies

For simulation and synthesis (not working with the FPGA device), we need an AWS EC2 instance at least the size of z1d.xlarge/c5.4xlarge or an equivalent server.

For experiments deployed to run on the actual FPGA device, we need an AWS EC2 f1.2xlarge instance.

### Software Dependencies
- Ubuntu 20.04
- g++ with c++17 support
- python3
- make

For simulation and synthesis, we also need:
- Xilinx 2020.2 tools and licenses
- VCS-2020.12

### Remote Access
Since we require proprietary software, specialized hardware as well as AWS nodes, we will provide each reviewer remote access to two servers:

1. A develop server (refered as `dev`) with pre-installed software for simulation and synthesis. GUI access to the `dev` will also be provided via VNC to run certain FPGA dev tools.
2. An AWS EC2 f1.2xlarge instance (referred as `aws`) to run experiments on the actual FPGA hardware.

As per instructions, access information will be distributed via the AE chairs.

## Get Started

### Installation
Clone the `asplos23-ae` branch of this repository:
```bash
# skip the clone if you are using servers provided by us
git clone https://github.com/efeslab/aws-fpga
```
In the `dev` server, enable the hardware development environment on **EVERY NEW** command-line shell:
```bash
cd aws-fpga
source hdk_setup.sh
```
**NOTE:** To simplify the hdk and sdk setup process, we recommend using **tmux**. In particular, you can enable the corresponding environment before invoking tmux, then every new command line window spawned from tmux does not need to be setup again.

**NOTE:** During the first setup, the script will run longer than subsequent runs because necessary software components will be compiled and installed.

In the `aws` server, enable the FPGA runtime on **EVERY NEW** command-line shell in a similar way:
```bash
cd aws-fpga
source sdk_setup.sh
```
Also check whether the FPGA driver has been loaded:
```bash
lsmod | grep xdma
# if not loaded, run the following commands
cd aws-fpga/sdk/linux-kernel-drivers/xdma
sudo make install
```

**NOTE:** `sdk_setup.sh` requires root permission to install certain components, so you may need to deal with sudo prompt if it is necessary.

**NOTE:** The rest of this documentation will assume the current directory is the root of the git repo and the setup scripts have been sourced in the corresponding server.

### Basic Simulation Test
Simulate a trace recording of the S5.2 debugging case study.

(0) Get a command-line access to the `dev` server.

(1) Go to the corresponding simulation directory.
```bash
# we were at the git repo root dir aws-fpga
cd hdk/cl/examples/cl_axis_fifo_buggy/verif/scripts
```

(2) Compile and run the simulation with VIDI to record both execution and validation trace (< 2min).
```bash
make AXI_MEMORY_MODEL=1 VCS=1 C_TEST=test_common RR_MODE=recordv
```

(3) Check the expected output messages.

There will be plenty of messages as well as warnings printed by the simulation toolchain/library.
The simulation successfully finishes if you see a "V C S   S i m u l a t i o n   R e p o r t" message at the end of the simulation that summarizes basic runtime, memory usage, etc.
Before that message, you should also see a box of "TEST REPORT", where describes the experiment setup and results:
  1. "buffer alignment" is 8-byte, which represents the alignment of the buffer allocated to communicate with FPGA.
  2. "delay mode" is `imm_start`, which represents the echo server is started before DMA is initiated.
  2. "total values" is "8192" and the rest of the counters are all zero, which means the echo server reponded with correct answers.

(4) Check the expected output files.
```bash
# we are still in the verif/scripts directory
ls ../sim/vcs/test_common_c/*.dump
```
There should be two trace files: `record.dump` contains the execution trace that will be used for replay; `validate_record.dump` contains application output traces that will be used to validate the correctness of the replay;

(5) Well done!

### Basic Synthesis Test
Synthesize the S5.2 debugging case study for FPGA deployment. Since we will provide prebuilt synthesis results, feel free to skip this step if you do not plan to check the synthesis process.

(0) Get a command-line access to the `dev` server.

(1) Go to the corresponding synthesis directory.
```bash
# we were at the git repo root dir aws-fpga
cd hdk/cl/examples/cl_axis_fifo_buggy/build/scripts
```

(2) Synthesize the RTL design with 250MHz clock (also including all optimizations and place & route)
```bash
export CL_DIR=${HOME}/aws-fpga/hdk/cl/examples/cl_axis_fifo_buggy/
./aws_build_dcp_from_cl.sh -strategy VIDI -clock_recipe_a A1
```

(3) Check the expected output messages.

The above command will create background synthesis job. The synthesis progress will be redirected to a timestamped log file whose path will be printed out.
Assuming the log file is `${TIMESTAMP}.nohup.out`, you can check synthesis progress by running
```bash
tail -f ${TIMESTAMP}.nohup.out
# NOTE: use ctrl+c to exit
```

(4) Check the prebuilt synthesis results.

Since the whole synthesis process normally take 5~8 hrs, we provide prebuilt synthesis results as well as FPGA images.
And we expect artifact reviewers to not complete the synthesis of any applications in the reviewing process.
To check the prebuilt synthesis results of the S5.2 application:
```bash
ls ~/aws-fpga-prebuilt/hdk/cl/examples/cl_axis_fifo_buggy/build/scripts
```
You should find many synthesis logs that follow a similar `${TIMESTAMP}.*` format.
Note that the `~/aws-fpga-prebuilt` is essentially another copy of the git repo and contains the synthesis history of all applications used in the rest of this document.

(5) Abort the synthesis.

Since we will use the prebuilt synthesis results to reproduce all synthesis-related results, let us abort the current basic synthesis test.
```bash
pkill -f ${TIMESTAMP}
```

### Basic Test on the actual FPGA
Deploy the S5.2 debugging case study to AWS F1 and run it on hardware.

(0) Get a command-line access to the `aws` server.

(1) Go to the software directory that works with the actual FPGA hardware.
```bash
# we were at the git repo root dir aws-fpga
cd hdk/cl/examples/cl_axis_fifo_buggy/software/runtime
```

(2) Deploy the prebuilt FPGA image and run the software component.
```bash
make correct_run
```

(3) Check the expected output.

In this and all following tests, you can safely ignore the warning message:
> WARNING: RR_CSR_VERSION mismatches!!!!!

The output is expected to have:
1. Logs of a few compilation commands
2. Command-line of flashing an FPGA image: `sudo fpga-load-local-image ...`
3. Command-line of invoking the application: `sudo RR_MODE=none  ./axis_fifo_hw.elf 4096 imm_start`
4. Some logs from the VIDI runtime, which can usually ignored if there is no error
5. Application output, which should show a box of "TEST REPORT" in this particular test. It should report a non-zero "total values" and a zero "incorrect values".

## Evaluation
### Experimental Workflow
#### Overview

We follow the directory structure of the official AWS FPGA develop repository.
Each application has a directory under `hdk/cl/examples/${APP}`.
And each application diretory has the following subdirectories:

  - `hdk/cl/examples/${APP}/design` contains the RTL implementation of the FPGA component
  - `hdk/cl/examples/${APP}/software` contains c/c++ implementation of the software component, used by both simulations and executions on actual FPGA
  - `hdk/cl/examples/${APP}/build` contains synthesis scripts, including scripts that upload the synthesized design to AWS
  - `hdk/cl/examples/${APP}/verif` contains simulation scripts

The implementation of different evaluation targets and their locations:

  - VIDI FPGA shim-layer: `hdk/cl/examples/cl_fpgarr/cl_fpgarr*`
  - VIDI software runtime: `hdk/cl/examples/cl_fpgarr/software/runtime/libfpgarr`
  - VIDI trace analysis/post-process: `hdk/cl/examples/cl_fpgarr/software/runtime/rr_tool`
  - S5.2 debugging case study: `hdk/cl/examples/cl_axis_fifo_buggy`
  - S5.3 testing case study: `hdk/cl/examples/cl_axi_atop_filter_buggy`
  - RTL application, DRAM DMA: `hdk/cl/examples/cl_fpgarr/cl_dram_dma*`
  - HLS applications: `hdk/cl/examples/cl_hls`
    - The original HLS code: `hdk/cl/examples/cl_hls/gen/${APP}`
    - The compiled RTL code: `hdk/cl/examples/cl_hls/design/hls_accel/${APP}`

#### Simulation Workflow (on the `dev` server)

Simulation is managed by Makefile under each application's `hdk/cl/examples/${APP}/verif/scripts` directory.
A typical simulation is launched by
```bash
make AXI_MEMORY_MODEL=1 VCS=1 C_TEST=xxx RR_MODE=xxx [compile|run|view]
```
Where:
  - `AXI_MEMORY_MODEL=1` opts in to use a less accurate yet faster simulation model for memory modules
  - `VCS=1` chooses the VCS simulator
  - `C_TEST=xxx` specifies the C source file (i.e., the software part of the application) that drives the simulation
  - `RR_MODE=xxx` configures VIDI to operate in different modes. See the [customization section](#experimentation-customization) for more details.
  - make targets can be the following
    - `compile`: compile the application and link against simulation libraries
    - `run`: run the simulation binary without re-compile anything
    - `view`: open waveform viewer to look into the simulation (NOTE: you need to have a desktop instead of pure command-line interfaces)
    - empty: `compile` then `run`

Simulation runs will create a separate work directory `hdk/cl/examples/${APP}/verif/sim/vcs/${TEST}`, which contains compilation logs, execution logs, waveform trace (`*.vpd`) and VIDI traces (i.e., `record.dump`, `validate_{record,replay}.dump`)

#### Synthesis Workflow (on the `dev` server)

Synthesis is managed by shell and tcl scripts under each application's `hdk/cl/examples/${APP}/build/scripts` directory.
A typical synthesis is launched by
```bash
export CL_DIR=${HOME}/aws-fpga/hdk/cl/examples/${APP}
./aws_build_dcp_from_cl.sh -strategy VIDI -clock_recipe_a A1
```
Where `-strategy` chooses a predefined set of synthesis parameters and `-clock_recipe` configs the clock frequency.
In this evaluation, we always use "clock group A, recipe A1", which is 250MHz. For other clock options, please check the [AWS doc](../hdk/docs/clock_recipes.csv).

A synthesis job will also generate the following files:
  - `hdk/cl/examples/${APP}/build/scripts/${TIMESTAMP}.nohup.out` is the stdout log
  - `hdk/cl/examples/${APP}/build/reports` contains various synthesis reports (e.g., utilization and timing analysis)
  - `hdk/cl/examples/${APP}/build/checkpoints` contains various synthesized images that can be uploaded to AWS

We don't expect reviewers to completely synthesize any applications. Prebuilt synthesis results/reports will be provided for evaluation.

#### Experiment Workflow on the actual FPGA (on the `aws` server)

Experiments on the actual FPGA hardware are managed by Makefile under each application's `hdk/cl/examples/${APP}/software/runtime` directory.
We will provide different make targets to automate different experiments, which will be detailed later.
The output of experiments will be stored in an ephemeral directory `/mnt/output`, which will be wiped out everytime we stop the AWS instance.
Unless explicitly specified, the output files are mostly named after the following pattern:
1. `/mnt/output/${APP}_none.log`: the stdout of executions without any record/replay (i.e., baseline)
2. `/mnt/output/${APP}_recordv.log`: the stdout of executions with recording and validation enabled
3. `/mnt/output/${APP}_record.dump`: the recorded trace that are essential for replay
4. `/mnt/output/${APP}_validate_record.dump`: the recorded reference trace that are used to validate the correctness of the replay
5. `/mnt/output/${APP}_replayv.log`: the stdout of executions with replaying and validation enabled
6. `/mnt/output/${APP}_validate_replay.dump`: the recorded trace that are used to validate the correctness of the replay
7. `/mnt/output/${APP}_diff.txt`: a report of the correctness of the replay, summarizing differences between the record and replay

To avoid rerunning experiments, please make sure to examine (or download to `dev`) the output directory during each reproducible experiments before stopping the AWS instance.

### Evaluation and Expected Results

#### S5.2 Debugging Case Study
Please check [its own doc](../hdk/cl/examples/cl_axis_fifo_buggy/README.md)
#### S5.3 Testing Case Study
Please check [its own doc](../hdk/cl/examples/cl_axi_atop_filter_buggy/README.md)
#### S5.4 Effectiveness of Vidi
In this experiment, we are going to run the rest of the benchmarks and confirm VIDI can correctly record and replay various applications.
We expect the experiment to last for about 3-4 hrs.

(0) Get a command-line access to the `aws` server.

**NOTE:** tmux is **strongly recommended** here because the experiments would be long and vulnerable to potential network issues.

(1) Run the DRAM DMA. Repeat 5 times.
```bash
# assume we were at the git repo root dir aws-fpga
cd hdk/cl/examples/cl_fpgarr/software/runtime
make NUM_TEST=5 test
```
Note that in paper we report numbers based on 10 trials. To speed up the artifact evaluation, we recommend 5 trials here. But the number of trials is configurable through the make variable `NUM_TEST`.

(2) Run all HLS benchmarks. Repeat 5 times.
```bash
cd hdk/cl/examples/cl_hls/software/runtime
make NUM_TEST=5 test_all
```

(3) Check output.

For each application `${APP}`, the expected outcomes are:
1. `/mnt/output/${APP}_none.log` and `/mnt/output/${APP}_recordv.log` show that the applications have the same output when recording is enabled (e.g., check with vimdiff).
2. `/mnt/output/${APP}_diff.txt` shows that the applications are replayed correctly (i.e., no happens-before violation nor output content mismatch).

(4) Copy the output files (excluding traces) to `dev` for further analysis

Run the following commands on the `dev` server
```bash
rsync -avP -f '- *.dump' ubuntu@efesfpga.ddns.net:/mnt/output/ ~/aws-output/
```

#### S5.5 Efficiency of Vidi (Runtime Performance Overhead and Storage Benefit)

We will need the experiment output files (should have been copied to `~/aws-output`) from the above S5.4 evaluation.

(0) Get a command-line access to the `dev` server

(1) Reproduce Table.1, which reports the runtime performance overhead and storage benefit of the corase-grained input recording.
```bash
# assume we were at the git repo root dir aws-fpga
cd artifact-eval
python3 scripts/table1.py --expr-output ~/aws-output | column -s, -t
```

#### S5.5 Efficiency of Vidi (Resource Overhead)

We will need the prebuilt syntheis results at `~/aws-fpga-prebuilt`.

(0) Get a command-line access to the `dev` server

(1) Reproduce Table.2

The data used here are synthesis reports of FPGA images of each application that we have run on the actual FPGA in the previous experiment.
```bash
python scripts/table2.py --prebuilt-synth ~/aws-fpga-prebuilt | column -s, -t
```

(2) Reproduce Figure.7

The data used here are synthesis reports of the DRAM DMA application with VIDI configured to trace different sets of interfaces.
With the prebuilt synthesis results, we can easily generate the Figure.7.
```bash
# assume we were at the git repo root dir aws-fpga
cd artifact-eval
python scripts/figure7.plot.py --prebuilt-synth ~/aws-fpga-prebuilt
```
A `resource_overhead_sweep.pdf` will be generated and you can download it via `scp` and double check.

**NOTE:** The following script was used to generate those configurations if you want to synthesis from scratch:
```bash
# assume we were at the git repo root dir aws-fpga
cd hdk/cl/examples/cl_fpgarr/design
# the following is just one example config "sda+pcim"
# check `./scripts/sweep_mergetree.sh --help` for more options
./scripts/sweep_mergetree.sh --sda=trace --ocl=fuse --bar1=fuse --pcim=trace --pcis=fuse
```

### Experimentation Customization
#### Customize the record/replay configurations
The environment variable `RR_MODE` specifies the configuration of VIDI. Allowed values are:
  - "none": disable record and replay, application traffic will bypass VIDI. Same as the configuration (R1) in S5.1
  - "record": enable record, disable replay. Only record the trace essential for replay (i.e., `record.dump`) and trash the validation trace (i.e., `validate_record.dump`) that can confirm the correctness of the replay.
  - "recordv": enable record, disable replay. Record both `record.dump` and `validate_record.dump`. Same as the configuration (R2) in S5.1
  - "replay": disable record, enable replay. Only replay the `record.dump` trace and trash the validation trace (i.e., `validate_replay.dump`) that can confirm the correcteness of the replay.
  - "replayv": disable record, enable replay. Both replay `record.dump` and record `validate_replay.dump`. Same as the configuration (R3) in S5.1

To change the path where trace should be dumped to or read from, set the following environment variables:
  - `RR_RECORD_PATH`: default is `record.dump`
  - `RR_VALIDATE_RECORD_PATH`: default is `validate_record.dump`
  - `RR_VALIDATE_REPLAY_PATH`: default is `validate_replay.dump`

#### Customize a new AWS F1 FPGA application to use VIDI

If tracing the standard five AXI interfaces provided by the shell, the new application can simply include the following files to their workflow:
  - include sim header: `${CL_FPGARR_ROOT}/verif/scripts/cl_fpgarr_sim.f`
    - example: `hdk/cl/examples/cl_axis_fifo_buggy/verif/scripts/top.vcs.f`
  - include synth header: `${CL_FPGARR_ROOT}/build/scripts/cl_fpgarr_src.tcl` and `${CL_FPGARR_ROOT}/build/scripts/cl_fpgarr_synth.tcl`
    - example: `hdk/cl/examples/cl_axis_fifo_buggy/build/scripts/{create_dcp_from_cl.tcl,synth_cl_axis_fifo.tcl}`

To extend VIDI to trace additional AXI interfaces or application internal AXI buses, check the following git commits:
  - Example changes that support tracing the DDR interface on F1: `git show 38d4d39a905b52d878dcafdeada4518d547a60b0`
  - Example changes that support tracing an application internal bus: `git show 4645c85a54729037e4350e2da17b3b119f256ef9`
