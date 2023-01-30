#/usr/bin/python3

import os
import argparse
from sh import grep, tail
from utils import get_resource_util
from config import benchmarks

HOME = os.getenv("HOME")
parser = argparse.ArgumentParser(description="Reproduce the Table.2 in the paper")
parser.add_argument('--prebuilt-synth', type=str, default=f"{HOME}/aws-fpga-prebuilt", help="The git repo that contains synthesis results (default: %(default)s)")

args = parser.parse_args()
HLS_SYNTH_PATH = f"{args.prebuilt_synth}/hdk/cl/examples/cl_hls/build/reports/"
FPGA_RR_SYNTH_PATH = f"{args.prebuilt_synth}/hdk/cl/examples/cl_fpgarr/build/reports/"

# sanity check
assert(os.path.exists(HLS_SYNTH_PATH))
assert(os.path.exists(FPGA_RR_SYNTH_PATH))

print("{},{},{},{}".format(
    "benchmark", "logic_overhead(%)", "reg_overhead(%)", "ram_overhead(%)"))

for bench, benchID in benchmarks.items():
    if bench == "test_dram_dma":
        rpt = FPGA_RR_SYNTH_PATH + benchID + ".hierarchical_utilization_route_design.rpt"
    else:
        rpt = HLS_SYNTH_PATH + benchID + ".hierarchical_utilization_route_design.rpt"
    logic_overhead, reg_overhead, ram_overhead = get_resource_util(rpt)

    print("{},{},{},{}".format(
        bench,
        logic_overhead, reg_overhead, ram_overhead))
