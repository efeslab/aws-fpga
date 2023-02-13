#!/usr/bin/python3
import matplotlib as mpl
import matplotlib.pyplot as plt
import os
import argparse
from utils import get_resource_util
from config import SWEEP_INTERFACES_MAP
from config import sweep_configurations

mpl.rcParams['pdf.fonttype'] = 42

HOME = os.getenv("HOME")
parser = argparse.ArgumentParser(
    description="Reproduce the Figure.7 in the paper")
parser.add_argument('--prebuilt-synth', type=str, default=f"{HOME}/aws-fpga-prebuilt",
                    help="The git repo that contains synthesis results (default: %(default)s)")
parser.add_argument('-o', '--output', type=str, default="resource_overhead_sweep.pdf",
                    help="Output figure path (default: %(default)s)")

args = parser.parse_args()
FPGA_RR_SYNTH_PATH = f"{args.prebuilt_synth}/hdk/cl/examples/cl_fpgarr/build/reports/"

# sanity check
assert(os.path.exists(FPGA_RR_SYNTH_PATH))

t = []  # total traced width
lut = []
ff = []
bram = []
name = []
# textdelta and texty are manually tuned figure label placements
textdelta = [20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20]
texty = [2.15, 2.45, 2.76, 4.02, 4.23, 4.55, 4.79, 1.45, 0.60, 0.15, 0.15]


for bench, benchID in sweep_configurations:
    name.append(bench)
    # for resource overhead
    rpt = FPGA_RR_SYNTH_PATH + benchID + ".hierarchical_utilization_route_design.rpt"
    logic_overhead, reg_overhead, ram_overhead = get_resource_util(rpt)
    lut.append(logic_overhead)
    ff.append(reg_overhead)
    bram.append(ram_overhead)
    # for traced width
    interface_components = bench.split('+')
    t.append(
        sum([SWEEP_INTERFACES_MAP[intf].total_width for intf in interface_components]))

fig, ax = plt.subplots(1, 1, figsize=(6.8, 4.5))

for i in range(0, len(t)):
    ax.axvline(x=t[i], ymin=0, ymax=100, color='gray',
               linewidth=1, dashes=(5, 3))
    ax.text(x=t[i]+textdelta[i], y=texty[i], s=name[i],
            rotation="vertical", fontsize=12)

ax.plot(t, lut, "o-", label="LUT")
ax.plot(t, ff, "o-", label="FF")
ax.plot(t, bram, "o-", label="BRAM")
ax.set_xlabel('Total Monitored Width (bits)', fontsize=16)
ax.set_ylabel('Resource Overhead (%)', fontsize=16)
ax.set_ylim([0, 9.2])
ax.tick_params(axis="y", labelsize=13)
ax.tick_params(axis="x", labelsize=13)

handles, labels = ax.get_legend_handles_labels()
leg = ax.legend(handles, labels, fontsize=12, ncol=1, loc='upper left')

fig.tight_layout()
plt.savefig(args.output)
# plt.show()
