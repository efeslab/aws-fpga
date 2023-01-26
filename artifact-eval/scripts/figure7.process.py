#/usr/bin/python3

from os import listdir
from os.path import isfile, join
from sh import grep, tail
import numpy as np

FPGA_RR_SYNTH_PATH="/mnt/storage/gefeizuo/FPGA/FPGARR/aws-fpga/hdk/cl/examples/cl_fpgarr/build/reports/"
benchmarks = {
        "sda":"22_06_26-041253",
        "sda+ocl":"22_06_26-131929",
        "pcim":"22_06_28-035704",
        "sda+pcim":"22_06_28-050150",
        "sda+ocl+bar1":"22_06_26-134359",
        "sda+ocl+pcim":"22_06_28-052116",
        "sda+ocl+bar1+pcim":"22_06_26-141449",
        "pcim+pcis":"22_06_28-053205",
        "sda+pcim+pcis":"22_06_28-054119",
        "sda+ocl+pcim+pcis":"22_06_28-055119",
        "sda+ocl+bar1+pcim+pcis":"22_06_26-210743"
}

def get_resource_util(f):
    rr = 0
    cl = 1
    sh = 2
    logic = []
    reg = []
    ram = []
    res = grep("-w", " CL ", f).replace(" ", "").splitlines()
    res.append(grep("-w", "static_sh", f).replace(" ", "").splitlines()[0])
    total_logic = 1180984
    total_reg = 2361968
    total_ram = 2160
    for l in res:
        l = l.split("|")
        logic.append(int(l[5]))
        reg.append(int(l[9]))
        ram.append(int(l[10]) + int(l[11])/2.0)
    logic_overhead = float(logic[rr] - logic[cl]) / float(total_logic - logic[sh]) * 100
    reg_overhead = float(reg[rr] - reg[cl]) / float(total_reg - reg[sh]) * 100
    ram_overhead = float(ram[rr] - ram[cl]) / float(total_ram - ram[sh]) * 100
    return logic_overhead, reg_overhead, ram_overhead

print("{},{},{},{}".format(
    "benchmark", "logic_overhead(%)", "reg_overhead(%)", "ram_overhead(%)"))
for bench in benchmarks:
    rpt = FPGA_RR_SYNTH_PATH + benchmarks[bench] + ".hierarchical_utilization_route_design.rpt"
    logic_overhead, reg_overhead, ram_overhead = get_resource_util(rpt)

    print("{},{},{},{}".format(
        bench,
        logic_overhead, reg_overhead, ram_overhead))
