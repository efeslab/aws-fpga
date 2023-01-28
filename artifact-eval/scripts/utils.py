import statistics as stat
from sh import grep
from typing import List

def geomean_of_percent(data: List[float]):
    scaledRatio = [100 + p for p in data]
    return stat.geometric_mean(scaledRatio) - 100

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
