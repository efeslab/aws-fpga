#/usr/bin/python3

from os import listdir
from os.path import isfile, join
from sh import grep, tail
import numpy as np

#OUTPUT_DIR = "/tmp/output/"
OUTPUT_DIR = "/tmp/fpgarr.eval/"
HLS_SYNTH_PATH="/mnt/storage/gefeizuo/FPGA/FPGARR/aws-fpga/hdk/cl/examples/cl_hls/build/reports/"
FPGA_RR_SYNTH_PATH="/mnt/storage/gefeizuo/FPGA/FPGARR/aws-fpga/hdk/cl/examples/cl_fpgarr/build/reports/"
NUM_RUNS = 10
benchmarks = {
        "test_dram_dma":"21_12_09-060616",
        "3d_rendering":"21_12_09-061040",
        "bnn":"21_12_09-064818",
        "digit_recognition":"21_12_09-224235",
        "face_detection":"21_12_10-211150",
        "spam_filter":"21_12_10-213413",
        "optical_flow":"21_12_11-014936",
        "sssp":"21_12_11-204801",
        "sha256":"21_12_11-233015",
        "mobilenet":"21_12_12-185349"
}

def get_elaspsed_ns(f):
    elapsed_time = grep("RR pre_rr->post_rr, elapsed ns:", f).split()[-1]
    user_elapsed_time = grep("RR user timer, elapsed ns:", f).split()[-1]
    if int(user_elapsed_time) == 0:
        return int(elapsed_time)
    else:
        return int(user_elapsed_time)

def get_hb_violation(f):
    res = tail("-n1", f).replace(":", " ").replace(","," ").split()
    hb_mismatches = float(res[6].replace("%", "").replace("(", " ").replace(")", " ").split()[1])
    total_violations = float(res[9].replace("%", "").replace("(", " ").replace(")", " ").split()[1])
    content_mismatches = float(res[-1].replace("%", "").replace("(", " ").replace(")", " ").split()[1])
    return hb_mismatches, total_violations, content_mismatches

def get_record_size(f):
    record_buffer_size = grep("Record Buffer", f).replace("(","").replace(")","").split()[-2]
    validate_buffer_size = grep("Validate Buffer", f).replace("(","").replace(")","").split()[-2]
    return int(record_buffer_size) + int(validate_buffer_size)

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

print("{},{},{},{},{},{},{},{},{}".format(
    "benchmark", "perf avg (%)", "perf std (%)", "hb violation (%)", "hb violation std (%)",
    "logic_overhead(%)", "reg_overhead(%)", "ram_overhead(%)", "buffer_size(B)"))
for bench in benchmarks:
    perf_overhead = []
    buffer_size = []
    hb_violation = []
    for i in range(1, NUM_RUNS+1):
        bench_postfix = bench + "_{:02d}_".format(i)
        none_ns    = get_elaspsed_ns(OUTPUT_DIR + bench_postfix + "none.log")
        recordv_ns = get_elaspsed_ns(OUTPUT_DIR + bench_postfix + "recordv.log")
        replayv_ns = get_elaspsed_ns(OUTPUT_DIR + bench_postfix + "replayv.log")
        size = get_record_size(OUTPUT_DIR + bench_postfix + "recordv.log")
        hbm, totv, contm = get_hb_violation(OUTPUT_DIR + bench_postfix + "diff.txt")
        perf_overhead.append((float(recordv_ns) - float(none_ns)) / float(none_ns) * 100.0)
        hb_violation.append(totv)
        buffer_size.append(size)

    #perf_overhead = np.array(perf_overhead)
    #hb_violation = np.array(hb_violation)

    if bench == "test_dram_dma":
        rpt = FPGA_RR_SYNTH_PATH + benchmarks[bench] + ".hierarchical_utilization_route_design.rpt"
    else:
        rpt = HLS_SYNTH_PATH + benchmarks[bench] + ".hierarchical_utilization_route_design.rpt"
    logic_overhead, reg_overhead, ram_overhead = get_resource_util(rpt)

    print("{},{},{},{},{},{},{},{},{}".format(
        bench,
        np.average(perf_overhead), np.std(perf_overhead),
        np.average(hb_violation), np.std(hb_violation),
        logic_overhead, reg_overhead, ram_overhead,
        np.average(buffer_size)))
