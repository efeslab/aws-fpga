#/usr/bin/python3

import os
import glob
from sh import grep, tail
import argparse
import statistics as stat
from typing import List

HOME = os.getenv("HOME")
parser = argparse.ArgumentParser(description="Reproduce the Table.1 in the paper")
parser.add_argument('--expr-output', type=str, required=True, help="The output directory of experiments on the actual FPGA hardware")
parser.add_argument('--synth-reports', type=str, default=f"{HOME}/aws-fpga-prebuilt", help="The git repo that contains synthesis results (default: %(default)s)")
parser.add_argument('--record-width', type=int, default=1694, help="The width (in bits) of the interfaces being recorded (default: %(default)s)")

args = parser.parse_args()
DRAM_OUTPUT_DIR = args.expr_output
HLS_OUTPUT_DIR  = args.expr_output
HLS_SYNTH_PATH = f"{args.synth_reports}/hdk/cl/examples/cl_hls/build/reports/"
FPGA_RR_SYNTH_PATH = f"{args.synth_reports}/hdk/cl/examples/cl_fpgarr/build/reports/"
benchmarks = {
        "test_dram_dma":"22_03_16-045258",
        "3d_rendering":"22_03_17-205701",
        "bnn":"22_03_16-210531",
        "digit_recognition":"22_03_16-211232",
        "face_detection":"22_03_16-211934",
        "spam_filter":"22_03_16-212635",
        "optical_flow":"22_03_17-020330",
        "sssp":"22_03_17-021031",
        "sha256":"22_03_17-021732",
        "mobilenet":"22_03_17-022433"
}

def check_file_existance(f):
    if not os.path.exists(f):
        raise RuntimeError(f"Does {f} exist?")

def get_elaspsed_ns(f):
    check_file_existance(f)
    elapsed_time = grep("RR pre_rr->post_rr, elapsed ns:", f).split()[-1]
    user_elapsed_time = grep("RR user timer, elapsed ns:", f).split()[-1]
    if int(user_elapsed_time) == 0:
        return int(elapsed_time)
    else:
        return int(user_elapsed_time)

def get_hb_violation(f):
    check_file_existance(f)
    res = tail("-n1", f).replace(":", " ").replace(","," ").split()
    hb_mismatches = float(res[6].replace("%", "").replace("(", " ").replace(")", " ").split()[1])
    total_violations = float(res[9].replace("%", "").replace("(", " ").replace(")", " ").split()[1])
    content_mismatches = float(res[-1].replace("%", "").replace("(", " ").replace(")", " ").split()[1])
    return hb_mismatches, total_violations, content_mismatches

def get_record_size(f):
    check_file_existance(f)
    record_buffer_size = grep("Record Buffer", f).replace("(","").replace(")","").split()[-2]
    validate_buffer_size = grep("Validate Buffer", f).replace("(","").replace(")","").split()[-2]
    return int(record_buffer_size) + int(validate_buffer_size)

def get_resource_util(f):
    check_file_existance(f)
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

def geomean_of_percent(data: List[float]):
    scaledRatio = [100 + p for p in data]
    return stat.geometric_mean(scaledRatio) - 100

print("{},{},{},{},{},{},{},{},{},{},{}".format(
    "benchmark", "avg(runtime)(ms)", "avg(overhead) (%)", "std(overhead) (%)", "hb violation (%)", "std(hb violation) (%)",
    "logic_overhead(%)", "reg_overhead(%)", "ram_overhead(%)", "avg(trace size) (B)", "Trace Reduction"))

for benchName, benchID in benchmarks.items():
    if benchName == "test_dram_dma":
        OUTPUT_DIR = DRAM_OUTPUT_DIR
    else:
        OUTPUT_DIR = HLS_OUTPUT_DIR
    runtime = []
    perf_overhead = []
    hb_violation = []
    trace_sizeB = []
    glob_pattern = f"{OUTPUT_DIR}/{benchName}*_diff.txt"
    matched_prefix = [path[:-len('diff.txt')] for path in glob.glob(glob_pattern)]
    for bench_prefix in matched_prefix:
        none_ns    = get_elaspsed_ns(bench_prefix + "none.log")
        recordv_ns = get_elaspsed_ns(bench_prefix + "recordv.log")
        replayv_ns = get_elaspsed_ns(bench_prefix + "replayv.log")
        record_sizeB = get_record_size(bench_prefix + "recordv.log")
        hbm, totv, contm = get_hb_violation(bench_prefix + "diff.txt")
        runtime.append(float(none_ns)/1000/1000)
        perf_overhead.append((float(recordv_ns) - float(none_ns)) / float(none_ns) * 100.0)
        hb_violation.append(totv)
        trace_sizeB.append(record_sizeB)

    #perf_overhead = np.array(perf_overhead)
    #hb_violation = np.array(hb_violation)

    if benchName == "test_dram_dma":
        rpt = FPGA_RR_SYNTH_PATH + benchID + ".hierarchical_utilization_route_design.rpt"
    else:
        rpt = HLS_SYNTH_PATH + benchID + ".hierarchical_utilization_route_design.rpt"
    logic_overhead, reg_overhead, ram_overhead = get_resource_util(rpt)

    mean_runtime = stat.mean(runtime)
    mean_trace_sizeB = stat.mean(trace_sizeB)
    cycles = (mean_runtime / 10**3) * 250 * 10**6 # 250MHz
    cycle_accurate_trace_sizeB = cycles * args.record_width // 8
    trace_size_reduction = int(cycle_accurate_trace_sizeB // mean_trace_sizeB)
    print("{},{},{},{},{},{},{},{},{},{},{}".format(
        benchName,
        mean_runtime,
        geomean_of_percent([overhead + 100 for overhead in perf_overhead]) - 100, stat.stdev(perf_overhead),
        stat.mean(hb_violation), stat.stdev(hb_violation),
        logic_overhead, reg_overhead, ram_overhead,
        mean_trace_sizeB, trace_size_reduction))
