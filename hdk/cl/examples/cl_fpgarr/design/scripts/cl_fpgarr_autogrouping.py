#! /usr/bin/env python3
import argparse
from pathlib import Path
from functools import reduce
from typing import Callable, List, Optional, Set
import sys

parser = argparse.ArgumentParser(description="""Generate tree structures that group the logging_bus or ungroup the
    replay_bus of each channel in each interface. This is an automated process
    because this script also features the ability to opt-in/out record/replay
    for each interface (i.e. you cannot opt-in/out individual channels). The
    generated .svh files should be included in the top-level wrapper (not on top
    of the file, but inline to the correct location).""")

# A dict of potential AXI interfaces and their metadata
# keys are canonical name in this automation scripts
# values are auxiliary info that is related to other part of the project
#  - INTF_ENUM: the enum identifier in the `AWSF1_INTF_RRCFG`` package specified in `cl_fpgarr_defs.svh``
#  - PLACEMENT: the placement_vec copied from `cl_fpgarr_defs.svh`, representing the physical distance between interfaces.
INTFCFG = {
    "sda": {
        "INTF_ENUM": "SDA",
        "PLACEMENT": 1,
        "DEFAULT_ENABLED": True,
    },
    "ocl": {
        "INTF_ENUM": "OCL",
        "PLACEMENT": 1,
        "DEFAULT_ENABLED": True,
    },
    "bar1": {
        "INTF_ENUM": "BAR1",
        "PLACEMENT": 0,
        "DEFAULT_ENABLED": True,
    },
    "pcim": {
        "INTF_ENUM": "PCIM",
        "PLACEMENT": 0,
        "DEFAULT_ENABLED": True,
    },
    "pcis": {
        "INTF_ENUM": "PCIS",
        "PLACEMENT": 1,
        "DEFAULT_ENABLED": True,
    },
    "ddrc": {
        "INTF_ENUM": "DDRC",
        "PLACEMENT": 0,
        "DEFAULT_ENABLED": False,
    },
    "app_axim": {
        "INTF_ENUM": "APP_AXIM",
        "PLACEMENT": 0,
        "DEFAULT_ENABLED": False,
    },
}
# INTFNAMES enforces an order across all interfaces that support RR
INTFNAMES = ["sda", "ocl", "bar1", "pcim", "pcis", "ddrc", "app_axim"]

class AXIIntf(object):
    def __init__(self, intfname):
        self.intfname = intfname
        self.cfg = INTFCFG[intfname]

    def getRecordBusName(self) -> str:
        return f"rr_{self.INTF_ENUM}_SH2CL_logging_bus"

    def getValidateBusName(self) -> str:
        return f"rr_{self.INTF_ENUM}_CL2SH_logging_bus"

    def getReplayBusName(self) -> str:
        return f"rr_{self.INTF_ENUM}_replay_bus"

    def getRecordBusBlackholeInst(self) -> str:
        return (
            f"rr_logging_bus_blackhole blackhole_{self.getRecordBusName()} (\n"
            f"  .in({self.getRecordBusName()})\n"
            ");"
        )

    def getValidateBusBlackholeInst(self) -> str:
        return (
            f"rr_logging_bus_blackhole blackhole_{self.getValidateBusName()} (\n"
            f"  .in({self.getValidateBusName()})\n"
            ");"
        )

    def getReplayBusWhiteholeInst(self) -> str:
        return (
            f"rr_replay_bus_whitehole whitehole_{self.getReplayBusName()} (\n"
            f"  .out({self.getReplayBusName()})\n"
            ");"
        )
    def __getattr__(self, name):
        return self.cfg[name]


class MergeNode(object):
    cnt = 0

    def __init__(self, name: str,
                 l: Optional['MergeNode'] = None,
                 r: Optional['MergeNode'] = None):
        self.name = name
        self.l = l
        self.r = r
        assert((l and r) or (l is None and r is None))

    def renderLoggingMerge(self) -> str:
        if self.l and self.r:
            rendered_l = self.l.renderLoggingMerge()
            rendered_r = self.r.renderLoggingMerge()
            self_render = (
                f"`UNPACKED_LOGGING_BUS_GROUP2({self.name}, "
                f"{self.l.name}, {self.r.name});"
            )
            return '\n'.join([rendered_l, rendered_r, self_render])
        else:
            return ""

    def passThroughLogging(self, dst_bus: str) -> str:
        return (
            f"`LOGGING_BUS_DUP({self.name}, {dst_bus});\n"
            f"rr_logging_bus_pt pt_{dst_bus} (.in({self.name}), .out({dst_bus}));"
        )

    def renderReplayMerge(self) -> str:
        if self.l and self.r:
            rendered_l = self.l.renderReplayMerge()
            rendered_r = self.r.renderReplayMerge()
            self_render = (
                f"`REPLAY_BUS_JOIN2({self.name},{self.l.name},{self.r.name});\n"
                f"rr_replay_bus_ungroup2 {self.name}_ungroup(\n"
                f"  .in({self.name}),\n"
                f"  .outA({self.l.name}),\n"
                f"  .outB({self.r.name})\n"
                ");"
            )
            return '\n'.join([rendered_l, rendered_r, self_render])
        else:
            return ""

    def passThroughReplay(self, src_bus: str) -> str:
        return (
            f"`REPLAY_BUS_DUP({self.name}, {src_bus});\n"
            f"rr_replay_bus_pt pt_{src_bus} "
            f"(.in({src_bus}), .out({self.name}));"
        )

    @classmethod
    def getTempName(cls) -> str:
        name = f"merge_{cls.cnt}"
        cls.cnt = cls.cnt + 1
        return name


def exportMergeStructure(filepath: Path,
                         top_node_name: str,
                         ignoredIntfs: Set[AXIIntf],
                         RRIntfs: List[AXIIntf],
                         ignore_callback: Callable[[AXIIntf], str],
                         getBusName_callback: Callable[[AXIIntf], str],
                         render_callback: Callable[[MergeNode], str],
                         passThrough_callback: Callable[[MergeNode, str], str]
                         ) -> None:
    """
    @param filepath: the output file to export the tree structure
    @param top_node_name: the bus name of the expected top-level node in the merge tree
    @param ignoredIntfs: the set of interfaces that should be excluded from the merge tree and ignored
    @param RRIntfs: the list of interfaces to be merged
    TODO: ignore_callback is no longer needed.
    @param ignore_callback: the callback that generates the code to ignore a bus
    @param getBusName_callback: the callback that generates the corresponding bus name of the interface. This normally extracts a few channels in an interface to merge.
    @param render_callback: the callback that generates the code to merge the interfaces in RRIntfs
    @param passThrough_callback: the callback to handle the case that the merge tree only has one node. This call back will generate the code to rename one bus to the expected top-level bus.
    """
    with open(filepath, "w") as f:
        f.write(AUTOGEN_INFO)
        buses_to_merge = [MergeNode(getBusName_callback(intf))
                          for intf in RRIntfs]
        if len(buses_to_merge) > 1:
            merged_node = reduce(
                lambda l, r: MergeNode(MergeNode.getTempName(), l, r),
                buses_to_merge)
            merged_node.name = top_node_name
            print(render_callback(merged_node), file=f)
        elif len(buses_to_merge) == 1:
            print(passThrough_callback(
                buses_to_merge[0], top_node_name), file=f)


intfMap = {intfname: AXIIntf(intfname) for intfname in INTFNAMES}
intf_toggles = parser.add_argument_group("Interface Toggles")
for intfname in INTFNAMES:
    intf_toggles.add_argument(f"--{intfname}", dest=intfname,
            action="store_true", default=intfMap[intfname].DEFAULT_ENABLED,
            help=f"enable {intfname} (default: %(default)s)")
    intf_toggles.add_argument(f"--no-{intfname}", dest=intfname,
                              action="store_false", help=f"disable {intfname}")
io_ctrl = parser.add_argument_group("Output Control")
io_ctrl.add_argument("-d", "--dir", type=str, default="gen",
                     help="The output directory. (default: %(default)s)")
io_ctrl.add_argument("--record-out", metavar="filename", type=str,
                     default="cl_fpgarr_autogroup_record.svh",
                     help="Group the channel to be recorded for replay in this file. (default: %(default)s)")
io_ctrl.add_argument("--validate-out", metavar="filename", type=str,
                     default="cl_fpgarr_autogroup_validate.svh",
                     help="Group the channel to be recorded for validation in this file. (default: %(default)s)")
io_ctrl.add_argument("--replay-out", metavar="filename", type=str,
                     default="cl_fpgarr_autoungroup_replay.svh",
                     help="Ungroup the channel to be replayed in this file. (default: %(default)s)")
io_ctrl.add_argument("--cfg-out", metavar="filename", type=str, default="cl_fpgarr_autogroup_cfg.svh",
                     help="Generate crucial grouping configuration headers to this file. (default: %(default)s)")
args = parser.parse_args()
AUTOGEN_INFO = (
    f"// cwd: {Path.cwd()}\n"
    f"// automatically generated by {' '.join(sys.argv)}\n"
)
AUTOGEN_HEADER = (
    f"`ifndef CL_FPGARR_AUTOGROUP_CFG_H\n"
    f"`define CL_FPGARR_AUTOGROUP_CFG_H\n"
) + AUTOGEN_INFO
AUTOGEN_FOOTER = (
    f"`endif\n"
)


print(f"{sys.argv[0]} is working with config:")
print(args)

ignoredIntfs = set(intfMap[intfname] for intfname in INTFNAMES
                   if not getattr(args, intfname))
RRIntfs = [intfMap[intfname] for intfname in INTFNAMES
           if getattr(args, intfname)]

output_dir = Path(args.dir)

# I/O setup
if not output_dir.exists():
    output_dir.mkdir(mode=0o755, parents=True, exist_ok=False)


# Grouping record for replay
TOP_LEVEL_RECORD_BUS_NAME = "merged_SH2CL_logging_bus"
exportMergeStructure(
    output_dir/args.record_out,
    TOP_LEVEL_RECORD_BUS_NAME,
    ignoredIntfs,
    RRIntfs,
    AXIIntf.getRecordBusBlackholeInst,
    AXIIntf.getRecordBusName,
    MergeNode.renderLoggingMerge,
    MergeNode.passThroughLogging
)

# Grouping record for validate
TOP_LEVEL_VALIDATE_BUS_NAME = "merged_CL2SH_logging_bus"
exportMergeStructure(
    output_dir/args.validate_out,
    TOP_LEVEL_VALIDATE_BUS_NAME,
    ignoredIntfs,
    RRIntfs,
    AXIIntf.getValidateBusBlackholeInst,
    AXIIntf.getValidateBusName,
    MergeNode.renderLoggingMerge,
    MergeNode.passThroughLogging
)

# Ungrouping replay
TOP_LEVEL_REPLAY_BUS_NAME = "unpacked_replay_bus"
exportMergeStructure(
    output_dir/args.replay_out,
    TOP_LEVEL_REPLAY_BUS_NAME,
    ignoredIntfs,
    RRIntfs,
    AXIIntf.getReplayBusWhiteholeInst,
    AXIIntf.getReplayBusName,
    MergeNode.renderReplayMerge,
    MergeNode.passThroughReplay
)

# Export grouping configuration header
with open(output_dir/args.cfg_out, "w") as f:
    f.write(AUTOGEN_HEADER)
    num_tracked_label = "RR_NUM_TRACKED_AXI"
    print((
        f"// axi interfaces under track: {', '.join([i.intfname for i in RRIntfs])}\n"
        f"// axi interfaces ignored: {', '.join([i.intfname for i in ignoredIntfs])}\n"
        f"parameter {num_tracked_label} = {len(RRIntfs)};"
    ), file=f)
    bracket_sep = ', \n\t'
    # tracked_intf_enum = [INTFCFG[intf.intfname]["INTF_ENUM"]
    #                     for intf in RRIntfs]
    # for placement_vec
    # indirect index
    # placement_vec_entries = [
    #     f"AWSF1_INTF_RRCFG::PLACEMENT_VEC[AWSF1_INTF_RRCFG::{eid}]"
    #     for eid in tracked_intf_enum]
    placement_vec_entries = [
        "{} /*{}*/".format(intf.PLACEMENT, intf.intfname)
        for intf in RRIntfs
    ]
    print(
        f"parameter int RR_TRACKED_AXI_PLACEMENT_VEC[0:{num_tracked_label}-1] = '{{\n\t{bracket_sep.join(placement_vec_entries)}\n}};", file=f)
    # for TRACKED_LOGE_ID
    tracked_loge_entries = []
    tracked_loge_cnt = 0
    for intfname in INTFNAMES:
        if getattr(args,intfname):
            tracked_loge_entries.append(f"{tracked_loge_cnt} /*{intfname}*/")
            tracked_loge_cnt += 1
        else:
            tracked_loge_entries.append(f"-1 /*{intfname}*/")
    print(f"parameter int RR_TRACKED_LOGE_INTF_IDX[0:AWSF1_INTF_RRCFG::NUM_INTF-1] = '{{\n\t{bracket_sep.join(tracked_loge_entries)}\n}};", file=f)
    for intf in RRIntfs:
        if getattr(args,intf.intfname):
            print(f"`define RR_ENABLE_{intf.INTF_ENUM}", file=f)
    f.write(AUTOGEN_FOOTER)
