import math
import argparse
"""
This is the merge-tree configuration generator for the packing module.
Example:
python3 cl_fpgarr_treegen.py 32 36 32 32 36 32 32 36 32 531 18 91 593 91
"""
parser = argparse.ArgumentParser(description=
    "Generate packing merge tree configuration")
parser.add_argument('channel_widths', metavar='widths', type=int, nargs='+',
    help="a space seperated list of channel widths")
parser.add_argument('-o', '--output', metavar='output_file', type=str,
    default="cl_fpgarr_packing_cfg.svh",
    help="output verilog parameter to this file")
args = parser.parse_args()

# input is a list of channel widths
# returns is a tuple, two list of channel widths, the wider one goes first
def divide_one_layer(CW, idxs):
  s = sorted(idxs, key=lambda x: CW[x], reverse=True)
  suml = 0
  l = []
  sumr = 0
  r = []
  for wid in s:
    if suml > sumr:
      r.append(wid)
      sumr += CW[wid]
    else:
      l.append(wid)
      suml += CW[wid]
  if suml > sumr:
    return (l, r)
  else:
    return (r, l)
class MergePlan(object):
  def __init__(self):
    # list of layer plan
    #   each layer plan is a list of node plan and has a height
    #   layer height > 0 has merge (M) or Queue(Q) plan
    #   layer height == 0 only has Q plan to reorder input
    # each node plan is a tuple (id of the previous layer to merge), if two ids
    # equals, means a queue
    self.plan = []
  # return node id of the added plan on that layer
  def addNodePlan(self, height, plan):
    if len(self.plan) < height + 1:
      self.plan.append([])
    self.plan[height].append(plan)
    return len(self.plan[height]) - 1
  def get_layer_plan(self, h, max_N):
    layer_plan = self.plan[h]
    plans_str = []
    for i in range(max_N):
      if i < len(layer_plan):
        np = layer_plan[i] # node plan
        plans_str.append("\'{%d, %d}" % (np[0], np[1]))
      else:
        plans_str.append("\'{0, 0}")
    return '\'{' + ', '.join(plans_str) + '}'

  # f: opened file object
  def writeVerilogParameters(self, f):
    # output four parameter
    # MERGE_TREE_HEIGHT
    # MERGE_TREE_MAX_NODES
    # int NODES_PER_LAYER [MERGE_TREE_HEIGHT-1:0]
    # int MERGE_PLAN [MERGE_TREE_HEIGHT-1:0][MERGE_TREE_MAX_NODES-1:0][1:0]
    h = len(self.plan)
    nodes_per_layer = [len(x) for x in self.plan]
    max_N = max(nodes_per_layer)
    f.write("`ifndef CL_FPGARR_PACKING_CFG_H\n")
    f.write("`define CL_FPGARR_PACKING_CFG_H\n")
    f.write("// height of the merge tree, layer 0 is for reorder input\n")
    f.write("parameter MERGE_TREE_HEIGHT=%d;\n" % h)
    f.write("// max number of nodes across all layers/height\n")
    f.write("parameter MERGE_TREE_MAX_NODES=%d;\n" % max_N)
    f.write("// number of nodes inside each layer, "
            "used to terminate generate for-loop\n")
    f.write("parameter int NODES_PER_LAYER [0:MERGE_TREE_HEIGHT-1] = "
            "\'{ %s };\n" % ', '.join([str(x) for x in nodes_per_layer]))
    f.write("// actual merge plan [layer][node][plan], each plan is "
            "a two-integer tuple, meaning the idx of nodes to merge or queue "
            "in the previous layer. Equal idx means queue, else means merge.\n"
            "// Height 0 is to shuffle the init channel width.\n")
    # generate the actual plan
    merge_plan = ', \n'.join([self.get_layer_plan(i, max_N)
      for i in range(h)])
    f.write("parameter int MERGE_PLAN [0:MERGE_TREE_HEIGHT-1] "
            "[0:MERGE_TREE_MAX_NODES-1] [0:1] = \'{\n%s\n};\n" % merge_plan)
    # a shortcut to the shuffling plan (MERGE_PLAN[0])
    f.write("// a shortcut to the shuffling plan (MERGE_PLAN[0])\n")
    f.write("parameter int SHUFFLE_PLAN [0:MERGE_TREE_MAX_NODES-1] [0:1] = "
            "MERGE_PLAN[0];\n")
    f.write("`endif // CL_FPGARR_PACKING_CFG_H\n")

# CW: all channel widths
# idxs: the index of leafs to consider
# depth: depth from the root, start from 0
# returns: (height, node id)
# hight is from the leaf, start from 0
def plan_merge(plan, CW, idxs):
  if len(idxs) == 1:
    cwid = idxs[0]
    nid = plan.addNodePlan(0, (cwid, cwid))
    print("Q (%d->%d) W%d" % (cwid, nid, CW[cwid]))
    return (0, nid)
  else:
    l_idxs, r_idxs = divide_one_layer(CW, idxs)
    lh, lid = plan_merge(plan, CW, l_idxs)
    rh, rid = plan_merge(plan, CW, r_idxs)
    h = max(lh, rh)
    # setup queue
    lhq = lh
    while lhq < h:
      lid_next = plan.addNodePlan(lhq+1, (lid, lid))
      print('--'*(lhq+1) + "> Q (%d->%d) W%d" % (lid, lid_next, sum([CW[x] for x in l_idxs])))
      lid = lid_next
      lhq = lhq + 1
    rhq = rh
    while rhq < h:
      rid_next = plan.addNodePlan(rhq+1, (rid, rid))
      print('--'*(rhq+1) + "> Q (%d->%d) W%d" % (rid, rid_next, sum([CW[x] for x in r_idxs])))
      rid = rid_next
      rhq = rhq + 1
    # merge
    nid = plan.addNodePlan(h+1, (lid, rid))
    print('--'*(h+1) + "> ID(%d) M(%d, %d) W%d" % (nid, lid, rid, sum([CW[x] for x in idxs])))
    return (h+1, nid)

CW = args.channel_widths
# number of channels
N = len(CW)
print(CW)
plan = MergePlan()
plan_merge(plan, CW, range(N))
with open(args.output, 'wt') as f:
  plan.writeVerilogParameters(f)
