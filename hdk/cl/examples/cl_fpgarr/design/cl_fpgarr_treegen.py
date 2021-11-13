import math
import argparse
"""
This is the merge-tree configuration generator for the packing module.
Example:
python3 cl_fpgarr_treegen.py --name record --CW 32,36,32,32,36,32,32,36,32,531,18,91,593,91
"""
RR_CHANNEL_WIDTH_BITS = 32
parser = argparse.ArgumentParser(description=
    "Generate packing merge tree configuration, can specify multiple pair "
    "of name and channel widths")
parser.add_argument('--name', dest="names", metavar='names', type=str,
    action="append",
    help="the name of the merge plan for the following channel widths")
parser.add_argument('--CW', dest="CWs", metavar='channel_widths', type=str,
    action="append",
    help="format: channel_cnt(int),binary_encoding_of_channel_widths (e.g. "
         "\"14,0000000000000000000000000101101100000000000000000000001001010001000000000000000000000000010110110000000000000000000000000001001000000000000000000000001000010011000000000000000000000000001000000000000000000000000000000010010000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010010000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010010000000000000000000000000000100000\")")
parser.add_argument('-o', '--output', metavar='output_file', type=str,
    default="cl_fpgarr_packing_cfg.svh",
    help="output verilog parameter to this file")
args = parser.parse_args()

# input is a list of channel widths
# returns is a tuple, two list of channel widths, the wider one goes first
def divide_one_layer(CW, idxs):
  s = sorted(idxs, key=lambda x: CW[x], reverse=True)
  suma = sum(CW)
  suml = 0
  l = []
  sumr = 0
  r = []
  for wid in s:
    if suml > sumr and (len(l) > len(r) or CW[wid]/suma > 0.01):
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
  def __init__(self, name, CW):
    # list of layer plan
    #   each layer plan is a list of node plan and has a height
    #   layer height > 0 has merge (M) or Queue(Q) plan
    #   layer height == 0 only has Q plan to reorder input
    # each node plan is a tuple (id of the previous layer to merge), if two ids
    # equals, means a queue
    self.name = name
    self.plan = []
    self.CW = CW
    self.run_plan()

  def run_plan(self):
    N = len(self.CW)
    init_idxs = range(N)
    self.plan_merge(init_idxs)

  # CW: all channel widths
  # idxs: the index of leafs to consider
  # depth: depth from the root, start from 0
  # returns: (height, node id)
  # hight is from the leaf, start from 0
  def plan_merge(self, idxs):
    CW = self.CW
    if len(idxs) == 1:
      cwid = idxs[0]
      nid = self.addNodePlan(0, (cwid, cwid))
      print("Q (%d->%d) W%d" % (cwid, nid, CW[cwid]))
      return (0, nid)
    else:
      l_idxs, r_idxs = divide_one_layer(CW, idxs)
      #print("dbg, divide to\n%s\n%s" % (
      #  str([CW[i] for i in l_idxs]),
      #  str([CW[i] for i in r_idxs])
      #))
      lh, lid = self.plan_merge(l_idxs)
      rh, rid = self.plan_merge(r_idxs)
      h = max(lh, rh)
      # insert queue node in the tree
      lhq = lh
      while lhq < h:
        lid_next = self.addNodePlan(lhq+1, (lid, lid))
        print('--'*(lhq+1) + "> Q (%d->%d) W%d" % (
          lid, lid_next, sum([CW[x] for x in l_idxs])
        ))
        lid = lid_next
        lhq = lhq + 1
      rhq = rh
      while rhq < h:
        rid_next = self.addNodePlan(rhq+1, (rid, rid))
        print('--'*(rhq+1) + "> Q (%d->%d) W%d" % (
          rid, rid_next, sum([CW[x] for x in r_idxs])
        ))
        rid = rid_next
        rhq = rhq + 1
      # merge
      nid = self.addNodePlan(h+1, (lid, rid))
      print('--'*(h+1) + "> ID(%d) M(%d, %d) W%d" % (
        nid, lid, rid, sum([CW[x] for x in idxs])
      ))
      return (h+1, nid)

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
  def writeVerilogParameters(self, f, indent=2, SEP=' '):
    # output four parameter
    # MERGE_TREE_HEIGHT
    # MERGE_TREE_MAX_NODES
    # int NODES_PER_LAYER [MERGE_TREE_HEIGHT-1:0]
    # int MERGE_PLAN [MERGE_TREE_HEIGHT-1:0][MERGE_TREE_MAX_NODES-1:0][1:0]
    h = len(self.plan)
    nodes_per_layer = [len(x) for x in self.plan]
    max_N = max(nodes_per_layer)
    prefix = SEP * indent
    f.write(prefix +
        "// height of the merge tree, layer 0 is for reorder input\n")
    f.write(prefix +
        "parameter MERGE_TREE_HEIGHT=%d;\n" % h)
    f.write(prefix +
        "// max number of nodes across all layers/height\n")
    f.write(prefix +
        "parameter MERGE_TREE_MAX_NODES=%d;\n" % max_N)
    f.write(prefix +
        "// number of nodes inside each layer, "
        "used to terminate generate for-loop\n")
    f.write(prefix +
        "parameter int NODES_PER_LAYER [0:MERGE_TREE_HEIGHT-1] = "
        "\'{ %s };\n" % ', '.join([str(x) for x in nodes_per_layer]))
    f.write(prefix +
        "// actual merge plan [layer][node][plan], each plan is "
        "a two-integer tuple, meaning the idx of nodes to merge or queue "
        "in the previous layer. Equal idx means queue, else means merge.\n"
        "// Height 0 is to shuffle the init channel width.\n")
    # generate the actual plan
    merge_plan = ', \n'.join([self.get_layer_plan(i, max_N)
      for i in range(h)])
    f.write(prefix +
        "parameter int MERGE_PLAN [0:MERGE_TREE_HEIGHT-1] "
        "[0:MERGE_TREE_MAX_NODES-1] [0:1] = \'{\n%s\n};\n" % merge_plan)
    # a shortcut to the shuffling plan (MERGE_PLAN[0])
    f.write(prefix +
        "// a shortcut to the shuffling plan (MERGE_PLAN[0])\n")
    f.write(prefix +
        "parameter int SHUFFLE_PLAN [0:MERGE_TREE_MAX_NODES-1] [0:1] = "
        "MERGE_PLAN[0];\n")

  # f is an opened file object
  # plans is a list of MergePlan()
  @classmethod
  def exportAllPlan(cls, f, plans):
    f.write("`ifndef CL_FPGARR_PACKING_CFG_H\n")
    f.write("`define CL_FPGARR_PACKING_CFG_H\n")
    for p in plans:
      f.write("package {};\n".format(p.name))
      p.writeVerilogParameters(f)
      f.write("endpackage\n")
    f.write("`endif // CL_FPGARR_PACKING_CFG_H\n")

names = args.names
CWs = args.CWs
if names is None or CWs is None:
  names = ["record_pkg", "validate_pkg"]
  CWs = [
      "14,0000000000000000000000000101101100000000000000000000001001010001000000000000000000000000010110110000000000000000000000000001001000000000000000000000001000010011000000000000000000000000001000000000000000000000000000000010010000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010010000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010010000000000000000000000000000100000",
      "11,0000000000000000000000000001001000000000000000000000001000010011000000000000000000000000010110110000000000000000000000100101000100000000000000000000000001011011000000000000000000000000000000100000000000000000000000000010001000000000000000000000000000000010000000000000000000000000001000100000000000000000000000000000001000000000000000000000000000100010"
  ]
plans = []
if len(names) == len(CWs):
  for name, CW in zip(names, CWs):
    cw_cfg = CW.split(',')
    CW_cnt = int(cw_cfg[0])
    CW_str = cw_cfg[1]
    CW_int = []
    for i in range(1,CW_cnt+1):
      l = len(CW_str) - i*RR_CHANNEL_WIDTH_BITS
      r = l + RR_CHANNEL_WIDTH_BITS
      CW_int.append(int("0b"+CW_str[l:r], base=2))
    print("name: %s, CW_int: %s" % (name, str(CW_int)))
    plan = MergePlan(name, CW_int)
    plans.append(plan)
  with open(args.output, 'wt') as f:
    MergePlan.exportAllPlan(f, plans)
else:
  print("name and CW mismatch: %d name, %d CW" % (len(names), len(CWs)))
