import math
import argparse
import sys
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

# {{{ Divide Rules
class DivideRule(object):
  # input is a list of channel widths
  # returns is a tuple, two list of channel widths, the wider one goes first
  @classmethod
  def divide_one_layer(cls, CW, idxs):
    assert(0 and "Should instantiate this function");

class DivideBySum(DivideRule):
  NAME="dividebysum"
class DivideByEvenHeadTail(DivideRule):
  NAME="dp"
# }}} Divide Rules

# Make use of divide rules
class MergePlan(object):
  NAME="PLAN TEMPLATE NAME"
  SEP = '------'
  # CW: all channel widths
  def __init__(self, name, CW, args):
    # list of layer plan
    #   each layer plan is a list of node plan and has a height
    #   layer height > 0 has merge (M) or Queue(Q) plan
    #   layer height == 0 only has Q plan to reorder input
    # each node plan is a tuple (id of the previous layer to merge), if two ids
    # equals, means a queue
    self.name = name
    self.plan = []
    self.CW = CW
    self.dbg_msg = ""
    self.args = args
    self.run_plan()

  def run_plan(self):
    N = len(self.CW)
    init_idxs = range(N)
    h, nid, msg = self.plan_merge(init_idxs)
    print(msg)
    if args.verbose:
      print("dbg msg:\n%s" % self.dbg_msg)

  # idxs: the index of leafs to consider
  # returns: (height, node id, info_msg)
  # hight is from the leaf, start from 0
  def plan_merge(self, idxs):
    assert(0 and "Please instantiate me")

  # return node id of the added plan on that layer
  # plan is a tuple (lid, rid)
  # lid != rid is a merge node
  # lid == rid is a queue node
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

class DivideBySumPlan(MergePlan):
  NAME="dividebysum"
  def divide_one_layer(self, CW, idxs):
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
    # Putting more bits on the left and fewer bits on the right saves resource
    if suml > sumr:
      return (l, r)
    else:
      return (r, l)
  def plan_merge(self, idxs):
    CW = self.CW
    if len(idxs) == 1:
      cwid = idxs[0]
      nid = self.addNodePlan(0, (cwid, cwid))
      msg = "ID(%d) Q(%d) W%d\n" % (nid, cwid, CW[cwid])
      return (0, nid, msg)
    else:
      l_idxs, r_idxs = self.divide_one_layer(CW, idxs)
      self.dbg_msg += "dbg, divide %s to\n%s\n%s\n" % (
        str([CW[i] for i in idxs]),
        str([CW[i] for i in l_idxs]),
        str([CW[i] for i in r_idxs])
      )
      lh, lid, l_msg = self.plan_merge(l_idxs)
      rh, rid, r_msg = self.plan_merge(r_idxs)
      h = max(lh, rh)
      # insert queue node in the tree
      lhq = lh
      while lhq < h:
        lid_next = self.addNodePlan(lhq+1, (lid, lid))
        l_msg += self.SEP*(lhq+1) + "> ID(%d) Q(%d) W%d\n" % (
          lid_next, lid, sum([CW[x] for x in l_idxs])
        )
        lid = lid_next
        lhq = lhq + 1
      rhq = rh
      while rhq < h:
        rid_next = self.addNodePlan(rhq+1, (rid, rid))
        r_msg += self.SEP*(rhq+1) + "> ID(%d) Q(%d) W%d\n" % (
          rid_next, rid, sum([CW[x] for x in r_idxs])
        )
        rid = rid_next
        rhq = rhq + 1
      # merge
      nid = self.addNodePlan(h+1, (lid, rid))
      msg = l_msg + r_msg
      msg += self.SEP*(h+1) + "> ID(%d) M(%d, %d) W%d\n" % (
        nid, lid, rid, sum([CW[x] for x in idxs])
      )
      return (h+1, nid, msg)

class DivideByDPPlan(DivideBySumPlan):
  NAME="divdp"
  def divide_one_layer(self, CW, idxs):
    # CW from min to max
    s = sorted(idxs, key=lambda x: CW[x])
    N = len(s)
    suma = sum([CW[i] for i in idxs])
    if N == 2:
      return ([s[1]], [s[0]])
    pairs = [] # (sum(first.width, second.width), first.id, second.id)
    if N % 2:
      odd_id = s.pop()
      pairs.append((CW[odd_id], odd_id, odd_id))
      N -= 1
    # for the rest of the CW, pair a max with a min
    # this is to reduce the variance of the width of the merged chanels in the
    # next layer
    for i in range(N//2):
      first = s[N - 1 - i]
      second = s[i]
      pairs.append((CW[first] + CW[second], first, second))
    # 01-bag packing, dp
    half_goal = suma // 2
    dp = [0] * (half_goal + 1)
    dp_solution = [set()] * (half_goal + 1)
    for i in range(len(pairs)):
      w = pairs[i][0]
      for j in range(half_goal, w - 1, -1):
        if dp[j] < dp[j-w] + w:
          dp[j] = dp[j-w] + w
          dp_solution[j] = dp_solution[j-w].copy()
          dp_solution[j].add(i)
    # put (< half_goal) solution to the right
    r_idxs = set()
    for i in dp_solution[half_goal]:
      r_idxs.add(pairs[i][1])
      r_idxs.add(pairs[i][2])
    l_idxs = set(idxs) - r_idxs
    return (list(l_idxs), list(r_idxs))

class DivideGreedyPlan(MergePlan):
  NAME="greedy"
  def plan_merge(self, idxs):
    # recursive idxs
    self.all_plan = []
    ridxs = idxs
    rCW = self.CW
    while len(ridxs) > 1:
      pairs = self.plan_one_layer(rCW, ridxs)
      self.all_plan.append(pairs)
      next_CW = []
      for w, _, _ in pairs:
        next_CW.append(w)
      rCW = next_CW
      ridxs = range(len(pairs))
    h = len(self.all_plan)
    nid, msg = self.registerPlan(h-1, 0)
    return (h, nid, msg)
  # recursive register node idx at height h
  # return (registered id, info_msg)
  def registerPlan(self, h, idx):
    if (h == -1):
      # termination case: leaf node
      nid = self.addNodePlan(0, (idx, idx))
      msg = "ID(%d) Q(%d) W%d\n" % (nid, idx, self.CW[idx])
      return (nid, msg)
    assert(h < len(self.all_plan))
    assert(idx < len(self.all_plan[h]))
    w, lid, rid = self.all_plan[h][idx]
    if lid != rid: # merge node
      lnid, l_msg = self.registerPlan(h-1, lid)
      rnid, r_msg = self.registerPlan(h-1, rid)
      nid = self.addNodePlan(h+1, (lnid, rnid))
      msg = l_msg + r_msg
      msg += self.SEP*(h+1) + "> ID(%d) M(%d, %d) W%d\n" % (nid, lnid, rnid, w)
      return (nid, msg)
    else: # queue node
      lnid, msg = self.registerPlan(h-1, lid)
      nid = self.addNodePlan(h+1, (lnid, lnid))
      msg += self.SEP*(h+1) + "> ID(%d) Q(%d) W%d\n" % (nid, lnid, w)
      return (nid, msg)
  def plan_one_layer(self, CW, idxs):
    # CW from min to max
    s = sorted(idxs, key=lambda x: CW[x])
    self.dbg_msg += "sorted %s\n" % (str([CW[i] for i in s]))
    N = len(s)
    pairs = [] # (sum(first.width, second.width), first.id, second.id)
    if N % 2:
      odd_id = s.pop()
      pairs.append((CW[odd_id], odd_id, odd_id))
      N -= 1
    # for the rest of the CW, pair a max with a min
    # this is to reduce the variance of the width of the merged chanels in the
    # next layer
    for i in range(N//2):
      first = s[N - 1 - i]
      second = s[i]
      w = CW[first] + CW[second]
      pairs.append((w, first, second))
    self.dbg_msg += "pairs: %s\n" % (str(
      [(w,CW[lid],CW[rid]) for w, lid, rid in pairs]
    ))
    return pairs

# Divide rule configurations
ALL_RULES = [DivideBySumPlan, DivideByDPPlan, DivideGreedyPlan]
ALL_RULES_MAP = dict([(cls.NAME, cls) for cls in ALL_RULES])
DEFAULT_RULE = DivideBySumPlan
parser.add_argument('-p', '--plan', metavar='divide_plan', type=str,
    action="append", choices=ALL_RULES_MAP.keys(), default=[],
    help="How should I divide? (default: %(default)s, choices: %(choices)s)")
parser.add_argument('-v', '--verbose', action="store_true", default=False,
    help="print debug messages")
args = parser.parse_args()

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
  if len(args.plan) == 0:
    divide_plans = [DEFAULT_RULE] * len(names)
  if len(args.plan) == 1:
    divide_plans = [ALL_RULES_MAP[args.plan[0]]] * len(names)
  else:
    divide_plans = [ALL_RULES_MAP[p] for p in args.plan]
  for name, CW, plan in zip(names, CWs, divide_plans):
    cw_cfg = CW.split(',')
    CW_cnt = int(cw_cfg[0])
    CW_str = cw_cfg[1]
    CW_int = []
    for i in range(1,CW_cnt+1):
      l = len(CW_str) - i*RR_CHANNEL_WIDTH_BITS
      r = l + RR_CHANNEL_WIDTH_BITS
      CW_int.append(int("0b"+CW_str[l:r], base=2))
    print("#"*80)
    print("name: %s, using divide_plan %s, CW_int: %s" % (name, plan.NAME, str(CW_int)))
    plan = plan(name, CW_int, args)
    plans.append(plan)
  with open(args.output, 'wt') as f:
    f.write("// automatically generated by %s\n" % ' '.join(sys.argv))
    MergePlan.exportAllPlan(f, plans)
else:
  print("name and CW mismatch: %d name, %d CW" % (len(names), len(CWs)))
