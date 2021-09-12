TASK?=
# setup
export DESIGNDIR=$(abspath $(dir $(lastword $(MAKEFILE_LIST)))/../)
# yosys + sby
ALL_SUB_PROVE_DIR=$(patsubst %/config.sby,%, $(wildcard */config.sby))
ALL_SUB_PROVE_TGT=$(foreach dir, $(ALL_SUB_PROVE_DIR), prove_$(dir))
ALL_SUB_VIEW_TGT=$(foreach dir, $(ALL_SUB_PROVE_DIR), view_$(dir))
# jaspergold
ALL_SUB_JGPROVE_TGT=$(foreach dir, $(ALL_SUB_PROVE_DIR), jp_$(dir))
ALL_SUB_JGVIEW_TGT=$(foreach dir, $(ALL_SUB_PROVE_DIR), jv_$(dir))
export CDS_LIC_FILE=/usr/caen/jasper-2021.06.001/license.dat
JG=/usr/caen/jasper-2021.06.001/bin/jg
.PHONY: ${ALL_SUB_PROVE_TGT}
all:
	echo "ALL: ${ALL_SUB_PROVE_DIR}"
${ALL_SUB_PROVE_TGT}: prove_%: %/config.sby
	@echo "Make: proving $*"
	@cd $* && sby -f config.sby ${TASK} ||:
	@find $*/*/engine_0/*.vcd -exec vcd2vpd {} {}.vpd > /dev/null 2>&1 \; ||:

${ALL_SUB_JGPROVE_TGT}: jp_%: %/jg.tcl
	@echo "jg: proving $*"
	@${JG} -no_gui -acquire_proj $<

${ALL_SUB_JGVIEW_TGT}: jv_%: %/jg.tcl
	@echo "jg: proving $*"
	@${JG} -acquire_proj $<

.SECONDEXPANSION:
${ALL_SUB_VIEW_TGT}: view_%: $$(wildcard %/config_${TASK}/engine_0/*.vpd)
	@echo "TASK: ${TASK}"
	@echo "Viewing: $<"
	dve -full64 -vpd $<
