TASK?=
# setup
MAGIC_FILE=jg.tcl
export DESIGNDIR=$(abspath $(dir $(lastword $(MAKEFILE_LIST)))/../)
ALL_SUB_PROVE_DIR=$(patsubst %/$(MAGIC_FILE),%, $(wildcard */$(MAGIC_FILE)))
# yosys + sby
ALL_SUB_PROVE_TGT=$(foreach dir, $(ALL_SUB_PROVE_DIR), prove_$(dir))
ALL_SUB_VIEW_TGT=$(foreach dir, $(ALL_SUB_PROVE_DIR), view_$(dir))
# jaspergold
ALL_SUB_JGPROVE_TGT=$(foreach dir, $(ALL_SUB_PROVE_DIR), jp_$(dir))
ALL_SUB_JGVIEW_TGT=$(foreach dir, $(ALL_SUB_PROVE_DIR), jv_$(dir))
export CDS_LIC_FILE=/usr/caen/jasper-2021.06.001/license.dat
JG=/usr/caen/jasper-2021.06.001/bin/jg
.PHONY: ${ALL_SUB_PROVE_TGT} ${ALL_SUB_VIEW_TGT} ${ALL_SUB_JGPROVE_TGT} ${ALL_SUB_JGVIEW_TGT} prove_all jp_all
all:
	echo "ALL: ${ALL_SUB_PROVE_DIR}"

prove_all: ${ALL_SUB_PROVE_TGT}
${ALL_SUB_PROVE_TGT}: prove_%: %/config.sby
	@echo "Make: proving $*"
	@cd $* && sby -f config.sby ${TASK} ||:
	@find $*/*/engine_0/*.vcd -exec vcd2vpd {} {}.vpd > /dev/null 2>&1 \; ||:

jp_all: ${ALL_SUB_JGPROVE_TGT}
${ALL_SUB_JGPROVE_TGT}: jp_%: %/jg.tcl
	@echo "jg: proving $*"
	@${JG} -no_gui -acquire_proj $< > $*/jg.log 2>&1
	@sed '/^SUMMARY$$/,/^determined$$/!d;/^determined$$/q' < $*/jg.log > $*/jg.summary
	@cat $*/jg.summary
	@if grep proven < $*/jg.summary | grep '100%' > /dev/null; then \
	    echo "Proven" && exit 0;\
	 else \
		echo "Fail to Proof" && exit 1; \
	 fi

${ALL_SUB_JGVIEW_TGT}: jv_%: %/jg.tcl
	@echo "jg: proving $*"
	@${JG} -acquire_proj $<

.SECONDEXPANSION:
${ALL_SUB_VIEW_TGT}: view_%: $$(wildcard %/config_${TASK}/engine_0/*.vpd)
	@echo "TASK: ${TASK}"
	@echo "Viewing: $<"
	dve -full64 -vpd $<
