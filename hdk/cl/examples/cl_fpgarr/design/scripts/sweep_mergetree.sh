#! /bin/bash
set -e
AUTOGROUPING=scripts/cl_fpgarr_autogrouping.py
TREEGEN=scripts/cl_fpgarr_treegen.py
EXPORT_INFO_FILE=/tmp/test.treegen.txt
if [[ ! -f "${AUTOGROUPING}" || ! -f "${TREEGEN}" ]]; then
  echo "check whether you are running in the cl_fpgarr/design directory"
  exit -1
fi
autogen() {
  ${AUTOGROUPING} "$@"
  pushd ../verif/scripts
  make AXI_MEMORY_MODEL=1 VCS=1 C_TEST=test_dram_dma_hwsw_cosim \
    RR_MODE=recordv \
    DEFAULT_DEFINES="+define+EXPORT_MERGE_TREE_INFO +define+EXPORT_MERGE_TREE_INFO_FILE=${EXPORT_INFO_FILE}"
  popd
  ${TREEGEN} -i /tmp/test.treegen.txt
}
autogen "$@"
