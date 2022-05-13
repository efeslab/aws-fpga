BATCH1="3d_rendering bnn digit_recognition face_detection"
BATCH2="spam_filter optical_flow sssp sha256 mobilenet"

for i in ${BATCH2}; do
  echo "#################################APP is ${i}" >> automate_synthesis.log
  HLS_DESIGN=$i ./aws_build_dcp_from_cl.sh -strategy GEFEI -clock_recipe_a A1 >> automate_synthesis.log 2>1
  # -vdefine COUNT_DDR
  sleep 600
done
