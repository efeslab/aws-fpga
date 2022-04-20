1. Always vdefine `CL_DISABLE_IRQ_PCIM`
2. compile with and without `CORRECT_AXI_ATOP_FILTER`

e.g.
`./aws_build_dcp_from_cl.sh -strategy GEFEI -clock_recipe_a A1 -vdefine CL_DISABLE_IRQ_PCIM`
`./aws_build_dcp_from_cl.sh -strategy GEFEI -clock_recipe_a A1 -vdefine CL_DISABLE_IRQ_PCIM,CORRECT_AXI_ATOP_FILTER`
