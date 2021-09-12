clear -all
analyze +define+FORMAL +define+TRANSKIDBUF_PIPELINE_SELF +define+JASPERGOLD -sv $env(DESIGNDIR)/transkidbuf_pipeline.sv $env(DESIGNDIR)/transkidbuf.sv;
elaborate -top {transkidbuf_pipeline}
clock clk
reset -formal !rstn -bound 10
prove -all
exit
