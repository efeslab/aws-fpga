clear -all
analyze +define+FORMAL +define+TRANSKIDBUF_SELF +define+JASPERGOLD -sv $env(DESIGNDIR)/transkidbuf.sv;
elaborate -top {transkidbuf}
clock clk
reset -formal !rstn -bound 10
prove -all
exit
