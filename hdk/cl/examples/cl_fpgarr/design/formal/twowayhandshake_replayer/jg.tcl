clear -all
analyze +define+FORMAL +define+TWOWAYHANDSHAKE_REPLAYER_SELF +define+JASPERGOLD -sv $env(DESIGNDIR)/twowayhandshake_replayer.sv;
elaborate -top {twowayhandshake_replayer}
clock clk
reset -formal !rstn -bound 10
prove -all
exit
