clear -all
analyze +define+FORMAL +define+TWOWAYHANDSHAKE_LOGGER_SELF +define+JASPERGOLD -sv $env(DESIGNDIR)/twowayhandshake_logger.sv;
elaborate -top {twowayhandshake_logger}
clock clk
reset -formal !rstn -bound 10
prove -all
exit
