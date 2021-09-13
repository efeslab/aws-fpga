clear -all
analyze +define+FORMAL +define+AXICHANNEL_LOGGER_SELF +define+JASPERGOLD -sv09 \
  $env(DESIGNDIR)/transkidbuf_pipeline.sv \
  $env(DESIGNDIR)/transkidbuf.sv \
  $env(DESIGNDIR)/twowayhandshake_logger.sv \
  $env(DESIGNDIR)/axichannel_logger.sv \
  ;
elaborate -top {axichannel_logger}
clock clk
reset -formal !rstn -bound 10
prove -all
exit
