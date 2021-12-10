#include <cstddef>
#include <cstdlib>
//#include <hls_video.h>

#include "Accel.h"
#include "AccelSchedule.h"
#include "AccelTest.h"
#include "Dense.h"
#include "ZipIO.h"
#include "ParamIO.h"
#include "DataIO.h"
#include "Timer.h"

extern "C" {
#include "test_common.h"
}

extern int main_bnn(int argc, char** argv);
extern int main_random();
/* use the stdout logger */
const struct logger *logger = &logger_stdout;

#if defined(SV_TEST) && defined(INT_MAIN)
extern "C" int test_main(uint32_t *exit_code)
#elif defined(SV_TEST)
extern "C" void test_main(uint32_t *exit_code)
#else
int main(int argc, char** argv)
#endif
{
#if defined(SCOPE)
  svScope scope;
  scope = svGetScopeFromName("tb");
  svSetScope(scope);
#endif
#if defined(SV_TEST)
  printf("Starting DDR init...\n");
  init_ddr();
  printf("Done DDR init...\n");
#endif

  int rc = 0;
  const bool USE_BNN = getenv("USE_BNN") != NULL;

  /* setup logging to print to stdout */
  rc = log_init("test_dram_dma_hwsw_cosim");
  fail_on(rc, out, "Unable to initialize the log.");
  rc = log_attach(logger, NULL, 0);
  fail_on(rc, out, "%s", "Unable to attach to the log.");

  /* initialize the fpga_plat library */
  rc = fpga_mgmt_init();
  fail_on(rc, out, "Unable to initialize the fpga_mgmt library");

  // ---------------------------------------------------------------------
  // [FPGARR] Initialize RR
  // ---------------------------------------------------------------------
  rc = hls_init();
  fail_on(rc, out, "init hls failed");
  rc = init_rr(0);
  fail_on(rc, out, "init rr failed");
  do_pre_rr();
  fail_on(is_replay(), out, "Skip application code, replaying");

  if (USE_BNN) {
    #if defined(SV_TEST)
      int argc = 2;
      char *argv[3] {"test_main", "1", NULL};
    #endif
    rc = main_bnn(argc, argv);
  } else {
    rc = main_random();
  }

out:
  do_post_rr();
  hls_exit();

#if !defined(SV_TEST)
  return rc;
#elif defined(INT_MAIN)
  *exit_code = rc;
  return rc;
#else
  *exit_code = rc;
#endif
}
