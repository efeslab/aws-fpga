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

extern "C" int hls_main(int argc, char** argv)
{
  int rc = 0;
  const bool USE_BNN = getenv("USE_BNN") != NULL;

  if (USE_BNN) {
    #if defined(SV_TEST)
      int argc = 2;
      char *argv[3] = {"test_main", "1", NULL};
    #endif
    rc = main_bnn(argc, argv);
  } else {
    rc = main_random();
  }

out:
  return rc;
}
