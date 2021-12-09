#include <cstddef>
//#include <hls_video.h>

#include "Accel.h"
#include "AccelSchedule.h"
#include "AccelTest.h"

extern "C" {
#include "test_common.h"
}


// used to generate test data
unsigned simple_hash(unsigned x) {
  unsigned temp = (((x)*(x+3)*(x+11)) % 47);
  return temp ^ (temp >> 2) ^ (temp >> 4) ^ (temp >> 6) & 1;
}

//------------------------------------------------------------------------
// Helper test function for the accelerator, random data
//------------------------------------------------------------------------
void test_conv_layer_random(
    const unsigned S,
    Word* wt,
    Word* kh
) {
  const unsigned M = CONVOLVERS*PIX_PER_PHASE / (S*S);

  // Generate the input data
  assert (M*S*S <= DMEM_WORDS*WORD_SIZE);
  Word* data_i = (Word*) MEM_ALLOC( DMEM_WORDS * sizeof(Word) );
  for (unsigned m = 0; m < M; ++m) {
    for (unsigned r = 0; r < S; ++r) {
      for (unsigned c = 0; c < S; ++c) {
        set_bit(data_i, m*S*S+r*S+c, simple_hash(m*S*S+r*S+c));
  }  }  }

  assert (S*S <= DMEM_O_WORDS*WORD_SIZE);
  Word* data_o = (Word*) MEM_ALLOC( DMEM_O_WORDS * sizeof(Word) );

  DB(2,
    printf ("*data*:\n");
    print_bits3d(data_i, 0, 2, S, 8,S);
    printf ("*params*:\n");
    print_bits3d(wt, 0, 2, K, K,K);
  );

  // Compute conv reference
  Word conv_ref[S*S];
  padded_conv(data_i, wt, conv_ref, M, S);
  // Compute bin reference
  Word khword = kh[0];
  NormComp nc;  nc(15,0) = khword(15,0);
  Word bin_ref[S*S];
  for (unsigned i = 0; i < S*S; ++i) {
    Bit b = (conv_ref[i] < nc) ? -1 : 0;
    set_bit(bin_ref, i, b);
  }

  test_conv_layer(
      wt, kh, data_i, data_o, conv_ref, bin_ref,
      M, 1, S
    );

  MEM_FREE( data_i );
  MEM_FREE( data_o );
}

//------------------------------------------------------------------------
// Main
//------------------------------------------------------------------------
#if defined(SV_TEST) && defined(INT_MAIN)
extern "C" int test_main(uint32_t *exit_code)
#elif defined(SV_TEST)
extern "C" void test_main(uint32_t *exit_code)
#else
int main()
#endif
{
  const unsigned N = 1;

  Word* wt = new Word[WT_WORDS];
  Word* kh = new Word[KH_WORDS];

  // setup AWSF1 simulation

#if defined(SCOPE)
  svScope scope;
  scope = svGetScopeFromName("tb");
  svSetScope(scope);
#endif
  printf("Starting DDR init...\n");
#ifdef SV_TEST
  init_ddr();
  printf("Done DDR init...\n");
#endif
  int rc = 0;
  rc = hls_init();
  fail_on(rc, out, "init hls failed");
  rc = init_rr(0);
  fail_on(rc, out, "init rr failed");
  do_pre_rr();
  fail_on(is_replay(), out, "Skip application code, replaying");

  // initialize the kernel weights
  for (unsigned m = 0; m < WT_WORDS; ++m) {
    for (unsigned i = 0; i < WORD_SIZE; ++i)
      set_bit(wt, m*WORD_SIZE+i, simple_hash(m*WORD_SIZE+i));
  }
  // initialize the batch-norm params
  for (unsigned n = 0; n < N; ++n) {
    NormComp nc = 10 + 10*n;

    int off = n % KH_PER_WORD;

    Word w = kh[n/KH_PER_WORD];
    w((off+1)*16-1, off*16) = nc(15,0);
    kh[n/KH_PER_WORD] = w;
  }

  test_conv_layer_random( 8, wt, kh);
  test_conv_layer_random(16, wt, kh);
  test_conv_layer_random(32, wt, kh);

  printf ("Tests passed!\n");


out:
  delete[] wt;
  delete[] kh;

  do_post_rr();
  hls_exit();

#if !defined(SV_TEST)
  return 0;
#elif defined(INT_MAIN)
  *exit_code = 0;
  return 0;
#else
  *exit_code = 0;
#endif
}