#include "AccelSchedule.h"
#include "AccelTest.h"
#include "Timer.h"

extern "C" {
#include "test_common.h"
}

static Timer timers[N_LAYERS] = {
  "xl-FC3",
  "xl-FC2",
  "xl-FC1",
  "xl-Conv6",
  "xl-Conv5",
  "xl-Conv4",
  "xl-Conv3",
  "xl-Conv2",
  "xl-Conv1"
};

// -----------------------------------------------------------------------
// Each layer may need multiple invocations of the accelerator due to
// limited on-chip storage of weights.
//
// This function computes the number of invocations needed and splits
// the weights for each invocation.
//
// We make the following assumptions now:
// 1. Only 1 output image per invocation
// 2. wt_mem is large enough to hold the weights for at least 1 image
// -----------------------------------------------------------------------
void compute_accel_schedule(
    Word* wt,
    Word* kh,
    unsigned n_inputs,
    unsigned n_outputs,
    unsigned width,
    const ap_uint<2> layer_type,  // 0=conv1, 1=conv, 2=dense
    const ap_uint<1> max_pool,
    AccelSchedule &schedule
) {
  assert (wt != NULL);
  assert (kh != NULL);
  const ap_uint<2> width_mode = width >> 4;
  ap_uint<3> layer_mode = 0;
  layer_mode(2,1) = layer_type(1,0);

  // for conv layers
  unsigned width_o = (max_pool==0) ? width : width / 2;
  // imgs_per_batch is the number of output images to compute per batch
  unsigned imgs_per_batch = 0;
  if (layer_type == LAYER_CONV1 || layer_type == LAYER_CONV)
    imgs_per_batch = find_conv_batch_size(width, width_o, n_inputs, n_outputs);

  // recalculate some values if dense layer
  if (layer_type == LAYER_DENSE || layer_type == LAYER_LAST) {
    width_o = 1;
    imgs_per_batch = find_dense_batch_size(n_inputs, n_outputs);
  }

  assert (imgs_per_batch != 0);

  unsigned n_batches = n_outputs / imgs_per_batch;
  schedule.resize(n_batches);

  // divide up the weights according to the value of imgs_per_batch
  unsigned idx = 0;
  for (unsigned o = 0; o < n_outputs; o+=imgs_per_batch, idx++) {
    layer_mode[0] = (o==0) ? 1 : 0;

    // add a new invocation to the schedule
    schedule[idx].n_inputs = n_inputs;
    schedule[idx].n_outputs = imgs_per_batch;
    schedule[idx].layer_mode = layer_mode;
    schedule[idx].width_mode = width_mode;
    schedule[idx].norm_mode = max_pool + 1;

    // now we divide up the weights
    Word* wt_i = schedule[idx].wt;
    if (layer_type == LAYER_CONV1)
      load_conv1_weights(wt, wt_i, o, imgs_per_batch);
    else if (layer_type == LAYER_CONV)
      load_conv_weights(wt, wt_i, o, n_inputs, imgs_per_batch);
    else
      load_dense_weights(wt, wt_i, o, n_inputs, imgs_per_batch);
    // divide up the kh params
    Word* kh_i = schedule[idx].kh;
    if (layer_type != LAYER_LAST)
      load_kh (kh, kh_i, o, imgs_per_batch);
    else
      load_kh (kh, kh_i, o, 2*imgs_per_batch);
  }
}

#define MEM_1G (1LL*1024LL*1024LL*1024LL)

// -----------------------------------------------------------------------
// Invoke accel multiple times based on an AccelSchedule (vec of AccelInfo)
// -----------------------------------------------------------------------
void run_accel_schedule(
    Word* data_i,
    Word* data_o,
    unsigned layer_idx,
    unsigned input_words,
    unsigned output_words,
    ap_uint<1> dmem_mode,
    AccelSchedule& s
) {
  // weight mems
  //static Word* wt_i = (Word*) MEM_ALLOC( WT_WORDS*sizeof(Word) );
  //static Word* kh_i = (Word*) MEM_ALLOC( KH_WORDS*sizeof(Word) );
  //if (!wt_i || !kh_i) {
  //  fprintf(stderr, "**** ERROR: Alloc wt_i or kh_i failed in %s\n", __FILE__);
  //  exit(-2);
  //}

  const unsigned N = s.size();
  const unsigned LAYERS = 9;

  uint32_t int_status_reg, control_reg;
  uint64_t accel_wt_i, accel_kh_i, accel_data_i, accel_data_o;
  int rc = 0;

#ifdef SV_TEST
  setup_send_rdbuf_to_c((uint8_t*)data_i, DMEM_WORDS * sizeof(Word));
#endif

  accel_data_i = 0;
  accel_data_o = MEM_1G;
  accel_wt_i = 2*MEM_1G;
  accel_kh_i = 3*MEM_1G;

  printf("accel_data_i: %lx\n", accel_data_i);
  printf("accel_data_o: %lx\n", accel_data_o);
  printf("accel_wt_i: %lx\n", accel_wt_i);
  printf("accel_kh_i: %lx\n", accel_kh_i);
  printf("input_words: %d\n", input_words);
  printf("output_words: %d\n", output_words);

  rc = do_dma_write((uint8_t*)data_i, input_words * sizeof(Word), accel_data_i, 0, slot_id); 
  //rc = do_dma_write((uint8_t*)data_o, output_words * sizeof(Word), accel_data_o, 0, slot_id); 
  fail_on(rc, out, "DMA write failed");
  printf("accel rounds N: %d\n", N);

  // Invoke accelerator once for each element in the schedule
  for (unsigned i = 0; i < N; ++i) {
    //for (unsigned j = 0; j < WT_WORDS; ++j)
    //  wt_i[j] = s[i].wt[j];
    //for (unsigned j = 0; j < KH_WORDS; ++j)
    //  kh_i[j] = s[i].kh[j];

    timers[LAYERS-1-layer_idx].start();

    do_dma_write((uint8_t*)s[i].wt, WT_WORDS * sizeof(Word), accel_wt_i, 0, slot_id);
    do_dma_write((uint8_t*)s[i].kh, KH_WORDS * sizeof(Word), accel_kh_i, 0, slot_id);

    hls_peek_ocl(0x00, &control_reg);
    printf("control status: %x\n", control_reg);

    hls_poke_ocl(0x10, accel_wt_i & 0xffffffff);
    hls_poke_ocl(0x14, (accel_wt_i >> 32) & 0xffffffff);
    hls_poke_ocl(0x1c, accel_kh_i & 0xffffffff);
    hls_poke_ocl(0x20, (accel_kh_i >> 32) & 0xffffffff);
    hls_poke_ocl(0x28, accel_data_i & 0xffffffff);
    hls_poke_ocl(0x2c, (accel_data_i >> 32) & 0xffffffff);
    hls_poke_ocl(0x34, accel_data_o & 0xffffffff);
    hls_poke_ocl(0x38, (accel_data_o >> 32) & 0xffffffff);
    hls_poke_ocl(0x40, s[i].n_inputs);
    hls_poke_ocl(0x48, s[i].n_outputs);
    hls_poke_ocl(0x50, (i==0) ? input_words : 0);
    hls_poke_ocl(0x58, (i==N-1) ? output_words : 0);
    hls_poke_ocl(0x60, s[i].layer_mode);
    hls_poke_ocl(0x68, dmem_mode);
    hls_poke_ocl(0x70, s[i].width_mode);
    hls_poke_ocl(0x78, s[i].norm_mode);

    hls_poke_ocl(0x04, 1); // Global Interrupt Enable
    hls_poke_ocl(0x08, 1); // Enable ap_done interrupt
    hls_poke_ocl(0x00, 1);

    hls_wait_task_complete(0x00);
    hls_wait(100);

    hls_poke_ocl(0x00, 1 << 4); // make it continue
    hls_poke_ocl(0x0c, 1);
    hls_peek_ocl(0x0c, &int_status_reg);
    printf("interrupt status: %d\n", int_status_reg);

    //top(
    //    wt_i, kh_i, data_i, data_o,
    //    s[i].n_inputs, s[i].n_outputs,
    //    (i==0)   ? input_words : 0,
    //    (i==N-1) ? output_words : 0,
    //    s[i].layer_mode,
    //    dmem_mode,
    //    s[i].width_mode,
    //    s[i].norm_mode
    //);


    timers[LAYERS-1-layer_idx].stop();
  }

  rc = do_dma_read((uint8_t*)data_o, output_words * sizeof(Word), accel_data_o, 0, slot_id);
  fail_on(rc, out, "DMA read failed");

  //MEM_FREE( wt_i );
  //MEM_FREE( kh_i );
out:
  return;
}

// -----------------------------------------------------------------------
// determine the appropriate output batch size which allows the params
// and data to fit within their respective memory sizes
// -----------------------------------------------------------------------
unsigned find_conv_batch_size(unsigned width, unsigned width_o,
                         unsigned n_inputs, unsigned n_outputs) {
  const unsigned input_bsize = DMEM_WORDS*WORD_SIZE / (width*width);
  const unsigned wt_bsize = WT_WORDS*CONV_W_PER_WORD /  n_inputs;
  const unsigned kh_bsize = KH_WORDS*KH_PER_WORD;
  unsigned imgs_per_batch = DMEM_WORDS*WORD_SIZE / (width_o*width_o);

  // adjust output batch size to fit into memories cleanly
  if (imgs_per_batch > n_outputs) imgs_per_batch = n_outputs;
  if (imgs_per_batch > wt_bsize) imgs_per_batch = wt_bsize;
  if (imgs_per_batch > kh_bsize) imgs_per_batch = kh_bsize;
  while (n_outputs % imgs_per_batch != 0) {
    imgs_per_batch--;
  }
  assert(imgs_per_batch != 0);

  DB_PRINT(0, ">> (Wt, KH) batch: (%u %u)\n", wt_bsize, kh_bsize);
  DB_PRINT(0, ">> Final batch: %u\n", imgs_per_batch);

  // We are going to assume the following:
  //  1. We have space for all the input feature maps in dmem
  //  2. We have space for at least n_inputs parameters in wt_i
  assert(n_inputs <= input_bsize);
  assert(wt_bsize != 0);

  return imgs_per_batch;
}

// returns the number of output WORDS per batch
unsigned find_dense_batch_size(unsigned n_inputs, unsigned n_outputs) {
  assert(WT_WORDS*WORD_SIZE >= n_inputs);
  const unsigned wt_bsize = WT_WORDS*WORD_SIZE / n_inputs;
  const unsigned kh_bsize = KH_WORDS*KH_PER_WORD;
  unsigned bits_per_batch = DMEM_WORDS*WORD_SIZE;

  // adjust output batch size to fit into memories cleanly
  if (bits_per_batch > n_outputs) bits_per_batch = n_outputs;
  if (bits_per_batch > wt_bsize) bits_per_batch = wt_bsize;
  if (bits_per_batch > kh_bsize) bits_per_batch = kh_bsize;
  while (n_outputs % bits_per_batch != 0) {
    bits_per_batch--;
  }
  assert(bits_per_batch != 0);

  DB_PRINT(0, ">> (Wt, KH) bits batch: (%u %u)\n", wt_bsize, kh_bsize);
  DB_PRINT(0, ">> Final bits batch: %u\n", bits_per_batch);

  return bits_per_batch;
}

// -----------------------------------------------------------------------
// load weights for 1st conv layer, the weights are arranged linearly
// within the CONVOLVERS banks of the wt_mem such that the first bank
// contains filters 0,1,2,...,C_WT_WORDS-1, etc
// We also pack 3 weights per word
// -----------------------------------------------------------------------
void load_conv1_weights(Word* wt, Word* wt_o, unsigned o, unsigned n_out)
{
  // curr is the index of the starting weight in [wt]
  const unsigned M = 3;
  unsigned curr = o*M;
  unsigned addr_i = curr / CONV_W_PER_WORD;
  unsigned off_i = curr % CONV_W_PER_WORD;

  Word w = wt[addr_i] >> off_i*WT_SIZE;
  Word w_o;
  for (unsigned n = 0; n < n_out; ++n) {
    for (unsigned i = 0; i < M; ++i) {
      if (off_i == 0)
        w = wt[addr_i];

      w_o = w_o >> WT_SIZE;
      w_o(M*WT_SIZE-1, (M-1)*WT_SIZE) =
        w(WT_SIZE-1, 0);
      w = w >> WT_SIZE;

      if (++off_i == CONV_W_PER_WORD) {
        off_i = 0;
        addr_i++;
      }
    }
    wt_o[n] = w_o;
  }
  //printf ("\nLoaded Weights:\n");
  //print_params3d(wt_o, 0, 15);
}

// -----------------------------------------------------------------------
// load weights for the bin conv layers, the weights are arranged within
// the CONVOLVERS banks of the wt_mem such that the first bank contains
// filters 0, CONVOLVERS, 2*CONVOLVERS, ...
// -----------------------------------------------------------------------
void load_conv_weights(Word* wt, Word* wt_o,
                  unsigned o, unsigned n_in, unsigned n_out
) {
  // curr is the index of the starting weight in [wt]
  unsigned curr = o*n_in;
  unsigned addr_i = curr / CONV_W_PER_WORD;
  unsigned off_i = curr % CONV_W_PER_WORD;
  unsigned wt_words = WTS_TO_WORDS(n_in*n_out);
  assert (wt_words <= WT_WORDS);

  Word w = wt[addr_i] >> off_i*WT_SIZE;
  Word w_o[CONVOLVERS];
  for (unsigned i = 0; i < CONVOLVERS; ++i)
    w_o[i] = 0;

  for (unsigned n = 0; n < (wt_words+CONVOLVERS-1)/CONVOLVERS; ++n) {
    for (unsigned i = 0; i < CONV_W_PER_WORD*CONVOLVERS; ++i) {
      if (off_i == 0)
        w = wt[addr_i];

      // for each 3x3 filter, write it to the right partition
      w_o[i % CONVOLVERS] = w_o[i % CONVOLVERS] >> WT_SIZE;
      w_o[i % CONVOLVERS](CONV_W_PER_WORD*WT_SIZE-1, (CONV_W_PER_WORD-1)*WT_SIZE) =
        w(WT_SIZE-1, 0);
      w = w >> WT_SIZE;

      if (++off_i == CONV_W_PER_WORD) {
        //print_wt_word(w);
        off_i = 0;
        addr_i++;
      }
    }

    for (unsigned m = 0; m < CONVOLVERS; ++m)
      wt_o[n*CONVOLVERS+m] = w_o[m];
  }
  //printf ("\nLoaded Weights:\n");
  //print_params3d(wt_o, 0, n_in*n_out);
}

// -----------------------------------------------------------------------
// load n_in*n_out single bit weights into accelerator
// o is which output bit we are starting from
// -----------------------------------------------------------------------
void load_dense_weights(Word* wt, Word* wt_o,
                      unsigned o, unsigned n_in, unsigned n_out
) {
  assert(n_in % WORD_SIZE == 0);
  // load in Word-sized chunks
  for (unsigned i = 0; i < n_in*n_out/WORD_SIZE; ++i) {
    wt_o[i] = wt[o*n_in/WORD_SIZE + i];
  }
}

// -----------------------------------------------------------------------
// load n_out sets of kh params into accelerator
// -----------------------------------------------------------------------
void load_kh(Word* kh, Word kh_i[], unsigned o, unsigned n_out) {
  unsigned kh_addr = o / KH_PER_WORD;
  for (unsigned i = 0; i*KH_PER_WORD < n_out; ++i) {
    kh_i[i] = kh[kh_addr + i];
  }
}

float total_time() {
  float t = 0;
  for (unsigned n = 0; n < N_LAYERS; ++n) {
    t += timers[n].get_time();
  }
  return t;
}
