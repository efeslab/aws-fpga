#include "cl_fpgarr.h"
#include <stdio.h>
#include <fcntl.h>

#ifdef SV_TEST
# include <fpga_pci_sv.h>
#endif

/*
 * Parse RR_MODE register configuration
 */
typedef union {
    struct {
        uint8_t recordEn : 1;
        uint8_t replayEn : 1;
        uint32_t unused: 30;
    };
    uint32_t val;
} rr_mode_t;
rr_mode_t rr_mode = { .recordEn = 0, .replayEn = 0, .unused = 0};

void init_rr() {
    char *rr_mode_env = getenv("RR_MODE");
    if (strcmp(rr_mode_env, "record") == 0) {
        rr_mode.recordEn = 1;
    } else if (strcmp(rr_mode_env, "replay") == 0) {
        rr_mode.replayEn = 1;
    } else {
        printf("WARNING: Invalid RR Mode\n");
    }
    printf("RR Mode (env): %s\n", rr_mode_env);
    printf("RR Mode (csr): %#x\n", rr_mode.val);
}

/*
 * Setup record/replay trace buffer
 */
uint8_t *trace_buffer = NULL;
uint64_t trace_buffer_hi = 0;
uint64_t trace_buffer_lo = 0;
uint64_t trace_buffer_size_hi = 0;
uint64_t trace_buffer_size_lo = 0;
void do_record_start() {
    trace_buffer = aligned_alloc(4096, 0x1000000);
    sv_map_host_memory(trace_buffer);
    trace_buffer_hi = ((uint64_t) trace_buffer >> 32) & 0xffffffff;
    trace_buffer_lo = ((uint64_t) trace_buffer) & 0xffffffff;
    trace_buffer_size_hi = 0;
    trace_buffer_size_lo = 0x1000000;

    // configure csrs via rr_cfg_bus
    cl_poke_bar1(RR_CSR_ADDR(BUF_ADDR_HI), trace_buffer_hi);
    cl_poke_bar1(RR_CSR_ADDR(BUF_ADDR_LO), trace_buffer_lo);
    cl_poke_bar1(RR_CSR_ADDR(BUF_SIZE_HI), trace_buffer_size_hi);
    cl_poke_bar1(RR_CSR_ADDR(BUF_SIZE_LO), trace_buffer_size_lo);
    cl_poke_bar1(RR_CSR_ADDR(WRITE_BUF_UPDATE), 1);
    cl_poke_bar1(RR_CSR_ADDR(RR_MODE), rr_mode.val); // 0b001
}
void do_record_stop() {
    sv_pause(1);
    cl_poke_bar1(RR_CSR_ADDR(RECORD_FORCE_FINISH), 1);
    sv_pause(1);

    uint64_t record_bits;
    uint32_t record_bits_lo, record_bits_hi;

    cl_peek_bar1(RR_CSR_ADDR(RECORD_BITS_HI), &record_bits_hi);
    cl_peek_bar1(RR_CSR_ADDR(RECORD_BITS_LO), &record_bits_lo);
    record_bits = (record_bits_hi << 32) | record_bits_lo;

    printf("record_bits: %d\n", record_bits);

    printf("Trace Buffer Dump:\n");
    for (int i = 0; i < 1024; i++) {
        printf("%02x", trace_buffer[i]);
        if (i % 64 == 63) {
            printf("\n");
        } else if (i % 8 == 7) {
            printf(" ");
        } else if (i % 4 == 3) {
            printf("_");
        }
    }

    int fd = open("record.dump", O_RDWR|O_CREAT, S_IRUSR|S_IWUSR);
    write(fd, &record_bits, 8);
    write(fd, trace_buffer, 0x1000000);
    fsync(fd);
    close(fd);
    free(trace_buffer);
}
void do_replay_start() {
    trace_buffer = aligned_alloc(4096, 0x1000000);
    sv_map_host_memory(trace_buffer);
    trace_buffer_hi = ((uint64_t) trace_buffer >> 32) & 0xffffffff;
    trace_buffer_lo = ((uint64_t) trace_buffer) & 0xffffffff;
    trace_buffer_size_hi = 0;
    trace_buffer_size_lo = 0x1000000;

    uint64_t record_bits;

    int fd = open("record.dump", O_RDONLY);

    read(fd, &record_bits, 8);
    uint64_t trace_buffer_size = ((record_bits - 1) / 512 + 1) * 64;
    trace_buffer_size_hi = (trace_buffer_size >> 32) & 0xffffffff;
    trace_buffer_size_lo = trace_buffer_size & 0xffffffff;

    read(fd, trace_buffer, 0x1000000);
    close(fd);
    // configure csrs via rr_cfg_bus
    cl_poke_bar1(RR_CSR_ADDR(BUF_ADDR_HI), trace_buffer_hi);
    cl_poke_bar1(RR_CSR_ADDR(BUF_ADDR_LO), trace_buffer_lo);
    cl_poke_bar1(RR_CSR_ADDR(BUF_SIZE_HI), trace_buffer_size_hi);
    cl_poke_bar1(RR_CSR_ADDR(BUF_SIZE_LO), trace_buffer_size_lo);
    cl_poke_bar1(RR_CSR_ADDR(RR_MODE), 0x2); // 0b010
    cl_poke_bar1(RR_CSR_ADDR(READ_BUF_UPDATE), 1);
}
void do_replay_stop() {
    sv_pause(1);
}
void do_pre_rr() {
    if (is_record()) {
        do_record_start();
    } else if (is_replay()) {
        do_replay_start();
    }
}
void do_post_rr() {
    if (is_record()) {
        do_record_stop();
    } else if (is_replay()) {
        do_replay_stop();
    }
}

/*
 * MISC internal utilities
 */
uint8_t is_record() {
    return rr_mode.recordEn == 1;
}

uint8_t is_replay() {
    return rr_mode.replayEn == 1;
}
