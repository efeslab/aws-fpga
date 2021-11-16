#include "cl_fpgarr.h"
#include <stdio.h>
#include <fcntl.h>
#include <stdlib.h>

#ifdef SV_TEST
#include <utils/sh_dpi_tasks.h>
# include <fpga_pci_sv.h>
#endif

/*
 * Parse RR_MODE register configuration
 */
typedef union {
    struct {
        uint8_t recordEn : 1;         // bit 0
        uint8_t replayEn : 1;         // bit 1
        uint8_t outputValidateEn : 1; // bit 2
        uint32_t unused: 29;
    };
    uint32_t val;
} rr_mode_t;
rr_mode_t rr_mode = {
    .recordEn = 0,
    .replayEn = 0,
    .outputValidateEn = 0,
    .unused = 0
};

int init_rr() {
    char *rr_mode_env = getenv("RR_MODE");
    if (strcmp(rr_mode_env, "record") == 0) {
        rr_mode.recordEn = 1;
    } else if (strcmp(rr_mode_env, "recordv") == 0) {
        rr_mode.recordEn = 1;
        rr_mode.outputValidateEn = 1;
    } else if (strcmp(rr_mode_env, "replay") == 0) {
        rr_mode.replayEn = 1;
    } else if (strcmp(rr_mode_env, "replayv") == 0) {
        rr_mode.replayEn = 1;
        rr_mode.outputValidateEn = 1;
    } else {
        printf("WARNING: Invalid RR Mode\n");
    }
    printf("RR Mode (env): %s\n", rr_mode_env);
    printf("RR Mode (csr): %#x\n", rr_mode.val);
    printf("SW RR_CSR_VERSION %d\n", RR_CSR_VERSION_INT);

    uint32_t hw_rr_csr_version;
    cl_peek_bar1(RR_CSR_ADDR(RR_CSR_VERSION), &hw_rr_csr_version);
    if (hw_rr_csr_version != RR_CSR_VERSION_INT) {
        printf("HW RR_CSR_VERSION %d\n", hw_rr_csr_version);
        printf("RR_CSR_VERSION mismatches, abort.\n");
        return -1;
    }
    return 0;
}

/*
 * Setup record/replay trace buffer
 */
uint8_t *record_buffer = NULL;
uint64_t record_buffer_size = 0;

uint8_t *validate_buffer = NULL;
uint64_t validate_buffer_size = 0;

uint8_t *replay_buffer = NULL;
uint64_t replay_buffer_size;

static void setup_buffer(uint8_t *p, uint64_t size, uint64_t buf_update_csr) {
    uint32_t trace_buffer_hi, trace_buffer_lo;
    uint32_t trace_buffer_size_hi, trace_buffer_size_lo;
    trace_buffer_hi = UINT64_HI32(p);
    trace_buffer_lo = UINT64_LO32(p);
    trace_buffer_size_hi = UINT64_HI32(size);
    trace_buffer_size_lo = UINT64_LO32(size);

    sv_map_host_memory(p);
    // configure csrs via rr_cfg_bus
    cl_poke_bar1(RR_CSR_ADDR(BUF_ADDR_HI), trace_buffer_hi);
    cl_poke_bar1(RR_CSR_ADDR(BUF_ADDR_LO), trace_buffer_lo);
    cl_poke_bar1(RR_CSR_ADDR(BUF_SIZE_HI), trace_buffer_size_hi);
    cl_poke_bar1(RR_CSR_ADDR(BUF_SIZE_LO), trace_buffer_size_lo);
    cl_poke_bar1(RR_CSR_ADDR(buf_update_csr), 1);
}
void do_record_start() {
    // always set RR_MODE first to avoid silently dropping traffic
    cl_poke_bar1(RR_CSR_ADDR(RR_MODE), rr_mode.val);
    record_buffer = aligned_alloc(BUFFER_ALIGNMENT, DEFAULT_BUFFER_SIZE);
    record_buffer_size = DEFAULT_BUFFER_SIZE;
    setup_buffer(record_buffer, record_buffer_size, RECORD_BUF_UPDATE);

    if (is_validate()) {
        validate_buffer = aligned_alloc(BUFFER_ALIGNMENT, DEFAULT_BUFFER_SIZE);
        validate_buffer_size = DEFAULT_BUFFER_SIZE;
        setup_buffer(validate_buffer, validate_buffer_size, VALIDATE_BUF_UPDATE);
    }
}

static uint64_t cl_peek_bar1_u64(uint64_t hi_csr, uint64_t lo_csr) {
    uint32_t hi, lo;
    cl_peek_bar1(RR_CSR_ADDR(lo_csr), &lo);
    cl_peek_bar1(RR_CSR_ADDR(hi_csr), &hi);
    return UINT64_FROM32(hi, lo);
}

static void dump_trace(const char *msg, const char *filename, uint8_t *p,
        uint64_t size_bits) {
    int size_bytes = (size_bits + 7) / 8;
    // print trace to stdout
    printf("%s: size %d bits (%d B)\n", msg, size_bits, size_bytes);
    printf("%s: Trace Dump:\n", msg);
    for (int i = 0; i < size_bytes; ++i) {
        // put 1-byte a time
        printf("%02x", p[i]);
        if (i % 64 == 63) {
            printf("\n");
        } else if (i % 8 == 7) {
            printf(" ");
        } else if (i % 4 == 3) {
            printf("_");
        }
    }
    putchar('\n');
    // save trace to file
    int fd = open(filename, O_RDWR|O_CREAT, S_IRUSR | S_IWUSR);
    write(fd, &size_bits, TRACE_LEN_BYTES);
    write(fd, p, size_bytes);
    fsync(fd);
    close(fd);
}

void do_record_stop() {
    sv_pause(1);
    cl_poke_bar1(RR_CSR_ADDR(RECORD_FORCE_FINISH), 1);
    sv_pause(1);

    uint64_t record_bits = cl_peek_bar1_u64(RECORD_BITS_HI, RECORD_BITS_LO);;
    dump_trace("Record Buffer", "record.dump", record_buffer, record_bits);
    free(record_buffer);

    if (is_validate()) {
        uint64_t validate_bits = cl_peek_bar1_u64(
                VALIDATE_BITS_HI, VALIDATE_BITS_LO);
        dump_trace("Validate Buffer", "validate_record.dump", validate_buffer,
                validate_bits);
        free(validate_buffer);
    }
}
void do_replay_start() {
    // always set RR_MODE first to avoid silently dropping traffic
    cl_poke_bar1(RR_CSR_ADDR(RR_MODE), rr_mode.val);
    if (is_validate()) {
        validate_buffer = aligned_alloc(BUFFER_ALIGNMENT, DEFAULT_BUFFER_SIZE);
        validate_buffer_size = DEFAULT_BUFFER_SIZE;
        setup_buffer(validate_buffer, validate_buffer_size, VALIDATE_BUF_UPDATE);
    }
    int fd = open("record.dump", O_RDONLY);
    uint64_t replay_bits;
    read(fd, &replay_bits, TRACE_LEN_BYTES);

    uint32_t replay_bits_hi = UINT64_HI32(replay_bits);
    uint32_t replay_bits_lo = UINT64_LO32(replay_bits);
    replay_buffer_size = ((replay_bits - 1) / 512 + 1) * 64;

    replay_buffer = aligned_alloc(4096, replay_buffer_size);
    read(fd, replay_buffer, replay_buffer_size);
    close(fd);

    cl_poke_bar1(RR_CSR_ADDR(REPLAY_BITS_HI), replay_bits_hi);
    cl_poke_bar1(RR_CSR_ADDR(REPLAY_BITS_LO), replay_bits_lo);
    // write to REPLAY_BUF_UPDATE will start the replay (i.e. pcim read)
    // So always put it in the last step
    setup_buffer(replay_buffer, replay_buffer_size, REPLAY_BUF_UPDATE);

}
void do_replay_stop() {
    sv_pause(1);
    free(replay_buffer);

    if (is_validate()) {
        cl_poke_bar1(RR_CSR_ADDR(RECORD_FORCE_FINISH), 1);
        sv_pause(1);
        uint64_t validate_bits = cl_peek_bar1_u64(
                VALIDATE_BITS_HI, VALIDATE_BITS_LO);
        dump_trace("Validate Buffer", "validate_replay.dump", validate_buffer,
                validate_bits);
        free(validate_buffer);
    }
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

uint8_t is_validate() {
    return rr_mode.outputValidateEn == 1;
}
