#include "cl_fpgarr.h"

#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <utils/log.h>

#include "cl_fpgarr_cfg.h"
#include "cl_fpgarr_csrs.h"
#include "cl_fpgarr_csrs_decode.h"
#include "cl_fpgarr_utils.h"

rr_mode_t rr_mode = RR_MODE_INIT;

static uint64_t buffer_size;
static struct timespec rr_start_time;
static uint64_t rr_user_timer_ns = 0;
static struct timespec rr_user_start_time;
static const char *record_path = DEFAULT_RECORD_PATH;
static const char *validate_record_path = DEFAULT_VALIDATE_RECORD_PATH;
static const char *validate_replay_path = DEFAULT_VALIDATE_REPLAY_PATH;

int init_rr(int slot_id) {
    char *rr_mode_env = getenv("RR_MODE");
    if (!rr_mode_env) {
        printf("Error: RR_MODE is undefined!\n");
        return -1;
    }
    if (strcmp(rr_mode_env, "record") == 0) {
        rr_mode.recordEn = 1;
        rr_mode.enable_PCIM_B_buffer = 1;
        rr_mode.enable_PCIM_workaround = 1;
    } else if (strcmp(rr_mode_env, "recordv") == 0) {
        rr_mode.recordEn = 1;
        rr_mode.outputValidateEn = 1;
        rr_mode.enable_PCIM_B_buffer = 1;
        rr_mode.enable_PCIM_workaround = 1;
    } else if (strcmp(rr_mode_env, "replay") == 0) {
        rr_mode.replayEn = 1;
        rr_mode.enable_PCIM_B_buffer = 0;
        rr_mode.enable_PCIM_workaround = 0;
    } else if (strcmp(rr_mode_env, "replayv") == 0) {
        rr_mode.replayEn = 1;
        rr_mode.outputValidateEn = 1;
        rr_mode.enable_PCIM_B_buffer = 0;
        rr_mode.enable_PCIM_workaround = 0;
    } else if (strcmp(rr_mode_env, "none") == 0) {
        rr_mode.recordEn = 0;
        rr_mode.replayEn = 0;
        rr_mode.outputValidateEn = 0;
    } else {
        printf("WARNING: Invalid RR Mode\n");
    }

    char *rr_buf_sizeB = getenv("RR_BUFSIZEB");
    if (!rr_buf_sizeB) {
        buffer_size = DEFAULT_BUFFER_SIZE;
    } else {
        buffer_size = atoi(rr_buf_sizeB);
    }
    // overriding
    const char *record_path_override = getenv("RR_RECORD_PATH");
    if (record_path_override) {
        record_path = record_path_override;
        printf("Overriding RR_RECORD_PATH: %s\n", record_path);
    }
    const char *validate_record_path_overide = getenv("RR_VALIDATE_RECORD_PATH");
    if (validate_record_path_overide) {
        validate_record_path = validate_record_path_overide;
        printf("Overriding RR_VALIDATE_RECORD_PATH: %s\n", validate_record_path);
    }
    const char *validate_replay_path_overide = getenv("RR_VALIDATE_REPLAY_PATH");
    if (validate_replay_path_overide) {
        validate_replay_path = validate_replay_path_overide;
        printf("Overriding RR_VALIDATE_REPLAY_PATH: %s\n", validate_replay_path);
    }
    // print basic info
    printf("RR Mode (env): %s\n", rr_mode_env);
    printf("RR Mode (csr): %#x\n", rr_mode.val);
    printf("RR Buffer Size: %ldB\n", buffer_size);
    printf("SW RR_CSR_VERSION %d\n", RR_CSR_VERSION_INT);

    // I experienced that random stuff left errno to nonzero before entering rr
    errno = 0;
    int rc;
#ifndef SV_TEST
    // init pci_bar1
    rc = fpga_pci_attach(slot_id, /* pf_id */ 0, /* bar_id */ 1,
                             /* flags */ 0, &pci_bar1_handle);
    assert(rc == 0);
#endif

    uint32_t hw_rr_csr_version;
    rc = rr_cfg_peek(RR_CSR_VERSION, &hw_rr_csr_version);
    fail_on(rc, err_out, "Fail to peek HW_RR_CSR_VERSION");
    if (hw_rr_csr_version != RR_CSR_VERSION_INT) {
        printf("HW RR_CSR_VERSION %d\n", hw_rr_csr_version);
        printf("WARNING: RR_CSR_VERSION mismatches!!!!!\n");
    }
    if (hw_rr_csr_version > RR_CSR_VERSION_INT) {
        printf("HW RR_CSR_VERSION is newer than software, abort\n");
        printf(
            "Newer software is allowed to run with out-dated hardware, but not "
            "vice versa.\n");
        goto err_out;
    }
    return 0;
err_out:
    return -1;
}

/*
 * Setup record/replay trace buffer
 */
static uint8_t *record_buffer = NULL;
static uint64_t record_buffer_size = 0;

static uint8_t *validate_buffer = NULL;
static uint64_t validate_buffer_size = 0;

static uint8_t *replay_buffer = NULL;
static uint64_t replay_buffer_size;
uint64_t replay_bits;

void do_record_start() {
    // always set RR_MODE first to avoid silently dropping traffic
    rr_cfg_poke(RR_MODE, rr_mode.val);
    record_buffer_size = buffer_size;
    record_buffer =
        rr_alloc_setup_buffer(record_buffer_size, RECORD_BUF_UPDATE);

    if (is_validate()) {
        validate_buffer_size = buffer_size;
        validate_buffer =
            rr_alloc_setup_buffer(validate_buffer_size, VALIDATE_BUF_UPDATE);
    }
}

void do_record_stop() {
    rr_wait_counter_stable(RECORD_BITS_LO, RECORD_BITS_HI);
    if (is_validate()) {
        rr_wait_counter_stable(VALIDATE_BITS_LO, VALIDATE_BITS_HI);
    }
    rr_cfg_poke(RECORD_FORCE_FINISH, 1);
    uint64_t record_bits =
        rr_wait_counter_stable(RECORD_BITS_LO, RECORD_BITS_HI);
    dump_trace("Record Buffer", record_path, record_buffer, record_bits);
    rr_dealloc_buffer(record_buffer);
    if (is_validate()) {
        uint64_t validate_bits =
            rr_wait_counter_stable(VALIDATE_BITS_LO, VALIDATE_BITS_HI);
        dump_trace("Validate Buffer", validate_record_path, validate_buffer,
                   validate_bits);
        rr_dealloc_buffer(validate_buffer);
    }
    destroy_irq();
}
void do_replay_start() {
    // always set RR_MODE first to avoid silently dropping traffic
    rr_cfg_poke(RR_MODE, rr_mode.val);
    if (is_validate()) {
        validate_buffer_size = buffer_size;
        validate_buffer =
            rr_alloc_setup_buffer(validate_buffer_size, VALIDATE_BUF_UPDATE);
    }
    int fd = open(record_path, O_RDONLY);
    read(fd, &replay_bits, TRACE_LEN_BYTES);

    uint32_t replay_bits_hi = UINT64_HI32(replay_bits);
    uint32_t replay_bits_lo = UINT64_LO32(replay_bits);
    replay_buffer_size = ((replay_bits - 1) / 512 + 1) * 64;

    uint64_t replay_pa;
    replay_buffer = rr_alloc_buffer(replay_buffer_size, &replay_pa);
    read(fd, replay_buffer, replay_buffer_size);
    close(fd);

    rr_cfg_poke(REPLAY_BITS_HI, replay_bits_hi);
    rr_cfg_poke(REPLAY_BITS_LO, replay_bits_lo);
#ifdef SV_TEST
    // write to REPLAY_BUF_UPDATE will start the replay (i.e. pcim read)
    // So always put it in the last step
    setup_buffer(replay_buffer, replay_buffer_size, REPLAY_BUF_UPDATE);
#else
    setup_buffer((uint8_t*)replay_pa, replay_buffer_size, REPLAY_BUF_UPDATE);
#endif
}
void do_replay_stop() {
    uint64_t rt_replay_bits;
    do {
        rt_replay_bits =
            rr_wait_counter_stable(RT_REPLAY_BITS_LO, RT_REPLAY_BITS_HI);
        log_info("runtime replay bits (%ld) =?= replay bits in the trace (%ld)",
                rt_replay_bits, replay_bits);
    } while (rt_replay_bits != replay_bits);
    rr_dealloc_buffer(replay_buffer);

    if (is_validate()) {
        rr_wait_counter_stable(VALIDATE_BITS_LO, VALIDATE_BITS_HI);
        rr_cfg_poke(RECORD_FORCE_FINISH, 1);
        uint64_t validate_bits =
            rr_wait_counter_stable(VALIDATE_BITS_LO, VALIDATE_BITS_HI);
        dump_trace("Validate Buffer", validate_replay_path, validate_buffer,
                   validate_bits);
        rr_dealloc_buffer(validate_buffer);
    }
}
void do_pre_rr() {
    // always allocate irq buffer first to make sure its phy addr is always the
    // same (at least I hope this works)
    init_irq();
    if (is_record()) {
        do_record_start();
    } else if (is_replay()) {
        do_replay_start();
    }
    clock_gettime(CLOCK_MONOTONIC, &rr_start_time);
}
void do_post_rr() {
    struct timespec rr_end_time, elapsed_time;
    uint64_t elapsed_ns;
    clock_gettime(CLOCK_MONOTONIC, &rr_end_time);
    timespec_sub(&rr_start_time, &rr_end_time, &elapsed_time);
    elapsed_ns = elapsed_time.tv_sec * 1000000000L + elapsed_time.tv_nsec;
    log_info("RR pre_rr->post_rr, elapsed ns: %ld", elapsed_ns);
    log_info("RR user timer, elapsed ns: %ld", rr_user_timer_ns);
    if (is_record()) {
        do_record_stop();
    } else if (is_replay()) {
        do_replay_stop();
    }
    debug_check();
#ifndef SV_TEST
    if (pci_bar1_handle != PCI_BAR_HANDLE_INIT)
        assert(fpga_pci_detach(pci_bar1_handle) == 0);
#endif
}

/*
 * MISC internal utilities
 */
uint8_t is_record() { return rr_mode.recordEn == 1; }

uint8_t is_replay() { return rr_mode.replayEn == 1; }

uint8_t is_validate() { return rr_mode.outputValidateEn == 1; }

void rr_wait_irq(uint32_t irq_id) {
    uint32_t offset = irq_id * 64;
    assert(irq_buffer);
    assert(offset < irq_buffer_size);
    while (irq_buffer[offset] == 0) {
#ifdef SV_TEST
        rr_wait(1);
#else
        ;
#endif
    }
    irq_buffer[offset] = 0;
}

void rr_user_timer_begin() {
    clock_gettime(CLOCK_MONOTONIC, &rr_user_start_time);
}

void rr_user_timer_end() {
    struct timespec rr_user_end_time, elapsed_time;
    uint64_t elapsed_ns;
    clock_gettime(CLOCK_MONOTONIC, &rr_user_end_time);
    timespec_sub(&rr_user_start_time, &rr_user_end_time, &elapsed_time);
    elapsed_ns = elapsed_time.tv_sec * 1000000000L + elapsed_time.tv_nsec;
    rr_user_timer_ns += elapsed_ns;
}
