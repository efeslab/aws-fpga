#include "cl_fpgarr.h"

#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <assert.h>

#include <utils/log.h>
#ifdef SV_TEST
#include <fpga_pci_sv.h>
#include <utils/sh_dpi_tasks.h>
#else
#include <fpga_pci.h>
#include <fpga_hugealloc.h>
#endif
void debug_check();
/*
 * Parse RR_MODE register configuration
 */
typedef union {
    struct {
        uint8_t recordEn : 1;          // bit 0
        uint8_t replayEn : 1;          // bit 1
        uint8_t outputValidateEn : 1;  // bit 2
        uint32_t unused : 29;
    };
    uint32_t val;
} rr_mode_t;

rr_mode_t rr_mode = {
    .recordEn = 0, .replayEn = 0, .outputValidateEn = 0, .unused = 0};

#ifndef SV_TEST
pci_bar_handle_t pci_bar1_handle = PCI_BAR_HANDLE_INIT;
#endif

static inline int rr_cfg_poke(uint64_t csr_idx, uint32_t value) {
#ifdef SV_TEST
    cl_poke_bar1(RR_CSR_ADDR(csr_idx), value);
    return 0;
#else
    assert(pci_bar1_handle != PCI_BAR_HANDLE_INIT);
    return fpga_pci_poke(pci_bar1_handle, RR_CSR_ADDR(csr_idx), value);
#endif
}

static inline int rr_cfg_peek(uint64_t csr_idx, uint32_t *value) {
#ifdef SV_TEST
    cl_peek_bar1(RR_CSR_ADDR(csr_idx), value);
    return 0;
#else
    assert(pci_bar1_handle != PCI_BAR_HANDLE_INIT);
    return fpga_pci_peek(pci_bar1_handle, RR_CSR_ADDR(csr_idx), value);
#endif
}

// TODO: There is a fpga_pci_peek64 but I haven't tested it.
static inline int rr_cfg_peek64(uint64_t lo_csr_idx, uint64_t hi_csr_idx,
                                uint64_t *value) {
    uint32_t lo, hi;
    int rc = 0;
    rc |= rr_cfg_peek(lo_csr_idx, &lo);
    rc |= rr_cfg_peek(hi_csr_idx, &hi);
    *value = UINT64_FROM32(hi, lo);
    return rc;
}

static uint64_t buffer_size;

int init_rr(int slot_id) {
    char *rr_mode_env = getenv("RR_MODE");
    if (!rr_mode_env) {
        printf("Error: RR_MODE is undefined!\n");
        return -1;
    }
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
    printf("RR Mode (env): %s\n", rr_mode_env);
    printf("RR Mode (csr): %#x\n", rr_mode.val);
    printf("RR Buffer Size: %ldB\n", buffer_size);
    printf("SW RR_CSR_VERSION %d\n", RR_CSR_VERSION_INT);

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

// pa is not used in software simulation
static uint8_t *rr_alloc_buffer(uint64_t size, uint64_t *pa) {
#ifdef SV_TEST
    uint8_t *va;
    va = aligned_alloc(BUFFER_ALIGNMENT, size);
    assert(va != NULL);
    return va;
#else
    void *va;
    uint64_t sizeB;
    assert(fpga_hugealloc_get(&va, pa, &sizeB) == 0);
    assert(size <= sizeB);
    memset(va, 0, sizeB);
    log_info("rr_alloc_buffer, va %p, pa %p, size %ld\n", va, (void *)(*pa),
             sizeB);
    return (uint8_t *)(va);
#endif
}

static void setup_buffer(uint8_t *p, uint64_t size, uint64_t buf_update_csr) {
    uint32_t trace_buffer_hi, trace_buffer_lo;
    uint32_t trace_buffer_size_hi, trace_buffer_size_lo;
    trace_buffer_hi = UINT64_HI32(p);
    trace_buffer_lo = UINT64_LO32(p);
    trace_buffer_size_hi = UINT64_HI32(size);
    trace_buffer_size_lo = UINT64_LO32(size);
#ifdef SV_TEST
    sv_map_host_memory(p);
#endif
    // configure csrs via rr_cfg_bus
    rr_cfg_poke(BUF_ADDR_HI, trace_buffer_hi);
    rr_cfg_poke(BUF_ADDR_LO, trace_buffer_lo);
    rr_cfg_poke(BUF_SIZE_HI, trace_buffer_size_hi);
    rr_cfg_poke(BUF_SIZE_LO, trace_buffer_size_lo);
    rr_cfg_poke(buf_update_csr, 1);
}

static uint8_t *rr_alloc_setup_buffer(uint64_t size, uint64_t buf_update_csr) {
    uint64_t pa;
    uint8_t *va = rr_alloc_buffer(size, &pa);
#ifdef SV_TEST
    setup_buffer(va, size, buf_update_csr);
    return va;
#else
    setup_buffer((uint8_t*)(pa), size, buf_update_csr);
    return (uint8_t *)(va);
#endif
}

static void rr_dealloc_buffer(uint8_t *buf) {
#ifdef SV_TEST
    free(buf);
#else
    fpga_hugealloc_put((void*)buf);
#endif
}

// in simulation, the unit is passed to sv_pause
// on real hardware, the unit is 1000us
static void rr_wait(uint32_t unit) {
#ifdef SV_TEST
    sv_pause(unit);
#else
    usleep(unit*1000);
#endif
}

// return the stable counter
// polling a 64-bit CSR counter until it is stable, then force it to finish,
// then wait the counter to be stable again
static uint64_t rr_wait_counter_stable(uint64_t lo_csr_idx, uint64_t hi_csr_idx) {
    uint64_t newcnt, oldcnt;
    rr_cfg_peek64(lo_csr_idx, hi_csr_idx, &newcnt);
    do {
        oldcnt = newcnt;
        rr_wait(POLLING_INTERVAL);
        rr_cfg_peek64(lo_csr_idx, hi_csr_idx, &newcnt);
    } while (newcnt != oldcnt);
    return newcnt;
}

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

static void dump_trace(const char *msg, const char *filename, uint8_t *p,
                       uint64_t size_bits) {
    int size_bytes = (size_bits + 7) / 8;
    // print trace to stdout
    printf("%s: size %ld bits (%d B)\n", msg, size_bits, size_bytes);
#ifdef DUMP_TRACE_TXT
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
#endif
    if (size_bytes) {
        // save trace to file
        int fd = open(filename, O_RDWR | O_CREAT,
                      S_IRUSR | S_IWUSR | S_IRGRP | S_IWGRP | S_IROTH);
        write(fd, &size_bits, TRACE_LEN_BYTES);
        write(fd, p, size_bytes);
        fsync(fd);
        close(fd);
    } else
        log_warning("Empty trace %s, will not save to file", filename);
}

void do_record_stop() {
    rr_wait_counter_stable(RECORD_BITS_LO, RECORD_BITS_HI);
    rr_cfg_poke(RECORD_FORCE_FINISH, 1);
    uint64_t record_bits =
        rr_wait_counter_stable(RECORD_BITS_LO, RECORD_BITS_HI);
    dump_trace("Record Buffer", "record.dump", record_buffer, record_bits);
    rr_dealloc_buffer(record_buffer);

    if (is_validate()) {
        uint64_t validate_bits =
            rr_wait_counter_stable(VALIDATE_BITS_LO, VALIDATE_BITS_HI);
        dump_trace("Validate Buffer", "validate_record.dump", validate_buffer,
                   validate_bits);
        rr_dealloc_buffer(validate_buffer);
    }
}
void do_replay_start() {
    // always set RR_MODE first to avoid silently dropping traffic
    rr_cfg_poke(RR_MODE, rr_mode.val);
    if (is_validate()) {
        validate_buffer_size = buffer_size;
        validate_buffer =
            rr_alloc_setup_buffer(validate_buffer_size, VALIDATE_BUF_UPDATE);
    }
    int fd = open("record.dump", O_RDONLY);
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
    uint64_t rt_replay_bits =
        rr_wait_counter_stable(RT_REPLAY_BITS_LO, RT_REPLAY_BITS_HI);
    if (rt_replay_bits != replay_bits) {
        log_error("runtime replay bits (%ld) != replay bits in the trace (%ld)",
                rt_replay_bits, replay_bits);
    }
    rr_dealloc_buffer(replay_buffer);

    if (is_validate()) {
        rr_wait_counter_stable(VALIDATE_BITS_LO, VALIDATE_BITS_HI);
        rr_cfg_poke(RECORD_FORCE_FINISH, 1);
        uint64_t validate_bits =
            rr_wait_counter_stable(VALIDATE_BITS_LO, VALIDATE_BITS_HI);
        dump_trace("Validate Buffer", "validate_replay.dump", validate_buffer,
                   validate_bits);
        rr_dealloc_buffer(validate_buffer);
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

/*
 * DBG related
 */
#define LOG_INFO_DBG_CSR_U32(csr_idx) \
    uint32_t csr_idx##_val; \
    rr_cfg_peek(csr_idx, &(csr_idx##_val)); \
    log_info("DBG: " #csr_idx " = %d", csr_idx##_val)
#define LOG_INFO_DBG_CSR_U64(csr_idx_pfx) \
    uint64_t csr_idx_pfx##_val; \
    rr_cfg_peek64(csr_idx_pfx##_LO, csr_idx_pfx##_HI, &(csr_idx_pfx##_val)); \
    log_info("DBG: " #csr_idx_pfx " = %ld", csr_idx_pfx##_val)
void debug_check() {
    // gefei dbg_csr
    LOG_INFO_DBG_CSR_U64(RR_WB_RECORD_DBG_BITS_NON_ALIGNED);
    LOG_INFO_DBG_CSR_U32(RR_WB_RECORD_DBG_BITS_FIFO_WR_CNT);

    LOG_INFO_DBG_CSR_U32(RR_WB_RECORD_DBG_BITS_CHPKT_CNT_pcim_R);
    LOG_INFO_DBG_CSR_U32(RR_WB_RECORD_DBG_BITS_CHPKT_CNT_sda_AW);
    LOG_INFO_DBG_CSR_U32(RR_WB_RECORD_DBG_BITS_CHPKT_CNT_bar1_W);
    LOG_INFO_DBG_CSR_U32(RR_WB_RECORD_DBG_BITS_CHPKT_CNT_ocl_AR);
    LOG_INFO_DBG_CSR_U32(RR_WB_RECORD_DBG_BITS_CHPKT_CNT_pcis_AW);
    LOG_INFO_DBG_CSR_U32(RR_WB_RECORD_DBG_BITS_CHPKT_CNT_ocl_AW);
    LOG_INFO_DBG_CSR_U32(RR_WB_RECORD_DBG_BITS_CHPKT_CNT_ocl_W);
    LOG_INFO_DBG_CSR_U32(RR_WB_RECORD_DBG_BITS_CHPKT_CNT_bar1_AW);
    LOG_INFO_DBG_CSR_U32(RR_WB_RECORD_DBG_BITS_CHPKT_CNT_pcis_W);
    LOG_INFO_DBG_CSR_U32(RR_WB_RECORD_DBG_BITS_CHPKT_CNT_pcis_B);
    LOG_INFO_DBG_CSR_U32(RR_WB_RECORD_DBG_BITS_CHPKT_CNT_pcis_AR);
    LOG_INFO_DBG_CSR_U32(RR_WB_RECORD_DBG_BITS_CHPKT_CNT_sda_AR);
    LOG_INFO_DBG_CSR_U32(RR_WB_RECORD_DBG_BITS_CHPKT_CNT_sda_W);
    LOG_INFO_DBG_CSR_U32(RR_WB_RECORD_DBG_BITS_CHPKT_CNT_bar1_AR);
}
