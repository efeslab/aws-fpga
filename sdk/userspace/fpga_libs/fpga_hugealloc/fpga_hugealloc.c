#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/mman.h>
#include <linux/mman.h>
#include <utils/lcd.h>
#include <assert.h>

#include "fpga_hugealloc_internal.h"

static int fpga_hugealloc_get_num_1g(void) {
    int ret, npages;

    FILE *fp = fopen(HUGE_PAGE_1G_AVAIL_PATH, "r");
    fail_on(!fp, err_open, "Error opening %s", HUGE_PAGE_1G_AVAIL_PATH);

    ret = fscanf(fp, "%d", &npages);
    fail_on(ret < 0, err_close, "Error parsing %s", HUGE_PAGE_1G_AVAIL_PATH);

    printf("[hugealloc] total 1g pages: %d\n", npages);
    return npages;

err_close:
    fclose(fp);
    return -EINVAL;
err_open:
    return -errno;
}

int fpga_hugealloc_get_all_pages(struct fpga_hugepage_desc **descs) {
    uint64_t npages = fpga_hugealloc_get_num_1g();

    void *ptr = NULL;
    ptr = mmap(NULL, npages * SIZE_1G, PROT_READ|PROT_WRITE,
            MAP_PRIVATE|MAP_ANONYMOUS|MAP_HUGETLB|MAP_HUGE_1GB|MAP_POPULATE, -1, 0);

    fail_on(ptr == MAP_FAILED, err_free, "Error mapping huge pages");

    *descs = malloc(npages * sizeof(struct fpga_hugepage_desc));

    uint64_t vfn;
    int ret;
    struct pagemap_entry pe;
    int fd = open(PAGEMAP_PATH, O_RDONLY);
    off_t actual_off;
    for (uint64_t i = 0; i < npages; i++) {
        vfn = ((uint64_t)ptr + i * SIZE_1G) >> PAGE_SHIFT;
        actual_off = lseek(fd, vfn * 8, SEEK_SET);
        fail_on((uint64_t)actual_off != vfn * 8, err_procfs, "lseek failed");

        ret = read(fd, &pe, sizeof(pe));
        fail_on(ret != sizeof(pe), err_procfs, "Error reading pagemap");


        printf("[hugealloc] pe: %016lx\n", *((uint64_t*)&pe));

        struct fpga_hugepage_desc *desc = (*descs) + i;
        desc->va = (void*) (vfn << PAGE_SHIFT);
        desc->pa = pe.pfn << PAGE_SHIFT;

        printf("[hugealloc] %p --> %p\n", desc->va, (void*)desc->pa);
    }
    close(fd);

    return npages;
err_procfs:
    close(fd);
err_free:
    free(*descs);
    *descs = NULL;
    return -errno;
}

int fpga_hugealloc_get(void **va, uint64_t *pa, uint64_t *sizeB) {
    void *ptr = mmap(NULL, HUGE_SIZE, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_POPULATE | MMAP_HUGE_FLAGS, -1, 0);
    fail_on(ptr == MAP_FAILED, err, "Error mapping one huge page");

    uint64_t vfn;
    int ret;
    struct pagemap_entry pe;
    int fd = open(PAGEMAP_PATH, O_RDONLY);
    off_t actual_off;
    vfn = ((uint64_t)ptr) >> PAGE_SHIFT;
    actual_off = lseek(fd, vfn * 8, SEEK_SET);
    fail_on((uint64_t)actual_off != vfn * 8, err_procfs, "lseek failed");

    ret = read(fd, &pe, sizeof(pe));
    fail_on(ret != sizeof(pe), err_procfs, "Error reading pagemap");

    printf("[hugealloc] pe: %016lx\n", *((uint64_t*)&pe));

    assert((uint64_t)ptr == vfn << PAGE_SHIFT);
    *va = ptr;
    *pa = pe.pfn << PAGE_SHIFT;
    *sizeB = HUGE_SIZE;

    printf("[hugealloc] %p --> %p\n", *va, (void*)(*pa));

    close(fd);
    return 0;
err_procfs:
    close(fd);
err:
    return -errno;
}

int fpga_hugealloc_put(void *va) {
    return munmap(va, HUGE_SIZE);
}
