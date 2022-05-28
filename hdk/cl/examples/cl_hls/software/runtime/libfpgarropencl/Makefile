include Makefile.inc
ifeq ($(CL_FPGARR_ROOT),)
	$(error "Need to source sdk_setup.sh")
endif
include ${CL_FPGARR_ROOT}/software/runtime/libfpgarr/Makefile.inc

CC?= gcc
CFLAGS+=-I$(SDK_DIR)/userspace/include -I$(XILINX_XRT)/include -I$(LIBFPGARR_PATH) -Wall
all: libfpgarropencl.a

LIBFPGARROPENCL_OBJS=$(LIBFPGARROPENCL_SRC:.c=.o)
ARCHIVENAME=libfpgarropencl.a

$(ARCHIVENAME): $(LIBFPGARROPENCL_OBJS)
	ar -crs $@ $^
%.o: %.c $(LIBFPGARROPENCL_HEADERS)
	$(CC) -c $(CFLAGS) $< -o $@

clean:
	rm -f $(LIBFPGARROPENCL_OBJS) $(ARCHIVENAME)
