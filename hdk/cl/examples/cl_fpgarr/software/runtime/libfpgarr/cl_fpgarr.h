#ifndef CL_FPGARR_H
#define CL_FPGARR_H
#include <stdint.h>

extern int init_rr(int slot_id);
extern void do_pre_rr();
extern void do_post_rr();

extern uint8_t is_record();
extern uint8_t is_replay();
extern uint8_t is_validate();

#endif // CL_FPGARR_H
