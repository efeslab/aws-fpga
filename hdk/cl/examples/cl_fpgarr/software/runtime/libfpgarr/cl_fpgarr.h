#ifndef CL_FPGARR_H
#define CL_FPGARR_H
#include <stdint.h>

extern int init_rr(int slot_id);
extern void do_pre_rr();
extern void do_post_rr();
// wait indefinitely until the interrupt appears
// Then clear that interrupt and return
extern void rr_wait_irq(uint32_t irq_id);

extern uint8_t is_record();
extern uint8_t is_replay();
extern uint8_t is_validate();

extern void rr_user_timer_begin();
extern void rr_user_timer_end();

#endif // CL_FPGARR_H
