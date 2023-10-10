/*
 * Copyright 2021, Breakaway Consulting Pty. Ltd.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#define __thread
#include <sel4/sel4.h>

#include <sel4cp.h>

#define INPUT_CAP 1

#define NOTIFICATION_BITS 57

char _stack[4096]  __attribute__((__aligned__(16)));

char sel4cp_name[16];

extern seL4_IPCBuffer __sel4_ipc_buffer_obj;

seL4_IPCBuffer *__sel4_ipc_buffer = &__sel4_ipc_buffer_obj;

extern const void (**const __init_array_start) (void);
extern const void (**const __init_array_end) (void);

__attribute__((weak)) sel4cp_msginfo protected(sel4cp_channel ch, sel4cp_msginfo msginfo)
{
    return seL4_MessageInfo_new(0, 0, 0, 0);
}

static void
run_init_funcs(void)
{
    size_t count = __init_array_end - __init_array_start;
    for (size_t i = 0; i < count; i++) {
        __init_array_start[i]();
    }
}

seL4_Word badge;

static void
handler_loop(void)
{
    bool have_reply = false;
    seL4_MessageInfo_t reply_tag;

    for (;;) {
        // inv: have_reply --> prev(is_endpoint)
        // inv: have_reply <--> ghost_reply_tag != Nothing
        seL4_MessageInfo_t tag;

        if (have_reply) {
            tag = seL4_ReplyRecv(INPUT_CAP, reply_tag, &badge);
        } else {
            tag = seL4_Recv(INPUT_CAP, &badge);
        }
        seL4_Word lbadge = badge;

        uint64_t is_endpoint = lbadge >> 63;

        if (is_endpoint) {
            have_reply = true;
            reply_tag = protected(lbadge & 0x3f, tag);
        } else {
            unsigned int idx = 0;
            have_reply = false;
            do  {
                if (lbadge & 1) {
                    notified(idx);
                }
                lbadge >>= 1;
                idx++;
            } while (lbadge != 0);
        }
    }
}

void
main(void)
{
    run_init_funcs();
    init();
    handler_loop();
}
