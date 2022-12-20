/******************************************************************************
 * FV2-201
 *
 * Copyright (C) 2019-2021 Trinity College Dublin (www.tcd.ie)
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************/

/*
 *  COPYRIGHT (c) 1989-2012.
 *  On-Line Applications Research Corporation (OAR).
 *
 *  Copyright (c) 2013, 2020 embedded brains GmbH.
 *
 *  The license and distribution terms for this file may be
 *  found in the file LICENSE in this distribution or at
 *  http://www.rtems.org/license/LICENSE.
 */

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include <tmacros.h>
#include <rtems/test.h>

#include <rtems/score/threadimpl.h>
#include <rtems/rtems/eventimpl.h>

const char rtems_test_name[] = "SPINTRCRITICAL 10";

#define MAX_ITERATION_COUNT 10000

#define GREEN RTEMS_EVENT_0

#define RED RTEMS_EVENT_1

#define EVENTS (GREEN | RED)

#define DEADBEEF 0xdeadbeef

typedef struct {
  Thread_Control *thread;
} test_context;

static bool blocks_for_event(Thread_Wait_flags flags)
{
  return flags == (THREAD_WAIT_CLASS_EVENT | THREAD_WAIT_STATE_INTEND_TO_BLOCK)
    || flags == (THREAD_WAIT_CLASS_EVENT | THREAD_WAIT_STATE_BLOCKED);
}

static bool interrupts_blocking_op(Thread_Wait_flags flags)
{
  return
    flags == (THREAD_WAIT_CLASS_EVENT | THREAD_WAIT_STATE_INTEND_TO_BLOCK);
}

//@ promela_term \<open>receive\<close>

static void test_receive(void *arg)
{
  rtems_status_code sc;
  rtems_event_set out;

  out = DEADBEEF;
  sc = rtems_event_receive(EVENTS, RTEMS_EVENT_ALL | RTEMS_WAIT, 1, &out);
  T_eq_u32(sc, RTEMS_SUCCESSFUL);
  T_eq_u32(out, EVENTS);
}

//@ promela_term \<open>send\<close>

static T_interrupt_test_state test_send(void *arg)
{
  rtems_status_code sc;
  test_context *ctx = arg;
  Thread_Control *thread = ctx->thread;
  Thread_Wait_flags flags = _Thread_Wait_flags_get(thread);
  T_interrupt_test_state state;

  if (blocks_for_event(flags)) {
    if (interrupts_blocking_op(flags)) {
      state = T_INTERRUPT_TEST_DONE;
    } else {
      state = T_INTERRUPT_TEST_LATE;
    }

    T_eq_u32(*(rtems_event_set *) thread->Wait.return_argument, DEADBEEF);
    T_eq_u32(_Thread_Wait_get_status(thread), STATUS_SUCCESSFUL);

    sc = rtems_event_send(thread->Object.id, GREEN);
    T_eq_u32(sc, RTEMS_SUCCESSFUL);

    T_eq_u32(*(rtems_event_set *) thread->Wait.return_argument, DEADBEEF);
    T_eq_u32(_Thread_Wait_get_status(thread), STATUS_SUCCESSFUL);

    sc = rtems_event_send(thread->Object.id, RED);
    T_eq_u32(sc, RTEMS_SUCCESSFUL);

    T_eq_u32(*(rtems_event_set *) thread->Wait.return_argument, EVENTS);
    T_eq_u32(_Thread_Wait_get_status(thread), STATUS_SUCCESSFUL);

    _Thread_Timeout(&thread->Timer.Watchdog);

    T_eq_u32(*(rtems_event_set *) thread->Wait.return_argument, EVENTS);
    T_eq_u32(_Thread_Wait_get_status(thread), STATUS_SUCCESSFUL);

    if (state == T_INTERRUPT_TEST_DONE) {
      T_eq_u32(_Thread_Wait_flags_get(thread), THREAD_WAIT_CLASS_EVENT | THREAD_WAIT_STATE_READY_AGAIN);
    }

    T_eq_u32(thread->Wait.count, EVENTS);
  } else {
    state = T_INTERRUPT_TEST_EARLY;
  }

  return state;
}

/******************************************************************************
 * FV2-201
 *
 * Copyright (C) 2019-2021 Trinity College Dublin (www.tcd.ie)
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************/

/*
 *  COPYRIGHT (c) 1989-2012.
 *  On-Line Applications Research Corporation (OAR).
 *
 *  Copyright (c) 2013, 2020 embedded brains GmbH.
 *
 *  The license and distribution terms for this file may be
 *  found in the file LICENSE in this distribution or at
 *  http://www.rtems.org/license/LICENSE.
 */

static const T_interrupt_test_config test_send_receive_config = {
  .action = test_receive,
  .interrupt = test_send,
  .max_iteration_count = MAX_ITERATION_COUNT
};

T_TEST_CASE(Event)
{
  test_context ctx;
  T_interrupt_test_state state;

  ctx.thread = _Thread_Get_executing();
  state = T_interrupt_test(&test_send_receive_config, &ctx);
  T_eq_int(state, T_INTERRUPT_TEST_DONE);
}

static rtems_task Init( rtems_task_argument argument )
{
  rtems_test_run( argument, TEST_STATE );
}

/* configuration information */

#define CONFIGURE_APPLICATION_NEEDS_SIMPLE_CONSOLE_DRIVER
#define CONFIGURE_APPLICATION_NEEDS_CLOCK_DRIVER

#define CONFIGURE_MAXIMUM_TASKS       1
#define CONFIGURE_INITIAL_EXTENSIONS RTEMS_TEST_INITIAL_EXTENSION

#define CONFIGURE_RTEMS_INIT_TASKS_TABLE
#define CONFIGURE_MICROSECONDS_PER_TICK  1000

#define CONFIGURE_INIT
#include <rtems/confdefs.h>

