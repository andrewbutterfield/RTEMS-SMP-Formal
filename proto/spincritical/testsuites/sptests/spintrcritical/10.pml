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
 *  Copyright (c) 2013 embedded brains GmbH.
 *
 *  The license and distribution terms for this file may be
 *  found in the file LICENSE in this distribution or at
 *  http://www.rtems.org/license/LICENSE.
 */

static bool blocks_for_event(Thread_Wait_flags flags);
static bool interrupts_blocking_op(Thread_Wait_flags flags);

/**/

assert_receive(val, stat) {
  rtems_test_assert(thread->Wait.return_argument == val);
  rtems_test_assert(_Thread_Wait_get_status(thread) == stat);
}

assert_receive3 (msg1, msg2, out_res, receive_res) {
  out = DEADBEEF;
  rtems_test_assert(rtems_event_receive(EVENTS, msg1, msg2, &out) == receive_res);
  rtems_test_assert(out == out_res);
}

assert_receive2 (msg1, msg2, out_res) {
  assert_receive3 (msg1, msg2, out_res, RTEMS_SUCCESSFUL)
}

fire_after (rtems_id timer, void *arg, l_send_receive) {
  if (blocks_for_event(flags)) {
    
    l_send_receive;
    
    if (ctx->hit) {
      rtems_test_assert(_Thread_Wait_flags_get(thread) == (THREAD_WAIT_CLASS_EVENT | THREAD_WAIT_STATE_READY_AGAIN));
    }

    rtems_test_assert(thread->Wait.count == EVENTS);
  }

  rtems_test_assert(rtems_timer_reset(timer) == RTEMS_SUCCESSFUL);
}

/**/

static void any_satisfy_before_timeout(rtems_id timer, void *arg) {
  fire_after ( timer
             , arg
             , [ assert_receive(DEADBEEF, STATUS_SUCCESSFUL);

                 rtems_test_assert(rtems_event_send(thread->Object.id, GREEN) == RTEMS_SUCCESSFUL);

                 assert_receive(GREEN, STATUS_SUCCESSFUL);

                 rtems_test_assert(rtems_event_send(thread->Object.id, RED) == RTEMS_SUCCESSFUL);
                 
                 assert_receive(GREEN, STATUS_SUCCESSFUL);

                 _Thread_Timeout(&thread->Timer.Watchdog);

                 assert_receive(GREEN, STATUS_SUCCESSFUL);])
}

static bool test_body_any_satisfy_before_timeout(void *arg) {
  assert_receive2 (RTEMS_EVENT_ANY | RTEMS_WAIT, 1, GREEN);
  assert_receive2 (RTEMS_EVENT_ANY | RTEMS_NO_WAIT, 0, RED);
}

static void test_any_satisfy_before_timeout(test_context *ctx) {
  rtems_test_assert (rtems_timer_fire_after (any_satisfy_before_timeout ()));
  interrupt_critical_section_test (test_body_any_satisfy_before_timeout, ctx, NULL);
}

/**/

static void all_satisfy_before_timeout(rtems_id timer, void *arg) {
  fire_after ( timer
             , arg
             , [ assert_receive(DEADBEEF, STATUS_SUCCESSFUL);

                 rtems_test_assert(rtems_event_send(thread->Object.id, GREEN) == RTEMS_SUCCESSFUL);

                 assert_receive(DEADBEEF, STATUS_SUCCESSFUL);

                 rtems_test_assert(rtems_event_send(thread->Object.id, RED) == RTEMS_SUCCESSFUL);

                 assert_receive(EVENTS, STATUS_SUCCESSFUL);

                 _Thread_Timeout(&thread->Timer.Watchdog);

                 assert_receive(EVENTS, STATUS_SUCCESSFUL); ])
}

static bool test_body_all_satisfy_before_timeout(void *arg) {
  assert_receive2 (RTEMS_EVENT_ALL | RTEMS_WAIT, 1, EVENTS)
}

static void test_all_satisfy_before_timeout(test_context *ctx) {
  rtems_test_assert (rtems_timer_fire_after (all_satisfy_before_timeout ()));
  interrupt_critical_section_test (test_body_all_satisfy_before_timeout, ctx, NULL);
}

/**/

static void timeout_before_satisfied(rtems_id timer, void *arg) {
  fire_after ( timer
             , arg
             , [ assert_receive(DEADBEEF, STATUS_SUCCESSFUL);

                 _Thread_Timeout(&thread->Timer.Watchdog);

                 assert_receive(DEADBEEF, STATUS_TIMEOUT);

                 rtems_test_assert(rtems_event_send(thread->Object.id, EVENTS) == RTEMS_SUCCESSFUL);

                 assert_receive(DEADBEEF, STATUS_TIMEOUT); ])
}

static bool test_body_timeout_before_all_satisfy(void *arg) {
  assert_receive3 (RTEMS_EVENT_ALL | RTEMS_WAIT, 1, DEADBEEF, RTEMS_TIMEOUT)
  assert_receive2 (RTEMS_EVENT_ALL | RTEMS_NO_WAIT, 0, EVENTS)
}

static void test_timeout_before_all_satisfy(test_context *ctx) {
  rtems_test_assert (rtems_timer_fire_after (timeout_before_satisfied ()));
  interrupt_critical_section_test (test_body_timeout_before_all_satisfy, ctx, NULL);
}

/**/

static rtems_task Init() {
  test_any_satisfy_before_timeout ();
  test_all_satisfy_before_timeout ();
  test_timeout_before_all_satisfy ();
}
