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
 * Copyright (c) 2014 embedded brains GmbH.  All rights reserved.
 *
 *  embedded brains GmbH
 *  Dornierstr. 4
 *  82178 Puchheim
 *  Germany
 *  <rtems@embedded-brains.de>
 *
 * The license and distribution terms for this file may be
 * found in the file LICENSE in this distribution or at
 * http://www.rtems.org/license/LICENSE.
 */

static Semaphore_Control *get_semaphore_control(rtems_id id);

static void release_semaphore(rtems_id timer, void *arg) {
  if ( _Thread_Wait_flags_get () == (THREAD_WAIT_CLASS_OBJECT | THREAD_WAIT_STATE_INTEND_TO_BLOCK) ) {
    rtems_test_assert ( rtems_semaphore_release () == RTEMS_SUCCESSFUL );
    rtems_test_assert ( _Thread_Wait_flags_get () == (THREAD_WAIT_CLASS_OBJECT | THREAD_WAIT_STATE_READY_AGAIN) );
    rtems_test_assert ( (&ctx->semaphore_control->Core_control.Semaphore)->count == 0 );
  } else {
    rtems_test_assert ( rtems_semaphore_release () == RTEMS_SUCCESSFUL );
  }
}

static bool test_body(void *arg) {
  sc = rtems_semaphore_obtain ( RTEMS_NO_WAIT );
  rtems_test_assert(sc == RTEMS_SUCCESSFUL || sc == RTEMS_UNSATISFIED);

  sc = rtems_semaphore_obtain ( RTEMS_WAIT );
  rtems_test_assert(sc == RTEMS_SUCCESSFUL || sc == RTEMS_TIMEOUT);
}

static void Init(rtems_task_argument ignored) {
  rtems_test_assert (rtems_semaphore_create () == RTEMS_SUCCESSFUL);
  interrupt_critical_section_test(test_body, ctx, release_semaphore);
}
