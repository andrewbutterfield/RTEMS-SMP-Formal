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
 *  Classic API Signal to Task from ISR
 *
 *  COPYRIGHT (c) 1989-2011.
 *  On-Line Applications Research Corporation (OAR).
 *
 *  The license and distribution terms for this file may be
 *  found in the file LICENSE in this distribution or at
 *  http://www.rtems.org/license/LICENSE.
 */

static volatile bool case_hit;
static rtems_id main_task;
static Thread_Control *main_thread;
static rtems_id other_task;

static bool is_case_hit( void );

/**/

test_event0 (val) {
    fatal_directive_check_status_only( rtems_event_send( other_task, val ), RTEMS_SUCCESSFUL );
}

/**/

static rtems_timer_service_routine test_event_from_isr(rtems_id timer, void *arg) {
  if ( is_case_hit () ) {
    /*
     *  This event send hits the critical section but sends to
     *  another task so doesn't impact this critical section.
     */
    test_event0 (0x02);

    /*
     *  This event send hits the main task but doesn't satisfy
     *  it's blocking condition so it will still block
     */
    test_event0 (0x02);

    case_hit = true;
  }
  test_event0 (0x01);
}

static bool test_body_event_from_isr( void *arg ) {
  rtems_test_assert( rtems_event_receive (0x01, RTEMS_DEFAULT_OPTIONS, 0, &out) == RTEMS_SUCCESSFUL );
}

/**/

static rtems_timer_service_routine test_event_with_timeout_from_isr(rtems_id timer, void *arg) {
  if ( is_case_hit() ) {
    case_hit = true;
  }
  fatal_directive_check_status_only ( rtems_event_send (main_task, 0x01), RTEMS_SUCCESSFUL);
}

static bool test_body_event_with_timeout_from_isr( void *arg ) {
  status = rtems_event_receive (0x01, RTEMS_DEFAULT_OPTIONS, 1, &out);
  rtems_test_assert ( status == RTEMS_SUCCESSFUL || status == RTEMS_TIMEOUT );
}

/**/

interrupt_critical0 (f1, f2) {
  case_hit = false;
  interrupt_critical_section_test ( f1, NULL, f2 );
  rtems_test_assert ( case_hit );
}

rtems_task Init(rtems_task_argument argument) {
  main_task = rtems_task_self();
  
  directive_failed ( rtems_task_create () );

  /**/
  
  interrupt_critical0 ( test_body_event_from_isr, test_event_from_isr );

  /**/

  interrupt_critical0 ( test_body_event_with_timeout_from_isr, test_event_with_timeout_from_isr );
}
