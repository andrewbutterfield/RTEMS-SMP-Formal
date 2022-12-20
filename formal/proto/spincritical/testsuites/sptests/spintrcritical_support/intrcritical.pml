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
 *  COPYRIGHT (c) 1989-2009.
 *  On-Line Applications Research Corporation (OAR).
 *
 *  The license and distribution terms for this file may be
 *  found in the file LICENSE in this distribution or at
 *  http://www.rtems.org/license/LICENSE.
 */

#define INTERRUPT_CRITICAL_NAME rtems_build_name( 'I', 'C', 'R', 'I' )

typedef struct {
  uint_fast32_t minimum;
  uint_fast32_t maximum;
  uint_fast32_t maximum_current;
  rtems_timer_service_routine_entry tsr;
  rtems_id timer;
  uint64_t t0;
  uint64_t t1;
} interrupt_critical_control;

static interrupt_critical_control interrupt_critical;

static void wait_for_tick_change( void )
{
  rtems_interval initial = rtems_clock_get_ticks_since_boot();
  rtems_interval now;

  do {
    now = rtems_clock_get_ticks_since_boot();
  } while ( now == initial );
}

static void timer_fire_after(void)
{
  if ( interrupt_critical.tsr != NULL ) {
    rtems_status_code sc = rtems_timer_fire_after(
      interrupt_critical.timer,
      1,
      interrupt_critical.tsr,
      NULL
    );
    rtems_test_assert( sc == RTEMS_SUCCESSFUL );
  }
}

static const rtems_extensions_table extensions = {
  .thread_switch =
    % ( Thread_Control *executing, Thread_Control *heir )
    {
      (void) executing;
      (void) heir;

      if ( interrupt_critical.t1 == 0 && heir->is_idle ) {
        interrupt_critical.t1 = rtems_clock_get_uptime_nanoseconds();
      }
    }
};

bool interrupt_critical_section_test(
  bool                              ( *test_body )( void * ),
  void                                *test_body_arg,
  rtems_timer_service_routine_entry    tsr
)
{
  bool done;
  rtems_status_code sc;
  rtems_id id;
  uint64_t delta;
  uint_fast32_t busy_delta;
  int retries = 3;

  /**/ // interrupt_critical_section_test_support_initialize
  uint_fast32_t m;

  interrupt_critical.tsr = tsr;

  if ( tsr != NULL && interrupt_critical.timer == 0 ) {
    rtems_status_code sc = rtems_timer_create(
      INTERRUPT_CRITICAL_NAME,
      &interrupt_critical.timer
    );
    rtems_test_assert( sc == RTEMS_SUCCESSFUL );
  }

  m = rtems_test_get_one_tick_busy_count();

  interrupt_critical.minimum = 0;
  interrupt_critical.maximum = m;
  interrupt_critical.maximum_current = m;
  /**/

  sc = rtems_extension_create(
    INTERRUPT_CRITICAL_NAME,
    &extensions,
    &id
  );
  rtems_test_assert( sc == RTEMS_SUCCESSFUL );

  wait_for_tick_change();
  timer_fire_after();

  /* Get estimate for test body duration */
  interrupt_critical.t0 = rtems_clock_get_uptime_nanoseconds();
  done = ( *test_body )( test_body_arg );
  if ( interrupt_critical.t1 == 0 ) {
    interrupt_critical.t1 = rtems_clock_get_uptime_nanoseconds();
  }

  /* Update minimum */

  delta = interrupt_critical.t1 - interrupt_critical.t0;
  busy_delta = (uint_fast32_t)
    ( ( interrupt_critical.maximum * ( 2 * delta ) )
      / rtems_configuration_get_nanoseconds_per_tick() );

  if ( busy_delta < interrupt_critical.maximum ) {
    interrupt_critical.minimum = interrupt_critical.maximum - busy_delta;
  }

  sc = rtems_extension_delete( id );
  rtems_test_assert( sc == RTEMS_SUCCESSFUL );

  while ( !done && retries >= 0 ) {
    wait_for_tick_change();

    /**/ // interrupt_critical_section_test_support_delay
    timer_fire_after();

    uint_fast32_t max = interrupt_critical.maximum_current;
    bool reset = max <= interrupt_critical.minimum;

    if ( reset ) {
      interrupt_critical.maximum_current = interrupt_critical.maximum;
    } else {
      interrupt_critical.maximum_current = max - 1;
    }

    rtems_test_busy( max );
    /**/
    
    if ( reset ) {
      --retries;
    }

    done = ( *test_body )( test_body_arg );
  }

  return done;
}
