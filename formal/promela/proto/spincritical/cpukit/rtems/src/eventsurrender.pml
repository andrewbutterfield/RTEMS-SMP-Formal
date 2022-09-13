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
 *  COPYRIGHT (c) 1989-2008.
 *  On-Line Applications Research Corporation (OAR).
 *
 *  The license and distribution terms for this file may be
 *  found in the file LICENSE in this distribution or at
 *  http://www.rtems.org/license/LICENSE.
 */

static void _Event_Satisfy(
  Thread_Control  *the_thread,
  Event_Control   *event,
  rtems_event_set  pending_events,
  rtems_event_set  seized_events
)
{
  event->pending_events = _Event_sets_Clear( pending_events, seized_events );
  *(rtems_event_set *) the_thread->Wait.return_argument = seized_events;
}

static bool _Event_Is_blocking_on_event(
  const Thread_Control *the_thread,
  Thread_Wait_flags     wait_class
)
{
  return (/*Thread_Wait_flags*/ /*wait_flags*/_Thread_Wait_flags_get( the_thread )
          & ( /*wait_mask*/THREAD_WAIT_CLASS_MASK | THREAD_WAIT_STATE_READY_AGAIN) )
         == wait_class;
}

static bool _Event_Is_satisfied0(
  rtems_event_set       pending_events,
  rtems_event_set      *seized_events,
  rtems_option    option_set,
  rtems_event_set event_condition
)
{
  *seized_events = _Event_sets_Get( pending_events, event_condition );

  return !_Event_sets_Is_empty( *seized_events )
    && ( *seized_events == event_condition || _Options_Is_any( option_set ) );
}

static bool _Event_Is_satisfied(
  const Thread_Control *the_thread,
  rtems_event_set       pending_events,
  rtems_event_set      *seized_events
)
{
  return _Event_Is_satisfied0( pending_events,
                               seized_events,
                               the_thread->Wait.option,
                               the_thread->Wait.count )
}

rtems_status_code _Event_Surrender(
  Thread_Control    *the_thread /*specific other thread*/,
  rtems_event_set    event_in,
  Event_Control     *event /*specific other thread*/,
  Thread_Wait_flags  wait_class /*THREAD_WAIT_CLASS_EVENT or THREAD_WAIT_CLASS_SYSTEM_EVENT*/,
  ISR_lock_Context  *lock_context /*specific other thread*/
)
{
  _Thread_Wait_acquire_default_critical( the_thread, lock_context );

  _Event_sets_Post( event_in, &event->pending_events );
  pending_events = event->pending_events;

  if (
      _Event_Is_blocking_on_event( the_thread, wait_class ) // mostly ensures that the_thread is not in the state THREAD_WAIT_STATE_READY_AGAIN (besides checking that the_thread is in the class wait_class)
      && _Event_Is_satisfied( the_thread, pending_events, &seized_events )
  ) {
    _Event_Satisfy( the_thread, event, pending_events, seized_events );

    ready_again = wait_class | THREAD_WAIT_STATE_READY_AGAIN;

    if ( /*success*/
        _Thread_Wait_flags_try_change_release(
                                              the_thread,
                                              wait_class | THREAD_WAIT_STATE_INTEND_TO_BLOCK,
                                              ready_again
                                              ))
    {
      block = true;
    } else {
      _Assert(
        _Thread_Wait_flags_get( the_thread )
          == ( wait_class | THREAD_WAIT_STATE_BLOCKED )
      );
      /**/_Thread_Wait_flags_set( the_thread, ready_again );
      
      Per_CPU_Control *cpu_self;

      /**/cpu_self = _Thread_Dispatch_disable_critical( lock_context );
      /**/_Thread_Wait_release_default( the_thread, lock_context );

      /**/_Thread_Timer_remove( the_thread );
      /**/_Thread_Unblock( the_thread );

      /**/_Thread_Dispatch_enable( cpu_self );
      block = false;
    }
  } else {
    block = true;
  }

  if ( block ) {
    _Thread_Wait_release_default( the_thread, lock_context );
  }

  return RTEMS_SUCCESSFUL;
}
