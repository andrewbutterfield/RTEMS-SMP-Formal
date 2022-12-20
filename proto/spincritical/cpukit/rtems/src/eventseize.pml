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

rtems_status_code _Event_Seize(
  rtems_event_set    event_in,
  rtems_option       option_set,
  rtems_interval     ticks,
  rtems_event_set   *event_out /*own thread*/,
  Thread_Control    *executing /*own thread*/,
  Event_Control     *event /*own thread*/,
  Thread_Wait_flags  wait_class /*THREAD_WAIT_CLASS_EVENT or THREAD_WAIT_CLASS_SYSTEM_EVENT*/,
  States_Control     block_state /*STATES_WAITING_FOR_EVENT or STATES_WAITING_FOR_SYSTEM_EVENT*/,
  ISR_lock_Context  *lock_context /*own thread*/
)
{
  pending_events = event->pending_events;

  if ( _Event_Is_satisfied0( pending_events, & seized_events, option_set, event_in ) ) {
    event->pending_events =
      _Event_sets_Clear( pending_events, seized_events );
    _Thread_Wait_release_default( executing, lock_context );
    *event_out = seized_events;
    return RTEMS_SUCCESSFUL;
  }

  if ( _Options_Is_no_wait( option_set ) ) {
    _Thread_Wait_release_default( executing, lock_context );
    *event_out = seized_events;
    return RTEMS_UNSATISFIED;
  }

  intend_to_block = wait_class | THREAD_WAIT_STATE_INTEND_TO_BLOCK;

  /*
   *  Note what we are waiting for BEFORE we enter the critical section.
   *  The interrupt critical section management code needs this to be
   *  set properly when we are marked as in the event critical section.
   *
   *  NOTE: Since interrupts are disabled, this isn't that much of an
   *        issue but better safe than sorry.
   */
  executing->Wait.return_code     = STATUS_SUCCESSFUL;
  executing->Wait.option          = option_set;
  executing->Wait.count           = event_in;
  executing->Wait.return_argument = event_out;
  /**/_Thread_Wait_flags_set( executing, intend_to_block );

  /**/cpu_self = _Thread_Dispatch_disable_critical( lock_context );
  /**/_Thread_Wait_release_default( executing, lock_context );

  if ( ticks ) {
    _Thread_Add_timeout_ticks( executing, cpu_self, ticks );
  }

  _Thread_Set_state( executing, block_state );

  if ( !
       /*success*/
       _Thread_Wait_flags_try_change_acquire(
                                             executing,
                                             intend_to_block,
                                             wait_class | THREAD_WAIT_STATE_BLOCKED
                                             ) )
  {
    /**/_Thread_Timer_remove( executing );
    /**/_Thread_Unblock( executing );
  }

  /**/_Thread_Dispatch_direct( cpu_self );
  return _Status_Get_after_wait( executing );
}



#if defined(RTEMS_MULTIPROCESSING)
static void _Event_MP_Initialize( void )
{
  _MPCI_Register_packet_processor( MP_PACKET_EVENT, _Event_MP_Process_packet );
}

RTEMS_SYSINIT_ITEM(
  _Event_MP_Initialize,
  RTEMS_SYSINIT_CLASSIC_EVENT_MP,
  RTEMS_SYSINIT_ORDER_MIDDLE
);
#endif
