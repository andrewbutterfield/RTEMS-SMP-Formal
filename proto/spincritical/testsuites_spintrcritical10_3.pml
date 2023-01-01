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

/*@ section \<open>\<close> */

#include "testsuites_spintrcritical10_begin.pml"

proctype send /* timeout_before_satisfied */ () {
  do
   :: wait_for_receive_blocked_then_suspend_on (target) ->

      thread_pool[target].event_out_surrender = deadbeef;

      suspend_off (target); // let the timeout the opportunity to happen on the target thread

      if
       :: wait_for_receive_timeout_then_suspend_on (target) ->
      
          event_atomic_surrender_send (current, target, events);
          assert (surrender_send_status == rtems_successful);
          assert (thread_pool[target].event_out_surrender == deadbeef);

          suspend_off (target)
       :: send_break ->
          // In case the timeout of the target thread happen, but also in case the execution of this proctype does not resume immediately after, then the content of thread_pool[target].event_out_surrender might have been changed (to potentially make the assertion fail). This is why we do not perform an explicit checking here.
          break
      fi
   :: send_break ->
      break
  od
}

proctype receive /* test_body_timeout_before_all_satisfy */ () {
  do
   :: wait_for_send_hit_or_no_retry ()
   :: else ->
      
      event_atomic_seize_receive (target, events, rtems_event_all | rtems_wait, 1, deadbeef);
      assert (seize_receive_status == rtems_timeout && seize_receive_event_out == deadbeef ||
              seize_receive_status == rtems_successful && seize_receive_event_out == events);
      
      event_atomic_seize_receive (target, events, rtems_event_all | rtems_no_wait, 0, deadbeef);
      assert (seize_receive_status == rtems_unsatisfied && seize_receive_event_out == 0 ||
              seize_receive_status == rtems_successful && seize_receive_event_out == events);
      
      retries --
  od
}

#include "testsuites_validation_end.pml"
