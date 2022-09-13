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

#include "cpukit.pml"

chan history_send = [0] of { int /* unique identifier */, int /* status code */ }
chan history_receive = [0] of { int /* unique identifier */, int /* status code */, int /* presence of the next optional argument */, int /* optional argument content: event_out */ }

int hit = 0
int send_break = 0
int surrender_send_status
int seize_receive_status
int seize_receive_event_out

inline event_atomic_surrender_send (current /**/,/**/ target, event_in) {
  event_surrender_send (history_send, 0, current, target, event_in);
  history_send ? _, surrender_send_status
}

inline event_atomic_seize_receive (current /**/,/**/ event_in, option_set, ticks, opt_event_out) {
  event_seize_receive (history_receive, 0, current, event_in, option_set, ticks, opt_event_out);
  history_receive ? _, seize_receive_status, _, seize_receive_event_out
}

int current = 1
int target = 0

int retries = 2

inline suspend_on (target) {
  thread_pool[target].state = thread_pool[target].state | states_suspended
}

inline suspend_off (target) {
  thread_pool[target].state = thread_pool[target].state & ~ states_suspended
}

inline wait_for_receive_blocked_then_suspend_on (target) {
  atomic {
    thread_pool[target].wait_flags == thread_wait_state_intend_to_block ||
      thread_pool[target].wait_flags == thread_wait_state_blocked ->
    hit = thread_pool[target].wait_flags == thread_wait_state_blocked;
    suspend_on (target) // We manually suspend the target thread to simulate the fact that its timer is still not yet elapsed, while the necessary time is taken to execute the next instructions. The thread must remain blocked because otherwise some next assertions on thread_pool[target].event_out_surrender might fail.
  }
}

inline wait_for_receive_timeout_then_suspend_on (target) {
  atomic {
    seize_receive_status == rtems_timeout -> // wait until the execution of the target thread terminates with 'timeout' as result
    suspend_on (target) // prevent meanwhile a potential next execution of another event_atomic_seize_receive
  }
}

inline wait_for_send_hit_or_no_retry () {
  hit >= 1 || retries <= 0 ->
  send_break = 1;
  break
}

#define deadbeef 3735928559
