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

#define mod_event_in(event_in) mod (event_in, 3)
#define mod_option_set(option_set) mod (option_set, 3)
#define mod_ticks(ticks) mod (ticks, 3)
#define mod_opt_event_out(opt_event_out) mod (opt_event_out, 2)

int terminated0 = 0
int terminated = terminated0

init {
  // never expecting "timeout"
  // always expecting termination

  assert (thread_num >= 2);
  
  int step = 4;
  int step0;
  int current;
  int target;
  int event_in;
  int option_set;
  int ticks;
  int opt_event_out;
  int nr;
  
  nr = _nr_pr;

  for (step0 : 1 .. step) {
    if
     :: current++
     :: current--
     :: target++
     :: target--
     :: event_in++
     :: event_in--
     :: option_set++
     :: option_set--
     :: ticks++
     :: ticks--
     :: /* scheduler */
        thread_set_off (mod_thread1 (current), states_suspended)
     :: /* scheduler */
        thread_set_on (mod_thread1 (current), states_waiting_for_event, states_suspended)
     :: true -> event_history_surrender_send (mod_thread1 (current), mod_thread1 (target), mod_event_in (event_in))
     :: true -> event_history_seize_receive (mod_thread1 (current)/* prevent all threads executing a receive action and making them blocked without a free slot for running at least one send action */, mod_event_in (event_in), mod_option_set (option_set), mod_ticks (ticks), mod_opt_event_out (opt_event_out))
    fi
  };

  for (target : 0 .. thread_num - 2) {
    if
     :: thread_set_off (target, states_suspended)
     :: else
    fi
  };
  
  for (target : 0 .. thread_num - 2) {
    if
     :: thread_pool[target].lock_seize > 0 ->
        if
         :: thread_pool[target].wait_flags == thread_wait_state_blocked ->
            int event_in0 = thread_pool[target].event_in; // Note: spin does not support the unfolding of this definition
            current = thread_num - 1;
            event_history_surrender_send (current, target, event_in0);
            thread_pool[current].lock_surrender_current == 0
         :: thread_pool[target].lock_seize == 0 ->
            skip
        fi
     :: else
    fi
  };

  nr == _nr_pr
  terminated = ! terminated
}

ltl termination { <> ([] (terminated != terminated0)) }
