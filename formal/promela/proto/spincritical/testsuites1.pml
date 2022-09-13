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

proctype scheduler (int step) {
  int current;
  do
   :: step <= 0 -> break
   :: step > 0 ->
      step--;
      if
       :: current++
       :: current--
       :: thread_set_on (mod_thread (current), states_waiting_for_event, states_suspended)
       :: thread_set_off (mod_thread (current), states_suspended)
      fi
  od
}

init {
  assert (thread_num >= 1);

  run scheduler (10);

  int step = 5;
  int current;
  int target;
  int event_in;
  int option_set;
  int ticks;
  do
   :: step <= 0 -> break
   :: step > 0 ->
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
       :: step--;
          event_history_surrender_send (mod_thread (current), mod_thread (target), event_in)
       :: step--;
          event_history_seize_receive (mod_thread (current), event_in, option_set, ticks, true)
      fi
  od
}
