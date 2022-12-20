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
 * Copyright (c) 2012, 2016 embedded brains GmbH.  All rights reserved.
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

/*
 *  COPYRIGHT (c) 1989-2008.
 *  On-Line Applications Research Corporation (OAR).
 *
 *  The license and distribution terms for this file may be
 *  found in the file LICENSE in this distribution or at
 *  http://www.rtems.org/license/LICENSE.
 */

/*@ section \<open>\<close> */

/*@ subsection \<open>...\<close> */

#define thread_num 3

#define mod(a, b) (a % (b) + (b)) % (b)
#define mod_thread(current) mod (current, thread_num)
#define mod_thread1(current) mod (current, thread_num - 1)

#define global_history_size 100 /* arbitrary number, but sufficiently high for tests */

chan global_history_surrender = [global_history_size] of { int /* unique identifier */, int /* status code */ }
int global_history_surrender_id = 0 /* unique identifier counter */

chan global_history_seize = [global_history_size] of { int /* unique identifier */, int /* status code */, int /* presence of the next optional argument */, int /* optional argument content: event_out */ } /* TODO: Consider a superset of Promela enriched with "option types" */
int global_history_seize_id = 0 /* unique identifier counter */

/*@ subsection \<open>cpukit/include/rtems/score/threadimpl.h\<close> */

#define thread_wait_state_ready_again0 4

int thread_wait_state_intend_to_block = 1
int thread_wait_state_blocked = 2
int thread_wait_state_ready_again = thread_wait_state_ready_again0

/*@ subsection \<open>cpukit/include/rtems/score/statesimpl.h\<close> */

#define states_ready0 0

int states_ready = states_ready0
int states_waiting_for_event = 4
int states_suspended = 32768

/*@ subsection \<open>cpukit/include/rtems/rtems/event.h\<close> */

int rtems_event_0 = 1
int rtems_event_1 = 2
int rtems_event_5 = 32
int rtems_event_7 = 128
int rtems_event_23 = 8388608

/*@ subsection \<open>cpukit/include/rtems/rtems/options.h\<close> */

int rtems_default_options = 0
int rtems_wait = 0
int rtems_no_wait = 1
int rtems_event_all = 0
int rtems_event_any = 2

/*@ subsection \<open>cpukit/include/rtems/rtems/status.h\<close> */

int rtems_successful = 0
int rtems_invalid_id = 4
int rtems_timeout = 6
int rtems_invalid_address = 9
int rtems_unsatisfied = 13
int rtems_not_implemented = 24

/*@ subsection \<open>...\<close> */

typedef thread {
  int state = states_ready0;
  int wait_flags = thread_wait_state_ready_again0;
  int lock_surrender_current = 0;
  int lock_surrender_target = 0;
  int lock_seize = 0;
  int pending = 0;
  int event_in = 0;
  int option_set = 0;
  int event_out_surrender = 0
}

thread thread_pool [thread_num]

/*@ text \<open>
    Our implementation model of thread will assume that a thread in the state
    \<^pml>\<open>states_waiting_for_event\<close> will not be suspended by any external scheduling
    process, even if \<^pml>\<open>states_waiting_for_event\<close> and
    \<^pml>\<open>states_suspended\<close> are disjoint options that can logically occur at the same
    time.
    \<close> */
#define thread_switch(current, prop0, prop1, prop2) atomic { prop0 && prop1 != (prop2) -> prop1 = prop2 };
#define thread_set_on(current, state0, state1) thread_switch(current, thread_pool[current].state != (thread_pool[current].state | state0), thread_pool[current].state, thread_pool[current].state | state1)
#define thread_set_off(current, state2) thread_switch(current, true, thread_pool[current].state, thread_pool[current].state & ~ state2)

/*@ subsection \<open>...\<close> */

#define if_is_satisfied(target, event_in, option_set) \
  int seized; \
  \
  seized = /* _Event_sets_Get */ thread_pool[target].pending & event_in; \
  if \
   :: ! /* _Event_sets_Is_empty */ (seized == 0) \
      && (seized == event_in || option_set & rtems_event_any) -> \
      \
      /* _Event_Satisfy */ \
      thread_pool[target].pending = /* _Event_sets_Clear */ thread_pool[target].pending & ~ seized;

#define not_waiting_for_event(target) (thread_pool[target].state & ~ states_waiting_for_event)

/**/

#define st_ready(current) thread_pool[current].state == states_ready
#define st_not_suspended(current) thread_pool[current].state != (thread_pool[current].state | states_suspended)

inline set_ready_unblock (target) {
  if
   :: /*@ text \<open>
          While \<^pml>\<open>event_surrender_exec\<close> is in execution, this
          \<^pml_token>\<open>atomic\<close> prevents a meanwhile change of the running state to
          \<^pml>\<open>thread_wait_state_blocked\<close> (by
          \<^pml>\<open>event_seize_receive\<close>). Without \<^pml_token>\<open>atomic\<close>,
          the execution of the \<^pml_token>\<open>else\<close> part might not happen, making the
          target thread being still blocked after this \<^pml>\<open>event_surrender_exec\<close>;
          i.e. at the cost of making this \<^pml>\<open>event_surrender_exec\<close> having been
          executed for nothing.
          \<close> */
      atomic { //@ \<^C>\<open>_Thread_Wait_flags_try_change_release\<close>
        thread_pool[target].wait_flags == thread_wait_state_intend_to_block ->
        thread_pool[target].wait_flags = thread_wait_state_ready_again;
      } //@ \<^C>\<open>_Thread_Wait_flags_try_change_release\<close>
   :: else -> //@ \<^C>\<open>_Thread_Wait_flags_try_change_release\<close>
      thread_pool[target].wait_flags = thread_wait_state_ready_again;
      //@ \<^C>\<open>_Thread_Dispatch_disable_critical\<close>
      thread_pool[target].state = not_waiting_for_event (target)
      //@ \<^C>\<open>_Thread_Dispatch_enable\<close>
  fi
}

inline event_surrender_return (history_return, history_id /**/,/**/ current /**/,/**/ target /**/,/**/ status) {
  atomic {
    thread_pool[current].lock_surrender_current = thread_pool[current].lock_surrender_current - 1; //@ \<^C>\<open>_Thread_Wait_release_default\<close>
    thread_pool[target].lock_surrender_target = thread_pool[target].lock_surrender_target - 1; //@ \<^C>\<open>_Thread_Wait_release_default\<close>
    history_return ! history_id, status
  }
}

proctype event_surrender_exec (chan history_return; int history_id /**/;/**/ int current /**/;/**/ int target; int event_in) {
  st_ready (current) ->
  if
   :: target < 0 || target >= thread_num ->
      st_ready (current) ->
      event_surrender_return (history_return, history_id, current, target, rtems_invalid_id)
   :: else ->
      st_ready (current) -> thread_pool[target].pending = thread_pool[target].pending | event_in; //@ \<^C>\<open>_Event_sets_Post\<close>

      st_ready (current) ->
      if
       :: thread_pool[target].wait_flags != thread_wait_state_ready_again -> //@ \<^C>\<open>_Event_Is_blocking_on_event\<close>
          st_ready (current) ->
          if_is_satisfied (target, thread_pool[target].event_in, thread_pool[target].option_set) /*@ \<^pml_token>\<open>
           :: then ->
              satisfy_thread_pending\<close> */
              st_ready (current) ->
              thread_pool[target].event_out_surrender = seized;
              st_ready (current) ->
              set_ready_unblock (target)
           :: else
          fi
       :: else
      fi;
      st_ready (current) ->
      event_surrender_return (history_return, history_id, current, target, rtems_successful)
  fi
}

inline event_surrender_send (history_return, history_id /**/,/**/ current /**/,/**/ target, event_in) {
  if
   :: atomic {
        // (
        thread_pool[current].lock_seize == 0
              /*@ text \<open>
                  prevent this \<^pml>\<open>event_surrender_send\<close> to be suspended by a
                  \<^pml>\<open>event_seize_receive\<close> while in execution
                  \<close>
                  text \<open>
                  Note: in the real implementation, a single thread would not be able to run both
                  \<^pml>\<open>event_seize_receive\<close> and
                  \<^pml>\<open>event_surrender_send\<close> at the same time
                  \<close> */
        // &&
        // thread_pool[current].lock_surrender_current == 0
              /*@ text \<open>
                  prevent the execution of several \<^pml>\<open>event_surrender_send\<close> by the
                  same thread
                  \<close> */
        // )
        ;
        
        thread_pool[current].lock_surrender_current = thread_pool[current].lock_surrender_current + 1;
        thread_pool[target].lock_surrender_target = thread_pool[target].lock_surrender_target + 1
      }; //@ \<^C>\<open>_Thread_Wait_acquire_default_critical\<close>
      run event_surrender_exec (history_return, history_id, current, target, event_in)
   :: else ->
      history_return ! history_id, rtems_not_implemented
  fi
}

inline event_history_surrender_send (current /**/,/**/ target, event_in) {
  event_surrender_send (global_history_surrender, global_history_surrender_id, current, target, event_in);
  global_history_surrender_id++
}

/**/

inline event_seize_return (history_return, history_id /**/,/**/ current /**/,/**/ status, opt_is_some, opt_event_out) {
  atomic {
    thread_pool[current].lock_seize = thread_pool[current].lock_seize - 1; //@ \<^C>\<open>_Thread_Wait_release_default\<close>
    history_return ! history_id, status, opt_is_some, opt_event_out
  }
}

#define event_seize_whenever_unblocked(current) \
  thread_pool[current].state == not_waiting_for_event (current) -> \
  event_seize_return (history_return, history_id, current, rtems_successful, true, thread_pool[current].event_out_surrender)

proctype event_seize_exec (chan history_return; int history_id /**/;/**/ int current /**/;/**/ int event_in; int option_set; int ticks; int opt_event_out) {
  st_ready (current) ->
  if
   :: event_in == 0 ->
      st_ready (current) ->
      event_seize_return (history_return, history_id, current, rtems_successful, true, thread_pool[current].pending)
   :: else ->
      st_ready (current) ->
      if_is_satisfied (current, event_in, option_set) /* \<^pml_token>\<open>
       :: then ->
          satisfy_thread_pending\<close> */
          st_ready (current) ->
          event_seize_return (history_return, history_id, current, rtems_successful, true, seized)
       :: else ->
          st_ready (current) ->
          if
           :: option_set & rtems_no_wait ->
              st_ready (current) ->
              event_seize_return (history_return, history_id, current, rtems_unsatisfied, true, seized)
           :: else ->
              st_ready (current) ->
              thread_pool[current].event_in = event_in;
              thread_pool[current].option_set = option_set;
              thread_pool[current].wait_flags = thread_wait_state_intend_to_block;
              st_ready (current) ->
              //@ \<^C>\<open>_Thread_Dispatch_disable_critical\<close>
              if
               :: atomic { //@ \<^C>\<open>_Thread_Wait_flags_try_change_acquire\<close>
                    thread_pool[current].wait_flags == thread_wait_state_intend_to_block ->
                    thread_pool[current].wait_flags = thread_wait_state_blocked;
                    //@ \<^C>\<open>_Thread_Wait_flags_try_change_acquire\<close>
                    thread_pool[current].state = thread_pool[current].state | states_waiting_for_event
                  }
               :: else //@ \<^C>\<open>_Thread_Wait_flags_try_change_acquire\<close>
              fi;
              /*@ text \<open>
                  During the next whole \<^pml_token>\<open>if\<close> simulating
                  \<^C>\<open>_Thread_Dispatch_direct\<close>, using \<^pml>\<open>st_ready\<close>
                  instead of \<^pml>\<open>st_not_suspended\<close> would be too strong: e.g. we
                  might be in a situation where \<^pml>\<open>event_surrender_send\<close> is itself
                  about to be suspended (as long as this \<^pml>\<open>event_seize_exec\<close> is
                  blocked, e.g. in the case where we assume a thread is able to call both
                  \<^pml>\<open>event_seize_exec\<close> and
                  \<^pml>\<open>event_surrender_send\<close> at the same time), at the precise
                  position where the associated \<^pml>\<open>set_ready_unblock\<close> is not yet
                  called. However this last is needed by \<^pml>\<open>st_ready\<close> for the
                  execution to progress (moreover in this case, an alternate call to
                  \<^pml>\<open>event_surrender_send\<close> by some unrelated thread would still
                  not make the execution progress).
                  \<close>
                  text \<open>
                  Note that the use of \<^pml>\<open>st_not_suspended\<close> would be considered as
                  legitimate, as they are all happening inside a
                  \<^C>\<open>_Thread_Dispatch_direct\<close> scope, which is the part supposed to
                  be managed by an external scheduler, handling the (timing) interruption and
                  resuming of thread.
                  \<close> */
              st_not_suspended (current) ->
              if
               :: ticks <= 0 -> //@ \<^C>\<open>_Thread_Dispatch_direct\<close>
                  st_not_suspended (current) ->
                  event_seize_whenever_unblocked (current)
               :: else -> //@ \<^C>\<open>_Thread_Dispatch_direct\<close>
                  st_not_suspended (current) ->
                  do
                   :: event_seize_whenever_unblocked (current);
                      break
                   :: else ->
                      st_not_suspended (current) ->
                      if
                       :: ticks <= 0 ->
                          atomic {
                            st_not_suspended (current) ->
                            set_ready_unblock (current)
                          };
                          event_seize_return (history_return, history_id, current, rtems_timeout, false, opt_event_out);
                          break
                       :: else ->
                          st_not_suspended (current) ->
                          ticks--
                      fi
                  od
              fi
          fi
      fi
  fi
}

inline event_seize_receive (history_return, history_id /**/,/**/ current /**/,/**/ event_in, option_set, ticks, opt_event_out) {
  if
   :: atomic {
        (thread_pool[current].lock_surrender_current == 0
              /*@ text \<open>
                  prevent this \<^pml>\<open>event_seize_receive\<close> to suspend an already
                  running \<^pml>\<open>event_surrender_send\<close>
                  \<close>
                  text \<open>
                  Note: in the real implementation, a single thread would not be able to run both
                  \<^pml>\<open>event_seize_receive\<close> and
                  \<^pml>\<open>event_surrender_send\<close> at the same time
                  \<close> */
         && thread_pool[current].lock_seize == 0
              /*@ text \<open>
                  prevent the execution of several \<^pml>\<open>event_seize_receive\<close> by the
                  same thread
                  \<close> */);

        thread_pool[current].lock_seize = thread_pool[current].lock_seize + 1
      }; //@ \<^C>\<open>_Thread_Wait_acquire_default_for_executing\<close>
      if
       :: opt_event_out ->
          run event_seize_exec (history_return, history_id, current, event_in, option_set, ticks, opt_event_out)
       :: else ->
          event_seize_return (history_return, history_id, current, rtems_invalid_address, false, opt_event_out)
      fi
   :: else ->
      history_return ! history_id, rtems_not_implemented, false, opt_event_out
  fi
}

inline event_history_seize_receive (current /**/,/**/ event_in, option_set, ticks, opt_event_out) {
  event_seize_receive (global_history_seize, global_history_seize_id, current, event_in, option_set, ticks, opt_event_out);
  global_history_seize_id++
}

/*@ subsection \<open>...\<close> */









/*@ text \<open>
    1st lock: locking the status of \<^pml>\<open>thread_pool[i]\<close> to prevent the modification
    of \<^pml>\<open>thread_pool[i].state\<close> by the scheduler, any threads remain able to
    modify that value concurrently
    \<close>
    text \<open>
    2nd lock: locking on all threads acting on \<^pml>\<open>thread_pool[i]\<close> except one,
    which is executing and can modify \<^pml>\<open>thread_pool[i].state\<close>
    \<close>
*/

/*@
  \<comment> \<open>write: \<^pml>\<open>thread_pool[target].pending\<close> (concurrent overlap of event_in protected as the writing in \<^pml>\<open>thread_pool[target].pending\<close> is a strict subset decreasing)\<close>
  \<comment> \<open>write: \<^pml>\<open>thread_pool[target].wait_flags\<close> (concurrently protected as it is always receiving the same value)\<close>
  \<comment> \<open>
  event_surrender_send: thread i acting on thread target
    if target not ready_again {
      if try_change_release[release, relaxed] (intend_to_block, ready_again) then
        ...
      else
        assert {is blocked}
        set[relaxed] (ready_again)
    }
  \<close>
*/

/*@
  \<comment> \<open>
  event_seize_receive:
    set[relaxed] (intend_to_block)
    try_change_acquire[acquire, acquire] (intend_to_block, blocked)
  \<close>
*/

//@ text \<open>\<^url>\<open>http://gcc.gnu.org/wiki/Atomic/GCCMM/AtomicSync\<close>\<close>
//@ text \<open>\<^url>\<open>https://irl.cs.ucla.edu/~yingdi/web/paperreading/smp_locking.pdf\<close>\<close>
