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

#include "../cpukit.pml"


proctype init_head_add () {
  chan ret = [0] of { mtype };
  int n = OP_ATTEMPTS;
  do
    :: n == 0 ->
       break
    :: n != 0 && sched_status != wait_for_del ->
       atomic {
         run head_add (ret, n);
         if
           :: ret ? error_queue_full ->
              sched_status = wait_for_del
           :: ret ? exit_success ->
              n --;
              if
                :: sched_status == wait_for_add ->
                   sched_status = not_waiting
                :: else ->
                   skip
              fi
         fi
       }
  od
}

proctype init_head_del () {
  chan ret = [0] of { mtype };
  int n = OP_ATTEMPTS;
  do
    :: n == 0 ->
       break
    :: n != 0 && sched_status != wait_for_add ->
       atomic {
         run head_del (ret, 10 + n);
         if
           :: ret ? error_queue_empty ->
              sched_status = wait_for_add
           :: ret ? exit_success ->
              n --;
              if
                :: sched_status == wait_for_del ->
                   sched_status = not_waiting
                :: else ->
                   skip
              fi
         fi
       }
  od
}

init {
  pid nr;
  q_size_max = QUEUE_SIZE;
  q_size_current = 0;
  q_tail = q_size_max - 1;
  q_head = 0;
  nr = _nr_pr;
  run init_head_add ();
  run init_head_del ();
  nr == _nr_pr;
  assert (q_size_current == 0);
}
