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

#define QUEUE_SIZE 4
#define OP_ATTEMPTS 5

mtype = { exit_success , error_queue_full , error_queue_empty }
mtype = { op_add , op_del }
mtype = { not_waiting , wait_for_add , wait_for_del }

int q_size_max
int q_size_current
int q_tail
int q_head
int q_content [QUEUE_SIZE]

mtype sched_status = not_waiting
chan history_op = [100] of { mtype }

proctype head_add (chan ret; int x) {
  atomic {
    history_op ! op_add;
    if
      :: q_size_current == q_size_max ->
         ret ! error_queue_full
      :: else ->
         q_content [q_head] = x;
         q_head = (q_head + 1) % q_size_max;
         q_size_current ++;
         ret ! exit_success
    fi
  }
}

proctype head_del (chan ret; int x) {
  atomic {
    history_op ! op_del;
    if
      :: q_size_current == 0 ->
         ret ! error_queue_empty
      :: else ->
         q_head = (q_head + q_size_max - 1) % q_size_max;
         q_content [q_head] = 0;
         q_size_current --;
         ret ! exit_success
    fi
  }
}

proctype tail_add (chan ret; int x) {
  atomic {
    history_op ! op_add;
    if
      :: q_size_current == q_size_max ->
         ret ! error_queue_full
      :: else ->
         q_content [q_tail] = x;
         q_tail = (q_tail + q_size_max - 1) % q_size_max;
         q_size_current ++;
         ret ! exit_success
    fi
  }
}

proctype tail_del (chan ret; int x) {
  atomic {
    history_op ! op_del;
    if
      :: q_size_current == 0 ->
         ret ! error_queue_empty
      :: else ->
         q_tail = (q_tail + 1) % q_size_max;
         q_content [q_tail] = 0;
         q_size_current --;
         ret ! exit_success
    fi
  }
}
