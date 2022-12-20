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

int q_size_max
int q_size_current
int q_tail
int q_head
int q_content [QUEUE_SIZE]

proctype head_add (chan ret; int x) {
  atomic {
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

proctype init_head_add () {
  chan ret = [0] of { mtype };
  int n = OP_ATTEMPTS;
  do
    :: n == 0 ->
       break
    :: else ->
       run head_add (ret, n);
       if
         :: ret ? error_queue_full ->
            skip
         :: ret ? exit_success ->
            n --
       fi
  od
}

proctype init_head_del () {
  chan ret = [0] of { mtype };
  int n = OP_ATTEMPTS;
  do
    :: n == 0 ->
       break
    :: else ->
       run head_del (ret, 10 + n);
       if
         :: ret ? error_queue_empty ->
            skip
         :: ret ? exit_success ->
            n --
       fi
  od
}

proctype init_simple () {
  chan ret = [100] of { mtype };
  run head_add (ret, 1);
  run head_add (ret, 2);
  run head_add (ret, 10);
  run head_add (ret, 20);
  run head_del (ret, 3);
  run head_del (ret, 4);
  run head_del (ret, 30);
  run head_del (ret, 40);
  run tail_add (ret, 5);
  run tail_add (ret, 6);
  run tail_add (ret, 50);
  run tail_add (ret, 60);
  run tail_del (ret, 7);
  run tail_del (ret, 8);
  run tail_del (ret, 70);
  run tail_del (ret, 80)
}

init {
  q_size_max = QUEUE_SIZE;
  q_size_current = 0;
  q_tail = q_size_max - 1;
  q_head = 0;
  // run init_simple ()
  run init_head_add ();
  run init_head_del ()
  
/* If the process init_head_del is always firstly executed (i.e., starting with an empty queue),
   this would result in an infinite loop because the error raised by head_del is always silently
   ignores in this implementation. */

}
