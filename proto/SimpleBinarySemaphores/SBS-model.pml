/* SPDX-License-Identifier: BSD-2-Clause */

/******************************************************************************
 * SBS-model.pml
 *
 * Copyright (C) 2025 Trinity College Dublin (www.tcd.ie)
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
 * We first model a Simple Binary Semaphore (SBS).
 *
 * It has two states: released, and obtained.
 * There is no concept of ownership.
 *
 * It has two operations: Release, and Obtain.
 *
 * Release sets its state to released.
 *
 * Obtain checks its state:
 *  if released, it sets it to obtained and returns;
 *  if obtained, the call blocks until *another* process does a Release,
 *  then it sets it (back) to obtained and returns.
 *
 * We simply model such a semaphore with a single-bit.
 */

inline Release(sbs) {
  sbs = 0 ; 
}

inline Obtain(sbs) {
  atomic{
    sbs == 0 ;
    sbs = 1;
  }
}

/*
 * Scenario:
 *
 * We have several processes performing atomic state-change actions,
 * on global shared state. These processes, as initially given, do not use any
 * synchronisation, so we obtain arbitrary interleavings.
 *
 * However, when we want to develop tests, we want to be able to choose any such
 * interleaving, and construct test code that *always* reproduces it, while
 * running in a real environment with the usual "capricious" scheduler. This is
 * achieved by adding in simple binary semaphores and inserting in appropriate
 * Obtain and Release calls. We call this process "orchestration".
 *
 * We define a scenario as a list of atomic actions, each tagged with the
 * identity of the process that performs it. Orchestration involves using the
 * changes in process tags between steps in a scenario to insert approproiate
 * SBS calls in both processes to enforce the suspension of the "before"
 * process, and the resumption of the "after" process.
 *
 * We seek an approach that is easy to automate
 */




init {

  bool sbs ;

  Obtain(sbs);  
  printf("Hello\n")
  Release(sbs);
  printf("World!\n")
}