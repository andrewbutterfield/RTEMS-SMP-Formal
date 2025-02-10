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
 * Goal:
 *
 * To formally model an automatable way of "orchestrating" concurrent test code
 * to make it deterministic, and to use Promela/SPIN to verify that the solution
 * is deadlock- and livelock-free.
 */

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
 * We define a process as a pair consisting of its identity, and a list of the 
 * atomic actions it performs. For now we assume the list is finite.
 *
 * We define a scenario as a list of atomic actions, each tagged with the
 * identity of the process that performs it. Orchestration involves using the
 * changes in process tags between steps in a scenario to insert appropriate
 * SBS calls in both processes to enforce the suspension of the "before"
 * process, and the resumption of the "after" process.
 *
 * We seek an approach that is easy to automate, and not dependent on the 
 * finiteness of the process action lists.
 */

/* Setup:
 * we will have three global variables, a predefined list of atomic actions, and
 * three processes.
 */

byte g1,g2,g3;

inline k1(val) { atomic{ g1 = val ; printf("p%d.k1(%d)\n",_pid,val) } }
inline k2(val) { atomic{ g2 = val ; printf("p%d.k2(%d)\n",_pid,val) } }
inline k3(val) { atomic{ g3 = val ; printf("p%d.k3(%d)\n",_pid,val) } }

proctype p1() { k1(13); k2(42); k3(99); }
proctype p2() { k2(13); k3(42); k1(99); }
proctype p3() { k3(13); k1(42); k2(99); }

/*
 * After some runs we obtained the following scenario:
 *
 *      p1.k1(13)
 *      p1.k2(42)
 *      p1.k3(99)
 *          p2.k2(13)
 *              p3.k3(13)
 *          p2.k3(42)
 *          p2.k1(99)
 *              p3.k1(42)
 *              p3.k2(99)
 *  Done, (g1,g2,g3)=(42,99,42)
 * 
 * So we shall now orchestrate this.
 */

// It helps to be able to backup a scenario final outcome
inline gbackup(b1,b2,b3) { b1=g1; b2=g2; b3=g3 }


// First, a single process that reproduces the scenario
byte ts1,ts2,ts3 ;

proctype theScenario() {
  g1=0; g2=0; g3=0;
  k1(13); k2(42); k3(99); k2(13); k3(13); k3(42); k1(99); k1(42); k2(99)
  gbackup(ts1,ts2,ts3);
  printf("theScenario: (ts1,ts2,ts3)=(%d,%d,%d)\n",ts1,ts2,ts3) ;
}

// It helps to be able to backup a scenario final outcome
inline gbackup(b1,b2,b3) { b1=g1; b2=g2; b3=g3 }

/*
 * Reproducing the scenario:
 * 
 * Every process has to obtain its own SBS at the start.
 * We "pre-Obtain" those of the processes that don't run first.
 *
 * When we switch from the running process to a designated waiting process, the
 * running process performs:
 *  1. Release the waiting SBS, which the waiting process now obtains.
 *  2. Obtain its own (as this is obtained, we block here.)
 * The invariant is that when a process is running its SBS is obtained.
 *
 * We need to care when a process has ended but needs to explicitly handover to
 * another waiting process (as per scenario above).
 */


/*
 * Model mainline
 */

init {

  run p1() ;
  run p2() ;
  run p3() ;

  _nr_pr == 1;

  printf("Done, (g1,g2,g3)=(%d,%d,%d)\n",g1,g2,g3) ;

  run theScenario() ;
  
}