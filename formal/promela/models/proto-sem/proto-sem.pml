/* SPDX-License-Identifier: BSD-2-Clause */

/*
 * proto-sem.pml
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
 */

/*
 * The model presented here is designed to work with the following files:
 *   Refinement:   proto-sem-rfn.yml
 *   Test Preamble: proto-sem-pre.h
 *   Test Postamble: proto-sem-post.h
 *   Test Runner: proto-sem-run.h
 */


#include "../common/rtems.pml"
#define TASK_MAX 3 
#define SEMA_MAX 2
#include "../common/model.pml"




inline outputDefines () {
   // printf("@@@ %d DEF NO_OF_EVENTS %d\n",_pid,NO_OF_EVENTS);
   atomic{printf("Nothing DEFINEd at present\n");}
}


/*
 * We define: 
 *  - two global variables g1,g2.
 *  - two functions that update both, differently
 *  - two tasks that each call one of the above functions.
 *
 *  Initially the functions are atomic.
 *  Later we might weaken this and mix the calls a bit.
 */

int g1,g2 ;

inline outputDeclarations () {
  printf("@@@ %d DECL int g1\n",_pid);
  printf("@@@ %d DECL int g2\n",_pid);
}


inline update1() {
  atomic{ g1 = g2+10; g2 = g1*2 }
}

inline update2() {
  atomic{ g2 = g1+5 ; g1 = g2*3 }
}







/*
 * Model Processes
 * We shall use four processes in this model.
 *  Two will represent RTEMS Tasks
 *  Two will be the common System and CLock processes
 */


inline chooseScenario() {

  // Common Defaults
  atomic{printf("No scenarios to be chosen right now\n")}
 

}


proctype Runner (byte nid, taskid) {

  atomic{ 
    printf("Runner running...\n") ;
    printf("@@@ %d TASK Runner\n",_pid);
  } ;

  atomic{
    printf("Runner: before update1\n");
    printf("@@@ %d SCALAR g1 %d\n",_pid,g1);
    printf("@@@ %d SCALAR g2 %d\n",_pid,g2);

    update1();
    printf("@@@ %d CALL update1\n",_pid);

    printf("Runner: after update1\n");
    printf("@@@ %d SCALAR g1 %d\n",_pid,g1);
    printf("@@@ %d SCALAR g2 %d\n",_pid,g2);
  }

  printf("@@@ %d LOG Sender %d finished\n",_pid,taskid);
  tasks[taskid].state = Zombie;
  printf("@@@ %d STATE %d Zombie\n",_pid,taskid)

}


proctype Worker (byte nid, taskid) {

  atomic{
    printf("Worker running...\n") ;
    printf("@@@ %d TASK Worker\n",_pid);
  } ;
  
  atomic{
    printf("Worker: before update2\n");
    printf("@@@ %d SCALAR g1 %d\n",_pid,g1);
    printf("@@@ %d SCALAR g2 %d\n",_pid,g2);

    update2();
    printf("@@@ %d CALL update2\n",_pid);
  
    printf("Worker: after update2\n");
    printf("@@@ %d SCALAR g1 %d\n",_pid,g1);
    printf("@@@ %d SCALAR g2 %d\n",_pid,g2);
  }

  printf("@@@ %d LOG Sender %d finished\n",_pid,taskid);
  tasks[taskid].state = Zombie;
  printf("@@@ %d STATE %d Zombie\n",_pid,taskid)
}

init {
  pid nr;

  printf("Prototype Semantics Model running.\n");
  printf("Setup...\n");

  printf("@@@ %d NAME Prototype_Semantics_TestGen\n",_pid)
  outputDefines();
  outputDeclarations();

  printf("@@@ %d INIT\n",_pid);
  chooseScenario();



  printf("Run...\n");

  run System();
  run Clock();

  run Runner(0,1);
  run Worker(0,2);

  _nr_pr == 1;


#ifdef TEST_GEN
  assert(false);
#endif

  printf("Prototype Semantics Model finished !\n")
}
