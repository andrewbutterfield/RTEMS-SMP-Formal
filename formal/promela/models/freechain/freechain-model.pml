/* SPDX-License-Identifier: BSD-2-Clause */

/*
 * freechain-model.pml
 *
 * Copyright (C) 2022 Trinity College Dublin (www.tcd.ie)
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

#include "../common/rtems.pml"

// Sizings, MEM_SIZE = 2 ** PTR_SIZE
#define PTR_SIZE 3
#define MEM_SIZE 8

// Nodes types
typedef Node {
  unsigned nxt  : PTR_SIZE
; unsigned prv  : PTR_SIZE
; byte     itm
}

inline ncopy (dst,src) {
  dst.nxt = src.nxt; dst.prv=src.prv; dst.itm = src.itm
}

// Memory
Node memory[MEM_SIZE] ;
byte memory0[MEM_SIZE] ;
unsigned nptr : PTR_SIZE ;  // one node pointer

typedef Control {
  unsigned head : PTR_SIZE
; unsigned tail : PTR_SIZE
; unsigned size : PTR_SIZE
}

Control chain ; // one chain

inline show_node0 () {
  printf("@@@ 0 PTR nptr %d\n",nptr)
}

inline show_node1 () {
// We ignore pointer values here as their values depend on $RTEMS_DEBUG
  printf("@@@ 0 STRUCT nptr\n");
  //  printf("@@@ 0 PTR nxt %d\n", nxt);
  //  printf("@@@ 0 PTR prv %d\n", prv);
  printf("@@@ 0 SCALAR itm %d\n", itm);
  printf("@@@ 0 END nptr\n")
}

inline show_node () {
   atomic{
     show_node0 ();
     if
     :: nptr -> int nxt = chain.head;
                int prv = memory[nptr].prv;
                int itm = memory[nptr].itm;
                show_node1 ()
     :: else -> skip
     fi
   }
}

inline show_chain0 () {
  printf("@@@ 0 SEQ chain\n")
}

inline show_chain1 () {
  printf("@@@ 0 SCALAR _ %d\n",itm)
}

inline show_chain2 () {
  printf("@@@ 0 END chain\n");
}

inline show_chain () {
   int cnp;
   int cnp0;
   atomic{
     cnp = chain.head;
     cnp0 = 0;
     show_chain0 ();
     do // infinite iteration in front of a cycle
       :: (cnp == 0) -> break;
       :: (cnp != 0) ->
            int itm = memory[cnp].itm;
            cnp = memory[cnp].nxt;
            memory0[cnp0] = itm;
            cnp0 = cnp0 + 1;
            show_chain1 ();
     od;
     show_chain2 ()
   }
}

inline append(ch,np) {
  assert (np != 0);
  assert (np != ch.head);
  assert (np != ch.tail);
  assert (memory[np].nxt == 0); // check that np was not already added (somewhere in the middle of the chain) to prevent a cycle
  assert (ch.size < MEM_SIZE);
  if
    :: ch.size == 0 ->
         assert (ch.head == 0);
         assert (ch.tail == 0);
         ch.head = np;
    :: else ->
         assert (ch.head != 0);
         assert (ch.tail != 0);
         memory[ch.tail].nxt = np;
  fi;
  memory[np].prv = ch.tail;
  ch.tail = np;
  ch.size = ch.size + 1;
}

inline doAppend0 () {
  printf("@@@ 0 CALL append %d %d\n",val,addr)
}

proctype doAppend(int addr; int val) {
  atomic{
    memory[addr].itm = val;
    append(chain,addr);
    doAppend0 ();
    show_chain();
  } ;
}

/* np = get(ch) */
inline get(ch,np) {
  np = ch.head ;
  if
    :: ch.size == 0 ->
         assert (ch.head == 0);
         assert (ch.tail == 0);
    :: else ->
         assert (ch.head != 0);
         assert (ch.tail != 0);
         assert (memory[ch.head].prv == 0);
         ch.head = memory[np].nxt;
         if
           :: ch.head == 0 ->
                ch.tail = 0
           :: else ->
                memory[np].nxt = 0; // let the deleted node be potentially added again in the chain
                memory[ch.head].prv = 0
         fi;
         ch.size = ch.size - 1;
  fi;
}

inline doGet0 () {
  printf("@@@ 0 CALL get %d\n",nptr)
}

proctype doGet() {
  atomic{
    get(chain,nptr);
    doGet0 ();
    show_chain();
    show_node();
  } ;
}

/* -----------------------------
 doNonNullGet waits for a non-empty chain
 before doing a get.
 In generated sequential C code this can be simply be treated
  the same as a call to doGet()
*/
inline doNonNullGet0 () {
  printf("@@@ 0 CALL getNonNull %d\n",nptr)
}

proctype doNonNullGet() {
  atomic{
    chain.head != 0;
    get(chain,nptr);
    assert (nptr != 0);
    doNonNullGet0 ();
    show_chain();
    show_node();
  } ;
}


init {
  pid nr;
  atomic{
    printf("\n\n Chain Model running.\n");
    printf("@@@ 0 NAME Chain_AutoGen\n");
    printf("@@@ 0 DEF MAX_SIZE 8\n");
    printf("@@@ 0 DCLARRAY Node memory MAX_SIZE\n");
    printf("@@@ 0 DECL unsigned nptr NULL\n");
    printf("@@@ 0 DECL Control chain\n");

    printf("\nInitialising...\n");
    printf("@@@ 0 INIT\n");
    chain.head = 0; chain.tail = 0; chain.size = 0;
    show_chain();
    show_node();
  } ;

  nr = _nr_pr;

  run doGet();
  nr == _nr_pr;

  run doAppend(6,21);
  run doAppend(3,22);
  run doAppend(4,23);
  run doNonNullGet();
  run doNonNullGet();
  run doNonNullGet();

  nr == _nr_pr;

  assert (chain.size == 0);

  printf("\nChain Model finished !\n\n")
}
