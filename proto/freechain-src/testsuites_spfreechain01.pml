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

#include "cpukit.pml"

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
