/* SPDX-License-Identifier: BSD-2-Clause */

/******************************************************************************
 * TestSync.pml
 *
 * Copyright (C) 2023 Trinity College Dublin (www.tcd.ie)
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

// Binary Semaphores
#define MAX_BINARY_SEMAPHORE 4
#define GLOBAL_MUTEX 0
bool semaphore[MAX_BINARY_SEMAPHORE];

inline init_sem( sem_number, value ) {
    semaphore[ sem_number ] = value ;
}

inline obtain_sem( sem_number ) {
    atomic{ semaphore[ sem_number] -> semaphore[ sem_number] = false ;}
}

inline release_sem( sem_number ) {
    semaphore[ sem_number] = true ;
}

inline start( taskno ) {
    obtain_sem( taskno );
    obtain_sem( GLOBAL_MUTEX );
}

inline perform( event ) {
    printf("%d\n",event)
}

inline yield( from, to ) {
    release_sem( GLOBAL_MUTEX );
    release_sem( to );
    obtain_sem( from );
    obtain_sem( GLOBAL_MUTEX );
}

inline leave_to( to ) {
    release_sem( GLOBAL_MUTEX );
    if
    :: to -> release_sem( to ); 
    :: else
    fi
}

proctype Task1() { // always runs first.
    printf("Task 1 started\n")
    start( 1 );
    perform( 101 );
    yield( 1, 2 );
    perform( 102 );
    leave_to( 2 );
    printf("Task 1 terminates\n");
}

proctype Task2() { // always waits first
    printf("Task 2 started\n")
    start( 2 );
    perform( 201 );
    yield( 2, 1 );
    perform( 202 );
    leave_to( 0 );
    printf("Task 2 terminates\n")
}

init {
  int i = 2;

    printf( "Test Sync Prototype\n" );
    init_sem( GLOBAL_MUTEX, true );
    init_sem( 1, true ); // We assume Task 1 goes first
    do // all other tasks wait at start
    ::  i < MAX_BINARY_SEMAPHORE -> init_sem( i, false ); i = i+1
    ::  else -> break;
    od   
    run Task1(); run Task2();
    (_nr_pr == 1);
    printf("DONE :-)\n") 
}