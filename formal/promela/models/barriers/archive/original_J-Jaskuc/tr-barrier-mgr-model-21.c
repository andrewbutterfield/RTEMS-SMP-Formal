/* SPDX-License-Identifier: BSD-2-Clause */

/**
 * @file
 *
 * @ingroup RTEMSTestCaseRtemsModelBarrierMgr
 */

/*
 * Copyright (C) 2022 embedded brains GmbH (http://www.embedded-brains.de)
 *                    Trinity College Dublin (http://www.tcd.ie)
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 */

/*
 * This file was automatically generated.  Do not edit it manually.
 * Please have a look at
 *
 * https://docs.rtems.org/branches/master/eng/req/howto.html
 *
 * for information how to maintain and re-generate this file.
 */

#ifndef HAVE_CONFIG_H
#include "config.h"
#endif

#include <rtems/score/threadimpl.h>


#include "tr-model-barrier-mgr.h"

//  ===============================================

// @@@ 0 DEF MAX_BARRIERS 2
#define MAX_BARRIERS 2
// @@@ 0 DEF BARRIER_MAN 0
#define BARRIER_MAN 0
// @@@ 0 DEF BARRIER_AUTO 1
#define BARRIER_AUTO 1
// @@@ 0 DEF MAX_WAITERS 3
#define MAX_WAITERS 3
// @@@ 0 DEF TASK_MAX 4
#define TASK_MAX 4
// @@@ 0 DEF SEMA_MAX 3
#define SEMA_MAX 3
// @@@ 0 DCLARRAY Semaphore semaphore SEMA_MAX
static rtems_id semaphore[SEMA_MAX];

//  ===== TEST CODE SEGMENT 0 =====

static void TestSegment0( Context* ctx ) {
  T_log(T_NORMAL,"@@@ 0 INIT");
  initialise_semaphore( ctx, semaphore );
  
}

//  ===== TEST CODE SEGMENT 3 =====

static void TestSegment3( Context* ctx ) {
  T_log(T_NORMAL,"@@@ 3 TASK Runner");
  checkTaskIs( ctx->runner_id );
  
  T_log(T_NORMAL,"@@@ 3 CALL NormalPriority");
  SetSelfPriority( PRIO_NORMAL );
  rtems_task_priority prio;
  rtems_status_code sc;
  sc = rtems_task_set_priority( RTEMS_SELF, RTEMS_CURRENT_PRIORITY, &prio );
  T_rsc_success( sc );
  T_eq_u32( prio, PRIO_NORMAL );
  
  T_log(T_NORMAL,"@@@ 3 CALL barrier_create 1 1 3 1");
  T_log(T_NORMAL, "Calling BarrierCreate(%d,%d,%d,%d)", 1, 1, 3, 1 );
  rtems_id bid;
  initialise_id(&bid);
  rtems_status_code rc;
  rtems_attribute attribs;
  attribs = mergeattribs(1);
  rc = rtems_barrier_create(1, attribs, 3, 1 ? &bid : NULL);
  T_log(T_NORMAL, "Returned 0x%x from Create", rc );
  
  T_log(T_NORMAL,"@@@ 3 SCALAR created 1");
  /* This is used later for cleanup */ ctx->barrier_id = bid;
  T_log(T_NORMAL,"@@@ 3 SCALAR rc 0");
  T_rsc( rc, 0 );
  T_log(T_NORMAL,"@@@ 3 SIGNAL 1");
  ReleaseSema( semaphore[1] );
  
  T_log(T_NORMAL,"@@@ 3 WAIT 0");
  ObtainSema( semaphore[0] );
  
  T_log(T_NORMAL,"@@@ 3 WAIT 1");
  ObtainSema( semaphore[1] );
  
  T_log(T_NORMAL,"@@@ 3 WAIT 2");
  ObtainSema( semaphore[2] );
  
  T_log(T_NORMAL,"@@@ 3 STATE 1 Zombie");
  /* Code to check that Task 1 has terminated */
}

//  ===== TEST CODE SEGMENT 4 =====

static void TestSegment4( Context* ctx ) {
  T_log(T_NORMAL,"@@@ 4 TASK Worker0");
  checkTaskIs( ctx->worker0_id );
  
  T_log(T_NORMAL,"@@@ 4 CALL NormalPriority");
  SetSelfPriority( PRIO_NORMAL );
  rtems_task_priority prio;
  rtems_status_code sc;
  sc = rtems_task_set_priority( RTEMS_SELF, RTEMS_CURRENT_PRIORITY, &prio );
  T_rsc_success( sc );
  T_eq_u32( prio, PRIO_NORMAL );
  
  T_log(T_NORMAL,"@@@ 4 WAIT 1");
  ObtainSema( semaphore[1] );
  
  T_log(T_NORMAL,"@@@ 4 CALL barrier_ident 1 1");
  T_log(T_NORMAL, "Calling BarrierIdent(%d,%d)", 1, 1 );
  rtems_id bid;
  initialise_id(&bid);
  rtems_status_code rc;
  rc = rtems_barrier_ident(1 , 1 ? &bid : NULL);
  T_log(T_NORMAL, "Returned 0x%x from Ident", rc );
  
  T_log(T_NORMAL,"@@@ 4 SCALAR rc 0");
  T_rsc( rc, 0 );
  T_log(T_NORMAL,"@@@ 4 SIGNAL 2");
  ReleaseSema( semaphore[2] );
  
  T_log(T_NORMAL,"@@@ 4 CALL barrier_wait 1 0");
  rtems_interval timeout = 0;
  T_log(T_NORMAL, "Calling BarrierWait(%d,%d)", bid, timeout );
  rc = rtems_barrier_wait(bid, timeout);
  T_log(T_NORMAL, "Returned 0x%x from Wait", rc );
  
  T_log(T_NORMAL,"@@@ 4 STATE 2 BarrierWait");
  /* Code to check that Task 2 is waiting on the barrier */
  T_log(T_NORMAL,"@@@ 4 STATE 2 Ready");
  /* We (Task 2) must have been recently ready because we are running */

  T_log(T_NORMAL,"@@@ 4 SCALAR rc 7");
  T_rsc( rc, 7 );
  T_log(T_NORMAL,"@@@ 4 SIGNAL 1");
  ReleaseSema( semaphore[1] );
  
  T_log(T_NORMAL,"@@@ 4 STATE 2 Zombie");
  /* Code to check that Task 2 has terminated */
}

//  ===== TEST CODE SEGMENT 5 =====

static void TestSegment5( Context* ctx ) {
  T_log(T_NORMAL,"@@@ 5 TASK Worker1");
  checkTaskIs( ctx->worker1_id );
  
  T_log(T_NORMAL,"@@@ 5 CALL NormalPriority");
  SetSelfPriority( PRIO_NORMAL );
  rtems_task_priority prio;
  rtems_status_code sc;
  sc = rtems_task_set_priority( RTEMS_SELF, RTEMS_CURRENT_PRIORITY, &prio );
  T_rsc_success( sc );
  T_eq_u32( prio, PRIO_NORMAL );
  
  T_log(T_NORMAL,"@@@ 5 WAIT 2");
  ObtainSema( semaphore[2] );
  
  T_log(T_NORMAL,"@@@ 5 CALL barrier_ident 1 1");
  T_log(T_NORMAL, "Calling BarrierIdent(%d,%d)", 1, 1 );
  rtems_id bid;
  initialise_id(&bid);
  rtems_status_code rc;
  rc = rtems_barrier_ident(1 , 1 ? &bid : NULL);
  T_log(T_NORMAL, "Returned 0x%x from Ident", rc );
  
  T_log(T_NORMAL,"@@@ 5 SCALAR rc 0");
  T_rsc( rc, 0 );
  T_log(T_NORMAL,"@@@ 5 SIGNAL 0");
  ReleaseSema( semaphore[0] );
  
  T_log(T_NORMAL,"@@@ 5 CALL barrier_wait 1 4");
  rtems_interval timeout = 4;
  T_log(T_NORMAL, "Calling BarrierWait(%d,%d)", bid, timeout );
  rc = rtems_barrier_wait(bid, timeout);
  T_log(T_NORMAL, "Returned 0x%x from Wait", rc );
  
  T_log(T_NORMAL,"@@@ 5 STATE 3 TimeWait 4");
  //  DON'T KNOW HOW TO REFINE: 5 'STATE
  T_log(T_NORMAL,"@@@ 5 STATE 1 OtherWait");
  /* Code to check that Task 1 is waiting (after pre-emption) */
  T_log(T_NORMAL,"@@@ 5 STATE 3 Ready");
  /* We (Task 3) must have been recently ready because we are running */

  T_log(T_NORMAL,"@@@ 5 STATE 3 Ready");
  /* We (Task 3) must have been recently ready because we are running */

  T_log(T_NORMAL,"@@@ 5 SCALAR rc 6");
  T_rsc( rc, 6 );
  T_log(T_NORMAL,"@@@ 5 CALL barrier_delete 1");
  T_log(T_NORMAL, "Calling BarrierDelete(%d)", bid);
  rc = rtems_barrier_delete(bid);
  T_log(T_NORMAL, "Returned 0x%x from Delete", rc );
  
  T_log(T_NORMAL,"@@@ 5 STATE 2 OtherWait");
  /* Code to check that Task 2 is waiting (after pre-emption) */
  T_log(T_NORMAL,"@@@ 5 STATE 3 Ready");
  /* We (Task 3) must have been recently ready because we are running */

  T_log(T_NORMAL,"@@@ 5 SCALAR rc 0");
  T_rsc( rc, 0 );
  T_log(T_NORMAL,"@@@ 5 SIGNAL 2");
  ReleaseSema( semaphore[2] );
  
  T_log(T_NORMAL,"@@@ 5 STATE 3 Zombie");
  /* Code to check that Task 3 has terminated */
}

//  ===============================================


// Task 0
static void Runner( RtemsModelBarrierMgr_Context *ctx )
{
  T_log( T_NORMAL, "Runner(Task 0) running" );
  TestSegment3( ctx );
  T_log( T_NORMAL, "Runner(Task 0) finished" );

  // Ensure we hold no semaphores
  ReleaseSema( ctx->runner_sema );
  ReleaseSema( ctx->worker0_sema );
  ReleaseSema( ctx->worker1_sema );
}

// Task 1
static void Worker0( rtems_task_argument arg )
{
  Context *ctx;
  ctx = (Context *) arg;
  rtems_event_set events;

  T_log( T_NORMAL, "Worker0(Task 1) running" );
  TestSegment4( ctx );
  T_log( T_NORMAL, "Worker0(Task 1) finished" );

  // Wait for events so that we don't terminate
  rtems_event_receive( RTEMS_ALL_EVENTS, RTEMS_DEFAULT_OPTIONS, 0, &events );
}

// Task 2
static void Worker1( rtems_task_argument arg )
{
  Context *ctx;
  ctx = (Context *) arg;
  rtems_event_set events;

  T_log( T_NORMAL, "Worker1(Task 2) running" );
  TestSegment5( ctx );
  T_log( T_NORMAL, "Worker1(Task 2) finished" );

  // Wait for events so that we don't terminate
  rtems_event_receive( RTEMS_ALL_EVENTS, RTEMS_DEFAULT_OPTIONS, 0, &events );
}

static void RtemsModelBarrierMgr_Setup21( void *arg )
{
  RtemsModelBarrierMgr_Context *ctx;
  ctx = arg;

  rtems_status_code   sc;
  rtems_task_priority prio;

  T_log( T_NORMAL, "Runner Setup" );
  memset( ctx, 0, sizeof( *ctx ) );
  ctx->runner_thread = _Thread_Get_executing();
  ctx->runner_id = ctx->runner_thread->Object.id;

  T_log( T_NORMAL, "Creating Runner Semaphore" );
  ctx->runner_sema = CreateSema("RUNR");

  T_log( T_NORMAL, "Creating Worker0 Semaphore" );
  ctx->worker0_sema = CreateSema("WRS0");

  T_log( T_NORMAL, "Creating Worker1 Semaphore" );
  ctx->worker1_sema = CreateSema("WRS1");

  sc = rtems_task_get_scheduler( RTEMS_SELF, &ctx->runner_sched );
  T_rsc_success( sc );

  #if defined(RTEMS_SMP)
  sc = rtems_scheduler_ident_by_processor( 1, &ctx->other_sched );
  T_rsc_success( sc );
  T_ne_u32( ctx->runner_sched, ctx->other_sched );
  #endif

  prio = 0;
  sc = rtems_task_set_priority( RTEMS_SELF, PRIO_NORMAL, &prio );
  T_rsc_success( sc );
  T_eq_u32( prio, PRIO_HIGH );

  ctx->worker0_id = CreateTask( "WRK0", PRIO_NORMAL );
  T_log( T_NORMAL, "Created Worker 0");
  StartTask( ctx->worker0_id, Worker0, ctx );
  T_log( T_NORMAL, "Started Worker 0");

  ctx->worker1_id = CreateTask( "WRK1", PRIO_NORMAL );
  T_log( T_NORMAL, "Created Worker 1");
  StartTask( ctx->worker1_id, Worker1, ctx );
  T_log( T_NORMAL, "Started Worker 1");
}

static RtemsModelBarrierMgr_Context RtemsModelBarrierMgr_Instance21;

static T_fixture RtemsModelBarrierMgr_Fixture21 = {
  .setup = RtemsModelBarrierMgr_Setup21,
  .stop = NULL,
  .teardown = RtemsModelBarrierMgr_Teardown,
  .scope = RtemsModelBarrierMgr_Scope,
  .initial_context = &RtemsModelBarrierMgr_Instance21
};

static T_fixture_node RtemsModelBarrierMgr_Node21;

void RtemsModelBarrierMgr_Run21()
{
  RtemsModelBarrierMgr_Context *ctx;

  T_set_verbosity( T_NORMAL );
  T_log( T_NORMAL, "Pushing Test Fixture..." );

  ctx = T_push_fixture(
    &RtemsModelBarrierMgr_Node21,
    &RtemsModelBarrierMgr_Fixture21
  );
  // This runs RtemsModelBarrierMgr_Fixture
  T_log( T_NORMAL, "Test Fixture Pushed" );

  ctx->this_test_number = 21;

  memset( &ctx->thread_switch_log, 0, sizeof( ctx->thread_switch_log ) );
  _Thread_Wait_flags_set( ctx->runner_thread, THREAD_WAIT_CLASS_PERIOD );

  TestSegment0( ctx );

  Runner( ctx );

  RtemsModelBarrierMgr_Cleanup( ctx );

  T_log( T_NORMAL, "Run Pop Fixture" );
  T_pop_fixture();
}

/** @} */
