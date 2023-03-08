/* SPDX-License-Identifier: BSD-2-Clause */

/**
 * @file
 *
 * @ingroup RTEMSTestCaseRtemsModelSemMgr
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


#include "tr-sem-mgr-model.h"

//  ===============================================

// @@@ 0 DEF MAX_MODEL_SEMAS 2
#define MAX_MODEL_SEMAS 2
// @@@ 0 DEF SEMAPHORE_LOCAL 0
#define SEMAPHORE_LOCAL 0
// @@@ 0 DEF SEMAPHORE_GLOBAL 1
#define SEMAPHORE_GLOBAL 1
// @@@ 0 DEF COUNTING_S 0
#define COUNTING_S 0
// @@@ 0 DEF BINARY_S 1
#define BINARY_S 1
// @@@ 0 DEF SIMPLE_BINARY_S 2
#define SIMPLE_BINARY_S 2
// @@@ 0 DEF FIFO 0
#define FIFO 0
// @@@ 0 DEF PRIORITY 1
#define PRIORITY 1
// @@@ 0 DEF NO_LOCKING 0
#define NO_LOCKING 0
// @@@ 0 DEF INHERIT_LOCKING 1
#define INHERIT_LOCKING 1
// @@@ 0 DEF CEILING_LOCKING 2
#define CEILING_LOCKING 2
// @@@ 0 DEF MRSP_LOCKING 3
#define MRSP_LOCKING 3
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
  SetSelfPriority( SM_PRIO_NORMAL );
  rtems_task_priority prio;
  rtems_status_code sc;
  sc = rtems_task_set_priority( RTEMS_SELF, RTEMS_CURRENT_PRIORITY, &prio );
  T_rsc_success( sc );
  T_eq_u32( prio, SM_PRIO_NORMAL );
  
  T_log(T_NORMAL,"@@@ 3 CALL merge_attribs 0 0 0 0 ");
  T_log(T_NORMAL, "Calling mergeattribs(%d,%d,%d,%d)", 0, 0, 0, 0 );
  rtems_attribute attribs;
  attribs = mergeattribs(0,0,0,0);
  
  T_log(T_NORMAL,"@@@ 3 CALL sema_create 1 1 2 1 ");
  T_log(T_NORMAL, "Calling SemaCreate(%d,%d,%d,%d)", 1, 1, 2, 1 );
  rtems_id sem_id;
  initialise_id(&sem_id);
  rtems_status_code rc;
  rc = rtems_semaphore_create(1, 1,attribs, 2, 1 ? &sem_id : NULL);
  T_log(T_NORMAL, "Returned 0x%x from Create", rc );
  
  T_log(T_NORMAL,"@@@ 3 SCALAR created 1");
  /* This is used later for cleanup */ ctx->sem_id = sem_id;
  T_log(T_NORMAL,"@@@ 3 SCALAR rc 0");
  T_rsc( rc, 0 );
  T_log(T_NORMAL,"@@@ 3 SIGNAL 1");
  ReleaseSema( semaphore[1] );
  
  T_log(T_NORMAL,"@@@ 3 WAIT 0");
  ObtainSema( semaphore[0] );
  
  T_log(T_NORMAL,"@@@ 3 CALL sema_delete 1");
  T_log(T_NORMAL, "Calling SemaDelete(%d)", sem_id);
  rc = rtems_semaphore_delete(sem_id);
  T_log(T_NORMAL, "Returned 0x%x from Delete", rc );
  
  T_log(T_NORMAL,"@@@ 3 SCALAR rc 0");
  T_rsc( rc, 0 );
  T_log(T_NORMAL,"@@@ 3 SIGNAL 0");
  ReleaseSema( semaphore[0] );
  
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
  SetSelfPriority( SM_PRIO_NORMAL );
  rtems_task_priority prio;
  rtems_status_code sc;
  sc = rtems_task_set_priority( RTEMS_SELF, RTEMS_CURRENT_PRIORITY, &prio );
  T_rsc_success( sc );
  T_eq_u32( prio, SM_PRIO_NORMAL );
  
  T_log(T_NORMAL,"@@@ 4 WAIT 1");
  ObtainSema( semaphore[1] );
  
  T_log(T_NORMAL,"@@@ 4 CALL sema_ident 1 0 1");
  T_log(T_NORMAL, "Calling SemaIdent(%d,%d, %d)", 1, 0, 1);
  rtems_id sem_id;
  initialise_id(&sem_id);
  rtems_status_code rc;
  rc = rtems_semaphore_ident(1 , 0, 1 ? &sem_id : NULL);
  T_log(T_NORMAL, "Returned 0x%x from Ident", rc );
  
  T_log(T_NORMAL,"@@@ 4 SCALAR rc 0");
  T_rsc( rc, 0 );
  T_log(T_NORMAL,"@@@ 4 SIGNAL 2");
  ReleaseSema( semaphore[2] );
  
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
  SetSelfPriority( SM_PRIO_NORMAL );
  rtems_task_priority prio;
  rtems_status_code sc;
  sc = rtems_task_set_priority( RTEMS_SELF, RTEMS_CURRENT_PRIORITY, &prio );
  T_rsc_success( sc );
  T_eq_u32( prio, SM_PRIO_NORMAL );
  
  T_log(T_NORMAL,"@@@ 5 WAIT 2");
  ObtainSema( semaphore[2] );
  
  T_log(T_NORMAL,"@@@ 5 CALL sema_ident 1 0 1");
  T_log(T_NORMAL, "Calling SemaIdent(%d,%d, %d)", 1, 0, 1);
  rtems_id sem_id;
  initialise_id(&sem_id);
  rtems_status_code rc;
  rc = rtems_semaphore_ident(1 , 0, 1 ? &sem_id : NULL);
  T_log(T_NORMAL, "Returned 0x%x from Ident", rc );
  
  T_log(T_NORMAL,"@@@ 5 SCALAR rc 0");
  T_rsc( rc, 0 );
  T_log(T_NORMAL,"@@@ 5 SIGNAL 0");
  ReleaseSema( semaphore[0] );
  
  T_log(T_NORMAL,"@@@ 5 SIGNAL 2");
  ReleaseSema( semaphore[2] );
  
  T_log(T_NORMAL,"@@@ 5 STATE 3 Zombie");
  /* Code to check that Task 3 has terminated */
}

//  ===============================================


// Task 0
static void Runner( RtemsModelSemMgr_Context *ctx )
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
static void RtemsModelSemMgr_Setup4( void *arg )
{
  RtemsModelSemMgr_Context *ctx;
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
  sc = rtems_task_set_priority( RTEMS_SELF, SM_PRIO_NORMAL, &prio );
  T_rsc_success( sc );
  T_eq_u32( prio, SM_PRIO_HIGH );
  
  ctx->worker0_id = CreateTask( "WRK0", SM_PRIO_NORMAL );
  T_log( T_NORMAL, "Created Worker 0");
  StartTask( ctx->worker0_id, Worker0, ctx );
  T_log( T_NORMAL, "Started Worker 0");

  ctx->worker1_id = CreateTask( "WRK1", SM_PRIO_NORMAL );
  T_log( T_NORMAL, "Created Worker 1");
  StartTask( ctx->worker1_id, Worker1, ctx );
  T_log( T_NORMAL, "Started Worker 1");

}

static RtemsModelSemMgr_Context RtemsModelSemMgr_Instance4;

static T_fixture RtemsModelSemMgr_Fixture4 = {
  .setup = RtemsModelSemMgr_Setup4,
  .stop = NULL,
  .teardown = RtemsModelSemMgr_Teardown,
  .scope = RtemsModelSemMgr_Scope,
  .initial_context = &RtemsModelSemMgr_Instance4
};

static T_fixture_node RtemsModelSemMgr_Node4;

void RtemsModelSemMgr_Run4()
{
  RtemsModelSemMgr_Context *ctx;

  T_set_verbosity( T_NORMAL );
  T_log( T_NORMAL, "Pushing Test Fixture..." );

  ctx = T_push_fixture(
    &RtemsModelSemMgr_Node4,
    &RtemsModelSemMgr_Fixture4
  );
  // This runs RtemsModelSemMgr_Fixture
  T_log( T_NORMAL, "Test Fixture Pushed" );

  ctx->this_test_number = 4;

  memset( &ctx->thread_switch_log, 0, sizeof( ctx->thread_switch_log ) );
  _Thread_Wait_flags_set( ctx->runner_thread, THREAD_WAIT_CLASS_PERIOD );

  TestSegment0( ctx );

  Runner( ctx );

  RtemsModelSemMgr_Cleanup( ctx );

  T_log( T_NORMAL, "Run Pop Fixture" );
  T_pop_fixture();
}

/** @} */
