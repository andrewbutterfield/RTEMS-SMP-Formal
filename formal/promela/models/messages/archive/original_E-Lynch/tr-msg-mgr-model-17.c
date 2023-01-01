/* SPDX-License-Identifier: BSD-2-Clause */

/**
 * @file
 *
 * @ingroup RTEMSTestCaseRtemsModelMessageMgr
 */

/*
 * Copyright (C) 2020 embedded brains GmbH (http://www.embedded-brains.de)
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


#include "tr-msg-mgr-model.h"
//  ===============================================

// @@@ 0 NAME Message_Manager_TestGen
// @@@ 0 DEF TASK_MAX 4
#define TASK_MAX 4
// @@@ 0 DEF BAD_ID 4
#define BAD_ID 4
// @@@ 0 DEF SEMA_MAX 3
#define SEMA_MAX 3
// @@@ 0 DEF MAX_MESSAGE_SIZE 1
#define MAX_MESSAGE_SIZE 1
// @@@ 0 DEF MAX_MESSAGE_QUEUES 3
#define MAX_MESSAGE_QUEUES 3
// @@@ 0 DEF MAX_PENDING_MESSAGES 4
#define MAX_PENDING_MESSAGES 4
// @@@ 0 DECL byte sendrc 0
static rtems_status_code sendrc = 0;
// @@@ 0 DECL byte recrc 0
static rtems_status_code recrc = 0;
// @@@ 0 DECL byte qrc 0
static rtems_status_code qrc = 0;
// @@@ 0 DECL uint8_t send_counter 0
static uint8_t send_counter = 0;
// @@@ 0 DCLARRAY uint8_t receive_buffer MAX_MESSAGE_SIZE
static uint8_t receive_buffer [ MAX_MESSAGE_SIZE ];
// @@@ 0 DCLARRAY uint8_t send_buffer MAX_MESSAGE_SIZE
static uint8_t send_buffer [ MAX_MESSAGE_SIZE ];
// @@@ 0 DCLARRAY RTEMS_MESSAGE_QUEUE_BUFFER queue_buffer MAX_PENDING_MESSAGES
static RTEMS_MESSAGE_QUEUE_BUFFER( MAX_MESSAGE_SIZE ) queue_buffer [MAX_PENDING_MESSAGES];
// @@@ 0 DCLARRAY byte recout TASK_MAX
// DCLARRAY: no refinement entry for 'recout_DCL'
// @@@ 0 DCLARRAY Semaphore semaphore SEMA_MAX
static rtems_id semaphore[SEMA_MAX];

//  ===== TEST CODE SEGMENT 0 =====

static void TestSegment0( Context* ctx ) {
  /* Test Name is defined in the Test Case code (tc-model-msg-mgr.c) */
  
  T_log(T_NORMAL,"@@@ 0 INIT");
  initialise_semaphore( ctx, semaphore );
  
}

//  ===== TEST CODE SEGMENT 3 =====

static void TestSegment3( Context* ctx ) {
  T_log(T_NORMAL,"@@@ 3 TASK Runner");
  checkTaskIs( ctx->runner_id );
  
  T_log(T_NORMAL,"@@@ 3 CALL message_queue_construct 1 1 4 1 1 qrc");
  T_log( T_NORMAL, "Calling construct(%d,%d,%d,%d,%d)");
  
  rtems_message_queue_config config;
  config.name = 1;
  config.maximum_pending_messages = MAX_PENDING_MESSAGES;
  config.maximum_message_size = MAX_MESSAGE_SIZE;
  config.storage_area = queue_buffer;
  config.storage_size = sizeof( queue_buffer );
  config.storage_free = NULL;
  config.attributes = RTEMS_DEFAULT_ATTRIBUTES;
  
  qrc = rtems_message_queue_construct(
    &config,
    &ctx->queue_id
  );
  T_log(T_NORMAL, "Queue id 0x%x", ctx->queue_id);
  T_log( T_NORMAL, "Returned 0x%x from construct", qrc );
  
  T_log(T_NORMAL,"@@@ 3 SCALAR qrc 0");
  T_rsc( qrc, 0 );
  T_log(T_NORMAL,"@@@ 3 SIGNAL 1");
  Wakeup( semaphore[1] );
  
  T_log(T_NORMAL,"@@@ 3 WAIT 0");
  Wait( semaphore[0] );
  
  T_log(T_NORMAL,"@@@ 3 CALL message_queue_send 1 1 1 1 sendrc");
  T_log( T_NORMAL, "Calling Send(%d,%d)");
  
  memset( send_buffer, 1, 1 );
  
  sendrc = rtems_message_queue_send(
    idNull(ctx, 1),
    1 ? send_buffer : NULL,
    1
  );
  
  T_log( T_NORMAL, "Returned 0x%x from send", sendrc );
  
  T_log(T_NORMAL,"@@@ 3 STATE 2 Ready");
  /* We (Task 2) must have been recently ready because we are running */

  T_log(T_NORMAL,"@@@ 3 SCALAR sendrc 0");
  T_rsc( sendrc, 0 );
  T_log(T_NORMAL,"@@@ 3 WAIT 1");
  Wait( semaphore[1] );
  
  T_log(T_NORMAL,"@@@ 3 WAIT 2");
  Wait( semaphore[2] );
  
  T_log(T_NORMAL,"@@@ 3 STATE 1 Zombie");
  /* Code to check that Task 1 has terminated */
}

//  ===== TEST CODE SEGMENT 4 =====

static void TestSegment4( Context* ctx ) {
  T_log(T_NORMAL,"@@@ 4 TASK Worker1");
  checkTaskIs( ctx->worker1_id );
  
  T_log(T_NORMAL,"@@@ 4 WAIT 1");
  Wait( semaphore[1] );
  
  T_log(T_NORMAL,"@@@ 4 SIGNAL 0");
  Wakeup( semaphore[0] );
  
  T_log(T_NORMAL,"@@@ 4 CALL message_queue_receive 2 1 1 10 recrc");
  T_log( T_NORMAL, "Calling Receive(%d,%d)");
  size_t receive_size;
  recrc = rtems_message_queue_receive(
  idNull(ctx, 1),
  receive_buffer,
  &receive_size,
  mergeopts(1),
  getTimeout(10)
  );
  T_log( T_NORMAL, "Returned 0x%x from receive", recrc );
  
  T_log(T_NORMAL,"@@@ 4 STATE 2 TimeWait 10");
  //  DON'T KNOW HOW TO REFINE: 4 'STATE
  T_log(T_NORMAL,"@@@ 4 STATE 2 Ready");
  /* We (Task 2) must have been recently ready because we are running */

  T_log(T_NORMAL,"@@@ 4 SCALAR recrc 0");
  T_rsc( recrc, 0 );
  T_log(T_NORMAL,"@@@ 4 SIGNAL 1");
  Wakeup( semaphore[1] );
  
  T_log(T_NORMAL,"@@@ 4 STATE 2 Zombie");
  /* Code to check that Task 2 has terminated */
}

//  ===== TEST CODE SEGMENT 5 =====

static void TestSegment5( Context* ctx ) {
  T_log(T_NORMAL,"@@@ 5 TASK Worker2");
  checkTaskIs( ctx->worker2_id );
  
  T_log(T_NORMAL,"@@@ 5 SIGNAL 2");
  Wakeup( semaphore[2] );
  
  T_log(T_NORMAL,"@@@ 5 STATE 3 Zombie");
  /* Code to check that Task 3 has terminated */
}

//  ===============================================


static void Runner( RtemsModelMessageMgr_Context *ctx )
{
  T_log( T_NORMAL, "Runner running" );
  TestSegment3( ctx );
  T_log( T_NORMAL, "Runner finished" );
}
/*
static void Worker17( rtems_task_argument arg )
{
  Context *ctx;

  ctx = (Context *) arg;
  rtems_event_set events;

  T_log( T_NORMAL, "Worker Running" );
  TestSegment4( ctx );
  T_log( T_NORMAL, "Worker finished" );

  rtems_event_receive( RTEMS_ALL_EVENTS, RTEMS_DEFAULT_OPTIONS, 0, &events );
}


RTEMS_ALIGNED( RTEMS_TASK_STORAGE_ALIGNMENT ) static char WorkerStorage17[
  RTEMS_TASK_STORAGE_SIZE(
    MAX_TLS_SIZE + RTEMS_MINIMUM_STACK_SIZE,
    WORKER_ATTRIBUTES
  )
];

static const rtems_task_config WorkerConfig17 = {
  .name = rtems_build_name( 'W', 'O', 'R', 'K' ),
  .initial_priority = PRIO_LOW,
  .storage_area = WorkerStorage17,
  .storage_size = sizeof( WorkerStorage17 ),
  .maximum_thread_local_storage_size = MAX_TLS_SIZE,
  .initial_modes = RTEMS_DEFAULT_MODES,
  .attributes = WORKER_ATTRIBUTES
};

*/
static void Worker1( rtems_task_argument arg )
{
  Context *ctx;

  ctx = (Context *) arg;
  rtems_event_set events;

  T_log( T_NORMAL, "Worker1 Running" );
  TestSegment4( ctx );
  T_log( T_NORMAL, "Worker1 finished" );

  rtems_event_receive( RTEMS_ALL_EVENTS, RTEMS_DEFAULT_OPTIONS, 0, &events );
}

static void Worker2( rtems_task_argument arg )
{
  Context *ctx;

  ctx = (Context *) arg;
  rtems_event_set events;

  T_log( T_NORMAL, "Worker2 Running" );
  TestSegment5( ctx );
  T_log( T_NORMAL, "Worker2 finished" );

  rtems_event_receive( RTEMS_ALL_EVENTS, RTEMS_DEFAULT_OPTIONS, 0, &events );
}

static void RtemsModelMessageMgr_Setup17(
  RtemsModelMessageMgr_Context *ctx
)
{
  rtems_status_code   sc;
  rtems_task_priority prio;

  T_log( T_NORMAL, "Runner Setup" );

  memset( ctx, 0, sizeof( *ctx ) );
  ctx->runner_thread = _Thread_Get_executing();
  ctx->runner_id = ctx->runner_thread->Object.id;
  ctx->worker1_wakeup = CreateWakeupSema();
  ctx->worker2_wakeup = CreateWakeupSema();
  ctx->runner_wakeup = CreateWakeupSema();

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

  //sc = rtems_task_construct( &WorkerConfig17, &ctx->worker_id );
  //T_log( T_NORMAL, "Construct Worker, sc = %x", sc );
  //T_assert_rsc_success( sc );

  //T_log( T_NORMAL, "Starting Worker..." );
  //sc = rtems_task_start( ctx->worker_id, Worker17, (rtems_task_argument) ctx );
  //T_log( T_NORMAL, "Started Worker, sc = %x", sc );
  //T_assert_rsc_success( sc );

  sc = rtems_task_create("WRKR",
                          PRIO_NORMAL, 
                          RTEMS_MINIMUM_STACK_SIZE,
                          RTEMS_DEFAULT_MODES,
                          RTEMS_DEFAULT_ATTRIBUTES,
                          &ctx->worker1_id);
  T_assert_rsc_success( sc );

  T_log( T_NORMAL, "Starting Worker1..." );
  sc = rtems_task_start( ctx->worker1_id, Worker1,ctx );
  T_log( T_NORMAL, "Started Worker1, sc = %x", sc );
  T_assert_rsc_success( sc );

  sc = rtems_task_create("WRKR",
                          PRIO_NORMAL, 
                          RTEMS_MINIMUM_STACK_SIZE,
                          RTEMS_DEFAULT_MODES,
                          RTEMS_DEFAULT_ATTRIBUTES,
                          &ctx->worker2_id);
  T_assert_rsc_success( sc );

  T_log( T_NORMAL, "Starting Worker2..." );
  sc = rtems_task_start( ctx->worker2_id, Worker2,ctx );
  T_log( T_NORMAL, "Started Worker2, sc = %x", sc );
  T_assert_rsc_success( sc );

}


static void RtemsModelMessageMgr_Setup_Wrap17( void *arg )
{
  RtemsModelMessageMgr_Context *ctx;

  ctx = arg;
  RtemsModelMessageMgr_Setup17( ctx );
}


static RtemsModelMessageMgr_Context RtemsModelMessageMgr_Instance17;

static T_fixture RtemsModelMessageMgr_Fixture17 = {
  .setup = RtemsModelMessageMgr_Setup_Wrap17,
  .stop = NULL,
  .teardown = RtemsModelMessageMgr_Teardown_Wrap,
  .scope = RtemsModelMessageMgr_Scope,
  .initial_context = &RtemsModelMessageMgr_Instance17
};

static T_fixture_node RtemsModelMessageMgr_Node17;

void RtemsModelMessageMgr_Run17()
{
  RtemsModelMessageMgr_Context *ctx;

  T_set_verbosity( T_NORMAL );

  T_log( T_NORMAL, "Runner Invoked" );
  T_log( T_NORMAL, "Pushing Test Fixture..." );


  ctx = T_push_fixture(
    &RtemsModelMessageMgr_Node17,
    &RtemsModelMessageMgr_Fixture17
  );

  T_log( T_NORMAL, "Test Fixture Pushed" );


  
  ctx->this_test_number = 17;


  ctx->send_status = RTEMS_INCORRECT_STATE;
  ctx->receive_option_set = 0;
  ctx->receive_timeout = RTEMS_NO_TIMEOUT;
  _Thread_Wait_flags_set( ctx->runner_thread, THREAD_WAIT_FLAGS_INITIAL );

  TestSegment0( ctx );

  Runner( ctx );

  RtemsModelMessageMgr_Cleanup( ctx );

  T_log( T_NORMAL, "Run Pop Fixture" );
  T_pop_fixture();
}

/** @} */
