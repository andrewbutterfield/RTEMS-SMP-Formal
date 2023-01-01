/* SPDX-License-Identifier: BSD-2-Clause */

/**
 * @file
 *
 * @ingroup RTEMSTestCaseRtemsEventReqSendReceive
 */

/*
 * Copyright (C) 2020 embedded brains GmbH (http://www.embedded-brains.de)
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

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include <rtems/score/threadimpl.h>

#include "tr-event-send-receive.h"

#include <rtems/test.h>

/**
 * @defgroup RTEMSTestCaseRtemsEventReqSendReceive \
 *   spec:/rtems/event/req/send-receive
 *
 * @ingroup RTEMSTestSuiteTestsuitesValidation0
 *
 * @{
 */

typedef enum {
  PRIO_HIGH = 1,
  PRIO_NORMAL,
  PRIO_LOW,
  PRIO_OTHER
} Priorities;

typedef enum {
  SENDER_NONE,
  SENDER_SELF,
  SENDER_SELF_2,
  SENDER_WORKER,
  SENDER_INTERRUPT
} SenderTypes;

typedef enum {
  RECEIVE_SKIP,
  RECEIVE_NORMAL,
  RECEIVE_INTERRUPT
} ReceiveTypes;

typedef enum {
  RECEIVE_COND_UNKNOWN,
  RECEIVE_COND_SATSIFIED,
  RECEIVE_COND_UNSATISFIED
} ReceiveConditionStates;

/**
 * @brief Test context for spec:/rtems/event/req/send-receive test case.
 */
typedef struct {
  /**
   * @brief This member defines the sender type to perform the event send
   *   action.
   */
  SenderTypes sender_type;

  /**
   * @brief This member defines the sender task priority.
   */
  Priorities sender_prio;

  /**
   * @brief This member defines the receiver ID used for the event send action.
   */
  rtems_id receiver_id;

  /**
   * @brief This member defines the events to send for the event send action.
   */
  rtems_event_set events_to_send;

  /**
   * @brief This member contains the status of the event send action.
   */
  rtems_status_code send_status;

  /**
   * @brief This member contains the scheduler ID of the runner task.
   */
  ReceiveTypes receive_type;

  /**
   * @brief This member defines the option set used for the event receive
   *   action.
   */
  rtems_option receive_option_set;

  /**
   * @brief This member defines the timeout used for the event receive action.
   */
  rtems_interval receive_timeout;

  /**
   * @brief This member contains the events received by the event receive
   *   action.
   */
  rtems_event_set received_events;

  /**
   * @brief This member contains the status of the event receive action.
   */
  rtems_status_code receive_status;

  /**
   * @brief This member contains the event conditon state of the receiver task
   *   after the event send action.
   */
  ReceiveConditionStates receive_condition_state;

  /**
   * @brief This member contains the pending events after an event send action
   *   which did not satsify the event condition of the receiver.
   */
  rtems_event_set unsatisfied_pending;

  /**
   * @brief This member contains the TCB of the runner task.
   */
  Thread_Control *runner_thread;

  /**
   * @brief This member contains the ID of the runner task.
   */
  rtems_id runner_id;

  /**
   * @brief This member contains the task ID of the worker task.
   */
  rtems_id worker_id;

  /**
   * @brief This member contains the ID of the semaphore used to wake up the
   *   worker task.
   */
  rtems_id worker_wakeup;

  /**
   * @brief This member contains the ID of the semaphore used to wake up the
   *   runner task.
   */
  rtems_id runner_wakeup;

  /**
   * @brief This member contains the scheduler ID of scheduler used by the
   *   runner task.
   */
  rtems_id runner_sched;

  /**
   * @brief This member contains the scheduler ID of another scheduler which is
   *   not used by the runner task.
   */
  rtems_id other_sched;

  /**
   * @brief This member contains the thread switch log.
   */
  T_thread_switch_log_4 thread_switch_log;

  /**
   * @brief This member contains a copy of the corresponding
   *   RtemsEventReqSendReceive_Run() parameter.
   */
  rtems_status_code ( *send )( rtems_id, rtems_event_set );

  /**
   * @brief This member contains a copy of the corresponding
   *   RtemsEventReqSendReceive_Run() parameter.
   */
  rtems_status_code ( *receive )( rtems_event_set, rtems_option, rtems_interval, rtems_event_set * );

  /**
   * @brief This member contains a copy of the corresponding
   *   RtemsEventReqSendReceive_Run() parameter.
   */
  rtems_event_set ( *get_pending_events )( Thread_Control * );

  /**
   * @brief This member contains a copy of the corresponding
   *   RtemsEventReqSendReceive_Run() parameter.
   */
  unsigned int wait_class;

  /**
   * @brief This member contains a copy of the corresponding
   *   RtemsEventReqSendReceive_Run() parameter.
   */
  int waiting_for_event;

  /**
   * @brief This member defines the pre-condition states for the next action.
   */
  size_t pcs[ 4 ];

  /**
   * @brief This member indicates if the test action loop is currently
   *   executed.
   */
  bool in_action_loop;
} RtemsEventReqSendReceive_Context;

static RtemsEventReqSendReceive_Context
  RtemsEventReqSendReceive_Instance;

static const char * const RtemsEventReqSendReceive_PreDesc_Id[] = {
  "InvId",
  "Task",
  "NA"
};

static const char * const RtemsEventReqSendReceive_PreDesc_Send[] = {
  "Zero",
  "Unrelated",
  "Any",
  "All",
  "MixedAny",
  "MixedAll",
  "NA"
};

static const char * const RtemsEventReqSendReceive_PreDesc_ReceiverState[] = {
  "NotWaiting",
  "Poll",
  "Timeout",
  "Lower",
  "Equal",
  "Higher",
  "Other",
  "Intend",
  "NA"
};

static const char * const RtemsEventReqSendReceive_PreDesc_Satisfy[] = {
  "All",
  "Any",
  "NA"
};

static const char * const * const RtemsEventReqSendReceive_PreDesc[] = {
  RtemsEventReqSendReceive_PreDesc_Id,
  RtemsEventReqSendReceive_PreDesc_Send,
  RtemsEventReqSendReceive_PreDesc_ReceiverState,
  RtemsEventReqSendReceive_PreDesc_Satisfy,
  NULL
};

#define INPUT_EVENTS ( RTEMS_EVENT_5 | RTEMS_EVENT_23 )

#define WORKER_ATTRIBUTES RTEMS_DEFAULT_ATTRIBUTES

#define MAX_TLS_SIZE RTEMS_ALIGN_UP( 64, RTEMS_TASK_STORAGE_ALIGNMENT )

typedef RtemsEventReqSendReceive_Context Context;

RTEMS_ALIGNED( RTEMS_TASK_STORAGE_ALIGNMENT ) static char WorkerStorage[
  RTEMS_TASK_STORAGE_SIZE(
    MAX_TLS_SIZE + RTEMS_MINIMUM_STACK_SIZE,
    WORKER_ATTRIBUTES
  )
];

static const rtems_task_config WorkerConfig = {
  .name = rtems_build_name( 'W', 'O', 'R', 'K' ),
  .initial_priority = PRIO_LOW,
  .storage_area = WorkerStorage,
  .storage_size = sizeof( WorkerStorage ),
  .maximum_thread_local_storage_size = MAX_TLS_SIZE,
  .initial_modes = RTEMS_DEFAULT_MODES,
  .attributes = WORKER_ATTRIBUTES
};

static rtems_id CreateWakeupSema( void )
{
  rtems_status_code sc;
  rtems_id id;

  sc = rtems_semaphore_create(
    rtems_build_name( 'W', 'K', 'U', 'P' ),
    0,
    RTEMS_SIMPLE_BINARY_SEMAPHORE,
    0,
    &id
  );
  T_assert_rsc_success( sc );

  return id;
}

static void DeleteWakeupSema( rtems_id id )
{
  if ( id != 0 ) {
    rtems_status_code sc;

    sc = rtems_semaphore_delete( id );
    T_rsc_success( sc );
  }
}

static void Wait( rtems_id id )
{
  rtems_status_code sc;

  sc = rtems_semaphore_obtain( id, RTEMS_WAIT, RTEMS_NO_TIMEOUT );
  T_quiet_rsc_success( sc );
}

static void Wakeup( rtems_id id )
{
  rtems_status_code sc;

  sc = rtems_semaphore_release( id );
  T_quiet_rsc_success( sc );
}

static bool BlockedForEvent( Context *ctx, Thread_Wait_flags flags )
{
  return flags == ( ctx->wait_class | THREAD_WAIT_STATE_BLOCKED );
}

static bool IntendsToBlockForEvent( Context *ctx, Thread_Wait_flags flags )
{
  return flags == ( ctx->wait_class | THREAD_WAIT_STATE_INTEND_TO_BLOCK );
}

static bool EventReadyAgain( Context *ctx, Thread_Wait_flags flags )
{
  return flags == ( ctx->wait_class | THREAD_WAIT_STATE_READY_AGAIN );
}

static bool IsSatisfiedFlags( Context *ctx )
{
  return EventReadyAgain(
    ctx,
    _Thread_Wait_flags_get( ctx->runner_thread )
  );
}

static bool IsSatisfiedState( Context *ctx )
{
  return ctx->runner_thread->current_state != ctx->waiting_for_event;
}

static void SendAction( Context *ctx )
{
  T_thread_switch_log *log;

  log = T_thread_switch_record_4( &ctx->thread_switch_log );
  T_quiet_null( log );
  ctx->send_status = ( *ctx->send )( ctx->receiver_id, ctx->events_to_send );
  log = T_thread_switch_record( NULL );
  T_quiet_eq_ptr( log, &ctx->thread_switch_log.log );
}

static void Send(
  Context *ctx,
  bool  ( *is_satsified )( Context * )
)
{
  SendAction( ctx );

  if ( ( *is_satsified )( ctx ) ) {
    ctx->receive_condition_state = RECEIVE_COND_SATSIFIED;
  } else {
    rtems_status_code sc;
    rtems_event_set pending;
    rtems_event_set missing;

    ctx->receive_condition_state = RECEIVE_COND_UNSATISFIED;
    pending = ( *ctx->get_pending_events )( ctx->runner_thread );
    ctx->unsatisfied_pending = pending;

    missing = INPUT_EVENTS & ~ctx->events_to_send;
    T_ne_u32( missing, 0 );
    sc = ( *ctx->send )( ctx->runner_id, missing );
    T_rsc_success( sc );

    pending = ( *ctx->get_pending_events )( ctx->runner_thread );
    T_eq_u32( pending, ctx->events_to_send & ~INPUT_EVENTS );
  }
}

static void Worker( rtems_task_argument arg )
{
  Context *ctx;

  ctx = (Context *) arg;

  while ( true ) {
    rtems_status_code   sc;
    rtems_task_priority prio;

    Wait( ctx->worker_wakeup );

    switch ( ctx->sender_prio ) {
      case PRIO_NORMAL:
      case PRIO_HIGH:
        prio = 0;
        sc = rtems_task_set_priority( RTEMS_SELF, ctx->sender_prio, &prio );
        T_rsc_success( sc );
        T_eq_u32( prio, PRIO_LOW );
        break;
      case PRIO_OTHER:
        sc = rtems_task_set_scheduler(
          RTEMS_SELF,
          ctx->other_sched,
          PRIO_LOW
        );
        T_rsc_success( sc );
        break;
      case PRIO_LOW:
        break;
    }

    Send( ctx, IsSatisfiedState );

    sc = rtems_task_set_scheduler(
      RTEMS_SELF,
      ctx->runner_sched,
      PRIO_HIGH
    );
    T_rsc_success( sc );

    Wakeup( ctx->runner_wakeup );
  }
}

static rtems_event_set GetPendingEvents( Context *ctx )
{
  rtems_event_set pending;
  rtems_status_code sc;

  sc = ( *ctx->receive )(
    RTEMS_PENDING_EVENTS,
    RTEMS_DEFAULT_OPTIONS,
    0,
    &pending
  );
  T_quiet_rsc_success( sc );

  return pending;
}

static void RtemsEventReqSendReceive_Cleanup( Context *ctx );

static void InterruptPrepare( void *arg )
{
  RtemsEventReqSendReceive_Cleanup( arg );
}

static void InterruptAction( void *arg )
{
  Context *ctx;

  ctx = arg;
  ctx->receive_status = ( *ctx->receive )(
    INPUT_EVENTS,
    ctx->receive_option_set,
    ctx->receive_timeout,
    &ctx->received_events
  );
  T_quiet_rsc_success( ctx->receive_status );
}

static void InterruptContinue( Context *ctx )
{
  rtems_status_code sc;

  sc = ( *ctx->send )( ctx->receiver_id, INPUT_EVENTS );
  T_quiet_rsc_success( sc );
}

static T_interrupt_test_state Interrupt( void *arg )
{
  Context                *ctx;
  Thread_Wait_flags       flags;
  T_interrupt_test_state  next_state;
  T_interrupt_test_state  previous_state;

  ctx = arg;
  flags = _Thread_Wait_flags_get( ctx->runner_thread );

  if ( IntendsToBlockForEvent( ctx, flags ) ) {
    next_state = T_INTERRUPT_TEST_DONE;
  } else if ( BlockedForEvent( ctx, flags ) ) {
    next_state = T_INTERRUPT_TEST_LATE;
  } else {
    next_state = T_INTERRUPT_TEST_EARLY;
  }

  previous_state = T_interrupt_test_change_state(
    T_INTERRUPT_TEST_ACTION,
    next_state
  );

  if ( previous_state == T_INTERRUPT_TEST_ACTION ) {
    if ( next_state == T_INTERRUPT_TEST_DONE ) {
      Send( ctx, IsSatisfiedFlags );
    } else {
      InterruptContinue( ctx );
    }
  }

  return next_state;
}

static const T_interrupt_test_config InterruptConfig = {
  .prepare = InterruptPrepare,
  .action = InterruptAction,
  .interrupt = Interrupt,
  .max_iteration_count = 10000
};

static void RtemsEventReqSendReceive_Pre_Id_Prepare(
  RtemsEventReqSendReceive_Context *ctx,
  RtemsEventReqSendReceive_Pre_Id   state
)
{
  switch ( state ) {
    case RtemsEventReqSendReceive_Pre_Id_InvId: {
      ctx->receiver_id = 0xffffffff;
      ctx->sender_type = SENDER_SELF;
      break;
    }

    case RtemsEventReqSendReceive_Pre_Id_Task: {
      ctx->receiver_id = ctx->runner_id;
      break;
    }

    case RtemsEventReqSendReceive_Pre_Id_NA:
      break;
  }
}

static void RtemsEventReqSendReceive_Pre_Send_Prepare(
  RtemsEventReqSendReceive_Context *ctx,
  RtemsEventReqSendReceive_Pre_Send state
)
{
  switch ( state ) {
    case RtemsEventReqSendReceive_Pre_Send_Zero: {
      ctx->events_to_send = 0;
      break;
    }

    case RtemsEventReqSendReceive_Pre_Send_Unrelated: {
      ctx->events_to_send = RTEMS_EVENT_7;
      break;
    }

    case RtemsEventReqSendReceive_Pre_Send_Any: {
      ctx->events_to_send = RTEMS_EVENT_5;
      break;
    }

    case RtemsEventReqSendReceive_Pre_Send_All: {
      ctx->events_to_send = RTEMS_EVENT_5 | RTEMS_EVENT_23;
      break;
    }

    case RtemsEventReqSendReceive_Pre_Send_MixedAny: {
      ctx->events_to_send = RTEMS_EVENT_5 | RTEMS_EVENT_7;
      break;
    }

    case RtemsEventReqSendReceive_Pre_Send_MixedAll: {
      ctx->events_to_send = RTEMS_EVENT_5 | RTEMS_EVENT_7 | RTEMS_EVENT_23;
      break;
    }

    case RtemsEventReqSendReceive_Pre_Send_NA:
      break;
  }
}

static void RtemsEventReqSendReceive_Pre_ReceiverState_Prepare(
  RtemsEventReqSendReceive_Context          *ctx,
  RtemsEventReqSendReceive_Pre_ReceiverState state
)
{
  switch ( state ) {
    case RtemsEventReqSendReceive_Pre_ReceiverState_NotWaiting: {
      ctx->sender_type = SENDER_SELF;
      ctx->receive_type = RECEIVE_SKIP;
      break;
    }

    case RtemsEventReqSendReceive_Pre_ReceiverState_Poll: {
      ctx->sender_type = SENDER_SELF;
      ctx->receive_type = RECEIVE_NORMAL;
      ctx->receive_option_set |= RTEMS_NO_WAIT;
      break;
    }

    case RtemsEventReqSendReceive_Pre_ReceiverState_Timeout: {
      ctx->sender_type = SENDER_SELF_2;
      ctx->receive_type = RECEIVE_NORMAL;
      ctx->receive_timeout = 1;
      break;
    }

    case RtemsEventReqSendReceive_Pre_ReceiverState_Lower: {
      ctx->sender_type = SENDER_WORKER;
      ctx->sender_prio = PRIO_HIGH;
      ctx->receive_type = RECEIVE_NORMAL;
      break;
    }

    case RtemsEventReqSendReceive_Pre_ReceiverState_Equal: {
      ctx->sender_type = SENDER_WORKER;
      ctx->sender_prio = PRIO_NORMAL;
      ctx->receive_type = RECEIVE_NORMAL;
      break;
    }

    case RtemsEventReqSendReceive_Pre_ReceiverState_Higher: {
      ctx->sender_type = SENDER_WORKER;
      ctx->sender_prio = PRIO_LOW;
      ctx->receive_type = RECEIVE_NORMAL;
      break;
    }

    case RtemsEventReqSendReceive_Pre_ReceiverState_Other: {
      ctx->sender_type = SENDER_WORKER;
      ctx->sender_prio = PRIO_OTHER;
      ctx->receive_type = RECEIVE_NORMAL;
      break;
    }

    case RtemsEventReqSendReceive_Pre_ReceiverState_Intend: {
      ctx->sender_type = SENDER_INTERRUPT;
      ctx->receive_type = RECEIVE_INTERRUPT;
      break;
    }

    case RtemsEventReqSendReceive_Pre_ReceiverState_NA:
      break;
  }
}

static void RtemsEventReqSendReceive_Pre_Satisfy_Prepare(
  RtemsEventReqSendReceive_Context    *ctx,
  RtemsEventReqSendReceive_Pre_Satisfy state
)
{
  switch ( state ) {
    case RtemsEventReqSendReceive_Pre_Satisfy_All: {
      ctx->receive_option_set |= RTEMS_EVENT_ALL;
      break;
    }

    case RtemsEventReqSendReceive_Pre_Satisfy_Any: {
      ctx->receive_option_set |= RTEMS_EVENT_ANY;
      break;
    }

    case RtemsEventReqSendReceive_Pre_Satisfy_NA:
      break;
  }
}

static void RtemsEventReqSendReceive_Post_SendStatus_Check(
  RtemsEventReqSendReceive_Context        *ctx,
  RtemsEventReqSendReceive_Post_SendStatus state
)
{
  switch ( state ) {
    case RtemsEventReqSendReceive_Post_SendStatus_Ok: {
      T_rsc_success( ctx->send_status );
      break;
    }

    case RtemsEventReqSendReceive_Post_SendStatus_InvId: {
      T_rsc( ctx->send_status, RTEMS_INVALID_ID );
      break;
    }

    case RtemsEventReqSendReceive_Post_SendStatus_NA:
      break;
  }
}

static void RtemsEventReqSendReceive_Post_ReceiveStatus_Check(
  RtemsEventReqSendReceive_Context           *ctx,
  RtemsEventReqSendReceive_Post_ReceiveStatus state
)
{
  switch ( state ) {
    case RtemsEventReqSendReceive_Post_ReceiveStatus_None: {
      T_eq_int( ctx->receive_condition_state, RECEIVE_COND_UNKNOWN );
      T_eq_u32( GetPendingEvents( ctx ), 0 );
      break;
    }

    case RtemsEventReqSendReceive_Post_ReceiveStatus_Pending: {
      T_eq_int( ctx->receive_condition_state, RECEIVE_COND_UNKNOWN );
      T_eq_u32( GetPendingEvents( ctx ), ctx->events_to_send );
      break;
    }

    case RtemsEventReqSendReceive_Post_ReceiveStatus_Timeout: {
      T_rsc( ctx->receive_status, RTEMS_TIMEOUT );
      T_eq_int( ctx->receive_condition_state, RECEIVE_COND_UNKNOWN );
      T_eq_u32( GetPendingEvents( ctx ), ctx->events_to_send );
      break;
    }

    case RtemsEventReqSendReceive_Post_ReceiveStatus_Satisfied: {
      T_rsc( ctx->receive_status, RTEMS_SUCCESSFUL );

      if ( ctx->receive_type != RECEIVE_NORMAL ) {
        T_eq_int( ctx->receive_condition_state, RECEIVE_COND_SATSIFIED );
      }

      T_eq_u32( ctx->received_events, ctx->events_to_send & INPUT_EVENTS );
      T_eq_u32( GetPendingEvents( ctx ), ctx->events_to_send & ~INPUT_EVENTS );
      break;
    }

    case RtemsEventReqSendReceive_Post_ReceiveStatus_Unsatisfied: {
      T_rsc( ctx->receive_status, RTEMS_UNSATISFIED );
      T_eq_int( ctx->receive_condition_state, RECEIVE_COND_UNKNOWN );
      T_eq_u32( GetPendingEvents( ctx ), ctx->events_to_send );
      break;
    }

    case RtemsEventReqSendReceive_Post_ReceiveStatus_Blocked: {
      T_eq_int( ctx->receive_condition_state, RECEIVE_COND_UNSATISFIED );
      T_eq_u32( ctx->unsatisfied_pending, ctx->events_to_send );
      break;
    }

    case RtemsEventReqSendReceive_Post_ReceiveStatus_NA:
      break;
  }
}

static void RtemsEventReqSendReceive_Post_SenderPreemption_Check(
  RtemsEventReqSendReceive_Context              *ctx,
  RtemsEventReqSendReceive_Post_SenderPreemption state
)
{
  T_thread_switch_log *log;
  size_t               i;

  log = &ctx->thread_switch_log.log;

  switch ( state ) {
    case RtemsEventReqSendReceive_Post_SenderPreemption_No: {
      /*
       * There may be a thread switch to the runner thread if the sender thread
       * was on another scheduler instance.
       */

      T_le_sz( log->recorded, 1 );

      for ( i = 0; i < log->recorded; ++i ) {
        T_ne_u32( log->events[ i ].executing, ctx->worker_id );
        T_eq_u32( log->events[ i ].heir, ctx->runner_id );
      }
      break;
    }

    case RtemsEventReqSendReceive_Post_SenderPreemption_Yes: {
      T_eq_sz( log->recorded, 2 );
      T_eq_u32( log->events[ 0 ].heir, ctx->runner_id );
      T_eq_u32( log->events[ 1 ].heir, ctx->worker_id );
      break;
    }

    case RtemsEventReqSendReceive_Post_SenderPreemption_NA:
      break;
  }
}

static void RtemsEventReqSendReceive_Setup(
  RtemsEventReqSendReceive_Context *ctx
)
{
  rtems_status_code   sc;
  rtems_task_priority prio;

  memset( ctx, 0, sizeof( *ctx ) );
  ctx->runner_thread = _Thread_Get_executing();
  ctx->runner_id = ctx->runner_thread->Object.id;
  ctx->worker_wakeup = CreateWakeupSema();
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

  sc = rtems_task_construct( &WorkerConfig, &ctx->worker_id );
  T_assert_rsc_success( sc );

  sc = rtems_task_start( ctx->worker_id, Worker, (rtems_task_argument) ctx );
  T_assert_rsc_success( sc );
}

static void RtemsEventReqSendReceive_Setup_Wrap( void *arg )
{
  RtemsEventReqSendReceive_Context *ctx;

  ctx = arg;
  ctx->in_action_loop = false;
  RtemsEventReqSendReceive_Setup( ctx );
}

static void RtemsEventReqSendReceive_Teardown(
  RtemsEventReqSendReceive_Context *ctx
)
{
  rtems_status_code   sc;
  rtems_task_priority prio;

  prio = 0;
  sc = rtems_task_set_priority( RTEMS_SELF, PRIO_HIGH, &prio );
  T_rsc_success( sc );
  T_eq_u32( prio, PRIO_NORMAL );

  if ( ctx->worker_id != 0 ) {
    sc = rtems_task_delete( ctx->worker_id );
    T_rsc_success( sc );
  }

  DeleteWakeupSema( ctx->worker_wakeup );
  DeleteWakeupSema( ctx->runner_wakeup );
}

static void RtemsEventReqSendReceive_Teardown_Wrap( void *arg )
{
  RtemsEventReqSendReceive_Context *ctx;

  ctx = arg;
  ctx->in_action_loop = false;
  RtemsEventReqSendReceive_Teardown( ctx );
}

static size_t RtemsEventReqSendReceive_Scope( void *arg, char *buf, size_t n )
{
  RtemsEventReqSendReceive_Context *ctx;

  ctx = arg;

  if ( ctx->in_action_loop ) {
    return T_get_scope( RtemsEventReqSendReceive_PreDesc, buf, n, ctx->pcs );
  }

  return 0;
}

static T_fixture RtemsEventReqSendReceive_Fixture = {
  .setup = RtemsEventReqSendReceive_Setup_Wrap,
  .stop = NULL,
  .teardown = RtemsEventReqSendReceive_Teardown_Wrap,
  .scope = RtemsEventReqSendReceive_Scope,
  .initial_context = &RtemsEventReqSendReceive_Instance
};

static const uint8_t RtemsEventReqSendReceive_TransitionMap[][ 3 ] = {
  {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_InvId,
    RtemsEventReqSendReceive_Post_ReceiveStatus_None,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Pending,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Pending,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Unsatisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Unsatisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Timeout,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Timeout,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Blocked,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Blocked,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Blocked,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Blocked,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Blocked,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Blocked,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
#if defined(RTEMS_SMP)
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Blocked,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
#else
    RtemsEventReqSendReceive_Post_SendStatus_NA,
    RtemsEventReqSendReceive_Post_ReceiveStatus_NA,
    RtemsEventReqSendReceive_Post_SenderPreemption_NA
#endif
  }, {
#if defined(RTEMS_SMP)
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Blocked,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
#else
    RtemsEventReqSendReceive_Post_SendStatus_NA,
    RtemsEventReqSendReceive_Post_ReceiveStatus_NA,
    RtemsEventReqSendReceive_Post_SenderPreemption_NA
#endif
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Blocked,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Blocked,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Pending,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Pending,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Unsatisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Unsatisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Timeout,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Timeout,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Blocked,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Blocked,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Blocked,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Blocked,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Blocked,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Blocked,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
#if defined(RTEMS_SMP)
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Blocked,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
#else
    RtemsEventReqSendReceive_Post_SendStatus_NA,
    RtemsEventReqSendReceive_Post_ReceiveStatus_NA,
    RtemsEventReqSendReceive_Post_SenderPreemption_NA
#endif
  }, {
#if defined(RTEMS_SMP)
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Blocked,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
#else
    RtemsEventReqSendReceive_Post_SendStatus_NA,
    RtemsEventReqSendReceive_Post_ReceiveStatus_NA,
    RtemsEventReqSendReceive_Post_SenderPreemption_NA
#endif
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Blocked,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Blocked,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Pending,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Pending,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Unsatisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Satisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Timeout,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Timeout,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Blocked,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Satisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Blocked,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Satisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Blocked,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Satisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_Yes
  }, {
#if defined(RTEMS_SMP)
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Blocked,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
#else
    RtemsEventReqSendReceive_Post_SendStatus_NA,
    RtemsEventReqSendReceive_Post_ReceiveStatus_NA,
    RtemsEventReqSendReceive_Post_SenderPreemption_NA
#endif
  }, {
#if defined(RTEMS_SMP)
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Satisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
#else
    RtemsEventReqSendReceive_Post_SendStatus_NA,
    RtemsEventReqSendReceive_Post_ReceiveStatus_NA,
    RtemsEventReqSendReceive_Post_SenderPreemption_NA
#endif
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Blocked,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Satisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Pending,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Pending,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Satisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Satisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Timeout,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Timeout,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Satisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Satisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Satisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Satisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Satisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_Yes
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Satisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_Yes
  }, {
#if defined(RTEMS_SMP)
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Satisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
#else
    RtemsEventReqSendReceive_Post_SendStatus_NA,
    RtemsEventReqSendReceive_Post_ReceiveStatus_NA,
    RtemsEventReqSendReceive_Post_SenderPreemption_NA
#endif
  }, {
#if defined(RTEMS_SMP)
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Satisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
#else
    RtemsEventReqSendReceive_Post_SendStatus_NA,
    RtemsEventReqSendReceive_Post_ReceiveStatus_NA,
    RtemsEventReqSendReceive_Post_SenderPreemption_NA
#endif
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Satisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Satisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Pending,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Pending,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Unsatisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Satisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Timeout,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Timeout,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Blocked,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Satisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Blocked,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Satisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Blocked,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Satisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_Yes
  }, {
#if defined(RTEMS_SMP)
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Blocked,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
#else
    RtemsEventReqSendReceive_Post_SendStatus_NA,
    RtemsEventReqSendReceive_Post_ReceiveStatus_NA,
    RtemsEventReqSendReceive_Post_SenderPreemption_NA
#endif
  }, {
#if defined(RTEMS_SMP)
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Satisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
#else
    RtemsEventReqSendReceive_Post_SendStatus_NA,
    RtemsEventReqSendReceive_Post_ReceiveStatus_NA,
    RtemsEventReqSendReceive_Post_SenderPreemption_NA
#endif
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Blocked,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Satisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Pending,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Pending,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Satisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Satisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Timeout,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Timeout,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Satisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Satisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Satisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Satisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Satisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_Yes
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Satisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_Yes
  }, {
#if defined(RTEMS_SMP)
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Satisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
#else
    RtemsEventReqSendReceive_Post_SendStatus_NA,
    RtemsEventReqSendReceive_Post_ReceiveStatus_NA,
    RtemsEventReqSendReceive_Post_SenderPreemption_NA
#endif
  }, {
#if defined(RTEMS_SMP)
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Satisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
#else
    RtemsEventReqSendReceive_Post_SendStatus_NA,
    RtemsEventReqSendReceive_Post_ReceiveStatus_NA,
    RtemsEventReqSendReceive_Post_SenderPreemption_NA
#endif
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Satisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }, {
    RtemsEventReqSendReceive_Post_SendStatus_Ok,
    RtemsEventReqSendReceive_Post_ReceiveStatus_Satisfied,
    RtemsEventReqSendReceive_Post_SenderPreemption_No
  }
};

static const struct {
  uint8_t Skip : 1;
  uint8_t Pre_Id_NA : 1;
  uint8_t Pre_Send_NA : 1;
  uint8_t Pre_ReceiverState_NA : 1;
  uint8_t Pre_Satisfy_NA : 1;
} RtemsEventReqSendReceive_TransitionInfo[] = {
  {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 1, 1, 1
  }, {
    0, 0, 0, 0, 1
  }, {
    0, 0, 0, 0, 1
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
#if defined(RTEMS_SMP)
    0, 0, 0, 0, 0
#else
    1, 0, 0, 0, 0
#endif
  }, {
#if defined(RTEMS_SMP)
    0, 0, 0, 0, 0
#else
    1, 0, 0, 0, 0
#endif
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 1
  }, {
    0, 0, 0, 0, 1
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
#if defined(RTEMS_SMP)
    0, 0, 0, 0, 0
#else
    1, 0, 0, 0, 0
#endif
  }, {
#if defined(RTEMS_SMP)
    0, 0, 0, 0, 0
#else
    1, 0, 0, 0, 0
#endif
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 1
  }, {
    0, 0, 0, 0, 1
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
#if defined(RTEMS_SMP)
    0, 0, 0, 0, 0
#else
    1, 0, 0, 0, 0
#endif
  }, {
#if defined(RTEMS_SMP)
    0, 0, 0, 0, 0
#else
    1, 0, 0, 0, 0
#endif
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 1
  }, {
    0, 0, 0, 0, 1
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
#if defined(RTEMS_SMP)
    0, 0, 0, 0, 0
#else
    1, 0, 0, 0, 0
#endif
  }, {
#if defined(RTEMS_SMP)
    0, 0, 0, 0, 0
#else
    1, 0, 0, 0, 0
#endif
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 1
  }, {
    0, 0, 0, 0, 1
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
#if defined(RTEMS_SMP)
    0, 0, 0, 0, 0
#else
    1, 0, 0, 0, 0
#endif
  }, {
#if defined(RTEMS_SMP)
    0, 0, 0, 0, 0
#else
    1, 0, 0, 0, 0
#endif
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 1
  }, {
    0, 0, 0, 0, 1
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }, {
#if defined(RTEMS_SMP)
    0, 0, 0, 0, 0
#else
    1, 0, 0, 0, 0
#endif
  }, {
#if defined(RTEMS_SMP)
    0, 0, 0, 0, 0
#else
    1, 0, 0, 0, 0
#endif
  }, {
    0, 0, 0, 0, 0
  }, {
    0, 0, 0, 0, 0
  }
};

static void RtemsEventReqSendReceive_Prepare(
  RtemsEventReqSendReceive_Context *ctx
)
{
  ctx->events_to_send = 0;
  ctx->send_status = RTEMS_INCORRECT_STATE;
  ctx->received_events = 0xffffffff;
  ctx->receive_option_set = 0;
  ctx->receive_timeout = RTEMS_NO_TIMEOUT;
  ctx->sender_type = SENDER_NONE;
  ctx->sender_prio = PRIO_NORMAL;
  ctx->receive_type = RECEIVE_SKIP;
  ctx->receive_condition_state = RECEIVE_COND_UNKNOWN;
  ctx->unsatisfied_pending = 0xffffffff;
  memset( &ctx->thread_switch_log, 0, sizeof( ctx->thread_switch_log ) );
  T_eq_u32( GetPendingEvents( ctx ), 0 );
  _Thread_Wait_flags_set( ctx->runner_thread, THREAD_WAIT_FLAGS_INITIAL );
}

static void RtemsEventReqSendReceive_Action(
  RtemsEventReqSendReceive_Context *ctx
)
{
  if ( ctx->sender_type == SENDER_SELF ) {
    SendAction( ctx );
  } else if ( ctx->sender_type == SENDER_WORKER ) {
    Wakeup( ctx->worker_wakeup );
  }

  if ( ctx->receive_type == RECEIVE_NORMAL ) {
    ctx->receive_status = ( *ctx->receive )(
      INPUT_EVENTS,
      ctx->receive_option_set,
      ctx->receive_timeout,
      &ctx->received_events
    );
  } else if ( ctx->receive_type == RECEIVE_INTERRUPT ) {
    T_interrupt_test_state state;

    state = T_interrupt_test( &InterruptConfig, ctx );
    T_eq_int( state, T_INTERRUPT_TEST_DONE );
  }

  if ( ctx->sender_type == SENDER_SELF_2 ) {
    SendAction( ctx );
  } else if ( ctx->sender_type == SENDER_WORKER ) {
    rtems_status_code   sc;
    rtems_task_priority prio;

    Wait( ctx->runner_wakeup );

    prio = 0;
    sc = rtems_task_set_priority( ctx->worker_id, PRIO_LOW, &prio );
    T_rsc_success( sc );
    T_eq_u32( prio, PRIO_HIGH );
  }
}

static void RtemsEventReqSendReceive_Cleanup(
  RtemsEventReqSendReceive_Context *ctx
)
{
  rtems_status_code sc;
  rtems_event_set events;

  events = 0;
  sc = ( *ctx->receive )(
    RTEMS_ALL_EVENTS,
    RTEMS_NO_WAIT | RTEMS_EVENT_ANY,
    0,
    &events
  );
  if ( sc == RTEMS_SUCCESSFUL ) {
    T_quiet_ne_u32( events, 0 );
  } else {
    T_quiet_rsc( sc, RTEMS_UNSATISFIED );
    T_quiet_eq_u32( events, 0 );
  }
}

static T_fixture_node RtemsEventReqSendReceive_Node;

void RtemsEventReqSendReceive_Run(
  rtems_status_code ( *send )( rtems_id, rtems_event_set ),
  rtems_status_code ( *receive )( rtems_event_set, rtems_option, rtems_interval, rtems_event_set * ),
  rtems_event_set (   *get_pending_events )( Thread_Control * ),
  unsigned int         wait_class,
  int                  waiting_for_event
)
{
  RtemsEventReqSendReceive_Context *ctx;
  size_t index;

  ctx = T_push_fixture(
    &RtemsEventReqSendReceive_Node,
    &RtemsEventReqSendReceive_Fixture
  );

  ctx->send = send;
  ctx->receive = receive;
  ctx->get_pending_events = get_pending_events;
  ctx->wait_class = wait_class;
  ctx->waiting_for_event = waiting_for_event;
  ctx->in_action_loop = true;
  index = 0;

  for (
    ctx->pcs[ 0 ] = RtemsEventReqSendReceive_Pre_Id_InvId;
    ctx->pcs[ 0 ] < RtemsEventReqSendReceive_Pre_Id_NA;
    ++ctx->pcs[ 0 ]
  ) {
    if ( RtemsEventReqSendReceive_TransitionInfo[ index ].Pre_Id_NA ) {
      ctx->pcs[ 0 ] = RtemsEventReqSendReceive_Pre_Id_NA;
      index += ( RtemsEventReqSendReceive_Pre_Id_NA - 1 )
        * RtemsEventReqSendReceive_Pre_Send_NA
        * RtemsEventReqSendReceive_Pre_ReceiverState_NA
        * RtemsEventReqSendReceive_Pre_Satisfy_NA;
    }

    for (
      ctx->pcs[ 1 ] = RtemsEventReqSendReceive_Pre_Send_Zero;
      ctx->pcs[ 1 ] < RtemsEventReqSendReceive_Pre_Send_NA;
      ++ctx->pcs[ 1 ]
    ) {
      if ( RtemsEventReqSendReceive_TransitionInfo[ index ].Pre_Send_NA ) {
        ctx->pcs[ 1 ] = RtemsEventReqSendReceive_Pre_Send_NA;
        index += ( RtemsEventReqSendReceive_Pre_Send_NA - 1 )
          * RtemsEventReqSendReceive_Pre_ReceiverState_NA
          * RtemsEventReqSendReceive_Pre_Satisfy_NA;
      }

      for (
        ctx->pcs[ 2 ] = RtemsEventReqSendReceive_Pre_ReceiverState_NotWaiting;
        ctx->pcs[ 2 ] < RtemsEventReqSendReceive_Pre_ReceiverState_NA;
        ++ctx->pcs[ 2 ]
      ) {
        if ( RtemsEventReqSendReceive_TransitionInfo[ index ].Pre_ReceiverState_NA ) {
          ctx->pcs[ 2 ] = RtemsEventReqSendReceive_Pre_ReceiverState_NA;
          index += ( RtemsEventReqSendReceive_Pre_ReceiverState_NA - 1 )
            * RtemsEventReqSendReceive_Pre_Satisfy_NA;
        }

        for (
          ctx->pcs[ 3 ] = RtemsEventReqSendReceive_Pre_Satisfy_All;
          ctx->pcs[ 3 ] < RtemsEventReqSendReceive_Pre_Satisfy_NA;
          ++ctx->pcs[ 3 ]
        ) {
          if ( RtemsEventReqSendReceive_TransitionInfo[ index ].Pre_Satisfy_NA ) {
            ctx->pcs[ 3 ] = RtemsEventReqSendReceive_Pre_Satisfy_NA;
            index += ( RtemsEventReqSendReceive_Pre_Satisfy_NA - 1 );
          }

          if ( RtemsEventReqSendReceive_TransitionInfo[ index ].Skip ) {
            ++index;
            continue;
          }

          RtemsEventReqSendReceive_Prepare( ctx );
          RtemsEventReqSendReceive_Pre_Id_Prepare( ctx, ctx->pcs[ 0 ] );
          RtemsEventReqSendReceive_Pre_Send_Prepare( ctx, ctx->pcs[ 1 ] );
          RtemsEventReqSendReceive_Pre_ReceiverState_Prepare(
            ctx,
            ctx->pcs[ 2 ]
          );
          RtemsEventReqSendReceive_Pre_Satisfy_Prepare( ctx, ctx->pcs[ 3 ] );
          RtemsEventReqSendReceive_Action( ctx );
          RtemsEventReqSendReceive_Post_SendStatus_Check(
            ctx,
            RtemsEventReqSendReceive_TransitionMap[ index ][ 0 ]
          );
          RtemsEventReqSendReceive_Post_ReceiveStatus_Check(
            ctx,
            RtemsEventReqSendReceive_TransitionMap[ index ][ 1 ]
          );
          RtemsEventReqSendReceive_Post_SenderPreemption_Check(
            ctx,
            RtemsEventReqSendReceive_TransitionMap[ index ][ 2 ]
          );
          RtemsEventReqSendReceive_Cleanup( ctx );
          ++index;
        }
      }
    }
  }

  T_pop_fixture();
}

/** @} */
