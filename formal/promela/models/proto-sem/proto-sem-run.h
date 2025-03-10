/* SPDX-License-Identifier: BSD-2-Clause */

static void Worker{0}( rtems_task_argument arg )
{{
  Context *ctx;
  rtems_event_set events;

  ctx = (Context *) arg;

  T_log( T_NORMAL, "Worker Running" );
  TestSegment4( ctx );
  T_log( T_NORMAL, "Worker finished" );

  // (void) rtems_task_suspend( RTEMS_SELF );
  // Ensure we hold no semaphores
  ReleaseTestSyncSema( ctx->worker_wakeup );
  ReleaseTestSyncSema( ctx->runner_wakeup );
  // Wait for events so we don't terminate
  rtems_event_receive( RTEMS_ALL_EVENTS, RTEMS_DEFAULT_OPTIONS, 0, &events );

}}

RTEMS_ALIGNED( RTEMS_TASK_STORAGE_ALIGNMENT ) static char WorkerStorage{0}[
  RTEMS_TASK_STORAGE_SIZE(
    MAX_TLS_SIZE + TEST_MINIMUM_STACK_SIZE,
    WORKER_ATTRIBUTES
  )
];

static const rtems_task_config WorkerConfig{0} = {{
  .name = rtems_build_name( 'W', 'O', 'R', 'K' ),
  .initial_priority = M_PRIO_LOW,
  .storage_area = WorkerStorage{0},
  .storage_size = sizeof( WorkerStorage{0} ),
  .maximum_thread_local_storage_size = MAX_TLS_SIZE,
  .initial_modes = RTEMS_DEFAULT_MODES,
  .attributes = WORKER_ATTRIBUTES
}};


static void RtemsModelProtoSem_Setup{0}(
  RtemsModelProtoSem_Context *ctx
)
{{
  rtems_status_code   sc;
  rtems_task_priority prio;

  T_log( T_NORMAL, "Runner Setup" );

  memset( ctx, 0, sizeof( *ctx ) );
  ctx->runner_thread = _Thread_Get_executing();
  ctx->runner_id = ctx->runner_thread->Object.id;

  T_log( T_NORMAL, "Creating Worker TestSync Semaphore" );
  ctx->worker_wakeup = CreateTestSyncSema( "WRKR" );
  T_log( T_NORMAL, "Creating Runner TestSync Semaphore" );
  ctx->runner_wakeup = CreateTestSyncSema( "RUNR" );

  sc = rtems_task_get_scheduler( RTEMS_SELF, &ctx->runner_sched );
  T_rsc_success( sc );

  #if defined(RTEMS_SMP)
  sc = rtems_scheduler_ident_by_processor( 1, &ctx->other_sched );
  T_rsc_success( sc );
  T_ne_u32( ctx->runner_sched, ctx->other_sched );
  #endif

  prio = 0;
  sc = rtems_task_set_priority( RTEMS_SELF, M_PRIO_NORMAL, &prio );
  T_rsc_success( sc );
  T_eq_u32( prio, M_PRIO_HIGH );

  sc = rtems_task_construct( &WorkerConfig{0}, &ctx->worker_id );
  T_log( T_NORMAL, "Construct Worker, sc = %x", sc );
  T_assert_rsc_success( sc );

  T_log( T_NORMAL, "Starting Worker..." );
  sc = rtems_task_start( ctx->worker_id, Worker{0}, (rtems_task_argument) ctx );
  T_log( T_NORMAL, "Started Worker, sc = %x", sc );
  T_assert_rsc_success( sc );
}}


static void RtemsModelProtoSem_Setup_Wrap{0}( void *arg )
{{
  RtemsModelProtoSem_Context *ctx;

  ctx = arg;
  RtemsModelProtoSem_Setup{0}( ctx );
}}


static RtemsModelProtoSem_Context RtemsModelProtoSem_Instance{0};

static T_fixture RtemsModelProtoSem_Fixture{0} = {{
  .setup = RtemsModelProtoSem_Setup_Wrap{0},
  .stop = NULL,
  .teardown = RtemsModelProtoSem_Teardown_Wrap,
  .scope = RtemsModelProtoSem_Scope,
  .initial_context = &RtemsModelProtoSem_Instance{0}
}};

static T_fixture_node RtemsModelProtoSem_Node{0};

void RtemsModelProtoSem_Run{0}(
  rtems_status_code ( *send )( rtems_id, rtems_event_set ),
  rtems_status_code ( *receive )( rtems_event_set, rtems_option, rtems_interval, rtems_event_set * ),
  rtems_event_set (   *get_pending_events )( Thread_Control * ),
  unsigned int         wait_class,
  int                  waiting_for_event
)
{{
  RtemsModelProtoSem_Context *ctx;

  T_set_verbosity( T_NORMAL );

  T_log( T_NORMAL, "Runner Invoked" );
  T_log( T_NORMAL, "Runner Wait Class: %d", wait_class );
  T_log( T_NORMAL, "Runner WaitForEvent: %d", waiting_for_event );

  T_log( T_NORMAL, "Pushing Test Fixture..." );


  ctx = T_push_fixture(
    &RtemsModelProtoSem_Node{0},
    &RtemsModelProtoSem_Fixture{0}
  );
  // This runs RtemsModelProtoSem_Fixture

  T_log( T_NORMAL, "Test Fixture Pushed" );


  ctx->send = send;
  ctx->receive = receive;
  ctx->get_pending_events = get_pending_events;
  ctx->wait_class = wait_class;
  ctx->waiting_for_event = waiting_for_event;

  ctx->this_test_number = {0};

  // RtemsModelProtoSem_Prepare( ctx );
  ctx->events_to_send = 0;
  ctx->send_status = RTEMS_INCORRECT_STATE;
  ctx->received_events = 0xffffffff;
  ctx->receive_option_set = 0;
  ctx->receive_timeout = RTEMS_NO_TIMEOUT;
  ctx->unsatisfied_pending = 0xffffffff;
  memset( &ctx->thread_switch_log, 0, sizeof( ctx->thread_switch_log ) );
  T_eq_u32( GetPending( ctx ), 0 );
  _Thread_Wait_flags_set( ctx->runner_thread, THREAD_WAIT_CLASS_PERIOD );

  TestSegment0( ctx );

  Runner( ctx );

  RtemsModelProtoSem_Cleanup( ctx );

  T_log( T_NORMAL, "Run Pop Fixture" );
  ShowWorkerSemaId( ctx->worker_id, ctx->worker_wakeup );
  T_pop_fixture();
  
}}

/** @}} */
