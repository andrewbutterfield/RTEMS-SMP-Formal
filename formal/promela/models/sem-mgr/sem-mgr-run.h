static void RtemsModelSemMgr_Setup{0}( void *arg )
{{
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
  sc = rtems_task_set_priority( RTEMS_SELF, M_PRIO_NORMAL, &prio );
  T_rsc_success( sc );
  T_eq_u32( prio, M_PRIO_HIGH );
  
  ctx->worker0_id = CreateTask( "WRK0", M_PRIO_NORMAL );
  T_log( T_NORMAL, "Created Worker 0");
  StartTask( ctx->worker0_id, Worker0, ctx );
  T_log( T_NORMAL, "Started Worker 0");

  ctx->worker1_id = CreateTask( "WRK1", M_PRIO_NORMAL );
  T_log( T_NORMAL, "Created Worker 1");
  StartTask( ctx->worker1_id, Worker1, ctx );
  T_log( T_NORMAL, "Started Worker 1");

}}

static RtemsModelSemMgr_Context RtemsModelSemMgr_Instance{0};

static T_fixture RtemsModelSemMgr_Fixture{0} = {{
  .setup = RtemsModelSemMgr_Setup{0},
  .stop = NULL,
  .teardown = RtemsModelSemMgr_Teardown,
  .scope = RtemsModelSemMgr_Scope,
  .initial_context = &RtemsModelSemMgr_Instance{0}
}};

static T_fixture_node RtemsModelSemMgr_Node{0};

void RtemsModelSemMgr_Run{0}()
{{
  RtemsModelSemMgr_Context *ctx;

  T_set_verbosity( T_NORMAL );
  T_log( T_NORMAL, "Pushing Test Fixture..." );

  ctx = T_push_fixture(
    &RtemsModelSemMgr_Node{0},
    &RtemsModelSemMgr_Fixture{0}
  );
  // This runs RtemsModelSemMgr_Fixture
  T_log( T_NORMAL, "Test Fixture Pushed" );

  ctx->this_test_number = {0};

  memset( &ctx->thread_switch_log, 0, sizeof( ctx->thread_switch_log ) );
  _Thread_Wait_flags_set( ctx->runner_thread, THREAD_WAIT_CLASS_PERIOD );
  
  TestSegment0( ctx );

  Runner( ctx );

  RtemsModelSemMgr_Cleanup( ctx );

  T_log( T_NORMAL, "Run Pop Fixture" );
  T_pop_fixture();
}}

/** @}} */
