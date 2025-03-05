# TestGen Code Structure

Lets start with `tr-event-mgr-model-5.c`

## XXX-pre.h

### Includes

```
#include "config.h"
#include <rtems/score/threadimpl.h>
#include "tr-event-mgr-model.h"
```

## Generated Code

### Declarations
Declarations ensure, from model, as well as:

```
// @@@ 0 DECL byte sendrc 0
static rtems_status_code sendrc = 0;
static rtems_status_code recrc = 0;
// @@@ 0 DCLARRAY EvtSet pending TASK_MAX
static rtems_event_set pending[TASK_MAX];
static rtems_event_set recout[TASK_MAX];
static rtems_id test_sync_sema[SEMA_MAX];
```

### Test Segments

```
static void TestSegment0( Context* ctx ){
T_log(T_NORMAL,"@@@ 0 INIT");
  initialise_pending( pending, TASK_MAX );
  initialise_semaphore( 0, ctx->runner_wakeup, test_sync_sema );
  initialise_semaphore( 1, ctx->worker_wakeup, test_sync_sema )
}
```

```
static void TestSegment1( Context* ctx ) {
  /* SWITCH[1] ReleaseTestSyncSema of proc1 (sometime) after proc0 */
  /* SWITCH[2] Suspension of proc1 in favour of proc2 */
  /* SWITCH[8] ReleaseTestSyncSema of proc1 (sometime) after proc3 */
  /* SWITCH[9] Suspension of proc1 in favour of proc2 */
}
```

```
static void TestSegment2( Context* ctx ) {
  /* SWITCH[2] ReleaseTestSyncSema of proc2 (sometime) after proc1 */
  /* SWITCH[3] Suspension of proc2 in favour of proc3 */
  /* SWITCH[9] ReleaseTestSyncSema of proc2 (sometime) after proc1 */
}
```

```
static void TestSegment3( Context* ctx ) {
  /* SWITCH[3] ReleaseTestSyncSema of proc3 (sometime) after proc2 */
  // @@@ 3 DECL byte sc
  rtems_status_code sc;
  // @@@ 3 DECL byte prio
  rtems_task_priority prio;
  /* SWITCH[4] Suspension of proc3 in favour of proc4 */
  /* SWITCH[5] ReleaseTestSyncSema of proc3 (sometime) after proc4 */
  T_log(T_NORMAL,"@@@ 3 TASK Worker");
  checkTaskIs( ctx->worker_id );
  .... and the all the Runner behaviour
```

```
static void TestSegment4( Context* ctx ) {
  /* SWITCH[4] ReleaseTestSyncSema of proc4 (sometime) after proc3 */
  // @@@ 4 DECL byte sc
  rtems_status_code sc;
  // @@@ 4 DECL byte prio
  rtems_task_priority prio;
  T_log(T_NORMAL,"@@@ 4 TASK Runner");
  checkTaskIs( ctx->runner_id );
  ... and all the Worker1 behaviour
```

## XXX-post.h

### Runner

```
static void Runner( RtemsModelEventsMgr_Context *ctx )
{
  T_log( T_NORMAL, "Runner running" );
  TestSegment4( ctx );
  T_log( T_NORMAL, "Runner finished" );
}
```

## XXX-run.h

Parameterised by a scenario number

### Worker

```
static void Worker5( rtems_task_argument arg )
{
  Context *ctx;
  rtems_event_set events;

  ctx = (Context *) arg;

  T_log( T_NORMAL, "Worker Running" );
  TestSegment3( ctx );
  T_log( T_NORMAL, "Worker finished" );

  // (void) rtems_task_suspend( RTEMS_SELF );
  // Ensure we hold no semaphores
  ReleaseTestSyncSema( ctx->worker_wakeup );
  ReleaseTestSyncSema( ctx->runner_wakeup );
  // Wait for events so we don't terminate
  rtems_event_receive( RTEMS_ALL_EVENTS, RTEMS_DEFAULT_OPTIONS, 0, &events );
}
```

Then we see

```
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


static void RtemsModelEventsMgr_Setup{0}(
  RtemsModelEventsMgr_Context *ctx
)
{{
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


static void RtemsModelEventsMgr_Setup_Wrap{0}( void *arg )
{{
  RtemsModelEventsMgr_Context *ctx;

  ctx = arg;
  RtemsModelEventsMgr_Setup{0}( ctx );
}}


static RtemsModelEventsMgr_Context RtemsModelEventsMgr_Instance{0};

static T_fixture RtemsModelEventsMgr_Fixture{0} = {{
  .setup = RtemsModelEventsMgr_Setup_Wrap{0},
  .stop = NULL,
  .teardown = RtemsModelEventsMgr_Teardown_Wrap,
  .scope = RtemsModelEventsMgr_Scope,
  .initial_context = &RtemsModelEventsMgr_Instance{0}
}};

static T_fixture_node RtemsModelEventsMgr_Node{0};

void RtemsModelEventsMgr_Run{0}(
   ctx = T_push_fixture(
    &RtemsModelEventsMgr_Node{0},
    &RtemsModelEventsMgr_Fixture{0}
   TestSegment0( ctx );
  Runner( ctx );
  RtemsModelEventsMgr_Cleanup( ctx );
  T_log( T_NORMAL, "Run Pop Fixture" );
  ShowWorkerSemaId( ctx->worker_id, ctx->worker_wakeup );
  T_pop_fixture();  
}}
```


