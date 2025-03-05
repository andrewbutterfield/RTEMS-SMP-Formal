# TestGen Code Structure

Lets start with `tr-event-mgr-model-5.c`

## Includes

```
#include "config.h"
#include <rtems/score/threadimpl.h>
#include "tr-event-mgr-model.h"
```

## Declarations
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

## Test Segments

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

## Runner

```
static void Runner( RtemsModelEventsMgr_Context *ctx )
{
  T_log( T_NORMAL, "Runner running" );
  TestSegment4( ctx );
  T_log( T_NORMAL, "Runner finished" );
}
```

## Worker

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