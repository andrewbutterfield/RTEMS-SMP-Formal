# TestGen Code Architecture

## Abstract Code Flow

Here we use a terse abstraction of code using Concurrent Kleene Algebra (CKA)
to make it easier to understand and compare.

### Code Abstractions

We abstract away from:

- the  "run number" <N>
- fixture push and pop

| Abstract | Concrete |
| --- | --- |
| Runner | The RTEMS Test Runner Task |
| Worker<n> | The RTEMS Test Worker Task(s) |
| Run | `X_Run(context)` |
| Setup | `T_push_fixture()` a.k.a. `X_Setup(X_Context)`  |
| ThreadSetup | thread switch logging and wait flags  |
| Cleanup | `X_Cleanup(ctx)` |
| Teardown | `T_pop_fixture()` a.k.a. `X_Teardown(X_Context)`  |
| RunRest | rest of Run once worker is started |
| MkTSS | `CreateTestSyncSema(tss)` |
| RelTSS | `ReleaseTestSyncSema(tss)` |
| DelTSS | `DeleteTestSyncSema(tss` |
| DelQ | `rtems_message_queue_delete(qid)` |
| ShowWSemaId | `ShowWorkerSemaId(id,wkup )
| GetSched | `rtems_task_get_scheduler(tid,scheduler)` |
| SchedIdProc | `rtems_scheduler_ident_by_processor(cpu,scheduler)` |
| SetPrio | `rtems_task_set_priority(id,newprio,oldprio)` |
| ConsTask | `rtems_task_construct(config,tid)` |
| StartTask | `rtems_task_start(id,code,arg)` |
| CreateTask | `rtems_task_create(nm,prio,tid)` (ignoring attr) |
| Hang | `rtems_event_receive(ALL_EVENTS, WAIT, 0, _)` |
| TstRcv | `rtems_event_receive(ALL_EVENTS, NOWAIT+ANY, 0, _)` |
| DelTask | `rtems_task_delete(tid)` |
| using[N] | true if worker[N] is used in scenario |
| --- | --- |


### Abstract Prototype Semantics

```
PS_runner() = TestSegment3()
```

```
Worker() 
  = TestSegment4(); RelTSS(worktss); RelTSS(runtss); Hang()
```

```
Run([worker]) = Setup(worker) ; ( RunRest() + worker() )
```

```
Setup(worker)
 = MkTSS(worktss) ; MkTSS(runtss) ; GetSched(self,runsched) ;
   (if RTEMS_SMP then SchedIdProc(1,worksched) else Skip) ;
   SetPrio(self,NORMAL); 
   ConsTask(workconfig,workid); StartTask(workid,worker)
```

```
RunRest() 
  = ThreadSetup(); TestSegment0(); PS_runner();
    Cleanup(); ShowWSemaId(workid,workwkup ); TearDown();  
```

```
Cleanup () = TstRcv() ; reports outcome (success/unsat)
```

```
TearDown()
  = SetPrio(self,HIGH) ; 
    (if using1 then DelTask(workid) else Skip) ; 
    DelTSS(worktss) ; DelTSS(runtss)
```



### Abstract Message Manager

```
MM_runner() = TestSegment3()
```

```
Worker1() = TestSegment4(); Hang()
```

```
Worker2() = TestSegment5(); Hang()
```

```
Run([worker1,worker2]) 
  = Setup([worker1,worker2]) ; ( RunRest() + worker1() + worker2() )
```

```
Setup([worker1,worker2])
 = MkTSS(work1tss) ; MkTSS(work2tss) ; MkTSS(runtss) ; 
   GetSched(self,runsched) ;
   (if RTEMS_SMP then SchedIdProc(1,worksched) else Skip) ;
   SetPrio(self,NORMAL); 
   CreateTask(WRKR,NORMAL,work1id);  StartTask(work1id,worker1) ;
   CreateTask(WRKR,NORMAL,work2id);  StartTask(work2id,worker2)
```

```
RunRest() 
  = ThreadSetup(); TestSegment0(); MM_runner();
    Cleanup(); ShowWSemaId(workid,workwkup ); TearDown();  
```

```
Cleanup () = DelQ() ; reports outcome (success/unsat)
```

```
TearDown()
  = SetPrio(self,HIGH) ; 
    (if using1 then DelTask(work1id) else Skip) ; DelTSS(work1tss) ;
    (if using2 then DelTask(work2id) else Skip) ; DelTSS(work2tss) ; DelTSS(runtss)
```



### Abstract Event Manager

```
EM_runner() = TestSegment4()
```

```
Worker() 
  = TestSegment3(); RelTSS(worktss); RelTSS(runtss); Hang()
```

```
Run([worker]) = Setup(worker) ; ( RunRest() + worker() )
```

```
Setup(worker)
 = MkTSS(worktss) ; MkTSS(runtss) ; GetSched(self,runsched) ;
   (if RTEMS_SMP then SchedIdProc(1,worksched) else Skip) ;
   SetPrio(self,NORMAL); 
   ConsTask(workconfig,workid); StartTask(workid,worker)
```

```
RunRest() 
  = ThreadSetup(); TestSegment0(); EM_runner();
    Cleanup(); ShowWSemaId(workid,workwkup ); TearDown();  
```

```
Cleanup () = TstRcv() ; reports outcome (success/unsat)
```

```
TearDown()
  = SetPrio(self,HIGH) ; 
    (if using1 then DelTask(workid) else Skip) ; 
    DelTSS(worktss) ; DelTSS(runtss)
```

### Abstract TEMPLATE

```
_runner() = TestSegmentR()
```

```
Worker[W]() 
  = TestSegment[f(W)](); RelTSS(worktss); RelTSS(runtss); Hang()
```

```
Run([worker]) = Setup(worker) ; ( RunRest() + worker() )
```

```
Setup(worker)
 = MkTSS(worktss) ; MkTSS(runtss) ; GetSched(self,runsched) ;
   (if RTEMS_SMP then SchedIdProc(1,worksched) else Skip) ;
   SetPrio(self,NORMAL); 
   ConsTask(workconfig,workid); StartTask(workid,worker)
```

```
RunRest() 
  = ThreadSetup(); TestSegment0(); _runner();
    Cleanup(); ShowWSemaId(workid,workwkup ); TearDown();  
```

```
Cleanup () = TstRcv() ; reports outcome (success/unsat)
```

```
TearDown()
  = SetPrio(self,HIGH) ; 
    (if using1 then DelTask(workid) else Skip) ; 
    DelTSS(worktss) ; DelTSS(runtss)
```

## Code Structure

We use the `event-mgr` model as our initial example

We assume that the RTEMS root directory is `rtems`
with sources in `rtems/src/rtems` and `rtems/src/rsb`.

The test executable is `ts-model-0.exe`, 
found in `rtems/src/rtems/build/sparc/leon3/testsuites/validation/`.

In `rtems/src/rtems/testsuites/validation/` we find:

Top-Level Sources:

```
ts-model-0.c
tx-support.h
tx-support.c
ts-default.h
ts-config.h
tx-model-0.h
tx-model-0.c
```
(versions of these can be be found in `models/toplevel`)

For each API model XXX, (in `models/XXX`)

```
tc-XXX-model.c 
tr-XXX-model.h
tr-XXX-model.c
tr-XXX-model-0.c
...
tr-XXX-model-N.c
```



### validation/ts-model-0.c

#### Includes 

```c
#include "config.h"
#include <rtems/test.h>
#include "ts-default.h" // at the end of the file !!!
```
#### Declares:

```c
const char rtems_test_name[] = "TestsuitesModel0";
#define CONFIGURE_MAXIMUM_PROCESSORS 5
```

### validation/ts-default.h

#### Includes

```c
#include <bsp.h>
#include <rtems/bspIo.h>
#include <rtems/chain.h>
#include <rtems/test-info.h>
#include <rtems/testopts.h>
#include <rtems/test.h>
#include <rtems/test-scheduler.h>
#include "ts-config.h"
#include "tx-support.h"
#include <rtems/score/scheduleredfsmp.h> // ifdef RTEMS_SMP
#include <rtems/scheduler.h> // in middle of file
#include <rtems/confdefs.h> // at the end of the file !!
```

#### Declares

A ton of stuff, some of it conditional on environment variables.
It also defines C functions, most notably (compressed):

```c
static void Runner(rtems_task_argument arg)
{  int exit_code;
  test_runner_argument = arg;
  (void) rtems_task_mode(RTEMS_ASR,RTEMS_ASR_MASK,&test_runner_initial_modes);
  (void) rtems_task_set_priority
                      (RTEMS_SELF,PRIO_DEFAULT,&test_runner_initial_priority);
  rtems_chain_initialize
      (&free_task_storage,task_storage,RTEMS_ARRAY_SIZE(task_storage)
       ,sizeof(task_storage[0]));
  rtems_test_begin(rtems_test_name,TEST_STATE);
  T_register();
  exit_code = T_main(&test_config);
  if (exit_code == 0) {rtems_test_end( rtems_test_name );}
  rtems_fatal( RTEMS_FATAL_SOURCE_EXIT, (uint32_t) exit_code );
}
```

Clearly our declarations of `Runner` override that above (ts-*default*.h).


### validation/ts-config.h

#### Includes

```c
#include <rtems.h>
```

#### Declares

```c
#define TEST_MICROSECONDS_PER_TICK 1000
#define TEST_RUNNER_NAME rtems_build_name( 'R', 'U', 'N', ' ' )
#define TEST_RUNNER_ARGUMENT 123456789
#define TEST_RUNNER_INITIAL_MODES RTEMS_NO_ASR
#define TEST_SCHEDULER_A_NAME rtems_build_name( 'A', ' ', ' ', ' ' )
#define TEST_SCHEDULER_B_NAME rtems_build_name( 'B', ' ', ' ', ' ' )
#define TEST_SCHEDULER_C_NAME rtems_build_name( 'C', ' ', ' ', ' ' )
#define TEST_SCHEDULER_D_NAME rtems_build_name( 'D', ' ', ' ', ' ' )
#if defined( __OPTIMIZE__ ) && !defined( RTEMS_GCOV_COVERAGE )
#define TEST_BASE_STACK_SIZE RTEMS_MINIMUM_STACK_SIZE
#else
#define TEST_BASE_STACK_SIZE ( 4 * RTEMS_MINIMUM_STACK_SIZE )
#endif
#define TEST_MAXIMUM_TLS_SIZE RTEMS_ALIGN_UP(64,RTEMS_TASK_STORAGE_ALIGNMENT )
#define TEST_MINIMUM_STACK_SIZE \
  ( TEST_BASE_STACK_SIZE + CPU_STACK_ALIGNMENT )
#define TEST_IDLE_STACK_SIZE \
  ( TEST_BASE_STACK_SIZE + 2 * CPU_STACK_ALIGNMENT )
#define TEST_INTERRUPT_STACK_SIZE \
  ( TEST_BASE_STACK_SIZE + 4 * CPU_INTERRUPT_STACK_ALIGNMENT )
#define TEST_MAXIMUM_BARRIERS 7
#define TEST_MAXIMUM_MESSAGE_QUEUES 3
#define TEST_MAXIMUM_PARTITIONS 4
#define TEST_MAXIMUM_PERIODS 2
#define TEST_MAXIMUM_SEMAPHORES 7
#define TEST_MAXIMUM_TASKS 32
#define TEST_MAXIMUM_TIMERS 10
#define TEST_MAXIMUM_USER_EXTENSIONS 5
#define TEST_TICKS_PER_TIMESLICE 2
void *test_task_stack_allocate( size_t size );
void test_task_stack_deallocate( void *stack );
void *test_idle_task_stack_allocate( uint32_t cpu_index, size_t *size );
extern rtems_task_argument test_runner_argument;
extern rtems_task_priority test_runner_initial_priority;
extern rtems_mode test_runner_initial_modes;
```


### validation/tx-support.h

#### Includes

```c
#include <rtems.h>
#include <rtems/irq-extension.h>
#include <rtems/score/atomic.h>
#include <rtems/score/threadq.h>
```

#### Declares

Lots of stuff, we just show an extract

```c
typedef enum {PRIO_PSEUDO_ISR,...,PRIO_ULTRA_LOW} Priority;
#define PRIO_DEFAULT 1
#define PRIO_INVALID 0xfffffffe
/**
 * @brief This constants represents a priority which is close to the priority
 *   of the idle thread.
 *
 * It may be used for the runner thread together with PRIO_FLEXIBLE for worker
 * threads.
 */
#define PRIO_NEARLY_IDLE 126
/**
 * @brief This constants represents a priority with a wider range of higher and
 *   lower priorities around it.
 *
 * It may be used for the worker threads together with PRIO_NEARLY_IDLE for the
 * runner thread.
 */
#define PRIO_FLEXIBLE 64
#define INVALID_ID 0xfffffffd
#define CreateTask( name, priority ) \
  DoCreateTask( \
    rtems_build_name( name[ 0 ], name[ 1 ], name[ 2 ], name[ 3 ] ), \
    priority \
  )
#define SCHEDULER_A_ID 0xf010001
rtems_id DoCreateTask( rtems_name name, rtems_task_priority priority );
void StartTask( rtems_id id, rtems_task_entry entry, void *arg );
void DeleteTask( rtems_id id );
void SuspendTask( rtems_id id );
void SuspendSelf( void );
void ResumeTask( rtems_id id );
rtems_event_set QueryPendingEvents( void );
rtems_task_priority GetPriority( rtems_id id );
rtems_task_priority SetPriority( rtems_id id, rtems_task_priority priority );
void SetScheduler(
  rtems_id            task_id,
  rtems_id            scheduler_id,
  rtems_task_priority priority
);
rtems_id CreateMutex( void );
void ObtainMutex( rtems_id id );
void RestoreRunnerPriority( void );
struct _Thread_Control;
struct _Thread_Control *GetThread( rtems_id id );
struct _Thread_Control *GetExecuting( void );
void WaitForHeir( uint32_t cpu_index, rtems_id task_id );
typedef enum {
  TASK_TIMER_INVALID,
  TASK_TIMER_INACTIVE,
  TASK_TIMER_TICKS,
  TASK_TIMER_REALTIME,
  TASK_TIMER_MONOTONIC
} TaskTimerState;
void ClockTick( void );
#if defined(RTEMS_SMP)
bool TicketLockIsAvailable( const SMP_ticket_lock_Control *lock );
void TicketLockWaitForOwned( const SMP_ticket_lock_Control *lock );
void *IdleBody( uintptr_t ignored );
/**
 * @brief This task configurations may be used to construct a task during
 *   tests.
 *
 * Only one task shall use this configuration at a time, otherwise two tasks
 * would share a stack.
 */
extern const rtems_task_config DefaultTaskConfig;
```

Implemented in `tx-support.c`.


### models/common/tx-model-0.h

#### Includes

```C
#include <rtems.h>
#include <rtems/score/thread.h>
#include <rtems/test.h>
```

#### Declares

```c
typedef enum {M_PRIO_HIGH..OTHER} Priorities;
rtems_id CreateTestSyncSema( char * name );
void DeleteTestSyncSema( rtems_id id );
void ObtainTestSyncSema( rtems_id id );
void ReleaseTestSyncSema( rtems_id id ) ;
void initialise_id ( rtems_id * id );
rtems_option mergeopts( bool wait, bool wantall );
rtems_interval getTimeout( int timeout ) ;
rtems_id idNull( rtems_id queue_id, bool passedid ) ;
void checkTaskIs( rtems_id expected_id ) ;
void initialise_semaphore( int sema_no,
                           rtems_id semaphore_id, 
                           rtems_id semaphore[] );
void ShowRunnerSemaId( rtems_id run_wake ) ;
void ShowWorkerSemaId( int worker_num, rtems_id work_wake ) ;
```

Implemented in `tx-model-0.c`.

### models/XXX/tc-XXX-pre.h

####  Includes

```c
#include <rtems/rtems/eventimpl.h>
#include <rtems/rtems/tasksdata.h>
#include <rtems/score/statesimpl.h>
#include <rtems/score/threadimpl.h>
#include "tr-event-mgr-model.h"
#include <rtems/test.h>
```


#### Defines

This defines C functions that wrap API calls 

```c
static rtems_status_code EventSend(...)
  { return rtems_event_send( id, event_in ); }

static rtems_status_code EventReceive(...)
{ return rtems_event_receive( event_in, option_set, ticks, event_out ); }

static rtems_event_set GetPendingEvents( Thread_Control *thread )
{ RTEMS_API_Control *api;
  api = thread->API_Extensions[ THREAD_API_RTEMS ];
  return api->Event.pending_events;
}

static rtems_status_code EventSystemSend(...)
{ return rtems_event_system_send( id, event_in ); }

static rtems_status_code EventSystemReceive(...)
{ return rtems_event_system_receive(event_in,...,event_out); }

static rtems_event_set GetPendingSystemEvents( Thread_Control *thread )
{ RTEMS_API_Control *api;
  api = thread->API_Extensions[ THREAD_API_RTEMS ];
  return api->System_event.pending_events;
}
```


### models/XXX/tc-XXX-run.h

Defines test cases 
(usually just one, 
 but event manager has regular and system variants)
 
```c
T_TEST_CASE( RtemsModelEventsMgr{0} )
{{
  RtemsModelEventsMgr_Run{0}(
    EventSend,
    EventReceive,
    GetPendingEvents,
    THREAD_WAIT_CLASS_EVENT,
    STATES_WAITING_FOR_EVENT
  );
}}
T_TEST_CASE( RtemsModelSystemEventsMgr{0} )
{{
  RtemsModelEventsMgr_Run{0}(
    EventSystemSend,
    EventSystemReceive,
    GetPendingSystemEvents,
    THREAD_WAIT_CLASS_SYSTEM_EVENT,
    STATES_WAITING_FOR_SYSTEM_EVENT
  );
}}```


### models/XXX/tc-XXX-post.h

Very simple:

```c
/** @} */
```


### models/XXX/XXX-model.h

#### Includes

```C
#include "tx-model-0.h"
#include <rtems.h>
#include <rtems/score/thread.h>
#include <rtems/test.h>
#include "ts-config.h"
```

### models/XXX/XXX-pre.h

#### Includes

```c
#include "config.h"
#include <rtems/score/threadimpl.h>
#include "tr-event-mgr-model.h"
```

### Generated Code 

### models/XXX/tc-XXX-model.c

#### Includes

```c
#include <rtems/rtems/eventimpl.h>
#include <rtems/rtems/tasksdata.h>
#include <rtems/score/statesimpl.h>
#include <rtems/score/threadimpl.h>
#include "tr-event-mgr-model.h"
#include <rtems/test.h>
```

#### Defines

Contents of `tc-XXX-pre.h` plus, for I=0..N :

```c
T_TEST_CASE( RtemsModelEventsMgrI )
{  RtemsModelEventsMgr_Run0(
    EventSend,
    EventReceive,
    GetPendingEvents,
    THREAD_WAIT_CLASS_EVENT,
    STATES_WAITING_FOR_EVENT
  );
}
T_TEST_CASE( RtemsModelSystemEventsMgr0 )
{ RtemsModelEventsMgr_Run0(
    EventSystemSend,
    EventSystemReceive,
    GetPendingSystemEvents,
    THREAD_WAIT_CLASS_SYSTEM_EVENT,
    STATES_WAITING_FOR_SYSTEM_EVENT
  );
}```



### models/XXX/tr-XXX-model-N.c


#### Declarations

Declarations ensure, from model, as well as:

```c
// @@@ 0 DECL byte sendrc 0
static rtems_status_code sendrc = 0;
static rtems_status_code recrc = 0;
// @@@ 0 DCLARRAY EvtSet pending TASK_MAX
static rtems_event_set pending[TASK_MAX];
static rtems_event_set recout[TASK_MAX];
static rtems_id test_sync_sema[SEMA_MAX];
```

#### Test Segments

```C 
static void TestSegment0( Context* ctx ){
T_log(T_NORMAL,"@@@ 0 INIT");
  initialise_pending( pending, TASK_MAX );
  initialise_semaphore( 0, ctx->runner_wakeup, test_sync_sema );
  initialise_semaphore( 1, ctx->worker_wakeup, test_sync_sema )
}
```

```c
static void TestSegment1( Context* ctx ) {
  /* SWITCH[1] ReleaseTestSyncSema of proc1 (sometime) after proc0 */
  /* SWITCH[2] Suspension of proc1 in favour of proc2 */
  /* SWITCH[8] ReleaseTestSyncSema of proc1 (sometime) after proc3 */
  /* SWITCH[9] Suspension of proc1 in favour of proc2 */
}
```

```c
static void TestSegment2( Context* ctx ) {
  /* SWITCH[2] ReleaseTestSyncSema of proc2 (sometime) after proc1 */
  /* SWITCH[3] Suspension of proc2 in favour of proc3 */
  /* SWITCH[9] ReleaseTestSyncSema of proc2 (sometime) after proc1 */
}
```

```c
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

```c
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

### models/XXX/XXX-post.h

#### Runner

```c
static void Runner( RtemsModelEventsMgr_Context *ctx )
{
  T_log( T_NORMAL, "Runner running" );
  TestSegment4( ctx );
  T_log( T_NORMAL, "Runner finished" );
}
```

### models/XXX/XXX-run.h

Parameterised by a scenario number

#### Worker

```c
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

```c
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

void RtemsModelEventsMgr_Run{0}(ctx)
   ctx = T_push_fixture(
    &RtemsModelEventsMgr_Node{0},
    &RtemsModelEventsMgr_Fixture{0})
   TestSegment0( ctx );
  Runner( ctx );
  RtemsModelEventsMgr_Cleanup( ctx );
  T_log( T_NORMAL, "Run Pop Fixture" );
  ShowWorkerSemaId( ctx->worker_id, ctx->worker_wakeup );
  T_pop_fixture();  
}}
```

## Code Flow

### Test Suite (`ts-`)

We start by looking at `validation/ts-model-0.c`.
Basically this just pulls in `validation/ts-default.h`.
There is no sign of a main program here.

### Test Case (`tc-`)

If we look at `models/XXX/tc-XXX-model.c` we find all the `T_TEST_CASE`s,
which invoke `RtemsModelXXX_RunN()`.
This looks like the starting point for a test.

### Test Run (`tr-`)

Looking in `models/XXX/tr-XXX-model.c` we find model-specific C code,
as well as the following:

```c
static void RtemsModelEventsMgr_Teardown()
void RtemsModelEventsMgr_Teardown_Wrap()
size_t RtemsModelEventsMgr_Scope()
void RtemsModelEventsMgr_Cleanup()
```

Looking at `models/XXX/gen/tr-XXX-model-<N>.c` we find test segments,
runner and worker code and:

```c
RTEMS_ALIGNED( RTEMS_TASK_STORAGE_ALIGNMENT ) static char WorkerStorage<N>[..];
static const rtems_task_config WorkerConfig<N> = {..}
static void RtemsModelEventsMgr_Setup<N>()
static void RtemsModelEventsMgr_Setup_Wrap<N>()
static RtemsModelEventsMgr_Context RtemsModelEventsMgr_Instance<N>;
static T_fixture RtemsModelEventsMgr_Fixture<N> = {..}
static T_fixture_node RtemsModelEventsMgr_Node<N>;
void RtemsModelEventsMgr_Run<N>(..)
```

### Test Fixture

####  Fixture Declaration

From `rtems/src/rtems/cpukit/include/rtems/test.h` (extract):

```c
typedef struct T_fixture {
	void (*setup)(void *);
	void (*stop)(void *);
	void (*teardown)(void *);
	size_t (*scope)(void *, char *, size_t);
	void *initial_context;
} T_fixture;

typedef struct T_fixture_node {
	struct T_fixture_node *next;
	struct T_fixture_node *previous;
	const T_fixture *fixture;
	void *context;
	unsigned int next_planned_steps;
	unsigned int next_steps;
	unsigned int failures;
} T_fixture_node
```

####  Fixture Code

From `rtems/src/rtems/cpukit/libtest/t-test.c` (extract):

```c
void *
T_push_fixture(T_fixture_node *node, const T_fixture *fixture)
{
	T_context *ctx;
	T_fixture_node *old;
	void *context;

	ctx = &T_instance;
	old = ctx->fixtures;
	old->previous = node;
	node->next = old;
	node->previous = NULL;
	node->fixture = fixture;
	context = fixture->initial_context;
	node->context = context;
	node->next_planned_steps = atomic_exchange_explicit(
	    &ctx->planned_steps, UINT_MAX, memory_order_relaxed);
	node->next_steps = atomic_exchange_explicit(&ctx->steps, 0,
	    memory_order_relaxed);
	node->failures = atomic_fetch_add_explicit(&ctx->failures, 0,
	    memory_order_relaxed);
	ctx->fixtures = node;

	if (fixture->setup != NULL) {
		(*fixture->setup)(context);
	}

	return context;
}

static void
T_do_pop_fixture(T_context *ctx)
{
	T_fixture_node *node;
	const T_fixture *fixture;
	T_fixture_node *next;

	node = ctx->fixtures;
	next = node->next;
	ctx->fixtures = next;
	fixture = node->fixture;

	if (fixture != NULL && fixture->teardown != NULL) {
		(*fixture->teardown)(node->context);
	}

	if (next != NULL) {
		unsigned int planned_steps;
		unsigned int steps;
		unsigned int failures;

		next->previous = NULL;
		planned_steps = atomic_exchange_explicit(&ctx->planned_steps,
		    node->next_planned_steps, memory_order_relaxed);
		steps = atomic_exchange_explicit(&ctx->steps, node->next_steps,
		    memory_order_relaxed);
		failures = atomic_fetch_add_explicit(&ctx->failures, 0,
		    memory_order_relaxed);
		ctx->fixture_steps += steps;
		T_check_steps(planned_steps, steps, node->failures - failures);
	}

	memset(node, 0, sizeof(*node));
}
```


### Test Execution Sequence

So we now start with `RtemsModelEventsMgr_Run<N>` and establish execution order.

The highlights are:

#### Start: RtemsModelXXX_Run

```c
ctx = T_push_fixture(
    &RtemsModelEventsMgr_Node<N>,
    &RtemsModelEventsMgr_Fixture<N>
  );
```
This pushes the fixture onto a stack and then 
runs `RtemsModelEventsMgr_Setup_Wrap<N>` 
on `RtemsModelEventsMgr_Instance<N>`.

This is just `RtemsModelEventsMgr_Setup<N>()` 
on an uninitialised `RtemsModelEventsMgr_Context`.

#### Into: RtemsModelXXX_Setup

This logs as "Runner Setup"

Sets itself as the runner thread in the test context.

Creates  worker and runner testsync semaphores (`CreateTestSyncSema`)

Assigns the runner scheduler to self

if `RTEMS_SMP` does something with other scheduler.

Set own priority to `M_PRIO_NORMAL` 
and checks that previous priority was `M_PRIO_HIGH`.

Constructs Worker using `WorkerConfig<N>` and starts it running `Worker<N>`.

#### Start: Worker

Initial priority is `M_PRIO_LOW`.

Logs as "Worker Running"

Executes `TestSegment3`

Releases both testsync semaphores

Calls `rtems_event_receive` to enter blocking state.

#### Back to: RtemsModelXXX_Run

initialises context, including the test_number

sets up thread switch logging? 
Sets thread wait flags

Executes `TestSegment0`

Executes `Runner` which excutes `TestSegment4`

Invokes `RtemsModelEventsMgr_Cleanup`

#### Into: RtemsModelXXX_Cleanup

This *just* does a receive for any of all possible events, 
without waiting, and reports the outcomes.

#### Back to: RtemsModelXXX_Run

Runs `ShowWorkerSemaId`

Calls `T_pop_fixture` which invokes `T_do_pop_fixture`

This performs a teardown if present

#### Into: RtemsModelXXX_Teardown

Sets own priority to high

Deletes the worker task

Deletes the testsync semaphores

#### Back to: RtemsModelXXX_RunN

Test run now complete!


