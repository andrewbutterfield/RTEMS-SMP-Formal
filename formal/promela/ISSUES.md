# ISSUES

## Link Failure

Cannot build more than one manager model at a time, because of multiple/conflicting definitions.

Duplicates in `tr-*-mgr-model.h` and `tr-*-mgr-model.c` 
where `*` is `msg` | `barrier` | `event` | `sem`.

```
checkTaskIs
initialise_semaphore
CreateWakeupSema
DeleteWakeupSema
Wait
Wakeup
mergeopts -- DIFFERENT between {event}, {msg,sem}  event has 'wantall'
initialise_pending
initialise_semaphore
ShowWorkerSemaId
ShowRunnerSemaId
CreateSema
DeleteSema
mergeattribs  -- DIFFERENT between {barrier}, {sem}
ShowSemaId 
```

DONE SO FAR

* created `models/common` with `tr-model-0.h` and `tr-model-0.c`.
* moved common stuff from message manager into `common/tr*`.

TO DO

* replace `Context` arguments with field components.

NOTE: `GetPending` is only used in the events manager.

Issue is now something like `rtems_id idNull( Context *ctx, bool passedid )` 
with implementation:

```
rtems_id idNull( Context *ctx, bool passedid )
{
  rtems_id id;

  if ( passedid ) { return ctx->queue_id; }
  else { return NULL; }
}
```

Also `Context` is used widely in `score` for task context handling.

In the Semaphore manager we have:

```
typedef RtemsModelSemMgr_Context Context;
```

So, we have to pass in the relevant fields, 
rather than the whole context, to these functions.

## Testbuilder

### Model Naming

This is broken

For test build we need to specify the semaphore model as `sem-mgr-model`,
and not as `semaphores`, so what is `model.yml` for?

clean takes a `model` parameter as typed by the user

spin and gentests invoke `get_model_paths`.

Need a consistent approach here, using the contents of `model.yml` (`models.yml`?).

### Model.h files

File `tr-<model>.h` currently defines test helpers 
(like `mergeopts`,`ObtainSema`).
It also has a fixed list declaring the `RtemsModel<Mgr>_RunN` functions.
This part should be auto-generated, in the way that `tc-<model>.c` is.


### Using tx-support.h

We do something strange here:

```
LowerPriority: |
  SetSelfPriority( PRIO_LOW );
  rtems_task_priority prio;
  rtems_status_code sc;
  sc = rtems_task_set_priority( RTEMS_SELF, RTEMS_CURRENT_PRIORITY, &prio );
  T_rsc_success( sc );
  T_eq_u32( prio, PRIO_LOW );
```

We use `tx-support` function `SetSelfPriority` to set priority to low
(it uses `rtems_task_set_priority` under the hood).
We then use `rtems_task_set_priority` to set priority to itself,
and check its previous value was low.
This is done everywhere, even in the Event Manager.

Two uses in `tr-event-send-receive.c` :

```
case PRIO_HIGH:
        prio = SetSelfPriority( ctx->sender_prio );
        T_eq_u32( prio, PRIO_LOW );
        break;

  SetSelfPriority( PRIO_NORMAL );
  ctx->worker_id = CreateTask( "WORK", PRIO_LOW );
  StartTask( ctx->worker_id, Worker, ctx );        
```


## Test Outcomes

###  Barriers

30 tests failing 

```
BM8:F:3 BM6:F:3 BM4:3 BM2:3 BM18:3 BM16:3 BM14:3 BM12:3 BM10:3 BM0:3
```

* 1st error is always line 94
* 2nd error jumps around lines: 147 153 158 172 177 182
* 3rd  error is invisible (no "F:0...." line)

### Messages

MessageMgr22:
```
F:0.17:0:@#/PML-MessageMgr022:tr-msg-mgr-model-22.c:192:RTEMS_SUCCESSFUL == RTEMS_TIMEOUT
```


### Semaphores

NOW FIXED.

All failures occurred at tr-sem-mgr-model.c:223 
They reported `3 == 2`.


The PML Runner proctype checks its initial priority just before finishing.
If low, it raises its priority to normal, to satisfy the test teardown.

This is inside `RtemsModelSemMgr_Teardown`.

Perhaps the test teardown should not care about this?

