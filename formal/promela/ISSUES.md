# ISSUES

## Barrier deadlocks

Running manually
`validation% sparc-rtems6-sis -leon3 -r s -m 2 ts-model-0.exe`
```
B:RtemsModelBarrierMgr17
L:Pushing Test Fixture...
L:Runner Setup
L:Creating Runner Semaphore
L:Creating Worker0 Semaphore
L:Creating Worker1 Semaphore
L:Created Worker 0
L:Started Worker 0
L:Created Worker 1
L:Started Worker 1
L:Test Fixture Pushed
L:@@@ 0 INIT
L:Runner(Task 0) running
L:@@@ 3 TASK Runner
L:@@@ 3 CALL NormalPriority
L:@@@ 3 CALL barrier_create 1 1 3 1
L:Calling BarrierCreate(1,1,3,1)
L:Returned 0x0 from Create
L:@@@ 3 SCALAR created 1
L:@@@ 3 SCALAR rc 0
L:@@@ 3 SIGNAL 1
L:semaphore release id = 436273157
L:semaphore release
L:Returned 0x0 from release
L:@@@ 3 CALL barrier_wait 1 0
L:Calling BarrierWait(1375797250,0)
```

Can run all other models together (`chains`,`event-mgr`,`msg-mgr`,`sem-mgr`).

## TO DO

* integrate the barrier manager
* redo the sema_set_priority model - it is failing with error returns
* move the following declarations to `tx-model-0`:
  -  return values
  -  task states

NOTE: `GetPending` is only used in the events manager.
Note also that this and other stuff was defined 
in SH's `tr-event-send-receive.c`.

## Testbuilder

### Model Naming


 * We use the same name for model, folder and root,
   based on Manual terminology, with "mgr" used to abbreviate "Manager". 
 * Names should be kept short
 * We only add "-model" to C sources placed into RTEMS test folders.
 
The names to be used are:

 * Barrier Manager: `barrier-mgr`
 * Chains: `chains`
 * Event Manager: `event-mgr`
 * Message Manager: `msg-mgr`
 * Semaphore Manager: `sem-mgr`

The role of `models.yml` is now simply to list all the currently available models.

### Current command behaviour:
 
 * `zero`,`clean`,`spin`,`gentests`, `copy`, `allsteps` require `xxx-mgr`

 * `allsteps` fails with a lookup error if first model is not `xx-model`,
    but fails with an informative error message if first is OK, 
    but subsequent are bad.

 * `models.yml` is used when `alltests` is specified
 

For test build we need to specify the semaphore model as `sem-mgr-model`,
and not as `semaphores`, so what is `model.yml` for?

clean takes a `model` parameter as typed by the user

spin and gentests invoke `get_model_paths`.

Need a consistent approach here, using the contents of `model.yml` (`models.yml`?).

### Model.h files

File `tr-<modelname>-model.h` currently defines test helpers 
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

