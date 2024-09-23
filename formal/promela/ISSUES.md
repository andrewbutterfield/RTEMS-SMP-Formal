# ISSUES

## PUZZLING

Test code (sem-mgr:49)

```
T_log(T_NORMAL,"@@@ 3 CALL sema_set_priority 1 -1 0");
  sem_id = 1;
  rtems_task_priority new_priority = -1;
  rtems_id scheduler_id;
  rtems_task_priority old_priority;
  rtems_status_code sc1;    
  sc1 = rtems_task_get_scheduler( RTEMS_SELF, &scheduler_id );
  T_quiet_rsc( sc1, RTEMS_SUCCESSFUL );
  rc = rtems_semaphore_set_priority(ctx->sem_id, scheduler_id, new_priority, &old_priority);
  T_log(T_NORMAL, "Returned 0x%x from setPrio", rc );
  T_log(T_NORMAL,"@@@ 3 SCALAR rc 9");
  T_rsc( rc, 9 );
```

Corresponding test output:

```
L:@@@ 3 CALL sema_set_priority 1 -1 0
L:Returned 0x13 from setPrio
L:@@@ 3 SCALAR rc 9
F:0.23:0:RUN/PML-SemMgr049:tr-sem-mgr-model-49.c:153:RTEMS_INVALID_PRIORITY == RTEMS_INVALID_ADDRESS
```

Relevant codes:

RTEMS_INVALID_ADDRESS = 9  a specified address was invalid
RTEMS_UNSATISFIED = 13     the request was not satisfied
RTEMS_INVALID_PRIORITY = 19 an invalid thread priority was provided


### STATUS

 * `allmodels` - 15 tests fail
 * `barrier-mgr` - all tests pass  
 * `chains` - all tests pass 
 * `event-mgr` - all tests pass
 * `msg-mgr` - 1 test fails
 * `sem-mgr` - 14 tests fail

 * `barrier-mgr` fixed by changing sis core argument from `-m 2` to `-m 4`.
 * `msg-mgr` now has only one test-fail: 
    `F:0.17:0:@)/PML-MessageMgr022:tr-msg-mgr-model-22.c:194:RTEMS_SUCCESSFUL == RTEMS_TIMEOUT`

msg 
 
### TO DO

* redo the sema_set_priority model - it is failing with error returns
* move the following declarations to `tx-model-0`:
  -  return values
  -  task states

NOTE: `GetPending` is only used here in the events manager.
There is a `GetPendingEvents` in SH's `tr-event-send-receive.c`.


### Current command behaviour:
 
 * `zero`,`clean`,`spin`,`gentests`, `copy`, `allsteps` require `xxx-mgr`

 * `allsteps` fails with a lookup error if first model is not `xx-model`,
    but fails with an informative error message if first is OK, 
    but subsequent are bad.

 * `models.yml` is used when `alltests` is specified
 

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

