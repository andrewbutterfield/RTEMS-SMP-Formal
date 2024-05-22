# ISSUES

## Model Naming

This is broken

For test build we need to specify the semaphore model as `sem-mgr-model`,
and not as `semaphores`, so what is `model.yml` for?

clean takes a `model` parameter as typed by the user

spin and gentests invoke `get_model_paths`.

## Using tx-support.h

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

### Semaphores

All failures occur at tr-sem-mgr-model.c:223 
They report `3 == 2`.

It involves setting the runner tasks' priority to high,
and checking that its previous priority was normal.

This is inside `RtemsModelSemMgr_Teardown`.

However, in the priority scenarios, the runner's priority is set to low.
In the "Common" defaults the runner's priority is set to medium.

Non-failing runs: 0 .. 13
Failing runs: 14 .. 49

Note that HIGH,NORMAL,LOW,OTHER - 1,2,3,4

```
  prio = 0;
  sc = rtems_task_set_priority( RTEMS_SELF, SM_PRIO_HIGH, &prio );
  T_rsc_success( sc );
  T_eq_u32( prio, SM_PRIO_NORMAL );
```

```
118:E:RtemsModelSemMgr9:N:34:F:0:D:0.015089
224:E:RtemsModelSemMgr8:N:40:F:0:D:0.018366
326:E:RtemsModelSemMgr7:N:36:F:0:D:0.016936
433:E:RtemsModelSemMgr6:N:35:F:0:D:0.017184
530:E:RtemsModelSemMgr5:N:35:F:0:D:0.016085
664:F:0.33:0:RUN/PML-SemMgr049:tr-sem-mgr-model.c:223:3 == 2
668:E:RtemsModelSemMgr49:N:37:F:1:D:0.021842
802:F:0.33:0:RUN/PML-SemMgr048:tr-sem-mgr-model.c:223:3 == 2
806:E:RtemsModelSemMgr48:N:37:F:1:D:0.021934
940:F:0.33:0:RUN/PML-SemMgr047:tr-sem-mgr-model.c:223:3 == 2
944:E:RtemsModelSemMgr47:N:37:F:1:D:0.021954
1078:F:0.33:0:RUN/PML-SemMgr046:tr-sem-mgr-model.c:223:3 == 2
1082:E:RtemsModelSemMgr46:N:37:F:1:D:0.021950
1239:F:0.33:0:RUN/PML-SemMgr045:tr-sem-mgr-model.c:223:3 == 2
1243:E:RtemsModelSemMgr45:N:37:F:1:D:0.025240
1400:F:0.33:0:RUN/PML-SemMgr044:tr-sem-mgr-model.c:223:3 == 2
1404:E:RtemsModelSemMgr44:N:37:F:1:D:0.025257
1561:F:0.33:0:RUN/PML-SemMgr043:tr-sem-mgr-model.c:223:3 == 2
1565:E:RtemsModelSemMgr43:N:37:F:1:D:0.025228
1722:F:0.33:0:RUN/PML-SemMgr042:tr-sem-mgr-model.c:223:3 == 2
1726:E:RtemsModelSemMgr42:N:37:F:1:D:0.025205
1883:F:0.33:0:RUN/PML-SemMgr041:tr-sem-mgr-model.c:223:3 == 2
1887:E:RtemsModelSemMgr41:N:37:F:1:D:0.025217
2044:F:0.33:0:RUN/PML-SemMgr040:tr-sem-mgr-model.c:223:3 == 2
2048:E:RtemsModelSemMgr40:N:37:F:1:D:0.025217
2154:E:RtemsModelSemMgr4:N:34:F:0:D:0.017115
2311:F:0.33:0:RUN/PML-SemMgr039:tr-sem-mgr-model.c:223:3 == 2
2315:E:RtemsModelSemMgr39:N:37:F:1:D:0.025182
2472:F:0.33:0:RUN/PML-SemMgr038:tr-sem-mgr-model.c:223:3 == 2
2476:E:RtemsModelSemMgr38:N:37:F:1:D:0.025225
2633:F:0.33:0:RUN/PML-SemMgr037:tr-sem-mgr-model.c:223:3 == 2
2637:E:RtemsModelSemMgr37:N:37:F:1:D:0.025218
2794:F:0.33:0:RUN/PML-SemMgr036:tr-sem-mgr-model.c:223:3 == 2
2798:E:RtemsModelSemMgr36:N:37:F:1:D:0.025202
2952:F:0.32:0:RUN/PML-SemMgr035:tr-sem-mgr-model.c:223:3 == 2
2956:E:RtemsModelSemMgr35:N:36:F:1:D:0.024778
3110:F:0.32:0:RUN/PML-SemMgr034:tr-sem-mgr-model.c:223:3 == 2
3114:E:RtemsModelSemMgr34:N:36:F:1:D:0.024894
3268:F:0.32:0:RUN/PML-SemMgr033:tr-sem-mgr-model.c:223:3 == 2
3272:E:RtemsModelSemMgr33:N:36:F:1:D:0.024882
3426:F:0.32:0:RUN/PML-SemMgr032:tr-sem-mgr-model.c:223:3 == 2
3430:E:RtemsModelSemMgr32:N:36:F:1:D:0.024773
3584:F:0.32:0:RUN/PML-SemMgr031:tr-sem-mgr-model.c:223:3 == 2
3588:E:RtemsModelSemMgr31:N:36:F:1:D:0.024889
3744:F:0.32:0:RUN/PML-SemMgr030:tr-sem-mgr-model.c:223:3 == 2
3748:E:RtemsModelSemMgr30:N:36:F:1:D:0.025081
3849:E:RtemsModelSemMgr3:N:33:F:0:D:0.016232
4005:F:0.32:0:RUN/PML-SemMgr029:tr-sem-mgr-model.c:223:3 == 2
4009:E:RtemsModelSemMgr29:N:36:F:1:D:0.025092
4165:F:0.32:0:RUN/PML-SemMgr028:tr-sem-mgr-model.c:223:3 == 2
4169:E:RtemsModelSemMgr28:N:36:F:1:D:0.025199
4323:F:0.32:0:RUN/PML-SemMgr027:tr-sem-mgr-model.c:223:3 == 2
4327:E:RtemsModelSemMgr27:N:36:F:1:D:0.025209
4481:F:0.32:0:RUN/PML-SemMgr026:tr-sem-mgr-model.c:223:3 == 2
4485:E:RtemsModelSemMgr26:N:36:F:1:D:0.025183
4616:F:0.32:0:RUN/PML-SemMgr025:tr-sem-mgr-model.c:223:3 == 2
4620:E:RtemsModelSemMgr25:N:36:F:1:D:0.021416
4751:F:0.32:0:RUN/PML-SemMgr024:tr-sem-mgr-model.c:223:3 == 2
4755:E:RtemsModelSemMgr24:N:36:F:1:D:0.021431
4909:F:0.32:0:RUN/PML-SemMgr023:tr-sem-mgr-model.c:223:3 == 2
4913:E:RtemsModelSemMgr23:N:36:F:1:D:0.024813
5067:F:0.32:0:RUN/PML-SemMgr022:tr-sem-mgr-model.c:223:3 == 2
5071:E:RtemsModelSemMgr22:N:36:F:1:D:0.024813
5225:F:0.32:0:RUN/PML-SemMgr021:tr-sem-mgr-model.c:223:3 == 2
5229:E:RtemsModelSemMgr21:N:36:F:1:D:0.024698
5383:F:0.32:0:RUN/PML-SemMgr020:tr-sem-mgr-model.c:223:3 == 2
5387:E:RtemsModelSemMgr20:N:36:F:1:D:0.024822
5478:E:RtemsModelSemMgr2:N:32:F:0:D:0.014805
5632:F:0.32:0:RUN/PML-SemMgr019:tr-sem-mgr-model.c:223:3 == 2
5636:E:RtemsModelSemMgr19:N:36:F:1:D:0.024833
5790:F:0.32:0:RUN/PML-SemMgr018:tr-sem-mgr-model.c:223:3 == 2
5794:E:RtemsModelSemMgr18:N:36:F:1:D:0.024796
5948:F:0.32:0:RUN/PML-SemMgr017:tr-sem-mgr-model.c:223:3 == 2
5952:E:RtemsModelSemMgr17:N:36:F:1:D:0.024671
6106:F:0.32:0:RUN/PML-SemMgr016:tr-sem-mgr-model.c:223:3 == 2
6110:E:RtemsModelSemMgr16:N:36:F:1:D:0.024812
6264:F:0.32:0:RUN/PML-SemMgr015:tr-sem-mgr-model.c:223:3 == 2
6268:E:RtemsModelSemMgr15:N:36:F:1:D:0.024798
6422:F:0.32:0:RUN/PML-SemMgr014:tr-sem-mgr-model.c:223:3 == 2
6426:E:RtemsModelSemMgr14:N:36:F:1:D:0.024661
6538:E:RtemsModelSemMgr13:N:38:F:0:D:0.018466
6650:E:RtemsModelSemMgr12:N:36:F:0:D:0.018053
6756:E:RtemsModelSemMgr11:N:34:F:0:D:0.016967
6847:E:RtemsModelSemMgr10:N:32:F:0:D:0.014699
6938:E:RtemsModelSemMgr1:N:32:F:0:D:0.014832
7028:E:RtemsModelSemMgr0:N:32:F:0:D:0.014614
7029:Z:TestsuitesModel0:C:50:N:1793:F:36:D:1.128172
```

## Model Scenarios

Spin file number to sub-scenario mapping:

```
0 : onesema | bad create, invalid name
1 : onesema | bad create, passed id null
2 : onesema | bad create, passed invalid initial count
3 : onesema | created and deleted
4 : onesema | created, release at max count
5 : onesema
6 : onesema
7 : onesema
8 : twosemas
9 : twosemas
10 : different_sema_counts | created, sema_count = 0
11 : different_sema_counts | created, sema_count = 1
12 : different_sema_counts | created, sema_count = 2
13 : different_sema_counts | created, sema_count = 3
14 : test_priority | created, testing no locking - priority inversion 
15 : test_priority | created, testing no locking - priority inversion 
16 : test_priority | created, testing no locking - priority inversion 
17 : test_priority | created, testing no locking - priority inversion 
18 : test_priority | created, testing no locking - priority inversion 
19 : test_priority | created, testing no locking - priority inversion 
20 : test_priority | created, testing no locking - priority inversion 
21 : test_priority | created, testing no locking - priority inversion 
22 : test_priority | created, testing no locking - priority inversion 
23 : test_priority | created, testing no locking - priority inversion 
24 : test_priority | created, testing priority ceiling protocol 
25 : test_priority | created, testing priority ceiling protocol 
26 : test_priority | created, testing priority inheritance protocol 
27 : test_priority | created, testing priority inheritance protocol 
28 : test_priority | created, testing priority inheritance protocol 
29 : test_priority | created, testing priority inheritance protocol 
30 : test_priority | created, testing priority inheritance protocol 
31 : test_priority | created, testing priority inheritance protocol 
32 : test_priority | created, testing priority inheritance protocol 
33 : test_priority | created, testing priority inheritance protocol 
34 : test_priority | created, testing priority inheritance protocol 
35 : test_priority | created, testing priority inheritance protocol 
36 : test_set_priority | set priority, no locking protocol, not defined
37 : test_set_priority | set priority, no locking protocol, not defined
38 : test_set_priority | set priority, no locking protocol, not defined
39 : test_set_priority | set priority, no locking protocol, not defined
40 : test_set_priority | set priority, no locking protocol, not defined
41 : test_set_priority | set priority, no locking protocol, not defined
42 : test_set_priority | set priority, no locking protocol, not defined
43 : test_set_priority | set priority, no locking protocol, not defined
44 : test_set_priority | set priority, no locking protocol, not defined
45 : test_set_priority | set priority, no locking protocol, not defined
46 : test_set_priority | set priority, ceiling locking protocol, successful
47 : test_set_priority | set priority, ceiling locking protocol, successful
48 : test_set_priority | set priority, invalid new priority
49 : test_set_priority | set priority, invalid new priority
```

It is clear that the priority scenarios induce the 2==3 test fail.

