# BARRIER MANAGER status

## 4th Nov 2022 TEST FAIL

* Platform: Dell G5, Ubuntu 20.04.5 LTS
* Generated: OK
* Compiles: OK
* Runs: OK
* All Tests Pass: No, 27 fail
```
F:0.7:0:RUN/PML-BarrierMgr000:tr-barrier-mgr-model-9.c:332:1 == 4
F:*:0:RUN:*:*:Wrong runner priority, expected 1, actual 4
E:RtemsModelBarrierMgr9:N:33:F:2:D:0.012084

F:*:0:RUN:*:*:Wrong runner priority, expected 1, actual 4
E:RtemsModelBarrierMgr8:N:36:F:1:D:0.012003

F:*:0:RUN:*:*:Wrong runner priority, expected 1, actual 4
E:RtemsModelBarrierMgr14:N:37:F:1:D:0.012264

F:0.19:0:WRK0/PML-BarrierMgr013:tr-barrier-mgr-model-13.c:185:RTEMS_SUCCESSFUL == RTEMS_TOO_MANY
F:*:0:RUN:*:*:RTEMS barrier leak (1)
F:*:0:RUN:*:*:Wrong runner priority, expected 1, actual 4
E:RtemsModelBarrierMgr13:N:33:F:3:D:0.011301

F:0.21:0:WRK0/PML-BarrierMgr012:tr-barrier-mgr-model-12.c:203:RTEMS_SUCCESSFUL == RTEMS_TOO_MANY
F:*:0:RUN:*:*:RTEMS barrier leak (1)
F:*:0:RUN:*:*:Wrong runner priority, expected 1, actual 4
E:RtemsModelBarrierMgr12:N:36:F:3:D:0.011563

F:*:0:RUN:*:*:Wrong runner priority, expected 1, actual 4
E:RtemsModelBarrierMgr0:N:36:F:1:D:0.009776
Z:Model0:C:22:N:757:F:27:D:0.246403
Y:ReportHash:SHA256:H_j2zroRO1RaYJR3cZx9Bn68EfP5EBnpXZej6By5tIU=
cpu 0 in error mode (tt = 0x80)
 12687650  00015ba0:  91d02000   ta  0x0
```
See `events/archive/20221103-170752`

## 3rd Nov 2022 BUILD FAIL

* Platform: Dell G5, Ubuntu 20.04.5 LTS
* Generated: OK
* Compiles: No
 ```
 Build failed
 -> task in 'testsuites/validation/ts-model-0.exe' failed with exit status 1 (run with -v to display more information)
```
It's the `tx-support` issue.
* Runs: n/a
* All Tests Pass: n/a

See `events/archive/20221103-171724`
