/* SPDX-License-Identifier: BSD-2-Clause */

/**
 * @file
 *
 * @ingroup RTEMSTestCaseRtemsModelSemMgr_Run
 */

/*
 * Copyright (C) 2020 embedded brains GmbH (http://www.embedded-brains.de)
 *               2022 Trinity College Dublin (http://www.tcd.ie)
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 */

/*
 * Do not manually edit this file.  It is part of the RTEMS quality process
 * and was automatically generated.
 *
 * If you find something that needs to be fixed or worded better please
 * post a report to an RTEMS mailing list or raise a bug report:
 *
 * https://docs.rtems.org/branches/master/user/support/bugs.html
 *
 * For information on updating and regenerating please refer to:
 *
 * https://docs.rtems.org/branches/master/eng/req/howto.html
 */

#ifndef _TR_MODEL_SEM_MGR_H
#define _TR_MODEL_SEM_MGR_H

#include <rtems.h>
#include <rtems/score/thread.h>

#include <rtems/test.h>

#ifdef __cplusplus
extern "C" {
#endif

/*
 * Run Setup/Cleanup structs/functions
 */
typedef struct {
  int this_test_number; // test number used to identify a test runner instance

  Thread_Control *runner_thread; // TCB of the runner task
  rtems_id runner_id; // ID of the tasks
  rtems_id worker0_id; 
  rtems_id worker1_id;

  rtems_id runner_sema; // ID of the Runner semaphore
  rtems_id worker0_sema; // ID of the Worker0 semaphore
  rtems_id worker1_sema; // ID of the Worker1 semaphore 
  rtems_id sem_id; // ID of the created semaphore
  rtems_id sem_id2;

  rtems_id runner_sched; // scheduler ID of scheduler used by the runner task
  rtems_id other_sched; // scheduler ID of another scheduler
                        // which is not used by the runner task
  T_thread_switch_log_4 thread_switch_log; // thread switch log
} RtemsModelSemMgr_Context;

typedef enum {
  SM_PRIO_HIGH = 1,
  SM_PRIO_NORMAL,
  SM_PRIO_LOW,
  SM_PRIO_OTHER
} Priorities;

#define POWER_OF_10 100

#define CreateTask( name, priority ) \
  DoCreateTask( \
    rtems_build_name( name[ 0 ], name[ 1 ], name[ 2 ], name[ 3 ] ), \
    priority \
  )

typedef RtemsModelSemMgr_Context Context;

rtems_id DoCreateTask( rtems_name name, rtems_task_priority priority );

void StartTask( rtems_id id, rtems_task_entry entry, void *arg );

void DeleteTask( rtems_id id );

rtems_id CreateSema( char * name);

void DeleteSema( rtems_id id );

void ObtainSema( rtems_id id );

void ReleaseSema( rtems_id id );

rtems_task_priority SetPriority( rtems_id id, rtems_task_priority priority );

rtems_task_priority SetSelfPriority( rtems_task_priority priority );

rtems_option mergeattribs( bool scope, bool priority, int semtype, int locking );

rtems_option mergeopts( bool wait );

void checkTaskIs( rtems_id expected_id ) ;

void ShowSemaId( Context *ctx ) ;

void initialise_id ( rtems_id * id );

void initialise_semaphore( Context *ctx, rtems_id semaphore[] );

void RtemsModelSemMgr_Setup( void *arg ) ;

void RtemsModelSemMgr_Teardown( void *arg ) ;

size_t RtemsModelSemMgr_Scope( void *arg, char *buf, size_t n ) ;

void RtemsModelSemMgr_Cleanup( RtemsModelSemMgr_Context *ctx );

/**
 * @addtogroup RTEMSTestCaseRtemsModelSemMgr_Run
 *
 * @{
 */

/**
 * @brief Runs the test case.
 */

void RtemsModelSemMgr_Run0(void);
void RtemsModelSemMgr_Run1(void);
void RtemsModelSemMgr_Run2(void);
void RtemsModelSemMgr_Run3(void);
void RtemsModelSemMgr_Run4(void);
void RtemsModelSemMgr_Run5(void);
void RtemsModelSemMgr_Run6(void);
void RtemsModelSemMgr_Run7(void);
void RtemsModelSemMgr_Run8(void);
void RtemsModelSemMgr_Run9(void);
void RtemsModelSemMgr_Run10(void);
void RtemsModelSemMgr_Run11(void);
void RtemsModelSemMgr_Run12(void);
void RtemsModelSemMgr_Run13(void);
void RtemsModelSemMgr_Run14(void);
void RtemsModelSemMgr_Run15(void);
void RtemsModelSemMgr_Run16(void);
void RtemsModelSemMgr_Run17(void);
void RtemsModelSemMgr_Run18(void);
void RtemsModelSemMgr_Run19(void);
void RtemsModelSemMgr_Run30(void);
void RtemsModelSemMgr_Run31(void);
void RtemsModelSemMgr_Run32(void);
void RtemsModelSemMgr_Run33(void);
void RtemsModelSemMgr_Run34(void);
void RtemsModelSemMgr_Run35(void);
void RtemsModelSemMgr_Run36(void);
void RtemsModelSemMgr_Run37(void);
void RtemsModelSemMgr_Run38(void);
void RtemsModelSemMgr_Run39(void);
void RtemsModelSemMgr_Run40(void);
void RtemsModelSemMgr_Run41(void);
void RtemsModelSemMgr_Run42(void);
void RtemsModelSemMgr_Run43(void);
void RtemsModelSemMgr_Run44(void);
void RtemsModelSemMgr_Run45(void);
void RtemsModelSemMgr_Run46(void);
void RtemsModelSemMgr_Run47(void);
void RtemsModelSemMgr_Run48(void);
void RtemsModelSemMgr_Run49(void);
void RtemsModelSemMgr_Run40(void);








/** @} */

#ifdef __cplusplus
}
#endif

#endif /* _TR_SEM_H */
