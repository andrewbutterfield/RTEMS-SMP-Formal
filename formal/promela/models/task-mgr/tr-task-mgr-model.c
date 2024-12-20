/* SPDX-License-Identifier: BSD-2-Clause */

/**
 * @file
 *
 * @ingroup RTEMSTestCaseRtemsModelEventsMgr
 */

/*
 * Copyright (C) 2020 embedded brains GmbH (http://www.embedded-brains.de)
 *                    Trinity College Dublin (http://www.tcd.ie)
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
 * This file was automatically generated.  Do not edit it manually.
 * Please have a look at
 *
 * https://docs.rtems.org/branches/master/eng/req/howto.html
 *
 * for information how to maintain and re-generate this file.
 */

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include <rtems/score/threadimpl.h>

#include "tr-task-mgr-model.h"

static const char PromelaModelTaskMgr[] = "/PML-TaskMgr";

#define INPUT_EVENTS ( RTEMS_EVENT_5 | RTEMS_EVENT_23 )

#define TASK_NAME_DEFAULT (0x54534b30) // TSK0 hex

void Wait( rtems_id id )
{
  rtems_status_code sc;

  sc = rtems_semaphore_obtain( id, RTEMS_WAIT, RTEMS_NO_TIMEOUT );
  T_quiet_rsc_success( sc );
}

void Wakeup( rtems_id id )
{
  rtems_status_code sc;

  sc = rtems_semaphore_release( id );
  T_quiet_rsc_success( sc );
}

/*
 * Here we need a mapping from model "task numbers/names" to thread Id's here
 *  Promela Process 3 corresponds to Task 0 (Worker), doing Send
 *  Promela Process 4 corresponds to Task 1 (Runner), doing Receive
 */

rtems_name mapName(int task)
{
    rtems_name taskName;
    if (!task) {
        taskName = 0;
    } 
    else {
        // TODO: Verify
        taskName = TASK_NAME_DEFAULT + task;
    }
    return taskName;
}

void init_tid(rtems_id* id, int max) {
    for( int i=0; i < max; i++ ) {
        id[i] = 0;
    }
}

rtems_task_priority priority_inversion(rtems_task_priority prio) {
    // Fix later
    int LOW_PRIO = 10;
    int HIGH_PRIO = 1;
    if (prio == LOW_PRIO) 
        return HIGH_PRIO;
    else if (prio == HIGH_PRIO)
        return LOW_PRIO;
    else return prio;
}
/*
rtems_mode mergeMode(bool preempt, bool tSlice, bool asr, int isr)
{
    rtems_mode taskMode;
    // Construct rtems_mode variable 
    taskMode |= preempt ? RTEMS_PREEMPT : RTEMS_NO_PREEMPT;
    taskMode |= tSlice ? RTEMS_TIMESLICE : RTEMS_NO_TIMESLICE;
    taskMode |= asr ? RTEMS_ASR : RTEMS_ASR;
    taskMode |=  RTEMS_INTERRUPT_LEVEL(isr);

    return taskMode;
}
*/

/*
void initialise_pending( rtems_event_set pending[], int max )
{
  int i;

  for( i=0; i < max; i++ ) {
    pending[i] = 0;
  }
}
*/

static void RtemsModelTaskMgr_Teardown(
  RtemsModelTaskMgr_Context *ctx
)
{
  rtems_status_code   sc;
  rtems_task_priority prio;

  T_log( T_NORMAL, "Runner Teardown" );

  prio = 0;
  sc = rtems_task_set_priority( RTEMS_SELF, M_PRIO_HIGH, &prio );
  T_rsc_success( sc );
  //T_eq_u32( prio, M_PRIO_HIGH );

  T_surrender_objects( ctx->seized_objects, rtems_task_delete );

  if ( ctx->worker_id != 0 ) {
    T_printf( "L:Deleting Task id : %d\n", ctx->worker_id );
    sc = rtems_task_delete( ctx->worker_id );
    T_rsc_success( sc );
  }

  T_log( T_NORMAL, "Deleting Worker 0 ReleaseTestSyncSema Semaphore" );
  DeleteTestSyncSema( ctx->worker0_wakeup );
  T_log( T_NORMAL, "Deleting Worker 1 ReleaseTestSyncSema Semaphore" );
  DeleteTestSyncSema( ctx->worker1_wakeup );
  T_log( T_NORMAL, "Deleting Runner ReleaseTestSyncSema Semaphore" );
  DeleteTestSyncSema( ctx->runner_wakeup );
  T_log( T_NORMAL, "Deleting Lock 0 ReleaseTestSyncSema Semaphore" );
  DeleteTestSyncSema( ctx->lock_0 );
  T_log( T_NORMAL, "Deleting Worker Flags TestSync Semaphore" );
  DeleteTestSyncSema( ctx->worker0_flag );
  DeleteTestSyncSema( ctx->worker1_flag );
}

void RtemsModelTaskMgr_Teardown_Wrap( void *arg )
{
  RtemsModelTaskMgr_Context *ctx;

  ctx = arg;
  RtemsModelTaskMgr_Teardown( ctx );
}


size_t RtemsModelTaskMgr_Scope( void *arg, char *buf, size_t n )
{
  RtemsModelTaskMgr_Context *ctx;
  size_t m;
  int p10;
  int tnum ;
  char digit;

  ctx = arg;
  p10 = POWER_OF_10;

  m = T_str_copy(buf, PromelaModelTaskMgr, n);
  buf += m;
  tnum = ctx->this_test_number;
  while( p10 > 0 && m < n )
  {
    digit = (char) ( (int) '0' + tnum / p10 );
    buf[0] = digit;
    ++buf;
    ++m;
    tnum = tnum % p10;
    p10 /= 10;
  }
  return m;
}

void RtemsModelTaskMgr_Cleanup(
  RtemsModelTaskMgr_Context *ctx
)
{
  rtems_status_code sc;
  rtems_event_set events;

  events = 0;
  sc = rtems_event_receive(
    RTEMS_ALL_EVENTS,
    RTEMS_NO_WAIT | RTEMS_EVENT_ANY,
    0,
    &events
  );

  if ( sc == RTEMS_SUCCESSFUL ) {
    T_quiet_ne_u32( events, 0 );
  } else {
    T_quiet_rsc( sc, RTEMS_UNSATISFIED );
    T_quiet_eq_u32( events, 0 );
  }
}