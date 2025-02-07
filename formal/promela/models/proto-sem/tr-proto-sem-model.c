/* SPDX-License-Identifier: BSD-2-Clause */

/**
 * @file
 *
 * @ingroup RTEMSTestCaseRtemsModelProtoSem
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

#include "tr-proto-sem-model.h"

static const char PromelaModelProtoSem[] = "/PML-ProtoSem";


int update1(int *p1, int *p2) {
  *p1 = *p2+10 ; 
  *p2 = *p1*2  ;
}

int update2(int* p1, int *p2) {
  *p1 = *p2+5 ; 
  *p2 = *p1*3  ;
}


#define INPUT_EVENTS ( RTEMS_EVENT_5 | RTEMS_EVENT_23 )

// this is GetPendingEvents from tr-event-send-receive.c
rtems_event_set GetPending( Context *ctx )
{
  rtems_event_set pending;
  rtems_status_code sc;

  sc = ( *ctx->receive )(
    RTEMS_PENDING_EVENTS,
    RTEMS_DEFAULT_OPTIONS,
    0,
    &pending
  );
  T_quiet_rsc_success( sc );

  return pending;
}




/*
 * Here we need a mapping from model "task numbers/names" to thread Id's here
 *  Promela Process 3 corresponds to Task 0 (Worker), doing Send
 *  Promela Process 4 corresponds to Task 1 (Runner), doing Receive
 */
rtems_id mapid( Context *ctx, int pid )
{
  rtems_id mapped_id;

  switch ( pid ) {
    case 1 : mapped_id = ctx->worker_id ; break;
    case 2 : mapped_id = ctx->runner_id; break;
    default : mapped_id = 0xffffffff; break;
  }
  return mapped_id;
}

void initialise_pending( rtems_event_set pending[], int max )
{
  int i;

  for( i=0; i < max; i++ ) {
    pending[i] = 0;
  }
}


static void RtemsModelProtoSem_Teardown(
  RtemsModelProtoSem_Context *ctx
)
{
  rtems_status_code   sc;
  rtems_task_priority prio;

  T_log( T_NORMAL, "Runner Teardown" );

  prio = 0;
  sc = rtems_task_set_priority( RTEMS_SELF, M_PRIO_HIGH, &prio );
  T_rsc_success( sc );
  T_eq_u32( prio, M_PRIO_NORMAL );

  if ( ctx->worker_id != 0 ) {
    T_printf( "L:Deleting Task id : %d\n", ctx->worker_id );
    sc = rtems_task_delete( ctx->worker_id );
    T_rsc_success( sc );
  }

  T_log( T_NORMAL, "Deleting Worker ReleaseTestSyncSema Semaphore" );
  DeleteTestSyncSema( ctx->worker_wakeup );
  T_log( T_NORMAL, "Deleting Runner ReleaseTestSyncSema Semaphore" );
  DeleteTestSyncSema( ctx->runner_wakeup );
}

void RtemsModelProtoSem_Teardown_Wrap( void *arg )
{
  RtemsModelProtoSem_Context *ctx;

  ctx = arg;
  RtemsModelProtoSem_Teardown( ctx );
}


size_t RtemsModelProtoSem_Scope( void *arg, char *buf, size_t n )
{
  RtemsModelProtoSem_Context *ctx;
  size_t m;
  int p10;
  int tnum ;
  char digit;

  ctx = arg;
  p10 = EVT_PWR_OF_10;

  m = T_str_copy(buf, PromelaModelProtoSem, n);
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

void RtemsModelProtoSem_Cleanup(
  RtemsModelProtoSem_Context *ctx
)
{
  rtems_status_code sc;
  rtems_event_set events;

  events = 0;
  sc = ( *ctx->receive )(
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
