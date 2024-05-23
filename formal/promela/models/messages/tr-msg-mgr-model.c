/* SPDX-License-Identifier: BSD-2-Clause */

/**
 * @file
 *
 * @ingroup RTEMSTestCaseRtemsModelMsgMgr
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

#include "tr-msg-mgr-model.h"



void initialise_pending( rtems_event_set pending[], int max )
{
  int i;

  for( i=0; i < max; i++ ) {
    pending[i] = 0;
  }
}

static void RtemsModelMessageMgr_Teardown(
  RtemsModelMessageMgr_Context *ctx
)
{
  rtems_status_code   sc;
  rtems_task_priority prio;

  T_log( T_NORMAL, "Runner Teardown" );

  prio = 0;
  sc = rtems_task_set_priority( RTEMS_SELF, PRIO_HIGH, &prio );
  T_rsc_success( sc );
  T_eq_u32( prio, PRIO_NORMAL );

  if ( ctx->worker1_id != 0 ) {
    T_printf( "L:Deleting Task id : %d\n", ctx->worker1_id );
    sc = rtems_task_delete( ctx->worker1_id );
    T_rsc_success( sc );
  }

  T_log( T_NORMAL, "Deleting Worker1 Wakeup Semaphore" );
  DeleteWakeupSema( ctx->worker1_wakeup );


  if ( ctx->worker2_id != 0 ) {
    T_printf( "L:Deleting Task id : %d\n", ctx->worker2_id );
    sc = rtems_task_delete( ctx->worker2_id );
    T_rsc_success( sc );
  }

  T_log( T_NORMAL, "Deleting Worker2 Wakeup Semaphore" );
  DeleteWakeupSema( ctx->worker2_wakeup );

  T_log( T_NORMAL, "Deleting Runner Wakeup Semaphore" );
  DeleteWakeupSema( ctx->runner_wakeup );
}

void RtemsModelMessageMgr_Teardown_Wrap( void *arg )
{
  RtemsModelMessageMgr_Context *ctx;

  ctx = arg;
  RtemsModelMessageMgr_Teardown( ctx );
}


size_t RtemsModelMessageMgr_Scope( void *arg, char *buf, size_t n )
{
  RtemsModelMessageMgr_Context *ctx;
  size_t m;
  int p10;
  int tnum ;
  char digit;

  ctx = arg;
  p10 = POWER_OF_10;

  m = T_str_copy(buf, PromelaModelMessageMgr, n);
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

void RtemsModelMessageMgr_Cleanup(
  RtemsModelMessageMgr_Context *ctx
)
{
  rtems_status_code status;

  if (ctx->queue_id != 0){
    status = rtems_message_queue_delete(ctx->queue_id);
    if (status != RTEMS_SUCCESSFUL) { T_quiet_rsc( status, RTEMS_INVALID_ID ); }
    else { T_rsc_success( status ); }
    ctx->queue_id = RTEMS_ID_NONE;
  }
}
