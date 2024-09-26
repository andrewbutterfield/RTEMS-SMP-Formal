/* SPDX-License-Identifier: BSD-2-Clause */

/**
 * @file
 *
 * @ingroup RTEMSTestCaseRtemsModelBarrierMgr
 */

/*
 * Copyright (C) 2020-2022 embedded brains GmbH (http://www.embedded-brains.de)
 *                         Trinity College Dublin (http://www.tcd.ie)
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

#include "tx-support.h"
#include "tx-model-0.h"
#include "tr-barrier-mgr-model.h"

static const char PromelaModelBarrierMgr[] = "/PML-BarrierMgr";


rtems_attribute setBarrierAttribute( bool automatic )
{
  rtems_attribute attribs;

  if ( automatic ) { attribs = RTEMS_BARRIER_AUTOMATIC_RELEASE ; }
  else             { attribs = RTEMS_BARRIER_MANUAL_RELEASE; }
    
  return attribs;
}


void RtemsModelBarrierMgr_Teardown( void *arg )
{
  RtemsModelBarrierMgr_Context *ctx;

  ctx = arg;

  rtems_status_code   sc;
  rtems_task_priority prio;

  T_log( T_NORMAL, "Teardown" );

  prio = 0;
  sc = rtems_task_set_priority( RTEMS_SELF, M_PRIO_HIGH, &prio );
  T_rsc_success( sc );
  T_eq_u32( prio, M_PRIO_NORMAL );

  DeleteTask(ctx->worker0_id);
  DeleteTask(ctx->worker1_id);

  T_log( T_NORMAL, "Deleting Runner Semaphore" );
  DeleteTestSyncSema( ctx->runner_sema );
  T_log( T_NORMAL, "Deleting Worker0 Semaphore" );
  DeleteTestSyncSema( ctx->worker0_sema );
  T_log( T_NORMAL, "Deleting Worker1 Semaphore" );
  DeleteTestSyncSema( ctx->worker1_sema );
}


size_t RtemsModelBarrierMgr_Scope( void *arg, char *buf, size_t n )
{
  RtemsModelBarrierMgr_Context *ctx;
  size_t m;
  int p10;
  int tnum ;
  char digit;

  ctx = arg;
  p10 = BAR_PWR_OF_10;

  m = T_str_copy(buf, PromelaModelBarrierMgr, n);
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

void RtemsModelBarrierMgr_Cleanup(
  RtemsModelBarrierMgr_Context *ctx
)
{
  rtems_status_code sc;

  if (ctx->barrier_id != 0) {
    sc = rtems_barrier_delete(ctx->barrier_id);
    if ( sc != RTEMS_SUCCESSFUL ) {
      T_quiet_rsc( sc, RTEMS_INVALID_ID );
    }
  }
}
