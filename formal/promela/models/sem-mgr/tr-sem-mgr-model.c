/* SPDX-License-Identifier: BSD-2-Clause */

/**
 * @file
 *
 * @ingroup RTEMSTestCaseRtemsModelSemVal
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

#include "tr-sem-mgr-model.h"


static const char PromelaModelSemMgr[] = "/PML-SemMgr";

rtems_attribute setSemaphoreAttributes( bool scope, bool priority
                                      , int semtype, int locking )
{
  rtems_attribute attribs;

  if ( scope ) { attribs = RTEMS_GLOBAL;}
  else {attribs = RTEMS_LOCAL; }
  
  if (priority) { attribs |= RTEMS_PRIORITY;}
  else {attribs |= RTEMS_FIFO;}
  
  if ( semtype == 0) { attribs |= RTEMS_COUNTING_SEMAPHORE;}
  else if (semtype==1) {attribs |= RTEMS_BINARY_SEMAPHORE;}
  else {attribs |= RTEMS_SIMPLE_BINARY_SEMAPHORE;}
  
  if (locking == 1) {attribs |= RTEMS_INHERIT_PRIORITY;}
  else if (locking == 2) {attribs |= RTEMS_PRIORITY_CEILING;}
  else if (locking == 3) { attribs |= RTEMS_MULTIPROCESSOR_RESOURCE_SHARING;}
  
  return attribs;
}

void RtemsModelSemMgr_Teardown( void *arg )
{
  RtemsModelSemMgr_Context *ctx;

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

size_t RtemsModelSemMgr_Scope( void *arg, char *buf, size_t n )
{
  RtemsModelSemMgr_Context *ctx;
  size_t m;
  int p10;
  int tnum ;
  char digit;

  ctx = arg;
  p10 = SEM_PWR_OF_10;

  m = T_str_copy(buf, PromelaModelSemMgr, n);
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

void RtemsModelSemMgr_Cleanup(
  RtemsModelSemMgr_Context *ctx
)
{
  rtems_status_code sc;

  if (ctx->sem_id != 0) {
    sc = rtems_semaphore_delete(ctx->sem_id);
    if ( sc != RTEMS_SUCCESSFUL ) {
      T_quiet_rsc( sc, RTEMS_INVALID_ID );
    }
  }
  
  if (ctx->sem_id2 != 0) {
    sc = rtems_semaphore_delete(ctx->sem_id2);
    if ( sc != RTEMS_SUCCESSFUL ) {
      T_quiet_rsc( sc, RTEMS_INVALID_ID );
    }
  }
}
