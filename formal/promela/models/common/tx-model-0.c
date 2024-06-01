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

#include "tx-model-0.h"

rtems_id CreateWakeupSema( void )
{
  rtems_status_code sc;
  rtems_id id;

  sc = rtems_semaphore_create(
    rtems_build_name( 'W', 'K', 'U', 'P' ),
    0,
    RTEMS_SIMPLE_BINARY_SEMAPHORE,
    0,
    &id
  );
  T_assert_rsc_success( sc );

  return id;
}

void DeleteWakeupSema( rtems_id id )
{
  if ( id != 0 ) {
    rtems_status_code sc;

    sc = rtems_semaphore_delete( id );
    T_rsc_success( sc );
  }
}

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

rtems_option mergeopts( bool wait, bool wantall )
{
  rtems_option opts;

  if ( wait ) { opts = RTEMS_WAIT; }
  else { opts = RTEMS_NO_WAIT; } ;
  if ( wantall ) { opts |= RTEMS_EVENT_ALL; }
  else { opts |= RTEMS_EVENT_ANY; } ;
  return opts;
}

rtems_interval getTimeout( int timeout )
{
  rtems_interval tout;

  if ( timeout == 0 ) { tout = RTEMS_NO_TIMEOUT; }
  else { tout = timeout; } ;
  return tout;
}

rtems_id idNull( rtems_id queue_id, bool passedid  )
{
  if ( passedid ) { return queue_id; }
  else { return 0xffffffff; }
}

void checkTaskIs( rtems_id expected_id )
{
  rtems_id own_id;

  own_id = _Thread_Get_executing()->Object.id;
  T_eq_u32( own_id, expected_id );
}

void initialise_semaphore( int sema_no,
                           rtems_id semaphore_id, 
                           rtems_id semaphore[] )
{
  semaphore[sema_no] = semaphore_id;
}

void ShowWorkerSemaId( int worker_num, rtems_id work_wake ) {
  T_printf( "L:Worker%d wakeup semaphore = %d\n", worker_num, work_wake );
}

void ShowRunnerSemaId( rtems_id run_wake ) {
  T_printf( "L:runner wakeup sema = %d\n", run_wake );
}



