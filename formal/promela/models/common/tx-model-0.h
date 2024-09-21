/* SPDX-License-Identifier: BSD-2-Clause */

#ifndef _TR_MODEL_0_H
#define _TR_MODEL_0_H

#include <rtems.h>
#include <rtems/score/thread.h>

#include <rtems/test.h>

#ifdef __cplusplus
extern "C" {
#endif

// #define POWER_OF_10 ... - not defined here, model-specific

typedef enum {
  M_PRIO_HIGH = 1,
  M_PRIO_NORMAL,
  M_PRIO_LOW,
  M_PRIO_OTHER
} Priorities;


rtems_id CreateTestSyncSema( char * name );

void DeleteTestSyncSema( rtems_id id );

void ObtainTestSyncSema( rtems_id id );

void ReleaseTestSyncSema( rtems_id id ) ;

void initialise_id ( rtems_id * id );

rtems_option mergeopts( bool wait, bool wantall );

rtems_interval getTimeout( int timeout ) ;

rtems_id idNull( rtems_id queue_id, bool passedid ) ;

void checkTaskIs( rtems_id expected_id ) ;

void initialise_semaphore( int sema_no,
                           rtems_id semaphore_id, 
                           rtems_id semaphore[] );

void ShowRunnerSemaId( rtems_id run_wake ) ;

void ShowWorkerSemaId( int worker_num, rtems_id work_wake ) ;

#endif