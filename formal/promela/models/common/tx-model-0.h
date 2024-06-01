/* SPDX-License-Identifier: BSD-2-Clause */

#ifndef _TR_MODEL_0_H
#define _TR_MODEL_0_H

#include <rtems.h>
#include <rtems/score/thread.h>

#include <rtems/test.h>

#ifdef __cplusplus
extern "C" {
#endif


typedef enum {
  M_PRIO_HIGH = 1,
  M_PRIO_NORMAL,
  M_PRIO_LOW,
  M_PRIO_OTHER
} Priorities;


rtems_id CreateWakeupSema( void );

void DeleteWakeupSema( rtems_id id );

void Wait( rtems_id id );

void Wakeup( rtems_id id ) ;

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