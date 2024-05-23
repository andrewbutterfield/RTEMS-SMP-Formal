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
  PRIO_HIGH = 1,
  PRIO_NORMAL,
  PRIO_LOW,
  PRIO_OTHER
} Priorities;


rtems_id CreateWakeupSema( void );

void DeleteWakeupSema( rtems_id id );

void Wait( rtems_id id );

void Wakeup( rtems_id id ) ;

rtems_event_set GetPending( Context *ctx );

rtems_option mergeopts( bool wait );

rtems_interval getTimeout( int timeout ) ;

rtems_id idNull( Context *ctx, bool passedid ) ;

rtems_id mapid( Context *ctx, int pid ) ;

void checkTaskIs( rtems_id expected_id ) ;

void ShowWorkerSemaId( Context *ctx ) ;

void ShowRunnerSemaId( Context *ctx ) ;

void initialise_semaphore( Context *ctx, rtems_id semaphore[] );
