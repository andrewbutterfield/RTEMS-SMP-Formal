/* SPDX-License-Identifier: BSD-2-Clause */

/*
 * PML Modelling code common to all/most models
 *
 * IMPORTANT: 
 *  a model must #define TASK_MAX and SEMA_MAX *before* #including this file.
 *
 * We start with return code, options, attributes
 */

// values equal or greater than this denote invalid task ids
#define BAD_ID TASK_MAX   

// Return Values
// Defined in cpukit/include/rtems/rtems/status.h
#define RC_OK      0  // RTEMS_SUCCESSFUL 
#define RC_InvName 3  // RTEMS_INVALID_NAME 
#define RC_InvId   4  // RTEMS_INVALID_ID 
#define RC_TooMany 5  // RTEMS_TOO_MANY 
#define RC_Timeout 6  // RTEMS_TIMEOUT 
#define RC_Deleted 7  // RTEMS_OBJECT_WAS_DELETED 
#define RC_InvSize 8 // RTEMS_INVALID_SIZE
#define RC_InvAddr 9  // RTEMS_INVALID_ADDRESS 
#define RC_InvNum  10 // RTEMS_INVALID_NUMBER 
#define RC_NotDefd  11 // RTEMS_NOT_DEFINED
#define RC_RsrcInUse 12 // RTEMS_RESOURCE_IN_USE
#define RC_Unsat  13 // RTEMS_UNSATISFIED 
#define RC_InvPrio 19 // RTEMS_INVALID_PRIORITY
#define RC_NotOwner 23 // RTEMS_NOT_OWNER_OF_RESOURCE

// Option Set Values
// Defined in cpukit/include/rtems/rtems/options.h
/*** 
#define RTEMS_DEFAULT_OPTIONS 0x00000000
#define RTEMS_EVENT_ALL       0x00000000
#define RTEMS_EVENT_ANY       0x00000002
#define RTEMS_NO_WAIT         0x00000001
#define RTEMS_WAIT            0x00000000
***/

mtype = {
  Wait, NoWait  // Waiting options
, All, Any      // Satisfaction options
}

// Attribute Set Values
// Defined in cpukit/include/rtems/rtems/attr.h
/***
#define RTEMS_APPLICATION_TASK                   0x00000000
#define RTEMS_BARRIER_AUTOMATIC_RELEASE          0x00000200
#define RTEMS_BARRIER_MANUAL_RELEASE             0x00000000
#define RTEMS_BINARY_SEMAPHORE                   0x00000010
#define RTEMS_COUNTING_SEMAPHORE                 0x00000000
#define RTEMS_DEFAULT_ATTRIBUTES                 0x00000000
#define RTEMS_FIFO                               0x00000000
#define RTEMS_FLOATING_POINT                     0x00000001
#define RTEMS_GLOBAL                             0x00000002
#define RTEMS_INHERIT_PRIORITY                   0x00000040
#define RTEMS_LOCAL                              0x00000000
#define RTEMS_MULTIPROCESSOR_RESOURCE_SHARING    0x00000100
#define RTEMS_NO_FLOATING_POINT                  0x00000000
#define RTEMS_NO_INHERIT_PRIORITY                0x00000000
#define RTEMS_NO_MULTIPROCESSOR_RESOURCE_SHARING 0x00000000
#define RTEMS_NO_PRIORITY_CEILING                0x00000000
#define RTEMS_PRIORITY                           0x00000004
#define RTEMS_PRIORITY_CEILING                   0x00000080
#define RTEMS_SEMAPHORE_CLASS                    0x00000030
#define RTEMS_SIMPLE_BINARY_SEMAPHORE            0x00000020
#define RTEMS_SYSTEM_TASK                        0x00008000
***/

/*
 * Scheduler Task States
 *   see Classic API, Scheduler Concepts, Background, Task State Transitions
 *
 * States: Non-existent, Dormant, Ready, Executing, Blocked
 *
 * We often want to model WHY something is Blocked:
 *   TimeWait  --  usually when waiting on a timeout
 *   BarrierWait --  waiting for a barrier to be released
 *   EventWait -- waiting for an event-set to be received
 *   MsgWait -- waiting for a message to be queued
 *   SemaWait -- waiting to acquire a semaphore
 *   PrioWait -- waiting for higher priority to yield/block/delete (?)
 *   OtherWait -- all other blocking conditions
 *
 *   We use Zombie for a deleted task at the end of a scenario
 *   We don't explicitly model Executing at present
 *   We haven't used Dormant yet but will need it for the Task Manager model
 */
mtype = {
  Zombie, Dormant, Ready , OtherWait, TimeWait, 
, BarrierWait, EventWait, MsgWait, PrioWait, SemaWait
}
/*
 * Transitions  (from-state(s) --Transition--> to-state ):
 *   Non-existent --Creating--> Dormant
 *   Dormant          --Starting-->     Ready
 *   Ready            --Dispatching-->  Executing
 *   Ready,Executing  --Blocking-->     Blocked
 *   Executing        --Yielding-->     Ready
 *   Blocked          --Readying-->     Ready
 *   existent         --Deleting-->     Non-existent
 *
 * We don't need mtype values for these.
 */

 /*
  *  We continue with bits of Promela code of general utility
  */

inline nl() { printf("\n") } // Useful shorthand