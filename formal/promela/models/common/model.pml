/* SPDX-License-Identifier: BSD-2-Clause */

/*
 * PML Modelling code common to all/most models
 *
 *  - Common Task Definition
 *  - Simple Binary Semaphores for Test Synchronisation
 *
 * IMPORTANT: 
 *  a model must #define TASK_MAX and SEMA_MAX *before* #including this file.
 */

 /*
 *  Common Task Definition
 *
 *  need text here to explain usage
 */
typedef Task {
  byte nodeid; // So we can spot remote calls
  byte pmlid; // Promela process id
  mtype state ; // {Zombie,Dormant,Ready,TimeWait,OtherWait,...}
  bool preemptable;
  byte prio; // lower number is higher priority
  int ticks; // clock ticks to keep track of timeout
  bool tout; // true if woken by a timeout
  bool isr;     // If task is woken from Interrupt context
};
Task tasks[TASK_MAX]; // tasks[0] models a NULL dereference
#define BAD_ID TASK_MAX   // this ID and higher are considered invalid

/*
 *  Simple Binary Semaphores for Test Synchronisation
 *
 *  need text here to explain usage
 */

 /*
 * Synchronisation Mechanisms
 *  TestSyncObtain(sem_id)   - call that waits to obtain semaphore `sem_id`
 *  TestSyncRelease(sem_id)  - call that releases semaphore `sem_id`
 *  TestSyncReleased(sem_id) - simulates ecosystem behaviour releases `sem_id`
 *
 * Binary semaphores:  True means available, False means in use.
 */

bool test_sync_sema[SEMA_MAX]; // Semaphore

inline TestSyncObtain(sem_id){
  atomic{
    printf("@@@ %d WAIT %d\n",_pid,sem_id);
    test_sync_sema[sem_id] ;        // wait until available
    test_sync_sema[sem_id] = false; // set as in use
    printf("@@@ %d LOG WAIT %d Over\n",_pid,sem_id);
  }
}

inline TestSyncRelease(sem_id){
  atomic{
    printf("@@@ %d SIGNAL %d\n",_pid,sem_id);
    test_sync_sema[sem_id] = true ; // release
  }
}

inline TestSyncReleased(sem_id)
{
  test_sync_sema[sem_id] = true ;
}



 /*
  *  We finish off with bits of Promela code of general utility
  */

inline nl() { printf("\n") } // Useful shorthand