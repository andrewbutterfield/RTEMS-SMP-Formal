/* SPDX-License-Identifier: BSD-2-Clause */

/*
 * PML Modelling code common to all/most models
 *
 *  - Simple Binary Semaphores for Test Synchronisation
 *
 * IMPORTANT: 
 *  a model must #define TASK_MAX and SEMA_MAX *before* #including this file.
 */

// values equal or greater than this denote invalid task ids
#define BAD_ID TASK_MAX   

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

bool semaphore[SEMA_MAX]; // Semaphore

inline TestSyncObtain(sem_id){
  atomic{
    printf("@@@ %d WAIT %d\n",_pid,sem_id);
    semaphore[sem_id] ;        // wait until available
    semaphore[sem_id] = false; // set as in use
    printf("@@@ %d LOG WAIT %d Over\n",_pid,sem_id);
  }
}

inline TestSyncRelease(sem_id){
  atomic{
    printf("@@@ %d SIGNAL %d\n",_pid,sem_id);
    semaphore[sem_id] = true ; // release
  }
}

inline TestSyncReleased(sem_id)
{
  semaphore[sem_id] = true ;
}



 /*
  *  We finish off with bits of Promela code of general utility
  */

inline nl() { printf("\n") } // Useful shorthand