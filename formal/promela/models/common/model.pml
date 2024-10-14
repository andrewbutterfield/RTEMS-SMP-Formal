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
  *  We continue with bits of Promela code of general utility
  */

inline nl() { printf("\n") } // Useful shorthand