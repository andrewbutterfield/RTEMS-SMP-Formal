/* SPDX-License-Identifier: BSD-2-Clause */

#ifndef _TR_MODEL_MESSAGE_MGR_H
#define _TR_MODEL_MESSAGE_MGR_H

#include "tr-model-0.h"

#ifdef __cplusplus
extern "C" {
#endif


/*
 * Run Setup/Cleanup structs/functions
 */
typedef struct {
  int this_test_number; // test number used to identify a test runner instance
  rtems_id receiver_id; // receiver ID used for the event send action.
  rtems_status_code send_status; // status of the message send action.
  rtems_option receive_option_set; // option set used for the message receive action
  rtems_interval receive_timeout; // timeout used for the message receive action
  rtems_status_code receive_status; // status of the message receive action
  rtems_status_code create; //status of the messsge queue create action
  rtems_attribute msg_queue_attr;

  rtems_id queue_id;
  uint8_t send_msg_counter; 
  size_t receive_size; //size of messages recieved by receive

  Thread_Control *runner_thread; // TCB of the runner task
  rtems_id runner_id; // ID of the runner task
  rtems_id worker1_id; // task ID of the worker task
  rtems_id worker2_id;
  rtems_id worker1_wakeup; // ID of the semaphore used to wake up the worker task
  rtems_id worker2_wakeup;
  rtems_id runner_wakeup; // ID of the semaphore used to wake up the runner task
  rtems_id runner_sched; // scheduler ID of scheduler used by the runner task
  rtems_id other_sched; // scheduler ID of another scheduler
                        // which is not used by the runner task
  T_thread_switch_log_4 thread_switch_log; // thread switch log
} RtemsModelMessageMgr_Context;

#define POWER_OF_10 100

#define WORKER_ATTRIBUTES RTEMS_DEFAULT_ATTRIBUTES

#define MAX_TLS_SIZE RTEMS_ALIGN_UP( 64, RTEMS_TASK_STORAGE_ALIGNMENT )

typedef RtemsModelMessageMgr_Context Context;

void RtemsModelMessageMgr_Setup_Wrap( void *arg ) ;

void RtemsModelMessageMgr_Teardown_Wrap( void *arg ) ;

size_t RtemsModelMessageMgr_Scope( void *arg, char *buf, size_t n ) ;

void RtemsModelMessageMgr_Cleanup( RtemsModelMessageMgr_Context *ctx );


/**
 * @addtogroup RTEMSTestCaseRtemsModelMessageMgr_Run
 *
 * @{
 */

/**
 * @brief Runs the parameterized test case.
 *
 */

void RtemsModelMessageMgr_Run0(void);

void RtemsModelMessageMgr_Run1(void);

void RtemsModelMessageMgr_Run2(void);

void RtemsModelMessageMgr_Run3(void);

void RtemsModelMessageMgr_Run4(void);

void RtemsModelMessageMgr_Run5(void);

void RtemsModelMessageMgr_Run6(void);

void RtemsModelMessageMgr_Run7(void);

void RtemsModelMessageMgr_Run8(void);

void RtemsModelMessageMgr_Run9(void);

void RtemsModelMessageMgr_Run10(void);

void RtemsModelMessageMgr_Run11(void);

void RtemsModelMessageMgr_Run12(void);

void RtemsModelMessageMgr_Run13(void);

void RtemsModelMessageMgr_Run14(void);

void RtemsModelMessageMgr_Run15(void);

void RtemsModelMessageMgr_Run16(void);

void RtemsModelMessageMgr_Run17(void);

void RtemsModelMessageMgr_Run18(void);

void RtemsModelMessageMgr_Run19(void);

void RtemsModelMessageMgr_Run20(void);

void RtemsModelMessageMgr_Run21(void);

void RtemsModelMessageMgr_Run22(void);


/** @} */

#ifdef __cplusplus
}
#endif

#endif /* _TR_EVENT_SEND_RECEIVE_H */
