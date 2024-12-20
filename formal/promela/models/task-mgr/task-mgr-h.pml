#define NUM_PROC 5

// We use two semaphores to synchronise the tasks
#define INVALID_ENTRY       (0)
#define SEMA_TASK_START_0 	(1)
#define SEMA_TASK_START_1  	(2)
#define SEMA_LOCK           (3)
#define SEMA_TASK0_FIN      (4)
#define SEMA_TASK1_FIN   	(5)

/*
 * We need to output annotations for any #define we use.
 * It is simplest to keep them all together,
 * and use an inline to output them.
 */

#define MAX_PRIO        255
#define BAD_PRIO        MAX_PRIO
#define CURRENT_PRIO    0
#define LOW_PRIO        1
#define MED_PRIO        5
#define HIGH_PRIO       10
#define ISR_PRIO        11

#define INVALID_ID      0
#define RUNNER_ID       1
#define TASK0_ID        2
#define TASK1_ID        3

#define CLEAR_TASKS     255

byte task_control = CLEAR_TASKS;

chan interrupt_channel = [1] of { byte, byte };

//byte priority_map[SCHED_MAX][TASK_MAX];

inline outputDefines () {

    printf("@@@ %d DEF TASK_MAX %d\n",_pid,TASK_MAX);
    printf("@@@ %d DEF INVALID_ID %d\n",_pid,INVALID_ID);
    printf("@@@ %d DEF SEMA_MAX %d\n",_pid,SEMA_MAX);

    // Priority inversion
    printf("@@@ %d DEF LOW_PRIO %d\n",_pid,HIGH_PRIO);
    printf("@@@ %d DEF MED_PRIO %d\n",_pid,MED_PRIO);
    printf("@@@ %d DEF HIGH_PRIO %d\n",_pid,LOW_PRIO);
	
	printf("@@@ %d DEF RC_OK RTEMS_SUCCESSFUL\n",_pid);
	printf("@@@ %d DEF RC_InvId RTEMS_INVALID_ID\n",_pid);
	printf("@@@ %d DEF RC_InvAddr RTEMS_INVALID_ADDRESS\n",_pid);
	printf("@@@ %d DEF RC_Unsat RTEMS_UNSATISFIED\n",_pid);
	printf("@@@ %d DEF RC_Timeout RTEMS_TIMEOUT\n",_pid);
}

inline outputDeclarations () {
    printf("@@@ %d DECL byte createRC 0\n",_pid);
    printf("@@@ %d DECL byte startRC 0\n",_pid);
    printf("@@@ %d DECL byte deleteRC 0\n",_pid);
    printf("@@@ %d DECL byte suspendRC 0\n",_pid);
    printf("@@@ %d DECL byte isSuspendRC 0\n",_pid);
    printf("@@@ %d DECL byte resumeRC 0\n",_pid);
    printf("@@@ %d DECL byte setPriorityRC 0\n",_pid);
    // Rather than refine an entire Task array, we refine array 'slices'
    //printf("@@@ %d DCLARRAY EvtSet pending TASK_MAX\n",_pid);
    //printf("@@@ %d DCLARRAY byte recout TASK_MAX\n",_pid);
    printf("@@@ %d DCLARRAY byte taskID TASK_MAX\n", _pid);
    printf("@@@ %d DCLARRAY Task tasks TASK_MAX\n",_pid);
    printf("@@@ %d DCLARRAY Semaphore semaphore SEMA_MAX\n",_pid);
}

typedef Mode {
    bool preempt;
    bool timeslice;
    bool ASR;
    int isr_lvl;
}

inline isNameValid(name, rc) {
    if
    ::  name == 0 ->
            rc = false;
    ::  else -> 
            rc = true;
    fi
}

inline setTask(tid, rc) {
    // Allocate the lowest available task ID
    // to the newly created task.
    atomic {
        byte raw_tid;
        //TestSyncObtain(SEMA_TASKCONTROL);
        raw_tid = task_control & (~task_control + 1);
        task_control = task_control - raw_tid;
        //TestSyncRelease(SEMA_TASKCONTROL);
        rc = true;

        if
        ::  raw_tid == 2 ->
                tid = 1;
        ::  raw_tid == 4 ->
                tid = 2;
        ::  raw_tid == 8 ->
                tid = 3;
        ::  raw_tid == 16 ->
                tid = 4;
    /*    
        ::  raw_tid == 32 ->
                tid = 5;
        ::  raw_tid == 64 ->
                tid = 6;
        ::  raw_tid == 128 ->
                tid = 7;
    */
        ::  else ->
                tid = 1;
                rc = false;
        fi
    }
}

inline removeTask(tid, rc) {
    byte raw_tid = 1 << tid;
    //TestSyncObtain(SEMA_TASKCONTROL);
    if
    ::  (task_control & raw_tid) != raw_tid ->
            task_control = task_control + raw_tid;
            rc = true;
    ::  (task_control & raw_tid) == raw_tid ->
            rc = false;
    fi
    //TestSyncRelease(SEMA_TASKCONTROL);
}

inline isHoldingMutex(tid, holding, rc) {
    /*
    If a given task is holding any bin semaphores
    which use a locking protocol: 
    return true, else false
    */
    atomic {
        holding = false;
        if
        ::  tid >= TASK_MAX ->
                rc = false;
        ::  tid == 0 ->
                rc = false;
        ::  else ->
                byte mutID = 0;
                do
                ::  mutID < SEMA_MAX ->
                        if
                        ::  tasks[tid].mutexs[mutID] == 1 ->
                                holding = true;
                        ::  else
                        fi
                else -> break;
                od
        fi
    }
}

inline ObtainMutex(tid, sid) {
    TestSyncObtain(sid);
    tasks[tid].mutexs[sid] = 1;
    tasks[tid].HoldingMutex = true;
}

inline ReleaseMutex(tid, sid) { 
    bool rc; // TODO 
    if
    ::  tasks[tid].mutexs[sid] == 1 ->
            TestSyncRelease(sid);
            isHoldingMutex(tid, tasks[tid].HoldingMutex, rc);
    ::  else -> rc = false
    fi
}
