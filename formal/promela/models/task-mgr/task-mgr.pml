/* SPDX-License-Identifier: BSD-2-Clause */

/*
 * task-mgr-model.pml
 *
 * Copyright (C) 2019-2021 Trinity College Dublin (www.tcd.ie)
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

/*
 * We need to output annotations for any #define we use.
 * It is simplest to keep them all together,
 * and use an inline to output them.
 */

#include "../common/rtems.pml"
#define TASK_MAX 5 
#define SEMA_MAX 6
#define SCHED_MAX 1
#include "../common/model.pml"

#include "task-mgr-h.pml"
#include "task-mgr-API.pml"

byte sendrc;            // Sender global variable
byte recrc;             // Receiver global variable
byte recout[TASK_MAX] ; // models receive 'out' location.

// Create global variables for scenarios

// Model return status
byte createRC;
byte startRC;
byte deleteRC;
byte suspendRC;
byte isSuspendRC;
byte resumeRC;

// Task Create
bool task_0_name;
byte tsk0_id;
byte createPrio;
bool createValId;

bool createTask;

// Task Start
byte taskEntry;
bool startValId;
bool startValEntry;
bool doubleStart;

bool startTask;

// Task Delete
byte deleteId;

bool deleteTask;

// Task Suspend/Resume
byte suspendId;
byte resumeId;
bool suspValId;
bool resumeValId;
bool doubleSuspend;
bool suspendSelf;

bool suspendTask;

// Priority

byte task_1_name;
byte tsk1_ID;
byte task_1_Entry;

bool testPrio;
bool raiseWithMutex;

// Declare Scenario Types
mtype = {CreateDestroy, TaskStart, SuspResume, ChangePrio}

inline chooseScenario() {

    // Defaults
    task_control = 28;	// 0001 1100 Task[1] reserved for runner.
    
    // Initialise scenario variables.

    // Task Create
    createTask = true;
    task_0_name = 1;
	createPrio = MED_PRIO;
	createValId = true;

    // Start Task
    startTask = true;
	startValId = true;
    startValEntry = true;
	doubleStart = false;
	taskEntry = SEMA_TASK_START_0;

    // Delete Task
	deleteTask = true;
    deleteId = INVALID_ID;

    // Suspend
    suspendTask = false;
    suspendId = INVALID_ID;
    suspValId = true;
    doubleSuspend = false;
    suspendSelf = false;
    // Resume
    resumeId = INVALID_ID;
    resumeValId = true;

    // Priority
    task_1_name = 2;
    task_1_Entry = SEMA_TASK_START_1;

    testPrio = false;
    raiseWithMutex = false;

    // Set runner task state to Ready
    // as this task is active from the start of all scenarios.
    tasks[RUNNER_ID].state = Ready;

    if
    ::  scenario = CreateDestroy;
    ::  scenario = TaskStart;
    ::  scenario = SuspResume;
    ::  scenario = ChangePrio;
    fi

    atomic{printf("@@@ %d LOG scenario ",_pid); printm(scenario); nl()} ;

    // Create/Delete
    if
    ::  scenario == CreateDestroy ->
            startTask = false; 
            deleteTask = false;
            // Create/Delete
            if
            ::  task_0_name = 0;                        atomic{printf("@@@ %d LOG Create: Invalid Name ",_pid); printm(scenario); nl()};
            ::  createPrio = 0;                         atomic{printf("@@@ %d LOG Create: Invalid Priority (0) ",_pid); printm(scenario); nl()};
            ::  createPrio = MAX_PRIO;                  atomic{printf("@@@ %d LOG Create: Invalid Priority (MAX) ",_pid); printm(scenario); nl()};
            ::  createValId = false;                    atomic{printf("@@@ %d LOG Create: Invalid Id ",_pid); printm(scenario); nl()};
//TODO      ::  scenario = TooMany;
            ::  createTask = false; deleteTask = true;  atomic{printf("@@@ %d LOG Delete: Invalid Id ",_pid); printm(scenario); nl()};
            ::  deleteTask = true;                      atomic{printf("@@@ %d LOG Create: Success ",_pid); printm(scenario); nl()};
            fi
    ::  scenario == TaskStart ->
            startTask = false;
            // Start
            if
            ::  startValId = false;         atomic{printf("@@@ %d LOG Start: Invalid Id ",_pid); printm(scenario); nl()};
            ::  startValEntry = false;      atomic{printf("@@@ %d LOG Start: Invalid Entry ",_pid); printm(scenario); nl()};
            ::  doubleStart = true;         atomic{printf("@@@ %d LOG Start: Task Already Started ",_pid); printm(scenario); nl()};
            ::  startTask = true;           atomic{printf("@@@ %d LOG Start: Success ",_pid); printm(scenario); nl()};
            fi
    ::  scenario == SuspResume ->
            suspendTask = true;
            // Suspend
            if
            ::  startValEntry = false; startTask = false;   atomic{printf("@@@ %d LOG Start: Invalid State for Suspend",_pid); printm(scenario); nl()};
            ::  suspValId = false;                          atomic{printf("@@@ %d LOG Start: Invalid Suspend Id ",_pid); printm(scenario); nl()};
            ::  resumeValId = false;                        atomic{printf("@@@ %d LOG Start: Invalid Resume Id ",_pid); printm(scenario); nl()};
            ::  doubleSuspend = true;                       atomic{printf("@@@ %d LOG Start: Already Suspended ",_pid); printm(scenario); nl()};
            ::  suspendSelf = true; suspendTask = false;    atomic{printf("@@@ %d LOG Start: Self Suspend ",_pid); printm(scenario); nl()};
            ::  skip;                                       atomic{printf("@@@ %d LOG Start: Suspend/Resume ",_pid); printm(scenario); nl()};
            fi
    ::  scenario == ChangePrio ->
            // Set Priority
            testPrio = true;
            if
            ::  suspendSelf = true;         atomic{printf("@@@ %d LOG Start: SuspendSelf",_pid); printm(scenario); nl()};
            ::  raiseWithMutex = true;      atomic{printf("@@@ %d LOG Start: Lower Priority while holding lock",_pid); printm(scenario); nl()};
            ::  skip;                       atomic{printf("@@@ %d LOG Start: Lower Task0, Raise Task1",_pid); printm(scenario); nl()};
            fi
    fi
}

inline SuspendResume(suspId, resumeId) {
    bool repeated = false;

suspRepeat:
    // Suspend
    printf("@@@ %d CALL task_suspend %d suspendRC\n", 
                _pid, suspId, suspendRC);
    task_suspend(tasks[suspId], suspendRC);
    printf("@@@ %d SCALAR suspendRC %d\n",_pid,suspendRC);

    // Scenario: Already Suspended
    if
    ::  doubleSuspend == true && repeated == false ->
            repeated = true;
            goto suspRepeat;
    ::  else
    fi
    //Check is suspended
    //...

    //Resume
    printf("@@@ %d CALL task_resume %d resumeRC\n", 
                _pid, resumeId, resumeRC);
    task_resume(tasks[resumeId], resumeRC);
    printf("@@@ %d SCALAR resumeRC %d\n",_pid,resumeRC);

}

inline changePriority (taskid, prio, oldPrio, rc) {
    // Change the Priority of the given task
    // If prio = 0 -> returns current Priority with no update.
    printf("@@@ %d CALL task_setPriority %d %d %d setPriorityRC\n", 
                            _pid, taskid, prio, old_prio, rc);
    task_setPrio(taskid, prio, old_prio, rc);
    printf("@@@ %d CALL oldPrio %d\n",_pid, old_prio);
    printf("@@@ %d SCALAR setPriorityRC %d\n",_pid,rc);
}

proctype Runner(byte nid, taskid) {
    assert(_priority == MED_PRIO)
    /*
    if
    :: multicore ->
        // printf("@@@ %d CALL RunnerScheduler %d\n", _pid, rcvCore);
        printf("@@@ %d CALL SetProcessor %d\n", _pid, rcvCore);
    :: else
    fi
    */
    // Runner Task Params
    tasks[taskid].nodeid = nid;
    tasks[taskid].pmlid = _pid;
    tasks[taskid].state = Ready;

	// Task 0 Create Params
	byte name = task_0_name;
    byte prio = createPrio;
    byte preempt = true;
	byte mode = 0;
	byte attr = 0;
	bool setRC;
	
	// Task 0 Start Params 
	byte entry = taskEntry;
	bool doubleDone = false;
	byte startId;
	//byte args = 0;

    // Procedure for Creating Task0
    if 
    ::  createTask == true ->
		if
		::	createValId == true ->
				setTask(tsk0_id, setRC);
				if 
				::	setRC == false ->
						printf("@@@ %d CALL TooMany\n", _pid);
				:: 	else
				fi
		::	else ->
				tsk0_id = 0;
				setRC = true;
		fi

		printf("@@@ %d CALL task_create %d %d %d %d %d createRC\n", 
				_pid, name, prio, mode, attr, tsk0_id);

        task_create(tasks[tsk0_id], tsk0_id, name, prio, preempt, setRC, createRC);
		
		printf("@@@ %d SCALAR createRC %d\n", _pid, createRC);
    ::  else
    fi

    // Procedure for Starting Task0
    if 
    ::  startTask == true ->
            if
            ::	startValId == true ->
                    startId = tsk0_id;
            :: 	startValId == false ->
                    startId = INVALID_ID;
            fi

            if
            ::  startValEntry == true ->
                    entry = SEMA_TASK_START_0;
            ::  startValEntry == false ->
                    entry = INVALID_ENTRY;
            fi
repeat_start:
            task_start(tasks[startId], entry, startRC);
            printf("@@@ %d CALL task_start %d %d startRC\n", 
                    _pid, startId, entry);
            printf("@@@ %d CALL startRC %d\n", _pid, startRC);
            if
            ::	startRC != RC_OK ->
                    TestSyncRelease(SEMA_TASK0_FIN);
            :: 	doubleStart == true ->
                // Scenario: Already Started
                    if 
                    ::	doubleDone == false ->
                        doubleDone = true;
                        goto repeat_start;
                    :: else
                    fi
            :: else
            fi
    ::  else -> skip
    fi

    // Procedure for Creating and Starting Task0
    if
    ::  testPrio == true ->
            // Create and Start New Task (1)
            setTask(tsk1_ID, setRC);
            printf("@@@ %d CALL task_create %d %d %d %d %d createRC\n", 
                    _pid, task_1_name, prio, mode, attr, tsk1_ID);
            task_create(tasks[tsk1_ID], tsk1_ID, task_1_name, prio, preempt, setRC, createRC);
            printf("@@@ %d SCALAR createRC %d\n", _pid, createRC);
            //
            task_start(tasks[tsk1_ID], task_1_Entry, startRC);
            printf("@@@ %d CALL task_start %d %d startRC\n", 
                    _pid, tsk1_ID, task_1_Entry);
            printf("@@@ %d CALL startRC %d\n", _pid, startRC);
    ::  else -> skip
    fi

    // Procedure for Resuming Task0 once it suspends itself
    if
    ::  suspendSelf == true ->
            //Resume
            // Wait for Task 0 to self Suspend
            printf("@@@ %d CALL WaitForSuspend %d resumeRC\n", 
                        _pid, tsk0_id, resumeRC);
            do
            ::  isSuspendRC == RC_AlrSuspd -> break;
            ::  else -> 
                    task_isSuspend(tasks[tsk0_id], isSuspendRC);
            od

            printf("@@@ %d CALL task_resume %d resumeRC\n", 
                        _pid, tsk0_id, resumeRC);
            task_resume(tasks[tsk0_id], resumeRC);
            printf("@@@ %d SCALAR resumeRC %d\n",_pid,resumeRC);
    ::  else
    fi

    // Obtain Semaphores, indicating both Worker Tasks have completed.
    // TODO: Possibly replace with an event receive.
    if 
    ::	startTask == true ->
            TestSyncObtain(SEMA_TASK0_FIN);
    ::	else
    fi
    if
    ::  testPrio == true ->
            TestSyncObtain(SEMA_TASK1_FIN);
    ::	else
    fi   

    // Procedure for Suspending and Resuming Worker Task 1
    if
    ::  suspendTask == true ->
            if
            ::  suspValId == true ->
                    suspendId = tsk0_id;
            ::  else // Set to 0
            fi
            if
            ::  resumeValId == true ->
                    resumeId = tsk0_id;
            ::  else // Set to 0
            fi
            SuspendResume(suspendId, resumeId);
    ::  else 
    fi

    if
    ::  createTask == true ->
            deleteId = tsk0_id;
    ::  else
    fi

    // Check that Priorities of Tasks has changed
    // Scenario: ChangePrio
    if
    ::  testPrio == true ->
            // Check Priority of Two tasks before deletion:
            byte setPriorityRC;
            byte old_prio = 1;
            printf("@@@ %d DECL byte priority 0\n",_pid);
            // TSK0
            changePriority(tsk0_id, CURRENT_PRIO, old_prio, setPriorityRC);
            // TSK1
            changePriority(tsk1_ID, CURRENT_PRIO, old_prio, setPriorityRC);
    ::  else
    fi

    // Delete Worker Tasks before deleting Runner
    if
    ::  deleteTask == true -> 
			printf( "@@@ %d CALL task_delete %d deleteRC\n", _pid, deleteId);
			
            task_delete(tasks[deleteId], deleteId, deleteRC);

            printf("@@@ %d SCALAR delRC %d\n", _pid, deleteRC);

            if
            ::  testPrio == true ->
                    printf( "@@@ %d CALL task_delete %d deleteRC\n", _pid, tsk1_ID);
			
                    task_delete(tasks[tsk1_ID], tsk1_ID, deleteRC);

                    printf("@@@ %d SCALAR delRC %d\n", _pid, deleteRC);
            ::  else
            fi
    ::  else 
    fi


    // Once done, free runner task model id
    // and kill Interupts:
    interrupt_channel ! INVALID_ID, 0;

    bool runRC;
    removeTask(taskid, runRC);
    if
    ::  runRC == true ->
            tasks[taskid].state = Zombie;
    ::  else
    fi

}

proctype Task0(byte taskId) {
    assert(_priority == MED_PRIO);
    assert(taskId < TASK_MAX);
    /*
    if
    :: multicore ->
        // printf("@@@ %d CALL RunnerScheduler %d\n", _pid, rcvCore);
        printf("@@@ %d CALL SetProcessor %d\n", _pid, rcvCore);
    :: else
    fi
    */

    if
    ::  startTask == true ->
            TestSyncObtain(SEMA_TASK_START_0);
            TestSyncRelease(SEMA_TASK_START_0);

            tasks[taskId].pmlid = _pid;
            //set_priority(_pid, tasks[taskid].prio)

            //Do Stuff

            // Self Suspend:
            if
            ::  suspendSelf == true ->
                    // Suspend
                    printf("@@@ %d CALL task_suspend %d suspendRC\n", 
                                    _pid, tsk0_id, suspendRC);
                    task_suspend(tasks[tsk0_id], suspendRC);
                    printf("@@@ %d SCALAR suspendRC %d\n",_pid,suspendRC);
            ::  else 
            fi
            
            if
            ::  testPrio == true ->
                    byte setPriorityRC;
                    byte old_prio = 1;
                    
                    printf("@@@ %d DECL byte priority 0\n",_pid);

                    // Priority Changing 
                    if 
                    ::  raiseWithMutex == true ->
                            // Obtain Mutex:
                            ObtainMutex(taskId, SEMA_LOCK);
                    ::  else
                    fi

                    // Check Priority
                    changePriority(taskId, CURRENT_PRIO, old_prio, setPriorityRC);

                    // Chage Priority to High
                    changePriority(taskId, LOW_PRIO, old_prio, setPriorityRC);

                    // Check Priority
                    changePriority(taskId, CURRENT_PRIO, old_prio, setPriorityRC);
            
                    if 
                    ::  raiseWithMutex == true ->
                            // Release Mutex:
                            ReleaseMutex(taskId, SEMA_LOCK);
                            // Check Priority
                            changePriority(taskId, CURRENT_PRIO, old_prio, setPriorityRC);
                    ::  else
                    fi       
            ::  else -> skip
            fi
            // Release Semaphores
            TestSyncRelease(SEMA_TASK0_FIN);
    ::  else -> skip
    fi
}

proctype Task1(byte taskId) {
    assert(_priority == MED_PRIO);
    assert(taskId < TASK_MAX);
    if
    ::  testPrio == true ->
            byte setPriorityRC;
            byte old_prio = 1;

            TestSyncObtain(SEMA_TASK_START_1);
            TestSyncRelease(SEMA_TASK_START_1);

            tasks[taskId].pmlid = _pid;
            //set_priority(_pid, tasks[taskid].prio)

            // Obtain Mutex:
            ObtainMutex(taskId, SEMA_LOCK);
            
            printf("@@@ %d DECL byte priority 0\n",_pid);

            // Check Priority
            changePriority(taskId, CURRENT_PRIO, old_prio, setPriorityRC);

            // Chage Priority to High
            changePriority(taskId, HIGH_PRIO, old_prio, setPriorityRC);

            // Check Priority
            changePriority(taskId, CURRENT_PRIO, old_prio, setPriorityRC);

            // Release Mutex:
            ReleaseMutex(taskId, SEMA_LOCK);

            TestSyncRelease(SEMA_TASK1_FIN);
        
    ::  else
    fi
}

/*
proctype Task2 (byte taskid) {

}
*/

proctype PrioInheritance() {
    //printf("@@@ %d prio Inheritance Start \n",_pid);
    /* RTEMS Case:
    If the task is currently holding any binary semaphores which use a locking protocol, 
    then the task’s priority cannot be lowered immediately. If the task’s priority were 
    lowered immediately, then this could violate properties of the locking protocol and 
    may result in priority inversion. The requested lowering of the task’s priority will
    occur when the task has released all binary semaphores which make the task more important. 
    */
    assert(_priority == ISR_PRIO);
    byte taskId, prio;
    do
    ::  interrupt_channel ? taskId, prio ->
            assert(taskId < TASK_MAX);
            if
            ::  taskId == 0 -> break;
            ::  else;
            fi
            tasks[taskId].HoldingMutex == false -> atomic {
                //printf("@@@ %d prio Inheritance Enabled \n",_pid);
                tasks[taskId].prio = prio;
                set_priority(tasks[taskId].pmlid, prio)
            }
    od
}

init {
    pid nr;

    printf("Task Manager Model running.\n");
    printf("Setup...\n");

    printf("@@@ %d NAME Task_Manager_TestGen\n",_pid)

    outputDefines();
    outputDeclarations();

    chooseScenario();
    printf("@@@ %d INIT\n",_pid);

    printf("Run...\n");

    set_priority(_pid, MED_PRIO);


    if 
    ::  startTask == true ->
            printf("@@@ %d DEF TASK_0 %d\n",_pid,startTask);
    ::  else
    fi
    if
    ::  testPrio == true ->
            printf("@@@ %d DEF TASK_1 %d\n",_pid,testPrio);
    ::  else
    fi

    run System();
    run Clock();
    run PrioInheritance() priority ISR_PRIO;

    TestSyncRelease(SEMA_LOCK);
	
    run Runner(0, RUNNER_ID) priority MED_PRIO;
    run Task0(TASK0_ID) priority MED_PRIO;
    run Task1(TASK1_ID) priority MED_PRIO;

	_nr_pr == 1;

	#ifdef TEST_GEN
	assert(false);
	#endif

	printf("Task Manager Model finished !\n")
}
