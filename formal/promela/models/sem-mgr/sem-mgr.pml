/* SPDX-License-Identifier: BSD-2-Clause */

/*
 * sem-mgr.pml
 *
 * Copyright (C) 2022-2024 Trinity College Dublin (www.tcd.ie)
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

#include "../common/rtems.pml"
#define TASK_MAX 4
#define SEMA_MAX 3
#include "../common/model.pml"

#define MAX_MODEL_SEMAS 3 // 0 for NULL pointers
#define NO_TIMEOUT 0

#define SEMAPHORE1_NAME 1
#define SEMAPHORE2_NAME 2

#define TASK1_ID 1
#define TASK2_ID 2
#define TASK3_ID 3

// In SMP setting there are different cores, but all are settled on same node.
#define THIS_CORE 0
#define THAT_CORE 1

// semWait optionset for semaphore_obtain
#define RTEMS_WAIT 1
#define RTEMS_NO_WAIT 0


// Semaphore Configurations
//semaphore scope
#define SEMAPHORE_LOCAL 0
#define SEMAPHORE_GLOBAL 1

//semaphore type
#define COUNTING_S 0
#define BINARY_S 1
#define SIMPLE_BINARY_S 2

//rtems_priority
#define FIFO 0
#define PRIORITY 1

//locking protocol (binary sem)
#define NO_LOCKING 0
#define INHERIT_LOCKING 1
#define CEILING_LOCKING 2
#define MRSP_LOCKING 3

#define PRIORITY_CEILING 0
#define HIGH_PRIORITY 1
#define MED_PRIORITY 2
#define LOW_PRIORITY 3

#define MY_SCHEDULER 1

#define UINT32_MAX 4294967295

/* 
 * Multicore setup
 */
bool multicore;
int task1Core;
int task2Core;
int task3Core;

mtype{ SemaWait } ; // need to know when Blocked on a semaphore

typedef SemState {
    bool blocked;
    byte taskCeilingPriority; // task's ceiling priority 
    byte initialPriority // task's initial/default priority
    byte effectivePriority; // task's current active priority
};
SemState semstate[TASK_MAX];


inline checkHighestPriorityRunning(taskid, sem_id) {
    atomic {
        int highestReadyPriority = 255; // Start with the lowest priority
        int highestPriorityTask = 0; // No task selected initially

        // Find the highest priority task in Ready state
        if
        :: tasks[TASK1_ID].state == Ready && semstate[TASK1_ID].effectivePriority < highestReadyPriority ->
            highestReadyPriority = semstate[TASK1_ID].effectivePriority;
            highestPriorityTask = TASK1_ID;
        :: else -> skip;
        fi;
        if
        :: tasks[TASK2_ID].state == Ready && semstate[TASK2_ID].effectivePriority < highestReadyPriority ->
            highestReadyPriority = semstate[TASK2_ID].effectivePriority;
            highestPriorityTask = TASK2_ID;
        :: else -> skip;
        fi;
        if
        :: tasks[TASK3_ID].state == Ready && semstate[TASK3_ID].effectivePriority < highestReadyPriority ->
            highestReadyPriority = semstate[TASK3_ID].effectivePriority;
            highestPriorityTask = TASK3_ID;
        :: else -> skip;
        fi;
        
        if :: highestPriorityTask != 0 && // Valid task
            model_semaphores[sem_id].holder != 0 -> // Semaphore has been obtained
            if
            :: model_semaphores[sem_id].LockingProtocol == INHERIT_LOCKING ->
                if 
                :: semstate[taskid].effectivePriority <= highestReadyPriority &&
                    model_semaphores[sem_id].holder != taskid ->
                    assert(semstate[taskid].effectivePriority <= highestReadyPriority);                
                :: else -> skip;
                fi
            :: model_semaphores[sem_id].LockingProtocol == CEILING_LOCKING ->

                if :: model_semaphores[sem_id].holder != taskid ->
                    assert(semstate[taskid].effectivePriority <= highestReadyPriority);
                :: else -> skip;
                fi
            :: model_semaphores[sem_id].LockingProtocol == NO_LOCKING ->
                skip;
            fi
        :: else -> skip;
        fi
    }
}


typedef Semaphore_model {
    byte s_name; // semaphore name
    int Count; // current count of the semaphore
    int maxCount; //max count of semaphore (only for counting)
    int semType; // counting/binary/simple binary
    bool Priority; //true for priotity, false for FIFO
    int LockingProtocol; //None/Inherit/Ceiling/MRsP
    bool isGlobal; // true for global, false for local
    bool isInitialised; // indicated whenever this semaphore was created
    int priorityCeiling; // stores the priority ceiling of the binary semaphore - relevant for binary sem, 0 otherwise
    bool isFlushed; //if true all tasks waiting must be flushed.
    int waiters[TASK_MAX]; // waiters on the semaphore indicated by position in queue ( 1 is next in queue)
    byte ownerPid; // set to pid of the task that obtained the binary semaphore
    int currPriority; // tracks the current elevated priority of the semaphore's task holder
    byte prevPriority; // records priority before last change
    byte holder; // Task ID of the current holder
    byte queue[TASK_MAX]; // Priority queue of waiting tasks
    byte task_queue_count; // Number of tasks in the queue
    
    //bool isFIFO; // true for tasks wait by FIFO (default)
    //bool isPriority // true for tasks wait by priority
    //bool isBinary; // true if binary semaphore
    //bool isCounting // true if counting semaphore (default)
    //bool isSimpleBinary // true f simple binary sempahore
    //bool useInheritPriority // true if uses priority inheritance 
    //bool usecurrPriority // true if uses priority cieling 
    //bool multiprocessResourceSharing // true if uses multiprocessor resource sharing
    //bool isLocal // true if local semaphore (default)
    //bool isGlobal // ture if global semaphore
};

Semaphore_model model_semaphores[MAX_MODEL_SEMAS]; // semaphores[0] models a NULL dereference


// Output configuration
inline outputDefines () {
   printf("@@@ %d DEF MAX_MODEL_SEMAS %d\n",_pid,MAX_MODEL_SEMAS);
   printf("@@@ %d DEF SEMAPHORE_LOCAL %d\n",_pid,SEMAPHORE_LOCAL);
   printf("@@@ %d DEF SEMAPHORE_GLOBAL %d\n",_pid,SEMAPHORE_GLOBAL);
   printf("@@@ %d DEF COUNTING_S %d\n",_pid,COUNTING_S);
   printf("@@@ %d DEF BINARY_S %d\n",_pid,BINARY_S);
   printf("@@@ %d DEF SIMPLE_BINARY_S %d\n",_pid,SIMPLE_BINARY_S);
   printf("@@@ %d DEF FIFO %d\n",_pid,FIFO);
   printf("@@@ %d DEF PRIORITY %d\n",_pid,PRIORITY);
   printf("@@@ %d DEF NO_LOCKING %d\n",_pid,NO_LOCKING);
   printf("@@@ %d DEF INHERIT_LOCKING %d\n",_pid,INHERIT_LOCKING);
   printf("@@@ %d DEF CEILING_LOCKING %d\n",_pid,CEILING_LOCKING);
   printf("@@@ %d DEF MRSP_LOCKING %d\n",_pid,MRSP_LOCKING);
   printf("@@@ %d DEF TASK_MAX %d\n",_pid,TASK_MAX);
   printf("@@@ %d DEF SEMA_MAX %d\n",_pid,SEMA_MAX);

}


/*
 * Running Orders (maintained by simple global sync counter):
 *  Create;;Ident = Semaphore Identified only after creating
 *  Acquire;;TestSyncRelease = Semaphore is acquired and then released
 *  Acquire;;Delete = Semaphore is acquired and then deleted
 * Here ;; is "sequential" composition of *different* threads.
 * Additionally task 1 will always create a semaphore before operations
 */

inline outputDeclarations () {
  printf("@@@ %d DCLARRAY Semaphore test_sync_sema SEMA_MAX\n",_pid);
}


/*
 * sema_create(name,count,sem_type,scope,locking,task_priority,id,rc)
 *
 * Simulates a call to rtems_semaphore_create
 *   name : name of the semaphore
 *   sem_type: whether semaphore is binary/simple binary/counting as in attribute set
 *   scope : whether semaphore is local/global as in the attribute set
 *   locking : specifies locking protocol used as in attribute set (only if task_priority is priority)
 *   rtems_priority : true for priority, false for FIFO
 *   count : binary semaphore- count=0 makes calling task owner of semaphore 
 *           simple binary semaphore- initial count always 1 (no owner)
 *           counting semaphore- initial count >=1 (no owner)
 *   task_priority : only relevant for binary semaphores with priority ceiling or mrsp locking protocol defined, 0 otherwise
 *   id : id of the semaphore if created successfully
 *   rc : updated with the return code when directive completes
 *
 * Corresponding RTEMS call:
 *   rc = rtems_barrier_create(name,attribs,count,task_priority,id);
 *     `name` models `rtems_name name`
 *     `count` models `uint32_t count`
 *     `scope` models if sem is globl or local as in `rtems_attribute attribute_set`
 *     `rtems_priority` task wait queue discipline used, true for priority, false for FIFO
 *     `sem_type` models if its a binary/simple binary/counting sem in`rtems_attribute attribute_set`
 *     `locking` models which locking protocol is used as in `rtems_attribute attribute_set`
 *     `task_priority` models `rtems_task_priority` only relevant for binary semaphores, 0 otherwise
 *     `id` models `rtems_event_set *id`
 *
 */
inline sema_create(name,count, maxcount, scope,rtems_priority,sem_type,locking,task_priority,id,rc) {
    atomic{

        if
        ::  id == 0 -> rc = RC_InvAddr;
        ::  name <= 0 -> rc = RC_InvName;
        ::  else ->
            if
            ::  id < MAX_MODEL_SEMAS ->
                if
                ::  !model_semaphores[id].isInitialised ->
                    if
                    ::  sem_type == COUNTING_S -> //sem_type

                        model_semaphores[id].Count = count;
                        model_semaphores[id].maxCount = maxcount;
                        model_semaphores[id].LockingProtocol = locking;
                        model_semaphores[id].s_name = name;
                        model_semaphores[id].semType = sem_type;
                        model_semaphores[id].isGlobal = scope; //if local can only be used by node that created it
                        model_semaphores[id].Priority = rtems_priority;
                        model_semaphores[id].isInitialised = true;
                        model_semaphores[id].priorityCeiling = task_priority;
                        rc = RC_OK;
                        printf("@@@ %d LOG %d Created {n: %d, count: %d, global: %d, RTEMS_Priority:%d, sem_type: counting, locking protocol: %d, task_priority:%d}\n", _pid, id, name, count, scope, rtems_priority, locking, task_priority);
                
                    ::  sem_type == BINARY_S ->

                        model_semaphores[id].maxCount = 1;
                        model_semaphores[id].LockingProtocol = locking;
                        model_semaphores[id].s_name = name;
                        model_semaphores[id].semType = sem_type;
                        model_semaphores[id].isGlobal = scope; //if local can only be used by node that created it
                        model_semaphores[id].Priority = rtems_priority;
                        model_semaphores[id].currPriority = task_priority;
                        model_semaphores[id].prevPriority = task_priority;
                        model_semaphores[id].isInitialised = true;
                        model_semaphores[id].priorityCeiling = task_priority;
                        rc = RC_OK;
                        if
                        ::  count ==1 -> model_semaphores[id].Count = count;
                        ::  count ==0 -> model_semaphores[id].Count = count; // make task the owner
                            model_semaphores[id].ownerPid = _pid;
                        ::  else -> rc = RC_InvNum;
                        fi

                        printf("@@@ %d LOG %d Created {n: %d, count: %d, global: %d, RTEMS_Priority:%d, sem_type: binary, locking protocol: %d, task_priority:%d}\n", _pid, id, name, count, scope, rtems_priority, locking, task_priority);

                    ::  sem_type == SIMPLE_BINARY_S ->
                        if
                        ::  count != 1 -> rc = RC_InvNum;
                        ::  else -> model_semaphores[id].Count = count; 
                        fi
                    fi
                ::  else /* model_semaphores[id].isInitialised */ -> RC_InvId;
                fi

            ::  else -> // new_sem_id >= MAX_MODEL_SEMAS
                rc = RC_TooMany;
            fi
        fi
    }
}

/*
 * sema_ident(name,node,id,rc)
 *
 * Simulates a call to rtems_senaphore_ident
 *   name : name of the semaphore
 *   node : id of the node
 *   id : id of the semaphore if created successfully
 *   rc : updated with the return code when the directive completes
 *
 * Corresponding RTEMS call:
 *   rc = rtems_semaphore_ident(name,node,id);
 *     `name` models `rtems_name name`
 *     `node` models `uint32_t node`
 *     `id` models `rtems_event_set *id`
 *
 */
inline sema_ident(name,node,id,rc) {
    
  atomic{

    int sem_index = 1; // 0 is NULL deref
    if
    ::  id == 0 -> rc = RC_InvAddr;
    ::  name <= 0 -> 
        rc = RC_InvName;
        id = 0;
    ::  else -> // name > 0
        do
        ::  sem_index < MAX_MODEL_SEMAS ->
            if
            ::  model_semaphores[sem_index ].isInitialised && 
                model_semaphores[sem_index ].s_name == name ->
                  id = sem_index ;
                  printf("@@@ %d LOG Semaphore %d Identified by name %d\n",
                          _pid, sem_index, name);
                  rc = RC_OK;
                  break;
            ::  else -> /* !model_semaphores[id].isInitialised || 
                           model_semaphores[sem_index ].s_name!=name */ 
                  sem_index ++;
            fi
        ::  else -> // sem_index  >= MAX_MODEL_SEMAS
              rc = RC_InvName;
              break;
        od
    fi
  }
}


/*
 * WaitForSemaphore(tid, sem_id, rc) waits to acquire semaphore. 
 *
 */
inline WaitForSemaphore(tid,sem_id, optionset, interval, rc){
    atomic{
        printf("@@@ %d LOG Task %d waiting, state = ",_pid,tid);
        printm(tasks[tid].state); nl()
    }
    tasks[tid].state == Ready; // breaks out of atomics if false
    printf("@@@ %d STATE %d Ready\n",_pid,tid)
    if
    ::  tasks[tid].tout -> 
        model_semaphores[sem_id].waiters[tid] = false;
        rc = RC_Timeout;
        tasks[tid].tout = false;
        rc = RC_Timeout;
        printf("@@@ %d LOG timeout for Semaphore %d \n", _pid, sem_id); //timeout
    ::  !model_semaphores[sem_id].isInitialised ->
        model_semaphores[sem_id].waiters[tid] = false;
        rc = RC_Deleted;
    ::  model_semaphores[sem_id].isFlushed ->
        model_semaphores[sem_id].waiters[tid] = false;
        rc = RC_Unsat;
        printf("@@@ %d LOG task %d flushed from Semaphore %d \n", _pid, tid, sem_id); //semaphore obtained
    ::  else -> model_semaphores[sem_id].Count = model_semaphores[sem_id].Count -1;
                rc = RC_OK;
                printf("@@@ %d LOG Semaphore %d obtained\n", _pid, sem_id); //semaphore obtained
    fi
 
}


inline preemptIfRequired(tid, preempting_tid, rc) {
  if
  ::  tasks[tid].preemptable  &&
      semstate[preempting_tid].effectivePriority < semstate[tid].effectivePriority &&
      tasks[preempting_tid].state == Ready ->
        tasks[tid].state = OtherWait;
        printf( "@@@ %d LOG task %d preempted by task %d\n", 
                _pid, tid, preempting_tid );
        printf("@@@ %d STATE %d OtherWait\n",_pid,tid);
        rc = true;
  ::  else -> 
        printf( "@@@ %d LOG task %d NOT preempted by task %d\n"
              , _pid, tid, preempting_tid );
        rc = false;
  fi
}


/*
* Helper functions for priority queueing
*/

typedef Priority_queue {
    int head;               // top of task queue
    int tail;               // end of queue
    int head_prio;
    bool queueFull = false; // used to determine full or empty state
    int waitingTasks[TASK_MAX];
}


Priority_queue queueList[SEMA_MAX];





/*
 * sema_set_priority( semaphore_id, scheduler_id, new_priority, 
 *                    old_prio_ptr, old_prio, rc )
 *
 * Simulates a call to rtems_semaphore_set_priority
 *   semaphore_id : identifier semaphore whose priority is to be set
 *   scheduler_id : identifies scheduler to which the new priority applies
 *   new_priority : the new priority for the semaphore  w.r.t the scheduler
 *   old_prio : the previous priority of the semaphore
 *   rc : updated with the return code when the directive completes
 *
 * Corresponding RTEMS call:
 *   rc = rtems_semaphore_set_priority( 
            sem_id, scheduler_id, new_priority, old_prio_ptr );
 *     `sem_id` models the semaphore id.
 *     `scheduler_id` models the scheduler id.
 *     `new_priority` models the new priority level
 *     `old_prio_ptr` models pointer to old priority store.
 *     `old_prio` models the old priority value
 *
 *  We usually use `sem_id` to denote pointer to semaphore and old priority,
 *  except when we want to distinguish between invalid id and address cases
 */
 #define INV_PRIO -1

inline sema_set_priority( sema_id, scheduler_id, new_priority, 
                          old_prio_ptr, old_prio, rc ) 
{ atomic {
    if
    :: sema_id == 0      -> rc = RC_InvId;
    :: old_prio_ptr == 0 -> rc = RC_InvAddr;
    :: new_priority < 1  -> rc = RC_InvPrio;
    :: model_semaphores[sema_id].LockingProtocol == NO_LOCKING ->
        rc = RC_NotDefd;
    :: else ->
        if
        :: model_semaphores[sema_id].Priority == PRIORITY &&
            model_semaphores[sema_id].LockingProtocol == CEILING_LOCKING ->
            old_prio = model_semaphores[sema_id].priorityCeiling;
            model_semaphores[sema_id].priorityCeiling = new_priority;
            rc = RC_OK;
        :: else -> rc = RC_NotDefd;
        fi
        // if
        // :: model_semaphores[sem_id].Priority == PRIORITY &&
        //     model_semaphores[sem_id].LockingProtocol == CEILING_LOCKING ->
        //     model_semaphores[sem_id].priorityCeiling = new_priority;
        //     rc = RC_OK;
        // :: else -> rc = RC_InvPrio;
        // fi
    fi 
  } 
}

/*
 * sema_obtain(self,sem_id, optionset, timeout, rc)
 *
 * Simulates a call to rtems_semaphore_obtain
 *   self : task id making the call
 *   sem_id : id of the semaphore
 *   optionset : specifies RTEMS_WAIT(1) or RTEMS_NO_WAIT (0)
 *   timeout : wait time on the semaphore (0 waits forever) only if RTEMS_WAIT is used 
 *   rc : updated with the return code when the wait completes
 *
 * Corresponding RTEMS call:
 *   rc = rtems_semaphore_obtain(sem_id, optionset, timeout);
 *     `sem_id` models `rtems_id id`
 *     `optionset` models `rtems_option option_set`
 *     `timeout` models `rtems_interval timeout`
 *
 *
 */
inline sema_obtain(self, sem_id, optionset, interval,rc) {
   atomic{
        if
        ::  sem_id >= MAX_MODEL_SEMAS || sem_id <= 0 || !model_semaphores[sem_id].isInitialised ->
            rc = RC_InvId;
        ::  else -> // id is correct
            if
            ::  model_semaphores[sem_id].semType == COUNTING_S ->

                if 
                ::  model_semaphores[sem_id].Count > 0 -> 
                    model_semaphores[sem_id].Count = model_semaphores[sem_id].Count -1;
                    rc = RC_OK;
                    printf("@@@ %d LOG Semaphore %d obtained\n", _pid, sem_id)
                    //change global variable
                :: else -> //semaphore already in use add task to wait queue if FIFO
                    if
                    ::  optionset == RTEMS_NO_WAIT ->
                        rc = RC_Unsat;
                    ::  else -> // RTEMS_WAIT
                        // check if semaphore is FIFO
                        if
                        ::  model_semaphores[sem_id].Priority == FIFO ->
                            int queue_no=1;
                            int tid = 1;
                            do 
                            ::  tid < TASK_MAX ->
                                if 
                                ::  model_semaphores[sem_id].waiters[tid] != 0 -> queue_no++;
                                ::  else -> skip;
                                fi
                                tid++;
                            ::  else-> break;
                            od
                            model_semaphores[sem_id].waiters[self] = queue_no;

                            if
                            ::  interval > NO_TIMEOUT ->
                                tasks[self].tout = false;
                                tasks[self].ticks = interval;
                                tasks[self].state = TimeWait;
                                printf("@@@ %d STATE %d TimeWait %d\n",_pid,self,interval);
                            ::  else -> // No timeout wait forever
                                tasks[self].state = SemaWait;
                                printf("@@@ %d STATE %d SemaWait\n",_pid,self);
                            fi
                            WaitForSemaphore(self, sem_id, optionset, interval, rc);
                        fi
                    fi
                fi
            :: model_semaphores[sem_id].semType == BINARY_S ->
                if
                :: model_semaphores[sem_id].Count == 0 ->
                    if
                    :: optionset == RTEMS_NO_WAIT ->
                        rc = RC_Unsat; // The semaphore could not be immediately obtained  
                        printf("@@@ %d LOG Semaphore %d could not be immediately obtained\n", _pid, sem_id);
                    :: else -> // RTMES_WAIT
                        if
                        :: model_semaphores[sem_id].holder != self ->
                            enqueue(sem_id, self); // Add the current task to the waiting queue
                            semstate[self].blocked = true; // Mark the task as blocked
                            if
                            :: model_semaphores[sem_id].LockingProtocol == INHERIT_LOCKING &&
                            semstate[model_semaphores[sem_id].holder].effectivePriority > semstate[self].effectivePriority ->
                                // Priority inheritance
                                printf("@@@ %d LOG Priority inheritance: Task %d (priority %d) inherits priority %d from Task %d\n",
                                    _pid,
                                    model_semaphores[sem_id].holder, 
                                    semstate[model_semaphores[sem_id].holder].effectivePriority,
                                    semstate[self].effectivePriority, 
                                    self);
                                semstate[model_semaphores[sem_id].holder].effectivePriority = semstate[self].effectivePriority;
                                if
                                ::  interval > NO_TIMEOUT ->
                                    tasks[self].tout = false;
                                    tasks[self].ticks = interval;
                                    tasks[self].state = TimeWait;
                                    printf("@@@ %d STATE %d TimeWait %d\n",_pid,self,interval);
                                ::  else -> // No timeout wait forever
                                    tasks[self].state = SemaWait;
                                    printf("@@@ %d STATE %d SemaWait\n",_pid,self);
                                fi
                                waitUntilReady(self);   
                            :: else -> skip;
                            fi
                            rc = RC_OK;
                        :: else ->
                            printf("@@@ %d LOG Task %d already holds semaphore %d\n", _pid, self, sem_id);
                            rc = RC_OK;
                        fi
                    fi
                :: else ->
                    // Semaphore is available, so acquire it
                    model_semaphores[sem_id].Count = 0;
                    model_semaphores[sem_id].holder = self;
                    tasks[self].state = Ready;
                    printf("@@@ %d STATE %d Ready\n",_pid,self);
                    if
                    :: model_semaphores[sem_id].LockingProtocol == CEILING_LOCKING ->
                        semstate[self].effectivePriority = model_semaphores[sem_id].priorityCeiling;
                        printf("@@@ %d LOG Task %d priority raised to ceiling priority %d due to CEILING_LOCKING\n",
                            _pid, self, model_semaphores[sem_id].priorityCeiling);
                    :: else -> skip;
                    fi
                    printf("@@@ %d LOG Semaphore %d acquired by Task %d\n", _pid, sem_id, self);
                    rc = RC_OK;
                fi
            fi
        fi
    }
}

/*
 * sema_release(self,sem_id,rc)
 *
 * Simulates a call to rtems_semaphore_release
 *   self: if of the calling task
 *   sem_id : id of the semaphore
 *   rc : updated with the return code when the directive completes
 *
 * Corresponding RTEMS call:
 *   rc = rtems_semaphore_release(sem_id);
 *     `sem_id` models `rtems_id id`
 *
 */
inline sema_release(self,sem_id,rc) {
    atomic{
        if
        ::  sem_id >= MAX_MODEL_SEMAS || sem_id <= 0 || !model_semaphores[sem_id].isInitialised ->
            rc = RC_InvId
        ::  model_semaphores[sem_id].Count == UINT32_MAX ->
            rc = RC_Unsat;
        ::  else -> 
            
            if
            :: model_semaphores[sem_id].semType == COUNTING_S && 
               model_semaphores[sem_id].Priority == FIFO ->
               
                model_semaphores[sem_id].Count++;
                int tid = 1;
                do 
                ::  tid < TASK_MAX ->
                    if 
                    ::  model_semaphores[sem_id].waiters[tid] == 1 -> 
                        model_semaphores[sem_id].waiters[tid] = 0;
                        tasks[tid].state = Ready;
                        int updatetid=1;
                        do
                        ::  updatetid < TASK_MAX ->
                            if 
                            ::  model_semaphores[sem_id].waiters[updatetid]!=0 -> model_semaphores[sem_id].waiters[updatetid]--
                            ::  else -> skip;
                            fi 
                            updatetid++;
                        ::  else -> break;
                        od
                    ::  else -> skip;
                    fi
                    tid++;
                ::  else-> break;
                od

                printf("@@@ %d LOG Semaphore %d released\n", _pid, sem_id)
                rc = RC_OK;

            :: model_semaphores[sem_id].semType == BINARY_S &&
               model_semaphores[sem_id].Priority == PRIORITY ->
                if
                :: model_semaphores[sem_id].holder == taskid ->
                    if
                    :: model_semaphores[sem_id].task_queue_count > 0 ->
                        model_semaphores[sem_id].holder = dequeue(sem_id); // Assign to next highest priority task
                        //model_semaphores[sem_id].ownerPid = _pid;
                        semstate[model_semaphores[sem_id].holder].blocked = false;
                        tasks[model_semaphores[sem_id].holder].state = Ready;
                        printf("@@@ %d STATE %d Ready\n",_pid, model_semaphores[sem_id].holder);
                        model_semaphores[sem_id].Count = 0;
                        printf("@@@ %d LOG Semaphore %d released by Task %d, now held by Task %d\n",
                            _pid, sem_id, _pid, model_semaphores[sem_id].holder);
                        rc = RC_OK;
                    :: else ->
                        model_semaphores[sem_id].Count = 1;
                        model_semaphores[sem_id].holder = 255; // No owner
                        printf("@@@ %d LOG Semaphore %d completely released by Task %d\n", _pid, sem_id, _pid);
                        rc = RC_OK;
                    fi
                    // Restore the original priority if the protocol is ceiling or inheritance and required
                    if
                    :: model_semaphores[sem_id].LockingProtocol == CEILING_LOCKING ||
                    model_semaphores[sem_id].LockingProtocol == INHERIT_LOCKING ->
                        semstate[taskid].effectivePriority = semstate[taskid].initialPriority;
                        printf("@@@ %d LOG Task %d priority restored to initial priority %d after releasing semaphore\n",
                            _pid, taskid, semstate[taskid].initialPriority);
                    :: else -> skip;
                    fi
                    printf("@@@ %d LOG Semaphore %d released by Task %d, now held by Task %d\n",
                        _pid, sem_id, taskid, model_semaphores[sem_id].holder);
                    rc = RC_OK;
                :: else ->
                    printf("@@@ %d LOG Task %d is not the owner of the semaphore %d and cannot release it\n", _pid, taskid, sem_id);
                    rc = RC_NotOwner;
                fi
            fi
        fi
    }
}



inline init_semaphore_priority_queue(sem_id) {
    atomic {
        model_semaphores[sem_id].holder = 255; // Invalid task ID indicating no holder
        model_semaphores[sem_id].task_queue_count = 0;
    }
}

inline enqueue(sem_id, task_id) {
    byte i, j;
    atomic {
        // Insert task into the queue based on effectivePriority
        i = model_semaphores[sem_id].task_queue_count;
        do
        :: i > 0 && semstate[model_semaphores[sem_id].queue[i-1]].effectivePriority > semstate[task_id].effectivePriority ->
            model_semaphores[sem_id].queue[i] = model_semaphores[sem_id].queue[i-1];
            i--;
        :: else -> break;
        od
        model_semaphores[sem_id].queue[i] = task_id;
        model_semaphores[sem_id].task_queue_count++;

        printf("@@@ %d LOG Task %d enqueued\n",_pid, task_id);
    }
}

inline dequeue(sem_id) {
    byte task_id;
    int i;
    atomic {
        task_id = model_semaphores[sem_id].queue[0]; // Always dequeue the highest priority task

        // Shift all elements in the queue to the left
        i = 0;
        do
        :: i < model_semaphores[sem_id].task_queue_count - 1 ->
            model_semaphores[sem_id].queue[i] = model_semaphores[sem_id].queue[i+1];
            i++;
        :: else ->
            break;
        od

        model_semaphores[sem_id].task_queue_count--;
        printf("@@@ %d LOG Task %d dequeued\n",_pid, task_id);
    }
    return task_id;
}


inline set_default_priority_options() {
    task_in[TASK1_ID].semType = BINARY_S;
    task_in[TASK2_ID].semType = BINARY_S;
    task_in[TASK3_ID].semType = BINARY_S;

    task_in[TASK1_ID].semWait = true;
    task_in[TASK2_ID].semWait = true;
    task_in[TASK3_ID].semWait = true;

    task_in[TASK1_ID].taskPreempt = true;
    task_in[TASK2_ID].taskPreempt = true;
    task_in[TASK3_ID].taskPreempt = true;

    task_in[TASK1_ID].doPriorityInversion = true;
    task_in[TASK2_ID].doPriorityInversion = true;
    task_in[TASK3_ID].doPriorityInversion = true;

    task_in[TASK1_ID].isPriority = PRIORITY;
    task_in[TASK2_ID].isPriority = PRIORITY;
    task_in[TASK3_ID].isPriority = PRIORITY;

    // Set the priority ceiling of each of the tasks
    task_in[TASK1_ID].taskPrio = PRIORITY_CEILING;
    task_in[TASK2_ID].taskPrio = PRIORITY_CEILING;
    task_in[TASK3_ID].taskPrio = PRIORITY_CEILING;

    // Set the initial priority of each of the tasks
    task_in[TASK1_ID].taskInitialPriority = LOW_PRIORITY;
    task_in[TASK2_ID].taskInitialPriority = HIGH_PRIORITY;
    task_in[TASK3_ID].taskInitialPriority = MED_PRIORITY;

    task_in[TASK1_ID].doCreate = true;

    // 1 Lower priority task runs and acquires lock
    task_in[TASK1_ID].doAcquire = true; 
    // 2 Higher priority task attempts to acquire lock - is blocked
    task_in[TASK2_ID].doAcquire = true;
    
    // 3 Medium priority task performs its logic with preference over lower

    // 4 Lower finishes and releases
    task_in[TASK1_ID].doRelease = true;

    // 5 Higher is now able to obtain
    task_in[TASK2_ID].doRelease = true;
}
    

/*
 * sema_delete(self,sem_id,rc)
 *
 * Simulates a call to rtems_semaphore_delete
 *   sem_id : id of the semaphore
 *   rc : updated with the return code when the directive completes
 *
 * Corresponding RTEMS call:
 *   rc = rtems_semaphore_delete(sem_id);
 *     `sem_id`  models `rtems_id id`
 *
 * All tasks waiting to obtain deleted semaphore are readied and returned status code
 * Binary semaphores with an owner cannot be deleted
 * Whena global semaphore is deleted, the semaphore identifier must be transmitted to every node
 *      in the system for deleton from the local copy of the global object table
 */
inline sema_delete(self,sem_id,rc) {
    atomic{
        if
        ::  sem_id >= MAX_MODEL_SEMAS || sem_id <= 0 || !model_semaphores[sem_id].isInitialised ->
            rc = RC_InvId
        ::  model_semaphores[sem_id].semType == BINARY_S && model_semaphores[sem_id].ownerPid != _pid ->
            rc = RC_RsrcInUse; // The binary semaphore had an owner
        ::  else -> 
            model_semaphores[sem_id].isInitialised = false;
            int tid=1;
            do
            ::  tid < TASK_MAX ->
                if
                ::  model_semaphores[sem_id].waiters[tid]!=0 ->
                    tasks[tid].state = Ready;
                ::  else -> skip;
                fi
                tid++;
            :: else-> break;
            od

            printf("@@@ %d LOG Semaphore %d deleted\n", _pid, sem_id)
            rc = RC_OK
        fi
    }
}


/*
 * sema_flush(self,sem_id,rc)
 *
 * Simulates a call to rtems_semaphore_flush
 *   sem_id : id of the semaphore
 *   rc : updated with the return code when the directive completes
 *
 * Corresponding RTEMS call:
 *   rc = rtems_semaphore_flush(sem_id);
 *     `sem_id`  models `rtems_id id`
 *
This directive unblocks all tasks waiting on the semaphore specified by id. 
The semaphore’s count is not changed by this directive. 
Tasks which are unblocked as the result of this directive will return from the rtems_semaphore_obtain() directive with a 
status code of RTEMS_UNSATISFIED to indicate that the semaphore was not obtained.
 */
inline sema_flush(self, sem_id, rc) {
    atomic {
        if
        ::  sem_id >= MAX_MODEL_SEMAS || sem_id <= 0 || !model_semaphores[sem_id].isInitialised ->
            rc = RC_InvId;
        ::  else ->
            model_semaphores[sem_id].isFlushed = true;
            int tid=1;
            do
            ::  tid < TASK_MAX ->
                if
                ::  model_semaphores[sem_id].waiters[tid]!=0 ->
                    tasks[tid].state = Ready;
                ::  else -> skip;
                fi
                tid++;
            ::  else -> break;
            od
            printf("@@@ %d LOG Semaphore %d Flushed\n", _pid, sem_id)
            rc = RC_OK;
        fi
    }

}



/*
 * Scenario Generation
 *
 *  (PLAN)
 *
 * We can create, ident, delete, obtain, release, flush, and set_priority
 *
 * One task can cover create, ident, delete (all kinds)
 * Two or more tasks will exercise obtain, release, flush (FIFO, one core)
 * Three tasks will exercise set_priority, obtain, release, flush 
 *    (prio, one core)
 * N tasks will exercise set_priority, obtain, release, flush 
 *    (prio, two/three cores)
 * 
 *
 */

 /*
 * Task variants:
 *   Task objectives - semaphore {Create, Acquire, TestSyncRelease, Delete}
 *   timeout_length in {0,1,2...}
 *   
 * Task Scenarios:
 *   vary: Priority, preemptable, timeout interval, 
 */
typedef TaskInputs {

    bool doCreate; // will task create a semaphore
    bool doCreate2;
    bool isGlobal;
    int Count; // if doCreate is true, specifies initial count of semaphore
    int maxCount; // max count of semaphore
    int semType; // counting/binary/simple binary

    bool isPriority; //false for FIFO, true for priority
    int LockingProtocol; //None/Inherit/Ceiling/MRsP


    byte sName; // Name of semaphore to create or identify
    bool doAcquire; // will task aquire the semaphore
    bool doAcquire2;
    bool semWait; //Will the task wait to obtain the semaphore
    byte timeoutLength; // only relevant if doAcquire is true, gives wait time
    bool doDelete; // will task delete the semaphore
    bool doDelete2;
    bool doRelease; // will task release the semaphore
    bool doRelease2;
    bool doFlush; //will task flush the semaphore
    bool doFlush2;
    bool doSetPriority; // will task set the priority ceiling for the semaphore
    bool doSetPriority2;

    byte taskPrio; // This is used for setting the ceiling priority in sema_create
    byte taskInitialPriority; // The intial priority of the task
    bool taskPreempt;

    bool idNull; // indicates whenever passed id is null

    bool doPriorityInversion; // needed for testing priority inversion and locking protocols

    int newTaskPrio; // used by sema_set_priority to set new priority ceiling
    //int newTaskPrio2;
}

TaskInputs task_in[TASK_MAX];

inline assignDefaults(defaults, opts) {
    opts.doCreate = defaults.doCreate;
    opts.doCreate2 = defaults.doCreate2;
    opts.isGlobal = defaults.isGlobal;
    opts.Count = defaults.Count;
    opts.maxCount = defaults.maxCount;
    opts.semType= defaults.semType;
    opts.isPriority = defaults.isPriority;
    opts.LockingProtocol= defaults.LockingProtocol;
    opts.sName = defaults.sName;
    opts.doAcquire = defaults.doAcquire;
    opts.doAcquire2 = defaults.doAcquire2;
    opts.semWait = defaults.semWait;
    opts.timeoutLength=defaults.timeoutLength;
    opts.doDelete=defaults.doDelete;
    opts.doDelete2=defaults.doDelete2;
    opts.doFlush2=defaults.doFlush2;
    opts.doRelease=defaults.doRelease;
    opts.doRelease2=defaults.doRelease2;
    opts.doFlush=defaults.doFlush;
    opts.doSetPriority=defaults.doSetPriority;
    opts.doSetPriority2=defaults.doSetPriority2;
    opts.taskPrio=defaults.taskPrio;
    opts.taskPreempt=defaults.taskPreempt;
    opts.idNull = defaults.idNull;
    opts.doPriorityInversion = defaults.doPriorityInversion;
    opts.newTaskPrio = defaults.newTaskPrio;
    opts.taskInitialPriority = defaults.taskInitialPriority;

}


/*
 * synchronisation semaphore Setup
 */
int task1Sema;
int task2Sema;
int task3Sema;

mtype = { onesema, twosemas, different_sema_counts
        , test_priority, test_set_priority };


inline chooseScenario() {

    // Common Defaults
    TaskInputs defaults;

    defaults.doCreate = false;
    defaults.doCreate2 = false;
    defaults.Count=1;
    defaults.maxCount = UINT32_MAX;
    defaults.isGlobal = false;
    defaults.semType = COUNTING_S;
    defaults.isPriority = false;
    defaults.LockingProtocol = NO_LOCKING;
    defaults.doAcquire2 = false;
    defaults.doAcquire = false;
    defaults.doRelease = false;
    defaults.doRelease2 = false;
    defaults.semWait = false;
    defaults.timeoutLength = NO_TIMEOUT;
    defaults.doDelete = false;
    defaults.doDelete2 = false;
    defaults.doFlush=false;
    defaults.doFlush2=false;
    defaults.doSetPriority=false;
    defaults.doSetPriority2=false;
    defaults.taskPrio = 2;
    defaults.taskPreempt = false;
    defaults.idNull = false;
    defaults.sName = SEMAPHORE1_NAME;
    defaults.doPriorityInversion = false;
    defaults.newTaskPrio = 0;
    defaults.taskInitialPriority = MED_PRIORITY;

    // Set the defaults
    assignDefaults(defaults, task_in[TASK1_ID]);
    task_in[TASK1_ID].doCreate = true; // Task 1 is always the creator
    assignDefaults(defaults, task_in[TASK2_ID]);
    assignDefaults(defaults, task_in[TASK3_ID]);


    // synchronization semaphore initialization
    test_sync_sema[0] = false;
    task1Sema = 0;
    test_sync_sema[1] = false;
    task2Sema = 1;
    test_sync_sema[2] = false;
    task3Sema = 2;

    tasks[TASK1_ID].state = Ready;
    tasks[TASK2_ID].state = Ready;
    tasks[TASK3_ID].state = Ready;

    multicore = false;
    task1Core = THIS_CORE;
    task2Core = THIS_CORE;
    task3Core = THIS_CORE;

    if
    ::  scenario = onesema;
    ::  scenario = twosemas;
    ::  scenario = different_sema_counts;
    ::  scenario = test_priority;
    ::  scenario = test_set_priority;
    fi
    atomic{printf("@@@ %d LOG scenario ",_pid); printm(scenario); nl()}
    
    if
    ::  scenario==onesema->true
    
        if
        ::  task_in[TASK1_ID].sName = 0;
            printf( "@@@ %d LOG sub-scenario bad create, invalid name\n", _pid); //RTEMS_INVALID_NAME
        ::  task_in[TASK1_ID].idNull = true;
            printf( "@@@ %d LOG sub-scenario bad create, passed id null\n", _pid); //RTEMS_INVALID_ADDRESS
        ::  task_in[TASK1_ID].Count = 0;
            printf( "@@@ %d LOG sub-scenario bad create, passed invalid initial count\n", _pid); //RTEMS_INVALID_NUMBER
        ::  task_in[TASK1_ID].doDelete = true;
            printf( "@@@ %d LOG sub-scenario created and deleted\n", _pid); //RTEMS_SUCCESSFUL    
        ::  task_in[TASK1_ID].Count = UINT32_MAX - 1;
            task_in[TASK1_ID].doRelease = true;
            task_in[TASK2_ID].doRelease = true;
            printf( "@@@ %d LOG sub-scenario created, release at max count\n", _pid); // RTEMS_UNSATISFIED   
        ::  task_in[TASK2_ID].doAcquire = true;
            task_in[TASK3_ID].doAcquire = true;
            task_in[TASK2_ID].doRelease = true;
            task_in[TASK3_ID].doRelease = false;
            //no wait 

        ::  task_in[TASK1_ID].doAcquire = true;
            task_in[TASK2_ID].doAcquire = true;
            task_in[TASK1_ID].doRelease = true;
            task_in[TASK2_ID].doRelease = false;
            // alternate no wait

        ::  task_in[TASK2_ID].doAcquire = true;
            task_in[TASK3_ID].doAcquire = true;
            task_in[TASK3_ID].semWait = true;
            task_in[TASK2_ID].doRelease=true;
            task_in[TASK3_ID].doRelease = false;
            printf( "@@@ %d LOG sub-scenario WAIT no timeout\n", _pid);   
            //wait with no timeout scenario

        ::  task_in[TASK2_ID].doAcquire = true;
            task_in[TASK3_ID].doAcquire = true;
            task_in[TASK3_ID].semWait = true;
            task_in[TASK3_ID].timeoutLength = 2;
            task_in[TASK2_ID].doRelease=true;
            task_in[TASK3_ID].doRelease = true;
            //timeout scenario

        ::  task_in[TASK2_ID].doAcquire= true;
            task_in[TASK3_ID].doAcquire = true;
            task_in[TASK3_ID].semWait = true;
            task_in[TASK2_ID].doRelease= false;
            task_in[TASK3_ID].doRelease = false;
            task_in[TASK2_ID].doFlush= true;
            task_in[TASK2_ID].doRelease = false;

            printf( "@@@ %d LOG sub-scenario FLUSH\n", _pid);  
            //fush on waiting task scenario

        fi


    ::  scenario == twosemas->
        if
        ::  task_in[TASK1_ID].doCreate2 = true;
            task_in[TASK2_ID].doAcquire = true;
            task_in[TASK3_ID].doAcquire = true;
            task_in[TASK2_ID].doRelease = true;
            task_in[TASK3_ID].doRelease = true;
            task_in[TASK2_ID].doAcquire2 = true;
            task_in[TASK3_ID].doAcquire2 = true;
            task_in[TASK2_ID].doRelease2 = true;
            task_in[TASK3_ID].doRelease2 = true;
            //no wait 

        ::  task_in[TASK1_ID].doCreate = true;
            task_in[TASK3_ID].doAcquire = true;
            task_in[TASK2_ID].doAcquire = true;
            // no wait simplified
                                         
        ::  task_in[TASK1_ID].doCreate2 = true;
            task_in[TASK2_ID].doAcquire = true;
            task_in[TASK3_ID].doAcquire = true;
            task_in[TASK3_ID].semWait = true;
            task_in[TASK2_ID].doRelease=true;
            task_in[TASK3_ID].doRelease = false;
            task_in[TASK2_ID].doAcquire2 = true;
            task_in[TASK3_ID].doAcquire2 = true;
            task_in[TASK2_ID].doRelease2=true;
            task_in[TASK3_ID].doRelease2 = false;
            //wait with no timeout  


        fi

    // Counting semaphores with different counts 
    :: scenario == different_sema_counts ->
        if
        :: task_in[TASK1_ID].Count = 0 ->
            printf("@@@ %d LOG sub-scenario created, sema_count = 0\n", _pid);
        :: task_in[TASK1_ID].Count = 1 ->
            printf("@@@ %d LOG sub-scenario created, sema_count = 1\n", _pid);
            task_in[TASK1_ID].maxCount = 1;
            task_in[TASK1_ID].doCreate = true;
            task_in[TASK1_ID].doAcquire = true;
            task_in[TASK1_ID].doRelease = true;
        :: task_in[TASK1_ID].Count = 2 ->
            printf("@@@ %d LOG sub-scenario created, sema_count = 2\n", _pid);
            task_in[TASK1_ID].maxCount = 2;
            task_in[TASK1_ID].doCreate = true;
            task_in[TASK1_ID].doAcquire = true;
            task_in[TASK2_ID].doAcquire = true;
            task_in[TASK1_ID].doRelease = true;
            task_in[TASK2_ID].doRelease = true;
        :: task_in[TASK1_ID].Count = 3 ->
            printf("@@@ %d LOG sub-scenario created, sema_count = 3\n", _pid);
            task_in[TASK1_ID].maxCount = 3;
            task_in[TASK1_ID].doCreate = true;
            task_in[TASK1_ID].doAcquire = true;
            task_in[TASK2_ID].doAcquire = true;
            task_in[TASK3_ID].doAcquire = true;
            task_in[TASK1_ID].doRelease = true;
            task_in[TASK2_ID].doRelease = true;
            task_in[TASK3_ID].doRelease = true;
         fi


    ::  scenario == test_priority ->
        set_default_priority_options();
        if
        
        // No Locking - Priority Inversion
        :: task_in[TASK1_ID].LockingProtocol = NO_LOCKING ->
            task_in[TASK1_ID].LockingProtocol = NO_LOCKING;
            task_in[TASK1_ID].LockingProtocol = NO_LOCKING;

            printf("@@@ %d LOG sub-scenario created, testing no locking - priority inversion \n", _pid);

        // Immediate Ceiling Priority Protocol
        :: task_in[TASK1_ID].LockingProtocol = CEILING_LOCKING ->
            task_in[TASK2_ID].LockingProtocol = CEILING_LOCKING;
            task_in[TASK3_ID].LockingProtocol = CEILING_LOCKING;

            printf("@@@ %d LOG sub-scenario created, testing priority ceiling protocol \n", _pid);
    
        // Priority Inheritance Protocol
        :: task_in[TASK1_ID].LockingProtocol = INHERIT_LOCKING ->
            task_in[TASK2_ID].LockingProtocol = INHERIT_LOCKING;
            task_in[TASK3_ID].LockingProtocol = INHERIT_LOCKING;

            printf("@@@ %d LOG sub-scenario created, testing priority inheritance protocol \n", _pid);
        fi

      
    ::  scenario == test_set_priority ->
        task_in[TASK1_ID].doSetPriority = true;
        set_default_priority_options();
        if
        // Priority Inversion
        :: task_in[TASK1_ID].LockingProtocol = NO_LOCKING ->            
            printf( "@@@ %d LOG sub-scenario set priority, no locking protocol, not defined\n", _pid); //RTEMS_NOT_DEFINED

        // Immediate Ceiling Priority Protocol
        :: task_in[TASK1_ID].LockingProtocol = CEILING_LOCKING ->
            printf( "@@@ %d LOG sub-scenario set priority, ceiling locking protocol, successful\n", _pid); //RTEMS_SUCCESSFUL
        
        // Invalid priority
        :: task_in[TASK1_ID].LockingProtocol = CEILING_LOCKING ->
            task_in[TASK1_ID].newTaskPrio = INV_PRIO;
            // we need to ensure address is valid
            printf( "@@@ %d LOG sub-scenario set priority, invalid new priority\n", _pid); //RTEMS_INVALID_PRIORITY
        
        
        fi


    fi


}

proctype Runner (byte nid, taskid; TaskInputs opts) {

    byte sc;
    printf( "@@@ %d DECL byte sc\n", _pid );
    byte prio ;
    printf( "@@@ %d DECL byte prio\n", _pid );


    tasks[taskid].nodeid = nid;
    tasks[taskid].pmlid = _pid;
    semstate[taskid].taskCeilingPriority = opts.taskPrio;
    tasks[taskid].preemptable = opts.taskPreempt;
    semstate[taskid].initialPriority = opts.taskInitialPriority;
    semstate[taskid].effectivePriority = opts.taskInitialPriority;
    
   

    printf("@@@ %d TASK Runner\n",_pid);
    if 
    :: semstate[taskid].initialPriority == HIGH_PRIORITY 
         -> printf("@@@ %d CALL HighPriority\n", _pid);
    :: semstate[taskid].initialPriority == MED_PRIORITY 
         -> printf("@@@ %d CALL NormalPriority\n", _pid);
    :: semstate[taskid].initialPriority == LOW_PRIORITY 
         -> printf("@@@ %d CALL LowPriority\n", _pid);
    fi

    byte rc;
    byte sem_id;
    if
    ::  opts.idNull -> sem_id = 0;
    ::  else -> sem_id = 1;
    fi

    //if
    //::  multicore ->
    //    printf("@@@ %d CALL SetProcessor %d\n", _pid, tasks[taskid].nodeid);
    //::  else -> skip
    //fi
    

    if
    ::  opts.doCreate ->
        sem_id=1
        printf("@@@ %d CALL merge_attribs %d %d %d %d \n", _pid, opts.isGlobal, opts.isPriority, opts.semType, opts.LockingProtocol);

        printf("@@@ %d CALL sema_create %d %d %d %d \n", 
                _pid, opts.sName, opts.Count, opts.taskPrio, sem_id);
                /*  (name,      count,       max Count,      scope,        rtems_priority,     sem_type,     locking,           task_priority,   id, rc) */
        sema_create(opts.sName, opts.Count, opts.maxCount, opts.isGlobal, opts.isPriority, opts.semType, opts.LockingProtocol, opts.taskPrio, sem_id, rc);

        if
        ::  rc == RC_OK ->
            printf("@@@ %d SCALAR created %d\n", _pid, sem_id);
        :: else -> skip;
        fi
        printf("@@@ %d SCALAR rc %d\n",_pid, rc);
    ::  else -> //ident
            sem_id=1
            printf("@@@ %d CALL sema_ident %d %d %d\n", _pid, opts.sName, nid, sem_id);
                                                            /* (name,   node, id,  rc) */
            sema_ident(opts.sName,nid,sem_id,rc);
            printf("@@@ %d SCALAR rc %d\n",_pid, rc);
    fi


    if
    ::  opts.doCreate2 ->
        sem_id=2;
        printf("@@@ %d CALL merge_attribs2 %d %d %d %d \n", _pid, opts.isGlobal, opts.isPriority, opts.semType, opts.LockingProtocol);

        printf("@@@ %d CALL sema_create2 %d %d %d %d \n", 
                _pid, SEMAPHORE2_NAME, opts.Count, opts.taskPrio, sem_id);
                /*  (name,      count,       max Count,      scope,        rtems_priority,     sem_type,     locking,           task_priority,   id, rc) */
        sema_create(SEMAPHORE2_NAME, opts.Count, opts.maxCount, opts.isGlobal, opts.isPriority, opts.semType, opts.LockingProtocol, opts.taskPrio, sem_id, rc);

        if
        ::  rc == RC_OK ->
            printf("@@@ %d SCALAR created2 %d\n", _pid, 2);
        :: else -> skip;
        fi
        printf("@@@ %d SCALAR rc %d\n",_pid, rc);
    ::  else -> //ident
            sem_id=2;
            printf("@@@ %d CALL sema_ident2 %d %d %d\n", _pid, SEMAPHORE2_NAME, nid, sem_id);
                                                            /* (name,   node, id,  rc) */
            sema_ident(SEMAPHORE2_NAME,nid,sem_id,rc);
            printf("@@@ %d SCALAR rc %d\n",_pid, rc);
    fi
    
   
    if
    ::  opts.doSetPriority ->
        atomic {
            int new_prio = opts.newTaskPrio;
            int old_prio = 10;
            sem_id=1;
            printf( "@@@ %d CALL sema_set_priority %d %d %d %d\n", 
                    _pid, sem_id, new_prio, sem_id, old_prio);
            sema_set_priority(sem_id, 1, new_prio, sem_id, old_prio, rc);
            printf("@@@ %d SCALAR rc %d\n",_pid, rc);
            if
            :: rc==0 -> printf("@@@ %d SCALAR old_prio %d\n",_pid, old_prio);
            fi
        }
    :: else -> skip;
    fi
    
  

    if
    ::  opts.doAcquire -> 
            sem_id=1
            printf("@@@ %d CALL sema_obtain %d %d %d\n",
                    _pid, sem_id, opts.semWait, opts.timeoutLength);
                    /* (self,   sem_id, optionset, timeout,   rc) */
            sema_obtain(taskid, sem_id, opts.semWait, opts.timeoutLength, rc);
            printf("@@@ %d SCALAR rc %d\n",_pid, rc);
    ::  else -> skip;
    fi

    if
    ::  opts.doAcquire2 -> 
            sem_id=2;
            printf("@@@ %d CALL sema_obtain2 %d %d %d\n",
                    _pid, sem_id, opts.semWait, opts.timeoutLength);
                    /* (self,   sem_id, optionset, timeout,   rc) */
            sema_obtain(taskid, sem_id, opts.semWait, opts.timeoutLength, rc);
            printf("@@@ %d SCALAR rc %d\n",_pid, rc);
    ::  else -> skip;
    fi

    if
    ::  opts.doPriorityInversion ->
        atomic {
            rc = false;
            preemptIfRequired(taskid, TASK2_ID, rc);
            if
            :: rc ->
                TestSyncRelease(task2Sema);
            :: else ->
                skip;   
            fi
        }
    :: else -> 
        TestSyncRelease(task2Sema);
        TestSyncObtain(task1Sema);
    fi



    checkHighestPriorityRunning(taskid, 1);

    if
    ::  opts.doPriorityInversion ->
        atomic {
            rc = false;
            printf("@@@ %d LOG entering t1 preemptifrequired\n",_pid);
            preemptIfRequired(taskid, TASK3_ID, rc);
            if
            :: rc || model_semaphores[sem_id].LockingProtocol == NO_LOCKING ->
                TestSyncRelease(task3Sema);
                TestSyncObtain(task1Sema);
            :: else -> 
                skip;   
            fi
        }
    ::  else -> skip;
    fi
    

    if
    ::  opts.doRelease -> 
            sem_id=1
            if
            :: opts.doPriorityInversion -> skip;
            :: else -> 
                TestSyncObtain(task1Sema);
            fi
           
            printf("@@@ %d CALL sema_release %d\n", _pid, sem_id);
                        /* (self,   sem_id, rc) */
            sema_release(taskid, sem_id, rc);
            if
            :: rc == RC_OK -> 
                printf("@@@ %d SCALAR released %d\n", _pid, sem_id);
            :: else -> skip;
            fi
            printf("@@@ %d SCALAR rc %d\n",_pid, rc);

            if
            :: opts.doPriorityInversion -> skip;
            :: else -> 
                TestSyncRelease(task1Sema);
            fi
    ::  else -> skip;
    fi

   
    if
    ::  opts.doPriorityInversion ->
        atomic {
            TestSyncRelease(task2Sema);
            TestSyncObtain(task1Sema);
        }
    ::  else -> skip;
    fi 

    if
    ::  opts.doRelease2 -> 
            sem_id=2
            TestSyncObtain(task1Sema);
           
            printf("@@@ %d CALL sema_release2 %d\n", _pid, sem_id);
                        /* (self,   sem_id, rc) */
            sema_release(taskid, sem_id, rc);
            if
            :: rc == RC_OK -> 
                printf("@@@ %d SCALAR released %d\n", _pid, sem_id);
            :: else -> skip;
            fi
            printf("@@@ %d SCALAR rc %d\n",_pid, rc);
            TestSyncRelease(task1Sema);
            
    ::  else -> skip;
    fi


    if 
    ::  opts.doFlush ->
        atomic {
            sem_id=1
            printf("@@@ %d CALL sema_flush %d\n",_pid, sem_id);
                                /*  (self,   sem_id, rc) */
            sema_flush(taskid, sem_id, rc);
            printf("@@@ %d SCALAR rc %d\n",_pid, rc);
        }
    ::  else -> skip
    fi

    if 
    ::  opts.doFlush2 ->
        atomic {
            sem_id=2
            printf("@@@ %d CALL sema_flush %d\n",_pid, sem_id);
                        /*  (self,   sem_id, rc) */
            sema_flush(taskid, sem_id, rc);
            printf("@@@ %d SCALAR rc %d\n",_pid, rc);
        }
    ::  else -> skip
    fi



    if 
    ::  opts.doDelete ->
        sem_id=1
        TestSyncObtain(task1Sema);
           
        printf("@@@ %d CALL sema_delete %d\n",_pid, sem_id);
                  /*  (self,   sem_id, rc) */
        sema_delete(taskid, sem_id, rc);
        printf("@@@ %d SCALAR rc %d\n",_pid, rc);
      
        TestSyncRelease(task1Sema);
    ::  else -> skip
    fi

    if 
    ::  opts.doDelete2 ->
        sem_id=2;
        TestSyncObtain(task1Sema);
           
        printf("@@@ %d CALL sema_delete2 %d\n",_pid, sem_id);
                  /*  (self,   sem_id, rc) */
        sema_delete(taskid, sem_id, rc);
        printf("@@@ %d SCALAR rc %d\n",_pid, rc);
      
        TestSyncRelease(task1Sema);
    ::  else -> skip
    fi
    
    
    if
    ::  opts.doPriorityInversion ->
        TestSyncRelease(task2Sema);
        TestSyncRelease(task3Sema);    
    :: else ->
        // Make sure everyone ran
        TestSyncObtain(task1Sema);
    fi

    // semWait for other tasks to finish
    TestSyncObtain(task2Sema);
    TestSyncObtain(task3Sema);

    // If Runner at low priority, now set to medium for teardown.
    if 
    :: semstate[taskid].initialPriority == LOW_PRIORITY 
         -> printf( "@@@ %d LOG Setting Task %d to Normal priority\n"
                   , _pid, taskid );
            printf( "@@@ %d CALL NormalPriority\n", _pid );
    :: else -> skip
    fi

    printf("@@@ %d LOG Task %d finished\n",_pid,taskid);
    tasks[taskid].state = Zombie;
    printf("@@@ %d STATE %d Zombie\n",_pid,taskid)    
}



proctype Worker0 (byte nid, taskid; TaskInputs opts) {

    byte sc;
    printf( "@@@ %d DECL byte sc\n", _pid );
    byte prio ;
    printf( "@@@ %d DECL byte prio\n", _pid );

    tasks[taskid].nodeid = nid;
    tasks[taskid].pmlid = _pid;
    semstate[taskid].taskCeilingPriority = opts.taskPrio;
    tasks[taskid].preemptable = opts.taskPreempt;
    semstate[taskid].initialPriority = opts.taskInitialPriority;
    semstate[taskid].effectivePriority = opts.taskInitialPriority;


    printf("@@@ %d TASK Worker0\n",_pid);
    if 
    :: semstate[taskid].initialPriority == HIGH_PRIORITY -> printf("@@@ %d CALL HighPriority\n", _pid);
    :: semstate[taskid].initialPriority == MED_PRIORITY -> printf("@@@ %d CALL NormalPriority\n", _pid);
    :: semstate[taskid].initialPriority == LOW_PRIORITY -> printf("@@@ %d CALL LowPriority\n", _pid);
    fi

    // Preemption check setup, uncomment if necessary
    //printf("@@@ %d CALL StartLog\n",_pid);
    byte rc;
    byte sem_id;
    if
    :: opts.idNull -> sem_id = 0;
    :: else -> sem_id = 1;
    fi

    //if
    //:: multicore ->
    //    printf("@@@ %d CALL SetProcessor %d\n", _pid, tasks[taskid].nodeid);
    //:: else -> skip
    //fi


    TestSyncObtain(task2Sema);

    if
    ::  opts.doCreate ->
        sem_id=1
        printf("@@@ %d CALL merge_attribs %d %d %d %d \n", _pid, opts.isGlobal, opts.isPriority, opts.semType, opts.LockingProtocol);

        printf("@@@ %d CALL sema_create %d %d %d %d \n", 
                _pid, opts.sName, opts.Count, opts.taskPrio, sem_id);
                /*  (name,      count,       max Count,      scope,        rtems_priority,     sem_type,     locking,           task_priority,   id, rc) */
        sema_create(opts.sName, opts.Count, opts.maxCount, opts.isGlobal, opts.isPriority, opts.semType, opts.LockingProtocol, opts.taskPrio, sem_id, rc);

        if
        ::  rc == RC_OK ->
            printf("@@@ %d SCALAR created %d\n", _pid, sem_id);
        :: else -> skip;
        fi
        printf("@@@ %d SCALAR rc %d\n",_pid, rc);
    ::  else -> //ident
            sem_id=1
            printf("@@@ %d CALL sema_ident %d %d %d\n", _pid, opts.sName, nid, sem_id);
                                                            /* (name,   node, id,  rc) */
            sema_ident(opts.sName,nid,sem_id,rc);
            printf("@@@ %d SCALAR rc %d\n",_pid, rc);
    fi

    if
    ::  opts.doCreate2 ->
        sem_id=2;
        printf("@@@ %d CALL merge_attribs2 %d %d %d %d \n", _pid, opts.isGlobal, opts.isPriority, opts.semType, opts.LockingProtocol);

        printf("@@@ %d CALL sema_create2 %d %d %d %d \n", 
                _pid, SEMAPHORE2_NAME, opts.Count, opts.taskPrio, sem_id);
                /*  (name,      count,       max Count,      scope,        rtems_priority,     sem_type,     locking,           task_priority,   id, rc) */
        sema_create(SEMAPHORE2_NAME, opts.Count, opts.maxCount, opts.isGlobal, opts.isPriority, opts.semType, opts.LockingProtocol, opts.taskPrio, sem_id, rc);

        if
        ::  rc == RC_OK ->
            printf("@@@ %d SCALAR created2 %d\n", _pid, sem_id);
        :: else -> skip;
        fi
        printf("@@@ %d SCALAR rc %d\n",_pid, rc);
    ::  else -> //ident
            sem_id=2
            printf("@@@ %d CALL sema_ident2 %d %d %d\n", _pid, SEMAPHORE2_NAME, nid, sem_id);
                                                            /* (name,   node, id,  rc) */
            sema_ident(SEMAPHORE2_NAME,nid,sem_id,rc);
            printf("@@@ %d SCALAR rc %d\n",_pid, rc);
    fi


    if
    ::  opts.doAcquire -> 
        atomic{
            sem_id=1
            if
            :: opts.doPriorityInversion -> skip;
            :: else -> TestSyncRelease(task3Sema); 
            fi
            printf("@@@ %d CALL sema_obtain %d %d %d\n",
                    _pid, sem_id, opts.semWait, opts.timeoutLength);
                    /* (self,   sem_id, optionset, timeout,   rc) */
            sema_obtain(taskid, sem_id, opts.semWait, opts.timeoutLength, rc);           
        }
        
        printf("@@@ %d SCALAR rc %d\n",_pid, rc);
    ::  else -> TestSyncRelease(task3Sema);
    fi

    if
    ::  opts.doPriorityInversion ->
        atomic {
            if :: model_semaphores[sem_id].LockingProtocol == CEILING_LOCKING ->
                TestSyncRelease(task1Sema);
            :: else -> 
                TestSyncRelease(task1Sema);
                TestSyncObtain(task2Sema);
            fi
        }             
    ::  else -> 
        atomic {
            TestSyncObtain(task2Sema);
        }
    fi

    
    //==============================================
    // 2. Task H: Blocked on the resource, waiting for Task L.
    
    if
    ::  opts.doAcquire2 -> 
        atomic{
            sem_id=2;
            printf("@@@ %d CALL sema_obtain2 %d %d %d\n",
                    _pid, sem_id, opts.semWait, opts.timeoutLength);
                    /* (self,   sem_id, optionset, timeout,   rc) */
            sema_obtain(taskid, sem_id, opts.semWait, opts.timeoutLength, rc);
           
        }
        
        printf("@@@ %d SCALAR rc %d\n",_pid, rc);
    ::  else -> skip;
    fi
    

    if
    ::  opts.doRelease -> 
        atomic{
            sem_id=1
            printf("@@@ %d CALL sema_release %d\n", _pid, sem_id);
                        /* (self,   sem_id, rc) */
            sema_release(taskid, sem_id, rc);
            if
            :: rc == RC_OK -> 
                printf("@@@ %d SCALAR released %d\n", _pid, sem_id);
            :: else -> skip;
            fi
            printf("@@@ %d SCALAR rc %d\n",_pid, rc);
    }
           
    ::  else -> skip;
    fi

    if
    ::  opts.doRelease2 -> 
        atomic{
            sem_id=2;
            printf("@@@ %d CALL sema_release2 %d\n", _pid, sem_id);
                        /* (self,   sem_id, rc) */
            sema_release(taskid, sem_id, rc);
            if
            :: rc == RC_OK -> 
                printf("@@@ %d SCALAR released %d\n", _pid, sem_id);
            :: else -> skip;
            fi
            printf("@@@ %d SCALAR rc %d\n",_pid, rc);
    }
           
    ::  else -> skip;
    fi


    if
    ::  opts.doPriorityInversion ->
        atomic {
            TestSyncRelease(task3Sema); 
            TestSyncObtain(task2Sema);
        }
    ::  else -> skip;
    fi

    //==============================================
    // 6. Task H: Finally acquires the resource

    if 
    ::  opts.doFlush ->
        atomic {
            sem_id=1
            printf("@@@ %d CALL sema_flush %d\n",_pid, sem_id);
                                /*  (self,   sem_id, rc) */
            sema_flush(taskid, sem_id, rc);
            printf("@@@ %d SCALAR rc %d\n",_pid, rc);
        }
    ::  else -> skip
    fi

    if 
    ::  opts.doFlush2 ->
        atomic {
            sem_id=2
            printf("@@@ %d CALL sema_flush %d\n",_pid, sem_id);
                        /*  (self,   sem_id, rc) */
            sema_flush(taskid, sem_id, rc);
            printf("@@@ %d SCALAR rc %d\n",_pid, rc);
        }
    ::  else -> skip
    fi
    


    if 
    ::  opts.doDelete ->
        sem_id=1
        printf("@@@ %d CALL sema_delete %d\n",_pid, sem_id);
                  /*  (self,   sem_id, rc) */
        sema_delete(taskid, sem_id, rc);
        printf("@@@ %d SCALAR rc %d\n",_pid, rc);
    ::  else -> skip
    fi

    if 
    ::  opts.doDelete2 ->
        sem_id=2;
        printf("@@@ %d CALL sema_delete2 %d\n",_pid, sem_id);
                  /*  (self,   sem_id, rc) */
        sema_delete(taskid, sem_id, rc);
        printf("@@@ %d SCALAR rc %d\n",_pid, rc);
    ::  else -> skip
    fi

    //==============================================
    // End

    TestSyncRelease(task1Sema);
    atomic{
        TestSyncRelease(task2Sema);
        printf("@@@ %d LOG Task %d finished\n",_pid,taskid);
        tasks[taskid].state = Zombie;
        printf("@@@ %d STATE %d Zombie\n",_pid,taskid)
    }
}

proctype Worker1 (byte nid, taskid; TaskInputs opts) {
   
    byte sc;
    printf( "@@@ %d DECL byte sc\n", _pid );
    byte prio ;
    printf( "@@@ %d DECL byte prio\n", _pid );
  
    
    tasks[taskid].nodeid = nid;
    tasks[taskid].pmlid = _pid;
    semstate[taskid].taskCeilingPriority = opts.taskPrio;
    tasks[taskid].preemptable = opts.taskPreempt;
    semstate[taskid].initialPriority = opts.taskInitialPriority;
    semstate[taskid].effectivePriority = opts.taskInitialPriority;


    printf("@@@ %d TASK Worker1\n",_pid);
    if 
    :: semstate[taskid].initialPriority == HIGH_PRIORITY -> printf("@@@ %d CALL HighPriority\n", _pid);
    :: semstate[taskid].initialPriority == MED_PRIORITY -> printf("@@@ %d CALL NormalPriority\n", _pid);
    :: semstate[taskid].initialPriority == LOW_PRIORITY -> printf("@@@ %d CALL LowPriority\n", _pid);
    fi

    // Preemption check setup, uncomment if necessary
    //printf("@@@ %d CALL StartLog\n",_pid);

    byte rc;
    byte sem_id;
    if
    :: opts.idNull -> sem_id = 0;
    :: else -> sem_id = 1;
    fi

    //if
    //:: multicore ->
    //    printf("@@@ %d CALL SetProcessor %d\n", _pid, tasks[taskid].nodeid);
    //:: else -> skip
    //fi
    
    TestSyncObtain(task3Sema);


    if
    ::  opts.doCreate ->
        sem_id=1
        printf("@@@ %d CALL merge_attribs %d %d %d %d \n", _pid, opts.isGlobal, opts.isPriority, opts.semType, opts.LockingProtocol);

        printf("@@@ %d CALL sema_create %d %d %d %d \n", 
                _pid, opts.sName, opts.Count, opts.taskPrio, sem_id);
                /*  (name,      count,       max Count,      scope,        rtems_priority,     sem_type,     locking,           task_priority,   id, rc) */
        sema_create(opts.sName, opts.Count, opts.maxCount, opts.isGlobal, opts.isPriority, opts.semType, opts.LockingProtocol, opts.taskPrio, sem_id, rc);

        if
        ::  rc == RC_OK ->
            printf("@@@ %d SCALAR created %d\n", _pid, sem_id);
        :: else -> skip;
        fi
        printf("@@@ %d SCALAR rc %d\n",_pid, rc);
    ::  else -> //ident
            sem_id=1
            printf("@@@ %d CALL sema_ident %d %d %d\n", _pid, opts.sName, nid, sem_id);
                                                            /* (name,   node, id,  rc) */
            sema_ident(opts.sName,nid,sem_id,rc);
            printf("@@@ %d SCALAR rc %d\n",_pid, rc);
    fi

    if
    ::  opts.doCreate2 ->
        sem_id=2;
        printf("@@@ %d CALL merge_attribs2 %d %d %d %d \n", _pid, opts.isGlobal, opts.isPriority, opts.semType, opts.LockingProtocol);

        printf("@@@ %d CALL sema_create2 %d %d %d %d \n", 
                _pid, SEMAPHORE2_NAME, opts.Count, opts.taskPrio, sem_id);
                /*  (name,      count,       max Count,      scope,        rtems_priority,     sem_type,     locking,           task_priority,   id, rc) */
        sema_create(SEMAPHORE2_NAME, opts.Count, opts.maxCount, opts.isGlobal, opts.isPriority, opts.semType, opts.LockingProtocol, opts.taskPrio, sem_id, rc);

        if
        ::  rc == RC_OK ->
            printf("@@@ %d SCALAR created2 %d\n", _pid, sem_id);
        :: else -> skip;
        fi
        printf("@@@ %d SCALAR rc %d\n",_pid, rc);
    ::  else -> //ident
            sem_id=2;
            printf("@@@ %d CALL sema_ident2 %d %d %d\n", _pid, SEMAPHORE2_NAME, nid, sem_id);
                                                            /* (name,   node, id,  rc) */
            sema_ident(SEMAPHORE2_NAME,nid,sem_id,rc);
            printf("@@@ %d SCALAR rc %d\n",_pid, rc);
    fi


    if
    ::  opts.doPriorityInversion ->
        atomic {
            TestSyncRelease(task1Sema);
            TestSyncObtain(task3Sema);
        }
        
    ::  else -> skip;
    fi

    if
    ::  opts.doAcquire -> 
        atomic{
            sem_id=1
            if
            :: opts.doPriorityInversion -> skip;
            :: else -> TestSyncRelease(task1Sema);
            fi
            
            printf("@@@ %d CALL sema_obtain %d %d %d\n",
                    _pid, sem_id, opts.semWait, opts.timeoutLength);
                    /* (self,   sem_id, optionset, timeout,   rc) */
            sema_obtain(taskid, sem_id, opts.semWait, opts.timeoutLength, rc);
            
 
        }
        
        printf("@@@ %d SCALAR rc %d\n",_pid, rc);

    ::  else -> TestSyncRelease(task1Sema);
    fi

    if
    ::  opts.doAcquire2 -> 
        atomic{
            sem_id=2;
            
            printf("@@@ %d CALL sema_obtain2 %d %d %d\n",
                    _pid, sem_id, opts.semWait, opts.timeoutLength);
                    /* (self,   sem_id, optionset, timeout,   rc) */
            sema_obtain(taskid, sem_id, opts.semWait, opts.timeoutLength, rc);
            
        }
        
        printf("@@@ %d SCALAR rc %d\n",_pid, rc);

    ::  else -> skip;
    fi
    

    

    if
    ::  opts.doRelease ->
        atomic{
            sem_id=1
            printf("@@@ %d CALL sema_release %d\n", _pid, sem_id);
                        /* (self,   sem_id, rc) */
            sema_release(taskid, sem_id, rc);
            if
            :: rc == RC_OK -> 
                printf("@@@ %d SCALAR released %d\n", _pid, sem_id);
            :: else -> skip;
            fi
            printf("@@@ %d SCALAR rc %d\n",_pid, rc);
        }

    ::  else -> skip;
    fi


    if
    ::  opts.doRelease2 ->
        atomic{
            sem_id=2;
            printf("@@@ %d CALL sema_release2 %d\n", _pid, sem_id);
                        /* (self,   sem_id, rc) */
            sema_release(taskid, sem_id, rc);
            if
            :: rc == RC_OK -> 
                printf("@@@ %d SCALAR released %d\n", _pid, sem_id);
            :: else -> skip;
            fi
            printf("@@@ %d SCALAR rc %d\n",_pid, rc);
        }

    ::  else -> skip;
    fi

    if 
    ::  opts.doFlush ->
        atomic {
            sem_id=1
            printf("@@@ %d CALL sema_flush %d\n",_pid, sem_id);
                                /*  (self,   sem_id, rc) */
            sema_flush(taskid, sem_id, rc);
            printf("@@@ %d SCALAR rc %d\n",_pid, rc);
        }
    ::  else -> skip
    fi

    if 
    ::  opts.doFlush2 ->
        atomic {
            sem_id=2
            printf("@@@ %d CALL sema_flush %d\n",_pid, sem_id);
                        /*  (self,   sem_id, rc) */
            sema_flush(taskid, sem_id, rc);
            printf("@@@ %d SCALAR rc %d\n",_pid, rc);
        }
    ::  else -> skip
    fi
    

    if 
    ::  opts.doDelete ->
        sem_id=1
        printf("@@@ %d CALL sema_delete %d\n",_pid, sem_id);
                  /*  (self,   sem_id, rc) */
        sema_delete(taskid, sem_id, rc);
        printf("@@@ %d SCALAR rc %d\n",_pid, rc);
    ::  else -> skip
    fi





    if 
    ::  opts.doDelete2 ->
        sem_id=2;
        printf("@@@ %d CALL sema_delete2 %d\n",_pid, sem_id);
                  /*  (self,   sem_id, rc) */
        sema_delete(taskid, sem_id, rc);
        printf("@@@ %d SCALAR rc %d\n",_pid, rc);
    ::  else -> skip
    fi
    
    atomic {
        TestSyncRelease(task2Sema);
        TestSyncRelease(task3Sema);
        printf("@@@ %d LOG Task %d finished\n",_pid,taskid);
        tasks[taskid].state = Zombie;
        printf("@@@ %d STATE %d Zombie\n",_pid,taskid)
    }
}

init {

    pid nr;

    printf("Semaphore Manager Model running.\n");
    printf("Setup...\n");

    printf("@@@ %d LOG TestName: Semaphore_Manager_TestGen\n",_pid)
    outputDefines();
    outputDeclarations();

    init_semaphore_priority_queue(1);
    init_semaphore_priority_queue(2);

    printf("@@@ %d INIT\n",_pid);
    chooseScenario();

    printf("Run...\n");

    run System();
    run Clock();
    

    run Runner(task1Core,TASK1_ID,task_in[TASK1_ID]);
    run Worker0(task2Core,TASK2_ID,task_in[TASK2_ID]);
    run Worker1(task3Core,TASK3_ID,task_in[TASK3_ID]);
    
    
    

    _nr_pr == 1;

    #ifdef TEST_GEN
    assert(false);
    #endif

    printf("Semaphore Manager Model finished !\n")

}
