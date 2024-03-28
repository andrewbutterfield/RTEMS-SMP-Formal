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

// Wait optionset for semaphore_obtain
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


// Return Values
// Defined in cpukit/include/rtems/rtems/status.h
#define RC_OK      0  // RTEMS_SUCCESSFUL 
#define RC_InvName 3  // RTEMS_INVALID_NAME 
#define RC_InvId   4  // RTEMS_INVALID_ID 
#define RC_TooMany 5  // RTEMS_TOO_MANY 
#define RC_Timeout 6  // RTEMS_TIMEOUT 
#define RC_Deleted 7  // RTEMS_OBJECT_WAS_DELETED 
#define RC_InvAddr 9  // RTEMS_INVALID_ADDRESS 
#define RC_InvNum  10 // RTEMS_INVALID_NUMBER 
#define RC_InvPrio 19 // RTEMS_INVALID_PRIORITY
#define RC_NotDefined  11 // RTEMS_NOT_DEFINED item has not been initialised
#define RC_ResourceInUse 12 // RTEMS_RESOURCE_IN_USE
#define RC_Unsatisfied  13 // RTEMS_UNSATISFIED This is the status to indicate that the request was not satisfied.
#define RC_NotOwner 23 // RTEMS_NOT_OWNER_OF_RESOURCE

#define RC_InvalidPriority 100 // todo RTEMS_INVALID_PRIORITY

/* 
 * Multicore setup
 */
bool multicore;
int task1Core;
int task2Core;
int task3Core;

// We envisage three RTEMS tasks involved.
#define TASK_MAX 4 // These are the "RTEMS" tasks only, numbered 1 & 2 & 3,
                   // We reserve 0 to model NULL pointers


// We use mutexes to synchronise the tasks
#define SEMA_MAX 3

mtype = {
// Task states, SemaWait is same as TimeWait but with no timeout
  Zombie, Ready, SemaWait, TimeWait, OtherWait 
};

typedef Task {
    byte nodeid; // So we can spot remote calls
    byte pmlid; // Promela process id
    mtype state ; // {Ready,SemaWait,TimeWait,OtherWait}
    bool preemptable;
    byte prio; // task's ceiling priority - lower number is higher priority
    byte initialPriority // task's initial/default priority
    int effectivePriority; // task's current active priority
    int ticks; // clock ticks to keep track of timeout
    bool tout; // true if woken by a timeout
};

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
    int ownerPid; // set to pid of the task that obtained the binary semaphore
    int currPriority; // tracks the current elevated priority of the semaphore's task holder
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
Task tasks[TASK_MAX];


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
 *  Acquire;;Release = Semaphore is acquired and then released
 *  Acquire;;Delete = Semaphore is acquired and then deleted
 * Here ;; is "sequential" composition of *different* threads.
 * Additionally task 1 will always create a semaphore before operations
 */
bool semaphore[SEMA_MAX]; // Mutexes

inline outputDeclarations () {
  printf("@@@ %d DCLARRAY Semaphore semaphore SEMA_MAX\n",_pid);
}

/*
 * Synchronisation Mechanisms
 *
 *  Obtained(sema_id) - call that waits if sema 
 *   `sema_id` is aquired by someone.
 *  Obtain(sema_id) - obttains sema `sema_id`
 *  Release(sema_id)  - call that releases sema `sema_id`
 *
 * Mutexes:  True means available, False means in use.
 */

inline Obtain(sema_id){
  atomic{
    printf("@@@ %d WAIT %d\n",_pid,sema_id);
    semaphore[sema_id] ;        // wait until available
    semaphore[sema_id] = false; // set as in use
    printf("@@@ %d LOG WAIT %d Over\n",_pid,sema_id);
  }
}

inline Release(sema_id){
  atomic{
    printf("@@@ %d SIGNAL %d\n",_pid,sema_id);
    semaphore[sema_id] = true ; // release
  }
}




inline nl() { printf("\n") } // Useful shorthand


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
        //::  locking != NO_LOCKING -> rc = RC_NotDefined;
        ::  else ->
            if
            ::  id < MAX_MODEL_SEMAS ->
                if
                ::  !model_semaphores[id].isInitialised ->
                    if
                    ::  sem_type == COUNTING_S -> //sem_type
                        if 
                        ::  task_priority != 0 -> rc = RC_InvPrio;
                        ::  count == 0 -> rc = RC_InvNum;
                        ::  else -> skip;
                        fi

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
                        printf("@@@ %d LOG %d Created {n: %d, count: %d, global: %d, RTEMS_Priority:%d, sem_type: counting, locking protocol: None, task_priority:%d}\n", _pid, id, name, count, scope, rtems_priority, task_priority);
                        
                
                    ::  sem_type == BINARY_S ->

                        model_semaphores[id].maxCount = 1;
                        model_semaphores[id].LockingProtocol = locking;
                        model_semaphores[id].s_name = name;
                        model_semaphores[id].semType = sem_type;
                        model_semaphores[id].isGlobal = scope; //if local can only be used by node that created it
                        model_semaphores[id].Priority = rtems_priority;
                        model_semaphores[id].currPriority = task_priority;
                        model_semaphores[id].isInitialised = true;
                        model_semaphores[id].priorityCeiling = task_priority;
                        rc = RC_OK;
                        if
                        ::  count ==1 -> model_semaphores[id].Count = count;
                        ::  count ==0 -> model_semaphores[id].Count = count; // make task the owner
                            model_semaphores[id].ownerPid = _pid;
                        ::  else -> rc = RC_InvNum;
                        fi
                        printf("@@@ %d LOG %d Created {n: %d, count: %d, global: %d, RTEMS_Priority:%d, sem_type: binary, locking protocol: None, task_priority:%d}\n", _pid, id, name, count, scope, rtems_priority, task_priority);

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
        rc = RC_Unsatisfied;
        printf("@@@ %d LOG task %d flushed from Semaphore %d \n", _pid, tid, sem_id); //semaphore obtained
    ::  else -> model_semaphores[sem_id].Count = model_semaphores[sem_id].Count -1;
                rc = RC_OK;
                printf("@@@ %d LOG Semaphore %d obtained\n", _pid, sem_id); //semaphore obtained
    fi
 
}


inline waitUntilReady(taskid) {
    atomic {
        printf("@@@ %d LOG Task %d waiting, state = ", _pid, taskid);
        printm(tasks[taskid].state); // Assuming printm is a macro or function that prints the task state
        nl(); // New line for clearer logs
        // The task waits here until its state changes to Ready.
        // In a real system, this would be managed by the scheduler which would change the task's state based on semaphore availability or other scheduling decisions.
        // In this simplified model, we use an explicit condition that must be met for the task to proceed.
        tasks[taskid].state == Ready;
        printf("@@@ %d STATE %d Ready\n", _pid, taskid);
    }
}



inline preemptIfRequired(tid, preempting_tid, rc) {
  if
  ::  tasks[tid].preemptable  &&
      tasks[preempting_tid].effectivePriority < tasks[tid].effectivePriority ->  
        tasks[tid].state = OtherWait;
        printf("@@@ %d LOG preemptIfRequired current task %d was preempted by task %d\n", _pid, tid, preempting_tid);
        printf("@@@ %d STATE %d OtherWait\n",_pid,tid);
        printf("@@@ %d STATE %d Ready\n", _pid, preempting_tid);
        rc = true;
  ::  else -> 
        printf("@@@ %d LOG preemptIfRequired current task %d was NOT preempted by task %d\n", _pid, tid, preempting_tid);
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


inline priority_enqueue(sem_id, task_id, Priority) {
    atomic {
        printf("@@@ %d LOG ==================priority_enqueue", _pid);
        if
        :: queueList[sem_id].queueFull == false ->
            // The queue is not full
            int i = queueList[sem_id].tail;
            do
            :: i >= queueList[sem_id].head && tasks[queueList[sem_id].waitingTasks[i]].prio > Priority ->
                printf("@@@ %d LOG true! %d > %d\n", _pid, tasks[queueList[sem_id].waitingTasks[i]].prio, Priority);
                // Shift elements to make room for the new task in the sorted order
                queueList[sem_id].waitingTasks[i + 1] = queueList[sem_id].waitingTasks[i];
                i--;
            :: else -> break;
            od;
            // Insert the task at the correct position in the sorted queue
            queueList[sem_id].waitingTasks[i + 1] = task_id;
            if
            :: queueList[sem_id].queueFull == false ->
                queueList[sem_id].tail++; // Increment the tail
                if
                :: queueList[sem_id].tail == TASK_MAX - 1 ->
                    queueList[sem_id].queueFull = true; // Mark the queue as full
                :: else ->
                    skip;
                fi
            fi
        :: else ->
            // The queue is full
            skip;
        fi
        
        // print current queue
        if
        :: queueList[sem_id].tail >= queueList[sem_id].head ->
            int j = queueList[sem_id].head;
            do
            :: j <= queueList[sem_id].tail ->
                printf("@@@ %d LOG task %d QQQ queueList[%d].waitingTasks[%d] = %d\n", _pid, task_id, sem_id, j, queueList[sem_id].waitingTasks[j]);
                j++;
            :: else -> break;
            od
        fi
    }
}


inline priority_dequeue(sem_id, task_id) {
    atomic {
        if
        :: queueList[sem_id].head <= queueList[sem_id].tail ->
            // The queue is not empty
            task_id = queueList[sem_id].waitingTasks[queueList[sem_id].head];
            printf("@@@ %d LOG testing %d\n", _pid, task_id);
            queueList[sem_id].head++; // Increment the head
            if
            :: queueList[sem_id].head > queueList[sem_id].tail ->
                // Reset the queue state when it becomes empty
                queueList[sem_id].head = 0;
                queueList[sem_id].tail = 0;
                queueList[sem_id].queueFull = false;
            :: else ->
                skip;
            fi
        :: else ->
            // The queue is empty
            task_id = 0;
        fi
    }
}



inline sema_set_priority(sem_id, scheduler_id, new_priority, old_priority, rc) {
    atomic {
        printf("@@@ % LOG ===model_semaphores[sem_id].LockingProtocol = %d, which should equal %d\n", _pid, model_semaphores[sem_id].LockingProtocol, NO_LOCKING);
        if
        :: sem_id == 0 ->
            rc = RC_InvId;
        // :: old_priority == NULL ->
        //     rc = RC_InvAddr;
        :: model_semaphores[sem_id].LockingProtocol == NO_LOCKING ->
            rc = RC_NotDefined;
        :: else ->
            // if
            // :: scheduler_id != SCHED_A && scheduler_id != SCHED_B ->
            //     rc = RC_InvId;
            // :: else ->
                // Initialize old_priority
                old_priority = 0;
                // // Find scheduler index
                // int scheduler_index = 0;
                // if
                // :: scheduler_id == SCHED_A ->
                //     scheduler_index = 1;
                // :: scheduler_id == SCHED_B ->
                //     scheduler_index = 2;
                // fi
                // Save old priority
                if
                :: model_semaphores[sem_id].Priority == PRIORITY &&
                   model_semaphores[sem_id].LockingProtocol == CEILING_LOCKING ->
                    //old_priority = model_semaphores[sem_id].priorityCeiling[MY_SCHEDULER];
                    old_priority = model_semaphores[sem_id].currPriority;
                :: else ->
                    rc = RC_NotDefined;
                fi
                // Set new priority
                if
                // :: new_priority == RTEMS_CURRENT_PRIORITY ->
                //     // Return current priority without changing it
                //     rc = RC_OK;
                :: model_semaphores[sem_id].Priority == PRIORITY &&
                   model_semaphores[sem_id].LockingProtocol == CEILING_LOCKING ->
                    //model_semaphores[sem_id].priorityCeiling[scheduler_index] = new_priority;
                    model_semaphores[sem_id].currPriority = new_priority;
                    rc = RC_OK;
                :: else ->
                    rc = RC_InvalidPriority;
                fi
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
                        rc = RC_Unsatisfied;
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
                :: model_semaphores[sem_id].Count == 1 -> // Binary semaphore is available
                    model_semaphores[sem_id].Count = 0; // Acquire the binary semaphore
                    model_semaphores[sem_id].ownerPid = _pid; // Set the current pid as owner
                    rc = RC_OK;
                    printf("@@@ %d LOG Binary Semaphore %d obtained\n", _pid, sem_id);
                :: else ->
                    if
                    :: model_semaphores[sem_id].Count == 0 && optionset == RTEMS_NO_WAIT ->
                        rc = RC_Unsatisfied; // The semaphore could not be immediately obtained  
                        printf("@@@ %d LOG Semaphore %d could not be immediately obtained\n", _pid, sem_id);
                    :: else -> // RTMES_WAIT
                        printf("@@@ %d LOG ==================================\n",_pid);

                        if
                        ::  model_semaphores[sem_id].Priority == PRIORITY ->
                            // printf("@@@ %d LOG ===tasks[self].effectivePriority %d < %d model_semaphores[sem_id].currPriority\n", 
                            //     _pid, tasks[self].effectivePriority, model_semaphores[sem_id].currPriority);
                            if
                            :: tasks[self].effectivePriority < model_semaphores[sem_id].currPriority ->
                                model_semaphores[sem_id].currPriority = PRIORITY_CEILING;
                                // printf("@@@ %d CALL sema_set_priority %d\n",
                                //     _pid, sem_id);
                                //     //_pid, sem_id, MY_SCHEDULER, MY_SCHEDULER, model_semaphores[sem_id].priorityCeiling);
                                //               /* (sem_id, scheduler_id, new_priority,     old_priority,                          rc) */
                                // sema_set_priority(sem_id, MY_SCHEDULER, PRIORITY_CEILING, model_semaphores[sem_id].currPriority, rc)
                                // printf("@@@ %d SCALAR rc %d\n",_pid, rc);
                                // printf("@@@ %d LOG rc is ==== %d", _pid, rc);
                            fi
                        fi
                        
                        priority_enqueue(sem_id, self, tasks[self].effectivePriority);
                        WaitForSemaphore(self, sem_id, optionset, interval, rc);
                        rc = rc;


                    // // check if semaphore is FIFO
                    //     if
                    //     ::  model_semaphores[sem_id].Priority == FIFO ->
                    //         int binary_queue_no=1;
                    //         int binary_tid = 1;
                    //         do 
                    //         ::  binary_tid < TASK_MAX ->
                    //             if 
                    //             ::  model_semaphores[sem_id].waiters[binary_tid] != 0 -> binary_queue_no++;
                    //             ::  else -> skip;
                    //             fi
                    //             binary_tid++;
                    //         ::  else-> break;
                    //         od
                    //         model_semaphores[sem_id].waiters[self] = binary_queue_no;

                    //         if
                    //         ::  interval > NO_TIMEOUT ->
                    //             tasks[self].tout = false;
                    //             tasks[self].ticks = interval;
                    //             tasks[self].state = TimeWait;
                    //             printf("@@@ %d STATE %d TimeWait %d\n",_pid,self,interval);
                    //         ::  else -> // No timeout wait forever
                    //             tasks[self].state = SemaWait;
                    //             printf("@@@ %d STATE %d SemaWait\n",_pid,self);
                    //         fi
                    //         WaitForSemaphore(self, sem_id, optionset, interval, rc);
                    //     fi
                    fi
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
        ::  model_semaphores[sem_id].semType == BINARY_S && model_semaphores[sem_id].ownerPid != _pid ->
            rc = RC_NotOwner; // The calling task was not the owner of the semaphore
        ::  model_semaphores[sem_id].Count == UINT32_MAX ->
            rc = RC_Unsatisfied;
        ::  else -> 
            model_semaphores[sem_id].Count++;

            int tid = 1;
            if
            :: model_semaphores[sem_id].Priority == FIFO ->
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

            :: model_semaphores[sem_id].Priority == PRIORITY ->

                if
                ::  model_semaphores[sem_id].ownerPid != _pid ->
                    rc = RC_NotOwner; // The calling task was not the owner of the semaphore
                :: else ->
                    rc = RC_OK;
                fi
                // Dequeue and Schedule Next Task
                //if :: !queueList[sem_id].queueFull ->  // Check if the queue is not empty
                    int next_task_id;
                    priority_dequeue(sem_id, next_task_id);
                    printf("@@@ %d LOG task %d dequeued\n", _pid, next_task_id);
                    tasks[next_task_id].state = Ready;
                    tasks[next_task_id].effectivePriority = tasks[next_task_id].initialPriority;
            fi
        fi
    }
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
            rc = RC_ResourceInUse; // The binary semaphore had an owner
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
 */

 /*
 * Task variants:
 *   Task objectives - semaphore {Create, Acquire, Release, Delete}
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
    bool Wait; //Will the task wait to obtain the semaphore
    byte timeoutLength; // only relevant if doAcquire is true, gives wait time
    bool doDelete; // will task delete the semaphore
    bool doDelete2;
    bool doRelease; // will task release the semaphore
    bool doRelease2;
    bool doFlush; //will task flush the semaphore
    bool doFlush2;

    byte taskPrio; // This is used for setting the ceiling priority in sema_create
    byte taskInitialPriority; // The intial priority of the task
    bool taskPreempt;

    bool idNull; // indicates whenever passed id is null

    bool doPriorityInversion;
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
    opts.Wait = defaults.Wait;
    opts.timeoutLength=defaults.timeoutLength;
    opts.doDelete=defaults.doDelete;
    opts.doDelete2=defaults.doDelete2;
    opts.doFlush2=defaults.doFlush2;
    opts.doRelease=defaults.doRelease;
    opts.doRelease2=defaults.doRelease2;
    opts.doFlush=defaults.doFlush;
    opts.taskPrio=defaults.taskPrio;
    opts.taskPreempt=defaults.taskPreempt;
    opts.idNull = defaults.idNull;
    opts.doPriorityInversion = defaults.doPriorityInversion;

}


/*
 * synchronisation semaphore Setup
 */
int task1Sema;
int task2Sema;
int task3Sema;


mtype = {onesema, twosemas, dfferent_sema_counts, one_binary_sema, test_priority_ceiling};
mtype scenario;

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
    defaults.Wait = false;
    defaults.timeoutLength = NO_TIMEOUT;
    defaults.doDelete = false;
    defaults.doDelete2 = false;
    defaults.doFlush=false;
    defaults.doFlush2=false;
    defaults.taskPrio = 2;
    defaults.taskPreempt = false;
    defaults.idNull = false;
    defaults.sName = SEMAPHORE1_NAME;
    defaults.doPriorityInversion = false;


    // Set the defaults
    assignDefaults(defaults, task_in[TASK1_ID]);
    task_in[TASK1_ID].doCreate = true; // Task 1 is always the creator
    assignDefaults(defaults, task_in[TASK2_ID]);
    assignDefaults(defaults, task_in[TASK3_ID]);


    // synchronization semaphore initialization
    semaphore[0] = false;
    task1Sema = 0;
    semaphore[1] = false;
    task2Sema = 1;
    semaphore[2] = false;
    task3Sema = 2;

    tasks[TASK1_ID].state = Ready;
    tasks[TASK2_ID].state = Ready;
    tasks[TASK3_ID].state = Ready;

    multicore = false;
    task1Core = THIS_CORE;
    task2Core = THIS_CORE;
    task3Core = THIS_CORE;

    if
    // ::  scenario = onesema;
    // ::  scenario = twosemas;
    // ::  scenario = dfferent_sema_counts;
    // ::  scenario = one_binary_sema;
    ::  scenario = test_priority_ceiling;
    fi
    atomic{printf("@@@ %d LOG scenario ",_pid); printm(scenario); nl()}
    
    if
    ::  scenario==onesema->true
    
        if
        ::  task_in[TASK1_ID].sName = 0;
            printf( "@@@ %d LOG sub-senario bad create, invalid name\n", _pid); //RTEMS_INVALID_NAME
        ::  task_in[TASK1_ID].idNull = true;
            printf( "@@@ %d LOG sub-senario bad create, passed id null\n", _pid); //RTEMS_INVALID_ADDRESS
        ::  task_in[TASK1_ID].Count = 0;
            printf( "@@@ %d LOG sub-senario bad create, passed invalid initial count\n", _pid); //RTEMS_INVALID_NUMBER
        ::  task_in[TASK1_ID].LockingProtocol = INHERIT_LOCKING;
            printf( "@@@ %d LOG sub-senario bad create, passed invalid locking protocol\n", _pid); //RTEMS_INVALID_PRIORITY
        ::  task_in[TASK1_ID].doDelete = true;
            printf( "@@@ %d LOG sub-senario created and deleted\n", _pid); //RTEMS_SUCCESSFUL    
        ::  task_in[TASK1_ID].Count = UINT32_MAX - 1;
            task_in[TASK1_ID].doRelease = true;
            task_in[TASK2_ID].doRelease = true;
            printf( "@@@ %d LOG sub-senario created, release at max count\n", _pid); // RTEMS_UNSATISFIED   
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
            task_in[TASK3_ID].Wait = true;
            task_in[TASK2_ID].doRelease=true;
            task_in[TASK3_ID].doRelease = false;
            printf( "@@@ %d LOG sub-senario WAIT no timeout\n", _pid);   
            //wait with no timeout scenario

        ::  task_in[TASK2_ID].doAcquire = true;
            task_in[TASK3_ID].doAcquire = true;
            task_in[TASK3_ID].Wait = true;
            task_in[TASK3_ID].timeoutLength = 2;
            task_in[TASK2_ID].doRelease=true;
            task_in[TASK3_ID].doRelease = true;
            //timeout scenario

        ::  task_in[TASK2_ID].doAcquire= true;
            task_in[TASK3_ID].doAcquire = true;
            task_in[TASK3_ID].Wait = true;
            task_in[TASK2_ID].doRelease= false;
            task_in[TASK3_ID].doRelease = false;
            task_in[TASK2_ID].doFlush= true;
            task_in[TASK2_ID].doRelease = false;

            printf( "@@@ %d LOG sub-senario FLUSH\n", _pid);  
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
            task_in[TASK3_ID].Wait = true;
            task_in[TASK2_ID].doRelease=true;
            task_in[TASK3_ID].doRelease = false;
            task_in[TASK2_ID].doAcquire2 = true;
            task_in[TASK3_ID].doAcquire2 = true;
            task_in[TASK2_ID].doRelease2=true;
            task_in[TASK3_ID].doRelease2 = false;
            //wait with no timeout  


        fi

    // Counting semaphores with different counts 
    :: scenario == dfferent_sema_counts ->
        if
        :: task_in[TASK1_ID].Count = 0 ->
            printf("@@@ %d LOG sub-senario created, sema_count = 0\n", _pid);
        :: task_in[TASK1_ID].Count = 1 ->
            printf("@@@ %d LOG sub-senario created, sema_count = 1\n", _pid);
            task_in[TASK1_ID].maxCount = 1;
            task_in[TASK1_ID].doCreate = true;
            task_in[TASK1_ID].doAcquire = true;
            task_in[TASK1_ID].doRelease = true;
        :: task_in[TASK1_ID].Count = 2 ->
            printf("@@@ %d LOG sub-senario created, sema_count = 2\n", _pid);
            task_in[TASK1_ID].maxCount = 2;
            task_in[TASK1_ID].doCreate = true;
            task_in[TASK1_ID].doAcquire = true;
            task_in[TASK2_ID].doAcquire = true;
            task_in[TASK1_ID].doRelease = true;
            task_in[TASK2_ID].doRelease = true;
        :: task_in[TASK1_ID].Count = 3 ->
            printf("@@@ %d LOG sub-senario created, sema_count = 3\n", _pid);
            task_in[TASK1_ID].maxCount = 3;
            task_in[TASK1_ID].doCreate = true;
            task_in[TASK1_ID].doAcquire = true;
            task_in[TASK2_ID].doAcquire = true;
            task_in[TASK3_ID].doAcquire = true;
            task_in[TASK1_ID].doRelease = true;
            task_in[TASK2_ID].doRelease = true;
            task_in[TASK3_ID].doRelease = true;
         fi

    ::  scenario == one_binary_sema ->

        // Set up a binary semaphore
        task_in[TASK1_ID].semType = BINARY_S;
        task_in[TASK1_ID].doCreate = true;

        // Task 1 acquires the semaphore
        task_in[TASK1_ID].doAcquire = true;

        // Task 2 tries to acquire the semaphore, but it SHOULD be blocked
        task_in[TASK2_ID].doAcquire = true;
     
        // Task 2 tries to release the semaphore that it does not have/own, it SHOULD be unsatisfied
        task_in[TASK2_ID].doRelease = true;

        // Task 1 releases the semaphore
        task_in[TASK1_ID].doRelease = true;

        // Delete the semaphore
        task_in[TASK1_ID].doDelete = true;

        printf("@@@ %d LOG sub-senario created, testing binary semaphore\n", _pid);
        // fi

    ::  scenario == test_priority_ceiling ->
        task_in[TASK1_ID].semType = BINARY_S;
        task_in[TASK2_ID].semType = BINARY_S;
        task_in[TASK3_ID].semType = BINARY_S;

        task_in[TASK1_ID].Wait = true;
        task_in[TASK2_ID].Wait = true;
        task_in[TASK3_ID].Wait = true;

        task_in[TASK1_ID].taskPreempt = true;
        task_in[TASK2_ID].taskPreempt = true;
        task_in[TASK3_ID].taskPreempt = true;

        task_in[TASK1_ID].doPriorityInversion = true;
        task_in[TASK2_ID].doPriorityInversion = true;
        task_in[TASK3_ID].doPriorityInversion = true;

        // task_in[TASK1_ID].isPriority = FIFO;
        // task_in[TASK2_ID].isPriority = FIFO;
        // task_in[TASK3_ID].isPriority = FIFO;

        task_in[TASK1_ID].isPriority = PRIORITY;
        task_in[TASK2_ID].isPriority = PRIORITY;
        task_in[TASK3_ID].isPriority = PRIORITY;

        task_in[TASK1_ID].LockingProtocol = CEILING_LOCKING;
        task_in[TASK1_ID].LockingProtocol = CEILING_LOCKING;
        task_in[TASK1_ID].LockingProtocol = CEILING_LOCKING;

        // task_in[TASK1_ID].LockingProtocol = NO_LOCKING;
        // task_in[TASK1_ID].LockingProtocol = NO_LOCKING;
        // task_in[TASK1_ID].LockingProtocol = NO_LOCKING;


        // Set the priority ceiling of each of the tasks
        task_in[TASK1_ID].taskPrio = PRIORITY_CEILING;
        task_in[TASK2_ID].taskPrio = PRIORITY_CEILING;
        task_in[TASK3_ID].taskPrio = PRIORITY_CEILING;

        // Set the initial priority of each of the tasks
        task_in[TASK1_ID].taskInitialPriority = LOW_PRIORITY;
        task_in[TASK2_ID].taskInitialPriority = HIGH_PRIORITY;
        task_in[TASK3_ID].taskInitialPriority = MED_PRIORITY;

        // // Setting the priority ceiling of each of the tasks ?
        // // This somehow make it hang
        // task_in[TASK1_ID].taskPrio = LOW_PRIORITY;
        // task_in[TASK2_ID].taskPrio = HIGH_PRIORITY;
        // task_in[TASK3_ID].taskPrio = MED_PRIORITY;

        task_in[TASK1_ID].doCreate = true;

        // 1 Lower prio task runs and acquires lock
        task_in[TASK1_ID].doAcquire = true; 
        // 2 Higher prio task attempts to acquire lock - is blocked
        task_in[TASK2_ID].doAcquire = true;
        
        // 3 Medium prio task performs its logic with preference over lower

        // 4 Lower finishes and releases
        task_in[TASK1_ID].doRelease = true;

        // 5 Higher is now able to obtain
        task_in[TASK2_ID].doRelease = true;

        printf("@@@ %d LOG sub-senario created, testing priority ceiling protocol \n", _pid);

        // 1. Task L: Running, holds the shared resource.
        // Task H: Blocked on the resource, waiting for Task L.
        // Task M: Becomes ready, has higher priority than Task L, and preempts it.
        // Task M: Runs and does its work, (unrelated to the shared resource).
        // Task M: Finishes and yields the processor.
        // Task L: Resumes, still holding the resource.
        // Task H: Remains blocked waiting for Task L to finish.

    fi


}

//proctype Worker
proctype Runner (byte nid, taskid; TaskInputs opts) {

    //==============================================
    // Initial setup

    if
    ::  opts.doPriorityInversion ->
        atomic {
            Release(task3Sema);
            Obtain(task1Sema);
        }
    
    ::  else -> skip;
    fi


    //==============================================
    // 1. Task L: Running, holds the shared resource.

    tasks[taskid].nodeid = nid;
    tasks[taskid].pmlid = _pid;
    tasks[taskid].prio = opts.taskPrio;
    tasks[taskid].preemptable = opts.taskPreempt;
    tasks[taskid].initialPriority = opts.taskInitialPriority;
    tasks[taskid].effectivePriority = opts.taskInitialPriority;
    
   

    printf("@@@ %d TASK Runner\n",_pid);
    if 
    ::  tasks[taskid].initialPriority == 1 -> printf("@@@ %d CALL HighPriority\n", _pid);
    ::  tasks[taskid].initialPriority == 2 -> printf("@@@ %d CALL NormalPriority\n", _pid);
    ::  tasks[taskid].initialPriority == 3 -> printf("@@@ %d CALL LowPriority\n", _pid);
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
    ::  opts.doAcquire -> 
            sem_id=1
            printf("@@@ %d CALL sema_obtain %d %d %d\n",
                    _pid, sem_id, opts.Wait, opts.timeoutLength);
                    /* (self,   sem_id, optionset, timeout,   rc) */
            sema_obtain(taskid, sem_id, opts.Wait, opts.timeoutLength, rc);
            printf("@@@ %d SCALAR rc %d\n",_pid, rc);
    ::  else -> skip;
    fi

    if
    ::  opts.doAcquire2 -> 
            sem_id=2;
            printf("@@@ %d CALL sema_obtain2 %d %d %d\n",
                    _pid, sem_id, opts.Wait, opts.timeoutLength);
                    /* (self,   sem_id, optionset, timeout,   rc) */
            sema_obtain(taskid, sem_id, opts.Wait, opts.timeoutLength, rc);
            printf("@@@ %d SCALAR rc %d\n",_pid, rc);
    ::  else -> skip;
    fi

    
    if
    ::  opts.doPriorityInversion ->
        
        atomic {
            sem_id=1;
            // // assuming only one sched_id so only passing prios
            // int new_prio = 1;
            // //int old_prio = 3; //model_semaphores[sem_id].currPriority;
            // printf("@@@ %d CALL sema_set_priority %d\n", _pid, sem_id);
            // //sema_set_priority(sem_id, sched_id, new_prio, old_prio, rc);
            // printf("@@@ %d SCALAR rc %d\n", _pid, rc);

            Release(task2Sema);
        }
    :: else -> skip;
    fi


    //==============================================
    // 3. Task L: Resumes, still holding the resource.
    // Task H: Remains blocked waiting for Task L to finish.

    if
    ::  opts.doPriorityInversion ->
        atomic {
            printf("@@@ %d LOG ---Here MPT will preempt the LPT (this task)\n",_pid);
            // check if it can be preempted 
            rc = false;
            // printf("@@@ %d LOG %d before (prio: %d) is preempted by %d (prio %d)",
            //     _pid, taskid, tasks[taskid].effectivePriority, TASK3_ID, tasks[TASK3_ID].effectivePriority);
            preemptIfRequired(taskid, TASK3_ID, rc);
            // printf("@@@ %d LOG %d before (prio: %d) is preempted by %d (prio %d)",
            //     _pid, taskid, tasks[taskid].effectivePriority, TASK3_ID, tasks[TASK3_ID].effectivePriority);
            if
            //:: !rc ->
            :: !(tasks[taskid].state == OtherWait &&
               tasks[TASK3_ID].state == Ready) ->
                Release(task3Sema);
                Obtain(task1Sema);                 
            :: else ->
                skip;   
            fi
        }
    ::  else -> skip;
    fi
    
    //==============================================
    // 5. Task L: Releases the resource

    if
    ::  opts.doRelease -> 
            sem_id=1
            //Obtain(task1Sema);
           
            printf("@@@ %d CALL sema_release %d\n", _pid, sem_id);
                        /* (self,   sem_id, rc) */
            sema_release(taskid, sem_id, rc);
            if
            :: rc == RC_OK -> 
                printf("@@@ %d SCALAR released %d\n", _pid, sem_id);
            :: else -> skip;
            fi
            printf("@@@ %d SCALAR rc %d\n",_pid, rc);
            //Release(task1Sema);
    ::  else -> skip;
    fi

   
    if
    ::  opts.doPriorityInversion ->
        atomic {
            Release(task2Sema);
            Obtain(task1Sema);
            
        }
    
    ::  else -> skip;
    fi 
    //==============================================
    // End

    if
    ::  opts.doRelease2 -> 
            sem_id=2
            Obtain(task1Sema);
           
            printf("@@@ %d CALL sema_release2 %d\n", _pid, sem_id);
                        /* (self,   sem_id, rc) */
            sema_release(taskid, sem_id, rc);
            if
            :: rc == RC_OK -> 
                printf("@@@ %d SCALAR released %d\n", _pid, sem_id);
            :: else -> skip;
            fi
            printf("@@@ %d SCALAR rc %d\n",_pid, rc);
            Release(task1Sema);
            
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
        Obtain(task1Sema);
           
        printf("@@@ %d CALL sema_delete %d\n",_pid, sem_id);
                  /*  (self,   sem_id, rc) */
        sema_delete(taskid, sem_id, rc);
        printf("@@@ %d SCALAR rc %d\n",_pid, rc);
      
        Release(task1Sema);
    ::  else -> skip
    fi

    if 
    ::  opts.doDelete2 ->
        sem_id=2;
        Obtain(task1Sema);
           
        printf("@@@ %d CALL sema_delete2 %d\n",_pid, sem_id);
                  /*  (self,   sem_id, rc) */
        sema_delete(taskid, sem_id, rc);
        printf("@@@ %d SCALAR rc %d\n",_pid, rc);
      
        Release(task1Sema);
    ::  else -> skip
    fi
    
    
    if
    ::  opts.doPriorityInversion ->
        atomic {
            Release(task2Sema);
            Release(task3Sema);        
        }
    fi

    // Make sure everyone ran
    Release(task3Sema);
    //Obtain(task1Sema); ///-
    // Wait for other tasks to finish
    Obtain(task2Sema);
    Obtain(task3Sema);

    printf("@@@ %d LOG Task %d finished\n",_pid,taskid);
    tasks[taskid].state = Zombie;
    printf("@@@ %d STATE %d Zombie\n",_pid,taskid)    
}



proctype Worker0 (byte nid, taskid; TaskInputs opts) {
    Obtain(task2Sema);
    //==============================================
    // Initial setup

    tasks[taskid].nodeid = nid;
    tasks[taskid].pmlid = _pid;
    tasks[taskid].prio = opts.taskPrio;
    tasks[taskid].preemptable = opts.taskPreempt;
    tasks[taskid].initialPriority = opts.taskInitialPriority;
    tasks[taskid].effectivePriority = opts.taskInitialPriority;


    printf("@@@ %d TASK Worker0\n",_pid);
    if 
    :: tasks[taskid].initialPriority == 1 -> printf("@@@ %d CALL HighPriority\n", _pid);
    :: tasks[taskid].initialPriority == 2 -> printf("@@@ %d CALL NormalPriority\n", _pid);
    :: tasks[taskid].initialPriority == 3 -> printf("@@@ %d CALL LowPriority\n", _pid);
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
            // if
            // ::  opts.doPriorityInversion ->
            //         printf("@@@ %d LOG ---\n",_pid);    
            // ::  else ->
            //         Release(task3sema);
            // fi
            //Release(task3Sema);
            //Release(task1Sema); ///-swap1
            printf("@@@ %d CALL sema_obtain %d %d %d\n",
                    _pid, sem_id, opts.Wait, opts.timeoutLength);
                    /* (self,   sem_id, optionset, timeout,   rc) */
            sema_obtain(taskid, sem_id, opts.Wait, opts.timeoutLength, rc);
           
        }
        
        printf("@@@ %d SCALAR rc %d\n",_pid, rc);
    ::  else skip;//-> Release(task3Sema);
    fi

    if
    ::  opts.doPriorityInversion ->
        atomic {
            Release(task1Sema); ///-swap1   
            Obtain(task2Sema);
        }
    
    ::  else -> skip;
    fi

    
    //==============================================
    // 2. Task H: Blocked on the resource, waiting for Task L.
    
    if
    ::  opts.doAcquire2 -> 
        atomic{
            sem_id=2;
            printf("@@@ %d CALL sema_obtain2 %d %d %d\n",
                    _pid, sem_id, opts.Wait, opts.timeoutLength);
                    /* (self,   sem_id, optionset, timeout,   rc) */
            sema_obtain(taskid, sem_id, opts.Wait, opts.timeoutLength, rc);
           
        }
        
        printf("@@@ %d SCALAR rc %d\n",_pid, rc);
    ::  else -> skip;
    fi
    
    
    if
    ::  opts.doPriorityInversion ->
        atomic {
            // I should now have obtained the semaphore given 
            // either a FIFO or a priority queue
            printf("@@@ %d LOG doing HPT critical work\n", _pid);
        }
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
            sema_release(taskid, 2, rc);
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
            rc = false;
            preemptIfRequired(taskid, TASK3_ID, rc);
            if
            //:: !rc ->
            :: !(tasks[taskid].state == OtherWait &&
               tasks[TASK3_ID].state == Ready) ->
                Release(task1Sema);
                Obtain(task2Sema);
            :: else ->
                Release(task3Sema);
                Obtain(task2Sema);
            fi
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

    Release(task1Sema);
    atomic{
        Release(task2Sema);
        printf("@@@ %d LOG Task %d finished\n",_pid,taskid);
        tasks[taskid].state = Zombie;
        printf("@@@ %d STATE %d Zombie\n",_pid,taskid)
    }
}

proctype Worker1 (byte nid, taskid; TaskInputs opts) {
   
    //==============================================
    // Initial setup

    if
    ::  opts.doPriorityInversion ->
        atomic {
            Obtain(task3Sema); ///-
            Release(task1Sema);
            Obtain(task3Sema);
        }
    
    ::  else -> skip;
    fi

    //==============================================
    // 4. Task M: Becomes ready, has higher priority than Task L, and preempts it.
    // Task M: Runs and does its work, unrelated to the shared resource.
    // Task M: Finishes and yields the processor.
    
    tasks[taskid].nodeid = nid;
    tasks[taskid].pmlid = _pid;
    tasks[taskid].prio = opts.taskPrio;
    tasks[taskid].preemptable = opts.taskPreempt;
    tasks[taskid].initialPriority = opts.taskInitialPriority;
    tasks[taskid].effectivePriority = opts.taskInitialPriority;


    printf("@@@ %d TASK Worker1\n",_pid);
    if 
    :: tasks[taskid].initialPriority == 1 -> printf("@@@ %d CALL HighPriority\n", _pid);
    :: tasks[taskid].initialPriority == 2 -> printf("@@@ %d CALL NormalPriority\n", _pid);
    :: tasks[taskid].initialPriority == 3 -> printf("@@@ %d CALL LowPriority\n", _pid);
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
            printf("@@@ %d LOG MPT is hogging resources\n",_pid);
            printf("@@@ %d CALL sema_busy_work\n", _pid);
            Release(task1Sema);
            Obtain(task3Sema);
        }
        
    ::  else -> skip;
    fi

    if
    ::  opts.doAcquire -> 
        atomic{
            sem_id=1
            //Release(task1Sema);
            printf("@@@ %d CALL sema_obtain %d %d %d\n",
                    _pid, sem_id, opts.Wait, opts.timeoutLength);
                    /* (self,   sem_id, optionset, timeout,   rc) */
            sema_obtain(taskid, sem_id, opts.Wait, opts.timeoutLength, rc);
            
 
        }
        
        printf("@@@ %d SCALAR rc %d\n",_pid, rc);

    ::  else -> skip;//Release(task1Sema);
    fi

    if
    ::  opts.doAcquire2 -> 
        atomic{
            sem_id=2;
            
            printf("@@@ %d CALL sema_obtain2 %d %d %d\n",
                    _pid, sem_id, opts.Wait, opts.timeoutLength);
                    /* (self,   sem_id, optionset, timeout,   rc) */
            sema_obtain(taskid, sem_id, opts.Wait, opts.timeoutLength, rc);
            
        }
        
        printf("@@@ %d SCALAR rc %d\n",_pid, rc);

    ::  else -> skip;
    fi
    

    
    //==============================================
    // End

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
    
    Release(task2Sema);
    
    atomic {
        Release(task3Sema);
        printf("@@@ %d LOG Task %d finished\n",_pid,taskid);
        tasks[taskid].state = Zombie;
        printf("@@@ %d STATE %d Zombie\n",_pid,taskid)
    }
}




bool stopclock = false;
/*
 * We need a process that periodically wakes up blocked processes.
 * This is modelling background behaviour of the system,
 * such as ISRs and scheduling.
 * We visit all tasks in round-robin order (to prevent starvation)
 * and make them ready if waiting on "other" things.
 * Tasks waiting for events or timeouts are not touched
 * This terminates when all tasks are zombies.
 */
proctype System () {
    byte taskid ;
    bool liveSeen;

    printf("@@@ %d LOG System running...\n",_pid);

    loop:
    taskid = 1;
    liveSeen = false;

    printf("@@@ %d LOG Loop through tasks...\n",_pid);
    atomic {
        printf("@@@ %d LOG Scenario is ",_pid);
        printm(scenario); nl();
    }
    do   // while taskid < TASK_MAX ....
    ::  taskid == TASK_MAX -> break;
    ::  else ->
        atomic {
            printf("@@@ %d LOG Task %d state is ",_pid,taskid);
            printm(tasks[taskid].state); nl()
        }
        if
        ::  tasks[taskid].state == Zombie -> taskid++
        ::  else ->
            if
            ::  tasks[taskid].state == OtherWait
                -> tasks[taskid].state = Ready
                    printf("@@@ %d LOG %d Ready\n",_pid,taskid)
            ::  else -> skip
            fi
            liveSeen = true;
            taskid++
        fi
    od

    printf("@@@ %d LOG ...all visited, live:%d\n",_pid,liveSeen);

    if
    ::  liveSeen -> goto loop
    ::  else
    fi
    printf("@@@ %d LOG All are Zombies, game over.\n",_pid);
    stopclock = true;
}


/*
 * We need a process that handles a clock tick,
 * by decrementing the tick count for tasks waiting on a timeout.
 * Such a task whose ticks become zero is then made Ready,
 * and its timer status is flagged as a timeout
 * This terminates when all tasks are zombies
 * (as signalled by System via `stopclock`).
 */
proctype Clock () {
    int tid, tix;
    printf("@@@ %d LOG Clock Started\n",_pid)
    do
    ::  stopclock  -> goto stopped
    ::  !stopclock ->
        printf(" (tick) \n");
        tid = 1;
        do
        ::  tid == TASK_MAX -> break
        ::  else ->
            atomic{
                printf("Clock: tid=%d, state=",tid); printm(tasks[tid].state); nl()
            };
            if
            ::  tasks[tid].state == TimeWait ->
                tix = tasks[tid].ticks - 1;
                // printf("Clock: ticks=%d, tix=%d\n",tasks[tid].ticks,tix);
                if
                ::  tix == 0
                    tasks[tid].tout = true
                    tasks[tid].state = Ready
                    printf("@@@ %d LOG %d Ready\n",_pid,tid)
                ::  else
                    tasks[tid].ticks = tix
                fi
            ::  else // state != TimeWait
            fi
            tid = tid + 1
        od
    od
    stopped:
    printf("@@@ %d LOG Clock Stopped\n",_pid);
}





init {

    pid nr;

    printf("Semaphore Manager Model running.\n");
    printf("Setup...\n");

    printf("@@@ %d LOG TestName: Semaphore_Manager_TestGen\n",_pid)
    outputDefines();
    outputDeclarations();




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
