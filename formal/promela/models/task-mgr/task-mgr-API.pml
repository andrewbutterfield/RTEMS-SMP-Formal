// Model of rtems_task_create(...)
inline task_create(task, tid, name, prio, preempt, tidRC, rc) {
    atomic {
        if
		::	name == 0 ->
				rc = RC_InvName;
        ::  prio == 0 ->
                rc = RC_InvPrio;
        ::  prio >= BAD_PRIO ->
                rc = RC_InvPrio;
		::  tidRC == false ->
                rc = RC_TooMany;
		::	tid == 0 ->
				rc = RC_InvAddr;
        ::  else ->
				task.pmlid = _pid;
				task.prio = prio;
				task.preemptable = preempt;
				task.state = Dormant;
        fi
    }
}
//*/

// Model of rtems_task_start(...)
inline task_start(task, entry, rc) {
    atomic {
        if
        ::  task.state == Zombie ->
                printf("@@@ %d LOG Start NULL out.\n",_pid);
                rc = RC_InvId;
		:: 	else ->
				if
				::  task.state != Dormant ->
						rc = RC_IncState;
				:: 	else ->
						if 
						::  entry == 0 -> rc = RC_InvAddr;
						::  else ->
							task.state = Ready;
							task.start = entry;
							// Start Task Model
							TestSyncRelease(entry);
							rc = RC_OK;
						fi
				fi
        fi
    }
}

// Model of rtems_task_suspend(...)
inline task_suspend(task, rc) {
    atomic {
        if
        ::  task.state == Zombie ->
                rc = RC_InvId;
        ::  task.state == Blocked ->
                rc = RC_AlrSuspd;
        ::  else ->
                task.state = Blocked;
                rc = RC_OK;
        fi
    }
}

// Model of rtems_task_is_suspended(...)
inline task_isSuspend(task, rc) {
    atomic {
        if
        ::  task.state == Zombie ->
                rc = RC_InvId;
        ::  task.state == Blocked ->
                rc = RC_AlrSuspd;
        ::  else ->
                rc = RC_OK;
        fi
    }
}

// Model of rtems_task_resume(...)
inline task_resume(task, rc) {
    atomic {
        if
        ::  task.state == Zombie ->
            rc = RC_InvId;
        ::  else ->
                if
                :: task.state != Blocked ->
                    rc = RC_IncState;
                :: else ->
                    task.state = Ready ->
                    rc = RC_OK;
                fi
        fi
    }
}

// Model of rtems_task_delete(...) 
inline task_delete(task, tid, rc) {
    atomic {
        if
        ::  task.state == Zombie ->
                rc = RC_InvId;
        ::  else ->
                if
                ::  task.isr == true ->
                        rc = RC_FrmIsr;
                ::  else ->
                        bool isremoved;
                        removeTask(tid, isremoved);
                        if
                        ::  isremoved == false ->
                                rc = RC_InvId;
                        ::  else ->
                                task.state = Zombie;
                                task.start = 0;
                                rc = RC_OK;
                        fi
                fi
        fi
    }
}
//*/

// Model of rtems_task_set_priority(...) 
inline task_setPrio(tid, new, old, rc) {
    atomic {
        if
        ::  tasks[tid].state == Zombie ->
                rc = RC_InvId;
        ::  old == INVALID_ID ->
                rc = RC_InvAddr;
        ::  else ->
                if
                ::  new > MAX_PRIO ->
                        rc = RC_InvPrio;
                ::  new == CURRENT_PRIO ->
                        old = tasks[tid].prio;
                        rc = RC_OK;
                ::  else ->
                        old = tasks[tid].prio;
                        if
                        ::  new > old -> 
                                tasks[tid].prio = new;
                                set_priority(tasks[tid].pmlid, new); //TODO
                        ::  else ->
                                /*
                                If the task is currently holding any 
                                binary semaphores which use a locking protocol, 
                                then the task’s priority cannot be lowered immediately
                                */
                                interrupt_channel ! tid, new;
                        fi
                        rc = RC_OK;
                fi
        fi
    }
}

/*
inline task_setPrio(task, sched, prio, rc) {
    if
    ::  prio == 0 ->
            rc = RC_InvAddr
    ::  else ->
            if
            ::  task.state == Zombie ->
                    rc = RC_InvId
            ::  else ->
                    if
                    ::  sched.state == Zombie ->
                            rc = RC_InvId
                    ::  else ->

}

inline rtems_task_wake_after(ticks) {

    // ticks == 0: RTEMS_YIELD_PROCESSOR
    int count = 0;
    do
    ::  
}
*/