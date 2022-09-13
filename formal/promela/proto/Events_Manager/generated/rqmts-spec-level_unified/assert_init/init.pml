inline outputDefines () {
	printf("@@@ %d DEF NO_OF_EVENTS %d\n" , _pid , 4)
	printf("@@@ %d DEF EVTS_NONE %d\n" , _pid , 0)
	printf("@@@ %d DEF EVTS_PENDING %d\n" , _pid , 0)
	printf("@@@ %d DEF EVT_0 %d\n" , _pid , 1)
	printf("@@@ %d DEF EVT_1 %d\n" , _pid , 2)
	printf("@@@ %d DEF EVT_2 %d\n" , _pid , 4)
	printf("@@@ %d DEF EVT_3 %d\n" , _pid , 8)
	printf("@@@ %d DEF NO_TIMEOUT %d\n" , _pid , 0)
	printf("@@@ %d DEF TASK_MAX %d\n" , _pid , 2)
	printf("@@@ %d DEF BAD_ID %d\n" , _pid , 2)
	printf("@@@ %d DEF SEMA_MAX %d\n" , _pid , 2)
	printf("@@@ %d DEF RC_OK RTEMS_SUCCESSFUL\n" , _pid)
	printf("@@@ %d DEF RC_InvId RTEMS_INVALID_ID\n" , _pid)
	printf("@@@ %d DEF RC_InvAddr RTEMS_INVALID_ADDRESS\n" , _pid)
	printf("@@@ %d DEF RC_Unsat RTEMS_UNSATISFIED\n" , _pid)
	printf("@@@ %d DEF RC_Timeout RTEMS_TIMEOUT\n" , _pid)
}


mtype = { Zombie , Ready , EventWait , TimeWait , OtherWait , Wait , NoWait , All , Any }
typedef Task { byte nodeid; byte pmlid; mtype state; bool preemptable; byte prio; int ticks; bool tout; unsigned pending : 4; unsigned wanted : 4; bool all }
Task tasks [2]
byte sendrc
byte recrc
byte recout
bool semaphore [2]
inline outputDeclarations () {
	printf("@@@ %d DCLARRAY EvtSet pending TASK_MAX\n" , _pid)
	printf("@@@ %d DECL byte sendrc 0\n" , _pid)
	printf("@@@ %d DECL byte recrc 0\n" , _pid)
	printf("@@@ %d DECL byte recout 0\n" , _pid)
	printf("@@@ %d DCLARRAY Semaphore semaphore SEMA_MAX\n" , _pid)
}


inline Obtain (sem_id) {
	atomic{
		printf("@@@ %d WAIT %d\n" , _pid , sem_id)
		semaphore[sem_id]
		semaphore[sem_id] = false
		printf("@@@ %d LOG WAIT %d Over\n" , _pid , sem_id)
	}
}


inline Release (sem_id) {
	atomic{
		printf("@@@ %d SIGNAL %d\n" , _pid , sem_id)
		semaphore[sem_id] = true
	}
}


inline Released (sem_id) {
	semaphore[sem_id] = true
}


inline printevents (evts) {
	printf("{%d,%d,%d,%d}" , ((evts / 8) % 2) , ((evts / 4) % 2) , ((evts / 2) % 2) , (evts % 2))
}


inline events (evts, e3, e2, e1, e0) {
	evts = ((((8 * e3) + (4 * e2)) + (2 * e1)) + e0)
}


inline setminus (diff, minuend, subtrahend) {
	diff = (minuend & (15 - subtrahend))
}


inline nl () {
	printf("\n")
}


inline waitUntilReady (id) {
	atomic{
		printf("@@@ %d LOG Task %d waiting, state = " , _pid , id)
		printm (tasks[id].state)
		nl ()
	}
	
	(tasks[id].state == Ready)
	printf("@@@ %d STATE %d Ready\n" , _pid , id)
}


inline satisfied (task, out, sat) {
	out = (task.pending & task.wanted)
	if
	:: (task.all && (out == task.wanted)) ->
		sat = true
	:: ((! task.all) && (out != 0)) ->
		sat = true
	:: else ->
		sat = false
	fi;
	
	printf("@@@ %d LOG satisfied(<pnd:%d wnt:%d all:%d>,out:%d,SAT:%d)\n" , _pid , task.pending , task.wanted , task.all , out , sat)
}


inline preemptIfRequired (sendid, rcvid) {
	if
	:: ((tasks[sendid].preemptable && (tasks[rcvid].state == EventWait)) && (tasks[rcvid].prio < tasks[sendid].prio)) ->
		tasks[sendid].state = OtherWait
		printf("@@@ %d STATE %d OtherWait\n" , _pid , sendid)
	:: else
	fi;
}


inline event_send (self, tid, evts, rc) {
	atomic{
		if
		:: (tid >= 2) ->
			rc = 4
		:: (tid < 2) ->
			tasks[tid].pending = (tasks[tid].pending | evts)
			unsigned got : 4
			bool sat
			satisfied (tasks[tid], got, sat)
			if
			:: sat ->
				tasks[tid].state = Ready
				printf("@@@ %d STATE %d Ready\n" , _pid , tid)
				preemptIfRequired (self, tid)
				if
				:: tasks[self].state = OtherWait ->
					Released (sendSema)
				:: else
				fi;
				waitUntilReady (self)
			:: else ->
				skip
			fi;
			rc = 0
		fi;
	}
}


inline event_receive (self, evts, wait, wantall, interval, out, rc) {
	atomic{
		printf("@@@ %d LOG pending[%d] = " , _pid , self)
		printevents (tasks[self].pending)
		nl ()
		tasks[self].wanted = evts
		tasks[self].all = wantall
		if
		:: (evts == 0) ->
			printf("@@@ %d LOG Receive Pending.\n" , _pid)
			out = tasks[self].pending
			rc = 0
		:: else ->
			bool sat
			retry: satisfied (tasks[self], out, sat)
			if
			:: sat ->
				printf("@@@ %d LOG Receive Satisfied!\n" , _pid)
				setminus (tasks[self].pending, tasks[self].pending, out)
				printf("@@@ %d LOG pending'[%d] = " , _pid , self)
				printevents (tasks[self].pending)
				nl ()
				rc = 0
			:: ((! sat) && (! wait)) ->
				printf("@@@ %d LOG Receive Not Satisfied (no wait)\n" , _pid)
				rc = 13
			:: (((! sat) && wait) && (interval > 0)) ->
				printf("@@@ %d LOG Receive Not Satisfied (timeout %d)\n" , _pid , interval)
				tasks[self].ticks = interval
				tasks[self].tout = false
				tasks[self].state = TimeWait
				printf("@@@ %d STATE %d TimeWait %d\n" , _pid , self , interval)
				Released (rcvSema)
				waitUntilReady (self)
				if
				:: tasks[self].tout ->
					rc = 6
				:: else ->
					goto retry
				fi;
			:: else ->
				printf("@@@ %d LOG Receive Not Satisfied (wait).\n" , _pid)
				tasks[self].state = EventWait
				printf("@@@ %d STATE %d EventWait\n" , _pid , self)
				Released (rcvSema)
				waitUntilReady (self)
				goto retry
			fi;
		fi;
		printf("@@@ %d LOG pending'[%d] = " , _pid , self)
		printevents (tasks[self].pending)
		nl ()
	}
}


typedef SendInputs { byte target_id; unsigned send_evts : 4 }
SendInputs send_in [3]
typedef ReceiveInputs { unsigned receive_evts : 4; bool will_wait; bool everything; byte wait_length }
ReceiveInputs receive_in [3]
bool doSend
byte sendPrio
bool sendPreempt
byte sendTarget
unsigned sendEvents : 4
bool doReceive
unsigned rcvEvents : 4
bool rcvWait
bool rcvAll
int rcvInterval
byte rcvPrio
int sendSema
int rcvSema
int startSema
mtype = { Send , Receive , SndRcv , RcvSnd , SndRcvSnd }
mtype scenario
inline chooseScenario () {
	doSend = true
	doReceive = true
	semaphore[0] = false
	semaphore[1] = false
	sendPrio = 0
	sendPreempt = false
	sendTarget = 1
	rcvPrio = 0
	rcvWait = true
	rcvAll = true
	rcvInterval = 0
	tasks[0].state = Ready
	tasks[1].state = Ready
	sendEvents = 10
	rcvEvents = 10
	sendSema = 0
	rcvSema = 1
	startSema = sendSema
	if
	:: scenario = Send
	:: scenario = Receive
	:: scenario = SndRcv
	fi;
	
	atomic{
		printf("@@@ %d LOG scenario " , _pid)
		printm (scenario)
		nl ()
	}
	
	if
	:: (scenario == Send) ->
		doReceive = false
		sendTarget = 2
	:: (scenario == Receive) ->
		doSend = false
		rcvWait = false
	:: (scenario == SndRcv) ->
		if
		:: sendEvents = 14
		:: sendEvents = 11
		fi;
	:: else
	fi;
}


active [0]  proctype Sender(byte nid; byte taskid){
	tasks[taskid].nodeid = nid
	tasks[taskid].pmlid = _pid
	tasks[taskid].prio = sendPrio
	tasks[taskid].preemptable = sendPreempt
	tasks[taskid].state = Ready
	printf("@@@ %d TASK Worker\n" , _pid)
	Obtain (sendSema)
	if
	:: doSend ->
		printf("@@@ %d CALL event_send %d %d %d sendrc\n" , _pid , taskid , sendTarget , sendEvents)
		event_send (taskid, sendTarget, sendEvents, sendrc)
		printf("@@@ %d SCALAR sendrc %d\n" , _pid , sendrc)
	:: else
	fi;
	
	Release (rcvSema)
	printf("@@@ %d LOG Sender %d finished\n" , _pid , taskid)
	tasks[taskid].state = Zombie
	printf("@@@ %d STATE %d Zombie\n" , _pid , taskid)
}


active [0]  proctype Receiver(byte nid; byte taskid){
	tasks[taskid].nodeid = nid
	tasks[taskid].pmlid = _pid
	tasks[taskid].prio = rcvPrio
	tasks[taskid].preemptable = false
	tasks[taskid].state = Ready
	printf("@@@ %d TASK Runner\n" , _pid , taskid)
	Release (startSema)
	Obtain (rcvSema)
	if
	:: doReceive ->
		printf("@@@ %d SCALAR pending %d %d\n" , _pid , taskid , tasks[taskid].pending)
		printf("@@@ %d CALL event_receive %d %d %d %d recout recrc\n" , _pid , rcvEvents , rcvWait , rcvAll , 0)
		event_receive (taskid, rcvEvents, rcvWait, rcvAll, 0, recout, recrc)
		printf("@@@ %d SCALAR recrc %d\n" , _pid , recrc)
		printf("@@@ %d SCALAR recout %d\n" , _pid , recout)
		printf("@@@ %d SCALAR pending %d %d\n" , _pid , taskid , tasks[taskid].pending)
	:: else
	fi;
	
	Release (sendSema)
	printf("@@@ %d LOG Receiver %d finished\n" , _pid , taskid)
	tasks[taskid].state = Zombie
	printf("@@@ %d STATE %d Zombie\n" , _pid , taskid)
}


bool stopclock = false
active [0]  proctype System(){
	byte taskid
	bool liveSeen
	printf("@@@ %d LOG System running...\n" , _pid)
	loop: taskid = 0
	liveSeen = false
	printf("@@@ %d LOG Loop through tasks...\n" , _pid)
	do
	:: (taskid == 2) ->
		break
	:: else ->
		atomic{
			printf("@@@ %d LOG Task %d state is " , _pid , taskid)
			printm (tasks[taskid].state)
			nl ()
		}
		if
		:: (tasks[taskid].state == Zombie) ->
			taskid = (taskid + 1)
		:: else ->
			if
			:: (tasks[taskid].state == OtherWait) ->
				tasks[taskid].state = Ready
				printf("@@@ %d STATE %d Ready\n" , _pid , taskid)
			:: else ->
				skip
			fi;
			liveSeen = true
			taskid = (taskid + 1)
		fi;
	od;
	
	printf("@@@ %d LOG ...all visited, live:%d\n" , _pid , liveSeen)
	if
	:: liveSeen ->
		goto loop
	:: else
	fi;
	
	printf("@@@ %d LOG All are Zombies, game over.\n" , _pid)
	stopclock = true
}


active [0]  proctype Clock(){
	int tid
	int tix
	printf("@@@ %d LOG Clock Started\n" , _pid)
	do
	:: stopclock ->
		goto stopped
	:: (! stopclock) ->
		printf(" (tick) \n")
		tid = 0
		do
		:: tid = 2 ->
			break
		:: else ->
			if
			:: (tasks[tid].state == TimeWait) ->
				tix = (tasks[tid].ticks - 1)
				if
				:: (tix == 0) ->
					tasks[tid].tout = true
					tasks[tid].state = Ready
					printf("@@@ %d STATE %d Ready\n" , _pid , tid)
				:: else ->
					tasks[tid].ticks = tix
				fi;
			:: else
			fi;
			tid = (tid + 1)
		od;
	od;
	
	stopped: printf("@@@ %d LOG Clock Stopped\n" , _pid)
}


init {
	pid nr
	printf("Event Manager Model running.\n")
	printf("Setup...\n")
	printf("@@@ %d NAME Event_Manager_TestGen\n" , _pid)
	outputDefines ()
	outputDeclarations ()
	printf("@@@ %d INIT\n" , _pid)
	chooseScenario ()
	printf("Run...\n")
	run System ()
	run Clock ()
	run Sender (0 , 0)
	run Receiver (0 , 1)
	(_nr_pr == 1)
	assert((! true))
	printf("Event Manager Model finished !\n")
}

