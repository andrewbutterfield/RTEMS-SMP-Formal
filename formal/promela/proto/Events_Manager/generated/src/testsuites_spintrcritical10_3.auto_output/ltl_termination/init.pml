chan global_history_surrender = [100] of { int , int }
int global_history_surrender_id = 0
chan global_history_seize = [100] of { int , int , int , int }
int global_history_seize_id = 0
int thread_wait_state_intend_to_block = 1
int thread_wait_state_blocked = 2
int thread_wait_state_ready_again = 4
int states_ready = 0
int states_waiting_for_event = 4
int states_suspended = 32768
int rtems_event_0 = 1
int rtems_event_1 = 2
int rtems_event_5 = 32
int rtems_event_7 = 128
int rtems_event_23 = 8388608
int rtems_default_options = 0
int rtems_wait = 0
int rtems_no_wait = 1
int rtems_event_all = 0
int rtems_event_any = 2
int rtems_successful = 0
int rtems_invalid_id = 4
int rtems_timeout = 6
int rtems_invalid_address = 9
int rtems_unsatisfied = 13
int rtems_not_implemented = 24
typedef thread { int state = 0; int wait_flags = 4; int lock_surrender_current = 0; int lock_surrender_target = 0; int lock_seize = 0; int pending = 0; int event_in = 0; int option_set = 0; int event_out_surrender = 0 }
thread thread_pool [3]
inline set_ready_unblock (target) {
	if
	:: atomic{
			(thread_pool[target].wait_flags == thread_wait_state_intend_to_block)
			thread_pool[target].wait_flags = thread_wait_state_ready_again
		}
	:: else ->
		thread_pool[target].wait_flags = thread_wait_state_ready_again
		thread_pool[target].state = (thread_pool[target].state & (~ states_waiting_for_event))
	fi;
}


inline event_surrender_return (history_return, history_id, current, target, status) {
	atomic{
		thread_pool[current].lock_surrender_current = (thread_pool[current].lock_surrender_current - 1)
		thread_pool[target].lock_surrender_target = (thread_pool[target].lock_surrender_target - 1)
		history_return ! history_id , status
	}
}


active [0]  proctype event_surrender_exec(chan history_return; int history_id; int current; int target; int event_in){
	(thread_pool[current].state == states_ready)
	if
	:: ((target < 0) || (target >= 3)) ->
		(thread_pool[current].state == states_ready)
		event_surrender_return (history_return, history_id, current, target, rtems_invalid_id)
	:: else ->
		(thread_pool[current].state == states_ready)
		thread_pool[target].pending = (thread_pool[target].pending | event_in)
		(thread_pool[current].state == states_ready)
		if
		:: (thread_pool[target].wait_flags != thread_wait_state_ready_again) ->
			(thread_pool[current].state == states_ready)
			int seized
			seized = (thread_pool[target].pending & thread_pool[target].event_in)
			if
			:: ((! (seized == 0)) && ((seized == thread_pool[target].event_in) || (thread_pool[target].option_set & rtems_event_any))) ->
				thread_pool[target].pending = (thread_pool[target].pending & (~ seized))
				(thread_pool[current].state == states_ready)
				thread_pool[target].event_out_surrender = seized
				(thread_pool[current].state == states_ready)
				set_ready_unblock (target)
			:: else
			fi;
		:: else
		fi;
		(thread_pool[current].state == states_ready)
		event_surrender_return (history_return, history_id, current, target, rtems_successful)
	fi;
}


inline event_surrender_send (history_return, history_id, current, target, event_in) {
	if
	:: atomic{
			(thread_pool[current].lock_seize == 0)
			thread_pool[current].lock_surrender_current = (thread_pool[current].lock_surrender_current + 1)
			thread_pool[target].lock_surrender_target = (thread_pool[target].lock_surrender_target + 1)
		} ->
		run event_surrender_exec (history_return , history_id , current , target , event_in)
	:: else ->
		history_return ! history_id , rtems_not_implemented
	fi;
}


inline event_history_surrender_send (current, target, event_in) {
	event_surrender_send (global_history_surrender, global_history_surrender_id, current, target, event_in)
	global_history_surrender_id = (global_history_surrender_id + 1)
}


inline event_seize_return (history_return, history_id, current, status, opt_is_some, opt_event_out) {
	atomic{
		thread_pool[current].lock_seize = (thread_pool[current].lock_seize - 1)
		history_return ! history_id , status , opt_is_some , opt_event_out
	}
}


active [0]  proctype event_seize_exec(chan history_return; int history_id; int current; int event_in; int option_set; int ticks; int opt_event_out){
	(thread_pool[current].state == states_ready)
	if
	:: (event_in == 0) ->
		(thread_pool[current].state == states_ready)
		event_seize_return (history_return, history_id, current, rtems_successful, true, thread_pool[current].pending)
	:: else ->
		(thread_pool[current].state == states_ready)
		int seized
		seized = (thread_pool[current].pending & event_in)
		if
		:: ((! (seized == 0)) && ((seized == event_in) || (option_set & rtems_event_any))) ->
			thread_pool[current].pending = (thread_pool[current].pending & (~ seized))
			(thread_pool[current].state == states_ready)
			event_seize_return (history_return, history_id, current, rtems_successful, true, seized)
		:: else ->
			(thread_pool[current].state == states_ready)
			if
			:: (option_set & rtems_no_wait) ->
				(thread_pool[current].state == states_ready)
				event_seize_return (history_return, history_id, current, rtems_unsatisfied, true, seized)
			:: else ->
				(thread_pool[current].state == states_ready)
				thread_pool[current].event_in = event_in
				thread_pool[current].option_set = option_set
				thread_pool[current].wait_flags = thread_wait_state_intend_to_block
				(thread_pool[current].state == states_ready)
				if
				:: atomic{
						(thread_pool[current].wait_flags == thread_wait_state_intend_to_block)
						thread_pool[current].wait_flags = thread_wait_state_blocked
						thread_pool[current].state = (thread_pool[current].state | states_waiting_for_event)
					}
				:: else
				fi;
				(thread_pool[current].state != (thread_pool[current].state | states_suspended))
				if
				:: (ticks <= 0) ->
					(thread_pool[current].state != (thread_pool[current].state | states_suspended))
					(thread_pool[current].state == (thread_pool[current].state & (~ states_waiting_for_event)))
					event_seize_return (history_return, history_id, current, rtems_successful, true, thread_pool[current].event_out_surrender)
				:: else ->
					(thread_pool[current].state != (thread_pool[current].state | states_suspended))
					do
					:: (thread_pool[current].state == (thread_pool[current].state & (~ states_waiting_for_event))) ->
						event_seize_return (history_return, history_id, current, rtems_successful, true, thread_pool[current].event_out_surrender)
						break
					:: else ->
						(thread_pool[current].state != (thread_pool[current].state | states_suspended))
						if
						:: (ticks <= 0) ->
							atomic{
								(thread_pool[current].state != (thread_pool[current].state | states_suspended))
								set_ready_unblock (current)
							}
							event_seize_return (history_return, history_id, current, rtems_timeout, false, opt_event_out)
							break
						:: else ->
							(thread_pool[current].state != (thread_pool[current].state | states_suspended))
							ticks = (ticks - 1)
						fi;
					od;
				fi;
			fi;
		fi;
	fi;
}


inline event_seize_receive (history_return, history_id, current, event_in, option_set, ticks, opt_event_out) {
	if
	:: atomic{
			((thread_pool[current].lock_surrender_current == 0) && (thread_pool[current].lock_seize == 0))
			thread_pool[current].lock_seize = (thread_pool[current].lock_seize + 1)
		} ->
		if
		:: opt_event_out ->
			run event_seize_exec (history_return , history_id , current , event_in , option_set , ticks , opt_event_out)
		:: else ->
			event_seize_return (history_return, history_id, current, rtems_invalid_address, false, opt_event_out)
		fi;
	:: else ->
		history_return ! history_id , rtems_not_implemented , false , opt_event_out
	fi;
}


inline event_history_seize_receive (current, event_in, option_set, ticks, opt_event_out) {
	event_seize_receive (global_history_seize, global_history_seize_id, current, event_in, option_set, ticks, opt_event_out)
	global_history_seize_id = (global_history_seize_id + 1)
}


chan history_send = [0] of { int , int }
chan history_receive = [0] of { int , int , int , int }
int hit = 0
int send_break = 0
int surrender_send_status
int seize_receive_status
int seize_receive_event_out
inline event_atomic_surrender_send (current, target, event_in) {
	event_surrender_send (history_send, 0, current, target, event_in)
	history_send ? _ , surrender_send_status
}


inline event_atomic_seize_receive (current, event_in, option_set, ticks, opt_event_out) {
	event_seize_receive (history_receive, 0, current, event_in, option_set, ticks, opt_event_out)
	history_receive ? _ , seize_receive_status , _ , seize_receive_event_out
}


int current = 1
int target = 0
int retries = 2
inline suspend_on (target) {
	thread_pool[target].state = (thread_pool[target].state | states_suspended)
}


inline suspend_off (target) {
	thread_pool[target].state = (thread_pool[target].state & (~ states_suspended))
}


inline wait_for_receive_blocked_then_suspend_on (target) {
	atomic{
		((thread_pool[target].wait_flags == thread_wait_state_intend_to_block) || (thread_pool[target].wait_flags == thread_wait_state_blocked))
		hit = (thread_pool[target].wait_flags == thread_wait_state_blocked)
		suspend_on (target)
	}
}


inline wait_for_receive_timeout_then_suspend_on (target) {
	atomic{
		(seize_receive_status == rtems_timeout)
		suspend_on (target)
	}
}


inline wait_for_send_hit_or_no_retry () {
	((hit >= 1) || (retries <= 0))
	send_break = 1
	break
}


active [0]  proctype send(){
	do
	:: wait_for_receive_blocked_then_suspend_on (target) ->
		thread_pool[target].event_out_surrender = 3735928559
		suspend_off (target)
		if
		:: wait_for_receive_timeout_then_suspend_on (target) ->
			event_atomic_surrender_send (current, target, (rtems_event_0 | rtems_event_1))
			assert((surrender_send_status == rtems_successful))
			assert((thread_pool[target].event_out_surrender == 3735928559))
			suspend_off (target)
		:: send_break ->
			break
		fi;
	:: send_break ->
		break
	od;
	
	printf("//@ 0.8444218515250481 \\<open>1\\<close> \\<open>326\\<close>\n")
}


active [0]  proctype receive(){
	do
	:: wait_for_send_hit_or_no_retry ()
	:: else ->
		event_atomic_seize_receive (target, (rtems_event_0 | rtems_event_1), (rtems_event_all | rtems_wait), 1, 3735928559)
		assert((((seize_receive_status == rtems_timeout) && (seize_receive_event_out == 3735928559)) || ((seize_receive_status == rtems_successful) && (seize_receive_event_out == (rtems_event_0 | rtems_event_1)))))
		event_atomic_seize_receive (target, (rtems_event_0 | rtems_event_1), (rtems_event_all | rtems_no_wait), 0, 3735928559)
		assert((((seize_receive_status == rtems_unsatisfied) && (seize_receive_event_out == 0)) || ((seize_receive_status == rtems_successful) && (seize_receive_event_out == (rtems_event_0 | rtems_event_1)))))
		retries = (retries - 1)
	od;
	
	printf("//@ 0.8444218515250481 \\<open>1\\<close> \\<open>351\\<close>\n")
}


int terminated0 = 0
int terminated = terminated0
init {
	int nr
	nr = _nr_pr
	run send ()
	run receive ()
	(nr == _nr_pr)
	terminated = (! terminated)
}

ltl termination {(! (<> ([] (terminated != terminated0))))}