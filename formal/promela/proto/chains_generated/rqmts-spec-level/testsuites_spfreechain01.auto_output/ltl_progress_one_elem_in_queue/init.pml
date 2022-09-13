mtype = { exit_success , error_queue_full , error_queue_empty }
mtype = { op_add , op_del }
mtype = { not_waiting , wait_for_add , wait_for_del }
int q_size_max
int q_size_current
int q_tail
int q_head
int q_content [4]
mtype sched_status = not_waiting
chan history_op = [100] of { mtype }
active [0]  proctype head_add(chan ret; int x){
	atomic{
		history_op ! op_add
		if
		:: (q_size_current == q_size_max) ->
			ret ! error_queue_full
		:: else ->
			q_content[q_head] = x
			q_head = ((q_head + 1) % q_size_max)
			q_size_current = (q_size_current + 1)
			ret ! exit_success
		fi;
		printf("//@ 0.8444218515250481 \\<open>1\\<close> \\<open>29\\<close> \\<open>%d\\<close> \\<open>%d\\<close>\n" , 0 , x)
	}
}


active [0]  proctype head_del(chan ret; int x){
	atomic{
		history_op ! op_del
		if
		:: (q_size_current == 0) ->
			ret ! error_queue_empty
		:: else ->
			q_head = (((q_head + q_size_max) - 1) % q_size_max)
			q_content[q_head] = 0
			q_size_current = (q_size_current - 1)
			ret ! exit_success
		fi;
		printf("//@ 0.8444218515250481 \\<open>1\\<close> \\<open>44\\<close> \\<open>%d\\<close> \\<open>%d\\<close>\n" , 0 , x)
	}
}


active [0]  proctype tail_add(chan ret; int x){
	atomic{
		history_op ! op_add
		if
		:: (q_size_current == q_size_max) ->
			ret ! error_queue_full
		:: else ->
			q_content[q_tail] = x
			q_tail = (((q_tail + q_size_max) - 1) % q_size_max)
			q_size_current = (q_size_current + 1)
			ret ! exit_success
		fi;
		printf("//@ 0.8444218515250481 \\<open>1\\<close> \\<open>59\\<close> \\<open>%d\\<close> \\<open>%d\\<close>\n" , 0 , x)
	}
}


active [0]  proctype tail_del(chan ret; int x){
	atomic{
		history_op ! op_del
		if
		:: (q_size_current == 0) ->
			ret ! error_queue_empty
		:: else ->
			q_tail = ((q_tail + 1) % q_size_max)
			q_content[q_tail] = 0
			q_size_current = (q_size_current - 1)
			ret ! exit_success
		fi;
		printf("//@ 0.8444218515250481 \\<open>1\\<close> \\<open>74\\<close> \\<open>%d\\<close> \\<open>%d\\<close>\n" , 0 , x)
	}
}


active [0]  proctype init_head_add(){
	chan ret = [0] of { mtype }
	int n = 5
	do
	:: (n == 0) ->
		break
	:: ((n != 0) && (sched_status != wait_for_del)) ->
		atomic{
			run head_add (ret , n)
			if
			:: ret ? error_queue_full ->
				sched_status = wait_for_del
			:: ret ? exit_success ->
				n = (n - 1)
				if
				:: (sched_status == wait_for_add) ->
					sched_status = not_waiting
				:: else ->
					skip
				fi;
			fi;
		}
	od;
}


active [0]  proctype init_head_del(){
	chan ret = [0] of { mtype }
	int n = 5
	do
	:: (n == 0) ->
		break
	:: ((n != 0) && (sched_status != wait_for_add)) ->
		atomic{
			run head_del (ret , (10 + n))
			if
			:: ret ? error_queue_empty ->
				sched_status = wait_for_add
			:: ret ? exit_success ->
				n = (n - 1)
				if
				:: (sched_status == wait_for_del) ->
					sched_status = not_waiting
				:: else ->
					skip
				fi;
			fi;
		}
	od;
}


active [0]  proctype init_simple(){
	chan ret = [100] of { mtype }
	run head_add (ret , 1)
	run head_add (ret , 2)
	run head_del (ret , 3)
	run head_del (ret , 4)
	run tail_add (ret , 5)
	run tail_add (ret , 6)
	run tail_del (ret , 80)
}


init {
	q_size_max = 4
	q_size_current = 0
	q_tail = (q_size_max - 1)
	q_head = 0
	run init_simple ()
}

ltl progress_one_elem_in_queue {(! (true U (q_size_current != 0)))}