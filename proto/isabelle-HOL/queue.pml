// K. Jiang and B. Jonsson, "Using SPIN to model check concurrent algorithms, using a translation from C to Promela", in Proc. 2nd Swedish Workshop on Multi-Core Computing, 2009, pp. 67-69.
// http://uu.diva-portal.org/smash/record.jsf?pid=diva2:291762

int int_mem[9];
int int_valid[9];
typedef node_t {
  int next;
  int value;
}

node_t node_t_mem[9];
int node_t_valid[9];

typedef queue_t {
  int Head;
  int Tail;
  int H_lock;
  int T_lock;
}
queue_t queue_t_mem[9];
int queue_t_valid[9];

proctype initialize(chan in_initialize; int Q){
  int node_t_ct; int dummy; int tmp;
  atomic {
    node_t_ct = 1;
    do
    :: (node_t_ct >= 9) -> break
    :: else ->
    if
    :: (node_t_valid[node_t_ct] == 0) ->
    node_t_valid[node_t_ct] = 1;
    break
    :: else -> node_t_ct ++
    fi
    od;
    assert (node_t_ct < 9);
    tmp = node_t_ct;
    node_t_ct = 1
  };
  dummy = tmp;
  node_t_mem[dummy].next = 0;
  node_t_mem[dummy].value = 0;
  queue_t_mem[Q].Tail = dummy;
  queue_t_mem[Q].Head = queue_t_mem[Q].Tail;
  queue_t_mem[Q].T_lock = 0;
  queue_t_mem[Q].H_lock =
  queue_t_mem[Q].T_lock;
  in_initialize ! 0;
  goto end;
  end :
  printf ("End of initialize\n")
}

proctype enqueue(chan in_enqueue; int Q; int val){
  int node_t_ct; int node;
  int tmp; int mem_5;
  printf ("Start of enqueue\n")
  atomic {
    node_t_ct = 1;
    do
    :: (node_t_ct >= 9) -> break
    :: else ->
    if
    :: (node_t_valid[node_t_ct] == 0) ->
    node_t_valid[node_t_ct] = 1;
    break
    :: else -> node_t_ct ++
    fi
    od;
    assert (node_t_ct < 9);
    tmp = node_t_ct;
    node_t_ct = 1
  };
  node = tmp;
  node_t_mem[node].value = val;
  node_t_mem[node].next = 0;
  atomic {
    (queue_t_mem[Q].T_lock == 0) ->
    queue_t_mem[Q].T_lock = 1
  };
  mem_5 = queue_t_mem[Q].Tail;
  node_t_mem[mem_5].next = node;
  queue_t_mem[Q].Tail = node;
  queue_t_mem[Q].T_lock = 0;
  in_enqueue ! 0;
  goto end;
  end :
  printf ("End of enqueue\n")
}

proctype dequeue(chan in_dequeue; int Q; int pvalue){
  int node; int new_head;
  printf ("Start of dequeue\n")
  atomic {
    (queue_t_mem[Q].H_lock == 0) ->
    queue_t_mem[Q].H_lock = 1
  };
  node = queue_t_mem[Q].Head;
  new_head = node_t_mem[node].next;
  if
  :: (new_head == 0) ->
  queue_t_mem[Q].H_lock = 0;
  in_dequeue ! 0;
  goto end
  :: else
  fi;
  int_mem[pvalue] = node_t_mem[new_head].
  value;
  queue_t_mem[Q].Head = new_head;
  queue_t_mem[Q].H_lock = 0;
  d_step {
    node_t_valid[node] = 0;
    node_t_mem[node].next = 0;
    node_t_mem[node].value = 0
  };
  in_dequeue ! 1;
  goto end;
  end :
  printf ("End of dequeue\n")
}

////////////////////////////////////////////////////////////////////////////////

int ins = 1;
int check;
proctype i(chan in_i; int Q){
  chan ret_initialize = [0] of { bit };
  run initialize(ret_initialize, Q);
  ret_initialize ? 0;
  in_i ! 0;
  goto end;
  end :
  printf ("End of i\n")
}

proctype e(int Q){
  chan ret_enqueue = [0] of { bit };
  run enqueue(ret_enqueue, Q, ins);
  ret_enqueue ? 0; ins ++;
  run enqueue(ret_enqueue, Q, ins);
  ret_enqueue ? 0; ins ++;
  run enqueue(ret_enqueue, Q, ins);
  ret_enqueue ? 0; ins ++;
  end :
  printf ("End of e\n")
}

proctype d(int Q){
  chan ret_dequeue = [0] of { int };
  int int_ct; int res; int val; int tmp;
  atomic {
    int_ct = 1;
    do
    :: (int_ct >= 9) -> break
    :: else ->
    if
    :: (int_valid[int_ct] == 0) ->
    int_valid[int_ct] = 1;
    break
    :: else -> int_ct ++
    fi
    od;
    assert (int_ct < 9);
    tmp = int_ct;
    int_ct = 1
  };
  val = tmp;
  run dequeue(ret_dequeue, Q, val);
  ret_dequeue ? res;
  if
  :: (int_mem[val] == check) -> check ++
  :: else -> assert(res == 0)
  fi;
  run dequeue(ret_dequeue, Q, val);
  ret_dequeue ? res;
  if
  :: (int_mem[val] == check) -> check ++
  :: else -> assert(res == 0)
  fi;
  run dequeue(ret_dequeue, Q, val);
  ret_dequeue ? res;
  if
  :: (int_mem[val] == check) -> check ++
  :: else -> assert(res == 0)
  fi;
  end :
  printf ("End of d\n")
}

proctype main (chan in_main) {
  chan ret_i = [0] of { bit };
  int queue_t_ct;
  int queue;
  int tmp;
  atomic {
    queue_t_ct = 1;
    do
    :: (queue_t_ct >= 9) -> break
    :: else ->
    if
    :: (queue_t_valid[queue_t_ct] == 0) ->
    queue_t_valid[queue_t_ct] = 1;
    break
    :: else -> queue_t_ct ++
    fi
    od;
    assert (queue_t_ct < 9);
    tmp = queue_t_ct;
    queue_t_ct = 1
  };
  queue = tmp;
  run i(ret_i, queue);
  ret_i ? 0;
  run e(queue);
  run d(queue);
  in_main ! 0;
  goto end;
  end :
  printf ("End of main\n")
}

init {
  chan ret_main = [0] of { bit };
  run main(ret_main);
  ret_main ? 0
}
