typedef Node { unsigned nxt : 3; unsigned prv : 3; byte itm }
inline ncopy (dst, src) {
	dst.nxt = src.nxt
	dst.prv = src.prv
	dst.itm = src.itm
}


Node memory [8]
byte memory0 [8]
unsigned nptr : 3
typedef Control { unsigned head : 3; unsigned tail : 3; unsigned size : 3 }
Control chain
inline show_node0 () {
	printf("@@@ 0 PTR nptr %d\n" , nptr)
}


inline show_node1 () {
	printf("@@@ 0 STRUCT nptr\n")
	printf("@@@ 0 SCALAR itm %d\n" , itm)
	printf("@@@ 0 END nptr\n")
}


inline show_node () {
	atomic{
		show_node0 ()
		if
		:: nptr ->
			int nxt = chain.head
			int prv = memory[nptr].prv
			int itm = memory[nptr].itm
			show_node1 ()
		:: else ->
			skip
		fi;
	}
}


inline show_chain0 () {
	printf("@@@ 0 SEQ chain\n")
}


inline show_chain1 () {
	printf("@@@ 0 SCALAR _ %d\n" , itm)
}


inline show_chain2 () {
	printf("@@@ 0 END chain\n")
}


inline show_chain () {
	int cnp
	int cnp0
	atomic{
		cnp = chain.head
		cnp0 = 0
		show_chain0 ()
		do
		:: (cnp == 0) ->
			break
		:: (cnp != 0) ->
			int itm = memory[cnp].itm
			cnp = memory[cnp].nxt
			memory0[cnp0] = itm
			cnp0 = (cnp0 + 1)
			show_chain1 ()
		od;
		show_chain2 ()
	}
}


inline append (ch, np) {
	assert((np != 0))
	assert((np != ch.head))
	assert((np != ch.tail))
	assert((memory[np].nxt == 0))
	assert((ch.size < 8))
	if
	:: (ch.size == 0) ->
		assert((ch.head == 0))
		assert((ch.tail == 0))
		ch.head = np
	:: else ->
		assert((ch.head != 0))
		assert((ch.tail != 0))
		memory[ch.tail].nxt = np
	fi;
	
	memory[np].prv = ch.tail
	ch.tail = np
	ch.size = (ch.size + 1)
}


inline doAppend0 () {
	printf("@@@ 0 CALL append %d %d\n" , val , addr)
}


active [0]  proctype doAppend(int addr; int val){
	atomic{
		memory[addr].itm = val
		append (chain, addr)
		doAppend0 ()
		show_chain ()
	}
}


inline get (ch, np) {
	np = ch.head
	if
	:: (ch.size == 0) ->
		assert((ch.head == 0))
		assert((ch.tail == 0))
	:: else ->
		assert((ch.head != 0))
		assert((ch.tail != 0))
		assert((memory[ch.head].prv == 0))
		ch.head = memory[np].nxt
		if
		:: (ch.head == 0) ->
			ch.tail = 0
		:: else ->
			memory[np].nxt = 0
			memory[ch.head].prv = 0
		fi;
		ch.size = (ch.size - 1)
	fi;
}


inline doGet0 () {
	printf("@@@ 0 CALL get %d\n" , nptr)
}


active [0]  proctype doGet(){
	atomic{
		get (chain, nptr)
		doGet0 ()
		show_chain ()
		show_node ()
	}
}


inline doNonNullGet0 () {
	printf("@@@ 0 CALL getNonNull %d\n" , nptr)
}


active [0]  proctype doNonNullGet(){
	atomic{
		(chain.head != 0)
		get (chain, nptr)
		assert((nptr != 0))
		doNonNullGet0 ()
		show_chain ()
		show_node ()
	}
}


init {
	pid nr
	atomic{
		printf("\n\n Chain Model running.\n")
		printf("@@@ 0 NAME Chain_AutoGen\n")
		printf("@@@ 0 DEF MAX_SIZE 8\n")
		printf("@@@ 0 DCLARRAY Node memory MAX_SIZE\n")
		printf("@@@ 0 DECL unsigned nptr NULL\n")
		printf("@@@ 0 DECL Control chain\n")
		printf("\nInitialising...\n")
		printf("@@@ 0 INIT\n")
		chain.head = 0
		chain.tail = 0
		chain.size = 0
		show_chain ()
		show_node ()
	}
	
	nr = _nr_pr
	run doGet ()
	(nr == _nr_pr)
	run doAppend (6 , 21)
	run doAppend (3 , 22)
	run doAppend (4 , 23)
	run doNonNullGet ()
	run doNonNullGet ()
	run doNonNullGet ()
	(nr == _nr_pr)
	assert((! (chain.size == 0)))
	printf("\nChain Model finished !\n\n")
}

