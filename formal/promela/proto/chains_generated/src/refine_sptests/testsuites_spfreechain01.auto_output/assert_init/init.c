/******************************************************************************
 * FV2-201
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
 ******************************************************************************/


#include <tmacros.h>
#include <rtems.h>
#include <rtems/test.h>
#include <rtems/score/chain.h>

static const T_config config = {
    .name = "Promela-Chains",
    .putchar = T_putchar_default,
    .verbosity = T_VERBOSE,
    .now = T_now_clock
};


rtems_chain_control chain;

typedef struct item
{
    rtems_chain_node node;
    int               val;
} item;

item* get_item( rtems_chain_control* control);
item* get_item( rtems_chain_control* control)
{
    return (item*) rtems_chain_get(control);
}

#define BUFSIZE 80
char buffer[BUFSIZE];


void show_chain(rtems_chain_control *control, char *str);
void show_chain(rtems_chain_control *control, char *str)
{
    item *itm;
    rtems_chain_node *nod;
    int cp, len;
    char *s;

    nod = (rtems_chain_node *)&control->Head;
    itm = (item *)nod->next;
    s = str;
    len = BUFSIZE;
    while (itm) {
        cp = T_snprintf(s, len, " %d",itm->val);
        s += cp;
        len -= cp;
        itm = (item*)((rtems_chain_node*)itm)->next;
     }
}

/* =============================================== */


const char rtems_test_name[] = "Chain_AutoGen";
// @@@ 0 NAME Chain_AutoGen
// @@@ 0 DEF MAX_SIZE 8
#define MAX_SIZE 8
// @@@ 0 DECL Node memory[MAX_SIZE]
item memory[MAX_SIZE] ;
// @@@ 0 DECL unsigned nptr NULL
// @@@ 0 DECL Control chain
rtems_chain_control chain ;

/* ===== TEST CODE SEGMENT 0 =====*/

void TestSegment0(void);
void TestSegment0(void) {
  item * nptr = NULL ;
  T_log(T_NORMAL,"@@@ 0 INIT");
  rtems_chain_initialize_empty(&chain);

#define str(s) #s
#define app(str, s) str(s)
#define xstr(s) app(str, s)
#define xT_eq_ptr(a, e) T_eq_ptr(a, e)

//@ promela_term \<open>show_chain0\<close>

  T_log(T_NORMAL,"@@@ 0 SEQ chain");


//@ promela_term \<open>show_chain2\<close>

  T_log(T_NORMAL,"@@@ 0 END chain");
  show_chain(&chain,buffer);

#define memory0_0 ""
#define memory0_1 memory0_0 " 0"
#define memory0_2 memory0_1 " 0"
#define memory0_3 memory0_2 " 0"
#define memory0_4 memory0_3 " 0"
#define memory0_5 memory0_4 " 0"
#define memory0_6 memory0_5 " 0"
#define memory0_7 memory0_6 " 0"
#define memory0_8 memory0_7 " 0"
#define memory0(pos) memory0_ ## pos
#define cnp0 0
  T_eq_str(buffer, app(memory0, cnp0) " 0");

#undef memory0_0
#undef memory0_1
#undef memory0_2
#undef memory0_3
#undef memory0_4
#undef memory0_5
#undef memory0_6
#undef memory0_7
#undef memory0_8
#undef memory0
#undef cnp0

//@ promela_term \<open>show_node0\<close>

#define nptr0 0
  T_log(T_NORMAL,"@@@ 0 PTR nptr " xstr(nptr0));
#if nptr0
  xT_eq_ptr(nptr,&memory[nptr0]);
#else
  T_eq_ptr(nptr,NULL);
#endif

#undef nptr0

//@ promela_term \<open>show_chain0\<close>

  T_log(T_NORMAL,"@@@ 0 SEQ chain");


//@ promela_term \<open>show_chain2\<close>

  T_log(T_NORMAL,"@@@ 0 END chain");
  show_chain(&chain,buffer);

#define memory0_0 ""
#define memory0_1 memory0_0 " 0"
#define memory0_2 memory0_1 " 0"
#define memory0_3 memory0_2 " 0"
#define memory0_4 memory0_3 " 0"
#define memory0_5 memory0_4 " 0"
#define memory0_6 memory0_5 " 0"
#define memory0_7 memory0_6 " 0"
#define memory0_8 memory0_7 " 0"
#define memory0(pos) memory0_ ## pos
#define cnp0 0
  T_eq_str(buffer, app(memory0, cnp0) " 0");

#undef memory0_0
#undef memory0_1
#undef memory0_2
#undef memory0_3
#undef memory0_4
#undef memory0_5
#undef memory0_6
#undef memory0_7
#undef memory0_8
#undef memory0
#undef cnp0

//@ promela_term \<open>show_node0\<close>

#define nptr0 0
  T_log(T_NORMAL,"@@@ 0 PTR nptr " xstr(nptr0));
#if nptr0
  xT_eq_ptr(nptr,&memory[nptr0]);
#else
  T_eq_ptr(nptr,NULL);
#endif

#undef nptr0

//@ promela_term \<open>doAppend0\<close>

#define val0 21
#define addr 6
  T_log(T_NORMAL,"@@@ 0 CALL append " xstr(val0) " " xstr(addr));
  memory[addr].val = val0;
  rtems_chain_append(&chain,(rtems_chain_node*)&memory[addr]);

#undef val0
#undef addr

//@ promela_term \<open>show_chain0\<close>

  T_log(T_NORMAL,"@@@ 0 SEQ chain");


//@ promela_term \<open>show_chain1\<close>

#define itm 21
  T_log(T_NORMAL,"@@@ 0 SCALAR _ " xstr(itm));

#undef itm

//@ promela_term \<open>show_chain2\<close>

  T_log(T_NORMAL,"@@@ 0 END chain");
  show_chain(&chain,buffer);

#define memory0_0 ""
#define memory0_1 memory0_0 " 21"
#define memory0_2 memory0_1 " 0"
#define memory0_3 memory0_2 " 0"
#define memory0_4 memory0_3 " 0"
#define memory0_5 memory0_4 " 0"
#define memory0_6 memory0_5 " 0"
#define memory0_7 memory0_6 " 0"
#define memory0_8 memory0_7 " 0"
#define memory0(pos) memory0_ ## pos
#define cnp0 1
  T_eq_str(buffer, app(memory0, cnp0) " 0");

#undef memory0_0
#undef memory0_1
#undef memory0_2
#undef memory0_3
#undef memory0_4
#undef memory0_5
#undef memory0_6
#undef memory0_7
#undef memory0_8
#undef memory0
#undef cnp0

//@ promela_term \<open>doAppend0\<close>

#define val0 22
#define addr 3
  T_log(T_NORMAL,"@@@ 0 CALL append " xstr(val0) " " xstr(addr));
  memory[addr].val = val0;
  rtems_chain_append(&chain,(rtems_chain_node*)&memory[addr]);

#undef val0
#undef addr

//@ promela_term \<open>show_chain0\<close>

  T_log(T_NORMAL,"@@@ 0 SEQ chain");


//@ promela_term \<open>show_chain1\<close>

#define itm 21
  T_log(T_NORMAL,"@@@ 0 SCALAR _ " xstr(itm));

#undef itm

//@ promela_term \<open>show_chain1\<close>

#define itm 22
  T_log(T_NORMAL,"@@@ 0 SCALAR _ " xstr(itm));

#undef itm

//@ promela_term \<open>show_chain2\<close>

  T_log(T_NORMAL,"@@@ 0 END chain");
  show_chain(&chain,buffer);

#define memory0_0 ""
#define memory0_1 memory0_0 " 21"
#define memory0_2 memory0_1 " 22"
#define memory0_3 memory0_2 " 0"
#define memory0_4 memory0_3 " 0"
#define memory0_5 memory0_4 " 0"
#define memory0_6 memory0_5 " 0"
#define memory0_7 memory0_6 " 0"
#define memory0_8 memory0_7 " 0"
#define memory0(pos) memory0_ ## pos
#define cnp0 2
  T_eq_str(buffer, app(memory0, cnp0) " 0");

#undef memory0_0
#undef memory0_1
#undef memory0_2
#undef memory0_3
#undef memory0_4
#undef memory0_5
#undef memory0_6
#undef memory0_7
#undef memory0_8
#undef memory0
#undef cnp0

//@ promela_term \<open>doAppend0\<close>

#define val0 23
#define addr 4
  T_log(T_NORMAL,"@@@ 0 CALL append " xstr(val0) " " xstr(addr));
  memory[addr].val = val0;
  rtems_chain_append(&chain,(rtems_chain_node*)&memory[addr]);

#undef val0
#undef addr

//@ promela_term \<open>show_chain0\<close>

  T_log(T_NORMAL,"@@@ 0 SEQ chain");


//@ promela_term \<open>show_chain1\<close>

#define itm 21
  T_log(T_NORMAL,"@@@ 0 SCALAR _ " xstr(itm));

#undef itm

//@ promela_term \<open>show_chain1\<close>

#define itm 22
  T_log(T_NORMAL,"@@@ 0 SCALAR _ " xstr(itm));

#undef itm

//@ promela_term \<open>show_chain1\<close>

#define itm 23
  T_log(T_NORMAL,"@@@ 0 SCALAR _ " xstr(itm));

#undef itm

//@ promela_term \<open>show_chain2\<close>

  T_log(T_NORMAL,"@@@ 0 END chain");
  show_chain(&chain,buffer);

#define memory0_0 ""
#define memory0_1 memory0_0 " 21"
#define memory0_2 memory0_1 " 22"
#define memory0_3 memory0_2 " 23"
#define memory0_4 memory0_3 " 0"
#define memory0_5 memory0_4 " 0"
#define memory0_6 memory0_5 " 0"
#define memory0_7 memory0_6 " 0"
#define memory0_8 memory0_7 " 0"
#define memory0(pos) memory0_ ## pos
#define cnp0 3
  T_eq_str(buffer, app(memory0, cnp0) " 0");

#undef memory0_0
#undef memory0_1
#undef memory0_2
#undef memory0_3
#undef memory0_4
#undef memory0_5
#undef memory0_6
#undef memory0_7
#undef memory0_8
#undef memory0
#undef cnp0

//@ promela_term \<open>doNonNullGet0\<close>

#define nptr0 6
  T_log(T_NORMAL,"@@@ 0 CALL getNonNull " xstr(nptr0));
  nptr = get_item(&chain);
  xT_eq_ptr(nptr,&memory[nptr0]);

#undef nptr0

//@ promela_term \<open>show_chain0\<close>

  T_log(T_NORMAL,"@@@ 0 SEQ chain");


//@ promela_term \<open>show_chain1\<close>

#define itm 22
  T_log(T_NORMAL,"@@@ 0 SCALAR _ " xstr(itm));

#undef itm

//@ promela_term \<open>show_chain1\<close>

#define itm 23
  T_log(T_NORMAL,"@@@ 0 SCALAR _ " xstr(itm));

#undef itm

//@ promela_term \<open>show_chain2\<close>

  T_log(T_NORMAL,"@@@ 0 END chain");
  show_chain(&chain,buffer);

#define memory0_0 ""
#define memory0_1 memory0_0 " 22"
#define memory0_2 memory0_1 " 23"
#define memory0_3 memory0_2 " 23"
#define memory0_4 memory0_3 " 0"
#define memory0_5 memory0_4 " 0"
#define memory0_6 memory0_5 " 0"
#define memory0_7 memory0_6 " 0"
#define memory0_8 memory0_7 " 0"
#define memory0(pos) memory0_ ## pos
#define cnp0 2
  T_eq_str(buffer, app(memory0, cnp0) " 0");

#undef memory0_0
#undef memory0_1
#undef memory0_2
#undef memory0_3
#undef memory0_4
#undef memory0_5
#undef memory0_6
#undef memory0_7
#undef memory0_8
#undef memory0
#undef cnp0

//@ promela_term \<open>show_node0\<close>

#define nptr0 6
  T_log(T_NORMAL,"@@@ 0 PTR nptr " xstr(nptr0));
#if nptr0
  xT_eq_ptr(nptr,&memory[nptr0]);
#else
  T_eq_ptr(nptr,NULL);
#endif

#undef nptr0

//@ promela_term \<open>show_node1\<close>

  T_log(T_NORMAL,"@@@ 0 STRUCT nptr");

#define nxt 3
  T_log(T_NORMAL,"@@@ 0 PTR nxt " xstr(nxt));
#if nxt
  xT_eq_ptr(nptr->node.next,&memory[nxt]);
#else
  T_eq_ptr(nptr->node.next,&chain.Tail.Node);
#endif

#define prv 0
  T_log(T_NORMAL,"@@@ 0 PTR prv " xstr(prv));
  T_eq_int(prv, 0);
  T_eq_ptr(nptr->node.previous,&chain.Head.Node);
  T_eq_ptr(nptr->node.previous->previous,NULL);
  T_eq_ptr(nptr->node.previous->next,nptr->node.next);

#define itm 21
  T_log(T_NORMAL,"@@@ 0 SCALAR itm " xstr(itm));
  T_eq_int(nptr->val,itm);

  T_log(T_NORMAL,"@@@ 0 END nptr");

#undef nxt
#undef prv
#undef itm

//@ promela_term \<open>doNonNullGet0\<close>

#define nptr0 3
  T_log(T_NORMAL,"@@@ 0 CALL getNonNull " xstr(nptr0));
  nptr = get_item(&chain);
  xT_eq_ptr(nptr,&memory[nptr0]);

#undef nptr0

//@ promela_term \<open>show_chain0\<close>

  T_log(T_NORMAL,"@@@ 0 SEQ chain");


//@ promela_term \<open>show_chain1\<close>

#define itm 23
  T_log(T_NORMAL,"@@@ 0 SCALAR _ " xstr(itm));

#undef itm

//@ promela_term \<open>show_chain2\<close>

  T_log(T_NORMAL,"@@@ 0 END chain");
  show_chain(&chain,buffer);

#define memory0_0 ""
#define memory0_1 memory0_0 " 23"
#define memory0_2 memory0_1 " 23"
#define memory0_3 memory0_2 " 23"
#define memory0_4 memory0_3 " 0"
#define memory0_5 memory0_4 " 0"
#define memory0_6 memory0_5 " 0"
#define memory0_7 memory0_6 " 0"
#define memory0_8 memory0_7 " 0"
#define memory0(pos) memory0_ ## pos
#define cnp0 1
  T_eq_str(buffer, app(memory0, cnp0) " 0");

#undef memory0_0
#undef memory0_1
#undef memory0_2
#undef memory0_3
#undef memory0_4
#undef memory0_5
#undef memory0_6
#undef memory0_7
#undef memory0_8
#undef memory0
#undef cnp0

//@ promela_term \<open>show_node0\<close>

#define nptr0 3
  T_log(T_NORMAL,"@@@ 0 PTR nptr " xstr(nptr0));
#if nptr0
  xT_eq_ptr(nptr,&memory[nptr0]);
#else
  T_eq_ptr(nptr,NULL);
#endif

#undef nptr0

//@ promela_term \<open>show_node1\<close>

  T_log(T_NORMAL,"@@@ 0 STRUCT nptr");

#define nxt 4
  T_log(T_NORMAL,"@@@ 0 PTR nxt " xstr(nxt));
#if nxt
  xT_eq_ptr(nptr->node.next,&memory[nxt]);
#else
  T_eq_ptr(nptr->node.next,&chain.Tail.Node);
#endif

#define prv 0
  T_log(T_NORMAL,"@@@ 0 PTR prv " xstr(prv));
  T_eq_int(prv, 0);
  T_eq_ptr(nptr->node.previous,&chain.Head.Node);
  T_eq_ptr(nptr->node.previous->previous,NULL);
  T_eq_ptr(nptr->node.previous->next,nptr->node.next);

#define itm 22
  T_log(T_NORMAL,"@@@ 0 SCALAR itm " xstr(itm));
  T_eq_int(nptr->val,itm);

  T_log(T_NORMAL,"@@@ 0 END nptr");

#undef nxt
#undef prv
#undef itm

//@ promela_term \<open>doNonNullGet0\<close>

#define nptr0 4
  T_log(T_NORMAL,"@@@ 0 CALL getNonNull " xstr(nptr0));
  nptr = get_item(&chain);
  xT_eq_ptr(nptr,&memory[nptr0]);

#undef nptr0

//@ promela_term \<open>show_chain0\<close>

  T_log(T_NORMAL,"@@@ 0 SEQ chain");


//@ promela_term \<open>show_chain2\<close>

  T_log(T_NORMAL,"@@@ 0 END chain");
  show_chain(&chain,buffer);

#define memory0_0 ""
#define memory0_1 memory0_0 " 23"
#define memory0_2 memory0_1 " 23"
#define memory0_3 memory0_2 " 23"
#define memory0_4 memory0_3 " 0"
#define memory0_5 memory0_4 " 0"
#define memory0_6 memory0_5 " 0"
#define memory0_7 memory0_6 " 0"
#define memory0_8 memory0_7 " 0"
#define memory0(pos) memory0_ ## pos
#define cnp0 0
  T_eq_str(buffer, app(memory0, cnp0) " 0");

#undef memory0_0
#undef memory0_1
#undef memory0_2
#undef memory0_3
#undef memory0_4
#undef memory0_5
#undef memory0_6
#undef memory0_7
#undef memory0_8
#undef memory0
#undef cnp0

//@ promela_term \<open>show_node0\<close>

#define nptr0 4
  T_log(T_NORMAL,"@@@ 0 PTR nptr " xstr(nptr0));
#if nptr0
  xT_eq_ptr(nptr,&memory[nptr0]);
#else
  T_eq_ptr(nptr,NULL);
#endif

#undef nptr0

//@ promela_term \<open>show_node1\<close>

  T_log(T_NORMAL,"@@@ 0 STRUCT nptr");

#define nxt 0
  T_log(T_NORMAL,"@@@ 0 PTR nxt " xstr(nxt));
#if nxt
  xT_eq_ptr(nptr->node.next,&memory[nxt]);
#else
  T_eq_ptr(nptr->node.next,&chain.Tail.Node);
#endif

#define prv 0
  T_log(T_NORMAL,"@@@ 0 PTR prv " xstr(prv));
  T_eq_int(prv, 0);
  T_eq_ptr(nptr->node.previous,&chain.Head.Node);
  T_eq_ptr(nptr->node.previous->previous,NULL);
  T_eq_ptr(nptr->node.previous->next,nptr->node.next);

#define itm 23
  T_log(T_NORMAL,"@@@ 0 SCALAR itm " xstr(itm));
  T_eq_int(nptr->val,itm);

  T_log(T_NORMAL,"@@@ 0 END nptr");

#undef nxt
#undef prv
#undef itm

}

T_TEST_CASE(Chain_AutoGen) {
  TestSegment0();
}

static void Init(rtems_task_argument arg)
{
   T_run_initialize(&config);
   T_register();
   T_run_by_name("Chain_AutoGen");
}

/* =============================================== */


/* configuration information */

#define CONFIGURE_APPLICATION_NEEDS_SIMPLE_CONSOLE_DRIVER
#define CONFIGURE_APPLICATION_NEEDS_CLOCK_DRIVER

#define CONFIGURE_INITIAL_EXTENSIONS RTEMS_TEST_INITIAL_EXTENSION

#define CONFIGURE_RTEMS_INIT_TASKS_TABLE
#define CONFIGURE_MAXIMUM_TASKS 1

#define CONFIGURE_INIT
#define CONFIGURE_INIT_TASK_ATTRIBUTES RTEMS_FLOATING_POINT
#include <rtems/confdefs.h>

/* global variables */

