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

#include <rtems/test.h>
#include <rtems/test-info.h>

// include <tmacros.h>
#include <rtems.h>
// include <t.h>

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
// @@@NAME Chain_AutoGen
// @@@DEF MAX_SIZE 8
#define MAX_SIZE 8

T_TEST_CASE(Chain_AutoGen) {
  // @@@DECL Node memory[MAX_SIZE]
  item memory[MAX_SIZE] ;
  // @@@DECL unsigned nptr NULL
  // @@@DECL Control chain
  rtems_chain_control chain ;
  item * nptr = NULL ;
  T_log(T_NORMAL,"@@@INIT");
  rtems_chain_initialize_empty(&chain);
  T_log(T_NORMAL,"@@@SEQ chain");
  T_log(T_NORMAL,"@@@END chain");
  show_chain(&chain,buffer);
  T_eq_str(buffer," 0");

  T_log(T_NORMAL,"@@@PTR nptr 0");
  T_eq_ptr(nptr,NULL);
  T_log(T_NORMAL,"@@@CALL append 23 4");
  memory[4].val = 23;
  rtems_chain_append(&chain,(rtems_chain_node*)&memory[4]);

  T_log(T_NORMAL,"@@@SEQ chain");
  T_log(T_NORMAL,"@@@SCALAR _ 23");
  T_log(T_NORMAL,"@@@END chain");
  show_chain(&chain,buffer);
  T_eq_str(buffer," 23 0");

  T_log(T_NORMAL,"@@@CALL getNonNull 4");
  nptr = get_item(&chain);
  T_eq_ptr(nptr,&memory[4]);

  T_log(T_NORMAL,"@@@SEQ chain");
  T_log(T_NORMAL,"@@@END chain");
  show_chain(&chain,buffer);
  T_eq_str(buffer," 0");

  T_log(T_NORMAL,"@@@PTR nptr 4");
  T_eq_ptr(nptr,&memory[4]);
  T_log(T_NORMAL,"@@@STRUCT nptr");
  T_log(T_NORMAL,"@@@PTR nxt 0");
  T_eq_ptr(nptr->node.next,&chain.Tail.Node);
  T_log(T_NORMAL,"@@@PTR prv 0");
  T_eq_ptr(nptr->node.previous,&chain.Head.Node);
  T_log(T_NORMAL,"@@@SCALAR itm 23");
  T_eq_int(nptr->val,23);
  T_log(T_NORMAL,"@@@END nptr");
  T_log(T_NORMAL,"@@@CALL append 22 3");
  memory[3].val = 22;
  rtems_chain_append(&chain,(rtems_chain_node*)&memory[3]);

  T_log(T_NORMAL,"@@@SEQ chain");
  T_log(T_NORMAL,"@@@SCALAR _ 22");
  T_log(T_NORMAL,"@@@END chain");
  show_chain(&chain,buffer);
  T_eq_str(buffer," 22 0");

  T_log(T_NORMAL,"@@@CALL getNonNull 3");
  nptr = get_item(&chain);
  T_eq_ptr(nptr,&memory[3]);

  T_log(T_NORMAL,"@@@SEQ chain");
  T_log(T_NORMAL,"@@@END chain");
  show_chain(&chain,buffer);
  T_eq_str(buffer," 0");

  T_log(T_NORMAL,"@@@PTR nptr 3");
  T_eq_ptr(nptr,&memory[3]);
  T_log(T_NORMAL,"@@@STRUCT nptr");
  T_log(T_NORMAL,"@@@PTR nxt 0");
  T_eq_ptr(nptr->node.next,&chain.Tail.Node);
  T_log(T_NORMAL,"@@@PTR prv 0");
  T_eq_ptr(nptr->node.previous,&chain.Head.Node);
  T_log(T_NORMAL,"@@@SCALAR itm 22");
  T_eq_int(nptr->val,22);
  T_log(T_NORMAL,"@@@END nptr");
  T_log(T_NORMAL,"@@@CALL append 21 6");
  memory[6].val = 21;
  rtems_chain_append(&chain,(rtems_chain_node*)&memory[6]);

  T_log(T_NORMAL,"@@@SEQ chain");
  T_log(T_NORMAL,"@@@SCALAR _ 21");
  T_log(T_NORMAL,"@@@END chain");
  show_chain(&chain,buffer);
  T_eq_str(buffer," 21 0");

  T_log(T_NORMAL,"@@@CALL getNonNull 6");
  nptr = get_item(&chain);
  T_eq_ptr(nptr,&memory[6]);

  T_log(T_NORMAL,"@@@SEQ chain");
  T_log(T_NORMAL,"@@@END chain");
  show_chain(&chain,buffer);
  T_eq_str(buffer," 0");

  T_log(T_NORMAL,"@@@PTR nptr 6");
  T_eq_ptr(nptr,&memory[6]);
  T_log(T_NORMAL,"@@@STRUCT nptr");
  T_log(T_NORMAL,"@@@PTR nxt 0");
  T_eq_ptr(nptr->node.next,&chain.Tail.Node);
  T_log(T_NORMAL,"@@@PTR prv 0");
  T_eq_ptr(nptr->node.previous,&chain.Head.Node);
  T_log(T_NORMAL,"@@@SCALAR itm 21");
  T_eq_int(nptr->val,21);
  T_log(T_NORMAL,"@@@END nptr");
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
