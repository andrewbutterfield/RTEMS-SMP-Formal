/*
 * Copyright (C) 2019-2021 Trinity College Dublin (www.tcd.ie)
 *               2013 Zhongwei Yao.
 *
 *  The license and distribution terms for this file may be
 *  found in the file LICENSE in this distribution or at
 *  http://www.rtems.org/license/LICENSE.
 */

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include <t.h>
#include <rtems/bspIo.h>
#include <tmacros.h>

const char rtems_test_name[] = "TTEST 2";

#define test_assert(e) (e) ? (void)0 : test_failed(__LINE__, #e)

static void
test_failed(int line, const char *e)
{
	printk("FAILED:%i:%s\n", line, e);
	rtems_test_exit(1);
}

typedef struct {
  Chain_Node Node;
  int x;
} test_node;

static rtems_task Init(rtems_task_argument ignored)
{
    Freechain_Control fc0;
    Freechain_Control fc;
    test_node *node;

    TEST_BEGIN();

    // ---
    _Chain_Initialize(&fc0.Free, NULL, 0, sizeof(test_node));
    _Chain_Initialize(&fc.Free, NULL, 0, sizeof(test_node));

    // ADD
    node = _Freechain_Get(&fc0, malloc, 1, sizeof(test_node));
    node->x = 1;
    _Freechain_Put(&fc, node);

    // ADD
    node = _Freechain_Get(&fc0, malloc, 1, sizeof(test_node));
    node->x = 2;
    _Freechain_Put(&fc, node);

    // ADD
    node = _Freechain_Get(&fc0, malloc, 1, sizeof(test_node));
    node->x = 3;
    _Freechain_Put(&fc, node);

    // DEL
    node = _Freechain_Get(&fc, malloc, 1, sizeof(test_node));
    test_assert(node->x == 3);
    
    // DEL
    node = _Freechain_Get(&fc, malloc, 1, sizeof(test_node));
    test_assert(node->x == 2);
    test_assert(! _Chain_Is_empty( &fc.Free ));
    
    // DEL
    node = _Freechain_Get(&fc, malloc, 1, sizeof(test_node));
    test_assert(node->x == 1);
    test_assert(_Chain_Is_empty( &fc.Free ));
    
    // ---
    TEST_END();
    rtems_test_exit(0);
}

/* configuration information */

#define CONFIGURE_APPLICATION_NEEDS_SIMPLE_CONSOLE_DRIVER
#define CONFIGURE_APPLICATION_DOES_NOT_NEED_CLOCK_DRIVER

#define CONFIGURE_INITIAL_EXTENSIONS RTEMS_TEST_INITIAL_EXTENSION

#define CONFIGURE_RTEMS_INIT_TASKS_TABLE
#define CONFIGURE_MAXIMUM_TASKS 1

#define CONFIGURE_INIT
#include <rtems/confdefs.h>

/* global variables */
