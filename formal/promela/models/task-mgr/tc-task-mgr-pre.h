/* SPDX-License-Identifier: BSD-2-Clause */

/**
 * @file
 *
 * @ingroup RTEMSTestCaseRtemsTaskMgr
 */

/*
 * Copyright (C) 2020 embedded brains GmbH (http://www.embedded-brains.de)
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 */

/*
 * Do not manually edit this file.  It is part of the RTEMS quality process
 * and was automatically generated.
 *
 * If you find something that needs to be fixed or worded better please
 * post a report to an RTEMS mailing list or raise a bug report:
 *
 * https://docs.rtems.org/branches/master/user/support/bugs.html
 *
 * For information on updating and regenerating please refer to:
 *
 * https://docs.rtems.org/branches/master/eng/req/howto.html
 */

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include <rtems/rtems/eventimpl.h>
#include <rtems/rtems/tasksdata.h>
#include <rtems/score/statesimpl.h>
#include <rtems/score/threadimpl.h>

#include "tr-task-mgr-model.h"

#include <rtems/test.h>

/**
 * @defgroup RTEMSTestCaseRtemsEventValSendReceive \
 *   spec:/rtems/event/val/send-receive
 *
 * @ingroup RTEMSTestSuiteTestsuitesValidation0
 *
 * @brief Tests the rtems_event_send and rtems_event_receive directives.
 *
 * This test case performs the following actions:
 *
 * - Run the event send and receive tests for the application event set defined
 *   by /rtems/event/req/send-receive.
 *
 * @{
 */

static rtems_status_code TaskCreate(
    rtems_name          name,
    rtems_task_priority initial_priority,
    size_t              stack_size,
    rtems_mode          initial_modes,
    rtems_attribute     attribute_set,
    rtems_id            *id
)
{
  return rtems_task_create( 
                            name, 
                            initial_priority, 
                            stack_size, 
                            initial_modes, 
                            attribute_set, 
                            id  
                        );
}

static rtems_status_code TaskStart(
    rtems_id            id,
    rtems_task_entry    entry_point,
    rtems_task_argument argument
)
{
    return rtems_task_start(
                            id,
                            entry_point,
                            argument
                        );
}

static rtems_status_code TaskDelete(
    rtems_id id 
)
{
    return rtems_task_delete( id );
}

static rtems_status_code TaskSuspend(
    rtems_id id 
)
{
    return rtems_task_suspend( id );
}

static rtems_status_code IsTaskSuspended(
    rtems_id id
)
{
    return rtems_task_is_suspended( id );
}

static rtems_status_code TaskResume(
    rtems_id id 
)
{
    return rtems_task_resume( id );
}

static rtems_status_code TaskSetPriority(
    rtems_id             id,
    rtems_task_priority  new_priority,
    rtems_task_priority *old_priority
)
{
    return rtems_task_set_priority( id, 
                                    new_priority, 
                                    old_priority
                                );
}