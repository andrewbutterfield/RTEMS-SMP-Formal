/* SPDX-License-Identifier: BSD-2-Clause */

/**
 * @file
 *
 * @ingroup RTEMSTestCaseRtemsBarrierVal
 */

/*
 * Copyright (C) 2020 embedded brains GmbH (http://www.embedded-brains.de)
 *               2022 Trinity College Dublin (http://www.tcd.ie)
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

#include <rtems/rtems/tasksdata.h>
#include <rtems/score/statesimpl.h>
#include <rtems/score/threadimpl.h>

#include "tr-barrier-mgr-model.h"

#include <rtems/test.h>

/**
 * @defgroup RTEMSTestCaseRtemsBarrierVal
 *
 * @ingroup RTEMSTestSuiteTestsuitesValidation0
 *
 * @brief Tests the rtems_barrier_create, rtems_barrier_ident,
 * rtems_barrier_wait, rtems_barrier_release and rtems_barrier_delete
 * directives.
 *
 * This test case performs the following actions:
 *
 * - Runs tests for Barrier Manager
 *
 * @{
 */

/**
 * @fn void T_case_body_RtemsBarrierVal void )
 */
/** @} */
