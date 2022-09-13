(******************************************************************************
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
 ******************************************************************************)

(*<*)
theory event
  imports Isabelle_Doc_reStructuredText.reStructuredText_Wrapper
begin

declare [[reStructuredText]]

comment \<open>
SPDX-License-Identifier: CC-BY-SA-4.0 OR BSD-2-Clause

Copyright (C) 2019-2021 Trinity College Dublin (www.tcd.ie)
\<close>

(*>*)

sectionX \<open>Test Generation for the Event Manager\<close>

text' \<open>
The Event Manager is a central piece of code in RTEMS SMP, being at the basis
of task communication and synchronization. It is used for instance in the
implementation of semaphores or various essential high-level data-structures,
and used in the Scheduling process. At the same time, its implementation is
making use of concurrent features of C11, and contains many unprotected
interactions with the Threads API. Having a Promela model faithfully modelling
the Event Manager code of RTEMS represent thus a real challenge, especially
with respect to formal testing. This application constitutes as well a way to
measure the completeness of our manual and automatic test generation tools
previously developed.
\<close>

(*<*)
rst_export_file

end
(*>*)
