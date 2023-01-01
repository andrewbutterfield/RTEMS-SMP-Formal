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
theory models
  imports Isabelle_Doc_reStructuredText.reStructuredText_Wrapper
begin

declare [[reStructuredText]]

comment \<open>
SPDX-License-Identifier: CC-BY-SA-4.0 OR BSD-2-Clause

Copyright (C) 2019-2021 Trinity College Dublin (www.tcd.ie)
\<close>

(*>*)

sectionX \<open>Models\<close>

subsectionX \<open>API: Test Samples\<close>

paragraphX \<open>High level structure of spintrcritical\<close>

text' \<open>
ISR = interrupt service routine
\<close>

subparagraphX \<open>Descriptions cited from the source\<close>

text' \<open>
\<^item> spintrcritical01 - spintrcritical05
  \<^item> semaphore release from ISR while blocking
\<^item> spintrcritical06 - spintrcritical07
  \<^item> semaphore release from ISR while blocking
\<^item> spintrcritical08
  \<^item> period ending while blocking
\<^item> spintrcritical09
  \<^item> timeout from ISR while blocking
\<^item> spintrcritical10
  \<^item> any satisfied before timeout while blocking on event
\<^item> spintrcritical11 - spintrcritical12
  \<^item> event send from ISR while blocking
\<^item> spintrcritical13 - spintrcritical14
  \<^item> timer fire from ISR while firing
\<^item> spintrcritical15
  \<^item> timeout of a thread while another is blocking
\<^item> spintrcritical16
  \<^item> timeout of a thread that had its blocking
\<close>

subparagraphX \<open>Missing descriptions\<close>

text' \<open>
\<^item> spintrcritical18
  \<^item> priority, ?
\<^item> spintrcritical20
  \<^item> long, ?
\<^item> spintrcritical21
  \<^item> eventimpl, ?
\<^item> spintrcritical22
  \<^item> long, ?
\<^item> spintrcritical23
  \<^item> priority, ?
\<^item> spintrcritical24
  \<^item> imfs, ?
\<close>

subparagraphX \<open>Miscellaneous analyzing scripts\<close>

text' \<open>
\<^item> \<^verbatim>\<open>grep -i semaphore spintrcritical??/*{h,c}\<close>
\<^item> \<^verbatim>\<open>grep interrupt_critical_section_test spintrcritical??/*{h,c}\<close>
\<^item> \<^verbatim>\<open>grep static init.c | while read i ; do echo "${i};" ; done\<close>
\<close>

subsubsectionX \<open>spintrcritical\<close>

paragraphX \<open>spintrcritical: prototype\<close>

text' \<open>
\<^item> C file \<^verbatim>\<open>testsuites/sptests/spintrcritical_support/intrcritical.h\<close> (standalone prototype file)
  \<^item> C function prototype \<^verbatim>\<open>interrupt_critical_section_test\<close>
\<close>

paragraphX \<open>spintrcritical: body\<close>

text' \<open>
\<^item> C file \<^verbatim>\<open>testsuites/sptests/spintrcritical_support/intrcritical.c\<close>
  \<^item> C function body \<^verbatim>\<open>interrupt_critical_section_test\<close> calling \<^verbatim>\<open>_Event_Seize\<close>
\<close>

subsectionX \<open>Missing Features on Inspection of C Files\<close>

text' \<open>
\<^item> Ctrl + Click on "struct" variables
\<^item> original C comments are not present in the generated \<^verbatim>\<open>all_core_index\<close>, \<^verbatim>\<open>all_core_raw\<close>, and \<^verbatim>\<open>diff\<close>
\<^item> In \<^verbatim>\<open>all_core_index\<close> etc, possibility to Ctrl + Click to the original C file; introduce the annotation command "text"?
\<close>

subsectionX \<open>Miscellaneous\<close>

text' \<open>
\<^item> \<^url>\<open>http://pages.cs.wisc.edu/~remzi/OSTEP/\<close>
\<^item> @{cite "DBLP:conf/ecrts/ColinP01a"}
\<close>

(*<*)
rst_export_file

end
(*>*)
