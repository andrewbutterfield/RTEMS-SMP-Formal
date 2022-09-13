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
theory experiments_next
  imports Isabelle_Doc_reStructuredText.reStructuredText_Wrapper
begin

declare [[reStructuredText]]

comment \<open>
SPDX-License-Identifier: CC-BY-SA-4.0 OR BSD-2-Clause

Copyright (C) 2019-2021 Trinity College Dublin (www.tcd.ie)
\<close>

(*>*)

sectionX \<open>\<close>

subsectionX \<open>API: Events, Thread\<close>

subsubsectionX \<open>Events\<close>

text' \<open>
In a nutshell, without detailing the specificity of respective files, we give a
quick overview of the architecture of the Event Manager in the RTEMS source.
\<close>

paragraphX \<open>events: prototype API\<close>

text' \<open>
\<^item> C file \<^verbatim>\<open>cpukit/include/rtems/rtems/event.h\<close> (standalone prototype file)
  \<^item> C function prototype \<^verbatim>\<open>rtems_event_receive\<close>
  \<^item> C function prototype \<^verbatim>\<open>rtems_event_send\<close>
  \<^item> C function prototype \<^verbatim>\<open>rtems_event_system_receive\<close>
  \<^item> C function prototype \<^verbatim>\<open>rtems_event_system_send\<close>

  \<^item> (C function body \<^verbatim>\<open>rtems_event_transient_receive\<close> calling \<^verbatim>\<open>rtems_event_system_receive\<close>)
  \<^item> (C function body \<^verbatim>\<open>rtems_event_transient_send\<close> calling \<^verbatim>\<open>rtems_event_system_send\<close>)
  \<^item> (C function body \<^verbatim>\<open>rtems_event_transient_clear\<close> calling \<^verbatim>\<open>rtems_event_system_receive\<close>)
\<close>

paragraphX \<open>events: receive, send (main entry points)\<close>

text' \<open>
\<^item> C file \<^verbatim>\<open>cpukit/rtems/src/eventreceive.c\<close>
  \<^item> C function body \<^verbatim>\<open>rtems_event_receive\<close> calling \<^verbatim>\<open>_Event_Seize\<close>
  \<^item> modelled by \<^file>\<open>models_events/src/cpukit/rtems/src/eventseize/eventreceive.pml\<close>

\<^item> C file \<^verbatim>\<open>cpukit/rtems/src/eventsend.c\<close>
  \<^item> C function body \<^verbatim>\<open>rtems_event_send\<close> calling \<^verbatim>\<open>_Event_Surrender\<close>
  \<^item> modelled by \<^file>\<open>models_events/src/cpukit/rtems/src/eventsurrender/eventsend.pml\<close>

\<^item> C file \<^verbatim>\<open>cpukit/rtems/src/systemeventreceive.c\<close>
  \<^item> C function body \<^verbatim>\<open>rtems_event_system_receive\<close> calling \<^verbatim>\<open>_Event_Seize\<close>
  \<^item> modelled by \<^file>\<open>models_events/src/cpukit/rtems/src/eventseize/systemeventreceive.pml\<close>

\<^item> C file \<^verbatim>\<open>cpukit/rtems/src/systemeventsend.c\<close>
  \<^item> C function body \<^verbatim>\<open>rtems_event_system_send\<close> calling \<^verbatim>\<open>_Event_Surrender\<close>
  \<^item> modelled by \<^file>\<open>models_events/src/cpukit/rtems/src/eventsurrender/systemeventsend.pml\<close>
\<close>

paragraphX \<open>events: seize, surrender (called by send and receive)\<close>

text' \<open>
\<^item> C file \<^verbatim>\<open>cpukit/rtems/src/eventseize.c\<close>
  \<^item> C function body \<^verbatim>\<open>_Event_Seize\<close>
  \<^item> modelled by \<^file>\<open>models_events/src/cpukit/rtems/src/eventseize.pml\<close>

\<^item> C file \<^verbatim>\<open>cpukit/rtems/src/eventsurrender.c\<close>
  \<^item> C function body \<^verbatim>\<open>_Event_Surrender\<close>
  \<^item> modelled by \<^file>\<open>models_events/src/cpukit/rtems/src/eventsurrender.pml\<close>
\<close>

subsubsectionX \<open>Thread\<close>

text' \<open>
The own implementation of seize and surrender is relying on the Thread API. We
list here the key functions of the API as used by surrender and seize.
\<close>

paragraphX \<open>thread: surrender\<close>

text' \<open>
\<^item> C files \<^verbatim>\<open>cpukit/rtems/src/eventsend.c\<close>, \<^verbatim>\<open>cpukit/rtems/src/systemeventsend.c\<close>
  \<^item> calling \<^verbatim>\<open>_Thread_Get\<close>
    \<^item> implemented in \<^verbatim>\<open>cpukit/score/src/threadget.c\<close>
\<close>

text' \<open>
\<^item> C files \<^verbatim>\<open>cpukit/rtems/src/eventsurrender.c\<close>
  \<^item> calling \<^verbatim>\<open>_Thread_Wait_flags_get\<close>
    \<^item> implemented in \<^verbatim>\<open>cpukit/include/rtems/score/threadimpl.h\<close>
  \<^item> calling \<^verbatim>\<open>_Thread_Wait_flags_set\<close>
    \<^item> implemented in \<^verbatim>\<open>cpukit/include/rtems/score/threadimpl.h\<close>
  \<^item> calling \<^verbatim>\<open>_Thread_Wait_flags_try_change_release\<close>
    \<^item> implemented in \<^verbatim>\<open>cpukit/include/rtems/score/threadimpl.h\<close>
  \<^item> calling \<^verbatim>\<open>_Thread_Wait_acquire_default_critical\<close>
    \<^item> implemented in \<^verbatim>\<open>cpukit/include/rtems/score/threadimpl.h\<close>
  \<^item> calling \<^verbatim>\<open>_Thread_Wait_release_default\<close>
    \<^item> implemented in \<^verbatim>\<open>cpukit/include/rtems/score/threadimpl.h\<close>
  \<^item> calling \<^verbatim>\<open>_Thread_Timer_remove\<close>
    \<^item> implemented in \<^verbatim>\<open>cpukit/include/rtems/score/threadimpl.h\<close>
  \<^item> calling \<^verbatim>\<open>_Thread_Unblock\<close>
    \<^item> implemented in \<^verbatim>\<open>cpukit/include/rtems/score/threadimpl.h\<close>
  \<^item> calling \<^verbatim>\<open>_Thread_Dispatch_enable\<close>
    \<^item> implemented in \<^verbatim>\<open>cpukit/include/rtems/score/threaddispatch.h\<close>
  \<^item> calling \<^verbatim>\<open>_Thread_Dispatch_disable_critical\<close>
    \<^item> implemented in \<^verbatim>\<open>cpukit/include/rtems/score/threaddispatch.h\<close>
\<close>

paragraphX \<open>thread: seize\<close>

text' \<open>
\<^item> C files \<^verbatim>\<open>cpukit/rtems/src/eventreceive.c\<close>, \<^verbatim>\<open>cpukit/rtems/src/systemeventreceive.c\<close>
  \<^item> calling \<^verbatim>\<open>_Thread_Wait_acquire_default_for_executing\<close>
    \<^item> implemented in \<^verbatim>\<open>cpukit/include/rtems/score/threadimpl.h\<close>
  \<^item> calling \<^verbatim>\<open>_Thread_Wait_release_default\<close>
    \<^item> implemented in \<^verbatim>\<open>cpukit/include/rtems/score/threadimpl.h\<close>
\<close>

text' \<open>
\<^item> C files \<^verbatim>\<open>cpukit/rtems/src/eventseize.c\<close>
  \<^item> calling \<^verbatim>\<open>_Thread_Wait_flags_set\<close>
    \<^item> implemented in \<^verbatim>\<open>cpukit/include/rtems/score/threadimpl.h\<close>
  \<^item> calling \<^verbatim>\<open>_Thread_Wait_flags_try_change_acquire\<close>
    \<^item> implemented in \<^verbatim>\<open>cpukit/include/rtems/score/threadimpl.h\<close>
  \<^item> calling \<^verbatim>\<open>_Thread_Wait_release_default\<close>
    \<^item> implemented in \<^verbatim>\<open>cpukit/include/rtems/score/threadimpl.h\<close>
  \<^item> calling \<^verbatim>\<open>_Thread_Add_timeout_ticks\<close>
    \<^item> implemented in \<^verbatim>\<open>cpukit/include/rtems/score/threadimpl.h\<close>
  \<^item> calling \<^verbatim>\<open>_Thread_Timer_remove\<close>
    \<^item> implemented in \<^verbatim>\<open>cpukit/include/rtems/score/threadimpl.h\<close>
  \<^item> calling \<^verbatim>\<open>_Thread_Unblock\<close>
    \<^item> implemented in \<^verbatim>\<open>cpukit/include/rtems/score/threadimpl.h\<close>
  \<^item> calling \<^verbatim>\<open>_Thread_Dispatch_disable_critical\<close>
    \<^item> implemented in \<^verbatim>\<open>cpukit/include/rtems/score/threaddispatch.h\<close>
  \<^item> calling \<^verbatim>\<open>_Thread_Dispatch_direct\<close>
    \<^item> implemented in \<^verbatim>\<open>cpukit/score/src/threaddispatch.c\<close>
  \<^item> calling \<^verbatim>\<open>_Thread_Set_state\<close>
    \<^item> implemented in \<^verbatim>\<open>cpukit/score/src/threadsetstate.c\<close>
\<close>

paragraphX \<open>thread: summary of expanded paths\<close>

text' \<open>
\<^item> \<^verbatim>\<open>cpukit/score/src/threadget.c\<close>
\<^item> \<^verbatim>\<open>cpukit/score/src/threadsetstate.c\<close>
\<^item> \<^verbatim>\<open>cpukit/score/src/threaddispatch.c\<close>
\<^item> \<^verbatim>\<open>cpukit/include/rtems/score/threaddispatch.h\<close>
\<^item> \<^verbatim>\<open>cpukit/include/rtems/score/threadimpl.h\<close>
\<close>

paragraphX \<open>thread: uniquely sorted\<close>

text' \<open>
  \<^item> calling \<^verbatim>\<open>_Thread_Add_timeout_ticks\<close>
    \<^item> implemented in \<^verbatim>\<open>cpukit/include/rtems/score/threadimpl.h\<close>
  \<^item> calling \<^verbatim>\<open>_Thread_Timer_remove\<close>
    \<^item> implemented in \<^verbatim>\<open>cpukit/include/rtems/score/threadimpl.h\<close>
  \<^item> calling \<^verbatim>\<open>_Thread_Unblock\<close>
    \<^item> implemented in \<^verbatim>\<open>cpukit/include/rtems/score/threadimpl.h\<close>
  \<^item> calling \<^verbatim>\<open>_Thread_Wait_acquire_default_critical\<close>
    \<^item> implemented in \<^verbatim>\<open>cpukit/include/rtems/score/threadimpl.h\<close>
  \<^item> calling \<^verbatim>\<open>_Thread_Wait_acquire_default_for_executing\<close>
    \<^item> implemented in \<^verbatim>\<open>cpukit/include/rtems/score/threadimpl.h\<close>
  \<^item> calling \<^verbatim>\<open>_Thread_Wait_flags_get\<close>
    \<^item> implemented in \<^verbatim>\<open>cpukit/include/rtems/score/threadimpl.h\<close>
  \<^item> calling \<^verbatim>\<open>_Thread_Wait_flags_set\<close>
    \<^item> implemented in \<^verbatim>\<open>cpukit/include/rtems/score/threadimpl.h\<close>
  \<^item> calling \<^verbatim>\<open>_Thread_Wait_flags_try_change_acquire\<close>
    \<^item> implemented in \<^verbatim>\<open>cpukit/include/rtems/score/threadimpl.h\<close>
  \<^item> calling \<^verbatim>\<open>_Thread_Wait_flags_try_change_release\<close>
    \<^item> implemented in \<^verbatim>\<open>cpukit/include/rtems/score/threadimpl.h\<close>
  \<^item> calling \<^verbatim>\<open>_Thread_Wait_release_default\<close>
    \<^item> implemented in \<^verbatim>\<open>cpukit/include/rtems/score/threadimpl.h\<close>
\<close>

sectionX \<open>Future Work and Related Work\<close>

subsectionX \<open>\<close>

subsubsectionX \<open>\<close>

text' \<open>
To get the minimal list of imported files of a C file, one can start with an archive with its
default entries, and sequentially remove one-by-one each entry, while compiling the C file after the
removal. A failure indicates that the removed entry is a required dependency.
\<close>

subsectionX \<open>\<close>

subsubsectionX \<open>\<close>

text' \<open>
Analyzing on the preprocessed code:
\<^item> if 1.c is including 2.h and 3.h, are there any portions of 2.h (respectively of 3.h, or any other header files) included at least twice?
\<^item> for all i.h; and all portions Ci1, Ci2 in i.h; is the position of Ci1 < the position of Ci2 (where position means the position referenced in the preprocessed file)?
\<^item> for all i.h; and all Ci1 in i.h; is the function in Ci1 ever used, or is it a ghost code?
\<close>

text' \<open>
Printing:
\<^item> absence of generated type in PML
\<close>

text' \<open>
Feature:
\<^item> include file
\<^item> skipping consecutive files
\<^item> tracking position with suitable editor
\<close>

text' \<open>
\begin{gather*}
  \begin{tabular}{c|c}
    $\text{C}^\text{PP}\text{99}_\text{\<^emph>\<open>annot\<close>11+CIL}^\text{ANSI}$ & $\text{PML}^\text{PP}\text{99}_\text{\<^emph>\<open>annot\<close>11+CIL}^\text{ANSI}$ \\
    $\downarrow$ & $\downarrow$ \\
    $\text{C}^\text{PP+TREE}\text{99}_\text{\<^emph>\<open>annot\<close>11+CIL}^\text{ANSI}$ & $\text{PML}^\text{PP+TREE}\text{99}_\text{\<^emph>\<open>annot\<close>11+CIL}^\text{ANSI}$
  \end{tabular}
\end{gather*}
\<close>

subsubsectionX \<open>(Next Works) $\mathcal{C}_\text{like}\text{99}_\text{\<^emph>\<open>annot\<close>11+CIL}^\text{ANSI}$ \<open>\<rightarrow>\<close> $\mathcal{C}_\text{like}\text{99}_\text{\<^emph>\<open>annot\<close>11}^\text{CIL}$\<close>

text' \<open>
\<^bold>\<open>Re-enabling C CIL semantics\<close>
\<close>

text' \<open>
\begin{gather*}
  \begin{tabular}{c|c}
    $\text{C}\text{99}_\text{\<^emph>\<open>annot\<close>11+CIL}^\text{ANSI}$ & $\text{PML}\text{99}_\text{\<^emph>\<open>annot\<close>11+CIL}^\text{ANSI}$ \\
    $\downarrow$ & $\downarrow$ \\
    $\text{C}\text{99}_\text{\<^emph>\<open>annot\<close>11}^\text{CIL}$ & $\text{PML}\text{99}_\text{\<^emph>\<open>annot\<close>11}^\text{CIL}$
  \end{tabular}
\end{gather*}
\<close>

subsubsectionX \<open>(Next Works) $\mathcal{C}_\text{like}\text{99}_\text{\<^emph>\<open>annot\<close>11}$ \<open>\<rightarrow>\<close> $\mathcal{C}_\text{like}\text{11}$\<close>

text' \<open>
\<^bold>\<open>Re-enabling C11 semantics\<close>
\<close>

text' \<open>
\begin{gather*}
  \begin{tabular}{c|c}
    $\text{C99}_\text{\<^emph>\<open>annot\<close>11}$ & $\text{PML99}_\text{\<^emph>\<open>annot\<close>11}$ \\
    $\downarrow$ & $\downarrow$ \\
    C11 & PML11
  \end{tabular}
\end{gather*}
\<close>

subsubsectionX \<open>(Next Works) $\text{C}^\text{TREE}\text{11}$ $\leftrightarrow$ $\text{PML}^\text{TREE}\text{11}$\<close>

text' \<open>
\<^bold>\<open>Model-Checking Phase\<close>
\<close>

text' \<open>
\<close>

subsubsectionX \<open>(Related Works) C11 \<open>\<rightarrow>\<close> LLVM\<close>

text' \<open>
\<^bold>\<open>Compatibility study with the C versions accepted by model-checking tools\<close>
\<close>

text' \<open>
\<^item> CDSchecker @{cite "DBLP:conf/oopsla/NorrisD13" and "DBLP:journals/toplas/NorrisD16"}
\<^item> Nidhugg @{cite "DBLP:conf/tacas/AbdullaAAJLS15" and "DBLP:journals/acta/AbdullaAAJLS17"}
\<^item> Genmc \<^url>\<open>http://plv.mpi-sws.org/genmc/\<close> @{cite "DBLP:conf/pldi/LahavVKHD17"} @{cite "DBLP:conf/popl/KangHLVD17"} @{cite "DBLP:journals/pacmpl/Kokologiannakis18"} @{cite "DBLP:journals/pacmpl/PodkopaevLV19"} @{cite "DBLP:conf/asplos/Kokologiannakis20"} @{cite "DBLP:conf/oopsla/BlumG16"}
\<^item> Cerberus @{cite "DBLP:conf/esop/BattyMNPS15"} @{cite "DBLP:conf/pldi/MemarianMLNCWS16"} @{cite "DBLP:conf/oopsla/NienhuisMS16"} @{cite "DBLP:conf/cav/LauGMPS19"}
\<^item> Misc., semantics, PhD thesis @{cite "DBLP:phd/ethos/Batty15"} @{cite "DBLP:phd/hal/Morisset17"}
\<close>

subsubsectionX \<open>(Related Works) {\LaTeX} \<open>\<rightarrow>\<close> RST\<close>

text' \<open>
\<^bold>\<open>\<close>
\<close>

text' \<open>
\<close>

(*<*)
rst_export_file

end
(*>*)
