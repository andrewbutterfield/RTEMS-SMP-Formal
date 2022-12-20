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
theory autoevent
  imports Isabelle_Doc_reStructuredText.reStructuredText_Wrapper
begin

declare [[reStructuredText]]
declare [[rst_file_symbol = false]]

comment \<open>
SPDX-License-Identifier: CC-BY-SA-4.0 OR BSD-2-Clause

Copyright (C) 2019-2021 Trinity College Dublin (www.tcd.ie)
\<close>

(*>*)

sectionX \<open>Automatic Approach: Modelling of the Event Manager in Promela\<close>

subsectionX \<open>Overview\<close>

text' \<open>
In this section, we provide a model of the Event Manager.
This model has the characteristic of being
as close as possible to the real C11 code.
It is not derived from the human readable documents
accompanying the RTEMS source,
rather it is derived based on the understanding
that one might possibly have of the code.
\<close>

text' \<open>
Our version of the Event Manager is situated in
\<^dir>\<open>FV2-201_models/events/src\<close> (where
\<^dir>\<open>FV2-201_models\<close> is the abbreviation we give to the first
directory of the git repository having \<open>models\<close> as name, and
\<^dir>\<open>FV2-201_models/events\<close> is abbreviated as
\<^dir>\<open>models_events\<close>), and particularly in
\<^file>\<open>models_events/src/cpukit.pml\<close> containing the core
implementation in Promela (representing
\<^verbatim>\<open>cpukit/rtems/src/eventsurrender.c\<close> and
\<^verbatim>\<open>cpukit/rtems/src/eventseize.c\<close>). The directory
includes several examples:

\<^item> \<^file>\<open>models_events/src/testsuites1.pml\<close> covers random
  cases of sending and receiving actions of events. Situations of deadlocks are
  allowed and can occur for instance when a receiving action remains blocked
  without a corresponding send action that can satisfy it.

\<^item> \<^file>\<open>models_events/src/testsuites2.pml\<close> is similar to
  \<^file>\<open>models_events/src/testsuites1.pml\<close> but
  any receiving actions are guaranteed to be ultimately not pending.
  After a number of iteration steps (either a send or receive action),
  we analyze if there is any receive actions not fulfilled.
  If this is the case, \<^file>\<open>models_events/src/testsuites2.pml\<close>
  triggers the appropriate send actions to force the resuming of blocked
  processes. Additionally, in contrast to the
  \<^file>\<open>models_events/src/testsuites1.pml\<close> example, this model
  is proved to be always correctly terminating by the model-checker.
\<close>

text' \<open>
Inside the directory, one can also find the three instancing examples of
\<^verbatim>\<open>testsuites/sptests/spintrcritical10/init.c\<close> now
independently split and respectively modelled in three different files:
\<^item> \<^file>\<open>models_events/src/testsuites_spintrcritical10_1.pml\<close>
\<^item> \<^file>\<open>models_events/src/testsuites_spintrcritical10_2.pml\<close>
\<^item> \<^file>\<open>models_events/src/testsuites_spintrcritical10_3.pml\<close>
\<close>

text' \<open>
After executing the following script (linebreaks added here for clarity),
\<^descr> \<^file>\<open>FV2-201_src/Promela_to_C/src/testgen_ml_spin.sh\<close>
  \<^descr> \<^file>\<open>models_events/src/testsuites_spintrcritical10_1.pml\<close>
  \<^descr> \<^file>\<open>models_events/src/testsuites_spintrcritical10_1.rfn\<close>
  \<^descr> \<^verbatim>\<open>--promela "$(cat\<close> \<^file>\<open>models_events/src/testsuites.cfg\<close> \<^verbatim>\<open>)"\<close>
\<close>

text' \<open>
in some directory
(where \<^dir>\<open>FV2-201_src\<close> is the abbreviation we give to the
first directory of the git repository having \<open>src\<close> as name),
a new folder, simply called \<^verbatim>\<open>_\<close>,
gets generated containing, among other things,
our C output file of interest
(that folder location had been specified
in \<^file>\<open>models_events/src/testsuites.cfg\<close>).

For convenience, we manually provide,
in \<^dir>\<open>models_events/generated\<close>,
the output folder \<^verbatim>\<open>_\<close> of what would have been generated by the above script,
so that one can inspect it without the need to run the script.

This gives us, for example, our desired C test file
\<^file>\<open>models_events/generated/src/testsuites_spintrcritical10_1.auto_output/ltl_termination/init.c\<close>.
Recall that part of that file is precisely dependent on the content of our provided refinement file
\<^file>\<open>models_events/src/testsuites_spintrcritical10_1.rfn\<close>.

To run this \<^verbatim>\<open>init.c\<close> file with the correct compilation options,
one can take advantage of the build program \<^verbatim>\<open>waf\<close>,
provided in RTEMS 6.
For
example, we can manually overwrite any \<^verbatim>\<open>init.c\<close> in the
\<^verbatim>\<open>testsuites\<close> directory (chosen randomly), such as this one:
\<^verbatim>\<open>testsuites/sptests/spintrcritical10/init.c\<close>.

On a machine having \<^verbatim>\<open>$HOME/tmp/rsb/6/bin\<close> as directory set up by
``rtems-source-builder'' (\<^url>\<open>https://git.rtems.org/rtems-source-builder\<close>), it
becomes then straightforward to run the \<^verbatim>\<open>sparc-rtems6-sis\<close> simulator using:
\<^item> \<^verbatim>\<open>export PATH=$HOME/tmp/rsb/6/bin:"$PATH"\<close>
\<^item> \<^verbatim>\<open>./waf -v\<close>
\<^item> \<^verbatim>\<open>sparc-rtems6-sis -leon3 -r build/sparc/leon3/testsuites/sptests/spintrcritical10.exe\<close>
\<close>

subsectionX \<open>Architecture Model\<close>

text' \<open>
Our implementation of send and receive in \<^file>\<open>models_events/src/cpukit.pml\<close>
is pretty close to the C RTEMS source:
we only have two Promela proctypes \<^verbatim>\<open>event_surrender_exec\<close> (representing send)
and \<^verbatim>\<open>event_seize_exec\<close> (representing receive)
that might be asynchronously launched at any time.
However, the main starting points for end-users
are respectively located in \<^verbatim>\<open>event_surrender_send\<close> and \<^verbatim>\<open>event_seize_receive\<close>.

Technically,
our implementation model can even be slightly more general
than the C implementation in RTEMS.
For instance, our \<^verbatim>\<open>event_surrender_send\<close> can take
two process identifiers for the origin thread and destination thread,
whereas in the C implementation,
a sending action is assumed to originate from a ``self'' thread.

The C implementation is highly concurrent:
a send can happen at the same time than a receive.
This makes our test generation to be slightly different
than what we modelled for the scheduler.
Indeed, our auto approach expects to associate
exactly one printf statement with only one proctype.
However here,
it would be possible to have several atomic blocks inside one proctype.
In the end,
while running our auto approach,
we would be not able to do a fine-grain identification of
which atomics inside a particular proctype are produced in the trail trace,
unless we change and adapt the C source so that
we have at most one C function executing an atomic action in Promela.
This is something we have not
performed; and especially the reason why we inserted a new option
\<^verbatim>\<open>no_atomic\<close> in
\<^file>\<open>models_events/src/testsuites_spintrcritical10_1.rfn\<close> to disable the generation
of any atomic statements.
\<close>

(*<*)
rst_export_file

end
(*>*)
