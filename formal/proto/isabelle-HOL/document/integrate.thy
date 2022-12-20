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
theory integrate
  imports Isabelle_Doc_reStructuredText.reStructuredText_Wrapper
begin

declare [[reStructuredText]]
declare [[rst_file_symbol = false]]

comment \<open>
SPDX-License-Identifier: CC-BY-SA-4.0 OR BSD-2-Clause

Copyright (C) 2019-2021 Trinity College Dublin (www.tcd.ie)
\<close>

(*>*)

sectionX \<open>Qualification tool-chain integration\<close>

text' \<open>
Our initial approach towards integration to the qualification tool-chain
(\<^url>\<open>https://gitrepos.estec.esa.int/external/rtems-smp-qualification-qual\<close>)
has been to analyse the current build architecture in place,
and replicate its structure for our test generation tools (both the manual and auto approaches).
This also included a check to ensure that any static analyzing tools
that have been initially setup in the tool-chain repository
can still be successfully applied to our own tools.

For the part that is closest to our interest,
the qualification tool-chain repository can at the
same time be approximated as a project deriving C test code from YAML specifications.
Even if from a single YAML specification file,
one can actually generate \<^emph>\<open>several\<close> C test scenarios.
The test generation approach of the qualification repository is fundamentally not very
different from our manual and auto approaches presented in this document.
Indeed,
instead of generating a C test file,
the data captured in our refinement files is generic enough for it to be instrumented,
so that we would get in return generated YAML files instead of C files.
The remaining work is similar to what we described in the previous sections:
however instead of manipulating C files at a low-level,
we would directly invoke their generation
from the qualification repository higher-level,
for them to be generated to the appropriate place.
At the time of writing one has to manually move the newly generated YAML specifications.
\<close>

subsectionX \<open>Structure of the Source\<close>

text' \<open>
The integration of our test generation code inside the
\<^verbatim>\<open>rtems-smp-qualification-qual\<close> repository is facilitated by the fact that
both programs are basically Python code:
e.g. both programs can directly take advantage
of any existing Python-build infrastructure,
or static analysing tools developed for Python.
However, parts of our test generation tools are first pre-processed with Coconut,
which gives rise to several implications that will be pointed out below.

Overall, the source is situated in \<^dir>\<open>FV2-201_src/Promela_to_C\<close> which will be
abbreviated as \<^dir>\<open>Promela_to_C\<close>.
Note that,
even if we can generate meta YAML files,
by abuse of language and simplicity,
our tool transformation can be mainly viewed as a
translation process going from Promela to C.
\<close>

text' \<open>
\<^dir>\<open>Promela_to_C/src\<close> is the main folder of the project, and the core
implementation is in \<^dir>\<open>Promela_to_C/src/src\<close>. The structure of
\<^dir>\<open>Promela_to_C/src\<close> is closely identical to
\<^verbatim>\<open>rtems-smp-qualification-qual\<close>, with only minor deviations. For example,
for direct dependency-reasons certain external libraries are provided in
\<^dir>\<open>Promela_to_C/src/src/modules\<close> and contains only Python source, whereas in
\<^verbatim>\<open>rtems-smp-qualification-qual\<close>, the \<^verbatim>\<open>modules\<close>
folder appears at an upper-level and is not necessarily related to Python source. Otherwise,
\<^dir>\<open>Promela_to_C/src/src\<close> can be seen as the folder analogous to
\<^verbatim>\<open>rtems-smp-qualification-qual/rtemsspec\<close>.
\<close>

subsectionX \<open>Static Analysing Tools for Python/Coconut\<close>

text' \<open>
The overall source is written in Python/Coconut,
where Coconut can be thought of as a pure macro-language for Python
(in the same spirit as taking advantage of macros in C directives, which
are pre-processed before compilation).
As one can obtain an ultimate Python source by expanding any occurring Coconut-macros,
this can accelerate the development for developers interested to quickly
express complex Python constructs with minimal lines of code (in Coconut).
For example,
we often used Coconut's pattern matching
that gets rewritten into equivalent Python code.
The generated Python code has the advantage
of carrying additional checks on types of variables being matched,
that are automatically inserted by Coconut.
In certain situations,
this might save up to a 1/2 ratio of lines of code.
Still, it is not mandatory to use Coconut-macros in a Coconut source: in this
case, the Coconut source would become de-facto accepted by regular Python compilers and usual static
analyses tools.\<^footnote>\<open>Historically, the project started to be written in Python/Coconut
because the use of Coconut-macros,
seen as an extended-superset of Python,
allowed the initial developers with no prior knowledge of Python
to be smoothly introduced to the language.
Since they were actually already familiar with most semantic aspects
of the Python language
(e.g. particularly on object-oriented programming, dynamic typing),
the task principally remained for them to assimilate Python/Coconut's syntax,
with the benefit of the possibility of falling back to
Coconut-constructs whenever ideas were to be quickly prototyped.\<close>

Overall, the generated Python gets executed as usual:
by dynamically loading any relevant Python/Coconut libraries at run-time.
However, one can get a fully-``statically'' typed effect on
the code by ensuring to always first execute a 100\<open>%\<close>-covering check on the code,
namely before executing the code for ``real'' purposes (at a second run-time).
This part dedicated to test that the source is fully covered with consistent types
can be automated,
through a methodological use of the
accompanying \<^file>\<open>Promela_to_C/src/Makefile\<close> (see
the
different rules to trigger the coverage check).
We particularly recommend to always manually execute
the 100\<open>%\<close>-coverage check as part of the ``static compilation'' process before any
``real'' execution, i.e. once the source has been changed.

Note that the first coverage check has nothing to do with code correctness:
in this stage,
we are only forcing the Python interpreter to behave as a static type checker
by a first attempt to execute arbitrary code,
which is one way to trigger its dynamic check of types.
There might be several limitations though, e.g. intrinsic to serializations
or in case one is using ``reflections'' at run-time,
however this looks similar as making heavy use of marshalling,
even in domain-languages with compilers performing static type-checking.
Nevertheless in our case,
it has experimentally appeared enough to apply our tested Python functions with arbitrary values,
while we made sure that any tested function did not produce irremediable side-effects
(at least during the first coverage test phase).

All in all,
the methodological process employed here is exactly following those in
\<^verbatim>\<open>rtems-smp-qualification-qual\<close>.
However,
we have disabled the analysing tools \<^verbatim>\<open>flake8\<close> and \<^verbatim>\<open>pylint\<close>, since more work on
the own Coconut compiler would be needed to make its generated constructs conform to the above
tools. At the time of writing, the use of \<^verbatim>\<open>mypy\<close> has been skipped as well
for related reasons.
\<close>

subsectionX \<open>Unifying the Manual and Auto Approaches\<close>

text' \<open>
The terms ``manual'' and ``auto'' used here originally refer to the
process by which
\<^item> annotations are added to Promela models, and
\<^item> selected assertions or LTL properties are negated.
\<close>

text' \<open>
A tool unifying the manual and auto approaches would ideally let the
user decide to execute any combination of tasks that may be found as
implemented in the manual and auto tools. Since
\<^emph>\<open>the negation of assertions and LTL properties\<close>
is a functionality specifically provided by the auto tool, and not
implemented in the manual approach, it is enough to directly take that
functionality and include it into the final unifying tool.

On the other hand, there is a distinction in the way 
\<^emph>\<open>annotations are added to Promela models\<close> for
these two approaches, regarding how refinement is done. It turns out
that the two refinement approaches are different but complementary,
and so we will be keep the two refinement approaches in our final
unifying tool.

The approach to refinement taken by the manual tool is referred to as
``generic'': annotations can be provided anywhere, using a relatively
rich and declarative language. Their executions are specified in
arbitrary state-rich Python code. Because such code generally has the
potential of manipulating and modifying internal states as
side-effects, the evaluation of annotations might be constrain to
follow a precise sequential order. This would ultimately depend on the
internal implementation of each annotation (the subset of
generic-annotations also includes ``purely computational''
annotations, e.g., without side-effects).

The approach to refinement taken by the automatic tool is referred to
as ``uniform'': annotations are automatically generated and can be
placed and associated to any named Promela constructs
(\<^verbatim>\<open>init\<close>, \<^verbatim>\<open>proctype\<close>
or \<^verbatim>\<open>inline\<close> declarations). Since these are
always just a record of values that get stored once in a global
context, the evaluation order of all uniform-annotations becomes
irrelevant: any two non-overlapping uniform-annotations can always be
evaluated in parallel. The refinement code has a fixed standard form:
it ranges from purely declarative data (such as YAML) to state-rich
general code (such as C). In addition, it is possible to insert
special C-like antiquoting directives in the code, that get
automatically expanded to C directives.

In terms of completeness, the two approaches are complementary: one
approach has always been experimentally able to mimic the other, and
produce an exact same C test file. For example, the serialization of
``dynamic'' Promela data-structures (such as dynamic arrays of unknown
length) is more natural to express in the generic-refinement approach,
although we can also implement an alternative serialization procedure
in the uniform-refinement approach.
\<close>

text' \<open>
Summing up, the unification of the manual and auto implementation has
been performed by essentially integrating the generic refinement
procedure into the existing codebase of auto, which already contained
the uniform version. The manual approach is still present and provided
in the source for inspection, so we have two entry-points:
\<^item> Manual-only approach with generic refinement:
\<^file>\<open>Promela_to_C/src/spin2test.sh\<close>
\<^item> Unified approach with both generic and uniform refinement:
\<^file>\<open>Promela_to_C/src/testgen_ml.sh\<close>
\<close>

text' \<open>
They are respectively calling \<^file>\<open>Promela_to_C/src/spin2test.coco\<close> and
\<^file>\<open>Promela_to_C/src/testgen_ml.coco\<close>. More deeply, these two files are just parsing
command lines: the two are internally invoking
\<^file>\<open>Promela_to_C/src/src/spin2test.coco\<close> and
\<^file>\<open>Promela_to_C/src/src/testgen.coco\<close>; with
\<^dir>\<open>Promela_to_C/src/src\<close> holding our whole implementation for the test generation.

Symmetrically, the coverage of files in this folder is particularly tested in
\<^dir>\<open>Promela_to_C/src/src/tests\<close>, with
\<^file>\<open>Promela_to_C/src/src/tests/test_coverage_spin2test.coco\<close> and
\<^file>\<open>Promela_to_C/src/src/tests/test_coverage_testgen.coco\<close> performing the
respective coverage.\<^footnote>\<open>Since parameters of all functions have to be provided for a
``ground'' test to occur, the two files \<^file>\<open>Promela_to_C/src/spin2test.coco\<close> and
\<^file>\<open>Promela_to_C/src/testgen_ml.coco\<close> can not be tested. In contrast, all functions
in \<^file>\<open>Promela_to_C/src/src/spin2test.coco\<close> and
\<^file>\<open>Promela_to_C/src/src/testgen.coco\<close> can be and have been fully tested.\<close>
\<close>

text' \<open>
The internal dependency structure of \<^file>\<open>Promela_to_C/src/src/spin2test.coco\<close> is
trivial: this file is only depending on
\<^file>\<open>Promela_to_C/src/src/refine_command.coco\<close> containing the implementation of
refinement commands for the \<^verbatim>\<open>refine_generic\<close> approach, which are described
in more details in some internal technical documentation accompanying the code.
\<close>

text' \<open>
On the other hand, the structure of \<^file>\<open>Promela_to_C/src/src/testgen.coco\<close> is
pretty involved:
\<^item> besides containing \<^file>\<open>Promela_to_C/src/src/refine_command.coco\<close>, i.e.
that same file used in \<^file>\<open>Promela_to_C/src/src/spin2test.coco\<close>,
\<^item> one can find \<^file>\<open>Promela_to_C/src/src/library.coco\<close> some general-purpose
library,
\<^item> as well as \<^file>\<open>Promela_to_C/src/src/syntax_pml.coco\<close> a module handling
the filtering of annotation comments in a C-like file
(Promela syntax is supported since the module
does not deeply analyse the content of code, but only comment delimiters),
\<^item> \<^file>\<open>Promela_to_C/src/src/syntax_ml.coco\<close> and
\<^file>\<open>Promela_to_C/src/src/syntax_yaml.coco\<close> correspond to two interchangeably
equivalent libraries parsing annotation commands.
\<^item> Finally \<^file>\<open>Promela_to_C/src/src/testgen.coco\<close> drives the main program to
perform the test generation execution. This is also where \<^verbatim>\<open>refine_uniform\<close>
gets implemented (but not exclusively as one can choose to trigger there either the
\<^verbatim>\<open>refine_generic\<close> and/or the \<^verbatim>\<open>refine_uniform\<close>
approach;
see some internal technical documentation accompanying the code for further comparisons on
the two approaches).
\<close>

text' \<open>
Putting it all together,
recall that \<^file>\<open>Promela_to_C/src/spin2test.sh\<close> and
\<^file>\<open>Promela_to_C/src/testgen_ml.sh\<close> are the two entry-points of our tool.
They do not assume anything about the versions of Python-libraries installed in the machine.
A virtual Python environment is always started by default (or created),
and any needed libraries installed with the precise versions following those described in
\<^file>\<open>Promela_to_C/src/requirements.txt\<close> (similarly as what is done in
\<^verbatim>\<open>rtems-smp-qualification-qual\<close>).
Note that even if one has already installed
the required libraries in the immediate environment where the script is called,
then the script will isolate itself inside an additional virtual environment,
and it might install again the exact same libraries inside this virtual environment.
However,
a next execution of the script will see that
the previous execution would have already installed the necessary packages,
so the virtual environment will be left unmodified.\<^footnote>\<open>To display the directory where libraries are installed,
one can execute:
``\<^verbatim>\<open>pip3 show promela | grep Location | cut -d ':' -f 2-\<close>''.\<close>
\<close>
(*
text' \<open>
Due to the fact that \<^file>\<open>Promela_to_C/src/testgen_ml.sh\<close> is pretty generic, and first
expects to receive as parameter an instantiated model-checker to drive the test generation, we
provide \<^file>\<open>Promela_to_C/src/testgen_ml_spin.sh\<close> a higher entry point invocation of
the tool, intended for end-users interested to directly use
\<^file>\<open>Promela_to_C/src/testgen_ml.sh\<close> with \<^verbatim>\<open>spin\<close> used as
default model-checker. (It is straightforward to copy the previous shell-script and repeat the same
invocation process to call instead another model-checker of interests.)
\<close>

text' \<open>
Note that \<^dir>\<open>Promela_to_C/src/src/modules\<close> is the placeholder for libraries that
we manually modify, and thus the versions of those present there have never been packaged by
\<^verbatim>\<open>pip3\<close> (even if probable anterior versions of respective libraries might
exist in the \<^verbatim>\<open>pip3\<close> database).
\<close>
*)
(*<*)
rst_export_file

end
(*>*)
