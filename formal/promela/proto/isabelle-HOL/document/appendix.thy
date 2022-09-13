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
theory appendix
  imports Isabelle_Doc_reStructuredText.reStructuredText_Wrapper
begin

declare [[reStructuredText]]
declare [[rst_file_symbol = false]]

comment \<open>
SPDX-License-Identifier: CC-BY-SA-4.0 OR BSD-2-Clause

Copyright (C) 2019-2021 Trinity College Dublin (www.tcd.ie)
\<close>

(*>*)

sectionX \<open>APPENDIX\<close>

subsectionX \<open>Automatic Extraction of Promela Models from C11 Code\<close>

text' \<open>
The automatic generation of C tests from Promela models assumed that we were
starting from a state where we already conveniently got a Promela model at our
disposal. Instead of writing this model by hand though, we are now interested
to generate models from RTEMS source, so that one could rely on an automated
mechanism to:
\<^item> get a high level of trusted computing base that the model we are
relying on is formally close to the initial C code in input it is expecting to
model,
\<^item> and generically have a way to apply the extraction process on the
different relevant piece of RTEMS code; for instance the Scheduler or the Event
Manager. This would also lower the maintenance effort on adapting any future
change of the original C code to model.
\<close>

text' \<open>
Here we describe experiments done to help with analysing RTEMS C code, and
particularly first focus on the RTEMS SMP scheduler as a case study.

As general picture,
we plan to apply the SPIN model-extractor tool Modex,
on the relevant C source of RTEMS dealing with the scheduler,
to get a Promela model.
The plan is to get initial Promela models that
match the code closely,
which we can then simplify and abstract in order to make analysis
easier.
These models will then be used, to generate tests for RTEMS,
as described previously.

With a closer look at the Scheduler source,
we notice it is using several features of C11
that can not be syntactically expressed in C99.
Also the overall Scheduler source is fairly large,
written in about 70k lines of code.
In particular,
a raw construction of a Promela model from the Scheduler source with
Modex would be not immediately possible,
because Modex can only accept code written in a subset of C99.

Model-checkers are only able to practically treat models
up to a certain size (or associated number of automaton states).
We will not treat the Scheduler source as a single file,
but will mostly attempt to preserve its original folder structure,
as it is currently found in the RTEMS source.
This would permit us to quickly isolate those
parts of the C source on which we should focus.

In this way,
we will be able to delimit which sections of the Scheduler
could be left behind an abstract black-box API,
from those sections of real interest.
Ideally,
for each C file in the tree hierarchy of the RTEMS project at position
\<^verbatim>\<open>dir1/dir2/dir3/file1.c\<close>,
we would wish to obtain an exact Promela model
situated at \<^verbatim>\<open>dir1/dir2/dir3/file1.pml\<close>.
However,
all the C files in the RTEMS project must first be preprocessed
before one can apply Modex,
as Modex requires a closed ground source as input.
This causes the first problem
since the C preprocessing phase is concatenating
all relevant C files into a single one.
Indeed,
applying Modex is not enough,
as we also have to implement an inversion process
to reconstitute back the initial tree hierarchy
from the preprocessed C file.
Additionally,
since Modex is basically also returning a single Promela file,
the same inversion process has to be applied on that Promela file.

Before going into  deeper detail of
how the preprocessing and tree reconstitution process functions,
we present what we obtain as result in output.

\<^item> The full Scheduler source is automatically imported by \<^verbatim>\<open>gcc\<close>
  (in the preprocessing phase)
  by following the \<^verbatim>\<open>#include\<close>-dependencies of
  \<^url>\<open>https://gitrepos.estec.esa.int/external/rtems-smp-qualification-rtems/-/blob/master/testsuites/smptests/smpmrsp01/init.c\<close>.

  In particular,
  the preprocessing result of \<^verbatim>\<open>gcc\<close>
  has been automatically arranged by our tool to be placed inside the directory
  \<^dir>\<open>FV2-201_models/semaphore_manager/generated/smpmrsp01/raw/0_smpmrsp01/c\<close>,
  abbreviated as \<^dir>\<open>smpmrsp01_raw_c\<close>,
  which contains:
  \<^descr> @{dir [path_last_level = 1] \<open>smpmrsp01_raw_c/rsb\<close>}
    a folder replicating the structure of
    \<^url>\<open>https://git.rtems.org/rtems-source-builder\<close>.
    In particular,
    @{dir [path_root_prefix = false, path_last_level = 5] \<open>smpmrsp01_raw_c/rsb/rtems/tmp/rtems/6\<close>} corresponds to the path set to contain
    all the binaries installed by the \<^verbatim>\<open>rtems-source-builder\<close> project,
    during its regular build invocation process.
  \<^descr> @{dir [path_last_level = 1] \<open>smpmrsp01_raw_c/rtems\<close>}
    a folder replicating the structure of
    \<^url>\<open>https://gitrepos.estec.esa.int/external/rtems-smp-qualification-rtems/-/tree/master/\<close>.

\<^item> Symmetrically,
  the full model of the Scheduler as generated by Modex
  (and post-treatment with our tools) is placed in
  \<^dir>\<open>FV2-201_models/semaphore_manager/generated/smpmrsp01/raw/0_smpmrsp01/pml\<close>
  (abbreviated as \<^dir>\<open>smpmrsp01_raw_pml\<close>).
  All files in this folder are Promela files,
  however their extensions do not finish with \<^verbatim>\<open>.pml\<close>,
  as instead,
  a \<^verbatim>\<open>.c\<close> or \<^verbatim>\<open>.h\<close> is used according to
  the extension of the original C file that this Promela model
  is expected to represent.
  For example, the Promela file
  \<^file>\<open>smpmrsp01_raw_pml/rtems/testsuites/smptests/smpmrsp01/init.c\<close>
  is the model representing the C file
  \<^file>\<open>smpmrsp01_raw_c/rtems/testsuites/smptests/smpmrsp01/init.c\<close>.
  We have explicitly kept all
  \<^verbatim>\<open>.c\<close> or \<^verbatim>\<open>.h\<close> extensions so that one can recursively apply
  graphical-difference-analysing tools to compare \<^dir>\<open>smpmrsp01_raw_c\<close> and \<^dir>\<open>smpmrsp01_raw_pml\<close>,
  such as \<^verbatim>\<open>meld\<close>\<^footnote>\<open>\<^url>\<open>https://packages.debian.org/buster/meld\<close>\<close> for example.
\<close>

text'\<open>
We now turn to the process generating \<^dir>\<open>smpmrsp01_raw_c\<close> and \<^dir>\<open>smpmrsp01_raw_pml\<close>.
In a nutshell, this involves the following conversion steps,
which are respectively described in the following sections:
\<^item> C11 \<open>\<rightarrow>\<close> $\text{C}^\text{PP}\text{11}$
\<^item> $\text{C}^\text{PP}\text{11}$ \<open>\<rightarrow>\<close> $\text{C}^\text{PP}\text{99}_\text{\<^emph>\<open>annot\<close>11}$
\<^item> $\text{C}^\text{PP}\text{99}_\text{\<^emph>\<open>annot\<close>11}$ \<open>\<rightarrow>\<close> $\text{C}^\text{PP}\text{99}_\text{\<^emph>\<open>annot\<close>11}^\text{CIL}$
\<^item> $\text{C}^\text{PP}\text{99}_\text{\<^emph>\<open>annot\<close>11}^\text{CIL}$ \<open>\<rightarrow>\<close> $\text{C}^\text{PP}\text{99}_\text{\<^emph>\<open>annot\<close>11+CIL}^\text{ANSI}$
\<^item> $\text{C}^\text{PP}\text{99}_\text{\<^emph>\<open>annot\<close>11+CIL}^\text{ANSI}$ \<open>\<rightarrow>\<close> $\text{PML}^\text{PP}\text{99}_\text{\<^emph>\<open>annot\<close>11+CIL}^\text{ANSI}$
\<^item> $\mathcal{C}_\text{like}\text{99/11/18}^\text{PP}$ \<open>\<rightarrow>\<close> $\mathcal{C}_\text{like}\text{99/11/18}^\text{PP+TREE}$:

  The last two
  $\text{C}^\text{PP}\text{99}_\text{\<^emph>\<open>annot\<close>11+CIL}^\text{ANSI}$ and
  $\text{PML}^\text{PP}\text{99}_\text{\<^emph>\<open>annot\<close>11+CIL}^\text{ANSI}$ respectively
  represent \<^dir>\<open>smpmrsp01_raw_c\<close> and \<^dir>\<open>smpmrsp01_raw_pml\<close>,
  but as a single \<^verbatim>\<open>.c\<close> file and \<^verbatim>\<open>.pml\<close> file.
  To additionally obtain a tree structure,
  we apply the generic function
  $\mathcal{C}_\text{like}\text{99/11/18}^\text{PP}$ \<open>\<rightarrow>\<close> $\mathcal{C}_\text{like}\text{99/11/18}^\text{PP+TREE}$.
  This leads to
  $\text{C}^\text{PP+TREE}\text{99}_\text{\<^emph>\<open>annot\<close>11+CIL}^\text{ANSI}$ and
  $\text{PML}^\text{PP+TREE}\text{99}_\text{\<^emph>\<open>annot\<close>11+CIL}^\text{ANSI}$,
  now depicting \<^dir>\<open>smpmrsp01_raw_c\<close> and \<^dir>\<open>smpmrsp01_raw_pml\<close> in the two tree structures as found in
  \<^dir>\<open>FV2-201_models/semaphore_manager/generated/smpmrsp01/raw/0_smpmrsp01\<close>.
\<close>

text' \<open>
Note that the intermediate files are provided as http-links,
as they are only provided here to illustrate
the intermediate phase of the translation process
producing \<^dir>\<open>smpmrsp01_raw_c\<close> and \<^dir>\<open>smpmrsp01_raw_pml\<close>.
In contrast, the final folders
\<^dir>\<open>smpmrsp01_raw_c\<close> and \<^dir>\<open>smpmrsp01_raw_pml\<close> are explicitly kept and saved in the repository.
\<close>

subsubsectionX \<open>Conversion Step Details\<close>

paragraphX \<open>C11 \<open>\<rightarrow>\<close> $\text{C}^\text{PP}\text{11}$\<close>

text' \<open>
\<^bold>\<open>Setup of RTEMS and pre-processing the scheduler\<close>
\<close>

text' \<open>
From the output of ``\<^verbatim>\<open>./waf -v\<close>'',
one can list all commands that are executed to compile the source of RTEMS.
In particular,
since the entry point of interest initializing the scheduler is situated in:
\<^verbatim>\<open>testsuites/smptests/smpmrsp01/init.c\<close>,
it is straightforward to get the full list of options
given to \<^verbatim>\<open>sparc-rtems5-gcc\<close> to compile that file:
\<^verbatim>\<open>[\<close>\<^verbatim>\<open>'\<close>sparc-rtems5-gcc\<^verbatim>\<open>'\<close>, \<^verbatim>\<open>'\<close>-MMD\<^verbatim>\<open>'\<close>, \<^verbatim>\<open>'\<close>-Wall\<^verbatim>\<open>'\<close>, \<^verbatim>\<open>'\<close>-Wmissing-prototypes\<^verbatim>\<open>'\<close>, \<^verbatim>\<open>'\<close>-Wimplicit-function-declaration\<^verbatim>\<open>'\<close>, \<^verbatim>\<open>'\<close>-Wstrict-prototypes\<^verbatim>\<open>'\<close>, \<^verbatim>\<open>'\<close>-Wnested-externs\<^verbatim>\<open>'\<close>, \<^verbatim>\<open>'\<close>-O2\<^verbatim>\<open>'\<close>, \<^verbatim>\<open>'\<close>-g\<^verbatim>\<open>'\<close>, \<^verbatim>\<open>'\<close>-fdata-sections\<^verbatim>\<open>'\<close>, \<^verbatim>\<open>'\<close>-ffunction-sections\<^verbatim>\<open>'\<close>, \<^verbatim>\<open>'\<close>-mcpu=leon3\<^verbatim>\<open>'\<close>, \<^verbatim>\<open>'\<close>-Icpukit / include\<^verbatim>\<open>'\<close>, \<^verbatim>\<open>'\<close>-I.. / .. / .. / cpukit / include\<^verbatim>\<open>'\<close>, \<^verbatim>\<open>'\<close>-Icpukit / score / cpu / sparc / include\<^verbatim>\<open>'\<close>, \<^verbatim>\<open>'\<close>-I.. / .. / .. / cpukit / score / cpu / sparc / include\<^verbatim>\<open>'\<close>, \<^verbatim>\<open>'\<close>-Ibsps / include\<^verbatim>\<open>'\<close>, \<^verbatim>\<open>'\<close>-I.. / .. / .. / bsps / include\<^verbatim>\<open>'\<close>, \<^verbatim>\<open>'\<close>-Ibsps / sparc / include\<^verbatim>\<open>'\<close>, \<^verbatim>\<open>'\<close>-I.. / .. / .. / bsps / sparc / include\<^verbatim>\<open>'\<close>, \<^verbatim>\<open>'\<close>-Ibsps / sparc / leon3 / include\<^verbatim>\<open>'\<close>, \<^verbatim>\<open>'\<close>-I.. / .. / .. / bsps / sparc / leon3 / include\<^verbatim>\<open>'\<close>, \<^verbatim>\<open>'\<close>-Itestsuites / support / include\<^verbatim>\<open>'\<close>, \<^verbatim>\<open>'\<close>-I.. / .. / .. / testsuites / support / include\<^verbatim>\<open>'\<close>, \<^verbatim>\<open>'\<close>.. / .. / .. / testsuites / smptests / smpmrsp01 / init.c\<^verbatim>\<open>'\<close>, \<^verbatim>\<open>'\<close>-c\<^verbatim>\<open>'\<close>, \<^verbatim>\<open>'\<close>-ortems / build / sparc / leon3 / testsuites / smptests / smpmrsp01 / init.c.566.o\<^verbatim>\<open>'\<close>, \<^verbatim>\<open>'\<close>-DHAVE\_CONFIG\_H=1\<^verbatim>\<open>'\<close>\<^verbatim>\<open>]\<close>

However,
instead of creating an object file,
we can get a standalone pre-processed content,
by replacing
``-ortems / build / sparc / leon3 / testsuites / smptests / smpmrsp01 / init.c.566.o''
with ``-E'' (and optionally followed by ``-CC'' to keep comments).

This leads to the respective files:
\<^url>\<open>https://www.scss.tcd.ie/frederic.tuong/init.c_pp\<close>
and
\<^url>\<open>https://www.scss.tcd.ie/frederic.tuong/init.c_pp_CC\<close>.
\<close>

paragraphX \<open>$\text{C}^\text{PP}\text{11}$ \<open>\<rightarrow>\<close> $\text{C}^\text{PP}\text{99}_\text{\<^emph>\<open>annot\<close>11}$\<close>

text' \<open>
\<^bold>\<open>Downgrading the C11 subset for Modex, towards $\text{C99}^\text{CIL}$ and $\text{C99}^\text{ANSI}$\<close>
\<close>

text' \<open>
The pre-processed obtained output is a very condensed file:
composed of 69~kLoC (respectively 29~kLoC without comments),
e.g. compared to the 27~kLoC of seL4 source (by counting comments).

To get a Promela model,
one can try to apply Modex on the file.
However, we obtain several parsing errors:
the scheduler is implemented with several constructs
not present in the C99 subset handled by Modex.
Additionally, a quick check using parsers
focusing on handling C11 and C18 constructs
also reveals that it is accepted by the C11 parser we
used\<^footnote>\<open>\<^url>\<open>https://hackage.haskell.org/package/language-c\<close>\<close>,
but not with the C18 one we
used\<^footnote>\<open>\<^url>\<open>https://github.com/jhjourdan/C11parser\<close> (Note that
besides C11, the project also supports C18, irrespective of its repository name.)\<close>.

Noting what is said above,
there are two solutions:
taking advantage of an automated tool translating C11 to C99,
or modifying by hand any part of the code with C11 constructs
in order to temporarily disable them.
Although the automated approach is the one we opt for a long term solution,
one can actually also start by doing some statistics
to measure the size of unsupported C11 constructs embedded in the initial input.

At the same time,
one can also analyse the C99 parser used in Modex,
to estimate the subset of C99 programs that Modex is supporting
from the C99 standard.
We actually notice its parser seems at first sight to accept
less programs compared to other C99 parsers,
e.g. such as the C99 default parser of Frama-C.
Furthermore,
a quick inspection of its source code reveals
that Frama-C is using the CIL framework
as an intermediate translation compilation phase:
the CIL AST is a ``generic'' AST,
simpler than the initial C99 AST.
From the CIL framework,
it is also possible to serialize to string and get in return
a kind of ``simplified'' (subset) pre-processed C99 AST.
In particular,
we conjecture that the latter pre-processed C99
can be made acceptable to Modex
more easily than raw C99 code not pre-processed by CIL.

Consequently, from the initial C11 AST, we temporarily disable by hand all C11
constructs rejected by the Frama-C parser
(obviously changing at the same time the semantics of the scheduler).
We obtain:
\<^url>\<open>https://www.scss.tcd.ie/frederic.tuong/init.c_pp0\<close>.
\<close>

paragraphX \<open>$\text{C}^\text{PP}\text{99}_\text{\<^emph>\<open>annot\<close>11}$ \<open>\<rightarrow>\<close> $\text{C}^\text{PP}\text{99}_\text{\<^emph>\<open>annot\<close>11}^\text{CIL}$\<close>

text' \<open>
\<^bold>\<open>Preprocessing with the CIL framework (included in Frama-C)\<close>
\<close>

text' \<open>
From this file,
we apply the Frama-C parser to obtain a CIL representation.
The latter serialization results in: \<^url>\<open>https://www.scss.tcd.ie/frederic.tuong/init_out.c\<close>.
\<close>

paragraphX \<open>$\text{C}^\text{PP}\text{99}_\text{\<^emph>\<open>annot\<close>11}^\text{CIL}$ \<open>\<rightarrow>\<close> $\text{C}^\text{PP}\text{99}_\text{\<^emph>\<open>annot\<close>11+CIL}^\text{ANSI}$\<close>

text' \<open>
\<^bold>\<open>Downgrading the C99 subset for Modex\<close>
\<close>

text' \<open>
However, applying Modex on it is still not immediate,
so we pursue additional manual pre-processing to obtain:
\<^url>\<open>https://www.scss.tcd.ie/frederic.tuong/init_out.c0\<close>.
\<close>

paragraphX \<open>$\text{C}^\text{PP}\text{99}_\text{\<^emph>\<open>annot\<close>11+CIL}^\text{ANSI}$ \<open>\<rightarrow>\<close> $\text{PML}^\text{PP}\text{99}_\text{\<^emph>\<open>annot\<close>11+CIL}^\text{ANSI}$\<close>

text' \<open>
\<^bold>\<open>Modex execution\<close>
\<close>

text' \<open>
Ultimately,
applying Modex on the latter produces this Promela file:
\<^url>\<open>https://www.scss.tcd.ie/frederic.tuong/model\<close>.
However it is rejected by spin,
since this particular model-checking tool does not support
a file with ``too many channel types'':
\<^verbatim>\<open>spin: model:3846, Error: too many channel types\<close>.
\<close>

paragraphX \<open>$\mathcal{C}_\text{like}\text{99/11/18}^\text{PP}$ \<open>\<rightarrow>\<close> $\mathcal{C}_\text{like}\text{99/11/18}^\text{PP+TREE}$\<close>

text' \<open>
\<^bold>\<open>Splitting a single preprocessed file into the original source tree hierarchy\<close>
\<close>

text' \<open>
This generation step is performed in \<^dir>\<open>FV2-201_src/C_to_Promela/src/6_isabelle_c/src_split\<close>.
This uses Isabelle/HOL, and in particular, Isabelle/C,
an implementation of C semantics in Isabelle/HOL.
\<close>

subsubsectionX \<open>Implementation and Statistics of the Sub-Generators\<close>

text' \<open>
In this section, we show the implementation details of scripts and tools involved behind the
different generation tasks. This will actually only concern tasks that are not in the category of
heuristics, since these lasts mostly consist in producing their output by patching their input with
some predefined replacement texts --- even if, for the particular inputs we are currently
considering, all replacements can be made automated and captured with regular expression patterns.

For the tasks that are automated, we compile a summarizing benchmark showing the overall performance
of the tools for each respective task. Afterwards, we will analyze their minimal computing
resources, which may highly vary depending on the different tools used.

We recall below the tasks that we are mainly focusing on:
\<^item> C11 \<open>\<rightarrow>\<close> $\text{C}^\text{PP}\text{11}$
  \<^item> Type of automation: \textsc{complete} (specialized to a first init.c file to consider)
  \<^item> Location: \<^dir>\<open>FV2-201_src/C_to_Promela/src/1_gcc\<close>
  \<^item> Abbreviation: \texttt{gcc\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }}
\<^item> $\text{C}^\text{PP}\text{11}$ \<open>\<rightarrow>\<close> $\text{C}^\text{PP}\text{99}_\text{\<^emph>\<open>annot\<close>11}$
  \<^item> Type of automation: \textsc{heuristic} (not presented)
\<^item> $\text{C}^\text{PP}\text{99}_\text{\<^emph>\<open>annot\<close>11}$ \<open>\<rightarrow>\<close> $\text{C}^\text{PP}\text{99}_\text{\<^emph>\<open>annot\<close>11}^\text{CIL}$
  \<^item> Type of automation: \textsc{complete} (in conjunction with heuristics preliminarily applied)
  \<^item> Location: \<^dir>\<open>FV2-201_src/C_to_Promela/src/3_frama_c\<close>
  \<^item> Abbreviation: \texttt{frama\_c\phantom{ }\phantom{ }\phantom{ }}
\<^item> $\text{C}^\text{PP}\text{99}_\text{\<^emph>\<open>annot\<close>11}^\text{CIL}$ \<open>\<rightarrow>\<close> $\text{C}^\text{PP}\text{99}_\text{\<^emph>\<open>annot\<close>11+CIL}^\text{ANSI}$
  \<^item> Type of automation: \textsc{heuristic} (not presented)
\<^item> $\text{C}^\text{PP}\text{99}_\text{\<^emph>\<open>annot\<close>11+CIL}^\text{ANSI}$ \<open>\<rightarrow>\<close> $\text{PML}^\text{PP}\text{99}_\text{\<^emph>\<open>annot\<close>11+CIL}^\text{ANSI}$
  \<^item> Type of automation: \textsc{complete} (in conjunction with heuristics preliminarily applied)
  \<^item> Location: \<^dir>\<open>FV2-201_src/C_to_Promela/src/5_modex\<close>
  \<^item> Abbreviation: \texttt{modex\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }}
\<^item> $\mathcal{C}_\text{like}\text{99/11/18}^\text{PP}$ \<open>\<rightarrow>\<close> $\mathcal{C}_\text{like}\text{99/11/18}^\text{PP+TREE}$
  \<^item> Type of automation: \textsc{complete} (generic translation, semantics not analyzed)
  \<^item> Location: \<^dir>\<open>FV2-201_src/C_to_Promela/src/6_isabelle_c\<close>
  \<^item> Abbreviation: \texttt{isabelle\_c}
\<close>

text' \<open>

Even if each respective task is using as input the output result of the immediate previous task, we
will run all of them independently in parallel from a same starting environment. This is to see for
example which external packages are needed to be installed before running each tool. So it will
require us to first generate all necessary input files, and retrieve (e.g. download) the appropriate
input files at the beginning for each tool. In particular, we assume starting from a same new
Debian\<^footnote>\<open>Debian is the operating system that we primarily support in the
\<open>rtems-smp-qualification\<close> project.\<close> server (without any graphic supports)
version
\<open>4.19.0-9-amd64 #1 SMP Debian 4.19.118-2+deb10u1 (2020-06-07) x86_64 GNU/Linux\<close>,
installed using the minimal installation image
\<^url>\<open>https://cdimage.debian.org/debian-cd/current/amd64/iso-cd/debian-10.4.0-amd64-netinst.iso\<close>.

We also assume having at our disposal the packages \<^verbatim>\<open>sudo\<close> and
\<^verbatim>\<open>time\<close> already installed, as well as
\<^verbatim>\<open>build-essential\<close>, \<^verbatim>\<open>dkms\<close>,
\<^verbatim>\<open>linux-headers-4.19.0-9-amd64\<close>. Note that these last packages (or their
recursive dependent packages) might not be strictly needed by the tools. However, we explicitly
installed them for efficiency reasons: we are actually making the experiments inside a virtual
machine, which can take advantage of additional optimizations proper to the machine whenever these
packages are installed.

Last, our virtual machine has a base memory of 8~GiB, a substantially same amount of SWAP memory,
the possibility to concurrently use up to a fixed number of CPUs, and an initial free disk storage
of at least 30~GiB. During the experiments, an effort was made to allocate the approximate same
resources of the host machine to the guest machine while each task was running, especially the host
CPU power, the host memory space, and the host network bandwidth (e.g. which might constantly change
depending on the time of the day when the experiments are taken).
\<close>

(*
 (ease of installation)
Number of Debian packages additionally installed : + dependencies
(e.g. how to make the tool use less disk space, or compute faster number of core used)
*)

text' \<open>
\<^bold>\<open>Location of the main generator script for each task\<close>
\<close>

text' \<open>
\<^descr> \texttt{gcc\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }}

  \<^file>\<open>FV2-201_src/C_to_Promela/src/1_gcc/full.sh\<close>
\<^descr> \<^emph>\<open>(not presented)\<close>

  \<^file>\<open>FV2-201_src/C_to_Promela/src/2_downgrade_c11/core.sh\<close>
\<^descr> \texttt{frama\_c\phantom{ }\phantom{ }\phantom{ }}

  \<^file>\<open>FV2-201_src/C_to_Promela/src/3_frama_c/full.sh\<close>
\<^descr> \<^emph>\<open>(not presented)\<close>

  \<^file>\<open>FV2-201_src/C_to_Promela/src/4_downgrade_c99/core.sh\<close>
\<^descr> \texttt{modex\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }}

  \<^file>\<open>FV2-201_src/C_to_Promela/src/5_modex/full.sh\<close>
\<^descr> \texttt{isabelle\_c}

  \<^file>\<open>FV2-201_src/C_to_Promela/src/6_isabelle_c/full.sh\<close>
\<close>

paragraphX \<open>A Many-Core Setting with 6 CPUs\<close>

text' \<open>
\<^bold>\<open>Time: Elapsed wall clock\<close> ``minutes \<open>:\<close> seconds \<open>.\<close> and the first $10^{-2}$ digits''
\<close>

text' \<open>
\<^descr> \texttt{gcc\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }} 31:42.93
\<^descr> \texttt{frama\_c\phantom{ }\phantom{ }\phantom{ }} 06:51.21
\<^descr> \texttt{modex\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }} 00:23.96
\<^descr> \texttt{isabelle\_c} 03:03.10
\<close>

text' \<open>
\<^bold>\<open>Disk: Increment usage\<close>
\<close>

text' \<open>
\<^descr> \texttt{gcc\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }} 4,6~GiB
\<^descr> \texttt{frama\_c\phantom{ }\phantom{ }\phantom{ }} 2,3~GiB
\<^descr> \texttt{modex\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }} 33~MiB
\<^descr> \texttt{isabelle\_c} 1,6~GiB
\<close>

text' \<open>
\<^bold>\<open>Disk: Number of Debian packages additionally installed\<close>
\<close>

text' \<open>
\<^descr> \texttt{gcc\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }} 074
\<^descr> \texttt{frama\_c\phantom{ }\phantom{ }\phantom{ }} 240
\<^descr> \texttt{modex\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }} 014
\<^descr> \texttt{isabelle\_c} 025
\<close>

text' \<open>
\<^bold>\<open>Network: Total received\<close>
\<close>

text' \<open>
\<^descr> \texttt{gcc\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }} 324,12~MiB
\<^descr> \texttt{frama\_c\phantom{ }\phantom{ }\phantom{ }} 176,46~MiB
\<^descr> \texttt{modex\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }} 005,94~MiB
\<^descr> \texttt{isabelle\_c} 463,49~MiB
\<close>

text' \<open>
\<^bold>\<open>Network: Total sent\<close>
\<close>

text' \<open>
\<^descr> \texttt{gcc\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }} 6,50~MiB
\<^descr> \texttt{frama\_c\phantom{ }\phantom{ }\phantom{ }} 3,53~MiB
\<^descr> \texttt{modex\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }} 145~KiB
\<^descr> \texttt{isabelle\_c} 8,70~MiB
\<close>

text' \<open>
\<^bold>\<open>Network: Average bitrate received\<close>
\<close>

text' \<open>
\<^descr> \texttt{gcc\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }} 995,94~kbit/s
\<^descr> \texttt{frama\_c\phantom{ }\phantom{ }\phantom{ }} 03,12~Mbit/s
\<^descr> \texttt{modex\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }} 01,47~Mbit/s
\<^descr> \texttt{isabelle\_c} 18,00~Mbit/s
\<close>

text' \<open>
\<^bold>\<open>Network: Average bitrate sent\<close>
\<close>

text' \<open>
\<^descr> \texttt{gcc\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }} 019,98~kbit/s
\<^descr> \texttt{frama\_c\phantom{ }\phantom{ }\phantom{ }} 062,51~kbit/s
\<^descr> \texttt{modex\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }} 035,04~kbit/s
\<^descr> \texttt{isabelle\_c} 337,85~kbit/s
\<close>

text' \<open>
\<^bold>\<open>Generator: Lines of code\<close>
\<close>

text' \<open>
\<^descr> \texttt{gcc\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }} 56
\<^descr> \texttt{frama\_c\phantom{ }\phantom{ }\phantom{ }} 43
\<^descr> \texttt{modex\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }} 34
\<^descr> \texttt{isabelle\_c} 38
\<close>

text' \<open>
\<^bold>\<open>Generator: Number of shell top-level commands executed\<close>
\<close>

text' \<open>
\<^descr> \texttt{gcc\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }} 40
\<^descr> \texttt{frama\_c\phantom{ }\phantom{ }\phantom{ }} 32
\<^descr> \texttt{modex\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }} 14
\<^descr> \texttt{isabelle\_c} 22
\<close>

text' \<open>
\<^bold>\<open>Additional GUI software provided\<close>
\<close>

text' \<open>
\<^descr> \texttt{gcc\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }}
The package does not include any GUI to build.
\<^descr> \texttt{frama\_c\phantom{ }\phantom{ }\phantom{ }}
The \<^emph>\<open>default\<close> rules of installation perform the full build of the project,
including the build of a GUI (and also a separate ``command-line-only tool''), even on a server
machine without graphical display.
\<^descr> \texttt{modex\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }}
The package does not include any GUI to build.
\<^descr> \texttt{isabelle\_c}
The package comes with a GUI (and also a separate ``command-line-only tool''), but its building
phase is by default only invoked the first time it is demanded (which was not executed in our case).
\<close>

text' \<open>
\<^bold>\<open>License\<close>
\<close>

text' \<open>
\<^descr> GCC
  \<^descr> Usage

  \<open>GPLv3+ with GCC Runtime Library Exception\<close>
  \<^descr> No modifications were made on GCC.

  Any other parts (e.g. those calling GCC or processing its output) that we
  modified are in \<open>BSD-3-Clause\<close>.
\<^descr> Frama-C
  \<^descr> Usage

  Parts of the components are either in \<open>CDDL-1.0\<close>,
  \<open>LGPL-2.0-or-later\<close>, \<open>LGPL-2.1-only\<close>, or
  \<open>Q modified license\<close>.
  \<^descr> Modifications

  \<open>LGPL-2.1-only\<close> is the licence of the parts that we
  modified.
\<^descr> Modex
  \<^descr> Usage

  \<open>All Rights Reserved. This software is for educational purposes only.\<close>

  Permission is given to distribute the code provided that its introductory message is not removed
  and no monies are exchanged.
  \<^descr> No modifications were made on Modex.

  Any other parts (e.g. those calling Modex or processing its output) that we
  modified are in \<open>BSD-3-Clause\<close>.
\<^descr> Isabelle/C/Split
  \<^descr> Usage
 
  \<open>BSD-3-Clause\<close>
  \<^descr> Modifications

  \<open>BSD-3-Clause\<close> is the licence of the parts that we
  modified.
\<close>

paragraphX \<open>Same Configuration and Type of CPU as in Previous Experiments But Now With Only One Core\<close>

text' \<open>
\<^bold>\<open>Time: Elapsed wall clock\<close> ``hours \<open>:\<close> minutes \<open>:\<close> seconds \<open>.\<close> and the first $10^{-2}$ digits''
\<close>

text' \<open>
\<^descr> \texttt{gcc\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }} 1:06:31.09
\<^descr> \texttt{frama\_c\phantom{ }\phantom{ }\phantom{ }} 0:11:15.45
\<^descr> \texttt{modex\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }} 0:00:23.78
\<^descr> \texttt{isabelle\_c} 0:04:06.52
\<close>

text' \<open>
\<^bold>\<open>Network: Average bitrate received\<close>
\<close>

text' \<open>
\<^descr> \texttt{gcc\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }} 676,72~kbit/s
\<^descr> \texttt{frama\_c\phantom{ }\phantom{ }\phantom{ }} 02,16~Mbit/s
\<^descr> \texttt{modex\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }} 01,56~Mbit/s
\<^descr> \texttt{isabelle\_c} 15,31~Mbit/s
\<close>

text' \<open>
\<^bold>\<open>Network: Average bitrate sent\<close>
\<close>

text' \<open>
\<^descr> \texttt{gcc\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }} 013,81~kbit/s
\<^descr> \texttt{frama\_c\phantom{ }\phantom{ }\phantom{ }} 042,98~kbit/s
\<^descr> \texttt{modex\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }} 037,74~kbit/s
\<^descr> \texttt{isabelle\_c} 286,47~kbit/s
\<close>

paragraphX \<open>Adjusted Elapsed Time Taking Into Consideration the Bandwidth Bitrates\<close>

text' \<open>
The presented elapsed times included the time spent in making the download communication of the
computer to the outside network, which performance may vary: e.g. depending on the length of files
being downloaded, quantity of files to download, or server response time. Thus, the final time
ranking might change.

However, as the results will show, we are going to not take into account the upload data, and only
consider how download data are affecting the elapsed times. This is because for each task the size
of upload data appears small, and occurs most often during the time range when a download is being
made, or to be initiated closely soon after.

Globally, the overall ranking of the elapsed times of each task remains similar as previous results.
\<close>

(*
t = min1*60+sec1-((size1/(speed1*1000/1024/1024)))
min2 = t/60
sec2 = t-min2*60
*)

text' \<open>
\<^bold>\<open>Time: Adjusted elapsed wall clock in the many-core setting\<close>
\<close>

text' \<open>
\<^descr> \texttt{gcc\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }} 26:01.68
\<^descr> \texttt{frama\_c\phantom{ }\phantom{ }\phantom{ }} 05:51.90
\<^descr> \texttt{modex\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }} 00:19.72
\<^descr> \texttt{isabelle\_c} 02:36.10
\<close>

text' \<open>
\<^bold>\<open>Time: Adjusted elapsed wall clock in the mono-core setting\<close>
\<close>

text' \<open>
\<^descr> \texttt{gcc\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }} 58:08.87
\<^descr> \texttt{frama\_c\phantom{ }\phantom{ }\phantom{ }} 10:16.15
\<^descr> \texttt{modex\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }} 00:19.79
\<^descr> \texttt{isabelle\_c} 03:34.78
\<close>

paragraphX \<open>Synthesis of Resource Usage\<close>

text' \<open>
\<^descr> \texttt{gcc\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }}

In this compiling task, we are only interested to the exact options given to GCC while compiling C
files in the RTEMS source. Thus, it may be not necessary to perform the complete build of the
project with GCC, which is triggered through \<^verbatim>\<open>waf\<close>. For example, one can
imagine executing \<^verbatim>\<open>waf\<close> in a simulation mode to only print the list of
commands it is planned to execute.

In more details, the build of the RSB repository could also be skipped, since it is occupying the
major part of the task's time (25~min in the 6-cores experiments, and 55~min in the one core). Also,
even if the build of a GCC cross-compiler would be fast, we are only interested to get a
preprocessed version of a C file, which might after all be equally obtained from any other versions
of GCC. In particular, we conjecture that the one already installed in the Debian machine would
provide a same preprocessed file than the cross-compiled GCC (when both are called with the same GCC
options).

Note that the cross-compiling phase appears to be nevertheless an unavoidable step, needed for other
RTEMS-related projects, so the investment of effort and time spent in this task ---while building a
cross-compiler--- will not be considered as wasted.

Overall, since this task is performing the worst on:
  \<^enum> the total elapsed time,
  \<^enum> the disk increment usage, and
  \<^enum> the complexity of the generator or ease of installation (regarding lines of code and
  approximate number of top-level shell commands to execute),

then its benchmarks can serve as a minimum (acceptable) lower bound to not cross, for other tools of
other tasks.

\<^descr> \texttt{frama\_c\phantom{ }\phantom{ }\phantom{ }}

The default installation of Frama-C triggers the complete build of the project which provides a
GUI. There might be particular options to only trigger the build of its command line version,
although which options to invoke do not appear to be immediate to find in the source code.

In parallel, the execution time of this task could be reduced by improving the number of packages
installed by opam, as we are only targeting the command line version of the tool. In particular,
several graphical packages (such as lablgtk) appears in the \<^emph>\<open>mandatory\<close> list of
Frama-C's dependent packages, i.e. always installed before Frama-C. Similarly, removing these
dependencies will impact in return the number of Debian packages to install, and lowering them.

Note that it is possible for opam to install several packages in parallel, a feature particularly
useful in a many-core computing setting. However, there is a separation barrier between the code
running the package manager and each code running their respective package installation. In
particular, an instance of the latter might at some point be optimally in need of the resources of
several cores, but there is no dynamic coordination between other computing instances regarding the
number of cores available at a particular moment of the installation.

\<^descr> \texttt{modex\phantom{ }\phantom{ }\phantom{ }\phantom{ }\phantom{ }}

Instead of implementing certain additional postprocessing out of Modex, the performance of this task
would have been improved if the same modifications were directly implemented in it. However, we
refrained from directly modifying Modex, as its license had been free only for a limited number of
fields of
endeavor.\<^footnote>\<open>\<^url>\<open>https://www.debian.org/social_contract.html\<close>\<close>

Practically, the benchmark shows that Modex's elapsed times do not substantially change when running
it in a multi-core setting, compared to an equivalent but single-core experiment. Since a large part
of the translation amounts to translating a C function to a respective Promela one, potentials for
efficiently exploiting parallelism become higher whenever the number of C functions to translate is
accordingly high (e.g. for the smpmrsp01 example, we currently have 821 functions). Note that this
kind of exploitation is particularly feasible due to the fact that each C function to translate can
be independently treated in parallel.

\<^descr> \texttt{isabelle\_c}

A closer look at the downloaded data shows that it is the highest compared to other tools. Indeed,
the archive of Isabelle2019 occupies a large part of the downloading activity: its size is
394.0~MiB. This archive contains several additional heap (binary) objects, that can all be removed
to gain at least 73.1~MiB of compressed archive.\<^footnote>\<open>When considering the full
extracted archive, the gain amounts to 255.12~MiB.\<close> On the other hand, removing heaps is at
the cost of making the tool's first invocation taking more CPU-time to reconstruct any missing ones,
whenever really needed.

Still, not all heaps are required by Isabelle/C. Even if its source currently uses HOL as default
entry-point, it is straightforward to rework its base dependencies, and replace any mentions of
``HOL'' by ``Pure'', its native ML kernel as equally valid entry-point.

Once HOL dependencies are removed, we can additionally drop its source from the archive (which are
not used by Isabelle/Split), as well as the source of any unused components, such as its GUI (its
build was not invoked) --- e.g. one can put them in a separate archive for optional download.

Note that there is the possibility of dynamically downloading the internal package dependencies
included in the archive, such as Java, Scala etc., through a script already provided in the
developer repository. This configuration would actually be similar as a fresh clone from the
Isabelle developer repository, where one starts with an archive without any pre-packaged
binaries. Some of these binaries will always be mandatory to retrieve though (e.g. polyml). For the
case of Isabelle2019, an archive version of its fresh clone would have a size of at most 17,8~MiB
(and without counting yet the potential gain from the removal of unused source).
\<close>

subsubsectionX \<open>Miscellaneous\<close>
paragraphX \<open>Three Variants of generation: raw, index, diff\<close>

text' \<open>
By executing \<open>gcc -E\<close> instead of \<open>gcc -c\<close> on a C file present in
\<open>./waf -v\<close>, we may not obtain the complete graph of source code implicitly imported by
the C file through \<open>gcc -E\<close>, but only a subset. For example, there is a function in
\<open>testsuites/sptests/speventsystem01/init.c\<close> calling \<open>rtems_event_receive\<close>,
however the body implementation of \<open>rtems_event_receive\<close> is not in the dependency graph
produced by \<open>gcc -E\<close>: for the \<open>gcc -E\<close> option to work, it is enough to
give a prototype version of \<open>rtems_event_receive\<close>, and this is particularly what was
done.

Since the body implementation of \<open>rtems_event_receive\<close> is ultimately needed by at least
\<open>gcc -o\<close> while in the final phase of producing an executable, one can actually find
where the body of \<open>rtems_event_receive\<close> is defined and resolved by inspecting the line
of the precise \<open>gcc -o\<close> associated to the above \<open>gcc -c\<close>.

Although this does not directly show which file is defining \<open>rtems_event_receive\<close>, we
end up with enough information to manually retrieve it: for the case of
\<open>testsuites/sptests/speventsystem01/init.c\<close>, its \<open>gcc -o\<close> is invoking
several \<open>-l\<close> options. A deeper inspection of \<open>-lrtemscpu\<close> particularly
reveals that the body of \<open>rtems_event_receive\<close> is indeed in one of the files stored in
the associated \<open>librtemscpu.a\<close>.

Note that here \<open>-lrtemscpu\<close> does not have to be explicitly written: for example, by
only giving \<open>-lrtemstest\<close> to \<open>gcc -o\<close>, \<open>gcc -o\<close> will
implicitly call \<open>ld\<close> on some ``own resolved versions of \<open>-l\<close>''. These
resolved versions might already contain \<open>-lrtemscpu\<close>, which will make
\<open>gcc -o\<close> executes its compiling process regardless of the presence of
\<open>-lrtemscpu\<close> or absence of the option.
\<close>

subsubsectionX \<open>Conclusion\<close>

text' \<open>
We have some powerful tools, based on Frama-C and Isabelle/C
to allow us to process RTEMS sources in a variety of ways.
These tools, however,
are very heavyweight,
and their use is unlikely to suit the majority or RTEMS users.

What they should help us to do, is to get the basic shape
of suitable Promela models from RTEMS code,
which we can simplify (carefully)
so that model-checking,
and hence,
test-generation,
become feasible.

The use of Frama-C in its own right may be something that
we can advocate in the future,
if we can address its codebase size.
\<close>

(*<*)
rst_export_file

end
(*>*)
