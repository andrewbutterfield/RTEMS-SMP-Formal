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
theory specimpl
  imports Isabelle_Doc_reStructuredText.reStructuredText_Wrapper
begin

declare [[reStructuredText]]

comment \<open>
SPDX-License-Identifier: CC-BY-SA-4.0 OR BSD-2-Clause

Copyright (C) 2019-2021 Trinity College Dublin (www.tcd.ie)
\<close>

(*>*)

sectionX \<open>Description of the Implementation\<close>

text' \<open>
This section details how to invoke our test generation tool to produce test files from Promela
model.

The technique is generic: it has been successfully applied to produce C test files, but also
``meta'' YAML test files (that can themselves be used at a later stage to generate more concrete
programming-language specific code, including C).

The information making our tool producing specific language implementation code is captured in
various additional data that we provide to our tool as input. Refinement files are examples of such
information needed by the tool to run.

The next sections start by giving a basic description of how folders are organized, and go deeper to
present the semantics of input format and refinement files of our test generation tool.
\<close>

subsectionX \<open>Structure of the Source\<close>

subsubsectionX \<open>Source\<close>

subsubsectionX \<open>Examples\<close>

text' \<open>
Running examples for the tool are located in \<^dir>\<open>FV2-201_models\<close>, whereas
\<^dir>\<open>Promela_to_C/examples\<close> is only relevant for configuring the current
model-checker invoked by the tool. Examples in \<^dir>\<open>FV2-201_models\<close> are mostly
independent, and thus can be tried out separately.
\<close>

text' \<open>
By taking \<^dir>\<open>FV2-201_models/chains\<close> as example, abbreviated as
\<^dir>\<open>models_chains\<close>, we list here its content:
\<^item> \<^file>\<open>models_chains/rqmts-spec-level/freechain/cpukit/1_pure/cpukit.pml\<close>: Minimal Promela model
without propositions and side-effects (e.g., without \<open>assert\<close> and
\<open>printf\<close>).
\<^item> \<^file>\<open>models_chains/rqmts-spec-level/freechain/cpukit/2_printf/cpukit.pml\<close>: Variant based on
\<^file>\<open>models_chains/rqmts-spec-level/freechain/cpukit/1_pure/cpukit.pml\<close> --- Example of printing with
\<open>printf\<close> to incrementally show the states of various data.
\<^item> \<^file>\<open>models_chains/rqmts-spec-level/freechain/testsuites_spfreechain01.pml\<close>: Variant
based on \<^file>\<open>models_chains/rqmts-spec-level/freechain/cpukit/1_pure/cpukit.pml\<close> where the
refinement part and configuration are separate:
  \<^item> \<^file>\<open>models_chains/rqmts-spec-level/freechain/testsuites_spfreechain01.rfn\<close> --- Usage
  of more elaborated formulae (i.e., \<open>ltl\<close> proposition)
  \<^item> \<^file>\<open>models_chains/rqmts-spec-level/freechain/testsuites.cfg\<close>
\<^item> \<^file>\<open>models_chains/rqmts-spec-level/freechain/testsuites/testsuites_spfreechain01.pml\<close>: Variant based on
\<^file>\<open>models_chains/rqmts-spec-level/freechain/testsuites_spfreechain01.pml\<close> --- Example of assertion using
\<open>assert\<close>.
\<close>

text' \<open>
Besides the example in \<^dir>\<open>models_chains/rqmts-spec-level\<close>, another ``low-level''
variant is provided in \<^dir>\<open>models_chains/src\<close>, which has actually been specifically
derived from \<^dir>\<open>models_chains/examples/only_generic\<close>, and particularly
\<^file>\<open>models_chains/examples/only_generic/chains.pml\<close> and
\<^file>\<open>models_chains/examples/only_generic/chains.rfn\<close>. Like
\<^dir>\<open>models_chains/rqmts-spec-level\<close>, we retrieve a similar structure:
  \<^item> \<^file>\<open>models_chains/src/testsuites_spfreechain01.pml\<close>
  \<^item> \<^file>\<open>models_chains/src/refine_sptests/testsuites_spfreechain01.rfn\<close>
  \<^item> \<^file>\<open>models_chains/src/testsuites.cfg\<close>
\<close>

text' \<open>
The folder \<^dir>\<open>models_chains/rqmts-spec-level/errors\<close> regroups several examples of
models which specifications might lead to miscellaneous corner cases.
  \<^item> For instance, the mutual interaction of \<open>add\<close> and \<open>del\<close>
  implemented in
  \<^file>\<open>models_chains/rqmts-spec-level/errors/queue_too_many_processes.pml\<close> can lead
  to an infinite execution loop (see the documentation in the file).
  \<^item> \<^file>\<open>models_chains/rqmts-spec-level/errors/queue_invalid_end_state.pml\<close>
  is an example where the program is terminating in some not expected ending point.
\<close>

subsectionX \<open>Semantics of the Generation\<close>

subsubsectionX \<open>Syntactic Invocation from the Shell\<close>

text' \<open>
\<^file>\<open>Promela_to_C/src/testgen_ml.sh\<close> takes an ordered list of Promela
\<^emph>\<open>contents\<close> as argument, where a ``content'' is more specifically defined as
being:
\<^item> either a \<^emph>\<open>path\<close> of a file containing a Promela source,
\<^item> or a raw \<^emph>\<open>string\<close> representing a Promela source, which is directly
provided in the command line as argument.
\<close>

text' \<open>
By default, all arguments of \<^file>\<open>Promela_to_C/src/testgen_ml.sh\<close> are understood to be paths of
files. The explicit way to specify that an incoming argument is not a path but a string is by using
the option \<^verbatim>\<open>--promela\<close> (or --- equivalently --- the shorter
\<^verbatim>\<open>-p\<close> option).
\<close>

text' \<open>
There are basically only two constraints to fulfill for a list of provided arguments be
characterized as well-parsed, and subsequently processed with the intended normal behavior of
\<^file>\<open>Promela_to_C/src/testgen_ml.sh\<close>:
\<^enum> Each argument must be separately well-parsed by the parser
\<^verbatim>\<open>promela-yacc\<close>, a parser library that we have derived from the initial
project \<^url>\<open>https://github.com/johnyf/promela\<close> to support more elements of the
Promela language, and that we provide in \<^dir>\<open>Promela_to_C/src/src/modules/promela_yacc\<close>.
\<^enum> Additionally, the final (ordered) concatenation of all arguments must produce a content
well-parsed by the parser integrated in the model-checker $\mathcal{M}$, which value is set at
run-time (more details below).
\<close>

text' \<open>
Note that as corollary, the combination of the above constraints makes any prefix concatenation
subsets of arguments be well-parsed by \<^verbatim>\<open>promela-yacc\<close>, as well as
well-parsed by the parser of $\mathcal{M}$.

Also, the acceptance range of \<^verbatim>\<open>promela-yacc\<close> has been modified to
additionally accept empty programs as well-parsed entities. This makes a sole invocation of
\<^file>\<open>Promela_to_C/src/testgen_ml.sh\<close> (without arguments) not failing: in the tiniest
setting, \<^file>\<open>Promela_to_C/src/testgen_ml.sh\<close> first start by compiling the source as
usual.
\<close>

text' \<open>
As we mentioned that \<^file>\<open>Promela_to_C/src/testgen_ml_spin.sh\<close> is a shortcut for
\<^file>\<open>Promela_to_C/src/testgen_ml.sh\<close>, an example to invoke the test generation program
would then be:
  \<^descr> \<^file>\<open>Promela_to_C/src/testgen_ml_spin.sh\<close>
    \<^descr> \<^verbatim>\<open>$STRIP/testsuites_spfreechain01.pml\<close>
    \<^descr> \<^verbatim>\<open>$STRIP/testsuites_spfreechain01.rfn\<close>
    \<^descr> \<^verbatim>\<open>--promela\<close> \<^verbatim>\<open>"$(cat\<close> \<^verbatim>\<open>$STRIP/testsuites.cfg\<close> \<^verbatim>\<open>)"\<close>
\<close>
(*
text' \<open>
\begin{gather*}
\begin{tabular}{ll}
\multicolumn{2}{l}{ \<^file>\<open>Promela_to_C/src/testgen_ml_spin.sh\<close> } \\
\<^verbatim>\<open>          \<close> & \<^verbatim>\<open>$STRIP/testsuites_spfreechain01.pml\<close> \\
              & \<^verbatim>\<open>$STRIP/testsuites_spfreechain01.rfn\<close> \\
              & \<^verbatim>\<open>--promela\<close> \<^verbatim>\<open>"$(cat\<close> \<^verbatim>\<open>$STRIP/testsuites.cfg\<close> \<^verbatim>\<open>)"\<close>
\end{tabular}
\end{gather*}
\<close>
*)
text' \<open>
where \<^verbatim>\<open>$STRIP\<close> is a shorthand for the folder
\<^dir>\<open>models_chains/rqmts-spec-level/freechain\<close> or
\<^dir>\<open>models_chains/src\<close>.

The motivation and details of the different files are now provided in the following part.
\<close>

subsubsectionX \<open>Extending Promela with an Annotation Language\<close>

paragraphX \<open>Semantics of Annotation Commands\<close>

text' \<open>
Since the Promela (specification) language can be approximated as a strict subset of the C
(programming) language, we must necessarily increase the expressivity of the language that our tool
is accepting in input, for the task of generating $\mathcal{C}$ test files from Promela models be first decidable,
and second as automatic as possible.

Consequently, not only will our tool take as input some Promela model, but it will also take some
additional information specifying how the model will have to be extracted to $\mathcal{C}$ (together with any
information that can not be automatically processed by our tool). Such information is basically what
\<^emph>\<open>refinement\<close> files are.

One way of providing the refinement information and model to the tool is by using an
\<^emph>\<open>annotation language\<close>, embedded inside Promela comments. Generally, annotations
have the advantage of acting as transparent information container with little disruption on the
source: e.g. similarly as to how one is taking advantage of programming languages supporting
arbitrary comments, to embed there ``formal'' information. Usually, the formal information can refer
to any piece of code mostly considered critical, enabling at the same time any forms of formal
reasoning, through a special system of reference quotations and dereferences to the code. However we
will see that this is not mandatory, e.g. the formal information can independently coexist with the
code and be placed before or next to it, also without making any particular referencing to the code.
\<close>

text' \<open>
A Promela \<^emph>\<open>comment\<close> is similar as a comment written in C: in Promela, there is
a preprocessing phase generating Promela tokens from some raw unpreprocessed source. It turns out
that the preprocessing language of Promela is strictly identical to the preprocessing language of
C. Consequently, we distinguish two types of
comments\<^footnote>\<open>\<^url>\<open>https://gcc.gnu.org/onlinedocs/gcc-7.5.0/cpp/\<close>\<close>:
\<^item> block comments enclosed between \<^verbatim>\<open>/*\<close> and
\<^verbatim>\<open>*/\<close>,
\<^item> line comments starting with \<^verbatim>\<open>//\<close>.
\<close>

text' \<open>
Additionally, we noticed that \<^verbatim>\<open>@@\<close> is not a symbol used in the reference
manuals of C and Promela that we inspected, also not used in the C and Promela source we dealt
with. So we took the liberty of changing the priority preprocessing of that symbol, by extending the
language of comments and considering the following item as valid:
\<^item> line comments starting with \<^verbatim>\<open>@@\<close>.
\<close>

text' \<open>
Similarly as to how an \<^emph>\<open>annotated comment\<close> is opened in
ACSL\<^footnote>\<open>\<^url>\<open>https://en.wikipedia.org/wiki/ANSI/ISO_C_Specification_Language\<close>\<close>,
we use the specific syntactic keyword \<^verbatim>\<open>@\<close> to distinguish between a regular
comment and a comment which content will be additionally submitted to the type system of our
annotation language. Overall, annotated comments are taking the following forms:
\<^item> block annotated comments enclosed between \<^verbatim>\<open>/*@\<close> and
\<^verbatim>\<open>*/\<close>,
\<^item> line annotated comments starting with \<^verbatim>\<open>//@\<close>,
\<^item> line annotated comments starting with \<^verbatim>\<open>@@@\<close>.
\<close>
(*
text' \<open>
Inside an annotated comment, we might want to use consecutive \<^emph>\<open>commands\<close>
(separated by spaces) to better organize the flow of information arising from our interaction with
the underlying formal system (i.e. our test generation tool). A command is composed of a
\<^emph>\<open>command-identifier\<close> taking several \<^emph>\<open>command-arguments\<close>
(still separated by spaces). Since all names are just separated by only spaces, to precisely
differentiate a command-argument from an command-identifier, we syntactically set all
command-arguments to be escaped within special delimiters:
\<^item> between the opening delimiter
\<^verbatim>\<open>\\<close>\<^verbatim>\<open><open>\<close>,
\<^item> and the closing delimiter \<^verbatim>\<open>\\<close>\<^verbatim>\<open><close>\<close>.
\<close>

text' \<open>
For readability reasons, in the remaining part of the document, the two enclosing delimiters
``\<^verbatim>\<open>\\<close>\<^verbatim>\<open><open>\<close>'' and
``\<^verbatim>\<open>\\<close>\<^verbatim>\<open><close>\<close>'' will respectively be depicted as
``\isa{{\isasymopen}}'' and ``\isa{{\isasymclose}}''.
\<close>

text' \<open>
For example, in the following annotated comment:
``\<^verbatim>\<open>/*@\<close> $\<^verbatim>\<open>cmd\<close>_1$ \isa{{\isasymopen}} $\text{arg}^1_1$ \isa{{\isasymclose}} \isa{{\isasymopen}} $\text{arg}^2_1$ \isa{{\isasymclose}} \isa{{\isasymopen}} $\text{arg}^3_1$ \isa{{\isasymclose}} 
         $\<^verbatim>\<open>cmd\<close>_2$ \isa{{\isasymopen}} $\text{arg}^1_2$ \isa{{\isasymclose}} \isa{{\isasymopen}} $\text{arg}^2_2$ \isa{{\isasymclose}} \isa{{\isasymopen}} $\text{arg}^3_2$ \isa{{\isasymclose}} \isa{{\isasymopen}} $\text{arg}^4_2$ \isa{{\isasymclose}}
   \<^verbatim>\<open>*/\<close>'',
$\<^verbatim>\<open>cmd\<close>_1$ is taking three arguments, whereas
$\<^verbatim>\<open>cmd\<close>_2$ four.
\<close>
*)

text' \<open>
Inside an annotated comment, we might want to use consecutive \<^emph>\<open>commands\<close> to
better organize the flow of information arising from our interaction with the underlying formal
system (i.e. our test generation tool). A command is composed of a
\<^emph>\<open>command-identifier\<close> taking several \<^emph>\<open>command-arguments\<close>.

We can thought of commands as ordered lists with possible duplication of elements, where several
same command-identifiers can appear in the list. In this setting, we place command-identifiers
aligned to the first indentation level, whereas command-arguments are just appearing in the second
one.
\<close>

text' \<open>
For example, in the following annotated comment expressed in YAML syntax,
$\<^verbatim>\<open>cmd\<close>_1$ is taking three arguments, whereas
$\<^verbatim>\<open>cmd\<close>_2$ four:\<^footnote>\<open>In some fictive programming language, one
could imagine the parsed data to be of type: ``((string, string list) dict) list''.\<close>
  \<^descr> \<^verbatim>\<open>/*@\<close>
    \<^descr> \<^verbatim>\<open>-\<close> $\<^verbatim>\<open>cmd\<close>_1$:
      \<^descr> \<^verbatim>\<open>-\<close> $\text{arg}^1_1$
      \<^descr> \<^verbatim>\<open>-\<close> $\text{arg}^2_1$
      \<^descr> \<^verbatim>\<open>-\<close> $\text{arg}^3_1$
    \<^descr> \<^verbatim>\<open>-\<close> $\<^verbatim>\<open>cmd\<close>_2$:
      \<^descr> \<^verbatim>\<open>-\<close> $\text{arg}^1_2$
      \<^descr> \<^verbatim>\<open>-\<close> $\text{arg}^2_2$
      \<^descr> \<^verbatim>\<open>-\<close> $\text{arg}^3_2$
      \<^descr> \<^verbatim>\<open>-\<close> $\text{arg}^4_2$
  \<^descr> \<^verbatim>\<open>*/\<close>
\<close>

text' \<open>
Equivalently, the same content can be rewritten in a \<^bold>\<open>single\<close> line as
follows:\<^footnote>\<open>Although practically, it might have been rendered split into several
lines.\<close>
  \<^descr> \<^verbatim>\<open>//@ [{"\<close>$\<^verbatim>\<open>cmd\<close>_1$\<^verbatim>\<open>": ["\<close>$\text{arg}^1_1$\<^verbatim>\<open>", "\<close>$\text{arg}^2_1$\<^verbatim>\<open>", "\<close>$\text{arg}^3_1$\<^verbatim>\<open>"]}, {"\<close>$\<^verbatim>\<open>cmd\<close>_2$\<^verbatim>\<open>": ["\<close>$\text{arg}^1_2$\<^verbatim>\<open>", "\<close>$\text{arg}^2_2$\<^verbatim>\<open>", "\<close>$\text{arg}^3_2$\<^verbatim>\<open>", "\<close>$\text{arg}^4_2$\<^verbatim>\<open>"]}]\<close>
\<close>

text' \<open>
At the time of writing, the above presented YAML syntax is fully supported. There is however an
internal syntax currently in effect and called ML. This ML syntax has been more intended for
developers, so it might not appear in public releases of the software. As an overview though, we can
quickly show how the above annotations are written in ML. First, all command-arguments appear
escaped
\<^item> between the opening delimiter
\<^verbatim>\<open>\\<close>\<^verbatim>\<open><open>\<close>,
\<^item> and the closing delimiter \<^verbatim>\<open>\\<close>\<^verbatim>\<open><close>\<close>.
\<close>

text' \<open>
For readability reasons, the two enclosing delimiters
``\<^verbatim>\<open>\\<close>\<^verbatim>\<open><open>\<close>'' and
``\<^verbatim>\<open>\\<close>\<^verbatim>\<open><close>\<close>'' can also be depicted as
``\isa{{\isasymopen}}'' and ``\isa{{\isasymclose}}''.
\<close>

text' \<open>
For example, in the following annotated comment:
``\<^verbatim>\<open>/*@\<close> $\<^verbatim>\<open>cmd\<close>_1$ \isa{{\isasymopen}} $\text{arg}^1_1$ \isa{{\isasymclose}} \isa{{\isasymopen}} $\text{arg}^2_1$ \isa{{\isasymclose}} \isa{{\isasymopen}} $\text{arg}^3_1$ \isa{{\isasymclose}} 
         $\<^verbatim>\<open>cmd\<close>_2$ \isa{{\isasymopen}} $\text{arg}^1_2$ \isa{{\isasymclose}} \isa{{\isasymopen}} $\text{arg}^2_2$ \isa{{\isasymclose}} \isa{{\isasymopen}} $\text{arg}^3_2$ \isa{{\isasymclose}} \isa{{\isasymopen}} $\text{arg}^4_2$ \isa{{\isasymclose}}
   \<^verbatim>\<open>*/\<close>'',
$\<^verbatim>\<open>cmd\<close>_1$ is taking three arguments, whereas
$\<^verbatim>\<open>cmd\<close>_2$ four.
\<close>

paragraphX \<open>Semantics of Annotated Files\<close>

text' \<open>
For flexibility reasons, we might want to separate the model information from the annotation
information. So our tool accepts to receive in input possibly different types of files containing
any information that the user might find relevant to combine together inside a unique file, or leave
them explicitly separate.

Generally, even if the list of file arguments is syntactically provided as ordered, it is ultimately
the concatenation of the overall content which will be semantically treated by the test generation
tool. Since our tool is internally calling the model-checker $\mathcal{M}$, the possibility or not
to permute the initial list of arguments that we provide in input will ultimately depend on how well
a final concatenation of permuted arguments would be supported by $\mathcal{M}$. In that respect,
our tool does not impose a restriction on the particular order of arguments to give as long as what
is provided will be eventually correctly treated by $\mathcal{M}$.

From what we mentioned above, the case of ``explicit'' elements of the language which are
semantically treated by $\mathcal{M}$ is clear: we are following the same convention as
$\mathcal{M}$. On the other hand, ``invisible'' constructs such as annotation comments are following
different freedom rules: they are by default not considered by $\mathcal{M}$ and all discarded (by
$\mathcal{M}$) in a first preprocessing phase. Consequently, since annotation comments are solely
interpreted by our tool, the possibility or not to permute invisible constructs (comments) will
differ from the possibility to permute or not more explicit elements of the language.
\<close>

text' \<open>
Besides having flexibility as benefit, with different files the overall maintaining activity can be
delegated to different persons: since a Promela file without annotations is standalone, maintaining
it only requires a knowledge of Promela. (That would nevertheless require to take care of any
informal constructs surrounding any ``pure'' Promela code, comprising in this case comments, be them
formal or not.)
\<close>

subsubsectionX \<open>Semantics of Commands\<close>

paragraphX \<open>Attribute Commands\<close>

text' \<open>
Annotation commands are supposed to have the ability to perform ``arbitrary'' side-effects during
their evaluation, e.g. ranging from unrisky behaviour to Turing-complete computation. However, the
first group of commands that we designed towards end-users is just a strict subset of annotation
commands: being more lightweight, \<^emph>\<open>attribute\<close> commands do not necessitate large
computation resources.

Attribute commands take pure information data as arguments: their evaluations will just have the
effect of making the information data stored somewhere inside some background context for later
retrieval (for instance, storing them once, persistently, at the start of our generation
tool). Later, it will be at the discretion of other non-attribute commands to retrieve any relevant
registered data. Registered data are then ultimately understood as a list, so a data registered
multiple times will appear multiple times in the list.

Unless otherwise stated, any commands presented in this document belong to the category of attribute
commands. To perform the test generation though, there must be obviously other non-attribute
commands that our tool is internally using and invoking. However at the time of writing we do not
provide an explicit interface for end-users to invoke them. There is one exception though: in the
``$\mathcal{C}$ test generation'' part, the user will have the possibility to make the tool execute more
powerful pre-defined non-attribute commands, but under some controlled conditions (see the details
in that part).
\<close>

paragraphX \<open>Positional Commands\<close>

text' \<open>
Whereas attribute commands are storing some information data inside a background context, instead of
making the data stored ``globally'', it might be sometimes convenient to store it next to an element
\<^theory_text>\<open>pml_proc_inl\<close> of the Promela model, such as the name of a proctype, the
name of an inline element, or the name of any elements which can be uniquely identified. This is to
have a handy way to retrieve back the ``personalized'' data associated to a given unique identifier
\<^theory_text>\<open>pml_proc_inl\<close>. Such retrieval would be mostly beneficial to certain
non-attribute commands internally invoked by our tool, while applying algorithms discriminating on
the selection of particular node elements of the input model, including the selection order.

To this end, all annotation commands are assumed to be evaluated within a particular
\<^emph>\<open>navigation context\<close>: the line where an annotation command is written has now
an importance. If a command is written in the same line as an existing Promela proctype or inline
declaration, now indifferently abbreviated as \<^theory_text>\<open>pml_proc_inl\<close>, then that
command will be additionally aware that \<^theory_text>\<open>pml_proc_inl\<close> is available for
its use.\<^footnote>\<open>We assume dealing with at most one proctype or inline per line.\<close>

However, to simplify our presentation, we will not detail which non-attribute commands are expecting
to receive a \<^theory_text>\<open>pml_proc_inl\<close> as parameter for its correct
functioning. Rather, we will sort all attribute commands into two groups, based on whether an
attribute command should be placed near a \<^theory_text>\<open>pml_proc_inl\<close> element, so
that its data would be consequently stored, and reused by other commands. This leads to two
situations:
\<^item> The notation ``\<^bold>\<open>(at \<^theory_text>\<open>pml_proc_inl\<close>)\<close>''
will indicate that the attribute command should be placed near a valid
\<^theory_text>\<open>pml_proc_inl\<close>. If we can not find a declaration close enough to the
command, or if one has provided a name \<^theory_text>\<open>pml_proc_inl\<close> which does not
exist, then the evaluation effect of the command will simply be the identity function.
\<^item> The notation ``\<^bold>\<open>(globally)\<close>'' will be used for attribute commands
which will be executed as usual no matter where it was placed.
\<close>

paragraphX \<open>Generic Commands\<close>

text' \<open>
While developing a non-trivial Promela model of consequent size or for testing reasons, it might be
interesting of quickly executing arbitrary actions, involving Turing-complete computation. Such
commands will be called \<^emph>\<open>generic\<close> commands. Being the most expressive, they are
generalizing de-facto attribute commands.

The high expressivity of generic commands comes nevertheless with a certain price, e.g. regarding
their automated execution: our tool will have to execute consecutive generic commands only in
sequential order (compared to other types of consecutive ``declarative'' commands, where more
parallel optimization potentials might happen). Reciprocally and still in relation with correctness,
providing a set of generic commands, additional cares must be taken while building an enumerative
list deciding which command should be the next one to execute from the set: the permutation of two
commands might irreversibly produce different side-effects!

Note that some cares must also be brought on the appearance order of certain attribute commands,
particularly if a generic command is in the background processing what has been stored by an initial
group of attribute commands --- more details will be provided in front of any such concerned
commands.

With the above warning in mind, at the time of writing, we have only publicly released a subset
interface of generic commands (among the many ones internally used by our tool). The precise set of
generic commands currently available is detailed in the ``Generating a Test File'' part.
\<close>

subsectionX \<open>Generating a Trail File\<close>

text' \<open>
Providing a Promela file \<^verbatim>\<open>file.pml\<close>, the role of the model-checker
$\mathcal{M}$ is to prove that all propositions written in \<^verbatim>\<open>file.pml\<close> is
true. If this is not the case, then there might still be situations where $\mathcal{M}$ is able to
derive a counter-example in front of a false proposition, showing why the check of
\<^verbatim>\<open>file.pml\<close> failed.

Since the overall operation involves several actions from $\mathcal{M}$, occurring at the time when
$\mathcal{M}$ is expected to be called, we consequently provide several commands, one for each
action.
\<close>

subsubsectionX \<open>Main Commands\<close>

paragraphX \<open>Warning: Evaluation Order\<close>

text' \<open>
  \<^descr> \<^verbatim>\<open>model_checker_verifier\<close> $\<^theory_text>\<open>cts\<close>_1$
  $\dots$ $\<^theory_text>\<open>cts\<close>_{n-1}$
  \<^bold>\<open>(globally)\<close> has the same semantics as
  \<^verbatim>\<open>model_checker_compile\<close> $\<^theory_text>\<open>cts\<close>_1$ $\dots$
  $\<^theory_text>\<open>cts\<close>_{n-1}$ \<^verbatim>\<open>file.pml\<close>. In particular,
  \<^verbatim>\<open>file.pml\<close> is the name of the Promela file that is not needed to
  explicitly write.
  
  Additionally, all \<^verbatim>\<open>model_checker_verifier\<close> commands are considered to be
  evaluated before any \<^verbatim>\<open>model_checker_compile\<close> commands.
  \<^descr> \<^verbatim>\<open>model_checker_compile\<close> $\<^theory_text>\<open>cts\<close>_1$
  $\dots$ $\<^theory_text>\<open>cts\<close>_n$
  \<^bold>\<open>(globally)\<close> declares the shell command
  ``$\<^theory_text>\<open>cts\<close>_1$ $\dots$ $\<^theory_text>\<open>cts\<close>_n$'' as command
  to be executed when $\mathcal{M}$ is used to check if all propositions of
  \<^verbatim>\<open>file.pml\<close> are true.
  
  Additionally, all \<^verbatim>\<open>model_checker_compile\<close> commands are considered to be
  evaluated before any \<^verbatim>\<open>model_checker_exec_one\<close> commands.
  \<^descr> \<^verbatim>\<open>model_checker_exec_one\<close> $\<^theory_text>\<open>cts\<close>_1$
  $\dots$ $\<^theory_text>\<open>cts\<close>_n$
  \<^bold>\<open>(globally)\<close> declares the shell command
  ``$\<^theory_text>\<open>cts\<close>_1$ $\dots$ $\<^theory_text>\<open>cts\<close>_n$'' as command
  to be executed when $\mathcal{M}$ is used to check if all propositions of
  \<^verbatim>\<open>file.pml\<close> are true.
  
  Additionally, it is assumed that the last \<^verbatim>\<open>model_checker_exec_one\<close>
  $\<^theory_text>\<open>cts\<close>_1$ $\dots$ $\<^theory_text>\<open>cts\<close>_n$ shell command
  is leaving a file named \<^verbatim>\<open>file.pml.trail\<close> (inside the same directory where
  it is invoked), in the particular case where $\mathcal{M}$ is able to derive a counter-example
  from \<^verbatim>\<open>file.pml\<close>. (In case there is no
  \<^verbatim>\<open>model_checker_exec_one\<close> command, it is the last
  \<^verbatim>\<open>model_checker_compile\<close> or
  \<^verbatim>\<open>model_checker_verifier\<close> which is considered in the previous sentence.)
  \<^descr> \<^verbatim>\<open>model_checker_trail\<close> $\<^theory_text>\<open>cts\<close>_1$
  $\dots$ $\<^theory_text>\<open>cts\<close>_{n-2}$
  \<^bold>\<open>(globally)\<close> declares the shell command
  ``$\<^theory_text>\<open>cts\<close>_1$ $\dots$ $\<^theory_text>\<open>cts\<close>_{n-2}$
  \<^verbatim>\<open>file.pml.trail\<close> \<^verbatim>\<open>file.pml\<close>'' as command to be
  executed when $\mathcal{M}$ is used to derive a readable counter-example from
  \<^verbatim>\<open>file.pml.trail\<close>. In particular,
  \<^verbatim>\<open>file.pml.trail\<close> and \<^verbatim>\<open>file.pml\<close> are the names
  that are not needed to explicitly write.

  Additionally, it is assumed that the command is directly printing the readable counter-example to
  the standard output (file descriptor).
\<close>

subsubsectionX \<open>Optional Commands\<close>

text' \<open>
  \<^descr> \<^verbatim>\<open>no_printf\<close>
  \<^bold>\<open>(at \<^theory_text>\<open>pml_proc_inl\<close>)\<close> declares that \<^theory_text>\<open>pml_proc_inl\<close> will not have any $\mathcal{C}$ code to print
  (irrespective of previous and future use of \<^verbatim>\<open>refine_uniform\<close>).
  
  \<^descr> \<^verbatim>\<open>no_atomic\<close>
  \<^bold>\<open>(at \<^theory_text>\<open>pml_proc_inl\<close>)\<close> declares that no extra $\<^verbatim>\<open>atomic\<close>^\text{PML}$ wrapper will be wrapped
  around the generated $\<^verbatim>\<open>printf\<close>^\text{PML}$ statement, whereas by default,
  there is one such being generated.
  
  \<^descr> \<^verbatim>\<open>print_first\<close>
  \<^bold>\<open>(at \<^theory_text>\<open>pml_proc_inl\<close>)\<close> declares to insert a $\<^verbatim>\<open>printf\<close>^\text{PML}$ at the beginning of the
  encountered proctype or inline declaration, seen as a sequence of instructions. By default, the
  insertion is performed at the last position of the sequence.
  
  \<^descr> \<^verbatim>\<open>disable_negation\<close>
  \<^bold>\<open>(at \<^theory_text>\<open>pml_proc_inl\<close>)\<close> declares that no negations of asserts $\<^verbatim>\<open>assert\<close>^\text{PML}$ will occur
  inside \<^theory_text>\<open>pml_proc_inl\<close>.
\<close>

subsectionX \<open>Generating a Test File\<close>

text' \<open>
To generate a $\mathcal{C}$ test file, we propose two independent approaches: the uniform refinement and the generic
refinement. The two approaches can be executed separately or both at the same time, so we could end
up with at most two generated $\mathcal{C}$ files.
\<close>

paragraphX \<open>Main Commands\<close>

text' \<open>
  \<^descr> \<^verbatim>\<open>export_code\<close> \<^theory_text>\<open>name\<close>
  \<^bold>\<open>(globally)\<close> declares to keep the $\mathcal{C}$ test file inside the location
  specified by \<^verbatim>\<open>export_dir\<close> and stored in the file-name
  \<^theory_text>\<open>name\<close>.
  
  If this option is not present, the content of all files which were meant to be saved on the
  file-system are instead discarded (irrespective of the presence of
  \<^verbatim>\<open>refine_uniform\<close> or \<^verbatim>\<open>refine_generic\<close>).
\<close>

subsubsectionX \<open>Uniform Refinement\<close>

text' \<open>
The \<^emph>\<open>uniform refinement\<close> approach gets activated when at least one occurrence
of the main commands below is used.
\<close>

paragraphX \<open>Main Commands\<close>

text' \<open>
  \<^descr> \<^verbatim>\<open>refine_uniform\<close> \<^theory_text>\<open>c_content\<close>
  \<^bold>\<open>(at \<^theory_text>\<open>pml_proc_inl\<close>)\<close> declares the $\mathcal{C}$ code
  \<^theory_text>\<open>c_content\<close> as code to be printed whenever
  \<^theory_text>\<open>pml_proc_inl\<close> appears in the counter-example generation.

  \<^descr> \<^verbatim>\<open>refine_uniform_force\<close>
  \<^bold>\<open>(globally)\<close> declares that all encountered proctype or inline declaration
  will receive a generated $\<^verbatim>\<open>printf\<close>^\text{PML}$ (encapsulated inside an
  $\<^verbatim>\<open>atomic\<close>^\text{PML}$, depending on
  \<^verbatim>\<open>no_atomic\<close>). By default, a
  $\<^verbatim>\<open>printf\<close>^\text{PML}$ is generated for a
  \<^theory_text>\<open>pml_proc_inl\<close> declaration only if there is a
  \<^verbatim>\<open>refine_uniform\<close> command associated to that declaration.
\<close>

text' \<open>
The uniform refinement approach inserts several uniform printing markers at key positions in the
input model received by \<^verbatim>\<open>model_checker_verifier\<close>. In return, it extracts from
the output of \<^verbatim>\<open>model_checker_trail\<close> a uniform list $L_{\text{cmd}}$ of
annotated attribute commands. All attribute commands are uniform in that they are composed of the
same command identifier, and only differing in their command arguments. In particular, from these
arguments we can retrieve a current \<^theory_text>\<open>c_content\<close> to print, earlier
declared by a corresponding \<^verbatim>\<open>refine_uniform\<close>. Ultimately, the sequence
order of \<^theory_text>\<open>c_content\<close> is reflecting how elements in $L_{\text{cmd}}$ have
been arranged. This makes the order of $L_{\text{cmd}}$ important, and specially taken in charge by
the generation process.
\<close>

text' \<open>
Operationally, it is not \<^theory_text>\<open>c_content\<close> which will be printed, but a
``preprocessed'' version of \<^theory_text>\<open>c_content\<close>: any directives
\<^verbatim>\<open>#refine\<close> appearing in \<^theory_text>\<open>c_content\<close> will
ultimately be rewritten to some equivalent generated $\mathcal{C}$ code. Other directives are left untouched, so
the generated code might again contain ``more legal'' $\mathcal{C}$ directives. However if the rewriting of a
\<^verbatim>\<open>#refine\<close> is failing for some reasons, then that particular
\<^verbatim>\<open>#refine\<close> line will be left untouched, and printed as it is in the output.
  
In more details, \<^verbatim>\<open>#refine\<close> has the same semantics as
\<^verbatim>\<open>#define\<close> when applied to ground values\<^footnote>\<open>The declaration
of functional macros is not yet supported by \<^verbatim>\<open>#refine\<close>.\<close>, except
that the right hand side (RHS) of the replacement rule is not a static list of $\mathcal{C}$ tokens, but an
interpreted \<^emph>\<open>antiquotation\<close>. This RHS is syntactically of the form:
  \<^descr> \<^verbatim>\<open>[["\<close>$ty_{\text{name}}$\<^verbatim>\<open>",\<close> $ty_{\text{arity}}$\<^verbatim>\<open>], "\<close>$var_{\text{pml}}$\<^verbatim>\<open>"]\<close>
\<close>

text' \<open>
where
\<^item> $var_{\text{pml}}$ is the name of the variable referring to one of the arguments taken by
\<^theory_text>\<open>pml_proc_inl\<close>,
\<^item> $ty_{\text{name}}$ is the type of $var_{\text{pml}}$,
\<^item> $ty_{\text{arity}}$ is \<^verbatim>\<open>null\<close> in case $var_{\text{pml}}$ is a
Promela scalar. Otherwise, it is a positive integer of at most the size of the array
$ty_{\text{name}}$. More details on types will be provided below.
\<close>

text' \<open>
Furthermore, some respective lines of \<^verbatim>\<open>#undef\<close> are appended in the end of
\<^theory_text>\<open>c_content\<close>. For example, if \<^theory_text>\<open>c_content\<close>
is of the form:
  \<^descr> \<^verbatim>\<open>#refine\<close>~$\<^verbatim>\<open>x\<close>_1$~\<^verbatim>\<open>[["\<close>$ty1_{\text{name}}$\<^verbatim>\<open>",\<close> $ty1_{\text{arity}}$\<^verbatim>\<open>], "\<close>$\<^theory_text>\<open>var\<close>_1$\<^verbatim>\<open>"]\<close>
  \<^descr> \<^verbatim>\<open>#refine\<close>~$\<^verbatim>\<open>x\<close>_2$~\<^verbatim>\<open>[["\<close>$ty2_{\text{name}}$\<^verbatim>\<open>",\<close> $ty2_{\text{arity}}$\<^verbatim>\<open>], "\<close>$\<^theory_text>\<open>var\<close>_2$\<^verbatim>\<open>"]\<close>
  \<^descr> \<^verbatim>\<open>#refine\<close>~$\<^verbatim>\<open>x\<close>_3$~\<^verbatim>\<open>[["\<close>$ty3_{\text{name}}$\<^verbatim>\<open>",\<close> $ty3_{\text{arity}}$\<^verbatim>\<open>], "\<close>$\<^theory_text>\<open>var\<close>_3$\<^verbatim>\<open>"]\<close>
  \<^descr> \<^verbatim>\<open>//\<close>~code
\<close>

(*
text' \<open>
``\<^verbatim>\<open>\\<close>\<^verbatim>\<open><^\<close>\<^theory_text>\<open>lang\<close>\<^verbatim>\<open>>\<close>\isa{{\isasymopen}}\<^theory_text>\<open>var\<close>\isa{{\isasymclose}}''\<^footnote>\<open>Note
that, without abbreviations, we obtain:
``\<^verbatim>\<open>\\<close>\<^verbatim>\<open><^\<close>\<^theory_text>\<open>lang\<close>\<^verbatim>\<open>>\<close>\<^verbatim>\<open>\\<close>\<^verbatim>\<open><open>\<close>\<^theory_text>\<open>var\<close>\<^verbatim>\<open>\\<close>\<^verbatim>\<open><close>\<close>''.\<close>
where:
\begin{itemize}
  \item \<^theory_text>\<open>lang\<close> is the name of the programming language inside which
    \<^theory_text>\<open>var\<close> is written. At the time of writing, this language is always
    the same as the language used to define \<^theory_text>\<open>pml_proc_inl\<close>.

    For the case of Promela, \<^theory_text>\<open>lang\<close> is written as
    ``\<^verbatim>\<open>promela\<close>'' (making the overall RHS expression starting with:
    ``\<^verbatim>\<open>\\<close>\<^verbatim>\<open><^promela>\<close>'').
    
    For readability reasons, in the remaining part of the document, symbols of the form
    ``\<^verbatim>\<open>\\<close>\<^verbatim>\<open><^promela>\<close>'' will be depicted as
    {\isacommand{promela}}.
  \item \<^theory_text>\<open>var\<close> is the name of the variable --- syntactically written in
    \<^theory_text>\<open>lang\<close> --- referring to one of the arguments taken by
    \<^theory_text>\<open>pml_proc_inl\<close>.
\end{itemize}
Furthermore, some respective lines of \<^verbatim>\<open>#undef\<close> are appended in the end of
\<^theory_text>\<open>c_content\<close>. For example, if \<^theory_text>\<open>c_content\<close>
is of the form:
  \<^descr> \<^verbatim>\<open>#refine\<close>~$\<^verbatim>\<open>x\<close>_1$~{\isacommand{promela}}\isa{{\isasymopen}}$\<^theory_text>\<open>var\<close>_1$\isa{{\isasymclose}}
  \<^descr> \<^verbatim>\<open>#refine\<close>~$\<^verbatim>\<open>x\<close>_2$~{\isacommand{promela}}\isa{{\isasymopen}}$\<^theory_text>\<open>var\<close>_2$\isa{{\isasymclose}}
  \<^descr> \<^verbatim>\<open>#refine\<close>~$\<^verbatim>\<open>x\<close>_3$~{\isacommand{promela}}\isa{{\isasymopen}}$\<^theory_text>\<open>var\<close>_3$\isa{{\isasymclose}}
  \<^descr> \<^verbatim>\<open>//\<close>~code
\<close>
*)
(*
text' \<open>
\begin{gather*}
  \begin{tabular}{c}
    \<^verbatim>\<open>#refine\<close>~$\<^verbatim>\<open>x\<close>_1$~{\isacommand{promela}}\isa{{\isasymopen}}$\<^theory_text>\<open>var\<close>_1$\isa{{\isasymclose}} \\
    \<^verbatim>\<open>#refine\<close>~$\<^verbatim>\<open>x\<close>_2$~{\isacommand{promela}}\isa{{\isasymopen}}$\<^theory_text>\<open>var\<close>_2$\isa{{\isasymclose}} \\
    \<^verbatim>\<open>#refine\<close>~$\<^verbatim>\<open>x\<close>_3$~{\isacommand{promela}}\isa{{\isasymopen}}$\<^theory_text>\<open>var\<close>_3$\isa{{\isasymclose}} \\
    \<^verbatim>\<open>//\<close>~code
  \end{tabular}
\end{gather*}
\<close>
*)
text' \<open>
we will get as output:
  \<^descr> \<^verbatim>\<open>#define\<close>~$\<^verbatim>\<open>x\<close>_1$~$\<^verbatim>\<open>value\<close>_1$
  \<^descr> \<^verbatim>\<open>#define\<close>~$\<^verbatim>\<open>x\<close>_2$~$\<^verbatim>\<open>value\<close>_2$
  \<^descr> \<^verbatim>\<open>#define\<close>~$\<^verbatim>\<open>x\<close>_3$~$\<^verbatim>\<open>value\<close>_3$
  \<^descr> \<^verbatim>\<open>//\<close>~code
  \<^descr> \<^verbatim>\<open>#undef\<close>~$\<^verbatim>\<open>x\<close>_1$
  \<^descr> \<^verbatim>\<open>#undef\<close>~$\<^verbatim>\<open>x\<close>_2$
  \<^descr> \<^verbatim>\<open>#undef\<close>~$\<^verbatim>\<open>x\<close>_3$
\<close>
(*
text' \<open>
\begin{gather*}
  \begin{tabular}{c}
    \<^verbatim>\<open>#define\<close>~$\<^verbatim>\<open>x\<close>_1$~$\<^verbatim>\<open>value\<close>_1$ \\
    \<^verbatim>\<open>#define\<close>~$\<^verbatim>\<open>x\<close>_2$~$\<^verbatim>\<open>value\<close>_2$ \\
    \<^verbatim>\<open>#define\<close>~$\<^verbatim>\<open>x\<close>_3$~$\<^verbatim>\<open>value\<close>_3$ \\
    \<^verbatim>\<open>//\<close>~code \\
    \<^verbatim>\<open>#undef\<close>~$\<^verbatim>\<open>x\<close>_1$ \\
    \<^verbatim>\<open>#undef\<close>~$\<^verbatim>\<open>x\<close>_2$ \\
    \<^verbatim>\<open>#undef\<close>~$\<^verbatim>\<open>x\<close>_3$
  \end{tabular}
\end{gather*}
\<close>
*)
text' \<open>
assuming that $\<^theory_text>\<open>var\<close>_1$, $\<^theory_text>\<open>var\<close>_2$, and
$\<^theory_text>\<open>var\<close>_3$ are all appearing as either global variables or local
variables of \<^theory_text>\<open>pml_proc_inl\<close>. In return,
$\<^verbatim>\<open>value\<close>_1$, $\<^verbatim>\<open>value\<close>_2$ and
$\<^verbatim>\<open>value\<close>_3$ respectively represent the \<^emph>\<open>serialized\<close>
values received by \<^theory_text>\<open>pml_proc_inl\<close>. These values are automatically
computed, serialized and printed by $\mathcal{M}$ during the counter-example simulation phase.

To serialize values $var$, the tool must know their types. At the time of writing, the type
inference process that our tool is performing is rather trivial: it tries to retrieve the types of
values by looking at the nearest proctype declaration. If the proctype declaration can not be found,
or for parameters of inline declarations or any other global variables, their types $typ$ have to be
manually provided, using the syntax mentioned above.
\<close>
(*
text' \<open>
using the syntax:
  \<^descr> \<^verbatim>\<open>@{promela ["\<close>$typ$\<^verbatim>\<open>"]\<close>~\isa{{\isasymopen}}$var$\isa{{\isasymclose}}\<^verbatim>\<open>}\<close>
\<close>
*)

text' \<open>
If the type of $var$ is not ground (e.g. such as the channel type
$\<^verbatim>\<open>chan\<close>$), some warning or error messages are raised with a default value
printed instead for that variable.

The serialization of arrays is supported if we manually provide its size. Note that, for the case of
arrays, we might obtain several expanded lines of \<^verbatim>\<open>#define\<close> and
\<^verbatim>\<open>#undef\<close> behind a single line of \<^verbatim>\<open>#refine\<close>.
\<close>

(*
text' \<open>
The serialization of arrays is supported if we provide its size using the syntax
``$typ$\<^verbatim>\<open>[\<close>$int$\<^verbatim>\<open>]\<close>'', where $int$ is a number (not
a variable). Note that, for the case of arrays, we might obtain several expanded lines of
\<^verbatim>\<open>#define\<close> and \<^verbatim>\<open>#undef\<close> behind a single line of
\<^verbatim>\<open>#refine\<close>.
\<close>
*)

subsubsectionX \<open>Generic Refinement\<close>

text' \<open>
The \<^emph>\<open>generic refinement\<close> approach gets activated when at least one occurrence
of the main command below is used.
\<close>

paragraphX \<open>Main Command\<close>

text' \<open>
  \<^descr> \<^verbatim>\<open>refine_generic\<close> \<^theory_text>\<open>yaml_content\<close>
  \<^bold>\<open>(globally)\<close> declares the YAML refinement data
  \<^theory_text>\<open>yaml_content\<close> as data to be used as initializer for the computation
  described below.
\<close>

text' \<open>
The generic refinement approach assumes that one can extract from the output of
\<^verbatim>\<open>model_checker_trail\<close> a list $L_{\text{cmd}}$ of annotated generic commands
to execute. Each generic command $cmd$ in $L_{\text{cmd}}$ is then executed one by
one. Additionally, each $cmd_i$ is taking as parameter a $state_i$ value, where $state_i$ is the
result produced by $cmd_{i-1}$ when applied with $state_{i-1}$ as argument, except that the first
element of $L_{\text{cmd}}$ is applied with an initializing value computed from
\<^theory_text>\<open>yaml_content\<close>.

Ultimately, we can retrieve from the last computed $state$ value some final $\mathcal{C}$ code to print.
\<close>

paragraphX \<open>Warning: Evaluation Order\<close>

text' \<open>
As long as \<^theory_text>\<open>yaml_content\<close> has been provided once, our tool automatically
computes each appropriate $state$ value, and ensures that each one gets correctly provided to a
corresponding $cmd$. End-users do not have to manually provide these $state$ values. However, there
is no automated check performed on the initial list $L_{\text{cmd}}$ of generic commands to execute,
especially regarding the order of its elements.

At the time of writing, the following generic commands are recognized, the more detailed
documentation of the commands and how to invoke them is provided in
\<^file>\<open>FV2-201/src/Promela_to_C/document/TestGeneration.md\<close>:
\<^item> \<^emph>\<open>pid\<close> \<^verbatim>\<open>INIT\<close>
\<^item> \<^emph>\<open>cid\<close> \<^verbatim>\<open>TASK\<close> \<^emph>\<open>tid\<close> \<^emph>\<open>pid\<close>
\<^item> \<^emph>\<open>pid\<close> \<^verbatim>\<open>NAME\<close> \<^emph>\<open>name\<close>
\<^item> \<^emph>\<open>pid\<close> \<^verbatim>\<open>DEF\<close> \<^emph>\<open>name\<close> \<^emph>\<open>value\<close>
\<^item> \<^emph>\<open>pid\<close> \<^verbatim>\<open>DECL\<close> \<^emph>\<open>typ\<close> \<^emph>\<open>name\<close>
\<^item> \<^emph>\<open>pid\<close> \<^verbatim>\<open>DECL\<close> \<^emph>\<open>typ\<close> \<^emph>\<open>name\<close> \<^emph>\<open>value\<close>
\<^item> \<^emph>\<open>pid\<close> \<^verbatim>\<open>DCLARRAY\<close> \<^emph>\<open>typ\<close> \<^emph>\<open>name\<close> \<^emph>\<open>value\<close>
\<^item> \<^emph>\<open>pid\<close> \<^verbatim>\<open>PTR\<close> \<^emph>\<open>name\<close> \<^emph>\<open>value\<close>
\<^item> \<^emph>\<open>pid\<close> \<^verbatim>\<open>CALL\<close> \<^emph>\<open>name\<close> \<open>[...]\<close>
\<^item> \<^emph>\<open>pid\<close> \<^verbatim>\<open>STRUCT\<close> \<^emph>\<open>name\<close>
\<^item> \<^emph>\<open>pid\<close> \<^verbatim>\<open>SEQ\<close> \<^emph>\<open>name\<close>
\<^item> \<^emph>\<open>pid\<close> \<^verbatim>\<open>END\<close> \<^emph>\<open>name\<close>
\<^item> \<^emph>\<open>pid\<close> \<^verbatim>\<open>SCALAR\<close> \<^verbatim>\<open>_\<close> \<^emph>\<open>value\<close>
\<^item> \<^emph>\<open>pid\<close> \<^verbatim>\<open>SCALAR\<close> \<^emph>\<open>name\<close> \<^emph>\<open>value\<close>
\<^item> \<^emph>\<open>pid\<close> \<^verbatim>\<open>SCALAR\<close> \<^emph>\<open>name\<close> \<^emph>\<open>value\<close> \<^emph>\<open>index\<close>
\<^item> \<^emph>\<open>pid\<close> \<^verbatim>\<open>STATE\<close> \<^emph>\<open>tid\<close> \<^emph>\<open>state\<close>
\<^item> \<^emph>\<open>pid\<close> \<^verbatim>\<open>LOG\<close> \<open>[...]\<close>
\<close>

text' \<open>
Note that \<^verbatim>\<open>_\<close> denotes a syntactic constant symbol, and \<open>[...]\<close>
represents a variadic list of arguments. Also, all generic commands are acting on the
\<^bold>\<open>(globally)\<close> level.
\<close>

subsubsectionX \<open>Optional Commands\<close>

text' \<open>
  \<^descr> \<^verbatim>\<open>enclose\<close> \<^theory_text>\<open>cts1_header\<close> \<^theory_text>\<open>cts2_footer\<close>
  \<^bold>\<open>(globally)\<close> declares that \<^theory_text>\<open>cts1_header\<close> will be printed as header and
  \<^theory_text>\<open>cts2_footer\<close> as footer. Multiple \<^verbatim>\<open>enclose\<close>
  commands do affect the nested generation order: if we encounter later another
  \<^verbatim>\<open>enclose\<close> \<^theory_text>\<open>cts1_header'\<close>
  \<^theory_text>\<open>cts2_footer'\<close>, then we will ultimately get as printed content:
  \<^theory_text>\<open>cts1_header\<close>, \<^theory_text>\<open>cts1_header'\<close>, $\dots$ ,
  \<^theory_text>\<open>cts2_footer'\<close>, \<^theory_text>\<open>cts2_footer\<close>.

  \<^descr> \<^verbatim>\<open>enclose_uniform\<close> \<^theory_text>\<open>cts1_header\<close> \<^theory_text>\<open>cts2_footer\<close>
  \<^bold>\<open>(globally)\<close> has the same semantics as \<^verbatim>\<open>enclose\<close>
  \<^theory_text>\<open>cts1_header\<close> \<^theory_text>\<open>cts2_footer\<close> except that
  all contents included by \<^verbatim>\<open>enclose_uniform\<close> appear nested inside any
  contents that are ever inserted by \<^verbatim>\<open>enclose\<close>. Additionally,
  \<^verbatim>\<open>enclose_uniform\<close> is only used in the uniform refinement approach.

  \<^descr> \<^verbatim>\<open>refine_uniform_log\<close>
  \<^bold>\<open>(globally)\<close> declares that an additional $\mathcal{C}$ comment will be placed near each $\mathcal{C}$ function being generated. Each
  comment contains the name of the \<^theory_text>\<open>pml_proc_inl\<close> declaration at the
  origin of the $\mathcal{C}$ function produced in output.

  \<^descr> \<^verbatim>\<open>refine_uniform_strip\<close>
  \<^bold>\<open>(globally)\<close> declares to remove any newlines surrounding
  \<^theory_text>\<open>c_content\<close> (in \<^verbatim>\<open>refine_uniform\<close>).
\<close>

subsectionX \<open>Generating a Project Directory\<close>

subsubsectionX \<open>Main Command\<close>

text' \<open>
  \<^descr> \<^verbatim>\<open>export_dir\<close> \<^theory_text>\<open>dir\<close>
  \<^bold>\<open>(globally)\<close> declares \<^theory_text>\<open>dir\<close> as the main directory for any code generated by the
  tool.
  
  If this option is not present, the content of all files which were meant to be saved on the
  file-system are instead printed on the standard output.
\<close>

subsubsectionX \<open>Optional Commands\<close>

text' \<open>
  \<^descr> \<^verbatim>\<open>export_input_yaml\<close> \<^theory_text>\<open>dir\<close>
  \<^bold>\<open>(globally)\<close> declares to export all command arguments in YAML format within
  specific annotation comments. Each argument will be exported to a file inside the directory
  \<^theory_text>\<open>dir\<close>, which will itself be created inside the directory specified by
  \<^verbatim>\<open>export_dir\<close>.

  \<^descr> \<^verbatim>\<open>export_input_only_content\<close>
  \<^bold>\<open>(globally)\<close> declares to not include annotation comments while exporting the
  data specified in \<^verbatim>\<open>export_input_yaml\<close>.

  \<^descr> \<^verbatim>\<open>export_pml\<close> \<^theory_text>\<open>name\<close>
  \<^bold>\<open>(globally)\<close> declares to keep any intermediate generated promela models
  inside the location specified by \<^verbatim>\<open>export_dir\<close> and stored in the file-name
  \<^theory_text>\<open>name\<close>.

  If this option is not present, the content of all files which were meant to be saved on the
  file-system are instead discarded.
  \<^descr> \<^verbatim>\<open>export_trail\<close> \<^theory_text>\<open>name\<close>
  \<^bold>\<open>(globally)\<close> declares to keep any intermediate generated output of
  \<^verbatim>\<open>model_checker_trail\<close> inside the location specified by
  \<^verbatim>\<open>export_dir\<close> and stored in the file-name \<^theory_text>\<open>name\<close>. It is only the human readable version which is saved (not
  the default binary file).

  If this option is not present, the content of all files which were meant to be saved on the
  file-system are instead discarded.
\<close>

subsectionX \<open>Checking Input Format\<close>

subsubsectionX \<open>Main Command\<close>

text' \<open>
  \<^descr> \<^verbatim>\<open>check_unparse_parse\<close>
  \<^bold>\<open>(globally)\<close> declares to serialize all (parsed)
  arguments provided to the program as input, and parse the resulting
  string. Afterwards, a comparison is made to check that the initial
  arguments and new ones are equal, and raise errors in case of
  mismatch.
\<close>

subsectionX \<open>Derivative Forms\<close>

subsubsectionX \<open>Positional Reference\<close>

text' \<open>
  \<^descr> \<^theory_text>\<open>cmd\<close>\<^verbatim>\<open>_at\<close> $\<^theory_text>\<open>arg\<close>_0$ $\<^theory_text>\<open>arg\<close>_1$ $\dots$ $\<^theory_text>\<open>arg\<close>_n$
  has the same semantics as ``\<^theory_text>\<open>cmd\<close>
  $\<^theory_text>\<open>arg\<close>_1$ $\dots$ $\<^theory_text>\<open>arg\<close>_n$ \<^bold>\<open>(at $\<^theory_text>\<open>arg\<close>_0$)\<close>'', except for
  commands \<^theory_text>\<open>cmd\<close> expecting to refer to a
  \<^theory_text>\<open>pml_proc_inl\<close> declaration. For these commands, it is no more
  mandatory that their positions have to be situated in the same line as a corresponding
  \<^theory_text>\<open>pml_proc_inl\<close>. Instead, $\<^theory_text>\<open>arg\<close>_0$ is
  specially used to indicate which declaration the command is referring to. This makes the writing
  of the annotation command possible to happen anywhere on a file.
  
  Since we assume for the moment being restricted to the use of Promela models not permitting
  redefinition of declarations, without loss of flexibility, the definition of an annotation can in
  this case also occur before the actual proper definition of the declaration.

  Non-exhaustive examples of \<^theory_text>\<open>cmd\<close>\<^verbatim>\<open>_at\<close>
  commands include \<^verbatim>\<open>refine_uniform_at\<close>, or
  \<^verbatim>\<open>no_printf_at\<close>.
\<close>

subsubsectionX \<open>Content as File\<close>

text' \<open>
  \<^descr> \<^theory_text>\<open>cmd\<close>\<^verbatim>\<open>_file\<close> $\<^theory_text>\<open>arg\<close>_1$ $\dots$ $\<^theory_text>\<open>arg\<close>_n$
  has the same semantics as ``\<^theory_text>\<open>cmd\<close>
  $\<^theory_text>\<open>arg'\<close>_1$ $\dots$ $\<^theory_text>\<open>arg'\<close>_n$'', where
  $\<^theory_text>\<open>arg'\<close>_k$ is the whole content of the file stored at path
  $\<^theory_text>\<open>arg\<close>_k$.

  If the path $\<^theory_text>\<open>arg\<close>_k$ is not an absolute path, then it is considered
  to be relative to the input resource from where the command
  \<^theory_text>\<open>cmd\<close>\<^verbatim>\<open>_file\<close> was read before the test
  generation program started. This leads to two situations:
    \<^enum> If \<^theory_text>\<open>cmd\<close>\<^verbatim>\<open>_file\<close> was read from a
    file, then the resolving of any relative links of commands inside the file is straightforward,
    based on the path of that file.
    \<^enum> If \<^theory_text>\<open>cmd\<close>\<^verbatim>\<open>_file\<close> was provided
    through the shell option \<^verbatim>\<open>--promela\<close> to the test generation program,
    then the base directory taken as starting directory for relative path resolving is the directory
    where the user has executed that program (not necessarily the program's directory).
  
  As a non-exhaustive example of commands particularly using the referencing of content through
  file, we can cite \<^verbatim>\<open>enclose_file\<close>.
\<close>

subsubsectionX \<open>Positional Reference and Content as File\<close>

text' \<open>
  \<^descr> \<^theory_text>\<open>cmd\<close>\<^verbatim>\<open>_file_at\<close> $\<^theory_text>\<open>arg\<close>_0$ $\<^theory_text>\<open>arg\<close>_1$ $\dots$ $\<^theory_text>\<open>arg\<close>_n$
  has the same semantics as ``\<^theory_text>\<open>cmd\<close>\<^verbatim>\<open>_file\<close>
  $\<^theory_text>\<open>arg\<close>_1$ $\dots$ $\<^theory_text>\<open>arg\<close>_n$ \<^bold>\<open>(at $\<^theory_text>\<open>arg\<close>_0$)\<close>'', with the
  particular use of $\<^theory_text>\<open>arg\<close>_0$ as previously mentioned (in the definition of \<^theory_text>\<open>cmd\<close>\<^verbatim>\<open>_at\<close>). Subsequently, the
  latter command has the same semantics as ``\<^theory_text>\<open>cmd\<close>
  $\<^theory_text>\<open>arg'\<close>_1$ $\dots$ $\<^theory_text>\<open>arg'\<close>_n$'' with the
  resolving of files $\<^theory_text>\<open>arg\<close>_k$ performed as previously mentioned (in the definition of \<^theory_text>\<open>cmd\<close>\<^verbatim>\<open>_file\<close>).
\<close>

(*<*)
rst_export_file

end
(*>*)
