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
theory specalgo
  imports Isabelle_Doc_reStructuredText.reStructuredText_Wrapper
begin

declare [[reStructuredText]]

comment \<open>
SPDX-License-Identifier: CC-BY-SA-4.0 OR BSD-2-Clause

Copyright (C) 2019-2021 Trinity College Dublin (www.tcd.ie)
\<close>

(*>*)

sectionX \<open>Specification of the Task: Testing the Concurrent Call of Functions from the API\<close>

subsectionX \<open>Statement of the Problem\<close>

text' \<open>
Let $f^\text{C}_1$, $\dots$, $f^\text{C}_n$ be $n$ functions written in a subset of $\text{C}$
preferably supporting concurrency, such as the C11 language.
\<close>

text' \<open>
Besides having $n$ functions, it is also assumed that these $n$ functions can be sequentially
executed in any order (thus concurrently as well), but each function can only be run without
interleaving, in \<^emph>\<open>atomic\<close> mode. How they will be ultimately ordered for final
execution is not yet determined --- i.e., this leads to at least $2^n$ possibilities of execution
paths, where unrestricted permutations remains to be counted inside the $2^n$ subsets of chosen
functions.
\<close>

text' \<open>
Given a proposition $\text{Prop}^\text{C}$ --- particularly depending on the state of the
environment immediately obtained after executing some functions $f^\text{C}_k$, arbitrary chosen
from above --- that one has meanwhile proved to be true (e.g., using an interactive theorem proving
tool, or a model-checker tool), the goal is to \<^emph>\<open>preserve the truth\<close> of
$\text{Prop}^\text{C}$ across multiple cycles of software maintenance and modifications of the
aforementioned $f^\text{C}_k$.

The idea is to generate a \<^emph>\<open>test program\<close> making the veracity of
$\text{Prop}^\text{C}$ easy to detect (e.g., computable in polynomial time) whenever $f^\text{C}_k$
is changing. This is particularly the case whenever we have a program:
\begin{itemize}
\item starting with the precise ordered sequence $S^\text{C}$ $=$ $f^\text{C}_{i_1}$, $\dots$,
  $f^\text{C}_{i_j}$
\item and ending with the assertion $\<^verbatim>\<open>assert\<close>^\text{C}$
  $\text{Prop}^\text{C}$ (or the more general form $\<^verbatim>\<open>ltl\<close>^\text{C}$
  $\text{Prop}^\text{C}$)
\end{itemize}
where:
\<^item> $i_1$, $\dots$, $i_j$ are distinct elements, chosen from the above $n$ functions such that
after executing $S^\text{C}$, a subsequent execution of $\<^verbatim>\<open>assert\<close>^\text{C}$
$\text{Prop}^\text{C}$ (resp. $\<^verbatim>\<open>ltl\<close>^\text{C}$ $\text{Prop}^\text{C}$) must
not fail.
\<close>

text' \<open>
The own design of $S^\text{C}$ is arbitrary, however the sequence is chosen to maximize the
potential of future failure of $\text{Prop}^\text{C}$ --- particularly when for various reasons, one
will have to modify the initial functions $f^\text{C}_1$, $\dots$, $f^\text{C}_n$ by hand (and
expect the property to continue to hold after the modifications).
\<close>

subsectionX \<open>Resolution: Generalities\<close>

text' \<open>
There is a particular case where getting the sequence $S^\text{C}$ is an \<^emph>\<open>easy\<close>
decidable heuristic: it is by exploiting certain characteristics of model-checker tools
$\mathcal{M}$, i.e.,
\<^enum> when $\mathcal{M}$ is \<^emph>\<open>able\<close> to return a counter-example from a
proposition we know it is false (particularly when the proposition remains simple enough for
$\mathcal{M}$ to automatically disprove it),
\<^enum> and when $S^\text{C}$ is exactly a prefix subset of the maximal non-looping part of the
above counter-example (i.e., the \<^emph>\<open>lasso handle\<close>, not the
\<^emph>\<open>lasso cycle\<close>) for which we assume that it can be automatically obtained when
one is trying to prove that $\neg \text{Prop}^\text{C}$ does not hold.
\<^enum> Note that instead of reasoning with $S^\text{C}$ and $\text{Prop}^\text{C}$, we can assume
instead being reasoning for the moment with $S^\text{PML}$ $=$ $f^\text{PML}_{i_1}$, $\dots$,
$f^\text{PML}_{i_j}$ and $\text{Prop}^\text{PML}$, where $\text{PML}$ designates the Promela
modelling language, and where each respective functions $f^\text{PML}_1, \dots, f^\text{PML}_n$ are
assumed to be for the moment \<open>reasonably equivalent\<close> to their counterpart functions
defined in C. In the remaining, this equivalence relation will be denoted as
$\mathcal{R}^{\text{C} \leftrightarrow \text{PML}}$, this leads to:
\begin{gather*}
\begin{tabular}{ccc}
  $f^\text{C}_{k}$ & $\mathcal{R}^{\text{C} \leftrightarrow \text{PML}}$ & $f^\text{PML}_{k}$ \\
  $\text{Prop}^\text{C}$ & $\mathcal{R}^{\text{C} \leftrightarrow \text{PML}}$ &
  $\text{Prop}^\text{PML}$ \\
  $\<^verbatim>\<open>assert\<close>^\text{C}$ & $\mathcal{R}^{\text{C} \leftrightarrow \text{PML}}$ & $\<^verbatim>\<open>assert\<close>^\text{PML}$ \\
  $\<^verbatim>\<open>ltl\<close>^\text{C}$ & $\mathcal{R}^{\text{C} \leftrightarrow \text{PML}}$ & $\<^verbatim>\<open>ltl\<close>^\text{PML}$ \\
\end{tabular}
\end{gather*}
\<close>

text' \<open>
In this task, we assume to be in the ideal setting satisfying all above points, i.e., where
$\mathcal{M}$ is able to compute $S^\text{PML}$. In particular, $\neg \text{Prop}^\text{PML}$ has
to be simple enough for the generation of the counter-example by $\mathcal{M}$ be possible.
\<close>

text' \<open>
The resolution proceeds as follows: while querying $\mathcal{M}$ with $\neg
\text{Prop}^\text{PML}$ in input, we can obtain in output a \<^emph>\<open>text explaining\<close>
how $S^\text{PML}$ is constituted with --- among other --- a \<^emph>\<open>line explaining\<close>
why $\neg \text{Prop}^\text{PML}$ is \<^bold>\<open>not\<close> satisfied after executing
$S^\text{PML}$. As a consequence, the sequence $S^\text{C}$ can be obtained by having an automated
way of analyzing the output of $\mathcal{M}$ to keep (resp. remove) any crucial (resp. superfluous)
information (that part is done after first reconstituting $S^\text{PML}$).
\<close>

text' \<open>
To get $S^\text{C}$, we present several equivalent possibilities:
\begin{itemize}
\item writing the printing in the model-checker $\mathcal{M}$ (through an option to be activated
  while treating Promela models),
\item or writing the printing in the Promela model (to be independently and abstractly executed by
  the model-checker).
\end{itemize}
In both cases, any information that are usually printed by $\mathcal{M}$ and not part of the C
language must be either not printed, or allowed to be printed but only inside an escaping C comment.
\<close>

subsectionX \<open>Computation of $S^\text{C}$: Printing in the Model-Checker\<close>

paragraphX \<open>Procedure\<close>

text' \<open>
This solution consists to modify the source of our model-checker $\mathcal{M}$ for it to exactly
print in output $S^\text{C}$, i.e., using several instructions
\begin{gather*}
  \begin{tabular}{c}
    $\<^verbatim>\<open>printf\<close>^\mathcal{M}$ \<open>\<langle>\<close>$\text{code}^\text{C}_{i_1}$\<open>\<rangle>\<close>\\
    $\vdots$\\
    $\<^verbatim>\<open>printf\<close>^\mathcal{M}$ \<open>\<langle>\<close>$\text{code}^\text{C}_{i_j}$\<open>\<rangle>\<close>
  \end{tabular}
\end{gather*}
\<close>

paragraphX \<open>Shortcomings\<close>

text' \<open>
\<^item> For this solution to be generic and to not depend on the back-end language, we can write
``$\<^verbatim>\<open>printf\<close>^\mathcal{M}$ $\text{code}^\mathcal{M}_{k}$'' instead of
``$\<^verbatim>\<open>printf\<close>^\mathcal{M}$
\<open>\<langle>\<close>$\text{code}^\text{C}_{k}$\<open>\<rangle>\<close>'' and let
$\text{code}^\mathcal{M}_{k}$ be abstractly provided while parsing the Promela model, e.g., inside
some appropriate annotated Promela comments.
\<^item> This solution implies to modify the source of all model-checking tools $\mathcal{M}$ that
are ever used.
\<close>

subsectionX \<open>Computation of $S^\text{C}$: Printing in the Model\<close>

paragraphX \<open>Procedure\<close>

text' \<open>
This solution consists to modify the source of our Promela model for it to exactly print in output
$S^\text{C}$, i.e., using several instructions
\begin{gather*}
  \begin{tabular}{c}
    $\<^verbatim>\<open>printf\<close>^\text{PML}$ \<open>\<langle>\<close>$\text{code}^\text{C}_{i_1}$\<open>\<rangle>\<close>\\
    $\vdots$\\
    $\<^verbatim>\<open>printf\<close>^\text{PML}$ \<open>\<langle>\<close>$\text{code}^\text{C}_{i_j}$\<open>\<rangle>\<close>
  \end{tabular}
\end{gather*}
\<close>

paragraphX \<open>Shortcomings\<close>

text' \<open>
For a reconstitution be faithful, i.e. later useful for testing activities, the order of all
executed $\<^verbatim>\<open>printf\<close>^\text{PML}$ in output is important and must exactly
match the order of Promela instructions that were actually executed by the model-checker. In
particular, due to the concurrent nature of Promela code, one way to ensure that property is by
encapsulating each $\<^verbatim>\<open>printf\<close>^\text{PML}$ and Promela instructions of
interest together inside an indivisible $\<^verbatim>\<open>atomic\<close>^\text{PML}$ block.
\<close>

subsectionX \<open>Computation of $S^\text{C}$: Reconstitution\<close>

text' \<open>
Ultimately, $S^\text{C}$ can be reconstituted from the sequential processing of each
\<open>\<langle>\<close>$\text{code}^\text{C}_{k}$\<open>\<rangle>\<close>.
\<close>

subsectionX \<open>Implementation of $\<^verbatim>\<open>assert\<close>^\text{C}$, $\<^verbatim>\<open>ltl\<close>^\text{C}$ and Computation of $\text{Prop}^\text{C}$\<close>

text' \<open>
Starting from $\text{Prop}^\text{PML}$, there are little restrictions on how one can generate a
proposition $\text{Prop}^\text{C}$ representing the initial one of Promela (i.e., which C
constructors allowed to use or not in $\text{Prop}^\text{C}$). The fundamental requirement of
interest here is to make the following properties always satisfied:
\<^item> if $\mathcal{M}$ proves $\text{Prop}^\text{PML}$ to be true, then there exists a
convincing proof that the execution of $\<^verbatim>\<open>assert\<close>^\text{C}$
$\text{Prop}^\text{C}$ and the execution of $\<^verbatim>\<open>assert\<close>^\text{C}$ $(0
\<^verbatim>\<open>==\<close> 0)$ are behaviorly similar.
\<^item> $\mathcal{M}$ proves $\neg \text{Prop}^\text{PML}$ to be true if and only if there exists
a convincing proof that the execution of $\<^verbatim>\<open>assert\<close>^\text{C}$
$\text{Prop}^\text{C}$ and the execution of $\<^verbatim>\<open>assert\<close>^\text{C}$ $(0
\<^verbatim>\<open>!=\<close> 0)$ are behaviorly similar.
\<^item> The above points are all respectively established for
$\<^verbatim>\<open>ltl\<close>^\text{C}$.
\<close>

text' \<open>
Consequently, the own implementation of $\<^verbatim>\<open>assert\<close>^\text{C}$ and
$\<^verbatim>\<open>ltl\<close>^\text{C}$ (in C) can be arbitrary as well, as long as the above
properties are satisfied. Its code would nevertheless have a close resemblance with the part
implementing $\<^verbatim>\<open>assert\<close>^\text{PML}$ and
$\<^verbatim>\<open>ltl\<close>^\text{PML}$.
\<close>

subsectionX \<open>Appendix: Relaxing the Atomic Constraint\<close>

text' \<open>
Instead of relaxing the atomic requirement, one can always reduce the number of instructions that a
function has inside an $\<^verbatim>\<open>atomic\<close>^\text{PML}$ bloc, and subsume this part to
task 1.
\<close>

(*<*)
rst_export_file

end
(*>*)
