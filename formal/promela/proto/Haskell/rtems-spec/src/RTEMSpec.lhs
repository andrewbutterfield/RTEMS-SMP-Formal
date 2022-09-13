\section{RTEMS Specifications}
\begin{code}
module RTEMSpec
    ( whatAmI
    ) where

whatAmI :: String
whatAmI =  "Models of RTEMS Specifications"
\end{code}


The new RTEMS Software Engineering manual describes
a way to specify a wide range of RTEMS artefacts.
Here we model that specification mechanism,
in order to:
\begin{itemize}
  \item better understand what it does;
  \item get a grip on its complexity; and
  \item form a basis for tools that can process and generate it.
\end{itemize}
We base this on the RTEMS Software Engineering manual,
22nd July 2020 version,
available from
\url{https://ftp.rtems.org/pub/rtems/people/sebh/eng2.pdf}
at the time of writing.
We focus on Chapter 5, ``Software Requirements Engineering'' \RSE{5}.

\subsection{Requirements for Requirements \RSE{5.1}}

Each requirement shall have a unique identifier (UID).
This will be implemented as absolute paths
from a specification base directory (typically \texttt{spec}).
We can also define relative UIDs \RSE{5.1.1}.

For each requirement directory,
there should be a \texttt{test} sub-directory
that contains validation specifications.

We have
absolute requirements (``shall'', ``shall not''),
recommendations (``should'', ``should not''),
permissions (``may''),
and possibilities and capabilities (``can'') \RSE{5.1.2}.

The ``Easy Approach to Requirements Syntax'' (EARS) shall be used \RSE{5.1.3}.

Requirement Sentence types:
\begin{description}
  \item [Ubiquitous]
        ``The \textsf{system-name} shall \textsf{system-response}.''
  \item [Event-Driven]
        ``When \textsf{opt-precond} \textsf{trigger}
          the \textsf{system-name} shall \textsf{system-response}.''
  \item [State-Driven]
        ``While \textsf{in-state}
          the \textsf{system-name} shall \textsf{system-response}.''
  \item [Unwanted]
        ``If \textsf{opt-precond} \textsf{trigger}
          the \textsf{system-name} shall \textsf{system-response}.''
  \item [Optional]
        ``Where \textsf{feature}
          the \textsf{system-name} shall \textsf{system-response}.''
\end{description}

Requirements should be \emph{separate}\RSE{5.1.5}
and \emph{conflict-free}\RSE{5.1.6}.

Requirements should have a \emph{justification}\RSE{5.1.8},
and a \emph{validation} suite of specification items that are
either \emph{test case items} or \emph{requirement validation items}\RSE{5.1.9}.

Performance requirements will take the form of benchmarks\RSE{5.1.10}.

\newpage
\subsection{Specification Items \RSE{5.2}}

We have a hierarchy of \emph{Specification Item}s\RSE{5.2.1}.
Things lower in the hierarchy are ``refinements'' of those higher up.
We omit the \emph{Item Type} suffix here,
and replace common-substrings of subtypes by \_,
possibly with subscripts to identify parts of such strings.


\begin{tabbing}
MM \=  MM \=  MM \= MM \kill
Root: \+ \\
 Build:  \\
 \> \_-Ada-Test-Program
    \_-BSP
    \_-Config-File
    \_-Config-Hdr
    \_-Group
 \\
 \> \_-Library
    \_-Objects
    \_-Option
    \_-Script
    \_-Start-File
    \_-Test-Program
 \\
 Constraint \\
 Glossary: \\
 \> \_-Group  \_-Term
 Interface \\
 \> App-Config-Group \\
 \> App-Config${}_1$-Option${}_2$: \\
 \> \> \_${}_1$-Feature-Enable-\_${}_2$
       \_${}_1$-Feature-\_${}_2$
       \_${}_1$-Value-\_${}_2$
    \\
 \> \_-Compound
    \_-Container
    \_-Define
    \_-Domain
    \_-Enum
    \_-Enumerator
 \\
 \> \_-FwdDecl
    \_-Function
    \_-Group
    \_-Hdr-File
    \_-Macro
    \_-Typedef
 \\
 \> \_-Unspec
    \_-Variable
 \\
 Requirement${}_3$: \\
 \> Functional${}_4$-\_: \\
 \> \> Action-\_${}_3$
       Generic-\_${}_4$-\_${}_3$
 \\
 \> Non-Functional-\_
 \\
 Reqmt-Validation \\
 Specification \\
 Test-Case \\
 Test-Platform \\
 Test-Procedure \\
 Test-Suite
\end{tabbing}



All of the above are called ``specification items'',
or just ``items''\RSE{5.2.2}.
They are stored in YAML format as attributes described as key-value pairs,
with each attribute key being a \emph{Name}.

In addition to Item Types we have other types of things such as Names, etc.
For an item-type we define \emph{explicit} attributes.
All of these must be specified.

\subsubsection{Root Item Type \RSE{5.2.2.1}}

Explicit Attributes:

\begin{tabular}{|l|l|r|}
\hline
  Key (Name) & Value Type & \RSE{pageno.}
\\\hline
  \K{SPDX-License-Identifier} & SPDX License Identifier & 89
\\\hline
  \K{copyrights} & list of Copyright & 72
\\\hline
  \K{enabled-by} & Enabled-By Expression & 73
\\\hline
  \K{links} & list of Link & 84
\\\hline
  \K{type} & item type (Name) & 84
\\\hline
\end{tabular}

\subsubsection{Build Item Type \RSE{5.2.2.2}}

Refines Root (\K{type} = \V{build}).

Explicit Attributes:

\begin{tabular}{|l|l|r|}
\hline
  Key (Name) & Value Type & \RSE{pageno.}
\\\hline
  \K{build-type} & build item type (Name) & 84
\\\hline
\end{tabular}

There are quite a number of build item refinements,
and here we only consider a subset:
BSP, Config-File, and Test-Program.

\newpage
\subsubsection{Build BSP Item Type \RSE{5.2.2.4}}

Refines Build (\K{build-type}=\V{bsp})

Explicit Attributes:

\begin{tabular}{|l|l|r|}
\hline
  Key (Name) & Value Type & \RSE{pageno.}
\\\hline
  \K{arch} & string & n/a
\\\hline
  \K{bsp} & string & n/a
\\\hline
  \K{cflags} & list of Build C Compiler Option & 63
\\\hline
  \K{cppflags} & list of Build C Preprocessor Option & 63
\\\hline
  \K{family} & string & n/a
\\\hline
  \K{includes} & list of Build Include Path & 64
\\\hline
  \K{install} & list of Build Install Directive & 65
\\\hline
  \K{source} & list of Build Source & 71
\\\hline
\end{tabular}

\subsubsection{Build Configuration File Item Type \RSE{5.2.2.5}}

Refines Build (\K{build-type}=\V{config-file})

\subsubsection{Build Test Program Item Type \RSE{5.2.2.13}}

Refines Build (\K{build-type}=\V{test-program})
