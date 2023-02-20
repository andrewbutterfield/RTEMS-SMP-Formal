\section{RTEMS Thread Queues}
\begin{code}
module Queues
    ( FIFOQ
    , isEmptyFIFOQ,  viewFIFOQ,  enqueueFIFO,  dequeueFIFO
    , Priority, PRIOQ
    , isEmptyPRIOQ,  viewPRIOQ,  enqueuePRIO,  dequeuePRIO
    , Cluster, CLSTRQ
    , isEmptyCLSTRQ, viewCLSTRQ, enqueueCLSTR, dequeueCLSTR 
    ) where
\end{code}

Here we define the three types of queues used for thread synchronisation
and scheduling.

\subsection{FIFO Queues}

See \cite[\S3.5]{RTEMS:CUSER}.

We model a FIFO queue as a Haskell list,
parameterised by content object type,
with enqueue and dequeue operations, and an emptiness check.

\begin{code}
type FIFOQ obj = [obj]

isEmptyFIFOQ :: FIFOQ obj -> Bool
isEmptyFIFOQ = null

viewFIFOQ :: Show obj => FIFOQ obj -> String
viewFIFOQ = show

enqueueFIFO :: obj -> FIFOQ obj -> FIFOQ obj
enqueueFIFO thing fifoq = fifoq ++ [thing]

dequeueFIFO :: FIFOQ obj -> (obj,FIFOQ obj)
dequeueFIFO [] = error "empty FIFO queue"
dequeueFIFO (thing:restq) = (thing,restq)
\end{code}

We have a variant of a FIFO queue called round-robin (RR).

In this, the dequeue operation immediately performs an enqueue operation
with the item just dequeued.
Typically the queue is initially setup by enqueuing all desired items,
and subsequent operations consists solely of dequeing.

\begin{code}
dequeueRR :: FIFOQ obj -> (obj,FIFOQ obj)
dequeueRR [] = error "empty RR queue"
dequeueRR (thing:restq) = (thing,restq++[thing])
\end{code}

\newpage
\subsection{Priority Queues}

See \cite[\S3.5]{RTEMS:CUSER}.

We model a priority queue as a Haskell list,
parameterised by content object type,
with enqueue and dequeue operations, and an emptiness check.

\begin{code}
type Priority = Int
type PRIOQ obj = [(Priority,obj)]

isEmptyPRIOQ :: PRIOQ obj -> Bool
isEmptyPRIOQ = null

viewPRIOQ :: Show obj => PRIOQ obj -> String
viewPRIOQ = show

enqueuePRIO :: obj -> Priority -> PRIOQ obj -> PRIOQ obj
enqueuePRIO thing p [] = [(p,thing)]
enqueuePRIO thing p prioq@(first@(q,_):restq)
  | p < q      =  (p,thing) : prioq
  -- p == q, insert as per FIFO, after those of same priority (c-user 3.5)
  | otherwise  =  first     : enqueuePRIO thing p restq

dequeuePRIO :: PRIOQ obj -> ((obj,Priority),PRIOQ obj)
dequeuePRIO [] = error "empty PRIO queue"
dequeuePRIO ((p,thing):restq) = ((thing,p),restq)
\end{code}

\subsection{Clustered Scheduling Queues (SMP)}

See \cite[\S3.5,\S5.4]{RTEMS:CUSER}.

For cluster scheduling, each scheduler has its own priority queue,
and these queues are themselves placed in a global round-robin queue.

\begin{code}
type Cluster = Int
type CLSTRQ obj =  FIFOQ (Cluster,PRIOQ obj)

isEmptyCLSTRQ :: CLSTRQ obj -> Bool
isEmptyCLSTRQ = all isEmptyPRIOQ . map snd

viewCLSTRQ :: Show obj => CLSTRQ obj -> String
viewCLSTRQ = show


enqueueCLSTR :: obj -> Priority -> Cluster -> CLSTRQ obj -> CLSTRQ obj
enqueueCLSTR thing p c [] = [(c,[(p,thing)])]
enqueueCLSTR thing p c (first@(c',prioq):rest)
  | c == c'    =  (c',enqueuePRIO thing p prioq):rest
  | otherwise  =  first : enqueueCLSTR thing p c rest

dequeueCLSTR :: CLSTRQ obj -> ((obj,Priority,Cluster),CLSTRQ obj)
dequeueCLSTR [] = error "empty CLSTR queue"
dequeueCLSTR ((c,prioq):restq)
  = let ((thing,p),prioq') =  dequeuePRIO prioq
    in ((thing,p,c),restq ++ [(c,prioq')])
\end{code}