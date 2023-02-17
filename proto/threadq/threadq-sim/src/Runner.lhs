\section{RTEMS Simulation Runner}
\begin{code}
module Runner
    ( requestInput
    , interactive
    , batch
    ) where
import Data.List
import Data.Char
import System.IO
import Queues
import SimState
\end{code}

Here we provide a simple mechanism/language to run simulations

The basic idea is to declare some objects, 
and then invoke actions upon them.

The language is line based, each line starting with a keyword.



\subsection{Reporting Failure}

\begin{code}
simFail :: SimState -> String -> IO SimState
simFail state msg = do { putStrLn msg ; return state }
simFail2 :: SimState -> obj -> String -> IO (obj, SimState)
simFail2 state obj msg = do { putStrLn msg ; return (obj,state) }
\end{code}

\subsection{Interactive Simulation}

\begin{code}
interactive = request initstate

request state = do
  cmd <- requestInput "_______________________\nCmd> "
  if null cmd
  then request state
  else do
    state' <- doCommand state cmd
    putStrLn $ show state'
    request state'

requestInput prompt = do
  putStr prompt
  hFlush stdout
  fmap trim getLine

trim = ltrim . reverse . ltrim . reverse

ltrim = dropWhile isSpace 
\end{code}

\newpage

\subsection{Batch Simulation}

\begin{code}  
batch sfn = do
  cmds <- fmap lines $ readFile sfn
  putStrLn ("Running '"++sfn)
  putStrLn ("\nInitial State:\n"++show initstate)
  state' <- perform initstate cmds
  putStrLn ("\nFinal State:\n"++show state')

perform :: SimState -> [String] -> IO SimState
perform state [] = do { putStrLn "Completed" ; return state }
perform state (cmd:cmds) = do  
  state' <- doCommand state cmd
  putStrLn ("State:\n"++show state')
  perform state' cmds
\end{code}

\subsection{Simulation Commands}

\begin{code}
doCommand :: SimState -> String -> IO SimState
doCommand state cmd = do
  putStrLn ("\n> "++cmd)
  case words cmd of
    []  ->  return state 
    ("new":what:args) -> makeNewObject state what args
    ["fq",qName,objName] -> enQueueStateFIFO state qName objName
    ["fd",qName] -> 
      do  (obj,state') <- deQueueStateFIFO state qName 
          putStrLn ("dequeued: "++obj)
          return state'
    ["pq",qName,objName,prio] -> enQueueStatePRIO state qName objName (rEAD prio)
    ["pd",qName] -> 
      do  ((obj,prio),state') <- deQueueStatePRIO state qName 
          putStrLn ("dequeued: "++obj++"!"++show prio)
          return state'
    ["cq",qName,objName,prio,cluster] 
      -> enQueueStateCLSTR state qName objName (rEAD prio) (rEAD cluster)
    ["cd",qName] -> 
      do  ((obj,prio,cluster),state') <- deQueueStateCLSTR state qName 
          putStrLn ("dequeued: "++obj++"!"++show prio++"@"++show cluster)
          return state'
    _ -> simFail state $ unlines
          [ "Unrecognised command '"++cmd++"'"
          , "Commands:"
          , "  new <otype> <names> - create new objects"
          , "  fq <qname> <oname> - FIFO enqueue"
          , "  fd <qname> - FIFO dequeue"
          , "  pq <qname> <oname> <prio> - PRIO enqueue"
          , "  pd <qname> - PRIO dequeue"
          , "  cq <qname> <oname> <prio> <cluster> - CLSTR enqueue"
          ]

rEAD :: String -> Int
rEAD str
 | all isDigit str  =  read str
 | otherwise        =  42
\end{code}

\newpage 

\subsubsection{Creating New Objects}

Object kinds:
\begin{code}
arbObj   = "a" ; arbDescr     = "arbitrary"
fifoQ    = "f" ; fifoDescr    = "FIFO Queue"
prioQ    = "p" ; prioDescr    = "Priority Queue"
clusterQ = "c" ; clusterDescr = "Cluster Queue"
\end{code}

\begin{code}
makeNewObject :: SimState -> String -> [String] -> IO SimState
makeNewObject state what args
  | what == arbObj    = makeNewArbitraryObjects state args
  | what == fifoQ     = makeNewFIFOQueues state args
  | what == prioQ     = makeNewPriorityQueues state args
  | what == clusterQ  = makeNewClusterQueues state args
  | otherwise         = simFail state $ unlines
                          [ "Unknown object type '"++what++"'"
                          ,"Object types:"
                          , "  " ++ arbObj   ++ " - " ++ arbDescr
                          , "  " ++ fifoQ    ++ " - " ++ fifoDescr
                          , "  " ++ prioQ    ++ " - " ++ prioDescr
                          , "  " ++ clusterQ ++ " - " ++ clusterDescr
                          ]
\end{code}

\begin{code}
makeNewArbitraryObjects :: SimState -> [String] -> IO SimState
makeNewArbitraryObjects state args
  = return state{ arbobjs = args ++ arbobjs state }
\end{code}

\begin{code}
makeNewFIFOQueues :: SimState -> [String] -> IO SimState
makeNewFIFOQueues state args
  = return state{ fifoQs = map newFIFOQueue args ++ fifoQs state }

newFIFOQueue name = (name,[])
\end{code}

\begin{code}
makeNewPriorityQueues :: SimState -> [String] -> IO SimState
makeNewPriorityQueues state args
  = return state{ prioQs = map newPriorityQueue args ++ prioQs state }

newPriorityQueue name = (name,[])
\end{code}

\begin{code}
makeNewClusterQueues :: SimState -> [String] -> IO SimState
makeNewClusterQueues state args
  = return state{ clusterQs = map newClusterQueue args ++ clusterQs state }

newClusterQueue name = (name,[])
\end{code}

\newpage

\subsubsection{Enqueing Objects}

\begin{code}
enQueueStateFIFO :: SimState -> String -> String -> IO SimState
enQueueStateFIFO state qName objName 
  = case nameLookup fifoqs qName of
      Nothing  ->  simFail state ("no such FIFO queue: "++qName)
      Just fifoq -> 
        let fifoq' = enqueueFIFO objName fifoq
            state' =  state{ fifoQs = nameUpdate qName fifoq' fifoqs}
        in return state'
  where fifoqs = fifoQs state
\end{code}

\begin{code}
enQueueStatePRIO :: SimState -> String -> String -> Priority -> IO SimState
enQueueStatePRIO state qName objName prio
  = case nameLookup prioqs qName of
      Nothing  ->  simFail state ("no such PRIO queue: "++qName)
      Just prioq -> 
        let prioq' = enqueuePRIO objName prio prioq
            state' =  state{ prioQs = nameUpdate qName prioq' prioqs}
        in return state'
  where prioqs = prioQs state
\end{code}

\begin{code}
enQueueStateCLSTR :: SimState -> String -> String -> Priority -> Cluster
                  -> IO SimState
enQueueStateCLSTR state qName objName prio cluster
  = case nameLookup clusterqs qName of
      Nothing  ->  simFail state ("no such CLSTR queue: "++qName)
      Just clusterq -> 
        let clusterq' = enqueueCLSTR objName prio cluster clusterq
            state' =  state{ clusterQs = nameUpdate qName clusterq' clusterqs}
        in return state'
  where clusterqs = clusterQs state
\end{code}

\newpage

\subsubsection{Dequeing Objects}

\begin{code}
deQueueStateFIFO :: SimState -> String -> IO (String, SimState)
deQueueStateFIFO state qName 
  = case nameLookup fifoqs qName of
      Nothing  ->  simFail2 state "" ("no such FIFO queue: "++qName)
      Just fifo -> 
        if isEmptyFIFOQ fifo
         then simFail2 state "" ("FIFO queue "++qName++" is empty")
         else let (objName,fifo') = dequeueFIFO fifo 
                  state' = state{fifoQs = nameUpdate qName fifo' fifoqs}
              in return (objName,state')
  where fifoqs = fifoQs state
\end{code}


\begin{code}
deQueueStatePRIO :: SimState -> String -> IO ((String, Priority), SimState)
deQueueStatePRIO state qName 
  = case nameLookup prioqs qName of
      Nothing  ->  simFail2 state ("",0) ("no such PRIO queue: "++qName)
      Just prioq -> 
        if isEmptyPRIOQ prioq
         then simFail2 state ("",0) ("PRIO queue "++qName++" is empty")
         else let ((objName,prio),prioq') = dequeuePRIO prioq 
                  state' = state{prioQs = nameUpdate qName prioq' prioqs}
              in return ((objName,prio),state')
  where prioqs = prioQs state
\end{code}


\begin{code}
deQueueStateCLSTR :: SimState -> String 
                  -> IO ((String, Priority, Cluster), SimState)
deQueueStateCLSTR state qName 
  = case nameLookup clusterqs qName of
      Nothing  ->  simFail2 state ("",0,0) ("no such CLSTR queue: "++qName)
      Just clusterq -> 
        if isEmptyCLSTRQ clusterq
         then simFail2 state ("",0,0) ("CLSTR queue "++qName++" is empty")
         else let ((objName,prio,cluster),clusterq') = dequeueCLSTR clusterq 
                  state' = state{clusterQs = nameUpdate qName clusterq' clusterqs}
              in return ((objName,prio,cluster),state')
  where clusterqs = clusterQs state
\end{code}