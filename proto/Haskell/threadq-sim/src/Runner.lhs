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
\end{code}

Here we provide a simple mechanism/language to run simulations

The basic idea is to declare some objects, 
and then invoke actions upon them.

The language is line based, each line starting with a keyword.

\subsection{Objects}

We segregate objects by their type.
\begin{code}
data Object
\end{code}
\begin{description}
  \item [Uninterpreted] arbitrary test objects
\begin{code}
  = Unint
\end{code}
  \item [FIFO]  FIFO queue objects
\begin{code}
  | FIFO Object
\end{code}
  \item [PRIO]  Priority queue objects
\begin{code}
  | PRIO Object
\end{code}
  \item [CLSTR] Cluster queue objects
\begin{code}
  | ClusterQ Object
\end{code}
\end{description}
The queue objects are themselves parameterised with a content object.

\newpage
\subsection{Simulation State}

We have a notion of an association list between names and objects
\begin{code}
type NamedObject obj = (String,obj)
type NamedObjects obj = [NamedObject obj]

nameLookup :: NamedObjects obj -> String -> Maybe obj
nameLookup namedObjs name = fmap snd $ find (hasName name) namedObjs
hasName name (n,_) = name == n
\end{code}

We define the state to be a collection of named objects:
\begin{code}
data SimState
  =  State {
       arbobjs  :: [String] -- basically tokens naming themselves
     , fifoQs    :: NamedObjects (FIFOQ String)
     , prioQs    :: NamedObjects (PRIOQ String)
     , clusterQs :: NamedObjects (CLSTRQ String)
     }

initstate = State [] [] [] []

instance Show SimState where
  show state = unlines $
    [ "__________"
    , "arbitrary: "   ++ sepBy " " (arbobjs state)
    , "fifo::\n  "    ++ (sepBy "\n  " $ map showFIFOq $ fifoQs state)
    , "prio::\n  "    ++ (sepBy "\n  " $ map showPrioQ $ prioQs state)
    , "cluster::\n  " ++ (sepBy "\n  " $ map showClusterQ $ clusterQs state)
    , "----------"
    ]
sepBy sep css = concat $ intersperse sep css

showFIFOq (nm,fifoq) = nm ++ " <" ++ sepBy "," fifoq ++ ">"

showPrioQ (nm,prioq) 
  = nm ++ " <" ++ sepBy "," (map showPItem prioq) ++ ">"
showPItem (p,thing) = show p ++ ':':thing

showClusterQ :: NamedObject (CLSTRQ String) -> String
showClusterQ (nm,clstq) 
  = nm ++ "::\n    " ++ sepBy "\n    " (map showCLItem clstq)
showCLItem (cno,prioq) = "["++show cno++"] "++ showPrioQ ("",prioq)

\end{code}

\subsection{Running Simulations}

\subsubsection{Interactive Simulation}

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

\subsubsection{Batch Simulation}

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
    ["enq",queue,object] -> enQueueObject state queue object
    _ -> do putStrLn ("Unrecognised command '"++cmd++"'")
            putStrLn $ unlines 
              [ "Commands:"
              , "  new <type> <names> - create new objects"
              , "  enq <type> <name> <name> - enqueue objects"
              ]
            return state
\end{code}

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
  | what == arbObj    =  makeNewArbitraryObjects state args
  | what == fifoQ     =  makeNewFIFOQueues state args
  | what == prioQ     =  makeNewPriorityQueues state args
  | what == clusterQ  =  makeNewClusterQueues state args
  | otherwise    =  do 
      putStrLn ("Unknown object type '"++what++"'")
      putStrLn $ unlines 
        [ "Object types:"
        , "  " ++ arbObj   ++ " - " ++ arbDescr
        , "  " ++ fifoQ    ++ " - " ++ fifoDescr
        , "  " ++ prioQ    ++ " - " ++ prioDescr
        , "  " ++ clusterQ ++ " - " ++ clusterDescr
        ]
      return state
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

\subsubsection{Enqueing Objects}

\begin{code}
enQueueObject :: SimState -> String -> String -> IO SimState
enQueueObject state queue object = return state
\end{code}