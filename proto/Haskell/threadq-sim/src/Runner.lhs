\section{RTEMS Simulation Runner}
\begin{code}
module Runner
    ( requestInput
    , interactive
    , batch
    ) where
import Data.List
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


\subsection{Simulation State}

We define the state to be a collection of named objects:
\begin{code}
type NamedObject obj = (String,obj)
data SimState
  =  State {
       arbobjs  :: [String] -- basically tokens naming themselves
     , fifoQs    :: [NamedObject (FIFOQ String)]
     , prioQs    :: [NamedObject (PRIOQ String)]
     , clusterQs :: [NamedObject (CLSTRQ String)]
     }

initstate = State [] [] [] []

instance Show SimState where
  show s = unlines $
    [ "arbitrary > " ++ sepBy " " (arbobjs s)
    , "fifo :\n"  ++ (sepBy "\n" $ map showFIFOq $ fifoQs s)
    , "prio :\n"  ++ (sepBy "\n" $ map showPrioQ $ prioQs s)
    , "cluster :\n"  ++ (sepBy "\n" $ map showClusterQ $ clusterQs s)
    ]
sepBy sep css = concat $ intersperse sep css

showFIFOq (nm,fifoq) = "  " ++ nm ++ " <" ++ sepBy "," fifoq ++ ">"

showPrioQ (nm,prioq) 
  = "  " ++ nm ++ " <" ++ sepBy "," (map showPItem prioq) ++ ">"
showPItem (p,thing) = show p ++ ':':thing

showClusterQ :: NamedObject (CLSTRQ String) -> String
showClusterQ (nm,clstq) 
  = "  " ++ nm ++ " :\n    " ++ sepBy "\n    " (map showCLItem clstq)
showCLItem (cno,prioq) = "["++show cno++"] "++ showPrioQ ("",prioq)

\end{code}

\subsection{Running Simulations}

\subsubsection{Interactive Simulation}

\begin{code}
requestInput prompt = do
  putStr prompt
  hFlush stdout
  getLine

interactive = request initstate

request s = do
  cmd <- requestInput "Cmd> "
  s' <- doCommand s cmd
  putStrLn $ show s'
  request s'
\end{code}

\subsubsection{Batch Simulation}

\begin{code}  
batch sfn = do
  cmds <- fmap lines $ readFile sfn
  putStrLn ("Running '"++sfn)
  putStrLn ("Initial State:\n"++show initstate)
  s' <- perform initstate cmds
  putStrLn ("Final State:\n"++show s')

perform :: SimState -> [String] -> IO SimState
perform s [] = do { putStrLn "Completed" ; return s }
perform s (cmd:cmds) = do  
  s' <- doCommand s cmd
  putStrLn ("State:\n"++show s')
  perform s' cmds
\end{code}

\subsection{Simulation Commands}

\begin{code}
doCommand :: SimState -> String -> IO SimState
doCommand s cmd = do
  putStrLn ("\n> "++cmd)
  case words cmd of
    []  ->  return s 
    ("new":what:args) -> makeNewObject s what args
    _ -> do putStrLn ("Unrecognised command '"++cmd++"'")
            putStrLn $ unlines 
              [ "Commands:"
              , "  new <type> <names> - create new objects"
              ]
            return s
\end{code}

\subsubsection{Creating New Objects}

\begin{code}
makeNewObject :: SimState -> String -> [String] -> IO SimState
makeNewObject s what args
  | what == "A"  =  makeNewArbitraryObjects s args
  | what == "F"  =  makeNewFIFOQueues s args
  | what == "P"  =  makeNewPriorityQueues s args
  | what == "C"  =  makeNewClusterQueues s args
  | otherwise    =  do 
      putStrLn ("Unknown object type '"++what++"'")
      putStrLn $ unlines 
        [ "Object types:"
        , "  A - arbitrary"
        , "  F - FIFO queue"
        , "  P - Priority queue"
        , "  C - Cluster queue"
        ]
      return s
\end{code}

\begin{code}
makeNewArbitraryObjects :: SimState -> [String] -> IO SimState
makeNewArbitraryObjects s args
  = return s{ arbobjs = args ++ arbobjs s }
\end{code}

\begin{code}
makeNewFIFOQueues :: SimState -> [String] -> IO SimState
makeNewFIFOQueues s args
  = return s{ fifoQs = map newFIFOQueue args ++ fifoQs s }

newFIFOQueue name = (name,[])
\end{code}

\begin{code}
makeNewPriorityQueues :: SimState -> [String] -> IO SimState
makeNewPriorityQueues s args
  = return s{ prioQs = map newPriorityQueue args ++ prioQs s }

newPriorityQueue name = (name,[])
\end{code}

\begin{code}
makeNewClusterQueues :: SimState -> [String] -> IO SimState
makeNewClusterQueues s args
  = return s{ clusterQs = map newClusterQueue args ++ clusterQs s }

newClusterQueue name = (name,[])
\end{code}