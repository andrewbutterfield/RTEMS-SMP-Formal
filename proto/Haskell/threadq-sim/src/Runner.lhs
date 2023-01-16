\section{RTEMS Simulation Runner}
\begin{code}
module Runner
    ( requestInput
    , interactive
    , batch
    ) where
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
  deriving Show

initstate = State [] [] [] []
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
  putStrLn ("State:\n"++show s')
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
            return s
\end{code}

\subsubsection{Creating New Objects}

\begin{code}
makeNewObject :: SimState -> String -> [String] -> IO SimState
makeNewObject s what args
  | what == "arb"  =  makeNewArbitraryObjects s args
  | otherwise  =  do putStrLn ("Unknown object type '"++what++"'")
                     return s
\end{code}

\begin{code}
makeNewArbitraryObjects :: SimState -> [String] -> IO SimState
makeNewArbitraryObjects s args
  = return s{ arbobjs = args ++ arbobjs s }
\end{code}