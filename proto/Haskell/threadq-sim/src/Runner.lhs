\section{RTEMS Simulation Runner}
\begin{code}
module Runner
    ( run
    ) where
import Queues
\end{code}

Here we provide a simple mechanism/language to run simulations

The basic idea is to declare some objects, 
and then invoke actions upon them.

The language is line based, each line starting with a keyword.

\begin{code}
run :: [String] -> IO ()
run [] = putStrLn "Runner has no input"
run (sfn:cmds) 
  = do putStrLn ("Running '"++sfn)
       putStrLn "Contents:"
       enact initstate cmds
\end{code}

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


enact :: SimState -> [String] -> IO ()
enact s cmds
  = do putStrLn ("Start state is "++show s)
       perform s cmds

perform :: SimState -> [String] -> IO ()
perform s [] = putStrLn "Completed"
perform s (cmd:cmds)
  = do putStrLn ("Doing "++cmd++" ...")
       putStrLn (" ... done: "++show s)
       perform s cmds
\end{code}


