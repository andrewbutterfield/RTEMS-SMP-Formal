\section{RTEMS Simulation State}
\begin{code}
module SimState
    ( SimState(..)
    , initstate
    , nameLookup, nameUpdate
    ) where
import Data.List
import Data.Char
import System.IO
import Queues
\end{code}

Here we define the simulator state

\subsection{Named Objects}

We have a notion of an association list between names and objects
\begin{code}
type NamedObject obj = (String,obj)
type NamedObjects obj = [NamedObject obj]

nameLookup :: NamedObjects obj -> String -> Maybe obj
nameLookup namedObjs name = fmap snd $ find (hasName name) namedObjs
hasName name (n,_) = name == n

nameUpdate :: String -> obj -> NamedObjects obj -> NamedObjects obj
nameUpdate name value []  =  []
nameUpdate name value (no@(n,_):namedObjs)
  | n == name  =  (n,value) : namedObjs
  | otherwise  =  no : nameUpdate name value namedObjs
\end{code}

\newpage

\subsection {The Simulator State}

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

