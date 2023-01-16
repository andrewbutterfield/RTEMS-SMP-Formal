\section{Program Mainline}

\begin{code}
module Main where

import System.Environment

import Queues
import Runner

main :: IO ()
main = do 
  putStrLn "\n\tThread Q Simulator\n"       
  args <- getArgs
  case args of
    [] -> interactive 
    (["-i"]) -> interactive 
    (["-b"]) -> do
      simFileName <- requestInput "Enter simulation filename: "
      batch simFileName
    (["-b",simFileName]) -> batch simFileName
    ([simFileName]) -> batch simFileName
    _ -> usage
  putStrLn "\n\tFinished!\n"

usage = putStrLn $ unlines
  [ "usage: tqsim [-i|-b] [fname]"
  , " -i        :  run iteractively (default if no args)"
  , " -b        :  request sim file name"
  , " -b fname  :  use sim file 'fname'"
  , " fname mmm :  use sim file 'fname'"
  ]
\end{code}
