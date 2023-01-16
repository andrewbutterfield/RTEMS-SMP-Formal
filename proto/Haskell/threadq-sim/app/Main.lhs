\section{Program Mainline}

\begin{code}
-- 45678 1 2345678 2 2345678 3 2345678 4 2345678 5 2345678 6 2345678 7 2345678 8
module Main where

import System.IO

import Queues
import Runner

main :: IO ()
main 
  = do putStrLn "\n\tThread Q Simulator\n"
       
       putStr "Enter simulation filename: "
       hFlush stdout
       simFileName <- getLine
       simCommands <- fmap lines $ readFile simFileName
       run simFileName simCommands
        
       putStrLn "\n\tFinished!\n"
\end{code}
