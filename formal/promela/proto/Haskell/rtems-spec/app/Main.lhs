\section{Program Mainline}

\begin{code}
-- 45678 1 2345678 2 2345678 3 2345678 4 2345678 5 2345678 6 2345678 7 2345678 8
module Main where

import RTEMSpec

main :: IO ()
main = putStrLn ("I contain: "++RTEMSpec.whatAmI)
\end{code}
