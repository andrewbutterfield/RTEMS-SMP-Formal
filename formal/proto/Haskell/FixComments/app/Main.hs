module Main where
import System.Environment

import FixComments

main :: IO ()
main = do
  args <- getArgs
  if null args
    then putStrLn "usage: fixcmt filename"
    else do
      source <- readFile $ head args
      let fixed = unlines $ fixComments [] $ lines source
      putStrLn fixed
