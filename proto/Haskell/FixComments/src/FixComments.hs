module FixComments where

import Data.Char

-- outside any multi-line comment
fixComments :: [String] -> [String] -> [String]
fixComments snl [] = reverse snl
fixComments snl (ln:lns)
  | isMLCommentOpen ln  =  fixingComment (correctOpenMLComment:snl) lns
  | otherwise           =  fixComments (ln:snl) lns

correctOpenMLComment = '/' : replicate 79 '*'

-- inside a multi-line comment
unclosed = " * UNCLOSED COMMENT!!!\n" ++ correctCloseMLComment
fixingComment snl [] = reverse (unclosed:snl)
fixingComment snl (ln:lns)
  | isMLCommentClose ln  = fixComments (correctCloseMLComment:snl) lns
  | otherwise            = fixingComment (fixComment ln : snl) lns

correctCloseMLComment = (' ' : replicate 78 '*') ++ "/"

fixComment ln
  | take 2 ln == " *"  =  ln
  | otherwise  =  " * " ++ ln

isMLCommentOpen ln = take 2 (skipWhite ln) == "/*"

isMLCommentClose ln = take 2 (skipWhite $ reverse ln) == "/*"

skipWhite = dropWhile isSpace
