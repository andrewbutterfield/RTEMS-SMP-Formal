module Main where

import Data.List (partition)
-- import Data.Maybe

import System.Environment
-- import System.Directory
import System.FilePath
-- import Control.Exception
import qualified Data.Map as M

import Debug.Trace
dbg msg x = trace (msg ++ show x) x
pdbg nm x = dbg ('@':nm++":\n") x


data Config
 = Config { testName :: String
          , spinxxmpl  :: FilePath
          , refinement :: FilePath
          , antiquote  :: Char
          , preamble   :: FilePath
          , postamble  :: FilePath
          , init_c     :: FilePath
          }

mkConfig :: String -> Config
mkConfig fileRoot
 = Config { testName = "test_name_not_set"
          , spinxxmpl = fileRoot ++ ".spn"
          , refinement = fileRoot ++ ".rfn"
          , antiquote = '`'
          , preamble = fileRoot ++ "-pre.h"
          , postamble = fileRoot ++ "-post.h"
          , init_c = fileRoot ++ "-init.c"
          }


showConfig config
 = "'" ++ testName config ++ "'\n"
   ++ spinxxmpl config
   ++ " --(" ++
   refinement config
   ++ " " ++
   [antiquote config]
   ++ ")-> [" ++
   preamble config
   ++ " ; _ ; " ++
   postamble config
   ++ "] >> " ++
   init_c config


main :: IO ()
main
 = do args <- getArgs
      config <- processArgs args
      rawspin <- readFile $ spinxxmpl config
      -- putStrLn ( "Raw SPIN Xmpl\n" ++ rawspin)
      let (tnm:testlines) = map dropMarker $ filter isTestLine $ lines rawspin
      let nConfig = setName tnm config
      putStrLn ("\nSpin2Test " ++ showConfig nConfig)
      -- putStrLn ( "Test Lines\n" ++ unlines testlines)
      rfntxt <- readFile $ refinement nConfig
      pretxt <- readFile $ preamble nConfig
      posttxt <- readFile $ postamble nConfig
      let refineMap = makeRefinement $ lines rfntxt
      let refine = mkRFun refineMap
      -- putStrLn ("Refine:\n"++show (M.assocs refineMap))
      let test = generateTest nConfig refine testlines
      -- putStrLn ("\nPRETXT\n"++pretxt)
      -- putStrLn ("\nTEST\n"++test)
      -- putStrLn ("\nPOSTTXT\n"++posttxt)
      let testProg = pretxt ++ test ++ posttxt
      writeFile (init_c nConfig) testProg
      putStrLn ("\nTest File written to "++init_c nConfig++"\n")

processArgs [root]  =  return $ mkConfig root
processArgs _
  = fail $ unlines [ "usage: spin2test file-root"
                   , "  file-root - common root for input files"                   , "            - default is 'test'"
                   ]


marker = "@@@"
markerSize = length marker
dropMarker = drop markerSize

isTestLine str  =  take markerSize str == marker

setName tnm config
 | hdr == "NAME"  =  config{testName=name}
 | otherwise  =  error "expected @@@NAME <name> as first test-line"
 where
   (hdr:name:_) = words tnm

data RefSpec = RS { args :: [String]
                  , body :: [String]
                  }

instance Show RefSpec where
  show rs = "\\ "++unwords (args rs) ++ " @\n" ++ unlines (body rs)

type Refinement = M.Map String RefSpec
type RefFun = String -> RefSpec

isEntryStart str   =  take 4 str == "===="
isRefineStart str  =  take 4 str == "----"
isEnd str          =  take 4 str == "****"

makeRefinement :: [String] -> Refinement
makeRefinement lns = parseRefine [] lns

parseRefine :: [(String,RefSpec)] -> [String]
            -> Refinement
parseRefine entries [] = error "premature end of refinement"
parseRefine entries (ln:lns)
 | isEntryStart ln  =  parseEntry entries lns
 | isEnd ln         =  M.fromList entries
 | otherwise = error ("==== or **** line expected, found:\n" ++ ln)

parseEntry :: [(String,RefSpec)] -> [String]
           -> Refinement
parseEntry entries [] = error "premature end of entry (no key)"
parseEntry entries (ln:lns)
 | null ws =  error "blank key"
 | otherwise  =  parseBody entries (head ws) (tail ws) lns
 where ws = words ln

parseBody :: [(String,RefSpec)] -> String -> [String] -> [String]
          -> Refinement
parseBody entries newkey args [] = error "premature end of body"
parseBody entries newkey args (ln:lns)
 | isRefineStart ln  =  scanBody entries newkey args [] lns
 | otherwise  = error ("---- lines expected, found:\n" ++ ln)

scanBody :: [(String,RefSpec)] -> String -> [String] -> [String] -> [String]
         -> Refinement
scanBody entries newkey args yrtne [] = error "unterminated body"
scanBody entries newkey args yrtne (ln:lns)
 | isEntryStart ln  =  parseEntry (mkEntry newkey args yrtne:entries) lns
 | isEnd ln         =  M.fromList (mkEntry newkey args yrtne:entries)
 | otherwise        =  scanBody entries newkey args (ln:yrtne) lns
 where mkEntry key args yrtne = (key, RS args $ reverse yrtne)

mkRFun :: Refinement -> RefFun
mkRFun f a
 = case M.lookup a f of
    Nothing -> RS [] []
    Just rs -> rs

{- =============================================================================
DEF, DECL used just after preamble.
All @@@ except DEF, DECL are used within a single TESTCASE
============================================================================= -}

generateTest config refine testlines
 = unlines
     [ "//@@@NAME "++testName config
     , "const char rtems_test_name[] = \""++testName config++"\";"
     , ""
     , defs
     , ""
     , "T_TEST_CASE("++testName config++") {"
     , ""
     , decls
     , init
     , rsteps
     , "}"
     , ""
     ,  "static void Init(rtems_task_argument arg)"
     ,  "{"
     ,  "   printf(\"Starting %s\\n\\n\", rtems_test_name );"
     ,  "   T_run_initialize(&config);"
     ,  "   T_register();"
     ,  "   T_run_by_name(\"" ++ testName config ++ "\");"
     ,  "   printf(\"\\n%s finished.\\n\",rtems_test_name);"
     ,  "}"
     ]
 where
   (dfs,rest1)  = partition isDef testlines
   defs = unlines $ map (unlines . refineDEF) dfs
   testwords = map words rest1
   i4 = ind 4
   (dcl,rest2) = partition isDecl testwords
   decls = unlines $ map (unlines . map i4 . refineDECL refine) dcl
   (inits,steps)  = partition isInit rest2
   init = unlines $ map (unlines . map i4 . refineINIT refine) inits
   rsteps = unlines $ map (unlines . map i4) $ refineSTEPS refine steps

ind 0 str = str
ind n str = ' ':(ind (n-1) str)


isDef  str = take 3 str == "DEF"

isDecl ("DECL":_) = True ; isDecl _ = False
isInit ("INIT":_) = True ; isInit _ = False

-- take 3 str == "DEF"
refineDEF :: String -> [String]
refineDEF str = ["//"++marker++str,"#define"++drop 3 str]

-- declw == ["DECL",typ,name]
--        | ["DECL",typ,name,init]
-- ref: no of args: 0
-- ref: body length: 1
refineDECL :: RefFun -> [String] -> [String]
refineDECL refine (ws@[_,typ,name])
 | null (args rs) && length bdy == 1  =  [log,dcl]
 where
   rs = refine typ
   bdy = body rs
   log = "//@@@"++unwords ws
   dcl = head bdy ++ " " ++ name ++ ";"
refineDECL refine (ws@[_,typ,name,init])
 | null (args rs) && length bdy == 1  =  [log,dcl]
 where
   rs = refine typ
   bdy = body rs
   log = "//@@@"++unwords ws
   dcl = head bdy ++ " " ++ name ++ " = " ++ init ++ ";"
refineDECL refine declw = ["// refine failed "++ unwords declw]

-- init ["INIT"]
-- ref: no of args: 0
refineINIT :: RefFun -> [String] -> [String]
refineINIT refine [init]
  | null (args rs)  =  logSTEP init : body rs
  where
    rs = refine init
refineINIT refine init = ["// refine failed "++ unwords init]

refineSTEPS :: RefFun -> [[String]] -> [[String]]
refineSTEPS refine []  =  []
refineSTEPS refine (step:steps) = refineSTEP refine steps step

refineSTEP :: RefFun -> [[String]] -> [String] -> [[String]]

-- CALL proc val1 .. valN
refineSTEP refine rest ws@("CALL":proc:args)
  = (logwSTEP ws : refineCALL refine proc args) : refineSTEPS refine rest

-- SCALAR var val
refineSTEP refine rest ws@["SCALAR",var,val]
 =  [log,obs] : refineSTEPS refine rest
 where
   log = logwSTEP ws
   obs = refineSCALAR refine var val

-- PTR var val
refineSTEP refine rest ws@["PTR",var,val]
 =  [log,obs] : refineSTEPS refine rest
 where
   log = logwSTEP ws
   obs = refinePTR refine var val


-- STRUCT var
  -- SCALAR field val
  -- PTR field val
-- END var
refineSTEP refine rest ws@["STRUCT",var]
  =  [logwSTEP ws] : refineSTRUCT refine var rest

-- SEQ var
  -- SCALAR _ val
  -- PTR _ val
-- END var
refineSTEP refine rest ws@["SEQ",var]
  =  [logwSTEP ws] : refineSEQ refine var [] rest

-- anyything else is ignored
refineSTEP refine rest step
  =  ["// ignoring: "++unwords step] : refineSTEPS refine rest

-- declw == ["CALL",proc,val1,..,valN]
-- ref arg.: proc
-- ref: no of args: N
-- ref: body length: 1
refineCALL refine proc vals
  | length as == length vals = map (substitute '`' rpl) $ body rs
  where
    rs = refine proc
    as = args rs
    rpl = M.fromList $ zip as vals



-- declw == ["SCALAR",var,val]
-- ref arg.: var
-- ref: no of args: 1
-- ref: body length: 1
refineSCALAR refine var val
  | length as == 1 && length bdy == 1
     = substitute '`' rpl obs
  | otherwise  =  []
  where
    rs = refine var
    as = args rs
    arg = head as
    bdy = body rs
    obs = head bdy
    rpl = M.fromList [(arg,val)]

-- declw == ["PTR",var,val]
-- ref arg.: var_PTR
-- ref: no of args: 1
-- ref: body length: 2
refinePTR refine var val
  | length as == 1 && length bdy == 2
     = if val == "0" then substitute '`' rpl nullobs
                     else substitute '`' rpl ptrobs
  where
    rs = refine (var++"_PTR")
    as = args rs
    arg = head as
    bdy = body rs
    [nullobs,ptrobs] = bdy
    rpl = M.fromList [(arg,val)]

-- STRUCT var
  -- SCALAR field val
  -- PTR field val
-- END var
refineSTRUCT refine svar []
 = [[logSTEP ("// premature end of STRUCT "++svar)]]

refineSTRUCT refine svar (ws@["SCALAR",field,fval]:rest)
 = refineSTRUCTSCALAR refine svar field fval : refineSTRUCT refine svar rest

refineSTRUCT refine svar (ws@["PTR",field,fval]:rest)
 = refineSTRUCTPTR refine svar field fval : refineSTRUCT refine svar rest

refineSTRUCT refine svar (ws@["END",evar]:rest)
 | svar == evar  =  refineSTEPS refine rest
 | otherwise    = ["// STRUCT var mistmatch "++svar++"/"++evar]
                  : refineSTEPS refine rest

refineSTRUCT refine svar (ws:rest)
 = ["// bad struct content: "++unwords ws] : refineSTRUCT refine svar rest

-- ref arg.: field_FSCALAR
-- ref: no of args 2
-- ref: bodylength 1
refineSTRUCTSCALAR refine svar field fval
 | length as == 2 && length bdy == 1  =  [substitute '`' rpl obs]
 | otherwise                          =  ["// STRUCTSCALAR unknown field "++field]
 where
   rs = refine (field++"_FSCALAR")
   as = args rs
   bdy = body rs
   obs = head bdy
   rpl = M.fromList $ zip as [svar,fval]

-- ref arg.: field_FPTR
-- ref: no of args 2
-- ref: bodylength 2
refineSTRUCTPTR refine svar field fval
 | length as == 2 && length bdy == 2
    =  if fval == "0"
       then [substitute '`' rpl nullobs]
       else [substitute '`' rpl ptrobs]
 | otherwise  =  ["// STRUCTPTR unknown field "++field]
 where
   rs = refine (field++"_FPTR")
   as = args rs
   bdy = body rs
   [nullobs,ptrobs] = bdy
   rpl = M.fromList $ zip as [svar,fval]


-- SEQ var
  -- SCALAR _ val
  -- PTR _ val
-- END var

refineSEQ refine svar _ []
 = [[logSTEP (" *** premature end of SEQ "++svar)]]

refineSEQ refine svar slavs (ws@["SCALAR","_",sval]:rest)
 = refineSEQ refine svar (sval:slavs) rest

refineSEQ refine svar slavs (ws@["END",evar]:rest)
 | svar == evar  = refineSEQEND refine svar (reverse slavs)
                    : refineSTEPS refine rest

refineSEQ refine svar slavs (ws:rest)
 = [logSTEP $ unwords ("**refineSEQ unknown: ":ws)]
   : refineSEQ refine svar slavs rest

-- ref arg.: svar_SEQ
-- ref: no of args 1
refineSEQEND refine svar svals
 | length as == 1 = map (substitute '`' rpl) bdy
 where
   rs = refine (svar++"_SEQ")
   as = args rs
   vals_str = concat $ map (' ':) svals
   bdy = body rs
   rpl = M.fromList $ zip as [vals_str]


logwSTEP ws   =  logSTEP $ unwords ws
logSTEP str   =  "T_log(\"@@@" ++ str ++ "\\n\");"

substitute :: Char -> (M.Map String String) -> String -> String
substitute aq rpl "" = ""
substitute aq rpl (c:cs)
  | c == aq   =  getarg aq rpl "" cs
  | otherwise  =  c : substitute aq rpl cs

getarg aq rpl gra "" = error "missing ` in refinement template"
getarg aq rpl gra (c:cs)
  | c == aq    =  replace rpl (reverse gra) ++ substitute aq rpl cs
  | otherwise  =  getarg aq rpl (c:gra) cs

replace rpl str
 = case M.lookup str rpl of
     Nothing    ->  error ("unknown template target: "++str)
     Just str'  ->  str'
