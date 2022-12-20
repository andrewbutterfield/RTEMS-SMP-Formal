(******************************************************************************
 * Splitting C-like Preprocessed Files
 *
 * Copyright (C) 2019-2021 Trinity College Dublin (www.tcd.ie)
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************)

theory Split_Exec
  imports Isabelle_Split.Split_Main
begin

section \<open>\<^theory>\<open>Isabelle_Split.Split_Main\<close>\<close>

subsection \<open>Initialization\<close>

ML \<open>
structure Split_Data =
struct

val path_src = getenv_strict "SPLIT_FILE_PREF"
val path_rm = is_some (OS.Process.getEnv "SPLIT_FILE_PREF_RM")

datatype write = Write_raw
               | Write_index
               | Write_diff

val write_mode =
  case
    map OS.Process.getEnv [ "SPLIT_FILE_WRITE_RAW"
                          , "SPLIT_FILE_WRITE_INDEX"
                          , "SPLIT_FILE_WRITE_DIFF" ]
  of
    [SOME _, NONE, NONE] => SOME Write_raw
  | [NONE, SOME _, NONE] => SOME Write_index
  | [NONE, NONE, SOME _] => SOME Write_diff
  | l =>
      tap (fn _ => if exists is_some l then
                     warning "Not yet implemented"
                   else
                     warning "Write action not specified")
      NONE
end
\<close>

subsubsection \<open>C\<close>

split_file \<open>$SPLIT_FILE_C\<close>

ML \<open>
structure Split_Data_C =
struct
val (initial_header, funs) = Split_Stack'.read_lines' Split_Stack.Data_C_Fun.get @{theory}
end
\<close>

setup \<open>
Context.theory_map (Split_Stack.Data_C_Fun.put [])
\<close>


(**)

ML\<open>
structure Split_Data_Multi_C =
struct
val funs =
  Split_File_Index.split_file_index0
    ("SPLIT_FILE_INDEX_PAT", \<^here>)
    ("SPLIT_FILE_INDEX_C", \<^here>)
    Split_File_Index.read_line_c
    Split_Stack.Data_C_Fun.put
end
\<close>

subsubsection \<open>PML\<close>

split_file \<open>$SPLIT_FILE_PML\<close>

ML \<open>
structure Split_Data_PML =
struct
val (initial_header, funs) = Split_Stack.read_lines Split_Stack.Data_PML_Fun.get @{theory}
                             |> apsnd (pair (NONE : Split_Merge.uniq_pat option)
                                       #> single)
end
\<close>

setup \<open>
Context.theory_map (Split_Stack.Data_PML_Fun.put [])
\<close>


(**)

ML\<open>
structure Split_Data_Multi_PML =
struct
val funs =
  Split_File_Index.split_file_index0
    ("SPLIT_FILE_INDEX_PAT", \<^here>)
    ("SPLIT_FILE_INDEX_PML", \<^here>)
    Split_File_Index.read_line_pml
    Split_Stack.Data_PML_Fun.put
end
\<close>

subsubsection \<open>Main\<close>

ML \<open>
structure Split_Gen =
struct

val pref_dir_rm = space_explode "/" Split_Data.path_src |> tl

val pref_dir_rm' = fn "" :: path =>
                        fold
                          (fn name1 =>
                            fn name2 :: path =>
                                 if name1 = name2 then
                                   path
                                 else
                                   error "Expecting a same path name"
                             | _ => error "Expecting an existing path name")
                          pref_dir_rm
                          path
                    | path => path

val pref_dir_rm'' =
  if Split_Data.path_rm then
    space_explode "/" #> pref_dir_rm' #> String.concatWith "/"
  else
    I

fun pref_dir pref = cons pref o pref_dir_rm'

val write =
  let
    val var = "SPLIT_FILE_EXEC"
    val write =
      case Split_Data.write_mode of
        SOME Split_Data.Write_raw => Split_File.write_raw
      | SOME Split_Data.Write_index => Split_File.write_index
      | SOME Split_Data.Write_diff => Split_File.write_diff
      | NONE => K (K (K (K (K ()))))
  in
    case OS.Process.getEnv var of
      NONE => 
        (fn here =>
          write NONE
          |> tap (fn _ => Split_Stack.undef var here))
    | SOME dir_output0 =>
        let
          val dir_output = Path.explode dir_output0
          val _ = if Path.is_absolute dir_output then
                    ()
                  else
                    warning ("Not an absolute path: " ^ var ^ " = " ^ \<^make_string> dir_output0)
        in
          K (write (SOME dir_output))
        end
  end

val funs_c = case Split_Data.write_mode of
               SOME Split_Data.Write_diff => Split_Data_Multi_C.funs
             | _ => Split_Data_C.funs

val funs_pml = case Split_Data.write_mode of
                 SOME Split_Data.Write_diff => Split_Data_Multi_PML.funs
               | _ => Split_Data_PML.funs

val _ =
  write
    \<^here>
    (map (apsnd (map (apsnd SOME))) funs_c)
    pref_dir
    "c"
    pref_dir_rm''

val _ =
  write
    \<^here>
    (map2
      (fn (uniq_c, funs_c) => fn (uniq_pml, funs_pml) =>
        if uniq_c = uniq_pml then
          case
            fold
              (fn (data_c, _) =>
                case data_c of
                  {typ = Split_CIL.GFun typ_fun2, ...} =>
                    (fn (({typ_fun = typ_fun1}, cts) :: pml, acc) =>
                        (pml, (if typ_fun1 = typ_fun2 then
                                 (data_c, SOME cts)
                               else
                                 error "Different order between the C generated functions and the PML ones")
                              :: acc)
                      | _ => error "Expecting (at least) an additional PML function to match the current C one")
                | _ => apsnd (cons (data_c, NONE)))
              funs_c
              (funs_pml, [])
           of ([], funs) => (uniq_c, rev funs)
            | _ => error "Remaining PML functions not fully consummed by the C ones"
        else
          error "Expecting similar C and PML names")
      funs_c
      funs_pml)
    pref_dir
    "pml"
    pref_dir_rm''

end
\<close>

end
