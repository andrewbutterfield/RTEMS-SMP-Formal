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

theory Split_Command
  imports Isabelle_C.C_Main
  keywords "split_file" :: thy_load % "ML"
begin

section \<open>\<^theory>\<open>Isabelle_C.C_Command\<close>\<close>

subsection \<open>CIL AST\<close>

ML \<comment> \<open>\<^theory>\<open>Isabelle_C.C_Ast\<close>\<close> \<open>
structure Split_CIL =
struct
datatype c_cil = GFun of string
               | GType
               | GEnumTag
               | GEnumTagDecl
               | GCompTag
               | GCompTagDecl
               | GVar
               | GVarDecl
               | GFunDecl
               | GAsm
               | GPragma
               | GAnnot
end
\<close>

subsection \<open>Parsing Entry-Point: Error and Acceptance Cases\<close>

ML \<comment> \<open>\<^theory>\<open>Isabelle_C.C_Eval\<close>\<close> \<open>
structure Split_Module =
struct

structure Data_In_Source = Generic_Data
  (type T = Input.source list
   val empty = []
   val extend = K empty
   val merge = K empty)

end
\<close>

subsection \<open>Definitions of Inner Annotation Commands\<close>

subsubsection \<open>Library\<close>

ML \<comment> \<open>\<^theory>\<open>Isabelle_C.C_Eval\<close>\<close> \<open>
structure Split_Stack =
struct

type data_c_fun = { file : string
                  , file_prev : string option
                  , file_next : string option
                  , file_pos : int (*pos*) * int (*total*)
                  , begin_line : int
                  , original_line : int
                  , typ : Split_CIL.c_cil }

structure Data_C_Fun = Generic_Data
  (type T = (int (* line *) * data_c_fun) list
   val empty = []
   val extend = K empty
   val merge = K empty)

type data_pml_fun = { typ_fun : string }

structure Data_PML_Fun = Generic_Data
  (type T = (int (* line *) * data_pml_fun) list
   val empty = []
   val extend = K empty
   val merge = K empty)

(* *)

fun update_file_prev file_prev ({ file, file_next, file_pos, begin_line, original_line, typ, ... } : data_c_fun) =
  { file = file
  , file_prev = file_prev
  , file_next = file_next
  , file_pos = file_pos
  , begin_line = begin_line
  , original_line = original_line
  , typ = typ }

fun update_file_next file_next ({ file, file_prev, file_pos, begin_line, original_line, typ, ... } : data_c_fun) =
  { file = file
  , file_prev = file_prev
  , file_next = file_next
  , file_pos = file_pos
  , begin_line = begin_line
  , original_line = original_line
  , typ = typ }

fun update_file_pos file_pos ({ file, file_prev, file_next, begin_line, original_line, typ, ... } : data_c_fun) =
  { file = file
  , file_prev = file_prev
  , file_next = file_next
  , file_pos = file_pos
  , begin_line = begin_line
  , original_line = original_line
  , typ = typ }

(* *)

fun read_lines0 data_get gthy =
  let
    val src = Split_Module.Data_In_Source.get gthy
              |> hd
              |> Input.source_content
              |> #1
              |> split_lines
    
    fun aux (global, lines, line_pos) =
      fn (x :: xs, (delim_line, data) :: delims) => 
          if line_pos = delim_line then
            aux ((data, lines) :: global, [], line_pos - 1) (xs, delims)
          else
            aux (global, x :: lines, line_pos - 1) (xs, (delim_line, data) :: delims)
       | (l, _) => (case lines of [] => (l, global)
                                | _ => error ("Expecting null" ^ @{make_string} lines))
  in
    aux ([], [], length src) (rev src, data_get gthy)
  end

fun read_lines data_get =
  Context.Theory
  #> read_lines0 data_get

(* *)

fun fill_prev update_file_prev funs =
  fold
    (fn (c_fun as ({file, ...} : data_c_fun), lines) =>
      fn (prev, funs) =>
        case prev of
          NONE =>
            (SOME file, (c_fun, lines) :: funs)
        | SOME file_prev =>
            if file_prev = file then
              (prev, (c_fun, lines) :: funs)
            else
              (SOME file, (update_file_prev prev c_fun, lines) :: funs))
    funs
    (NONE, [])
  |> #2

fun fill_pos funs =
  map_index
    (uncurry
      let val len = length funs
      in fn pos => apfst (update_file_pos (pos + 1, len)) end)
    funs

fun fill_prev_next_pos xs = xs |>
 (fill_prev update_file_prev
  #> fill_prev update_file_next
  #> fill_pos)

fun undef var here =
  warning
    ("Undefined Isabelle environment variable: \"" ^ var ^ "\""
     ^ Position.here here)
end
\<close>

subsubsection \<open>Initialization\<close>

ML \<comment> \<open>\<^theory>\<open>Pure\<close>\<close> \<open>
local

fun escape_string s = "\"" ^ s ^ "\""

val _ = Theory.setup
  (C_Inner_Syntax.command0
    (C_Inner_Toplevel.generic_theory
      o (fn ( ( ( ( ( ((source, file), begin_line)
                    , _ (*begin_col1*))
                  , _ (*begin_col2*))
                , _ (*end_line*))
              , _ (*end_col1*))
            , _ (*end_col2*)) =>
          let
            val original_line = Int.toString (Position.line_of (Input.pos_of source) |> the)
          in
            ML_Context.expression
              (Input.pos_of source)
              (ML_Lex.read ("Context.>> (Split_Stack.Data_C_Fun.map (cons (" ^ original_line ^ ",\
                            \ {file = " ^ escape_string file ^ ",\
                            \ file_prev = NONE,\
                            \ file_next = NONE,\
                            \ file_pos = (0, 0),\
                            \ begin_line = " ^ begin_line ^ ",\
                            \ original_line = " ^ original_line ^ ",\
                            \ typ = let open Split_CIL in ")
               @ ML_Lex.read_source source
               @ ML_Lex.read " end })))")
          end))
    (C_Parse.ML_source
     -- C_Parse.string
     -- C_Parse.number
     -- C_Parse.number
     -- C_Parse.number
     -- C_Parse.number
     -- C_Parse.number
     -- C_Parse.number)
    ("frama_c_cil", \<^here>, \<^here>, \<^here>)
   #>
   C_Inner_Syntax.command0
    (C_Inner_Toplevel.generic_theory
      o (fn (typ_fun, pos) =>
          Split_Stack.Data_PML_Fun.map (cons (Position.line_of pos |> the, {typ_fun = typ_fun}))))
    (C_Parse.position C_Parse.string)
    ("modex", \<^here>, \<^here>, \<^here>))
in end
\<close>

subsection \<open>Definitions of Outer Classical Commands\<close>

subsubsection \<open>Library\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/ML/ml_file.ML\<close>\<close> \<open>
structure Split_Outer_File =
struct

fun command_split0 lines pos gthy =
  fold
    (fn line => fn (pos, gthy) =>
      (case Symbol_Pos.explode (line, pos) of
         [] => (pos, gthy)
       | line0 =>
          ( line0 |> List.last |-> Position.advance
          , if String.isPrefix "/*@ " line andalso String.isSuffix " */" line then
              C_Module.C (Input.source true line (pos, pos)) gthy
            else
              gthy))
      |> apfst (Position.advance "\n"))
    lines
    (pos, gthy)
  |> #2

fun command_split ({src_path, lines, digest, pos}: Token.file) =
  let
    val provide = Resources.provide (src_path, digest);
  in Split_Module.Data_In_Source.map (cons (Input.source true (cat_lines lines) (pos, pos)))
    #> command_split0 lines pos
    #> Context.mapping provide (Local_Theory.background_theory provide)
  end;

fun split files gthy =
  command_split (hd (files (Context.theory_of gthy))) gthy;

end;
\<close>

subsubsection \<open>Initialization\<close>

ML \<comment> \<open>\<^theory>\<open>Pure\<close>\<close> \<open>
local
val semi = Scan.option \<^keyword>\<open>;\<close>;

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>split_file\<close> "read and evaluate a file"
    (Resources.parse_files "split_file" --| semi
     >> (Toplevel.generic_theory o Split_Outer_File.split));
in end
\<close>

end
