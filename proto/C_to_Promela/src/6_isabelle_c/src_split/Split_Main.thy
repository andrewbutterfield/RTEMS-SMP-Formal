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

theory Split_Main
  imports Split_Command
begin

section \<open>\<^theory>\<open>Isabelle_C.C_Main\<close>\<close>

subsection \<open>Library\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/ML/ml_pretty.ML\<close>\<close>
(*  Author:     Frédéric Tuong, Trinity College Dublin *)
(*  Title:      Pure/ML/ml_pretty.ML
    Author:     Makarius

Minimal support for raw ML pretty printing, notably for toplevel pp.
*)
\<open>
structure Split_Pretty =
struct
val make_unf_string_fn =
  "(fn x => (Pretty.unformatted_string_of o Pretty.from_polyml) (ML_system_pretty \
    \(x, FixedInt.fromInt (ML_Print_Depth.get_print_depth ()))))";
end
\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/ML/ml_antiquotation.ML\<close>\<close>
(*  Author:     Frédéric Tuong, Trinity College Dublin *)
(*  Title:      Pure/ML/ml_antiquotation.ML
    Author:     Makarius

ML antiquotations.
*)
\<open>
structure Split_Antiquotation =
struct
(* basic antiquotations *)

val _ = Theory.setup
 (ML_Antiquotation.inline (Binding.make ("make_unf_string", \<^here>)) (Args.context >> K Split_Pretty.make_unf_string_fn))
end
\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/General/table.ML\<close>\<close> \<open>
structure Inttab =
struct
fun map_either (k, default) f tab =
  case Inttab.lookup tab k of
    NONE => Inttab.update_new (k, default) tab
  | SOME v => Inttab.update (k, f v) tab
open Inttab
end
\<close>

ML \<comment> \<open>\<^theory>\<open>Isabelle_C.C_Eval\<close>\<close> \<open>
structure Split_Merge =
struct

datatype uniq_pat = Uniq_pat of string (* pattern uniquely identifying an original source file *)

type 'a content =
  { content_pat : uniq_pat (* id of the element *)
  , content_data : 'a list
  , content_length : int
  , content_null : bool (* true: to not display *)
  , content_c_fun : Split_Stack.data_c_fun list }

type encoding_line =
  { encod_nth : int (* pos in several lines *)
  , encod_size : int (* size of the line to be reconstructed *)
  , encod_line : (int (* pos in single line *) * string (* diff content *)) list (* diff in single line *) }

type encoding_source =
  { encod_content : encoding_line content (* diff in several lines for reconstruction purpose *)
  , encod_model : uniq_pat (* id of the longest taken as encoding model *) }

type T =
  { max_content : string content
  , min_encoded : encoding_source list }


(**)

fun empty max_pat ((max_c_fun, max_cts), max_cts_null) =
  ( { max_content = { content_pat = max_pat
                    , content_data = max_cts
                    , content_length = length max_cts
                    , content_null = max_cts_null
                    , content_c_fun = max_c_fun }
    , min_encoded = [] }
  : T)

fun merge pat1
          ((c_fun1, cts1), cts_null1)
          ( { max_content = { content_pat = pat0
                            , content_data = cts0
                            , content_length = cts_length0
                            , content_null = cts_null0
                            , content_c_fun = c_fun0 }
            , min_encoded = encoded0 }
          : T)
          =
  let
    val cts_length1 = length cts1
    val ( (min_pat, min_cts, min_cts_length, min_cts_null, min_c_fun)
        , (max_pat, max_cts, max_cts_length, max_cts_null, max_c_fun)) =
      (if cts_length0 < cts_length1 then I else swap)
        ( (pat0, cts0, cts_length0, cts_null0, c_fun0)
        , (pat1, cts1, cts_length1, cts_null1, c_fun1))
    val _ = if pat0 = pat1 then
              error "Not expecting the same value"
            else if cts_null0 <> cts_null1 then
              error "Not yet implemented"
            else
              ()
  in
  (
    { max_content = { content_pat = max_pat
                    , content_data = max_cts
                    , content_length = max_cts_length
                    , content_null = max_cts_null
                    , content_c_fun = max_c_fun }
    , min_encoded =
        case
          map_index
            (fn (encod_nth, (line1, line2)) =>
              if line1 = line2 then
                NONE
              else
                let
                  fun sub s n = SOME (String.sub (s, n)) handle Subscript => NONE
                  val encod_line =
                    map_index
                      (fn (n, c1) =>
                        if
                          case sub line2 n of
                            SOME c2 => c1 = c2
                          | NONE => false
                        then
                          NONE
                        else
                          SOME (n, c1))
                      (String.explode line1)
                    |> 
                      let
                        fun cons0 (acc0, acc) =
                          case acc0 of NONE => acc
                                     | SOME (n0, acc0) => (n0, String.implode (rev acc0)) :: acc
                      in
                        fn l =>
                          fold
                            (fn NONE => pair NONE o cons0
                              | SOME (n, c) =>
                                  apfst (SOME o (fn NONE => (n, [c])
                                                  | SOME (n0, acc0) => (n0, c :: acc0))))
                            l
                            (NONE, [])
                          |> cons0
                      end
                    |> rev
                in
                  SOME { encod_nth = encod_nth
                       , encod_size = String.size line1
                       , encod_line = encod_line }
                end)
            (min_cts ~~ take min_cts_length max_cts)
          |> map_filter I
        of
          [] => encoded0
        | content_data =>
            { encod_content = { content_pat = min_pat
                              , content_data = content_data
                              , content_length = min_cts_length
                              , content_null = min_cts_null
                              , content_c_fun = min_c_fun }
            , encod_model = max_pat }
            :: encoded0 }
  : T)
  end


(**)

local

fun build_tab' funs =
  Symtab.empty
  |>
    fold
      (fn (c_fun as { file, begin_line, ... } : Split_Stack.data_c_fun, lines) =>
        Symtab.map_default
          (file, Inttab.empty)
          (Inttab.map_default
            (begin_line, [])
            (cons ((c_fun, these lines), is_none lines))))
      funs
  |>
    Symtab.map (K (Inttab.map (K (rev
                                  #> split_list
                                  #> (fn (cts, cts_null) =>
                                       (cts |> split_list |> apsnd flat, forall I cts_null))))))

fun build_tab'' (uniq_pat0, tab0) xs =
  fold
    (uncurry
      (fn pat1 =>
        Symtab.fold
          (uncurry
            (fn file1 =>
              Symtab.map_default (file1, Inttab.empty)
              o
              Inttab.fold
                (fn (begin_line1, cts1) =>
                  Inttab.map_either
                    (begin_line1, empty pat1 cts1)
                    (merge pat1 cts1))))))
    xs
    (Symtab.map (K (Inttab.map (K (empty uniq_pat0)))) tab0)

in

fun build_tab x = x |>
 (map
   (apsnd build_tab')
  #> (fn [] => Symtab.empty
       | x :: xs => build_tab'' x xs))

end


(**)

local

fun serialize_uniq_pat (Uniq_pat pat) = pat

fun serialize_content
  ( { content_pat
    , content_data
    , content_length
    , content_null
    , ... }
  : encoding_line content) =
  ( serialize_uniq_pat content_pat
  , map (fn { encod_nth, encod_size, encod_line } => (encod_nth, encod_size, encod_line))
        content_data
  , content_length
  , content_null )

in

fun serialize ({ max_content = { content_pat, content_data, content_null, content_c_fun, ... }
               , min_encoded
               , ... } : T) =
  ( (content_data, content_null)
  , ( serialize_uniq_pat content_pat
    , map (fn { encod_content, encod_model } =>
             (serialize_content encod_content, serialize_uniq_pat encod_model))
          min_encoded
    , map (fn { begin_line, original_line, file_pos, ... } =>
             { begin_line = begin_line
             , original_line = original_line
             , file_pos = file_pos })
          content_c_fun ) )

end

end
\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/General/file.ML\<close>\<close> \<open>
structure Split_File =
struct

local

val insert_range = fn
    [] => []
  | x :: xs =>
      let
        val (x, xs) =
          fold
            (fn x1 as ((data1, (prev1, next1)), lines1) =>
             fn (x0 as ((data0, (prev0, next0)), lines0), xs) =>
              case (next0, prev1) of
                (SOME next0, SOME prev1) =>
                  if next0 = prev1 then
                    ( ((data1, (NONE, next1)), lines1)
                    , C_Scan.Right next0 :: C_Scan.Left ((data0, (prev0, NONE)), lines0) :: xs)
                  else
                    (x1, C_Scan.Left x0 :: xs)
              | _ => (x1, C_Scan.Left x0 :: xs))
            xs
            (x, [])
      in
        rev (C_Scan.Left x :: xs)
      end

(**)

fun filter_tilde pref_dir = map_filter (fn "~" => NONE | name => SOME name) o pref_dir

val mkdir_rec =
  fold (fn name => fn dir => 
           let
             val dir = Path.append dir (Path.basic name)
             val dir0 = Path.implode (Path.expand dir)
             val _ = if OS.FileSys.isDir dir0 handle OS.SysErr _ => false then
                       ()
                     else
                       OS.FileSys.mkDir dir0
           in
             dir
           end)
  oo filter_tilde

fun write_fic path_out_dir path_out_name file_content =
  File.write_list (Path.append path_out_dir (Path.basic path_out_name))
                  (separate "\n" file_content)

(**)

fun write_dir_list pref_dir dir_output =
 fn (_, (_, true)) => I
  | (path_out, (file_content, _)) => fn () =>
      let 
        val path_out = space_explode "/" path_out |> rev
      in
        write_fic (mkdir_rec pref_dir (path_out |> tl |> rev) dir_output)
                  (hd path_out)
                  file_content
      end

fun write_dir_list2 pref_dir pref_dir_name dir_output (path_out, contents) =
  tap (fn () =>
        fold let
               val path_out_dir = mkdir_rec pref_dir (space_explode "/" path_out) dir_output
             in
               fn ((file_content, nulls), _) => fn cpt =>
                 let
                   val _ =
                     if nulls then
                       Output.information
                         ("Empty content skipped: \""
                          ^ Path.implode path_out_dir
                          ^ "/" ^ Int.toString cpt ^ "." ^ pref_dir_name ^ "\"")
                     else
                       write_fic path_out_dir
                                 (Int.toString cpt ^ "." ^ pref_dir_name)
                                 file_content
                 in cpt + 1 end
             end
             contents
             0)

(**)

fun map_split_newline f =
  map f
  #> split_list
  #> (fn (lines, nulls) => (lines |> separate [""] |> flat, forall I nulls))

fun build_tab f_cons funs insert_ml_delim pref_dir_rm =
  Symtab.empty
  |>
    fold
      (fn ( ( { file
              , file_prev
              , file_next
              , file_pos
              , begin_line
              , original_line
              , ...}
              : Split_Stack.data_c_fun)
          , lines) =>
         Symtab.map_default
           (file, [])
           (f_cons (#1 file_pos)
                   file_prev
                   ( ( "/*@ ML \<open>" ^ @{make_unf_string} { begin_line = begin_line
                                                       , original_line = original_line
                                                       , file_pos = file_pos }
                       ^ "\<close> */"
                       :: these lines
                     , (file_prev, file_next))
                   , is_none lines)))
      funs
  |> Symtab.map
      (K (insert_ml_delim
           let
             val print_file =
               let
                 val file_cmd = "\<^file>"
               in
                 fn msg =>
                 fn NONE => []
                  | SOME file =>
                      ["/*@ " ^ msg ^ " \<comment> \<open>" ^ file_cmd ^ "\<open>" ^ pref_dir_rm file ^ "\<close>\<close> */", ""]
               end
           in
             rev
             #> insert_range
             #> map_split_newline
                 (fn C_Scan.Left ((body, (file_prev, file_next)), is_none_lines) => 
                       ( flat [ print_file "previous" file_prev
                              , body
                              , print_file "next" file_next]
                       , is_none_lines)
                   | C_Scan.Right range => (print_file "range" (SOME range), true))
           end))

fun build_tab2 funs pref_dir_rm =
  let
    val tree_output =
      build_tab (fn cpt => fn SOME _ =>
                                (fn content => cons ([content], cpt))
                            | NONE =>
                                fn content => fn (buf, cpt) :: bufs => (content :: buf, cpt) :: bufs
                                               | [] => [([content], cpt)])
                funs
                (fn f => map (apfst f) #> rev)
                pref_dir_rm
    val tree_output_index =
      Inttab.empty
      |> Symtab.fold
          (fn (path_out, [((_, nulls), cpt)]) =>
                Inttab.update_new (cpt, (path_out, nulls, NONE))
            | (path_out, contents) =>
                pair 0
                #> fold
                     (fn ((_, nulls), cpt) => fn (cpt_local, tab) =>
                        ( cpt_local + 1
                        , Inttab.update_new (cpt, (path_out, nulls, SOME cpt_local)) tab))
                     contents
                #> #2)
          tree_output
      |> Inttab.dest
  in
    (tree_output, tree_output_index)
  end

val funs_single = fn [(NONE, funs)] => funs
                   | _ => error "Not yet implemented"

in

fun write_raw dir_output funs pref_dir pref_dir_name pref_dir_rm =
  Symtab.fold
    (case dir_output of
       NONE => K I
     | SOME dir_output => write_dir_list (pref_dir pref_dir_name) dir_output)
    (build_tab (K (K cons)) (funs_single funs) I pref_dir_rm)
    ()

fun write_index dir_output funs pref_dir pref_dir_name pref_dir_rm =
  let
    val pref_dir = pref_dir pref_dir_name
    val (tree_output, tree_output_index) = build_tab2 (funs_single funs) pref_dir_rm
    val () =
      case dir_output of
        NONE => ()
      | SOME dir_output =>
        File.write_list
          (Path.append dir_output (Path.basic (pref_dir_name ^ ".thy")))
          ([ [ "theory " ^ pref_dir_name
             , "  imports Isabelle_C.C_Main"
             , "begin"
             , ""
             , "declare [[C_starting_env = last]]"
             , "" ]
           , map
               (fn (_, (path_out, nulls, ext)) =>
                 (if nulls then "\<comment>" else "C_file")
                 ^ " "
                 ^ Symbol.open_
                 ^ space_implode
                     "/"
                     let
                       val path_out = filter_tilde pref_dir (space_explode "/" path_out)
                     in
                       case ext of NONE => path_out
                                 | SOME nb => path_out @ [Int.toString nb ^ "." ^ pref_dir_name]
                     end
                 ^ Symbol.close)
               tree_output_index
           , [ ""
             , "end" ]]
           |> flat
           |> map (fn s => s ^ "\n"))
  in
    Symtab.fold
      (case dir_output of
         NONE => K I
       | SOME dir_output =>
         fn (path_out, [(content, _)]) => write_dir_list pref_dir dir_output (path_out, content)
          | path_cts => write_dir_list2 pref_dir pref_dir_name dir_output path_cts)
      tree_output
      ()
  end

fun write_diff dir_output funs pref_dir pref_dir_name _ =
  Symtab.fold
    (case dir_output of
       NONE => K I
     | SOME dir_output =>
        write_dir_list (pref_dir pref_dir_name) dir_output
        o
        apsnd
          (Inttab.dest
           #>
           map_split_newline
             (#2
              #> Split_Merge.serialize
              #> (fn ((content_data, content_null), data) =>
                   ("/*@ ML \<open>" ^ @{make_unf_string} data ^ "\<close> */" :: content_data, content_null)))))
    (Split_Merge.build_tab (map (apfst (fn SOME s => s | NONE => error "Not yet implemented"))
                                funs))
    ()

end

end
\<close>

ML \<open>
structure Split_Stack' =
struct
fun read_lines' data_get =
  Split_Stack.read_lines data_get
  #> apsnd (Split_Stack.fill_prev_next_pos
            #> pair (NONE : Split_Merge.uniq_pat option)
            #> single)
end
\<close>

ML \<open>
structure Split_File_Index =
struct

fun fold_lines f fic acc =
  fic
  |> Path.explode
  |> File.read_lines
  |> (fn lines => fold f lines acc)

fun read_line_c gthy =
  Split_Stack.read_lines0 Split_Stack.Data_C_Fun.get gthy
  |> apsnd Split_Stack.fill_prev_next_pos

val read_line_pml = Split_Stack.read_lines0 Split_Stack.Data_PML_Fun.get

fun split_file_index fic_pat fic_path read_line put gthy =
  ([], gthy)
  |>
    fold_lines
      (fn path0 => fn (c_funs, gthy) =>
        let
          val path = Path.explode path0
          val src = File.read path
          val pos = Path.position path
          val gthy =
            gthy
            |> Split_Module.Data_In_Source.map (cons (Input.source false src (pos, pos)))
            |> Split_Outer_File.command_split0 (split_lines src) pos
          val (_, funs) = read_line gthy
        in
          (funs :: c_funs, put [] gthy)
        end)
      fic_path
  |> apfst (rev #> map2 pair (rev (fold_lines (cons o SOME o Split_Merge.Uniq_pat) fic_pat [])))

fun split_file_index0 (fic_pat, pos_pat) (fic_path, pos_path) =
  case (OS.Process.getEnv fic_pat, OS.Process.getEnv fic_path) of
    (SOME fic_pat, SOME fic_path) =>
      (fn read_line => fn put => Context.>>> (split_file_index fic_pat fic_path read_line put))
  | (fic_pat0, fic_path0) =>
      K (K [])
      |> tap (fn _ => if is_none fic_pat0 then Split_Stack.undef fic_pat pos_pat else ())
      |> tap (fn _ => if is_none fic_path0 then Split_Stack.undef fic_path pos_path else ())

end
\<close>

end
