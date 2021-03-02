(**********************************************************************)
(* CertiCoq                                                           *)
(* Copyright (c) 2017                                                 *)
(**********************************************************************)

open Pp
open Printer
open Metacoq_template_plugin.Ast_quoter
open ExceptionMonad
open AstCommon
open Plugin_utils

(** Various Utils *)

(* TODO move to plugin_utils *)

let pr_char c = str (Char.escaped c)

let pr_char_list =
  prlist_with_sep mt pr_char

let string_of_chars (chars : char list) : string =
  let buf = Buffer.create 16 in
  List.iter (Buffer.add_char buf) chars;
  Buffer.contents buf

let chars_of_string (s : string) : char list =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

(* remove duplicates but preserve order, keep the leftmost element *)
let nub (xs : 'a list) : 'a list = 
  List.fold_right (fun x xs -> if List.mem x xs then xs else x :: xs) xs []

let rec coq_nat_of_int x =
  match x with
  | 0 -> Datatypes.O
  | n -> Datatypes.S (coq_nat_of_int (pred n))

let debug_msg (flag : bool) (s : string) =
  if flag then
    Feedback.msg_debug (str s)
  else ()

let printProg prog names (dest : string) (import : string list) =
  PrintClight.print_dest_names_imports prog (Cps.M.elements names) dest import

(** Compilation Command Arguments *)

type command_args =
 | CPS
 | TIME
 | TIMEANF
 | OPT of int
 | DEBUG
 | ARGS of int
 | ANFCONFIG of int (* To measure different ANF configurations *)
 | EXT of string (* Filename extension to be appended to the file name *)
 | DEV of int    (* For development purposes *)
 | PREFIX of string (* Prefix to add to the generated FFI fns, avoids clashes with C fns *)
 | FILENAME of string (* Name of the generated file *)

type options =
  { cps       : bool;
    time      : bool;
    time_anf  : bool;
    olevel    : int;
    debug     : bool;
    args      : int;
    anf_conf  : int;
    filename  : string;
    ext       : string;
    dev       : int;
    prefix    : string;
    prims     : ((BasicAst.kername * char list) * bool)  list;
  }

let default_options : options =
  { cps       = false;
    time      = false;
    time_anf  = false;
    olevel    = 1;
    debug     = false;
    args      = 5;
    anf_conf  = 0;
    filename  = "";
    ext       = "";
    dev       = 0;
    prefix    = "";
    prims     = [];
  }


let make_options (l : command_args list) (pr : ((BasicAst.kername * char list) * bool) list) (fname : string) : options =
  let rec aux (o : options) l =
    match l with
    | [] -> o
    | CPS      :: xs -> aux {o with cps = true} xs
    | TIME     :: xs -> aux {o with time = true} xs
    | TIMEANF  :: xs -> aux {o with time_anf = true} xs
    | OPT n    :: xs -> aux {o with olevel = n} xs
    | DEBUG    :: xs -> aux {o with debug = true} xs
    | ARGS n   :: xs -> aux {o with args = n} xs
    | ANFCONFIG n :: xs -> aux {o with anf_conf = n} xs
    | EXT s    :: xs -> aux {o with ext = s} xs
    | DEV n    :: xs -> aux {o with dev = n} xs
    | PREFIX s :: xs -> aux {o with prefix = s} xs
    | FILENAME s :: xs -> aux {o with filename = s} xs
  in
  let opts = { default_options with filename = fname } in
  let o = aux opts l in
  {o with prims = pr}

let make_pipeline_options (opts : options) =
  let cps    = opts.cps in
  let args = coq_nat_of_int opts.args in
  let olevel = coq_nat_of_int opts.olevel in
  let timing = opts.time in
  let timing_anf = opts.time_anf in
  let debug  = opts.debug in
  let anfc = coq_nat_of_int opts.anf_conf in
  let dev = coq_nat_of_int opts.dev in
  let prefix = chars_of_string opts.prefix in
  let prims = opts.prims in
  Pipeline.make_opts cps args anfc olevel timing timing_anf debug dev prefix prims


(** Main Compilation Functions *)

(* Get fully qualified name of a constant *)
let get_name (gr : Names.GlobRef.t) : string =
  match gr with
  | Names.GlobRef.ConstRef c -> Names.KerName.to_string (Names.Constant.canonical c)
  | _ -> CErrors.user_err ~hdr:"template-coq" (Printer.pr_global gr ++ str " is not a constant definition")


(* Quote Coq term *)
let quote opts gr =
  let debug = opts.debug in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, c = Evarutil.new_global sigma gr in
  debug_msg debug "Quoting";
  let time = Unix.gettimeofday() in
  let term = Metacoq_template_plugin.Ast_quoter.quote_term_rec true env (EConstr.to_constr sigma c) in
  let time = (Unix.gettimeofday() -. time) in
  debug_msg debug (Printf.sprintf "Finished quoting in %f s.. compiling to L7." time);
  term

(* Compile Quoted term with CertiCoq *)
let compile opts term imports =
  let debug = opts.debug in
  let options = make_pipeline_options opts in
  let p = Pipeline.compile options term in
  match p with
  | (CompM.Ret ((nenv, header), prg), dbg) ->
    debug_msg debug "Finished compiling, printing to file.";
    let time = Unix.gettimeofday() in
    let fname = opts.filename in
    let suff = opts.ext in
    let cstr = fname ^ suff ^ ".c" in
    let hstr = fname ^ suff ^ ".h" in
    printProg prg nenv cstr imports (* (List.map Tm_util.string_to_list imports) *);
    printProg header nenv hstr [];

    (* let cstr = Metacoq_template_plugin.Tm_util.string_to_list (Names.KerName.to_string (Names.Constant.canonical const) ^ suff ^ ".c") in
     * let hstr = Metacoq_template_plugin.Tm_util.string_to_list (Names.KerName.to_string (Names.Constant.canonical const) ^ suff ^ ".h") in
     * Pipeline.printProg (nenv,prg) cstr;
     * Pipeline.printProg (nenv,header) hstr; *)
    let time = (Unix.gettimeofday() -. time) in
    Feedback.msg_debug (str (Printf.sprintf "Printed to file in %f s.." time));
    debug_msg debug "Pipeline debug:";
    debug_msg debug (string_of_chars dbg)
  | (CompM.Err s, dbg) ->
    debug_msg debug "Pipeline debug:";
    debug_msg debug (string_of_chars dbg);
    CErrors.user_err ~hdr:"pipeline" (str "Could not compile: " ++ (pr_char_list s) ++ str "\n")

(* Generate glue code for the compiled program *)
let generate_glue (standalone : bool) opts globs =
  if standalone && opts.filename = "" then
    CErrors.user_err ~hdr:"glue-code" (str "You need to provide a file name with the -file option.")
  else
  let debug = opts.debug in
  let options = make_pipeline_options opts in

  let time = Unix.gettimeofday() in
  (match Glue.generate_glue options globs with
  | CompM.Ret (((nenv, header), prg), logs) ->
    let time = (Unix.gettimeofday() -. time) in
    debug_msg debug (Printf.sprintf "Generated glue code in %f s.." time);
    (match logs with [] -> () | _ ->
      debug_msg debug (Printf.sprintf "Logs:\n%s" (String.concat "\n" (List.map string_of_chars logs))));
    let time = Unix.gettimeofday() in
    let suff = opts.ext in
    let fname = opts.filename in
    let cstr = if standalone then fname ^ ".c" else "glue." ^ fname ^ suff ^ ".c" in
    let hstr = if standalone then fname ^ ".h" else "glue." ^ fname ^ suff ^ ".h" in
    printProg prg nenv cstr [];
    printProg header nenv hstr [];

    let time = (Unix.gettimeofday() -. time) in
    debug_msg debug (Printf.sprintf "Printed glue code to file in %f s.." time)
  | CompM.Err s ->
    CErrors.user_err ~hdr:"glue-code" (str "Could not generate glue code: " ++ pr_char_list s))


let compile_with_glue (opts : options) (gr : Names.GlobRef.t) (imports : string list) : unit =
  let term = quote opts gr in
  compile opts (Obj.magic term) imports;
  generate_glue false opts (fst (Obj.magic term))

let compile_only opts gr imports =
  let term = quote opts gr in
  compile opts (Obj.magic term) imports

let generate_glue_only opts gr =
  let term = quote opts gr in
  generate_glue true opts (fst (Obj.magic term))

let print_to_file (s : string) (file : string) =
  let f = open_out file in
  Printf.fprintf f "%s\n" s;
  close_out f

let show_ir opts gr =
  let term = quote opts gr in
  let debug = opts.debug in
  let options = make_pipeline_options opts in
  let p = Pipeline.show_IR options (Obj.magic term) in
  match p with
  | (CompM.Ret prg, dbg) ->
    debug_msg debug "Finished compiling, printing to file.";
    let time = Unix.gettimeofday() in
    let suff = opts.ext in
    let fname = opts.filename in
    let file = fname ^ suff ^ ".ir" in
    print_to_file (string_of_chars prg) file;
    let time = (Unix.gettimeofday() -. time) in
    Feedback.msg_debug (str (Printf.sprintf "Printed to file in %f s.." time));
    debug_msg debug "Pipeline debug:";
    debug_msg debug (string_of_chars dbg)
  | (CompM.Err s, dbg) ->
    debug_msg debug "Pipeline debug:";
    debug_msg debug (string_of_chars dbg);
    CErrors.user_err ~hdr:"show-ir" (str "Could not compile: " ++ (pr_char_list s) ++ str "\n")


(* Quote Coq inductive type *)
let quote_ind opts gr : Metacoq_template_plugin.Ast_quoter.quoted_program * string =
  let debug = opts.debug in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, c = Evarutil.new_global sigma gr in
  let name = match gr with
    | Names.GlobRef.IndRef i -> 
        let (mut, _) = i in
        Names.KerName.to_string (Names.MutInd.canonical mut)
    | _ -> CErrors.user_err ~hdr:"template-coq"
       (Printer.pr_global gr ++ str " is not an inductive type") in
  debug_msg debug "Quoting";
  let time = Unix.gettimeofday() in
  let term = quote_term_rec true env (EConstr.to_constr sigma c) in
  let time = (Unix.gettimeofday() -. time) in
  debug_msg debug (Printf.sprintf "Finished quoting in %f s.." time);
  (term, name)

let ffi_command opts gr =
  let (term, name) = quote_ind opts gr in
  let debug = opts.debug in
  let options = make_pipeline_options opts in

  let time = Unix.gettimeofday() in
  (match Ffi.generate_ffi options (Obj.magic term) with
  | CompM.Ret (((nenv, header), prg), logs) ->
    let time = (Unix.gettimeofday() -. time) in
    debug_msg debug (Printf.sprintf "Generated FFI glue code in %f s.." time);
    (match logs with [] -> () | _ ->
      debug_msg debug (Printf.sprintf "Logs:\n%s" (String.concat "\n" (List.map string_of_chars logs))));
    let time = Unix.gettimeofday() in
    let suff = opts.ext in
    let cstr = ("ffi." ^ name ^ suff ^ ".c") in
    let hstr = ("ffi." ^ name ^ suff ^ ".h") in
    printProg prg nenv cstr [];
    printProg header nenv hstr [];

    let time = (Unix.gettimeofday() -. time) in
    debug_msg debug (Printf.sprintf "Printed FFI glue code to file in %f s.." time)
  | CompM.Err s ->
    CErrors.user_err ~hdr:"ffi-glue-code" (str "Could not generate FFI glue code: " ++ pr_char_list s))

let glue_command opts grs =
  let terms = grs |> List.rev
              |> List.map (fun gr -> fst (quote opts gr)) 
              |> List.concat |> nub in
  generate_glue true opts (Obj.magic terms)
