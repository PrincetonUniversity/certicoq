type command_args =
 | CPS
 | TIME
 | TIMEANF
 | OPT of int
 | DEBUG
 | ARGS of int 
 | ANFCONFIG of int (* The number of fvs passed as params and the original params shall not exceed this number *)
 | EXT of string (* Filename extension to be appended to the file name *)
 | DEV of int
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
    prims     : ((BasicAst.kername * char list) * bool) list;
  }

val default_options : options
val make_options : command_args list -> ((BasicAst.kername * char list) * bool) list -> string -> options

val get_name : Names.GlobRef.t -> string
  
val compile_with_glue : options -> Names.GlobRef.t -> string list -> unit
val compile_only : options -> Names.GlobRef.t -> string list -> unit
val generate_glue_only : options -> Names.GlobRef.t -> unit
val show_ir : options -> Names.GlobRef.t -> unit
val ffi_command : options -> Names.GlobRef.t -> unit
val glue_command : options -> Names.GlobRef.t list -> unit
