Require compcert.common.AST
        compcert.common.Errors
        compcert.common.Values
        compcert.lib.Integers
        compcert.cfrontend.Cop
        compcert.cfrontend.Ctypes
        compcert.cfrontend.Clight
        compcert.cfrontend.Csyntax
        compcert.lib.Coqlib
        compcert.lib.Floats
        compcert.common.Globalenvs
        Int31.

Require Glue.glue
        Compiler.pipeline.

(* Standard lib *)
Require Import ExtrOcamlBasic ExtrOcamlString ExtrOCamlFloats ExtrOCamlInt63.
Require Import Coq.extraction.Extraction.
Require Import ZArith NArith.
Require Import ExtrOcamlBasic.

(* Coqlib *)
Extract Inlined Constant Coqlib.proj_sumbool => "(fun x -> x)".

(* L6_to_Clight *)
(* Extract Constant pipeline.print_Clight => "PrintClight.print_if". *)
(* Extract Constant L6_to_Clight.print_Clight_dest => "PrintClight.print_dest". *)
(* Extract Constant L6_to_Clight.print_Clight_dest_names => "PrintClight.print_dest_names". *)
(* Extract Constant pipeline.print_Clight_names_dest_imports => "PrintClight.print_dest_names_imports". *)
(* Extract Constant pipeline.print => "print_string". *)


(* Time each phase, print to debug channel *)

Extract Constant AstCommon.timePhase =>
"(fun c x a -> let time = Unix.gettimeofday() in
               let temp = x a in
               let time = (Unix.gettimeofday() -. time) in
               Feedback.msg_debug (Pp.str (Printf.sprintf ""Time elapsed in %s:  %f"" ((fun s-> (String.concat """" (List.map (String.make 1) s))) c) time));
               temp)".

Extract Inductive positive => int
[ "(fun p->1+2*p)" "(fun p->2*p)" "1" ]
"(fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))".

Extract Inductive Z => int [ "0" "" "(~-)" ]
"(fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))".

Extract Inductive N => int [ "0" "" ]
"(fun f0 fp n -> if n=0 then f0 () else fp n)".


Extract Constant Pos.add => "(+)".
Extract Constant Pos.succ => "Pervasives.succ".
Extract Constant Pos.pred => "fun n -> Pervasives.max 1 (n-1)".
Extract Constant Pos.sub => "fun n m -> Pervasives.max 1 (n-m)".
Extract Constant Pos.mul => "( * )".
Extract Constant Pos.min => "Pervasives.min".
Extract Constant Pos.max => "Pervasives.max".
Extract Constant Pos.compare =>
 "fun x y -> if x=y then 0 else if x<y then -1 else 1".
Extract Constant Pos.compare_cont =>
 "fun c x y -> if x=y then c else if x<y then -1 else 1".

Extract Constant N.add => "(+)".
Extract Constant N.succ => "Pervasives.succ".
Extract Constant N.pred => "fun n -> Pervasives.max 0 (n-1)".
Extract Constant N.sub => "fun n m -> Pervasives.max 0 (n-m)".
Extract Constant N.mul => "( * )".
Extract Constant N.min => "Pervasives.min".
Extract Constant N.max => "Pervasives.max".
Extract Constant N.div => "fun a b -> if b=0 then 0 else a/b".
Extract Constant N.modulo => "fun a b -> if b=0 then a else a mod b".
Extract Constant N.compare =>
 "fun x y -> if x=y then 0 else if x<y then -1 else 1".


Extract Constant Z.add => "(+)".
Extract Constant Z.succ => "Pervasives.succ".
Extract Constant Z.pred => "Pervasives.pred".
Extract Constant Z.sub => "(-)".
Extract Constant Z.mul => "( * )".
Extract Constant Z.opp => "(~-)".
Extract Constant Z.abs => "Pervasives.abs".
Extract Constant Z.min => "Pervasives.min".
Extract Constant Z.max => "Pervasives.max".
Extract Constant Z.compare =>
 "fun x y -> if x=y then 0 else if x<y then -1 else 1".

Extract Constant Z.of_N => "fun p -> p".
Extract Constant Z.abs_N => "Pervasives.abs".

(* Int31 *)
Extract Inductive Int31.digits => "bool" [ "false" "true" ].
Extract Inductive Int31.int31 => "int" [ "Camlcoq.Int31.constr" ] "Camlcoq.Int31.destr".
Extract Constant Int31.twice => "Camlcoq.Int31.twice".
Extract Constant Int31.twice_plus_one => "Camlcoq.Int31.twice_plus_one".
Extract Constant Int31.compare31 => "Camlcoq.Int31.compare".
Extract Constant Int31.On => "0".
Extract Constant Int31.In => "1".

Extract Inductive Decimal.int => unit [ "(fun _ -> ())" "(fun _ -> ())" ] "(fun _ _ _ -> assert false)".
Extract Inductive Hexadecimal.int => unit [ "(fun _ -> ())" "(fun _ -> ())" ] "(fun _ _ _ -> assert false)".
Extract Inductive Numeral.int => unit [ "(fun _ -> ())" "(fun _ -> ())" ] "(fun _ _ _ -> assert false)".

Extraction Inline Equations.Prop.Classes.noConfusion.
Extraction Inline Equations.Prop.Logic.eq_elim.
Extraction Inline Equations.Prop.Logic.eq_elim_r.
Extraction Inline Equations.Prop.Logic.transport.
Extraction Inline Equations.Prop.Logic.transport_r.
Extraction Inline Equations.Prop.Logic.False_rect_dep.
Extraction Inline Equations.Prop.Logic.True_rect_dep.
Extraction Inline Equations.Init.pr1.
Extraction Inline Equations.Init.pr2.
Extraction Inline Equations.Init.hidebody.
Extraction Inline Equations.Prop.DepElim.solution_left.

Extract Inlined Constant RandyPrelude.ascii_dec_bool => "(=)".

(* Avoid name clashes with OCaml or Coq module names *)
Extraction Blacklist config List String Nat Int Ast Universes UnivSubst Typing Retyping 
           OrderedType Logic Common Equality Char char uGraph
           Instances Classes Term Monad Coqlib Errors Compile Checker Eq Classes0 Numeral
           Uint63 Number.

(* Cutting the dependency to R.
Extract Inlined Constant Fcore_defs.F2R => "fun _ -> assert false".
Extract Inlined Constant Fappli_IEEE.FF2R => "fun _ -> assert false".
Extract Inlined Constant Fappli_IEEE.B2R => "fun _ -> assert false".
Extract Inlined Constant Fappli_IEEE.round_mode => "fun _ -> assert false".
Extract Inlined Constant Fcalc_bracket.inbetween_loc => "fun _ -> assert false". *)

Extraction Library Zeven.
Extraction Library Zeven.
Extraction Library ZArith_dec.
Extraction Library Sumbool.
Extraction Library Zbool.
Extraction Library SpecFloat.
Separate Extraction FloatOps.Prim2SF.

Cd "Extraction".
Separate Extraction
         Ctypes.merge_attributes Ctypes.remove_attributes Ctypes.build_composite_env
         Csyntax
         Ctypes.make_program
         AST.signature_main
         Floats.Float32.from_parsed Floats.Float.from_parsed
         Floats.Float32.of_bits Floats.Float.of_bits
         Floats.Float32.to_bits Floats.Float.to_bits
         String.length
         Compiler.pipeline.make_opts
         Compiler.pipeline.compile
         Glue.glue.generate_glue
         Glue.ffi.generate_ffi
         cps.M.elements
         Compiler.pipeline.show_IR.

Recursive Extraction Library BinPos.
Recursive Extraction Library OrdersTac.

Cd "..".
