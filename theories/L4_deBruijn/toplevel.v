Require Import L4.expression.
Require Import Common.Common Common.compM Common.Pipeline_utils.
Require Import L2k.compile.
Require Import L4.L3_to_L4.
Require Import L4.L3_to_L3_eta.
Require Import L4.L3_eta_crct.
Require Import L4.L3_to_L3_eta_correct.
Require Import L4.L3_to_L4_correct.
Require L2k.
Require Import BinNat.

Import Monads.

Import MonadNotation.


Definition L3_eta_Program := Program L2k.compile.Term.
Typeclasses Opaque L3_eta_Program.

Definition compile_L2k_eta
  : CertiCoqTrans (Program L2k.compile.Term) L3_eta_Program:=
  fun src =>
    debug_msg "Translating from L2k to L2k - eta expansion" ;;
    (LiftCertiCoqTrans "L2k_eta" L3_to_L3_eta.Program_Program src).

(* TODO instance for correctness proof *)

Let L4Term := prod ienv L4.expression.exp.

Instance L4_Lang : Lang L4Term :=
  { Value := L4.expression.exp ;
    TermWf := fun P => L4.expression.exp_wf (0%N) (snd P);
    BigStep := fun P Res => exists n, L4.expression.eval_n n (snd P) = Some Res
  }.

Definition compile_L4 (prims : list (kername * string * bool * nat * positive))
  : CertiCoqTrans L3_eta_Program L4Term :=
  fun src =>
    debug_msg "Translating from L2k to L4" ;;
    LiftCertiCoqTrans "L4" (fun p =>  
                              (L3_to_L4.inductive_env (AstCommon.env p),
                               L3_to_L4.translate_program prims (AstCommon.env p)(main p))) src.
