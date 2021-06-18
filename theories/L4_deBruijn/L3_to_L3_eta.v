(** Intermediate L3_eta language.

  Enforce eta-expanded branches in match, so that the following L3-L4 phase
  can strip them correctly. 

  Note that we cannot optimize by not eta-expanding a branch which has already
  enough lambdas as this would not be a substitutive operation: 
  translation of terms before or after substitution would only be alpha-beta equivalent,
  not syntactically equal.

  We hence leave it to later phases to reduce the potentially dummy beta-redexes
  that are produced here. They would be of the form (\x1 .. xn. t) y1 .. yn where the
  y's are always variables.
*)

Require Import Coq.Arith.Arith Coq.NArith.BinNat Coq.Strings.String Coq.Lists.List
        Coq.omega.Omega Coq.Program.Program Coq.micromega.Psatz.
Require Export Common.Common.  (* shared namespace *)
Open Scope N_scope.
Opaque N.add.
Opaque N.sub.
Require Import L2k.compile.
Module L3t := L2k.compile.
Require Import L4.expression.

(** Tactics *)
Ltac forward H :=
  match type of H with
  | ?T -> _ => let H' := fresh in enough (H' : T);[ specialize (H H'); clear H' | ]
  end.

Import L3t.

Section TermTranslation.

  Fixpoint is_n_lambda n t :=
    match n with
    | 0%nat => true
    | S n => match t with
            | TLambda _ t => is_n_lambda n t
            | _ => false
            end
    end.

  (* Move Γ |- body : τ1 -> .. -> τn -> τ to 
     Γ, x1 : τ1, .., xn : τn |- body x1 .. xn : τ
   *)

  Fixpoint eta_expand (n : nat) (t : Term) : Term :=
    match n with
    | 0%nat => t
    | S n' => TLambda nAnon (eta_expand n' (TApp (lift 0 t) (TRel 0)))
    end.
      
  Eval compute in is_n_lambda 1 (TLambda (nNamed "x") (TRel 0)).
  Eval compute in eta_expand 1 (TLambda (nNamed "x") (TRel 0)).
  
  Eval compute in eta_expand 2 (TLambda (nNamed "x") (TRel 0)).
  Eval compute in eta_expand 2 (TLambda (nNamed "x") (TRel 1)).
    
  Eval compute in eta_expand 3 (TRel 0).
  Eval compute in eta_expand 1 (TLambda (nNamed "x") (TRel 0)).
  Eval compute in eta_expand 2 (TLambda (nNamed "x") (TRel 1)).
  
  Fixpoint trans (t : Term) : Term :=
    match t with
    | TWrong str => TWrong str
    | TProof => TProof
    | TRel n => TRel n
    | TLambda n t => TLambda n (trans t)
    | TLetIn n t u => TLetIn n (trans t) (trans u)
    | TApp t u => TApp (trans t) (trans u)
    | TConst s => TConst s
    | TConstruct ind c args =>      
      TConstruct ind c (trans_terms args)
    | TCase ind t brs =>
      TCase ind (trans t) (trans_brs ind brs)
    | TFix d n =>
      let defs' := trans_fixes d in
      TFix defs' n
    | TProj _ _ => TWrong "TProj"
    end

  with trans_terms (ts : Terms) : Terms :=
    match ts with
    | tnil => tnil
    | tcons t ts => tcons (trans t) (trans_terms ts)
    end
  with trans_brs (i : inductive) (brs : Brs) : Brs :=
    match brs with
    | bnil => bnil
    | bcons n t brs =>
      let transt := trans t in
      let etat := eta_expand n transt in
      bcons n etat (trans_brs i brs)
    end
  with trans_fixes (d : Defs) : Defs :=
    match d with
    | dnil => dnil
    | dcons na t n ds => dcons na (trans t) n (trans_fixes ds)
    end.
  
End TermTranslation.

Definition transEC (ec:envClass Term) : envClass Term :=
  match ec with
    | ecTrm t => ecTrm (trans t)
    | ecTyp n itp => ecTyp _ n itp
  end.

Fixpoint transEnv (p:environ Term) : environ Term :=
  match p with
    | nil => nil
    | cons (nm, ec) q => cons (nm, transEC ec) (transEnv q)
  end.

(** start-to-L4 translations **)

Definition translate_program
           (e : environ L3t.Term) (t : L3t.Term) : L3t.Term :=
  trans t.

Definition Program_Program (pgm : Program L3t.Term) : Program L3t.Term :=
  let 'mkPgm main env := pgm in
  {| main := trans main; env := transEnv env |}.
