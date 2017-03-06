Require Import L2.compile.
Require Import L2.wcbvEval.
Require Import certiClasses.
Require Import Common.Common.
Require Import L1g.instances.

Instance bigStepOpSemL2Term : BigStepOpSem (Program L2.compile.Term) :=
  BigStepOpWEnv _ WcbvEval.

(** FIX!! *)
Instance WfL2Term : GoodTerm (Program L2.compile.Term) :=
  fun _  => True.

Instance certiL2 : CerticoqLanguage (Program L2.compile.Term) := {}.

Instance certiL1g_to_L2: 
  CerticoqTotalTranslation (Program L1g.compile.Term)
                           (Program L2.compile.Term) :=
  stripProgram.


Require Import certiClasses2.

Check (@CerticoqTranslationCorrect _ _ bigStepOpSemL2Term WfL2Term).

(***
Instance certiL1g_to_L2Correct :
  CerticoqTranslationCorrect bigStepOpSemL2Term WfL2Term.
***)