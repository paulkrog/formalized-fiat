
Require Import FiatFormal.Language.Step.
Require Import FiatFormal.Language.SubstExpExp.
Require Import FiatFormal.Language.SubstTypeExp.
Require Import FiatFormal.Language.SubstTypeType.
Require Import FiatFormal.Language.TyJudge.

Require Import FiatFormal.Language.SubstExistential.
Require Import FiatFormal.Language.Preservation.

(* When a closed program takes a step the results has the same type. *)
Theorem preservationP
 :  forall p p' t
 ,  TYPEPROG nil nil p t
 -> STEPP p p'
 -> TYPEPROG nil nil p' t.
Proof.
  intros p p' t HT HS.
  gen p' t.
  induction p; intros.
  Case "PLet".
  invert HS; intros.
  invert HT; intros; subst.
  invert H; intros; subst.
  eapply subst_ADT_prog.
  simpl in *. eassumption.
  invert H6; intros; subst.
  assumption.
  Case "PExp".
  invert HS; intros; subst.
  invert HT; intros; subst.
  apply TYExp.
  apply (preservation _ _ _ _ _ H3 H0).
Qed.


(* When we multi-step evaluate some expression,
   then the result has the same type as the original.
 *)
Lemma preservation_steps
 :  forall x1 t1 x2
 ,  TYPE nil nil x1 t1
 -> STEPS x1 x2
 -> TYPE nil nil x2 t1.
Proof.
 intros.
 induction H0; eauto.
  eapply preservation; eauto.
Qed.


(* When we multi-step evaluate some expression,
   then the result has the same type as the original.
   Using the left-linearised form for the evaluation.
 *)
Lemma preservation_stepsl
 :  forall x1 t1 x2
 ,  TYPE nil nil x1 t1
 -> STEPSL x1 x2
 -> TYPE nil nil x2 t1.
Proof.
 intros.
 induction H0.
  auto.
  apply IHSTEPSL.
  eapply preservation.
   eauto. auto.
Qed.
