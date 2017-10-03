
Require Import FiatFormal.Language.Step.
Require Import FiatFormal.Language.SubstExpExp.
Require Import FiatFormal.Language.SubstTypeExp.
Require Import FiatFormal.Language.SubstTypeType.
Require Import FiatFormal.Language.TyJudge.


(* When a program takes a step the results has the same type. *)
Theorem preservationP
 :  forall ke te p p' t
 ,  TYPEPROG ke te p t
 -> STEPP p p'
 -> TYPEPROG ke te p' t.
Proof.
  intros ke te x x' t HT HS.
  gen ke te x' t.
  induction x; intros.
  Case "PLet".
  invert HS; intros.


 intros ke te x x' t HT HS.
 gen ke te x' t.
 induction x; intros.

 Case "XVar".
  inverts HS.

 Case "XLAM".
  inverts HS.

 Case "XAPP".
  inverts HT.
  inverts keep HS.

  SCase "ESAPPLAM".
   inverts H3.
   eapply subst_type_value in H4; eauto.
   rewrite substTE_liftTE in H4. auto.

  SCase "ESAPP1".
   apply TYAPP; eauto.

 Case "XLam".
  inverts HS.

 Case "XApp".
  inverts HT.
  inverts keep HS.

  SCase "ESAppLam".
   inverts H3.
   lets D: subst_value_value H9 H5. auto.

  SCase "EsApp1".
   eapply TYApp; eauto.

  SCase "EsApp2".
   eapply TYApp; eauto.
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
