
Require Import FiatFormal.Language.Step.
Require Import FiatFormal.Language.SubstExpExp.
Require Import FiatFormal.Language.SubstTypeExp.
Require Import FiatFormal.Language.SubstTypeType.
Require Import FiatFormal.Language.TyJudge.


(* A well typed expression is either a value, or can take a step. *)
Theorem progress
 :  forall x
 ,  (exists t, TYPE nil nil x t)
 -> value x \/ (exists x', STEP x x') \/ hasChoiceX x.
Proof.
 intros.
 induction x; destruct H as [tx].

 Case "XVar".
  inverts H. false.

 (* Case "XLAM". *)
 (*  left. apply type_wfX in H. auto. *)

 (* Case "XAPP". *)
 (*  inverts H. *)
 (*  destruct IHx. eauto. *)
 (*  SCase "x value". *)
 (*   right. inverts H. inverts H4. *)
 (*    inverts H1. false. *)
 (*    inverts H0. *)
 (*    exists (substTX 0 t x1). eapply ESLAMAPP. *)
 (*    inverts H0. *)
 (*  SCase "x steps". *)
 (*   right. *)
 (*    destruct H as [x']. *)
 (*    exists (XAPP x' t). *)
 (*    apply ESAPP1. auto. *)

 Case "XLam".
  left. apply type_wfX in H. auto.

 Case "XApp".
  right.
  inverts H.
  destruct IHx1 as [| []]; eauto.
  SCase "x1 value".
  destruct IHx2 as [| []]; eauto.

   SSCase "x2 value".
   left.
   inverts H.
   inverts H1.
   inverts H2. false.
   inverts H4.
   exists (substXX 0 x2 x0). apply ESLamApp. auto.

   SSCase "x2 steps".
   left.
   destruct H0 as [x2'].
   exists (XApp x1 x2').
   apply ESApp2; auto.

   SSCase "x2 hasChoice".
   inversion H0.

  SCase "x1 steps".
  left.
  destruct H as [x1'].
  exists (XApp x1' x2).
  apply ESApp1; auto.

  SCase "x1 hasChoice".
  inversion H.
Qed.
