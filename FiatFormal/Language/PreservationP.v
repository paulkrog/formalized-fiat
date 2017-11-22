
Require Import FiatFormal.Language.Step.
Require Import FiatFormal.Language.SubstExpExp.
Require Import FiatFormal.Language.SubstTypeExp.
Require Import FiatFormal.Language.SubstTypeType.
Require Import FiatFormal.Language.TyJudge.

Require Import FiatFormal.Language.SubstExistential.
Require Import FiatFormal.Language.Preservation.


(* When a closed program takes a step the result has the same type. *)
Theorem preservationP
  : forall pb ds pbOK p p' t,
    TYPEPROG ds nil nil p t
    -> STEPP pb ds pbOK p p'
    -> TYPEPROG ds nil nil p' t.
Proof.
  intros pb ds pbOK p p' t HT HS.
  gen pb ds pbOK p' t.
  induction p; intros.
  Case "PLet".
  invert HS; intros.
  invert HT; intros; subst.
  invert H; intros; subst.

  (* new *)
  inversion H6; subst.
  eapply subst_ADT_prog'; eauto.
  cut (forall m t, TYPEMETHOD r ds nil nil m (substTT 0 r t)
              -> TYPE ds nil nil (body m) (substTT 0 r t)); intros.
  apply Forall2_map_left.
  apply Forall2_map_right.
  eapply Forall2_impl with (R1 := (fun m y => TYPEMETHOD r ds nil nil m (substTT 0 r y))).
  intros. apply H. auto.
  apply Forall2_map_right'.
  apply mapCtor in H4; subst; auto.
  intros. inversion H0; auto.
  inversion H; subst. simpl; auto.
  (* end new *)

  Case "PExp".
  invert HS; intros; subst.
  invert HT; intros; subst.
  apply TYExp.
  apply (preservation _ _ _ _ _ _ H3 H0).
Qed.
(* Proof. *)
(*   intros pb ds pbOK p p' t HT HS. *)
(*   gen pb ds pbOK p' t. *)
(*   induction p; intros. *)
(*   Case "PLet". *)
(*   invert HS; intros. *)
(*   invert HT; intros; subst. *)
(*   invert H; intros; subst. *)
(*   eapply subst_ADT_prog; invert H7; intros; subst. *)
(*   simpl in *. eassumption. *)
(*   eassumption. *)
(*   assumption. *)
(*   Case "PExp". *)
(*   invert HS; intros; subst. *)
(*   invert HT; intros; subst. *)
(*   apply TYExp. *)
(*   apply (preservation _ _ _ _ _ _ H4 H0). *)
(* Qed. *)


(* (* When we multi-step evaluate some expression, *)
(*    then the result has the same type as the original. *)
(*  *) *)
(* Lemma preservation_steps *)
(*   : forall ds x1 t1 x2, *)
(*     TYPE ds nil nil x1 t1 *)
(*     -> STEPS x1 x2 *)
(*     -> TYPE ds nil nil x2 t1. *)
(* Proof. *)
(*  intros. *)
(*  induction H0; eauto. *)
(*   eapply preservation; eauto. *)
(* Qed. *)


(* (* When we multi-step evaluate some expression, *)
(*    then the result has the same type as the original. *)
(*    Using the left-linearised form for the evaluation. *)
(*  *) *)
(* Lemma preservation_stepsl *)
(*   : forall ds x1 t1 x2, *)
(*     TYPE ds nil nil x1 t1 *)
(*     -> STEPSL x1 x2 *)
(*     -> TYPE ds nil nil x2 t1. *)
(* Proof. *)
(*  intros. *)
(*  induction H0. *)
(*   auto. *)
(*   apply IHSTEPSL. *)
(*   eapply preservation. *)
(*    eauto. auto. *)
(* Qed. *)
