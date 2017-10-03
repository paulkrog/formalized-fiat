
Require Import FiatFormal.Language.Step.
Require Import FiatFormal.Language.SubstExpExp.
Require Import FiatFormal.Language.SubstTypeExp.
Require Import FiatFormal.Language.SubstTypeType.
Require Import FiatFormal.Language.TyJudge.
Require Import FiatFormal.Language.Progress.

(* A well typed program is either a value, can take a step, or has a choice. *)
Theorem progressP
  : forall p,
    (exists t, TYPEPROG nil nil p t)
    -> valueP p \/ (exists p', STEPP p p'). (* \/ hasChoiceP p. *)
Proof.
  intros.
  induction p.
  Case "PLet".
  right.
  destruct H as [tp].
  inverts H.
  invert_adt_type.
  eexists.
  eapply SP_Prog.
  Case "PExp".
  inverts H.
  invert_prog_type.
  rename x into t.
  pose proof (progress e).
  destruct H. eexists. eassumption. (* TODO: ask ben why ex_spec *)
                                (* doesn't match here *)
  left; repeat constructor.
  inversion H; auto.
  unfold closedP. simpl.
  inversion H. unfold closedX in *. assumption. (* TODO: ask ben how *)
  (* to write Ltac to automate this *)
  right. dest H. exists (PEXP x'). auto.
Qed.

(*  intros. *)
(*  induction p; destruct H as [tx]. *)

(*  Case "XVar". *)
(*   inverts H. false. *)

(*  Case "XLAM". *)
(*   left. apply type_wfX in H. auto. *)

(*  Case "XAPP". *)
(*   inverts H. *)
(*   destruct IHx. eauto. *)
(*   SCase "x value". *)
(*    right. inverts H. inverts H4. *)
(*     inverts H1. false. *)
(*     inverts H0. *)
(*     exists (substTX 0 t x1). eapply ESLAMAPP. *)
(*     inverts H0. *)
(*   SCase "x steps". *)
(*    right. *)
(*     destruct H as [x']. *)
(*     exists (XAPP x' t). *)
(*     apply ESAPP1. auto. *)

(*  Case "XLam". *)
(*   left. apply type_wfX in H. auto. *)

(*  Case "XApp". *)
(*   right. *)
(*   inverts H. *)
(*   destruct IHx1; eauto. *)
(*   SCase "x1 value". *)
(*    destruct IHx2; eauto. *)
(*    inverts H. *)

(*    SSCase "x2 value". *)
(*     inverts H1. *)
(*      inverts H2. false. *)
(*      inverts H4. *)
(*      exists (substXX 0 x2 x0). apply ESLamApp. auto. *)

(*    SSCase "x2 steps". *)
(*     destruct H0 as [x2']. *)
(*     exists (XApp x1 x2'). *)
(*     apply ESApp2; auto. *)

(*   SCase "x1 steps". *)
(*    destruct H as [x1']. *)
(*    exists (XApp x1' x2). *)
(*    apply ESApp1; auto. *)
(* Qed. *)
