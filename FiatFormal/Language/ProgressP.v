
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
    -> valueP p \/ (exists p', STEPP p p') \/ hasChoiceP p.
Proof.
  intros. induction p.
  Case "PLet".
  right. left.
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
  destruct H as [| []];

  eauto.
  SCase "e value".
  left; repeat constructor.
  inversion H; auto.
  unfold closedP. simpl.
  inversion H. unfold closedX in *. assumption.

  SCase "e steps".
  right. left. dest H. exists (PEXP x'). auto.

  SCase "e hasChoice".
  repeat right.
  inversion H.

  (* intros. *)
  (* induction p. *)
  (* Case "PLet". *)
  (* right. *)
  (* destruct H as [tp]. *)
  (* inverts H. *)
  (* invert_adt_type. *)
  (* eexists. *)
  (* eapply SP_Prog. *)
  (* Case "PExp". *)
  (* inverts H. *)
  (* invert_prog_type. *)
  (* rename x into t. *)
  (* pose proof (progress e). *)
  (* destruct H. eexists. eassumption. (* TODO: ask ben why ex_spec *) *)
  (*                               (* doesn't match here *) *)
  (* left; repeat constructor. *)
  (* inversion H; auto. *)
  (* unfold closedP. simpl. *)
  (* inversion H. unfold closedX in *. assumption. (* TODO: ask ben how *) *)
  (* (* to write Ltac to automate this *) *)
  (* right. dest H. exists (PEXP x'). auto. *)
Qed.
