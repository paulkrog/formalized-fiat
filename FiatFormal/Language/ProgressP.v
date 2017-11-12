
Require Import FiatFormal.Language.Step.
Require Import FiatFormal.Language.SubstExpExp.
Require Import FiatFormal.Language.SubstTypeExp.
Require Import FiatFormal.Language.SubstTypeType.
Require Import FiatFormal.Language.TyJudge.
Require Import FiatFormal.Language.Progress.


(* A well typed program is either a value, can take a step, or has a choice. *)
Theorem progressP
  : forall pb ds pbOK p,
    (exists t, TYPEPROG ds nil nil p t)
    -> valueP p \/ (exists p', STEPP pb ds pbOK p p') \/ hasChoiceP p.
Proof.
  intros. gen pb ds pbOK. induction p; intros.
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
  pose proof (progress pb ds pbOK e).
  destruct H as [| []];

  eauto.
  SCase "e value".
  left; repeat constructor.
  inversion H; auto.
  unfold closedP. simpl.
  inversion H. unfold closedX in *. assumption.

  SCase "e steps".
  right. left. dest H. exists (PEXP x'). auto.
Qed.
