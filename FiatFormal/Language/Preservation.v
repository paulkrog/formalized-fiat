
Require Import FiatFormal.Language.Step.
Require Import FiatFormal.Language.TyJudge.
Require Import FiatFormal.Language.SubstExpExp.


(* When a well typed expression transitions to the next state
   then its type is preserved. *)
Theorem preservation
  : forall alg_ds adt_ds x x' t,
    TYPE alg_ds adt_ds nil x  t
 -> STEP adt_ds x x'
 -> TYPE alg_ds adt_ds nil x' t.
Proof.
 intros alg_ds adt_ds x x' t HT HS. gen t.
 induction HS; intros; inverts_type; eauto.

 (* Evaluation in an arbitrary context. *)
 Case "EsContext".
  destruct H; inverts_type; eauto.

  SCase "XCon".
   eapply TYCon; eauto.
   eapply exps_ctx_Forall2_swap; eauto.
  SCase "EsOpCall".
  admit.

 (* Case "EsLamApp". *)
 (*  eapply subst_exp_exp; eauto. *)

  Case "XLet".
  inversion H9; subst.

  Case "XFix".
  repeat (eapply subst_exp_exp); eauto.
  pose proof (type_tyenv_weaken1).
  pose proof (H0 alg_ds adt_ds nil v1 t0 (TFun t0 t) H7).
  pose proof (type_wfX _ _ _ _ _ H7).
  pose proof (liftX_closed_pmk v1 1 nil H2); simpl in *. rewrite <- H3.
  assumption.

 Case "EsMatchAlt".
  eapply subst_exp_exp_list; eauto.
  eapply getAlt_bodyIsWellTyped_fromCase; eauto.
  assert (tsArgs = tsArgs0).
   lets D: getAlt_ctorArgTypesMatchDataDef H4 H7 H0. auto.
   subst. auto.

 Case "XCallBody".
 repeat nforall.
 eapply subst_exp_exp_list; eauto.
 assert (XB: x = b); burn; subst.

 admit.

(* Qed. *)
Admitted.
(* ORIG *)
(*  intros ds x x' t HT HS. gen t. *)
(*  induction HS; intros; inverts_type; eauto. *)

(*  (* Evaluation in an arbitrary context. *) *)
(*  Case "EsContext". *)
(*   destruct H; inverts_type; eauto.  *)

(*   SCase "XCon". *)
(*    eapply TYCon; eauto. *)
(*    eapply exps_ctx_Forall2_swap; eauto. *)

(*  Case "EsLamApp". *)
(*   eapply subst_exp_exp; eauto. *)

(*  Case "EsCaseAlt". *)
(*   eapply subst_exp_exp_list; eauto. *)
(*   eapply getAlt_bodyIsWellTyped_fromCase; eauto. *)
(*   assert (tsArgs = tsArgs0). *)
(*    lets D: getAlt_ctorArgTypesMatchDataDef H4 H7 H0. auto. *)
(*    subst. auto. *)
(* Qed. *)


(* When we multi-step evaluate some expression,
   then the result has the same type as the original. *)
Lemma preservation_steps
  : forall alg_ds adt_ds x1 t1 x2,
    TYPE alg_ds adt_ds nil x1 t1
    -> STEPS adt_ds       x1 x2
    -> TYPE alg_ds adt_ds nil x2 t1.
Proof.
(*  intros ds x1 t1 x2 HT HS. *)
(*  induction HS; eauto using preservation. *)
(* Qed. *)
Admitted.

(* When we multi-step evaluate some expression,
   then the result has the same type as the original.
   Using the left-linearised form for the evaluation.
 *)
Lemma preservation_stepsl
  : forall alg_ds adt_ds x1 t1 x2,
    TYPE alg_ds adt_ds nil x1 t1
    -> STEPSL adt_ds x1 x2
    -> TYPE alg_ds adt_ds nil x2 t1.
Proof.
(*  intros ds x1 t1 x2 HT HSL. *)
(*  induction HSL; eauto using preservation. *)
(* Qed. *)
Admitted.
