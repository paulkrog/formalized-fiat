
Require Export FiatFormal.Language.TyJudge.
Require Export FiatFormal.Language.Exp.
Require Export FiatFormal.Language.SubstExpExp.


(* The body of an alternative is well typed under an environment
   that includes the arguments of the constructor being matched. *)
Lemma getAlt_bodyIsWellTyped_fromAlts
  : forall alg_ds adt_ds te tPat tResult alts dc tsArgs x,
    Forall (fun a => TYPEA alg_ds adt_ds te a tPat tResult) alts
 -> In (AAlt dc tsArgs x) alts
 -> TYPE alg_ds adt_ds (te >< tsArgs) x tResult.
Proof.
(*  intros.  *)
(*  norm. spec H H0.  *)
(*  inverts_type. auto. *)
(* Qed. *)
Admitted.

(* The body of an alternative of a case expression is well typed
   under an environment that includes the arguments of the constructor
   being matched. *)
Lemma getAlt_bodyIsWellTyped_fromCase
  : forall alg_ds adt_ds te tResult tCon alts dc tsArgs x1 x2,
    TYPE alg_ds adt_ds te (XMatch x1 alts) tResult
    -> getDataDef dc alg_ds = Some (DefData dc tsArgs tCon)
    -> getAlt     dc alts   = Some (AAlt    dc tsArgs x2)
    -> TYPE alg_ds adt_ds (te >< tsArgs) x2 tResult.
Proof.
(*  intros. *)
(*  inverts keep H. *)
(*  lets HA:  getAlt_in H1. *)
(*  lets HXT: getAlt_bodyIsWellTyped_fromAlts H5 HA. *)
(*  auto. *)
(* Qed. *)
Admitted.


(* If an alternative is well typed then the types of the ctor
   args embedded in it match those in the data type definition *)
Lemma getAlt_ctorArgTypesMatchDataDef
  : forall alg_ds adt_ds te tCon tResult alts dc x tsArgs tsArgs',
    Forall (fun alt => TYPEA alg_ds adt_ds te alt tCon tResult) alts
    -> getDataDef dc alg_ds = Some (DefData dc tsArgs  tCon)
    -> getAlt dc alts       = Some (AAlt    dc tsArgs' x)
    -> tsArgs = tsArgs'.
Proof.
(*  intros. norm. *)
(*  lets D: getAlt_in H1. spec H D. *)
(*  inverts_type. rip. *)
(* Qed. *)
Admitted.

Lemma liftX_closed_pmk
  : forall x n te,
    wfX te x -> (liftX n (length te) x) = x.
Proof.
  intros x n.
  gen n.
  induction x using exp_mutind with
     (PA := fun a => forall n te, wfA te a -> (liftA n (length te) a) = a)
     (PF := fun f => f = f); intros; rip; burn; subst.
  inverts_wfX. dest t.
  simpl.
  fbreak_le_gt_dec; auto.
  pose proof (get_above_false _ _ _ _ l H); nope.
  inverts_wfX.
  spec IHx H2. simpl in *; subst.
  erewrite IHx; burn.
  inverts_wfX; simpl.
  spec IHx1 H3; spec IHx2 H4; espread; burn.
  inverts_wfX; repeat nforall.
  simpl.

  assert (forall x, In x xs -> liftX n (length te) x = x).
  intros. apply H. assumption. spec H3 H0. assumption.
  pose proof (map_ext_in _ _ xs H0).
  rewrite H1.
  rewrite map_id; burn.

  simpl.
  inverts_wfX.
  repeat nforall.

  assert (forall a, In a aa -> liftA n (length te) a = a).
  intros. apply H. assumption. spec H5 H0. assumption.
  pose proof (map_ext_in _ _ aa H0).
  rewrite H1.
  rewrite map_id.
  spec IHx H4. espread; burn.

  inverts_wfX.
  simpl.
  inverts_wfX.
  assert (liftX n (length (te >< tsArgs)) x = x).
  eapply IHx.
  assumption.
  rewrite H6.
  rewrite plus_comm. rewrite <- app_length.
  rewrite H; burn.

  inverts_wfX.
  simpl. repeat nforall.
  assert (forall x, In x xs -> liftX n0 (length te) x = x).
  intros. apply H. assumption. spec H9 H0. assumption.
  pose proof (map_ext_in _ _ xs H0).
  rewrite H1.
  rewrite map_id; burn.
Qed.