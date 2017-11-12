
Require Import FiatFormal.Language.Step.
Require Import FiatFormal.Language.SubstExpExp.
Require Import FiatFormal.Language.SubstTypeExp.
Require Import FiatFormal.Language.SubstTypeType.
Require Import FiatFormal.Language.TyJudge.


(* The body of an alternative is well typed under an environment
   that includes the arguments of the constructor being matched. *)
Lemma getAlt_bodyIsWellTyped_fromAlts
  : forall ds ke te tPat tResult alts dc tsArgs x,
    Forall (fun a => TYPEA ds ke te a tPat tResult) alts
    -> In (AAlt dc tsArgs x) alts
    -> TYPE ds ke (te >< tsArgs) x tResult.
Proof.
 intros.
 nforall. spec H H0.
 invert_exp_type. auto.
Qed.


(* The body of an alternative of a case expression is well typed
   under an environment that includes the arguments of the constructor
   being matched. *)
Lemma getAlt_bodyIsWellTyped_fromMatch
  : forall ds ke te tResult tCon alts dc tsArgs x1 x2,
    TYPE ds ke te (XMatch x1 alts) tResult
    -> getDataDef dc ds   = Some (DefData dc tsArgs tCon)
    -> getAlt     dc alts = Some (AAlt    dc tsArgs x2)
    -> TYPE ds ke (te >< tsArgs) x2 tResult.
Proof.
 intros.
 inverts keep H.
 lets HA:  getAlt_in H1.
 lets HXT: getAlt_bodyIsWellTyped_fromAlts H5 HA.
 auto.
Qed.


(* If an alternative is well typed then the types of the ctor
   args embedded in it match those in the data type definition *)
Lemma getAlt_ctorArgTypesMatchDataDef
  : forall ds ke te tCon tResult alts dc x tsArgs tsArgs',
    Forall (fun alt => TYPEA ds ke te alt tCon tResult) alts
    -> getDataDef dc ds = Some (DefData dc tsArgs  tCon)
    -> getAlt dc alts   = Some (AAlt    dc tsArgs' x)
    -> tsArgs = tsArgs'.
Proof.
 intros. nforall.
 lets D: getAlt_in H1. spec H D.
 invert_exp_type.
 rewrite H0 in H5. inversion H5; auto.
Qed.


Lemma liftXX_closed :
  forall ds te x t n,
    TYPE ds nil te x t
    -> length te = n
    -> x = liftXX 1 n x.
Proof.
  intros. gen ds te t n.
  induction x using exp_mutind
    with (PA := fun a => forall ds te tBuilds tRes n,
                    TYPEA ds nil te a tBuilds tRes
                    -> length te = n
                    -> a = liftXA 1 n a);
    intros; try inverts H; nope; simpl.

  Case "XVar".
  lift_cases. exfalso. eapply get_above_false.
  rewrite <- H0 in l. eauto. eauto. reflexivity.

  Case "XApp".
  erewrite <- IHx1; eauto.
  erewrite <- IHx2; eauto.

  Case "XTup".
  invert_exp_type.
  f_equal.
  assert (x = liftXX 1 n x).
  assert (In x (l0 :> x)) by auto.
  pose proof (Forall2_exists_left _ _ _ _ H H6).
  dest y. spec H2 H0. spec H2 H1. auto.
  rewrite <- H.
  assert (l0 = map (liftXX 1 n) l0).
  nforall. assert (map (fun b => b) l0 = l0).
  rewrite <- map_id. auto. rewrite <- H0.
  rewrite map_map.
  apply map_ext_in; intros.
  spec H3 H4.
  apply in_cons with (a:=x) in H4.
  pose proof (Forall2_exists_left _ _ _ _ H4 H6).
  destruct H5.
  eapply H3; eauto.
  rewrite <- H0; auto.

  Case "XProj".
  assert (x = liftXX 1 n0 x).
  eapply IHx; eauto. rewrite <- H; auto.

  Case "XNFun".
  assert (x = liftXX 1 (n + length ts) x).
  eapply IHx; eauto. rewrite app_length.
  burn. burn.

  Case "XNApp".
  invert_exp_type.
  assert (x = liftXX 1 n x).
  eapply IHx; eauto. rewrite <- H; auto.
  invert_exp_type.
  assert (x = liftXX 1 n x).
  eapply IHx; eauto. rewrite <- H; auto.
  nforall.
  assert (In x0 (l0 :> x0)) by auto.
  pose proof (Forall2_exists_left _ _ _ _ H0 H9).
  dest y. assert (x0 = liftXX 1 n x0) by eauto.
  rewrite <- H5.
  assert (l0 = map (liftXX 1 n) l0).
  assert (map (fun b => b) l0 = l0).
  rewrite <- map_id. auto. rewrite <- H6.
  rewrite map_map.
  apply map_ext_in; intros.
  spec H3 H8.
  assert (In a (l0 :> x0)) by auto.
  pose proof (Forall2_exists_left _ _ _ _ H10 H9).
  destruct H11. eapply H3; eauto.
  rewrite <- H6; auto.

  Case "XFix".
  assert (x = liftXX 1 (S (S n)) x).
  eapply IHx. eauto. rewrite <- H0. auto.
  rewrite <- H; auto.

  Case "XCon".
  invert_exp_type.
  assert (x = liftXX 1 n x).
  assert (In x (l0 :> x)) by auto.
  pose proof (Forall2_exists_left _ _ _ _ H H12).
  dest y. eapply H2; eauto. rewrite <- H.
  repeat nforall.
  assert (l0 = map (liftXX 1 n) l0).
  assert (map (fun b => b) l0 = l0).
  rewrite <- map_id. auto. rewrite <- H0.
  rewrite map_map.
  apply map_ext_in; intros.
  spec H3 H4.
  assert (In a (l0 :> x)) by auto.
  pose proof (Forall2_exists_left _ _ _ _ H8 H12).
  destruct H9. eapply H3; eauto.
  rewrite <- H0; auto.

  Case "XMatch".
  invert_exp_type.
  assert (x = liftXX 1 n x).
  eapply IHx; eauto. rewrite <- H.
  repeat nforall.
  rename x0 into a.
  assert (a = liftXA 1 n a).
  assert (In a (l0 :> a)) by auto.
  spec H6 H0. eapply H2; eauto.
  rewrite <- H0.
  assert (l0 = map (liftXA 1 n) l0).
  assert (map (fun b => b) l0 = l0).
  rewrite <- map_id. auto. rewrite <- H4.
  rewrite map_map.
  apply map_ext_in; intros.
  spec H3 H8.
  assert (In a0 (l0 :> a)) by auto.
  spec H6 H9. eapply H3; eauto. rewrite <- H4; auto.

  Case "XChoice".
  invert_exp_type.
  assert (x = liftXX 1 n x).
  assert (In x (l0 :> x)) by auto.
  pose proof (Forall2_exists_left _ _ _ _ H H13).
  dest y. eapply H2; eauto. rewrite <- H.
  repeat nforall.
  assert (l0 = map (liftXX 1 n) l0).
  assert (map (fun b => b) l0 = l0).
  rewrite <- map_id. auto. rewrite <- H0.
  rewrite map_map.
  apply map_ext_in; intros.
  spec H3 H4.
  assert (In a (l0 :> x)) by auto.
  pose proof (Forall2_exists_left _ _ _ _ H5 H13).
  destruct H8. eapply H3; eauto.
  rewrite <- H0; auto.

  Case "AAlt".
  assert (x = liftXX 1 (n + length ts) x).
  eapply IHx; eauto. rewrite <- H0.
  rewrite app_length. burn. rewrite <- H; auto.
Qed.


(* When a well typed expression transitions to the next state *)
(*    then its type is preserved. *)
Theorem preservation
  : forall pb ds pbOK x x' t,
    TYPE ds nil nil x t
    -> STEP pb ds pbOK x x'
    -> TYPE ds nil nil x' t.
Proof.
 intros pb ds pbOK x x' t HT HS. gen t.
 induction HS; intros; invert_exp_type; eauto.

 (* Evaluation in an arbitrary context. *)
 Case "EsContext".
 destruct H; invert_exp_type; eauto.

 SCase "XCon".
 eapply TYCon; eauto.
 eapply exps_ctx_Forall2_swap; eauto.

 SCase "XChoice".
 eapply TYChoice; eauto.
 eapply exps_ctx_Forall2_swap; eauto.

 SCase "Tup".
 eapply TYTup; eauto.
 eapply exps_ctx_Forall2_swap; eauto.

 SCase "NApp".
 eapply TYNApp; eauto.
 eapply exps_ctx_Forall2_swap; eauto.

 Case "EsFixApp".
 eapply subst_value_value; eauto.
 eapply subst_value_value; eauto.
 assert (v2 = liftXX 1 0 v2).
 eapply liftXX_closed; eauto.
 rewrite H0.
 apply type_tyenv_weaken; auto.
 eapply (Forall2_get_get_same); eauto.

 Case "EsNFunApp".
 eapply subst_exp_exp_list; eauto.

 Case "EsCaseAlt".
 eapply subst_exp_exp_list; eauto.
 eapply getAlt_bodyIsWellTyped_fromMatch; eauto.
 lets D: getAlt_ctorArgTypesMatchDataDef H4 H7 H0. auto.
 subst. auto.

 Case "EsChoice".
 spec pbOK H0.
 apply pbOK in H4.
 assert (get 0 (vs :> v) = Some v) by auto.
 pose proof (Forall2_get_get_same _ _ _ _ _ _ H4 H1 H8).
 eauto.
Qed.


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
