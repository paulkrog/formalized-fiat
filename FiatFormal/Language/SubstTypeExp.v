
Require Import FiatFormal.Language.TyJudge.
Require Import FiatFormal.Language.SubstTypeType.


(* Substitution of types in expressions preserves typing.

   Note that substituting a type into an expression can instantiate
   type variables, so we also need to perform the substitution
   to the result type.
 *)
Theorem subst_type_exp_ix
  : forall ix ds ke te x1 t1 t2 k2,
    get ix ke = Some k2
    -> TYPE ds ke te x1 t1
    -> KIND (delete ix ke)  t2 k2
    -> TYPE ds (delete ix ke)     (substTE ix t2 te)
           (substTX ix t2 x1) (substTT ix t2 t1).
Proof.
  intros. gen ix ds ke te t1 t2 k2.
  induction x1 using exp_mutind
    with (PA := fun a => forall ix ds ke te tBuilds tRes t2 k2, (* dc tsArgs x, *)
                    get ix ke = Some k2
                    -> TYPEA ds ke te a (* (AAlt dc tsArgs x) *) tBuilds tRes
                    -> KIND (delete ix ke) t2 k2
                    -> TYPEA ds (delete ix ke) (substTE ix t2 te)
                            (substTA ix t2 a (* (AAlt dc tsArgs x) *)) (substTT ix t2 tBuilds) (substTT ix t2 tRes));
    intros; simpl; inverts H0; eauto.

  Case "XVar".
  apply TYVar.
  unfold substTE. eapply get_map. auto.
  eapply subst_type_type_ix; eauto.

  Case "XApp".
  eapply TYApp.
  eapply IHx1_1 in H6; eauto.
  eapply IHx1_2 in H8; eauto.

  Case "XTup".
  apply TYTup.
  apply (Forall2_map_left (TYPE ds (delete ix ke) (substTE ix t2 te))).
  apply (Forall2_map_right (fun (x : exp) (y : ty) => TYPE ds (delete ix ke) (substTE ix t2 te) (substTX ix t2 x) y)).
  apply (Forall2_impl_in (TYPE ds ke te)); eauto.
  nforall. intros.
  eapply H; eauto.

  Case "XProj".
  eapply TYProj; simpl; eauto.
  spec IHx1 H6. simpl in *; eauto.

  Case "XNFun".
  eapply TYNFun; eauto.
  apply Forall_map.
  repeat nforall; intros.
  eapply subst_type_type_ix; eauto.
  spec IHx1 H8.
  unfold substTE in *.
  rewrite <- map_app; eauto.

  Case "XNApp".
  apply TYNApp with (ts := map (substTT ix t2) ts).
  assert (substTT ix t2 (TNFun ts t1) = TNFun (map (substTT ix t2) ts) (substTT ix t2 t1)) by auto.
  rewrite <- H0.
  eapply IHx1; eauto.
  apply (Forall2_map_left (TYPE ds (delete ix ke) (substTE ix t2 te))).
  apply (Forall2_map_right (fun (x : exp) (y : ty) => TYPE ds (delete ix ke) (substTE ix t2 te) (substTX ix t2 x) y)).
  apply (Forall2_impl_in  (TYPE ds ke te)); eauto.
  nforall. intros.
  eapply H; eauto.

  Case "XFix".
  eapply TYFix. eapply subst_type_type_ix; eauto.
  unfold substTE in *.
  assert (substTT ix t3 (TFun t1 t2) = (TFun (substTT ix t3 t1) (substTT ix t3 t2))) by auto.
  rewrite <- H0.
  repeat rewrite <- map_cons.
  eapply IHx1; eauto.

  Case "XCon".
  eapply TYCon; eauto.
  apply (Forall2_map_left (TYPE ds (delete ix ke) (substTE ix t2 te))).
  apply (Forall2_impl_in  (TYPE ds ke te)); eauto.
  nforall; eauto.
  intros. spec H7 H3.
  assert (y = substTT ix t2 y).
  apply simpleSubstEq; auto.
  rewrite H8.
  nforall.
  eapply H; eauto.

  Case "XMatch".
  eapply TYMatch; eauto.
  assert (TCon tcPat = (substTT ix t2 (TCon tcPat))) by auto.
  rewrite H0.
  eapply IHx1; eauto.

  apply Forall_map.
  apply (Forall_impl_in (fun a => TYPEA ds ke te a (TCon tcPat) t1)); eauto.
  repeat nforall; intros.
  spec H H0. spec H H1. spec H H3. eauto.
  rewrite map_length; auto.

  (* norm. *) repeat nforall.
  intros. rename x into d.
  rewrite map_map. unfold Basics.compose.
  eapply map_exists_in.
  have (In d (map dcOfAlt aa)).
  assert (exists a, dcOfAlt a = d /\ In a aa).
  eapply map_in_exists. auto.
  shift a. rip.
  eapply dcOfAlt_substTA.

  Case "XChoice".
  eapply TYChoice; eauto.
  assert (t1 = substTT ix t2 t1).
  nforall. apply get_in in H10.
  spec H7 H10.
  apply simpleSubstEq; auto.
  rewrite <- H0; auto.
  eapply subst_type_type_ix; eauto.

  apply (Forall2_map_left (TYPE ds (delete ix ke) (substTE ix t2 te))).
  apply (Forall2_impl_in  (TYPE ds ke te)); eauto.
  nforall; eauto.
  intros. apply In_tl in H3. spec H7 H3.
  assert (y = substTT ix t2 y).
  apply simpleSubstEq; auto.
  rewrite H5.
  nforall.
  eapply H; eauto.

  Case "XAlt".
  assert (ts = map (substTT ix t2) ts).
  apply simpleSubstMapEq; auto.
  eapply TYAlt; eauto.
  rewrite <- H0; auto.
  rewrite <- H0; auto.

  apply Forall_map.

  rewrite Forall_forall; intros.
  repeat nforall.
  eapply subst_type_type_ix; eauto.

  unfold substTE in *.
  rewrite <- map_app.
  eapply IHx1; eauto.
Qed.


Theorem subst_type_value
  : forall ds ke te x1 t1 t2 k2,
    TYPE ds (ke :> k2) te x1 t1
    -> KIND ke  t2 k2
    -> TYPE ds ke (substTE 0 t2 te)
           (substTX 0 t2 x1) (substTT 0 t2 t1).
Proof.
 intros.
 assert (ke = delete 0 (ke :> k2)). auto. rewrite H1.
 eapply subst_type_exp_ix; simpl; eauto.
Qed.
