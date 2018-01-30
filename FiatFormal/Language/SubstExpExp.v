
Require Import FiatFormal.Language.SubstTypeType.
Require Import FiatFormal.Language.SubstTypeExp.
Require Import FiatFormal.Language.TyJudge.


(* Substitution of Values in Values preserves Typing *)
Theorem subst_value_value_ix
  : forall ds ix ke te x1 t1 x2 t2,
    get ix te = Some t2
    -> TYPE ds ke te           x1 t1
    -> TYPE ds ke (delete ix te) x2 t2
    -> TYPE ds ke (delete ix te) (substXX ix x2 x1) t1.
Proof.
  intros. gen ds ix ke te t1 x2 t2.
  induction x1 using exp_mutind
    with (PA := fun a => forall ds ix ke te tsBuilds tRes x2 t2,
                    get ix te = Some t2
                    -> TYPEA ds ke te a tsBuilds tRes
                    -> TYPE  ds ke (delete ix te) x2 t2
                    -> TYPEA ds ke (delete ix te) (substXA ix x2 a) tsBuilds tRes);
    intros; inverts H0; simpl; eauto.

  Case "XVar".
  fbreak_nat_compare.
  SCase "n = ix".
  rewrite H in H3. inverts H3. auto.

  SCase "n < ix".
  apply TYVar.
  rewrite <- H3. apply get_delete_above. auto. auto.

  SCase "n > ix".
  apply TYVar. auto.
  rewrite <- H3.
  destruct n.
  burn.
  simpl. nnat. apply get_delete_below. omega.
  auto.

  Case "XTup".
  apply TYTup; forall2_pull_in_maps.
  apply (Forall2_impl_in (TYPE ds ke te)); eauto.
  nforall. intros.
  eapply H; eauto.

  Case "XNFun".
  apply TYNFun; auto.
  rewrite delete_app.
  eapply IHx1; eauto.
  rewrite <- delete_app.
  eapply type_tyenv_weaken_append; auto.

  Case "XNApp".
  eapply TYNApp.
  spec IHx1 H7.
  eapply IHx1; eauto.
  forall2_pull_in_maps.
  apply (Forall2_impl_in (TYPE ds ke te)); eauto.
  nforall. intros.
  eapply H; eauto.

  Case "XFix".
  eapply TYFix; eauto.
  repeat rewrite delete_rewind.
  eapply IHx1; eauto.
  simpl. pose proof (liftXX_plus 1 1).
  rewrite <- H0.
  repeat apply type_tyenv_weaken; auto.

  Case "XCon".
  eapply TYCon; eauto.
  forall2_pull_in_maps.
  apply (Forall2_impl_in  (TYPE ds ke te)); eauto.
  repeat nforall; eauto.

  Case "XMatch".
  eapply TYMatch; eauto.
  apply Forall_map.
  apply (Forall_impl_in (fun x : alt => TYPEA ds ke (delete ix te) (substXA ix x2 x) (TCon tcPat) t1)).
  repeat nforall; intros.
  spec H H0. eauto.

  repeat nforall; intros; eauto.
  rewrite map_length; auto.

  repeat nforall.
  intros. rename x into d.
  rewrite map_map. unfold Basics.compose.
  eapply map_exists_in.
  have (In d (map dcOfAlt aa)).
  assert (exists a, dcOfAlt a = d /\ In a aa).
  eapply map_in_exists. auto.
  shift a. rip.
  eapply dcOfAlt_substXA.

  Case "XChoice".
  eapply TYChoice; eauto.
  forall2_pull_in_maps.
  apply (Forall2_impl_in  (TYPE ds ke te)); eauto.
  repeat nforall; eauto.

  Case "XAlt".
  assert (ts = map (substTT ix t2) ts).
  apply simpleSubstMapEq; auto.
  eapply TYAlt; eauto.
  repeat nforall.
  rewrite delete_app.
  eapply IHx1; eauto.
  rewrite <- delete_app.
  eapply type_tyenv_weaken_append; auto.
Qed.


Theorem subst_value_value
  : forall ds ke te x1 t1 x2 t2,
    TYPE ds ke (te :> t2) x1 t1
    -> TYPE ds ke te x2 t2
    -> TYPE ds ke te (substXX 0 x2 x1) t1.
Proof.
  intros.
  assert (te = delete 0 (te :> t2)). auto.
  rewrite H1. eapply subst_value_value_ix; eauto. eauto.
Qed.


(* Substitution of several expressions at once. *)
Theorem subst_exp_exp_list
  : forall ds ks te x1 xs t1 ts,
    Forall2 (TYPE ds ks te) xs ts
    -> TYPE ds ks (te >< ts) x1 t1
    -> TYPE ds ks te (substXXs 0 xs x1) t1.
Proof.
  intros ds ks te x1 xs t1 ts HF HT.
  gen ts ks x1.
  induction xs; intros; invert_exp_type.

  - Case "base case".
    destruct ts.
    + simpl. auto.
    + nope.

  - Case "step case".
    simpl.
    destruct ts.
    + nope.
    + inverts HF.
      eapply IHxs.
      * eauto.
      * simpl in HT.
        eapply subst_value_value.
        eauto.
        rrwrite (length xs = length ts).
        eapply type_tyenv_weaken_append. auto.
Qed.
