
Require Import FiatFormal.Language.SubstExpExp.
Require Import FiatFormal.Language.SubstTypeExp.
Require Import FiatFormal.Language.TyJudge.
Require Import FiatFormal.Language.SubstTypeType.

Lemma mapCtor {A : Type} :
  forall (C : A -> A) xs xs',
    (forall x x', C x = C x' -> x = x')
    -> map C xs = map C xs'
    -> xs = xs'.
Proof.
  induction xs;
    destruct xs'; auto; try nope;
      intros.
  inversion H0.
  f_equal. spec H H2; auto.
  apply IHxs; auto.
Qed.


Theorem subst_exp_prog_ix :
  forall ds ke te t1 ix p t2 s,
    get ix te = Some t1
    -> TYPE ds ke (delete ix te) s t1
    -> TYPEPROG ds ke te p t2
    -> TYPEPROG ds ke (delete ix te) (substXP ix s p) t2.
Proof.
  intros. gen s ix t1.
  induction H1; intros.
  - Case "PLet".
    invert H; intros; subst; simpl.
    apply TYLet.
    + (* prove A generalized *)
      apply TYADT; try assumption.
      forall2_pull_in_maps.
      apply (Forall2_impl_in (fun m t => TYPEMETHOD tr ds ke te m (substTT 0 tr t))); eauto; intros.
      * destruct x; simpl. inverts H5; subst. eapply TYMETHOD; eauto.
        eapply subst_value_value_ix; first [ eassumption; assumption ].
      * forall2_push_out_map_right; auto.
    + (* prove B generalized *)
      unfold liftTE in *.
      rewrite map_delete.
      rewrite delete_app.
      apply mapCtor in H9; subst.
      * assert (length ms = length (map (substTT 0 tr) ts)).
        eapply Forall2_length; eauto.
        rewrite map_length in H. rewrite H.
        eapply IHTYPEPROG; simpl.
        -- apply get_app_left_some.
           apply get_map.
           eassumption.
        -- rewrite <- delete_app.
           apply type_tyenv_weaken_append.
           rewrite <- map_delete.
           pose proof type_kienv_weaken.
           unfold liftTE in H3.
           apply H4. assumption.
      * (* injective cTor *)
        intros; inversion H; auto.
    + assumption.
  - Case "PExp".
    apply TYExp.
    eapply subst_value_value_ix; first [ eassumption |  assumption].
Qed.


Theorem subst_exp_prog
  : forall ds ke te t1 p t2 s,
    TYPEPROG ds ke (te :> t1) p t2
    -> TYPE ds ke te s t1
    -> TYPEPROG ds ke te (substXP 0 s p) t2.
Proof.
  intros.
  assert (te = delete 0 (te :> t1)). auto.
  rewrite H1.
  eapply subst_exp_prog_ix; simpl; eauto.
Qed.

(* new *)
(* Substitution of several expressions at once. *)
Theorem subst_exp_prog_list
  : forall ds ks te ts p1 t1 xs,
    Forall2 (TYPE ds ks te) xs ts
    -> TYPEPROG ds ks (te >< ts) p1 t1
    -> TYPEPROG ds ks te (substXXsP 0 xs p1) t1.
Proof.
  intros ds ks te ts p1 t1 xs HF HT.
  gen ts ks p1.
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
        eapply subst_exp_prog.
        eauto.
        rrwrite (length xs = length ts).
        eapply type_tyenv_weaken_append. auto.
Qed.


Theorem subst_type_prog_ix
  : forall ds ix ke kx S te p t,
    get ix ke = Some kx
    -> KIND (delete ix ke) S kx
    -> TYPEPROG ds ke te p t
    -> TYPEPROG ds (delete ix ke) (substTE ix S te) (substTP ix S p) (substTT ix S t).
Proof.
  intros. gen S ix kx.
  induction H1; intros.
  - Case "PLet".
    simpl. invert H; intros; subst.
    assert
      (Hcomp : forall ix S tr t, substTT (0 + ix) S (substTT 0 tr t)
                            = (substTT 0 (substTT (0 + ix) S tr)
                                       (substTT (1 + 0 + ix) (liftTT 0 S) t)));
      intros.
    + apply substTT_substTT with (n:=0) (m:=ix0).
    + simpl in Hcomp.
      rewrite map_map.
      simpl. rewrite <- map_map with (f:=(substTT (Datatypes.S ix) (liftTT 0 S))).
      apply TYLet.
      * SCase "ADT".
        apply TYADT.
        -- eapply subst_type_type_ix; eassumption.
        -- forall2_pull_in_maps.
           apply (Forall2_impl_in
                    (fun m t => TYPEMETHOD tr ds ke te m (substTT 0 tr t)));
             eauto; intros.
          ++ destruct x; simpl. inverts H5; subst.
             simpl.
             rewrite <- Hcomp.
             rewrite <- H16. simpl.
             rewrite map_app.
             rewrite dup_map.
             eapply TYMETHOD; eauto.
             assert (Hsubst: (TNFun
                                (dup (substTT ix S tr) arity >< map (substTT ix S) dom)
                                    (TNProd (nil :> substTT ix S tr :> substTT ix S tRes)))
                             = (substTT ix S
                                        (TNFun ((dup tr arity) >< dom)
                                               (TNProd (nil :> tr :> tRes)))));
               simpl.
             rewrite <- dup_map.
             rewrite <- map_app.
             auto.
             rewrite Hsubst.
             eapply subst_type_exp_ix.
             eassumption.
             assumption.
             assumption.
          ++ forall2_push_out_map_right; auto.
      * SCase "PROG".
        rewrite liftTE_substTE with (n:=0) (n':=ix).
        unfold substTE in *. rewrite <- map_app.
        apply mapCtor in H9; subst.
        rewrite liftTT_substTT with (n:=0) (n':=ix).
        simpl.
        rewrite delete_rewind in *.
        eapply IHTYPEPROG.
        simpl.
        eassumption.
        simpl.
        eapply liftTT_weaken.
        assumption.
        intros. inversion H; auto.
      * eapply subst_type_type_ix; eauto.
  - Case "PExp".
    apply TYExp.
    eapply subst_type_exp_ix; eassumption.
Qed.


Theorem subst_type_prog
  : forall ds ke te X S p t,
    TYPEPROG ds (ke :> X) te p t
    -> KIND ke S KStar
    -> TYPEPROG ds ke (substTE 0 S te) (substTP 0 S p) (substTT 0 S t).
Proof.
  intros.
  assert (ke = delete 0 (ke :> X)). auto.
  rewrite H1.
  eapply subst_type_prog_ix; simpl; eauto.
  destruct X; assumption.
Qed.


Theorem subst_ADT_prog :
  forall ds X r kr t1 t2 x p,
    TYPEPROG ds (nil :> X) (nil :> t1) p (liftTT 0 t2)
    -> KIND nil r kr
    -> TYPE ds nil nil x (substTT 0 r t1)
    -> TYPEPROG ds nil nil (substXP 0 x (substTP 0 r p)) t2.
Proof.
  intros ds X r kr t1 t2 x p HP HK HT.
  pose proof (subst_type_prog) as STP.
  specialize (STP _ _ _ _ r _ _ HP).
  pose proof
       (subst_exp_prog ds nil nil (substTT 0 r t1) (substTP 0 r p) (t2))
    as ESL.
  simpl in *.
  destruct kr.
  specialize (STP HK). rewrite substTT_liftTT in STP.
  specialize (ESL x STP).
  specialize (ESL HT).
  assumption.
Qed.


Theorem subst_ADT_prog' :
  forall ds X r kr ts t2 xs p,
    TYPEPROG ds (nil :> X) (nil >< ts) p (liftTT 0 t2)
    -> KIND nil r kr
    -> Forall2 (TYPE ds nil nil) xs (map (substTT 0 r) ts)
    -> TYPEPROG ds nil nil (substXXsP 0 xs (substTP 0 r p)) t2.
Proof.
  intros ds X r kr ts t2 xs p HP HK HT.
  pose proof (subst_type_prog) as STP.
  specialize (STP _ _ _ _ r _ _ HP).
  pose proof
       (subst_exp_prog_list ds nil nil (map (substTT 0 r) ts) (substTP 0 r p) t2)
    as ESL.
  simpl in *.
  destruct kr.
  specialize (STP HK);
    unfold substTE in STP. rewrite substTT_liftTT in STP.
  rewrite map_app in STP; simpl in *.
  specialize (ESL xs HT).
  specialize (ESL STP).
  assumption.
Qed.