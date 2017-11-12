
Require Import FiatFormal.Language.SubstExpExp.
Require Import FiatFormal.Language.SubstTypeExp.
Require Import FiatFormal.Language.TyJudge.
Require Import FiatFormal.Language.SubstTypeType.


Theorem subst_exp_prog_ix :
  forall ds ke te t1 ix p t2 s,
    get ix te = Some t1
    -> TYPE ds ke (delete ix te) s t1
    -> TYPEPROG ds ke te p t2
    -> TYPEPROG ds ke (delete ix te) (substXP ix s p) t2.
Proof.
  intros. gen s ix t1.
  induction H1; intros.
  Case "PLet".
  invert H; intros; subst; simpl.
  apply TYLet.
  (* prove A generalized *)
  apply TYADT; try assumption.
  eapply subst_value_value_ix; first [ eassumption; assumption ].
  (* prove B generalized *)
  unfold liftTE in *.
  rewrite map_delete.
  rewrite delete_rewind.
  eapply IHTYPEPROG; simpl.
  apply get_map.
  eassumption.
  apply type_tyenv_weaken.
  rewrite <- map_delete.
  pose proof type_kienv_weaken.
  unfold liftTE in H.
  apply H. assumption.
  Case "PExp".
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

Theorem subst_type_prog_ix
  : forall ds ix ke kx S te p t,
    get ix ke = Some kx
    -> KIND (delete ix ke) S kx
    -> TYPEPROG ds ke te p t
    -> TYPEPROG ds (delete ix ke) (substTE ix S te) (substTP ix S p) (substTT ix S t).
Proof.
  intros. gen S ix kx.
  induction H1; intros.
  Case "PLet".
  simpl. invert H; intros; subst.
  assert
    (Hcomp : substTT (0 + ix) S (substTT 0 tr t2)
             = (substTT 0 (substTT (0 + ix) S tr)
                        (substTT (1 + 0 + ix) (liftTT 0 S) t2))).
  apply substTT_substTT with (n:=0) (m:=ix).
  simpl in Hcomp.
  rewrite Hcomp.
  apply TYLet.
  SCase "ADT".
  apply TYADT.
  eapply subst_type_type_ix.
  eassumption.
  assumption.
  assumption.
  assert (Hcomp' : substTT (0 + ix) S (substTT 0 tr t)
                   = (substTT 0 (substTT (0 + ix) S tr)
                              (substTT (1 + 0 + ix) (liftTT 0 S) t))).
  apply substTT_substTT with (n:=0) (m:=ix).
  simpl in Hcomp'.
  rewrite <- Hcomp'.
  eapply subst_type_exp_ix.
  eassumption.
  assumption.
  assumption.
  SCase "PROG".
  rewrite delete_rewind in *.
  rewrite liftTE_substTE with (n:=0) (n':=ix).
  eapply IHTYPEPROG.
  simpl.
  eassumption.
  simpl.
  eapply liftTT_weaken.
  assumption.
  Case "PExp".
  apply TYExp.
  eapply subst_type_exp_ix.
  eassumption.
  assumption.
  assumption.
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

(* Main lemma supporting preservation *)
Theorem subst_ADT_prog :
  forall ds X r kr t1 t2 x p,
    TYPEPROG ds (nil :> X) (nil :> t1) p t2
    -> KIND nil r kr
    -> TYPE ds nil nil x (substTT 0 r t1)
    -> TYPEPROG ds nil nil (substXP 0 x (substTP 0 r p)) (substTT 0 r t2).
Proof.
  intros ds X r kr t1 t2 x p HP HK HT.
  pose proof (subst_type_prog) as STP.
  specialize (STP _ _ _ _ r _ _ HP).
  pose proof
       (subst_exp_prog ds nil nil (substTT 0 r t1) (substTP 0 r p) (substTT 0 r t2))
    as ESL.
  simpl in *.
  destruct kr.
  specialize (STP HK).
  specialize (ESL x STP).
  specialize (ESL HT).
  assumption.
Qed.
