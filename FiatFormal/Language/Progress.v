
Require Import FiatFormal.Language.Step.
Require Import FiatFormal.Language.SubstExpExp.
Require Import FiatFormal.Language.SubstTypeExp.
Require Import FiatFormal.Language.SubstTypeType.
Require Import FiatFormal.Language.TyJudge.


Lemma In_Context :
  forall C Val x,
    exps_ctx Val C
    -> @In exp x (C x).
Proof.
  intros.
  induction H; auto.
Qed.


Lemma canonicalFormTFun :
  forall ds ke te t1 t2 x,
    TYPE ds ke te x (TFun t1 t2)
    -> value x
    -> exists x', x = (XFix t1 t2 x').
Proof.
  intros. gen ds ke te t1 t2 H0.
  induction x using exp_mutind
    with (PA := fun a => a = a); rip; try inverts H0; try nope; try inverts H.
  exists x; reflexivity.
Qed.


Lemma canonicalFormTNFun :
  forall ds ke te tsArgs tRes x,
    TYPE ds ke te x (TNFun tsArgs tRes)
    -> value x
    -> exists x', x = (XNFun tsArgs x').
Proof.
  intros. gen ds ke te tsArgs tRes H0.
  induction x using exp_mutind
    with (PA := fun a => a = a); rip; try inverts H0; try nope; try inverts H.
  exists x; reflexivity.
Qed.


Lemma canonicalFormTNProd :
  forall ds ke te ts x,
    TYPE ds ke te x (TNProd ts)
    -> value x
    -> exists xs, x = (XTup xs).
Proof.
  intros. gen ds ke te ts H0.
  induction x using exp_mutind
    with (PA := fun a => a = a); rip; try inverts H0; try nope; try inverts H.
  exists (@nil exp); reflexivity.
  exists (l0 :> x); reflexivity.
Qed.


Lemma wellTypedProjHasX :
  forall ds ke te ts t xs n,
    TYPE ds ke te (XTup xs) (TNProd ts)
    -> get n ts = Some t
    -> exists x, get n xs = Some x.
Proof.
  intros.
  inverts H.
  pose proof @get_length_less_exists exp.
  pose proof(Forall2_length _ _ _ H5).
  apply get_length_less in H0. rewrite <- H1 in H0.
  spec H H0. dest x. eauto.
Qed.


(* A well typed expression is either a value, can take a step,
   or contains a choice. *)
Theorem progress
  : forall pb ds pbOK x,
    (exists t, TYPE ds nil nil x t)
    -> value x \/ (exists x', STEP pb ds pbOK x x') \/ hasChoiceX x.
Proof.
 intros. gen pb ds pbOK.
 induction x using exp_mutind with
     (PA := fun a => a = a);
   rip; first [destruct H as [tx] | destruct H0 as [tx]];
     try invert_exp_type; nope.

 Case "XApp".
 right.
 edestruct IHx1; eauto.
 SCase "value x1".
 edestruct IHx2; eauto.
 SSCase "value x2".
 pose proof (canonicalFormTFun).
 spec H1 H4. spec H1 H. destruct H1 as [x' LAM]; subst.
 SSSCase "fix".
 left; exists (substXX 0 (XFix t11 tx x') (substXX 0 x2 x')). apply EsFixApp. inverts H0; auto.
 destruct H0 as [STx2 | HCx2].
 SSCase "x2 steps".
 destruct STx2 as [x2'].
 left; exists (XApp x1 x2'). eauto.
 SSCase "x2 hasChoice".
 right; auto.
 destruct H as [STx1 | HCx1].
 SCase "x1 steps".
 destruct STx1 as [x1'].
 left; exists (XApp x1' x2).
 eapply (EsContext pb ds pbOK (fun xx => XApp xx x2)); eauto.
 SCase "x1 hasChoice".
 right; auto.

 Case "XTup".
 assert (Forall (fun x => wnfX x \/ (exists x', STEP pb ds pbOK x x') \/ hasChoiceX x) xs) as HWS.
 repeat nforall. rip.
 have (exists t, TYPE ds nil nil x t). dest t.
 have (value x \/ (exists x', STEP pb ds pbOK x x') \/ hasChoiceX x).
 inverts H2; rip.
 inverts H3; rip.
 (* All ctor args are wnf, or there is a context where one can step *)
 lets D: (@exps_ctx_run exp exp) HWS.
 inverts D.
 (* All ctor args are wnf *)
 left. eauto 6.
 (* There is a context where one ctor arg can step *)
 right.
 dest C. dest x'.
 rip. destruct H3 as [STx' | HCx'].
 left.
 lets D: step_context_XTup_exists H1 STx'.
 destruct D as [x'']. eauto.
 SCase "hasChoice x".
 (* nope. *)
 right; apply HcTup.
 apply Exists_exists. exists x'. rip.
 eapply In_Context; eauto.

 Case "XProj".
 right. assert (exists t, TYPE ds nil nil x t) by eauto.
 destruct (IHx pb ds H pbOK); eauto.
 SCase "value x".
 pose proof (canonicalFormTNProd).
 spec H1 H4. spec H1 H0. dest xs; subst.
 left.
 pose proof (wellTypedProjHasX _ _ _ _ _ _ _ H4 H6).
 dest x. exists x. apply EsTupProj; auto.
 inverts H0. inverts H2; auto.
 destruct H0 as [STx | HCx].
 SCase "x steps".
 left. dest x'. exists (XProj n x').
 eapply (EsContext pb ds pbOK (fun xx => XProj n xx)); eauto.
 SCase "x hasChoice".
 (* nope. *)
 right; auto.

 Case "XNFun".
 left; eauto.

 Case "XNApp".
 right. assert (exists t, TYPE ds nil nil x t) by eauto.
 destruct (IHx pb ds H0 pbOK); eauto.
 pose proof (canonicalFormTNFun).
 spec H2 H5. spec H2 H1. dest x'; subst.
 assert (Forall (fun x => wnfX x \/ (exists x', STEP pb ds pbOK x x') \/ hasChoiceX x) xs) as HWS.

 repeat nforall. rip.
 have (exists t, TYPE ds nil nil x t). dest t.
 have (value x \/ (exists x', STEP pb ds pbOK x x') \/ hasChoiceX x).
 inverts H4; rip. inverts H6. auto.
 (* All args are wnf, or there is a context where one can step *)
 lets D: (@exps_ctx_run exp exp) HWS.
 inverts D.
 (* All ctor args are wnf *)
 left. eauto 6.
 (* There is a context where one ctor arg can step *)
 dest C. rename x' into x''. dest x'.
 rip. destruct H6 as [STx' | HCx'].
 left.
 destruct STx'.
 exists (XNApp (XNFun ts x'') (C x)).
 eapply (EsContext pb ds pbOK (fun xx => XNApp (XNFun ts x'') (C xx))).
 apply XcNApp2; eauto. auto.
 SCase "x' hasChoice".
 right; apply HcNApp2.
 apply Exists_exists. exists x'. rip.
 eapply In_Context; eauto.
 destruct H1 as [STx | HCx].
 left.
 dest x'.
 exists (XNApp x' xs); eauto.
 eapply (EsContext pb ds pbOK (fun xx => XNApp xx xs)); eauto.
 SCase "x hasChoice".
 right; eauto.

 Case "XFix".
 left; eauto.

 Case "XCon".
 (* All ctor args are either wnf or can step *)
 assert (Forall (fun x => wnfX x \/ (exists x', STEP pb ds pbOK x x') \/ hasChoiceX x) xs) as HWS.
 repeat nforall. rip.
 have (exists t, TYPE ds nil nil x t). dest t.
 have (value x \/ (exists x', STEP pb ds pbOK x x') \/ hasChoiceX x).
 inverts H2; rip.
 inverts H6; rip.
 (* All ctor args are wnf, or there is a context where one can step *)
 lets D: (@exps_ctx_run exp exp) HWS.
 inverts D.
 (* All ctor args are wnf *)
 left. eauto 6.
 (* There is a context where one ctor arg can step *)
 right.
 dest C. dest x'.
 rip. destruct H6 as [STx' | HCx'].
 left.
 lets D: step_context_XCon_exists H1 STx'.
 destruct D as [x'']. eauto.
 SCase "hasChoice x".
 right; apply HcCon.
 apply Exists_exists. exists x'. rip.
 eapply In_Context; eauto.

 Case "XMatch".
 right. assert (exists t, TYPE ds nil nil x t) by eauto.
 destruct (IHx pb ds H0 pbOK); eauto.
 SCase "x value".
 destruct x; nope.
 SSCase "XCon".
 inverts_type.
 rewrite H8 in H11. inversion H11; subst.
 assert (exists ts x, getAlt d aa = Some (AAlt d ts x)).
 apply getAlt_exists.
 repeat nforall. spec H10 H15. auto.
 dest ts. dest x.
 left. exists (substXXs 0 l x). eapply EsMatchAlt.
 inverts H1. inverts H3; auto. eauto.
 destruct H1 as [STx | HCx].
 SCase "x steps".
 left; destruct STx as [x'].
 exists (XMatch x' aa).
 lets D: EsContext XcMatch; eauto.
 SCase "x hasChoice".
 right; auto.
Qed.
