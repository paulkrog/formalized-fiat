
Require Import FiatFormal.Language.Step.
Require Import FiatFormal.Language.SubstExpExp.
Require Import FiatFormal.Language.SubstTypeExp.
Require Import FiatFormal.Language.SubstTypeType.
Require Import FiatFormal.Language.TyJudge.

Lemma canonicalFormTFun :
  forall ds ke te t1 t2 x,
    TYPE ds ke te x (TFun t1 t2)
    -> value x
    -> exists x', (x = (XLam t1 x') \/ x = (XFix t1 t2 x')).
Proof.
  intros. gen ds ke te t1 t2 H0.
  induction x using exp_mutind
    with (PA := fun a => a = a); rip; try inverts H0; try nope; try inverts H.
  exists x; left; reflexivity.
  exists x; right; reflexivity.
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
  pose proof(Forall2_length _ _ _ H6).
  apply get_length_less in H0. rewrite <- H1 in H0.
  spec H H0. dest x. eauto.
Qed.


(* A well typed expression is either a value, can take a step,
   or contains a choice. *)
Theorem progress
  : forall ds x,
    (exists t, TYPE ds nil nil x t)
    -> value x \/ (exists x', STEP x x') \/ hasChoiceX x.
Proof.
(*  intros. gen ds. *)
(*  induction x using exp_mutind *)
(*    with (PA := fun a => a = a); *)
(*    rip; first [destruct H as [tx] | destruct H0 as [tx]]. *)

(*  Case "XVar". *)
(*   inverts H. false. *)

(*  (* Case "XLAM". *) *)
(*  (*  left. apply type_wfX in H. auto. *) *)

(*  (* Case "XAPP". *) *)
(*  (*  inverts H. *) *)
(*  (*  destruct IHx. eauto. *) *)
(*  (*  SCase "x value". *) *)
(*  (*   right. inverts H. inverts H4. *) *)
(*  (*    inverts H1. false. *) *)
(*  (*    inverts H0. *) *)
(*  (*    exists (substTX 0 t x1). eapply ESLAMAPP. *) *)
(*  (*    inverts H0. *) *)
(*  (*  SCase "x steps". *) *)
(*  (*   right. *) *)
(*  (*    destruct H as [x']. *) *)
(*  (*    exists (XAPP x' t). *) *)
(*  (*    apply ESAPP1. auto. *) *)

(*  Case "XLam". *)
(*   left. apply type_wfX in H. auto. *)

(*  Case "XApp". *)
(*   right. *)
(*   inverts H. *)
(*   destruct (IHx1 ds) as [| []]; eauto. *)
(*   SCase "x1 value". *)
(*   pose proof (canonicalFormTFun). *)
(*   spec H0 H5. spec H0 H. *)
(*   destruct H0 as [x' [LAM | FIX]]; subst. *)
(*   destruct (IHx2 ds) as [| []]; eauto. *)
(*   SSCase "x2 value". *)
(*   left. exists (substXX 0 x2 x'); apply EsLamApp; inverts H0; auto. *)
(*   SSCase "x2 steps". *)
(*   destruct H0 as [x'']. *)
(*   left. exists (XApp (XLam t11 x') x''). eauto. *)
(*   SSCase "x2 hasChoice". *)
(*   inversion H0. *)
(*   destruct (IHx2 ds) as [| []]; eauto. *)
(*   left. exists (substXX 0 (XFix t11 tx x') (substXX 0 x2 x')). apply EsFixApp; inverts H0; auto. *)
(*   destruct H0 as [x'']. *)
(*   left; exists (XApp (XFix t11 tx x') x''). eauto. *)
(*   inversion H0. *)
(*   SCase "x1 steps". *)
(*   left. destruct H as [x1']. exists (XApp x1' x2). apply EsContext. *)
(*   apply ESApp1; auto. *)

(*   SCase "x1 hasChoice". *)
(*   inversion H. *)
(* Qed. *)


(* Theorem progress *)
(*  :  forall ds x t *)
(*  ,  TYPE ds nil x t *)
(*  -> value x \/ (exists x', STEP x x'). *)
(* Proof. *)
 intros. gen ds.
 induction x using exp_mutind with
     (PA := fun a => a = a);
   rip; first [destruct H as [tx] | destruct H0 as [tx]];
     try invert_exp_type; nope.

 Case "XLam".
 left; eauto.

 Case "XApp".
 right.
 edestruct IHx1; eauto.
 SCase "value x1".
 edestruct IHx2; eauto.
 SSCase "value x2".
 pose proof (canonicalFormTFun).
 spec H1 H5. spec H1 H. destruct H1 as [x' [LAM | FIX]]; subst.
 SSSCase "lam".
 left; exists (substXX 0 x2 x'). apply EsLamApp. inverts H0; auto.
 SSSCase "fix".
 left; exists (substXX 0 (XFix t11 tx x') (substXX 0 x2 x')). apply EsFixApp. inverts H0; auto.
 destruct H0 as [STx2 | HCx2].
 SSCase "x2 steps".
 destruct STx2 as [x2'].
 left; exists (XApp x1 x2'). auto.
 SSCase "x2 hasChoice".
 nope.
 destruct H as [STx1 | HCx1].
 SCase "x1 steps".
 destruct STx1 as [x1'].
 left; exists (XApp x1' x2).
 eapply (EsContext (fun xx => XApp xx x2)); auto.
 SCase "x1 hasChoice".
 nope.

 Case "XTup".
 assert (Forall (fun x => wnfX x \/ (exists x', STEP x x') \/ hasChoiceX x) xs) as HWS.
 repeat nforall. rip.
 have (exists t, TYPE ds nil nil x t). dest t.
 have (value x \/ (exists x', STEP x x') \/ hasChoiceX x).
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
 nope.

 Case "XProj".
 right. destruct (IHx ds); eauto.
 SCase "value x".
 pose proof (canonicalFormTNProd).
 spec H0 H5. spec H0 H. dest xs; subst.
 left.
 pose proof (wellTypedProjHasX _ _ _ _ _ _ _ H5 H7).
 dest x. exists x. apply EsTupProj; auto.
 inverts H. inverts H1; auto.
 destruct H as [STx | HCx].
 SCase "x steps".
 left. dest x'. exists (XProj n x').
 eapply (EsContext (fun xx => XProj n xx)); eauto.
 SCase "x hasChoice".
 nope.

 Case "XNFun".
 left; eauto.

 Case "XNApp".
 right. destruct (IHx ds); eauto.
 pose proof (canonicalFormTNFun).
 spec H1 H6. spec H1 H0. dest x'; subst.
 assert (Forall (fun x => wnfX x \/ (exists x', STEP x x') \/ hasChoiceX x) xs) as HWS.

 repeat nforall. rip.
 have (exists t, TYPE ds nil nil x t). dest t.
 have (value x \/ (exists x', STEP x x') \/ hasChoiceX x).
 inverts H3; rip. inverts H4. inverts H3; auto.
 (* All args are wnf, or there is a context where one can step *)
 lets D: (@exps_ctx_run exp exp) HWS.
 inverts D.
 (* All ctor args are wnf *)
 left. eauto 6.
 (* There is a context where one ctor arg can step *)
 (* right. *)
 dest C. rename x' into x''. dest x'.
 rip. destruct H4 as [STx' | HCx'].
 left.
 destruct STx'.
 exists (XNApp (XNFun ts x'') (C x)).
 eapply (EsContext (fun xx => XNApp (XNFun ts x'') (C xx))).
 apply XcNApp2; eauto. auto.
 SCase "x' hasChoice".
 nope.
 destruct H0 as [STx | HCx].
 left.
 dest x'.
 exists (XNApp x' xs); eauto.
 eapply (EsContext (fun xx => XNApp xx xs)); eauto.
 SCase "x hasChoice".
 nope.

 Case "XFix".
 left; eauto.

 Case "XCon".
 (* All ctor args are either wnf or can step *)
 assert (Forall (fun x => wnfX x \/ (exists x', STEP x x') \/ hasChoiceX x) xs) as HWS.
 repeat nforall. rip.
 have (exists t, TYPE ds nil nil x t). dest t.
 have (value x \/ (exists x', STEP x x') \/ hasChoiceX x).
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
 nope.

 Case "XMatch".
 right.
 destruct (IHx ds); eauto.
 (* have HS: (value x \/ (exists x', STEP x x')). *)
 (* inverts HS. clear IHx. *)
 SCase "x value".
 destruct x; nope.
 SSCase "XCon".
 inverts_type.
 rewrite H8 in H9. inversion H9; subst.
 (* rrwrite (dcs0 = dcs). *)
 assert (exists ts x, getAlt d aa = Some (AAlt d ts x)).
 apply getAlt_exists.
 repeat nforall. spec H11 H15. auto.
 (* have HG: (exists ts x, getAlt d aa = Some (AAlt d ts x)) *)
 (*   by burn using getAlt_exists. *)
 dest ts. dest x.
 left. exists (substXXs 0 l x). eapply EsMatchAlt.
 inverts H0. inverts H2; auto. eauto.

 destruct H0 as [STx | HCx].
 SCase "x steps".
 left; destruct STx as [x'].
 exists (XMatch x' aa).
 lets D: EsContext XcMatch; eauto.
 SCase "x hasChoice".
 nope.
Qed.
