
Require Import FiatFormal.Language.Step.
Require Import FiatFormal.Language.TyJudge.
Require Import FiatFormal.Language.Exp.

Theorem fiatProgress
  : forall alg_ds adt_ds x t,
    TYPE alg_ds adt_ds nil x t
    -> value x \/ (exists x', STEP adt_ds x x') \/ Xhas_choice adt_ds x.
Proof.
 intros. gen t.
 induction x using exp_mutind with
     (PA := fun a => a = a)
     (PF := fun f => f = f); rip; burn.

 Case "XApp".
 right.
 inverts_type.
 edestruct IHx1; eauto.

 SCase "value x1".
 edestruct IHx2; eauto.

 SSCase "value x2".
 assert (HF: exists t1 t2 x, x1 = XFix t1 t2 x).
 { apply (value_fix _ _ _ _ _ _ H H5). }
 destruct HF as [t11].
 destruct H1 as [t12].
 destruct H1 as [x12].
 subst.
 left.
 exists (substX 0 (XFix t11 t12 x12) (substX 0 x2 x12)).
 eauto.
 destruct H0 as [[x2'] | HC].

 SSCase "x2 steps".
 left.
 exists (XApp x1 x2'). auto.

 SSCase "x2 hasChoice".
 right. eauto.
 destruct H  as [[x1'] | HC].

 SCase "x1 steps".
 left.
 exists (XApp x1' x2).
 eapply (EsContext _ (fun xx => XApp xx x2)); auto.

 SCase "x1 hasChoice".
 right. eauto.


 Case "XCon".
  inverts_type.

  (* All ctor args are either wnf or can step *)
  assert (Forall (fun x => wnfX x \/ (exists x', STEP adt_ds x x') \/ (Xhas_choice adt_ds x)) xs) as HWS.
   norm. rip.
   have (exists t, TYPE alg_ds adt_ds nil x t). dest t.
   have (value x \/ (exists x', STEP adt_ds x x') \/ (Xhas_choice adt_ds x)).
   inverts H2; burn.

  (* All ctor args are wnf, or there is a context where one can step *)
  lets D: (@exps_ctx_run exp exp) HWS.
  inverts D.
   (* All ctor args are wnf *)
   left. eauto 6.
   (* There is a context where one ctor arg can step *)
   right.
    dest C. dest x'.
    rip.
    inverts H5.
    left.
    lets D: step_context_XCon_exists H1 H0.
    destruct D as [x'']. eauto.
    right.
    apply HC_XCon. apply Exists_exists.
    exists x'; rip.
    eapply exps_In_C_pmk. eassumption.

 Case "XMatch".
  right.
  inverts_type.
  have HS: (value x \/ (exists x', STEP adt_ds x x') \/ (Xhas_choice adt_ds x)).
  inverts HS. clear IHx.
  SCase "x value".
   destruct x; nope.
    SSCase "XCon".
     inverts_type.
     rrwrite (dcs0 = dcs).
     have HG: (exists ts x, getAlt d aa = Some (AAlt d ts x))
      by burn using getAlt_exists.
     dest ts. dest x.
     left.
     exists (substXs 0 l x).
     burn.

  SCase "x steps or hasChoice".
  destruct H0 as [[x'] | HC].
  left.
  exists (XMatch x' aa).
  lets D: EsContext XcMatch; eauto.
  SSCase "x hasChoice".
  right.
  eauto.

  Case "XCall".

  pose proof (wellTypedCallHasBody_pmk _ _ _ _ _ _ _ H0).
  inverts_type.
  (* pose proof (Forall2_Forall_left _ _ _ _ H H11). *)

  assert (Forall (fun x => wnfX x \/ (exists x', STEP adt_ds x x') \/ (Xhas_choice adt_ds x)) xs) as HWS.
  norm. rip.
   have (exists t, TYPE alg_ds adt_ds nil x t). dest t.
   have (value x \/ (exists x', STEP adt_ds x x') \/ (Xhas_choice adt_ds x)).
   inverts H4; burn.

  (* All method args are wnf, or there is a context where one can step *)
  (*    or haschoice *)
  lets D: (@exps_ctx_run exp exp) HWS.
  right.
  inverts D.
  SCase "xs all wnf".

  (* All method args are wnf, must show a step with method body *)
  (* rewrite Forall_forall in H0. *)
  (* spec H0 ac. *)
  (* pose proof (getADTSigInCons_pmk _ _ _ _ H10). *)
  (* spec H0 H4. invert H0; intros. *)

  dest b. left.
  exists (substXs 0 xs b).
  apply EsADTCall; burn.

   (* There is a context where one ctor arg can step *)
    dest C. dest x'.
    rip.
    inverts H5.
    left.
    lets D: step_context_XCall_exists_pmk H3 H2.
    destruct D as [x'']. eauto.
    right.
    apply HC_XCallArgs. apply Exists_exists.
    exists x'; rip.
    eapply exps_In_C_pmk. eassumption.

Qed.


(* ORIG *)
(* A well typed expression is either a well formed value,
   or can transition to the next state. *)
(* Theorem progress *)
(*  :  forall ds x t *)
(*  ,  TYPE ds nil x t *)
(*  -> value x \/ (exists x', STEP x x'). *)
(* Proof. *)
(*  intros. gen t. *)
(*  induction x using exp_mutind with  *)
(*   (PA := fun a => a = a); rip; burn. *)

(*  Case "XApp". *)
(*   right. *)
(*   inverts_type. *)
(*   edestruct IHx1; eauto. *)
(*   SCase "value x1". *)
(*    edestruct IHx2; eauto. *)
(*     SSCase "value x2". *)
(*      have HF: (exists t x, x1 = XLam t x). *)
(*      destruct HF as [t11]. *)
(*      destruct H1 as [x12]. *)
(*      subst. *)
(*      exists (substX 0 x2 x12). *)
(*      eauto.  *)
(*     SSCase "x2 steps". *)
(*      destruct H0 as [x2']. *)
(*      exists (XApp x1 x2'). auto. *)
(*   SCase "x1 steps". *)
(*    destruct H  as [x1']. *)
(*    exists (XApp x1' x2). *)
(*    eapply (EsContext (fun xx => XApp xx x2)); auto. *)

(*  Case "XCon". *)
(*   inverts_type. *)

(*   (* All ctor args are either wnf or can step *) *)
(*   assert (Forall (fun x => wnfX x \/ (exists x', STEP x x')) xs) as HWS. *)
(*    norm. rip. *)
(*    have (exists t, TYPE ds nil x t). dest t. *)
(*    have (value x \/ (exists x', STEP x x')). *)
(*    inverts H2; burn. *)

(*   (* All ctor args are wnf, or there is a context where one can step *) *)
(*   lets D: (@exps_ctx_run exp exp) HWS. *)
(*   inverts D. *)
(*    (* All ctor args are wnf *) *)
(*    left. eauto 6. *)
(*    (* There is a context where one ctor arg can step *) *)
(*    right. *)
(*     dest C. dest x'. *)
(*     rip. *)
(*     lets D: step_context_XCon_exists H1 H5. *)
(*     destruct D as [x'']. eauto. *)

(*  Case "XCase". *)
(*   right. *)
(*   inverts_type. *)
(*   have HS: (value x \/ (exists x', STEP x x')). *)
(*   inverts HS. clear IHx. *)
(*   SCase "x value". *)
(*    destruct x; nope. *)
(*     SSCase "XCon". *)
(*      inverts_type. *)
(*      rrwrite (dcs0 = dcs). *)
(*      have HG: (exists ts x, getAlt d aa = Some (AAlt d ts x)) *)
(*       by burn using getAlt_exists. *)
(*      dest ts. dest x. *)
(*      exists (substXs 0 l x). *)
(*      burn. *)

(*   SCase "x steps". *)
(*    destruct H0 as [x']. *)
(*    exists (XCase x' aa). *)
(*    lets D: EsContext XcCase; eauto. *)
(* Qed. *)
(* Admitted. *)
