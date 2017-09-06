
Require Export FiatFormal.Language.ExpBase.
Require Export FiatFormal.Language.ExpLift.
Require Export FiatFormal.Language.ExpSubst.
Require Export FiatFormal.Language.ExpAlt.

(* Weak normal forms cannot be reduced further by
   call-by-value evaluation. *)
Inductive wnfX : exp -> Prop :=
 | Wnf_XVar
   : forall i
   , wnfX (XVar i)

 (* | Wnf_XLam *)
 (*   : forall t1 x2 *)
 (*   , wnfX (XLam t1 x2) *)

 | Wnf_XFix
   : forall t1 t2 x1
   , wnfX (XFix t1 t2 x1)

 | Wnf_XCon
   :  forall dc xs
   ,  Forall wnfX xs
   -> wnfX (XCon dc xs).
Hint Constructors wnfX.


(* Well formed expressions are closed under the given environment. *)
Inductive wfX : tyenv -> exp -> Prop :=
 | WfX_XVar
   :  forall te i
   ,  (exists t, get i te = Some t)
   -> wfX te (XVar i)

 (* | WfX_XLam *)
 (*   :  forall te t x *)
 (*   ,  wfX (te :> t) x *)
 (*   -> wfX te (XLam t x) *)

 | WfX_XFix
   : forall te t1 t2 x1
   , wfX (te :> (TFun t1 t2) :> t1) x1
     -> wfX te (XFix t1 t2 x1) (* TODO *)

 | WfX_XApp
   :  forall te x1 x2
   ,  wfX te x1 -> wfX te x2
   -> wfX te (XApp x1 x2)

 | WfX_XCon
   :  forall te dc xs
   ,  Forall (wfX te) xs
   -> wfX te (XCon dc xs)

 | WfX_XMatch
   :  forall te x alts
   ,  wfX te x
   -> Forall (wfA te) alts
   -> wfX te (XMatch x alts)

 | WfX_XChoice
   : forall te t1 xs fp,
     Forall (wfX te) xs
     -> wfP te fp
     -> wfX te (XChoice t1 xs fp)

 | WfX_XCall
   : forall adt_ds x s te ac n xs,
     getADTBody ac n adt_ds  = Some x
     -> getADTSig ac n adt_ds = Some s
     (* Having appropriate size of tyenv all the matters here *)
     -> wfX (buildMethodTyEnv (TAdt ac) s) x
     -> length xs = s.(arity) + length(s.(dom))
     -> Forall (wfX te) xs
     -> wfX te (XCall ac n xs)

with    wfA : tyenv -> alt -> Prop :=
 | WfA_AAlt
   : forall te dc ds ts x tsArgs tResult,
     getDataDef dc ds = Some (DefData dc tsArgs tResult)
     -> wfX (te >< tsArgs) x
     -> length ts = length tsArgs (* TODO: reconsider whether necessary *)
     -> wfA te (AAlt dc ts x)

with wfP : tyenv -> fpred -> Prop :=
     | WfP_FPred
       : forall pc x te,
         wfP te (FPred pc x).

Hint Constructors wfX.
Hint Constructors wfA.


(* Closed expressions are well formed under an empty environment. *)
Definition closedX (xx: exp) : Prop
 := wfX nil xx.
Hint Unfold closedX.


(* Values are closed expressions that cannot be reduced further. *)
Inductive value : exp -> Prop :=
 | Value
   :  forall xx
   ,  wnfX xx -> closedX xx
   -> value xx.
Hint Constructors value.

Lemma value_wnfX
 : forall xx, value xx -> wnfX xx.
Proof.
  intros. inverts H. auto. Qed.
Hint Resolve value_wnfX.

Lemma value_closedX
 : forall xx, value xx -> closedX xx.
Proof.
  intros. inverts H. auto. Qed.
Hint Resolve value_closedX.

Lemma value_wnfXs_XCon
 : forall xs dc
 , value (XCon dc xs) -> Forall wnfX xs.
Proof.
 intros. inverts H. inverts H0. auto.
Qed.
Hint Resolve value_wnfXs_XCon.

Lemma value_closedXs_XCon
 : forall xs dc
 , value (XCon dc xs) -> Forall closedX xs.
Proof.
 intros. inverts H. inverts H1. auto.
Qed.
Hint Resolve value_closedXs_XCon.

(* Invert all hypothesis that are compound well-formedness statements. *)
Ltac inverts_wfX :=
 repeat
  (match goal with
   | [ H: wfX _ (XVar  _)        |- _ ] => inverts H
   (* | [ H: TYPE _ _ _ (XLam  _ _)  _    |- _ ] => inverts H *)
   | [ H: wfX _ (XFix _ _ _)     |- _ ] => inverts H
   | [ H: wfX _ (XApp  _ _)      |- _ ] => inverts H
   | [ H: wfX _ (XCon  _ _)      |- _ ] => inverts H
   | [ H: wfX _ (XMatch _ _)     |- _ ] => inverts H
   | [ H: wfX _ (XChoice _ _ _)  |- _ ] => inverts H
   | [ H: wfA _ (AAlt _ _ _)     |- _ ] => inverts H
   | [ H: wfX _ (XCall _ _ _)    |- _ ] => inverts H
   | [ H: wfP _ (FPred _ _)      |- _ ] => inverts H
   end).

(* Lemma liftX_closed_pmk *)
(*   : forall x n te, *)
(*     wfX te x -> (liftX n (length te) x) = x. *)
(* Proof. *)
(*   intros x n. *)
(*   gen n. *)
(*   induction x using exp_mutind with *)
(*      (PA := fun a => forall n te, wfA te a -> (liftA n (length te) a) = a) *)
(*      (PF := fun f => f = f); intros; rip; burn; subst. *)
(*   inverts_wfX. dest t. *)
(*   simpl. *)
(*   fbreak_le_gt_dec; auto. *)
(*   pose proof (get_above_false _ _ _ _ l H); nope. *)
(*   inverts_wfX. *)
(*   spec IHx H2. simpl in *; subst. *)
(*   erewrite IHx; burn. *)
(*   inverts_wfX; simpl. *)
(*   spec IHx1 H3; spec IHx2 H4; espread; burn. *)
(*   inverts_wfX; repeat nforall. *)
(*   simpl. *)

(*   assert (forall x, In x xs -> liftX n (length te) x = x). *)
(*   intros. apply H. assumption. spec H3 H0. assumption. *)
(*   pose proof (map_ext_in _ _ xs H0). *)
(*   rewrite H1. *)
(*   rewrite map_id; burn. *)

(*   simpl. *)
(*   inverts_wfX. *)
(*   repeat nforall. *)

(*   assert (forall a, In a aa -> liftA n (length te) a = a). *)
(*   intros. apply H. assumption. spec H5 H0. assumption. *)
(*   pose proof (map_ext_in _ _ aa H0). *)
(*   rewrite H1. *)
(*   rewrite map_id. *)
(*   spec IHx H4. espread; burn. *)

(*   simpl. *)
(*   inverts_wfX. *)
(*   assert (liftX n (length (te >< ts)) x = x). *)
(*   eapply IHx. *)
(*   pose proof (getAlt_ctorArgTypesMatchDataDef _ _ _ _). *)
(*   eapply IHx. *)

(*   Admitted. *)