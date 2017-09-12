(* TODO/NOTES

Consider negative effects of adding typing rule for switching between
opaque typing by TYPE and TYPE_ADT_BODY. Proofs break.

The main reason for adding the new typing rule is to facilitate the
needed subst_exp_exp_ADT_pmk proof in SubstExpExp.v

Still not sure how (if at all) to represent product types

*)




Require Export FiatFormal.Language.Exp.

(* Type Judgement assigns a type to an expression. *)
Inductive TYPE : alg_defs -> adt_defs -> tyenv -> exp -> ty -> Prop :=
 (* Variables *)
 | TYVar
   :  forall alg_ds adt_ds te i t,
     get i te = Some t
   -> TYPE alg_ds adt_ds te (XVar i) t

 (* Lambda Abstraction *)
 (* | TYLam *)
 (*   :  forall alg_ds adt_ds te x t1 t2, *)
 (*     TYPE alg_ds adt_ds (te :> t1) x            t2 *)
 (*     -> TYPE alg_ds adt_ds te         (XLam t1 x) (TFun t1 t2) *)

 | TYFix
   : forall alg_ds adt_ds te t1 t2 x1,
     TYPE alg_ds adt_ds (te :> (TFun t1 t2) :> t1) x1 t2
     -> TYPE alg_ds adt_ds te (XFix t1 t2 x1) (TFun t1 t2)

 (* Applications *)
 | TYApp
   :  forall alg_ds adt_ds te x1 x2 t1 t2,
     TYPE alg_ds adt_ds te x1           (TFun t1 t2)
   -> TYPE alg_ds adt_ds te x2           t1
   -> TYPE alg_ds adt_ds te (XApp x1 x2) t2

 (* Data Constructors *)
 | TYCon
   :  forall alg_ds adt_ds te xs dc dcs tsArgs tc,
     getDataDef dc alg_ds = Some (DefData     dc tsArgs (TCon tc))
   -> getTypeDef tc alg_ds = Some (DefDataType tc dcs)
   -> In dc dcs
   -> Forall2 (TYPE alg_ds adt_ds te) xs tsArgs
   -> TYPE alg_ds adt_ds te (XCon dc xs) (TCon tc)

 (* Match Expressions *)
 | TYMatch
   :  forall alg_ds adt_ds te xObj tcPat tResult alts dcs,

      (* check types of expression and alternatives *)
     TYPE alg_ds adt_ds te xObj (TCon tcPat)
   -> Forall (fun alt => TYPEA alg_ds adt_ds te alt (TCon tcPat) tResult) alts

      (* there must be at least one alternative *)
   -> length alts > 0

      (* all data cons must have a corresponding alternative *)
   -> getTypeDef tcPat alg_ds = Some (DefDataType tcPat dcs)
   -> Forall (fun dc => In dc (map dcOfAlt alts)) dcs

   -> TYPE alg_ds adt_ds te (XMatch xObj alts) tResult

 | TYChoice
   : forall alg_ds adt_ds t1 t2 xs te P ts,
     TYPEP alg_ds adt_ds te P t2
     -> Forall2 (TYPE alg_ds adt_ds te) xs ts
     -> TYPE alg_ds adt_ds te (XChoice t1 xs P) t1

 (* | TYCall *)
 (*   : forall alg_ds adt_ds ac n te s b r xs, *)
 (*     getADTSig ac n adt_ds = Some s *)
 (*     -> getADTBody ac n adt_ds = Some b *)
 (*     -> getADTRep ac adt_ds = Some r *)
 (*     -> Forall2 (TYPE alg_ds adt_ds te) xs (buildMethodTyEnv (TAdt ac) s) *)
 (*     -> TYPE alg_ds adt_ds (buildMethodTyEnv r s) b s.(cod) (* TRANSLUCENT *) *)
 (*     -> TYPE alg_ds adt_ds te (XCall ac n xs) s.(cod)       (* OPAQUE *) *)
 | TYCall
   : forall alg_ds adt_ds ac n te r s b xs,
     getADTSig ac n adt_ds = Some s
     -> getADTBody ac n adt_ds = Some b
     -> getADTRep ac adt_ds = Some r
     -> Forall2 (TYPE alg_ds adt_ds te) xs (buildMethodTyEnv (TAdt ac) s)
     -> TYPE_ADT_BODY alg_ds adt_ds te r s b s.(cod_opaque) (* CONSIDER:
 should this premise be "TYPE" rather than "TYPE_ADT_BODY" *)
     -> TYPE alg_ds adt_ds te (XCall ac n xs) s.(cod_opaque)

 (* | TYOpaque (* TODO: discuss this with ben *) *)
 (*   : forall alg_ds adt_ds r s body, *)
 (*     TYPE_ADT_BODY alg_ds adt_ds r s body s.(cod_opaque) *)
 (*     -> TYPE alg_ds adt_ds (buildMethodTyEnv (TAdt s.(ac)) s) body s.(cod_opaque) *)

with TYPE_ADT_BODY : alg_defs -> adt_defs -> tyenv -> Rep -> Sig -> exp -> ty -> Prop :=
     | TYBody : forall alg_ds adt_ds te r s body,
         TYPE alg_ds adt_ds (te >< (buildMethodTyEnv r s)) body s.(cod_clear)
         -> TYPE_ADT_BODY alg_ds adt_ds te r s body s.(cod_opaque)

with TYPEP : alg_defs -> adt_defs -> tyenv -> fpred -> ty -> Prop :=
     (* placeholder for predicate typing -- this is old *)
     | TYPred : forall alg_ds adt_ds te pc x,
         TYPEP alg_ds adt_ds te (FPred pc x) (TPred pc)

with TYPEA : alg_defs -> adt_defs -> tyenv -> alt -> ty -> ty -> Prop :=
     (* Match Alternatives *)
     | TYAlt
       :  forall alg_ds adt_ds te x1 t1 dc tsArgs tResult,
         getDataDef dc alg_ds = Some (DefData dc tsArgs tResult)
         -> TYPE  alg_ds adt_ds (te >< tsArgs) x1 t1
         -> TYPEA alg_ds adt_ds te (AAlt dc tsArgs x1) tResult t1.

Hint Constructors TYPE.
Hint Constructors TYPEA.
Hint Constructors TYPEP.


(* Invert all hypothesis that are compound typing statements. *)
Ltac inverts_type :=
 repeat
  (match goal with
   | [ H: TYPE _ _ _ (XVar  _)    _    |- _ ] => inverts H
   (* | [ H: TYPE _ _ _ (XLam  _ _)  _    |- _ ] => inverts H *)
   | [ H: TYPE _ _ _ (XFix _ _ _)  _    |- _ ] => inverts H
   | [ H: TYPE _ _ _ (XApp  _ _)  _    |- _ ] => inverts H
   | [ H: TYPE _ _ _ (XCon  _ _)  _    |- _ ] => inverts H
   | [ H: TYPE _ _ _ (XMatch _ _)  _    |- _ ] => inverts H
   | [ H: TYPE _ _ _ (XChoice _ _ _) _  |- _ ] => inverts H
   | [ H: TYPEA _ _ _ (AAlt _ _ _) _ _  |- _ ] => inverts H
   | [ H: TYPE _ _ _ (XCall _ _ _) _ |- _ ] => inverts H
   | [ H: TYPEP _ _ _ (FPred _ _) _ |- _ ] => inverts H
   | [ H: TYPE_ADT_BODY _ _ _ _ _ _ _ |- _ ] => inverts H
   end).


(********************************************************************)
(* Forms of values.
   If we know the type of a value,
   then we know the form of that value. *)
(* Lemma value_lam *)
(*  :  forall x alg_ds adt_ds te t1 t2 *)
(*  ,  value x *)
(*  -> TYPE alg_ds adt_ds te x (TFun t1 t2) *)
(*  -> (exists t x', x = XLam t x') *)
(* Proof. *)
(*  intros. destruct x; burn. *)
(* Qed. *)
(* Hint Resolve value_lam. *)

Lemma value_fix
  : forall x alg_ds adt_ds te t1 t2,
    value x
    -> TYPE alg_ds adt_ds te x (TFun t1 t2)
    -> exists t1 t2 x', x = XFix t1 t2 x'.
Proof.
  intros. destruct x; burn.
(* Qed. *)
Admitted.
Hint Resolve value_fix.

(********************************************************************)
(* A well typed expression is well formed *)
Theorem type_wfX
  :  forall alg_ds adt_ds te x t,
    TYPE alg_ds adt_ds te x t
    -> wfX te x.
Proof.

 (* intros. gen alg_ds adt_ds te t. *)
 (* induction x using exp_mutind with *)
 (*     (PA := fun a => forall alg_ds adt_ds te t1 t2, *)
 (*                TYPEA alg_ds adt_ds te a t1 t2 *)
 (*                -> wfA te a) *)
 (*     (PF := fun f => forall alg_ds adt_ds te t1, *)
 (*                TYPEP alg_ds adt_ds te f t1 *)
 (*                -> wfP te f) *)
 (*  ; intros; inverts_type; eauto. *)

 (* Case "XCon". *)
 (*  apply WfX_XCon. repeat nforall. intros. *)
 (*  have HT: (exists t, TYPE alg_ds adt_ds te x t). *)
 (*  spec H H0 alg_ds adt_ds te. *)
 (*  destruct HT as [t]. *)
 (*  burn. *)

 (* Case "XMatch". *)
 (*  eapply WfX_XMatch; repeat nforall; burn. *)

 (*  Case "XChoice". *)
 (*  apply WfX_XChoice. *)
 (*  repeat nforall; intros. *)
 (*  spec H H0 alg_ds adt_ds te. *)
 (*  pose proof (Forall2_exists_left (TYPE alg_ds adt_ds te)). *)
 (*  spec H1 H0 H9. *)
 (*  destruct H1 as [y]; burn. *)
 (*  eapply IHx; burn. *)
 (*  apply WfP_FPred. *)

 (*  Case "XCall". *)
 (*  repeat nforall. *)


  (* apply (WfX_XCall adt_ds ). *)

(* Qed. *)
Admitted.
Hint Resolve type_wfX.


(* Weakening Type Env in Type Judgement.
   We can insert a new type into the type environment, provided we
   lift existing references to types higher in the stack across
   the new one. *)
Lemma type_tyenv_insert
 :  forall alg_ds adt_ds te ix x t1 t2
 ,  TYPE alg_ds adt_ds te x t1
 -> TYPE alg_ds adt_ds (insert ix t2 te) (liftX 1 ix x) t1.
Proof.
(*  intros. gen ix ds te t1. *)
(*  induction x using exp_mutind with  *)
(*   (PA := fun a => forall ix ds te t3 t4 *)
(*       ,  TYPEA ds te a t3 t4  *)
(*       -> TYPEA ds (insert ix t2 te) (liftA 1 ix a) t3 t4) *)
(*   ; intros; inverts_type; burn; simpl. *)

(*  Case "XVar". *)
(*   lift_cases; burn. *)

(*  Case "XLam". *)
(*   apply TYLam. *)
(*   rewrite insert_rewind. auto. *)

(*  Case "XCon". *)
(*   eapply TYCon; burn. *)
(*    apply (Forall2_map_left (TYPE ds (insert ix t2 te))). *)
(*    apply (Forall2_impl_in  (TYPE ds te)); eauto. *)
(*    nforall. eauto. *)

(*  Case "XCase". *)
(*   eapply TYCase; eauto. *)
(*    apply Forall_map. *)
(*    apply (Forall_impl_in (fun a => TYPEA ds te a (TCon tcPat) t1)); eauto. *)
(*    repeat nforall. burn. *)

(*   rewrite map_length; auto. *)

(*   norm. *)
(*    intros. rename x0 into d.  *)
(*    rewrite map_map. unfold Basics.compose. *)
(*    eapply map_exists_in. *)
(*    have (In d (map dcOfAlt aa)).  *)
(*    assert (exists a, dcOfAlt a = d /\ In a aa). *)
(*     eapply map_in_exists. auto. *)
(*    shift a. rip. *)
(*    eapply dcOfAlt_liftA. *)

(*  Case "XAlt". *)
(*   eapply TYAlt; eauto. *)
(*   rewrite insert_app. auto. *)
(* Qed.  *)
Admitted.

(* We can push a new type onto the environment stack provided
   we lift references to existing types across the new one. *)
Lemma type_tyenv_weaken1
 :  forall alg_ds adt_ds te x t1 t2
 ,  TYPE alg_ds adt_ds te x t1
 -> TYPE alg_ds adt_ds (te :> t2) (liftX 1 0 x) t1.
Proof.
(*  intros. *)
(*  rrwrite (te :> t2 = insert 0 t2 te). *)
(*  burn using type_tyenv_insert. *)
(* Qed. *)
Admitted.

(* We can push several new types onto the environment stack provided
   we lift referenes to existing types across the new one. *)
Lemma type_tyenv_weaken_append
 :  forall alg_ds adt_ds te te' x t1
 ,  TYPE alg_ds adt_ds te x t1
 -> TYPE alg_ds adt_ds (te >< te') (liftX (length te') 0 x) t1.
Proof.
(*  intros. *)
(*  induction te'; simpl. *)
(*  rewrite liftX_zero; auto. *)
(*  rewrite <- nat_plus_one. *)
(*  rrwrite (length te' + 1 = 1 + length te'). *)
(*  rewrite <- liftX_plus. *)
(*  eapply type_tyenv_weaken1. auto.  *)
(* Qed. *)
Admitted.

Lemma wellTypedCallHasBody_pmk : forall ac n alg_ds adt_ds te xs t,
    TYPE alg_ds adt_ds te (XCall ac n xs) t ->
    exists b, getADTBody ac n adt_ds = Some b.
Proof.
  (* intros. *)
  (* inverts_type; burn. *)
Admitted.
(* Qed. *)