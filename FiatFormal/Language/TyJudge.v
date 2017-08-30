
Require Export FiatFormal.Language.Exp.

(* Type Judgement assigns a type to an expression. *)
Inductive TYPE : alg_defs -> adt_defs -> tyenv -> exp -> ty -> Prop :=
 (* Variables *)
 | TYVar
   :  forall alg_ds adt_ds te i t,
     get i te = Some t
   -> TYPE alg_ds adt_ds te (XVar i) t

 (* Lambda Abstraction *)
 | TYLam
   :  forall alg_ds adt_ds te x t1 t2,
     TYPE alg_ds adt_ds (te :> t1) x            t2
     -> TYPE alg_ds adt_ds te         (XLam t1 x) (TFun t1 t2)

 | TYFix
   : forall alg_ds adt_ds te t1 t2 x1,
     TYPE alg_ds adt_ds (te :> (TFun t1 t2) :> t1) x1 t2
     (* TODO: reconsider after defining step relation for fix *)
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
   : forall alg_ds adt_ds t1 t2 xs te P,
     TYPEP alg_ds adt_ds te P t2
     -> TYPE alg_ds adt_ds te (XChoice t1 xs P) t1

 | TYCall
   : forall alg_ds adt_ds ac n te s xs,
     (* check that all adts are well typed *)
     WELL_TYPED_ADTS alg_ds adt_ds
     -> getADTSig ac n adt_ds = Some s
     -> Forall2 (TYPE alg_ds adt_ds te) xs (buildMethodTyEnv (TAdt ac) s)
     -> TYPE alg_ds adt_ds te (XCall ac n xs) s.(cod)

with WELL_TYPED_ADTS : alg_defs -> adt_defs -> Prop :=
     (* TODO: consider whether or not a tyenv needed *)
     | TYADTS : forall alg_ds adt_ds,
         Forall (WELL_TYPED_ADT alg_ds adt_ds) (getADTCons adt_ds)
         -> WELL_TYPED_ADTS alg_ds adt_ds

with WELL_TYPED_ADT : alg_defs -> adt_defs -> adtcon -> Prop :=
     | TYADT : forall alg_ds adt_ds ac adt_d r ss xs,
         getADTDef ac adt_ds = Some adt_d
         -> getRep adt_d = r
         -> getSigs adt_d = ss
         -> getBodies adt_d = xs
         (* ensure that cod = (FiatProdType)? *)
         -> Forall3 (TYPE alg_ds adt_ds) (map (buildMethodTyEnv r) ss) xs (map cod ss) (* TODO: cod needs to reference Rep, not opaque type variable *)
         -> WELL_TYPED_ADT alg_ds adt_ds ac

with TYPEP : alg_defs -> adt_defs -> tyenv -> fpred -> ty -> Prop :=
     (* placeholder for predicate typing -- this is old *)
     | TYPred : forall alg_ds adt_ds te pc,
         TYPEP alg_ds adt_ds te (FPred pc) (TPred pc)

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
Hint Constructors WELL_TYPED_ADTS.
Hint Constructors WELL_TYPED_ADT.

(* Inductive wellTypedMethod : *)


(* Inductive wfDef : def -> Prop := *)
(* | WF_DTYPE : forall tc dcs, wfDef (DefDataType tc dcs) *)
(* | WF_DATA  : forall dc ts tResult, wfDef (DefDataType dc ts tResult) *)
(* | WF_ADT   : forall ac r sigs xs ds te, *)
(*     let sigs' := map (replace_TAdt_with_Rep r ac) sigs *)
(*     in *)
(*     Forall2 (TYPE ds (te >< sigs')) xs (map get_last sigs') *)

(*             Inductive wfDefs : defs -> Prop := *)
(* | WFD_NIL  : wfDefs nil *)
(* | WFD_CONS : forall d ds, wfDef d -> wfDefs ds -> wfDefs (ds :> d). *)


(* Invert all hypothesis that are compound typing statements. *)
Ltac inverts_type :=
 repeat
  (match goal with
   | [ H: TYPE  _ _ (XVar  _)    _    |- _ ] => inverts H
   | [ H: TYPE  _ _ (XLam  _ _)  _    |- _ ] => inverts H
   | [ H: TYPE _ _ (XFix _ _ _)  _    |- _ ] => inverts H
   | [ H: TYPE  _ _ (XApp  _ _)  _    |- _ ] => inverts H
   | [ H: TYPE  _ _ (XCon  _ _)  _    |- _ ] => inverts H
   | [ H: TYPE  _ _ (XMatch _ _)  _    |- _ ] => inverts H
   | [ H: TYPE  _ _ (XChoice _ _ _) _  |- _ ] => inverts H
   | [ H: TYPEA _ _ (AAlt _ _ _) _ _  |- _ ] => inverts H
   end).


(********************************************************************)
(* Forms of values.
   If we know the type of a value,
   then we know the form of that value. *)
Lemma value_lam
 :  forall x alg_ds adt_ds te t1 t2
 ,  value x
 -> TYPE alg_ds adt_ds te x (TFun t1 t2)
 -> (exists t x', x = XLam t x') \/ (exists t1 t2 x', x = XFix t1 t2 x'). (* TODO *)
Proof.
(*  intros. destruct x; burn. *)
(* Qed. *)
Admitted.
Hint Resolve value_lam.


(********************************************************************)
(* A well typed expression is well formed *)
Theorem type_wfX
  :  forall alg_ds adt_ds te x t,
    TYPE alg_ds adt_ds te x t
    -> wfX te x.
Proof.
(*  intros. gen ds te t. *)
(*  induction x using exp_mutind with  *)
(*   (PA := fun a => forall ds te t1 t2 *)
(*       ,  TYPEA ds te a t1 t2  *)
(*       -> wfA te a) *)
(*   ; intros; inverts_type; eauto. *)

(*  Case "XCon". *)
(*   apply WfX_XCon. repeat nforall. intros. *)
(*   have HT: (exists t, TYPE ds te x t). *)
(*   spec H H0 ds te. *)
(*   destruct HT as [t]. *)
(*   burn. *)

(*  Case "XCase". *)
(*   eapply WfX_XCase; repeat nforall; burn. *)
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
