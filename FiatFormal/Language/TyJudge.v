(* TODO/NOTES

Switching order of forall binding changes typechecking result.

This type checks:

 | TYProg
   : forall alg_ds adt_ds d ac pf te r x t,
     TYPE alg_ds adt_ds te x t
     -> getADTRep ac adt_ds d pf = r
     -> TYPE_ADT alg_ds adt_ds ac
     -> TYPE alg_ds adt_ds te x t
     -> TYPE alg_ds adt_ds te (XLet ac x) (typeSubst ac r t)

This does not:

 | TYProg
   : forall alg_ds adt_ds d pf ac te r x t,
     TYPE alg_ds adt_ds te x t
     -> getADTRep ac adt_ds d pf = r
     -> TYPE_ADT alg_ds adt_ds ac
     -> TYPE alg_ds adt_ds te x t
     -> TYPE alg_ds adt_ds te (XLet ac x) (typeSubst ac r t)

*)

Require Export FiatFormal.Language.Exp.

(* Type Judgement assigns a type to an expression. *)
Inductive TYPE : alg_defs -> adt_defs -> tyenv -> exp -> ty -> Prop :=
 (* Variables *)
 | TYVar
   :  forall alg_ds adt_ds te i t,
     get i te = Some t
   -> TYPE alg_ds adt_ds te (XVar i) t

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

 | TYNaryFun
   : forall alg_ds adt_ds te x tsArgs tResult,
     TYPE alg_ds adt_ds (te >< tsArgs) x         tResult
     -> TYPE alg_ds adt_ds te (XNaryFun tsArgs x) (TNaryFun tsArgs tResult)

 | TYNaryApp
   :  forall alg_ds adt_ds te x xs tsArgs t2,
     TYPE alg_ds adt_ds te x           (TNaryFun tsArgs t2)
   -> Forall2 (TYPE alg_ds adt_ds te) xs tsArgs
   -> TYPE alg_ds adt_ds te (XNaryApp x xs) t2

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

 | TYPair
   : forall alg_ds adt_ds te t1 t2 x1 x2,
     TYPE alg_ds adt_ds te x1 t1
     -> TYPE alg_ds adt_ds te x2 t2
     -> TYPE alg_ds adt_ds te (XPair x1 x2) (TProd t1 t2)

 | TYFst
   : forall alg_ds adt_ds te t1 t2 x,
     TYPE alg_ds adt_ds te x (TProd t1 t2)
     -> TYPE alg_ds adt_ds te (XFst x) t1

 | TYSnd
   : forall alg_ds adt_ds te t1 t2 x,
     TYPE alg_ds adt_ds te x (TProd t1 t2)
     -> TYPE alg_ds adt_ds te (XSnd x) t2

 | TYOpCall
   : forall alg_ds adt_ds ac n te r s xs tsArgs tResult,
     getADTSig ac n adt_ds = Some s
     -> getADTRep ac adt_ds = Some r
     -> sigToNaryFunTy r s = TNaryFun tsArgs tResult
     -> Forall2 (TYPE alg_ds adt_ds te) xs tsArgs
     -> TYPE alg_ds adt_ds te (XOpCall ac n xs) tResult

 | TYProg
   : forall alg_ds adt_ds ac n te r x t,
     TYPE alg_ds adt_ds te x t
     -> getADTRep ac adt_ds = Some r
     -> TYPE_ADT alg_ds adt_ds ac
     -> TYPE alg_ds adt_ds te x t
     -> TYPE alg_ds adt_ds te (XLet ac n x) (typeSubst ac r t)

with TYPE_ADT : alg_defs -> adt_defs -> adtcon -> Prop :=
     | TYAdt : forall alg_ds adt_ds ac ss bs r,
         getADTBodies ac adt_ds = Some bs
         -> getADTSigs ac adt_ds = Some ss
         -> getADTRep ac adt_ds = Some r
         -> Forall2 (TYPE alg_ds adt_ds nil) bs (map (sigToNaryFunTy r) ss)
         -> TYPE_ADT alg_ds adt_ds ac

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
   | [ H: TYPE _ _ _ (XNaryFun _ _)  _    |- _ ] => inverts H
   | [ H: TYPE _ _ _ (XNaryApp _ _)  _    |- _ ] => inverts H
   | [ H: TYPE _ _ _ (XApp  _ _)  _    |- _ ] => inverts H
   | [ H: TYPE _ _ _ (XCon  _ _)  _    |- _ ] => inverts H
   | [ H: TYPE _ _ _ (XMatch _ _)  _    |- _ ] => inverts H
   | [ H: TYPE _ _ _ (XChoice _ _ _) _  |- _ ] => inverts H
   | [ H: TYPEA _ _ _ (AAlt _ _ _) _ _  |- _ ] => inverts H
   | [ H: TYPE _ _ _ (XPair _ _) _      |- _ ] => inverts H
   | [ H: TYPE _ _ _ (XFst _) _         |- _ ] => inverts H
   | [ H: TYPE _ _ _ (XSnd _) _         |- _ ] => inverts H
   | [ H: TYPE _ _ _ (XOpCall _ _ _) _ |- _ ] => inverts H
   | [ H: TYPEP _ _ _ (FPred _ _) _ |- _ ] => inverts H
   | [ H: TYPE _ _ _ (XLet _ _ _) _ |- _ ] => inverts H
   | [ H: TYPE_ADT _ _ _ _ |- _ ] => inverts H
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

(* ---------------------------------------------------------- *)

Definition buildNaryApp x xs :=
  XNaryApp x xs.

Lemma type_method_type_nary :
  forall alg_ds adt_ds ac n te xs b tResult,
    TYPE alg_ds adt_ds te (XOpCall ac n xs) tResult
    -> getADTBody ac n adt_ds = Some b
    -> TYPE_ADT alg_ds adt_ds ac
    -> TYPE alg_ds adt_ds te (buildNaryApp b xs) tResult.
Proof.
  intros. unfold buildNaryApp.
  eapply TYNaryApp.
  inversion H; subst.
  inversion H1; subst.
  rewrite H9 in H4. norm_inverts_option.
Admitted.

Lemma adt_x_in_xs :
  forall ac n adt_ds b bs,
    getADTBody ac n adt_ds = Some b
    -> getADTBodies ac adt_ds = Some bs
    -> In b bs.
Proof.
  intros. unfold getADTBody, getADTBodies in *.
  induction bs.
Admitted.

(* Lemma wellTypedCallHasBody_pmk : forall ac n alg_ds adt_ds te xs t, *)
(*     TYPE alg_ds adt_ds te (XOpCall ac n xs) t -> *)
(*     exists b, getADTBody ac n adt_ds = Some b. *)
(* Proof. *)
  (* intros. *)
  (* inverts_type; burn. *)
(* Admitted. *)
(* Qed. *)


Fixpoint methodSubstX ac n s x : exp :=
  match x with
  | XOpCall ac' n' xs => if andb (adtcon_beq ac ac') (beq_nat n n')
                        then (buildNaryApp s xs)
                        else XOpCall ac' n' (map (methodSubstX ac n s) xs)
  | XLet ac' n' x' => XLet ac' n' (methodSubstX ac n s x')
  | XNaryFun tsArgs x' => XNaryFun tsArgs (methodSubstX ac n s x')
  | XNaryApp x' xs => XNaryApp (methodSubstX ac n s x') (map (methodSubstX ac n s) xs)
  | XFix t1 t2 x' => XFix t1 t2 (methodSubstX ac n s x')
  | XApp x1 x2 => XApp (methodSubstX ac n s x1) (methodSubstX ac n s x2)
  | XVar n => XVar n
  | XCon dc xs => XCon dc (map (methodSubstX ac n s) xs)
  | XMatch x' aa => XMatch (methodSubstX ac n s x') (map (methodSubstA ac n s) aa)
  | XChoice t1 xs fp => XChoice t1 xs fp (* TODO *)
  | XPair x1 x2 => XPair (methodSubstX ac n s x1) (methodSubstX ac n s x2)
  | XFst x' => XFst (methodSubstX ac n s x')
  | XSnd x' => XSnd (methodSubstX ac n s x')
  end
with methodSubstA ac n s a : alt :=
       match a with
       | AAlt dc ts x
         => AAlt dc ts (methodSubstX ac n s x)
       end.

(* Fixpoint methodSubstX ac n adt_ds b d pf (pre : getADTBody ac n adt_ds d pf = Some b) (x : exp) : exp := *)
(*   match x with *)
(*   | XOpCall ac' n' xs => if andb (adtcon_beq ac ac') (beq_nat n n') *)
(*                         then (buildNaryApp b xs) *)
(*                         else XOpCall ac' n' (map (methodSubstX ac n adt_ds b pre) xs) *)
(*   | XLet ac' x' => XLet ac (methodSubstX ac n adt_ds b pre x') *)
(*   | XNaryFun tsArgs x' => XNaryFun tsArgs (methodSubstX ac n adt_ds b pre x') *)
(*   | XNaryApp x' xs => XNaryApp (methodSubstX ac n adt_ds b pre x') (map (methodSubstX ac n adt_ds b pre) xs) *)
(*   | XFix t1 t2 x' => XFix t1 t2 (methodSubstX ac n adt_ds b pre x') *)
(*   | XApp x1 x2 => XApp (methodSubstX ac n adt_ds b pre x1) (methodSubstX ac n adt_ds b pre x2) *)
(*   | XVar n => XVar n *)
(*   | XCon dc xs => XCon dc (map (methodSubstX ac n adt_ds b pre) xs) *)
(*   | XMatch x' aa => XMatch (methodSubstX ac n adt_ds b pre x') (map (methodSubstA ac n adt_ds b pre) aa) *)
(*   | XChoice t1 xs fp => XChoice t1 xs fp (* TODO *) *)
(*   | XPair x1 x2 => XPair (methodSubstX ac n adt_ds b pre x1) (methodSubstX ac n adt_ds b pre x2) *)
(*   | XFst x' => XFst (methodSubstX ac n adt_ds b pre x') *)
(*   | XSnd x' => XSnd (methodSubstX ac n adt_ds b pre x') *)
(*   end *)

(* with methodSubstA ac n adt_ds b d pf (pre : getADTBody ac n adt_ds d pf = Some b) (a : alt) : alt := *)
(*        match a with *)
(*        | AAlt dc ts x *)
(*          => AAlt dc ts (methodSubstX ac n adt_ds b pre x) *)
(*        end. *)

(* Fixpoint methodsToFunctions (ac : adtcon) (adt_ds : adt_defs) (d : adt_def) (pre : getADTDef ac adt_ds = Some d) (x : exp) : exp := *)
(*   match pre with *)
(*   | _ => *)
