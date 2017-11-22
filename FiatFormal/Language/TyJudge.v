
Require Import FiatFormal.Language.SubstTypeType.
Require Export FiatFormal.Language.KiJudge.
Require Export FiatFormal.Language.TyEnv.
Require Export FiatFormal.Language.Exp.


(* Type judgement assigns a type to an expression. *)
Inductive TYPE (ds : defs) : kienv -> tyenv -> exp -> ty -> Prop :=
 | TYVar
   : forall i ke te t,
     get i te = Some t
   -> KIND ke t  KStar
   -> TYPE ds ke te (XVar i) t

 | TYApp
   : forall ke te x1 x2 t11 t12,
     TYPE ds ke te x1 (TFun t11 t12)
   -> TYPE ds ke te x2 t11
   -> TYPE ds ke te (XApp x1 x2) t12

 | TYTup
   : forall ke te xs ts,
     Forall2 (TYPE ds ke te) xs ts
     -> TYPE ds ke te (XTup xs) (TNProd ts)

 | TYNFun
   : forall ke te x ts tRes,
     Forall (fun t => KIND ke t KStar) ts
     -> TYPE ds ke (te >< ts) x tRes
     -> TYPE ds ke te (XNFun ts x) (TNFun ts tRes)

 | TYProj
   : forall ke te n x ts tRes,
     TYPE ds ke te x (TNProd ts)
     -> get n ts = Some tRes
     -> TYPE ds ke te (XProj n x) tRes

 | TYNApp
   : forall ke te x xArgs ts tRes,
     TYPE ds ke te x (TNFun ts tRes)
     -> Forall2 (TYPE ds ke te) xArgs ts
     -> TYPE ds ke te (XNApp x xArgs) tRes

 | TYFix
   : forall ke te t1 t2 x,
     KIND ke t1 KStar
     -> TYPE ds ke (te :> (TFun t1 t2) :> t1) x t2
     -> TYPE ds ke te (XFix t1 t2 x) (TFun t1 t2)

 | TYCon
   : forall ke te dc xs tsArgs tc dcs,
     getDataDef dc ds = Some (DefData dc tsArgs (TCon tc))
     -> getTypeDef tc ds = Some (DefDataType tc dcs)
     -> Forall (simpleType) tsArgs
     -> In dc dcs
     -> Forall2 (TYPE ds ke te) xs tsArgs
     -> TYPE ds ke te (XCon dc xs) (TCon tc)

 (* Case Expressions *)
 | TYMatch
   : forall ke te xObj tcPat tRes alts dcs,
     (* check types of expression and alternatives *)
     TYPE ds ke te xObj (TCon tcPat)
     -> Forall (fun alt => TYPEA ds ke te alt (TCon tcPat) tRes) alts
     (* there must be at least one alternative *)
     -> length alts > 0
     (* all data cons must have a corresponding alternative *)
     -> getTypeDef tcPat ds = Some (DefDataType tcPat dcs)
     -> Forall (fun dc => In dc (map dcOfAlt alts)) dcs
     -> TYPE ds ke te (XMatch xObj alts) tRes

 | TYChoice
   : forall ke te tRes pc xs tsArgs,
     (* get proof constructor definition *)
     getPropDef pc ds = Some (DefProp pc tsArgs)
     -> Forall (simpleType) tsArgs
     (* require at least one arg type for any prop *)
     -> get 0 tsArgs = Some tRes
     -> KIND ke tRes KStar
     (* check type of annotation plus types of expressions
        match signature of proof constructor *)
     -> Forall2 (TYPE ds ke te) xs (tl tsArgs)
     -> TYPE ds ke te (XChoice tRes pc xs) tRes

with TYPEA (ds : defs) : kienv -> tyenv -> alt -> ty -> ty -> Prop :=
 | TYAlt
   : forall ke te x1 t1 dc tsArgs tcPat,
     getDataDef dc ds = Some (DefData dc tsArgs (TCon tcPat))
     -> Forall (simpleType) tsArgs
     (* note: checking tRes well kinded is implicit in TYMatch, I *)
     (* believe *)
     (* note: currently there is no such KIND premise in TYCon, which seems wrongly asymmetric *)
     -> Forall (fun t => KIND ke t KStar) tsArgs
     -> TYPE  ds ke (te >< tsArgs) x1 t1
     -> TYPEA ds ke te (AAlt dc tsArgs x1) (TCon tcPat) t1.

Hint Constructors TYPE.
Hint Constructors TYPEA.


(* -------------------------------------------------- *)
Fixpoint dup {A : Type} (a : A) (c : nat) : list A :=
  match c with
  | O => nil
  | S c' => a :: (dup a c')
  end.

Lemma dup_map {A : Type} : forall (f : A -> A) (a : A) (c : nat),
    map f (dup a c) = dup (f a) c.
Proof.
  induction c; burn.
Qed.

Inductive TYPEMETHOD (rep : ty) (ds : defs) : kienv -> tyenv -> method -> ty -> Prop :=
| TYMETHOD : forall ke te arity dom body cod tRes,
    cod = (TNProd ((nil :> rep) :> tRes))
    -> TYPE ds ke te body (TNFun ((dup rep arity) >< dom) cod)
    -> TYPEMETHOD rep ds ke te (mkMethod arity dom body cod) (TNFun ((dup rep arity) >< dom) cod).
Hint Constructors TYPEMETHOD.

(* ADT judgement assigns a type to an ADT. *)
Inductive TYPEADT (ds : defs) : kienv -> tyenv -> adt -> list ty -> Prop :=
| TYADT : forall ke te ms tr ts,
    KIND ke tr KStar
    -> Forall2 (TYPEMETHOD tr ds ke te) ms (map (substTT 0 tr) ts)
    -> TYPEADT ds ke te (IADT tr ms (map (TExists) ts)) (map (TExists) ts).
Hint Constructors TYPEADT.

(* Program judgement assigns a type to a program. *)
Inductive TYPEPROG (ds : defs) : kienv -> tyenv -> prog -> ty -> Prop :=
| TYLet : (* forall ds ke te tr x t p t2, *)
    forall ke te tr ms ts t2 p,
    TYPEADT ds ke te (IADT tr ms (map (TExists) ts)) (map (TExists) ts)
    -> TYPEPROG ds (ke :> KStar) ((liftTE 0 te) >< ts) p t2
    -> TYPEPROG ds ke te (PLET (IADT tr ms (map (TExists) ts)) p) (substTT 0 tr t2)
    (* TYPEADT ds ke te (IADT tr x (TExists t)) (TExists t) *)
    (* -> TYPEPROG ds (ke :> KStar) ((liftTE 0 te) :> t) p t2 *)
    (* -> TYPEPROG ds ke te (PLET (IADT tr x (TExists t)) p) (substTT 0 tr t2) *)
| TYExp : forall ke te x t,
    TYPE ds ke te x t
    -> TYPEPROG ds ke te (PEXP x) t.


Ltac invert_adt_type :=
  repeat
    (match goal with
     | [ H : TYPEADT _ _ _ ?a _ |- _ ] => destruct a; inverts H
     end).

Ltac invert_exp_type :=
  repeat
    (match goal with
     | [ H: TYPE  _ _ _ (XVar  _)     _    |- _ ] => inverts H
     | [ H: TYPE  _ _ _ (XApp  _ _)   _    |- _ ] => inverts H
     | [ H: TYPE  _ _ _ (XTup _)   _    |- _ ] => inverts H
     | [ H: TYPE  _ _ _ (XProj  _ _)   _    |- _ ] => inverts H
     | [ H: TYPE  _ _ _ (XFix  _ _ _)   _    |- _ ] => inverts H
     | [ H: TYPE  _ _ _ (XNFun _ _)   _    |- _ ] => inverts H
     | [ H: TYPE  _ _ _ (XNApp  _ _)   _    |- _ ] => inverts H
     | [ H: TYPE  _ _ _ (XCon _ _) _    |- _ ] => inverts H
     | [ H: TYPE  _ _ _ (XMatch _ _)   _    |- _ ] => inverts H
     | [ H: TYPE  _ _ _ (XChoice _ _ _) _ |- _ ] => inverts H
     | [ H: TYPEA _ _ _ (AAlt _ _ _)    _ _  |- _ ] => inverts H
    end).

Ltac invert_prog_type :=
  repeat
    (match goal with
     | [ H : TYPEPROG _ _ _ _ _ |- _] => inverts H
    end).

Ltac inverts_method_type :=
  repeat
    (match goal with
     | [ H : TYPEMETHOD _ _ _ _ _ |- _ ] => inverts H
    end).

Ltac inverts_type :=
  repeat
    (match goal with
     | [ H : TYPE _ _ _ _ _ |- _ ] => inverts H
     | [ H : TYPEADT _ _ _ _ _ |- _ ] => inverts H
     | [ H : TYPEPROG _ _ _ _ _ |- _ ] => inverts H
     end).


Lemma Forall2_exists_right_in
 : forall {A B} (R: A -> B -> Prop) y xs ys
 ,             In y ys  -> Forall2 R xs ys
 -> (exists x, In x xs  /\         R x  y).
Proof.
 intros.
 induction H0.
  false.
  simpl in H. destruct H.
   subst.
   exists x. split. simpl. auto. auto.
   lets D: IHForall2 H.
   destruct D.
   exists x0.
    inverts H2.
    split. simpl. auto. auto.
Qed.

(* ----------------------------------------------------- *)
(* The type produced by a type judgement is well kinded. *)
Theorem type_kind
  : forall ds ke te x t,
    TYPE ds ke te x t
    -> KIND ke t KStar.
Proof.
 intros. gen ds ke te t.
 induction x using exp_mutind
   with (PA := fun a => forall ds ke te tBuilds tRes,
                   TYPEA ds ke te a tBuilds tRes
                   -> KIND ke tRes KStar); intros; try (first [inverts H | inverts H0]); eauto.

 Case "XApp".
 eapply IHx1 in H4. inverts H4. auto.

 Case "XTup".
 inverts H0. inverts H3.
 apply KINProd; auto.
 inverts keep H0.
 inverts keep H5.
 apply KINProd. apply Forall_cons.
 eapply H1; eauto.
 rewrite Forall_forall; intros.
 rename x0 into t.
 rename l0 into xs.
 nforall.
 pose proof (Forall2_exists_right_in _ _ _ _ H H7) as [x' [INx' TYx']].
 spec H2 INx' TYx'; auto.

 Case "XProj".
 spec IHx H4.
 inverts_kind.
 nforall.
 pose proof (get_in _ _ _ _ H6).
 spec H1 H; auto.

 Case "XNApp".
 inverts keep H0.
 inverts keep H6.
 spec IHx H4. inverts_kind; auto.
 inverts keep H0.
 spec IHx H6.
 inverts_kind; auto.

 Case "XCon".
 inverts H0; auto.
 inverts H0; auto.

 Case "XMatch".
 inverts keep H0; nope.
 inverts keep H0.
 repeat nforall.
 spec H5 x0.
 assert (In x0 (l0 :> x0)) by auto.
 spec H5 H. spec H1 H5; auto.

 Case "XChoice".
 inverts H0; auto.
 inverts H0; auto.
Qed.


(* A well typed expression is well formed. *)
Theorem type_wfX
  : forall ds ke te x t,
    TYPE ds ke te x t
    -> wfX ke te x.
Proof.
  intros. gen ds ke te t.
  induction x using exp_mutind
    with (PA := fun a => forall ds ke te tBuilds tRes,
                    TYPEA ds ke te a tBuilds tRes
                    -> wfA ke te a); intros; simpl.

  Case "XVar".
  inverts H. eauto.

  Case "XApp".
  inverts H.
  apply IHx1 in H4.
  apply IHx2 in H6.
  auto.

  Case "XTup".
  inverts keep H0.
  nforall.
  constructor.
  rewrite Forall_forall; intros.
  pose proof (Forall2_exists_left_in _ _ _ _ H1 H4) as [y [INy TYx]].
  eapply H; eauto.

  Case "XProj".
  inverts keep H.
  constructor. eapply IHx.
  eauto.

  Case "XNFun".
  inverts keep H.
  constructor.
  apply Forall_forall; intros.
  nforall. spec H4 H0.
  eapply kind_wfT; eauto.
  spec IHx H6; auto.

  Case "XNApp".
  inverts keep H0.
  spec IHx H5.
  constructor; auto.
  rewrite Forall_forall; intros.
  repeat nforall.
  spec H H1.
  pose proof (Forall2_exists_left_in _ _ _ _ H1 H7) as [y [INy TYx]].
  eapply H; eauto.

  Case "XFix".
  inverts keep H.
  constructor.
  eapply kind_wfT; eauto.
  pose proof (type_kind _ _ _ _ _ H).
  inverts_kind. eapply kind_wfT; eauto.
  eapply IHx; eauto.

  Case "XCon".
  inverts keep H0.
  constructor.
  repeat nforall. intros.
  pose proof (Forall2_exists_left_in _ _ _ _ H1 H10) as [y [INy TYx]].
  eapply H; eauto.

  Case "XMatch".
  inverts keep H0.
  repeat nforall.
  constructor.
  eapply IHx; eauto.
  rewrite Forall_forall; intros.
  spec H H1. spec H4 H1. spec H H4; auto.

  Case "XChoice".
  inverts keep H0.
  constructor. eapply kind_wfT; eauto.
  repeat nforall. intros.
  pose proof (Forall2_exists_left_in _ _ _ _ H1 H11) as [y [INy TYx]].
  eapply H; eauto.

  Case "Alt".
  inverts keep H. econstructor; eauto.
Qed.
Hint Resolve type_wfX.


Lemma In_tl (A : Type)
  : forall x l,
    @In A x (tl l)
    -> @In A x l .
Proof.
  intros.
  destruct l. nope.
  simpl in *; auto.
Qed.


(********************************************************************)
(* Weakening the kind environment of a type judgement.
   We can insert a new kind into the kind environment of a type
   judgement, provided we lift existing references to kinds higher
   than this in the stack over the new one.

   References to existing elements of the kind environment may
   appear in the type environment, expression, as well as the
   resulting type -- so we must lift all of them.
 *)
Lemma type_kienv_insert
  : forall ix ds ke te x1 t1 k2,
    TYPE ds ke te x1 t1
 -> TYPE ds (insert ix k2 ke) (liftTE ix te) (liftTX ix x1) (liftTT ix t1).
Proof.
  intros. gen ix ds ke te t1 k2.
  induction x1 using exp_mutind
    with (PA := fun a => forall ix ds ke te tBuilds tRes k2,
                    TYPEA ds ke te a tBuilds tRes
                    -> TYPEA ds (insert ix k2 ke) (liftTE ix te) (liftTA ix a)
                            (liftTT ix tBuilds) (liftTT ix tRes));
    intros; invert_exp_type; simpl; eauto.

  Case "XVar".
  apply TYVar.
  apply get_map. auto.
  apply liftTT_insert. auto.

  Case "XApp".
  eapply TYApp.
  eapply IHx1_1 in H4. simpl in H4. eauto.
  eapply IHx1_2 in H6. eauto.

  Case "XTup".
  eapply TYTup; simpl; auto.
  apply (Forall2_map_left (TYPE ds (insert ix k2 ke) (liftTE ix te))).
  apply (Forall2_map_right (fun (x : exp) (y : ty) => TYPE ds (insert ix k2 ke) (liftTE ix te) (liftTX ix x) y)).
  apply (Forall2_impl_in  (TYPE ds ke te)); eauto.
  nforall. intros.
  eapply H; eauto.

  Case "XProj".
  eapply TYProj; simpl; eauto.
  spec IHx1 H4. simpl in *; eauto.

  Case "XNFun".
  eapply TYNFun; eauto.
  apply Forall_map.
  repeat nforall; intros.
  apply liftTT_insert; auto.
  spec IHx1 H6.
  unfold liftTE in *.
  rewrite <- map_app; eauto.

  Case "XNApp".
  apply TYNApp with (ts := map (liftTT ix) ts).
  assert (liftTT ix (TNFun ts t1) = (TNFun (map (liftTT ix) ts) (liftTT ix t1))) by auto.
  rewrite <- H0.
  apply IHx1; auto.

  apply (Forall2_map_left (TYPE ds (insert ix k2 ke) (liftTE ix te))).
  apply (Forall2_map_right (fun (x : exp) (y : ty) => TYPE ds (insert ix k2 ke) (liftTE ix te) (liftTX ix x) y)).
  apply (Forall2_impl_in  (TYPE ds ke te)); eauto.
  nforall. intros.
  eapply H; eauto.

  Case "XFix".
  eapply TYFix. apply liftTT_insert; auto.
  unfold liftTE in *.
  assert (liftTT ix (TFun t1 t2) = (TFun (liftTT ix t1) (liftTT ix t2))) by auto.
  rewrite <- H.
  repeat rewrite <- map_cons.
  apply IHx1; auto.

  Case "XCon".
  eapply TYCon; eauto.
  apply (Forall2_map_left (TYPE ds (insert ix k2 ke) (liftTE ix te))).
  apply (Forall2_impl_in  (TYPE ds ke te)); eauto.
  nforall; eauto.
  intros. spec H5 H1.
  assert (y = liftTT ix y).
  apply simpleLiftEq; auto.
  rewrite H6.
  nforall.
  apply H; auto.

  Case "XMatch".
  eapply TYMatch; eauto.
  assert (TCon tcPat = (liftTT ix (TCon tcPat))) by auto.
  rewrite H0.
  apply IHx1; auto.

  apply Forall_map.
  apply (Forall_impl_in (fun a => TYPEA ds ke te a (TCon tcPat) t1)); eauto.
  repeat nforall; intros.
  spec H H0. spec H H1. eauto.
  rewrite map_length; auto.

  (* norm. *) repeat nforall.
  intros. rename x into d.
  rewrite map_map. unfold Basics.compose.
  eapply map_exists_in.
  have (In d (map dcOfAlt aa)).
  assert (exists a, dcOfAlt a = d /\ In a aa).
  eapply map_in_exists. auto.
  shift a. rip.
  eapply dcOfAlt_liftTA.

  Case "XChoice".
  eapply TYChoice; eauto.
  assert (t1 = liftTT ix t1).
  nforall. apply get_in in H8.
  spec H5 H8.
  apply simpleLiftEq; auto.
  rewrite <- H0; auto.
  apply liftTT_insert; auto.

  apply (Forall2_map_left (TYPE ds (insert ix k2 ke) (liftTE ix te))).
  apply (Forall2_impl_in  (TYPE ds ke te)); eauto.
  nforall; eauto.
  intros. apply In_tl in H1. spec H5 H1.
  assert (y = liftTT ix y).
  apply simpleLiftEq; auto.
  rewrite H3.
  nforall.
  apply H; auto.

  Case "XAlt".
  eapply TYAlt; eauto.
  assert (map (liftTT ix) ts = ts).
  repeat nforall. rewrite <- map_id.
  apply map_ext_in; intros. symmetry.
  spec H6 H.
  apply (simpleLiftEq _ _ H6).
  rewrite H; auto.
  pose proof (simpleLiftMapEq _ ix H6).
  rewrite <- H; auto.

  rewrite Forall_forall; intros.
  repeat nforall.
  pose proof map_in_exists.
  apply H0 in H as [y [FY INY]].
  rewrite <- FY.
  apply liftTT_insert. apply H9; auto.

  unfold liftTE in *.
  rewrite <- map_app.
  apply IHx1; auto.
Qed.


Lemma type_kienv_weaken
  : forall ds ke te x1 t1 k2,
    TYPE ds ke te x1 t1
 -> TYPE ds (ke :> k2) (liftTE 0 te) (liftTX 0 x1) (liftTT 0 t1).
Proof.
 intros.
 assert (ke :> k2 = insert 0 k2 ke).
  destruct ke; auto. rewrite H0.
  apply type_kienv_insert. auto.
Qed.


(********************************************************************)
(* Weakening the type environment of a type judgement.
   We can insert a new type into the type environment of a type
   judgement, provided we lift existing references to types higher
   than this in the stack over the new one.
 *)
Lemma type_tyenv_insert
  : forall ds ke te ix x1 t1 t2,
    TYPE ds ke te x1 t1
    -> TYPE ds ke (insert ix t2 te) (liftXX 1 ix x1) t1.
Proof.
  intros. gen ds ix ke te t1 t2.
  induction x1 using exp_mutind
    with (PA := fun a => forall ds ke te ix tBuilds tRes t2,
                    TYPEA ds ke te a tBuilds tRes
                    -> TYPEA ds ke (insert ix t2 te) (liftXA 1 ix a) tBuilds tRes);
    intros; invert_exp_type; simpl; eauto.

  Case "XVar".
  lift_cases; intros; auto.

  Case "XTup".
  eapply TYTup; eauto.
  apply (Forall2_map_left (TYPE ds ke (insert ix t2 te))).
  apply (Forall2_impl_in  (TYPE ds ke te)); eauto.
  nforall. eauto.

  Case "XNFun".
  eapply TYNFun; eauto.
  rewrite insert_app. auto.

  Case "XNApp".
  eapply TYNApp; eauto.
  apply (Forall2_map_left (TYPE ds ke (insert ix t2 te))).
  apply (Forall2_impl_in  (TYPE ds ke te)); eauto.
  nforall. eauto.

  Case "XFix".
  eapply TYFix; eauto.
  repeat rewrite insert_rewind.
  apply IHx1; auto.

  Case "XCon".
  eapply TYCon; eauto.
  apply (Forall2_map_left (TYPE ds ke (insert ix t2 te))).
  apply (Forall2_impl_in  (TYPE ds ke te)); eauto.
  repeat nforall. eauto.

  Case "XMatch".
  eapply TYMatch; eauto.
  apply Forall_map.
  apply (Forall_impl_in (fun a => TYPEA ds ke te a (TCon tcPat) t1)); eauto.
  repeat nforall. burn.

  rewrite map_length; auto.

  (* norm. *) repeat nforall.
  intros. rename x into d.
  rewrite map_map. unfold Basics.compose.
  eapply map_exists_in.
  have (In d (map dcOfAlt aa)).
  assert (exists a, dcOfAlt a = d /\ In a aa).
  eapply map_in_exists. auto.
  shift a. rip.
  eapply dcOfAlt_liftXA.

  Case "XChoice".
  eapply TYChoice; eauto.
  apply (Forall2_map_left (TYPE ds ke (insert ix t2 te))).
  apply (Forall2_impl_in  (TYPE ds ke te)); eauto.
  repeat nforall. eauto.

  Case "XAlt".
  eapply TYAlt; eauto.
  rewrite insert_app. auto.
Qed.


Lemma type_tyenv_weaken
  : forall ds ke te x1 t1 t2,
    TYPE ds ke te x1 t1
    -> TYPE ds ke (te :> t2) (liftXX 1 0 x1) t1.
Proof.
  intros.
  assert (te :> t2 = insert 0 t2 te).
  destruct te; auto. rewrite H0.
  apply type_tyenv_insert. auto.
Qed.

Lemma type_tyenv_weaken_append
  : forall ds ke te x1 t1 te',
    TYPE ds ke te x1 t1
    -> TYPE ds ke (te >< te') (liftXX (length te') 0 x1) t1.
Proof.
 intros.
 induction te'; simpl.
 rewrite liftXX_zero; auto.
 rewrite <- nat_plus_one.
 rrwrite (length te' + 1 = 1 + length te').
 rewrite <- liftXX_plus.
 eapply type_tyenv_weaken. auto.
Qed.
