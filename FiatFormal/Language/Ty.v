
Require Export FiatFormal.Language.Ki.

(* PMK: what I learned from writing ty_ind by hand: *)
(* No mutual induction needed in proof of ty_ind.
*)
Unset Elimination Schemes.
(* Type Expressions *)
Inductive ty  : Type :=
 | TCon    : nat -> ty             (* Data type constructor. *)
 | TVar    : nat -> ty             (* deBruijn index. *)
 (* | TForall : ty  -> ty           (* Type variable binding. *) *)
 | TFun    : ty  -> ty -> ty     (* Function type constructor. *)

 | TExists : ty -> ty
 | TNProd   : list ty -> ty
 | TNFun    : list ty -> ty -> ty.

Theorem ty_ind :
  forall
    (PT : ty -> Prop),
    (forall n, PT (TCon n))
    -> (forall n, PT (TVar n))
    -> (forall t1 t2, PT t1 -> PT t2 -> PT (TFun t1 t2))
    -> (forall t, PT t -> PT (TExists t))
    -> (forall ts, Forall PT ts -> PT (TNProd ts))
    -> (forall ts tRes, Forall PT ts -> PT tRes -> PT (TNFun ts tRes))
    (* -> (Forall PT nil) *)
    (* -> (forall t ts, PT t -> Forall PT ts -> Forall PT (ts :> t)) *)
    -> forall t, PT t.
Proof.
  intros PT.
  intros tcon tvar tfun texists tnprod tnfun.
  (* refine (fix IHT t : PT t := _). *)
  refine (fix IHT t : PT t := _).
          (* with IHL l : Forall PT l := _ *)
          (*                               for IHT). *)
  intros.
  case t; intros.
  Case "TCon".
  apply tcon.
  Case "TVar".
  apply tvar.
  Case "TFun".
  Guarded.
  apply tfun. apply IHT. apply IHT. Guarded.
  Case "TExists".
  apply texists. apply IHT. Guarded.
  Case "TNProd".
  apply tnprod. induction l. apply Forall_nil. apply Forall_cons. apply IHT. Guarded. apply IHl. Guarded.

(* remember l. induction l. apply IHL. Guarded. apply IHL. Guarded. *)
  Case "TNFun".
  apply tnfun.  induction l. apply Forall_nil. apply Forall_cons. apply IHT. Guarded. apply IHl. Guarded.

(* remember l. induction l. apply IHL. apply IHL. Guarded. *)
  apply IHT.
  Guarded.
  (* Case "LIST". *)
  (* induction l; intros. *)
  (* apply Forall_nil. Guarded. *)
  (* apply Forall_cons. Focus 2. apply IHl. Guarded. *)
  (* apply IHT. Guarded. *)
  (* apply IHL. *)
Qed.
(*   remember l. *)
(*   case l0; intros. *)
(*   apply IHL. Guarded. *)
(*   remember l. induction l. apply IHL. apply IHL. *)
(* Qed. *)
Unset Elimination Schemes.

(********************************************************************)
(* Mutual induction principle for expressions.
   As expressions are indirectly mutually recursive with lists,
   Coq's Combined scheme command won't make us a strong enough
   induction principle, so we need to write it out by hand. *)

(* Theorem exp_mutind *)
(*  : forall *)
(*     (PX : exp -> Prop) *)
(*     (PA : alt -> Prop) *)
(*  ,  (forall n,                                PX (XVar n)) *)
(*  -> (forall t  x1,   PX x1                 -> PX (XLam t x1)) *)
(*  -> (forall x1 x2,   PX x1 -> PX x2        -> PX (XApp x1 x2)) *)
(*  -> (forall dc xs,            Forall PX xs -> PX (XCon dc xs)) *)
(*  -> (forall x  aa,   PX x  -> Forall PA aa -> PX (XCase x aa)) *)
(*  -> (forall dc ts x, PX x                  -> PA (AAlt dc ts x)) *)
(*  ->  forall x, PX x. *)
(* Proof. *)
(*  intros PX PA. *)
(*  intros var lam app con case alt. *)
(*  refine (fix  IHX x : PX x := _ *)
(*          with IHA a : PA a := _ *)
(*          for  IHX). *)

(*  (* expressions *) *)
(*  case x; intros. *)

(*  Case "XVar". *)
(*   apply var. *)

(*  Case "XLam". *)
(*   apply lam. *)
(*    apply IHX. *)

(*  Case "XApp". *)
(*   apply app. *)
(*    apply IHX. *)
(*    apply IHX. *)

(*  Case "XCon". *)
(*   apply con. *)
(*    induction l; intuition. *)

(*  Case "XCase". *)
(*   apply case. *)
(*    apply IHX. *)
(*    induction l; intuition. *)

(*  (* alternatives *) *)
(*  case a; intros. *)

(*  Case "XAlt". *)
(*   apply alt. *)
(*    apply IHX. *)
(* Qed. *)

Hint Constructors ty.


(********************************************************************)
Inductive wfT : kienv -> ty -> Prop :=
| WfT_TCon : forall ke n,
    wfT ke (TCon n)
| WfT_TVar : forall ke i k,
    get i ke = Some k
    -> wfT ke (TVar i)
| WfT_TFun : forall ke t1 t2,
    wfT ke t1
    -> wfT ke t2
    -> wfT ke (TFun t1 t2)
| WfT_TNProd : forall ke ts,
    Forall (wfT ke) ts
    -> wfT ke (TNProd ts)
| WfT_TNFun : forall ke ts tRes,
    Forall (wfT ke) ts
    -> wfT ke tRes
    -> wfT ke (TNFun ts tRes)
| WfT_TExists : forall ke t,
    wfT (ke :> KStar) t
    -> wfT ke (TExists t).

Hint Constructors wfT.

(* Similar to wfX, wfT has been made into an Inductive datatype above *)
(* Well formed types are closed under the given kind environment *)
(* Fixpoint wfT (ke: kienv) (tt: ty) : Prop := *)
(*  match tt with *)
(*  | TCon _     => True *)
(*  | TVar i     => exists k, get i ke = Some k *)
(*  (* | TForall t  => wfT (ke :> KStar) t *) *)
(*  | TFun t1 t2 => wfT ke t1 /\ wfT ke t2 *)

(*  (* | TNProd ts      => True *) *)
(*  (* | TNFun  ts tRes => Forall (wfT ke) ts /\ wfT ke tRes *) *)
(*  (* | TNFun ts tRes => wfT ke tRes *) *)
(*  | TExists t     => wfT (ke :> KStar) t *)
(*  end. *)
(* Hint Unfold wfT. *)


(* A closed type is well formed under an empty kind environment. *)
Definition closedT (tt: ty) : Prop
 := wfT nil tt.
Hint Unfold closedT.


(********************************************************************)
(* Lifting of type indices in types.
   When we push new elements on the environment stack, we need
   to lift referenes to existing elements across the new ones. *)
Fixpoint liftTT (d: nat) (tt: ty) : ty :=
  match tt with
  | TCon _     => tt

  | TVar ix
    => if le_gt_dec d ix
      then TVar (S ix)
      else tt

  (* |  TForall t *)
  (*    => TForall (liftTT (S d) t) *)

  | TFun t1 t2
    => TFun    (liftTT d t1) (liftTT d t2)

  | TExists t
    => TExists (liftTT (S d) t)

  | TNProd ts
    => TNProd (map (liftTT d) ts)

  | TNFun ts tRes
    => TNFun (map (liftTT d) ts) (liftTT d tRes)
  end.
Hint Unfold liftTT.


(* Tactic to help deal with lifting functions. *)
Ltac lift_cases
 := match goal with
     |  [ |- context [le_gt_dec ?n ?n'] ]
     => case (le_gt_dec n n')
    end.


(********************************************************************)
(* Substitution for the outer-most binder in a type. *)
Fixpoint substTT (d: nat) (u: ty) (tt: ty) : ty
 := match tt with
    | TCon _
      => tt

    | TVar ix
      => match nat_compare ix d with
        | Eq => u
        | Gt => TVar (ix - 1)
        | _  => TVar  ix
        end

    (* |  TForall t *)
    (* => TForall (substTT (S d) (liftTT 0 u) t) *)

    | TFun t1 t2
      => TFun (substTT d u t1) (substTT d u t2)

    | TExists t
      => TExists (substTT (S d) (liftTT 0 u) t)

    | TNProd ts
      => TNProd (map (substTT d u) ts)

    | TNFun ts tRes
      => TNFun (map (substTT d u) ts) (substTT d u tRes)
  end.


(********************************************************************)
(* PMK: TODO -- now, types can contain lists, believe we need to *)
(* provide custom induction scheme or use one generated by Coq's Scheme.  *)
(* Changing the order of lifting. *)
Lemma liftTT_liftTT
 :  forall n n' t
 ,  liftTT n              (liftTT (n + n') t)
 =  liftTT (1 + (n + n')) (liftTT n t).
Proof.
 intros. gen n n'.
 induction t; intros; auto.

 Case "TVar".
  simpl.
  repeat (unfold liftTT; lift_cases; intros); burn.

 (* Case "TForall". *)
 (*  simpl. *)
 (*  assert (S (n + n') = (S n) + n'). omega. rewrite H. *)
 (*  rewrite IHt. auto. *)

 Case "TFun".
 simpl. apply f_equal2; auto.

 Case "TExists".
 simpl.
 assert (S (n + n') = (S n) + n'). omega. rewrite H.
 rewrite IHt. auto.

 Case "TNProd".
 simpl. apply f_equal.
 repeat (rewrite map_map).
 assert (S (n + n') = (S n) + n'). omega. rewrite H0.
 apply map_ext_in; intros.
 apply (Forall_in _ _ _ H H1).

 Case "TNFun".
 simpl. apply f_equal2; auto.
 repeat (rewrite map_map).
 assert (S (n + n') = (S n) + n'). omega. rewrite H0.
 apply map_ext_in; intros.
 apply (Forall_in _ _ _ H H1).
Qed.


(* Lifting then substituting at the same index doesn't do anything.

   When we lift indices in a type that are greater or equal to some
   depth d, there will be no indices of value d in the result. The
   lifting process increments indices greater than 'd', but then the
   substitution process decrements them again, so we get back to
   the type we started with.
 *)
Lemma substTT_liftTT
 :  forall d t1 t2
 ,  substTT d t2 (liftTT d t1) = t1.
Proof.
 intros. gen d t2.
 induction t1; intros; eauto.

 Case "TVar".
  simpl; lift_cases; unfold substTT;
   fbreak_nat_compare; intros;
   burn.

 (* Case "TForall". *)
 (*  simpl. *)
 (*  rewrite IHt1. auto. *)

 Case "TFun".
  simpl.
  rewrite IHt1_1.
  rewrite IHt1_2. auto.

  Case "TExists".
  simpl.
  rewrite IHt1. auto.

  Case "TNProd".
  simpl. apply f_equal.
  repeat rewrite (map_map).
  rewrite <- map_id.
  apply map_ext_in; intros.
  apply (Forall_in _ _ _ H H0).

  Case "TNFun".
  simpl. apply f_equal2.
  repeat rewrite (map_map).
  rewrite <- map_id.
  apply map_ext_in; intros.
  apply (Forall_in _ _ _ H H0).
  apply IHt1.
Qed.


(* Lifting after substitution *)
Lemma liftTT_substTT
 :  forall n n' t1 t2
 ,  liftTT n (substTT (n + n') t2 t1)
 =  substTT (1 + n + n') (liftTT n t2) (liftTT n t1).
Proof.
 intros. gen n n' t2.
 induction t1; intros; eauto.

 Case "TVar".
  repeat (simpl; fbreak_nat_compare;
          try lift_cases; try intros);
   burn.

 (* Case "TForall". *)
 (*  simpl. *)
 (*  rewrite (IHt1 (S n) n'). simpl. *)
 (*  rewrite (liftTT_liftTT 0 n). auto. *)

 Case "TFun".
  simpl.
  rewrite IHt1_1. auto.
  rewrite IHt1_2. auto.

  Case "TExists".
  simpl.
  rewrite (IHt1 (S n) n'). simpl.
  rewrite (liftTT_liftTT 0 n). auto.

  Case "TNProd".
  simpl. apply f_equal.
  repeat rewrite (map_map).
  apply map_ext_in; intros.
  apply (Forall_in _ _ _ H H0).

  Case "TNFun".
  simpl. apply f_equal2.
  repeat rewrite (map_map).
  apply map_ext_in; intros.
  apply (Forall_in _ _ _ H H0).
  apply IHt1.
Qed.


(* Lifting after substitution, another way. *)
Lemma liftTT_substTT'
 :  forall n n' t1 t2
 ,  liftTT (n + n') (substTT n t2 t1)
 =  substTT n (liftTT (n + n') t2) (liftTT (1 + n + n') t1).
Proof.
 intros. gen n n' t2.
 induction t1; intros; auto.

 Case "TVar".
  repeat ( unfold liftTT; unfold substTT; fold liftTT; fold substTT
         ; try lift_cases; try fbreak_nat_compare
         ; intros); burn.

 (* Case "TForall". *)
 (*  simpl. f_equal. *)
 (*  rewrite (IHt1 (S n) n'). f_equal. *)
 (*   simpl. rewrite (liftTT_liftTT 0 (n + n')). auto. *)

 Case "TFun".
  simpl. f_equal.
   apply IHt1_1.
   apply IHt1_2.

   Case "TExists".
   simpl. f_equal.
   rewrite (IHt1 (S n) n'). f_equal.
   simpl. rewrite (liftTT_liftTT 0 (n + n')). auto.

   Case "TNProd".
   simpl. apply f_equal.
   repeat rewrite (map_map).
   apply map_ext_in; intros.
   apply (Forall_in _ _ _ H H0).

   Case "TNFun".
   simpl. apply f_equal2.
   repeat rewrite (map_map).
   apply map_ext_in; intros.
   apply (Forall_in _ _ _ H H0).
   apply IHt1.
Qed.


(* Commuting substitutions. *)
Lemma substTT_substTT
 :  forall n m t1 t2 t3
 ,  substTT (n + m) t3 (substTT n t2 t1)
 =  substTT n (substTT (n + m) t3 t2)
              (substTT (1 + n + m) (liftTT n t3) t1).
Proof.
 intros. gen n m t2 t3.
 induction t1; intros; auto.

 Case "TVar".
  repeat (simpl; fbreak_nat_compare); try burn.
  rewrite substTT_liftTT. auto.

 (* Case "TForall". *)
 (*  simpl. f_equal. *)
 (*  rewrite (IHt1 (S n) m). f_equal. *)
 (*   simpl. rewrite (liftTT_substTT 0 (n + m)). auto. *)
 (*   simpl. rewrite (liftTT_liftTT 0 n). auto. *)

 Case "TFun".
  simpl. f_equal.
   apply IHt1_1.
   apply IHt1_2.

   Case "TExists".
   simpl. f_equal.
   rewrite (IHt1 (S n) m). f_equal.
   simpl. rewrite (liftTT_substTT 0 (n + m)). auto.
   simpl. rewrite (liftTT_liftTT 0 n). auto.

   Case "TNProd".
   simpl. apply f_equal.
   repeat rewrite (map_map).
   apply map_ext_in; intros.
   apply (Forall_in _ _ _ H H0).

   Case "TNFun".
   simpl. apply f_equal2.
   repeat rewrite (map_map).
   apply map_ext_in; intros.
   apply (Forall_in _ _ _ H H0).
   apply IHt1.
Qed.
