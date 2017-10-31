
Require Export FiatFormal.Language.Ki.


(* Algebraic Data Type Constructors *)
Inductive tycon : Type :=
 | TyConData   : nat -> tycon.
Hint Constructors tycon.

Fixpoint tycon_beq t1 t2 :=
  match t1, t2 with
  | TyConData n1, TyConData n2 => beq_nat n1 n2
  end.

Inductive propcon : Type :=
| PropCon : nat -> propcon.
Hint Constructors propcon.

Fixpoint propcon_beq t1 t2 :=
  match t1, t2 with
  | PropCon n1, PropCon n2 => beq_nat n1 n2
  end.


Unset Elimination Schemes.
(* Type Expressions *)
Inductive ty  : Type :=
 | TCon    : tycon -> ty         (* Data type constructor. *)
 | TVar    : nat -> ty             (* deBruijn index. *)
 | TFun    : ty  -> ty -> ty      (* Function type constructor. *)
 | TExists : ty -> ty
 | TNProd   : list ty -> ty
 | TNFun    : list ty -> ty -> ty
 | TProp    : propcon -> ty.

Hint Constructors ty.

Theorem ty_ind :
  forall
    (PT : ty -> Prop),
    (forall tc, PT (TCon tc))
    -> (forall n, PT (TVar n))
    -> (forall t1 t2, PT t1 -> PT t2 -> PT (TFun t1 t2))
    -> (forall t, PT t -> PT (TExists t))
    -> (forall ts, Forall PT ts -> PT (TNProd ts))
    -> (forall ts tRes, Forall PT ts -> PT tRes -> PT (TNFun ts tRes))
    -> (forall pc, PT (TProp pc))
    -> forall t, PT t.
Proof.
  intros PT.
  intros tcon tvar tfun texists tnprod tnfun pcon.
  refine (fix IHT t : PT t := _).
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
  Case "TNFun".
  apply tnfun.  induction l. apply Forall_nil. apply Forall_cons. apply IHT. Guarded. apply IHl. Guarded.
  apply IHT.
  Guarded.
  Case "TProp".
  apply pcon.
  Guarded.
Qed.
Unset Elimination Schemes.

(* Data Constructors *)
Inductive datacon : Type :=
 | DataCon    : nat -> datacon.
Hint Constructors datacon.

Fixpoint datacon_beq t1 t2 :=
  match t1, t2 with
  | DataCon n1, DataCon n2 => beq_nat n1 n2
  end.

Inductive proofcon : Type :=
| ProofCon : nat -> proofcon.
Hint Constructors proofcon.

Fixpoint proofcon_beq t1 t2 :=
  match t1, t2 with
  | ProofCon n1, ProofCon n2 => beq_nat n1 n2
  end.

(* Definitions.
   Carries meta information about type and data constructors. *)
Inductive def  : Type :=
(* Definition of a data type constructor *)
| DefDataType
  : tycon          (* Name of data type constructor *)
    -> list datacon (* Data constructors that belong to this type *)
    -> def

(* Definition of a data constructor *)
| DefData
  : datacon     (* Name of data constructor *)
    -> list ty   (* Types of arguments *)
    -> ty        (* Type  of constructed data *)
    -> def

(* Definition of a proposition type constructor *)
| DefPropType
  : propcon         (* name of proposition type constructor *)
    -> list proofcon (* proof constructors that build proof of this proposition *)
    -> def

(* Definition of a proof constructor *)
| DefProof
  : proofcon        (* name of proof constructor *)
    -> list ty       (* types of arguments *)
    -> ty            (* type of constructed proof *)
    -> def.
Hint Constructors def.

(* Definition environment.
   Holds the definitions of all current type and data constructors. *)
Definition defs  := list def.


(* Lookup the def of a given type constructor.
   Returns None if it's not in the list. *)
Fixpoint getTypeDef (tc: tycon) (ds: defs) : option def :=
 match ds with
 | ds' :> DefDataType tc' _ as d
 => if tycon_beq tc tc'
     then  Some d
     else  getTypeDef tc ds'

 | ds' :> _ => getTypeDef tc ds'
 | Empty    => None
 end.

(* Lookup the def of a given data constructor.
   Returns None if it's not in the list. *)
Fixpoint getDataDef (dc: datacon) (ds: defs) : option def :=
 match ds with
 | ds' :> DefData dc' _ _ as d
 => if datacon_beq dc dc'
     then  Some d
     else  getDataDef dc ds'

 | ds' :> _ => getDataDef dc ds'
 | Empty    => None
 end.

(* Lookup the def of a given proposition type constructor.
   Returns None if it's not in the list. *)
Fixpoint getPropDef (pc: propcon) (ds: defs) : option def :=
 match ds with
 | ds' :> DefPropType pc' _ as d
 => if propcon_beq pc pc'
     then  Some d
     else  getPropDef pc ds'

 | ds' :> _ => getPropDef pc ds'
 | Empty    => None
 end.

(* Lookup the def of a given proof constructor.
   Returns None if it's not in the list. *)
Fixpoint getProofDef (pc: proofcon) (ds: defs) : option def :=
 match ds with
 | ds' :> DefProof pc' _ _ as d
 => if proofcon_beq pc pc'
     then  Some d
     else  getProofDef pc ds'

 | ds' :> _ => getProofDef pc ds'
 | Empty    => None
 end.


(* Boolean equality for data constructors. *)
Lemma datacon_beq_eq
 :  forall dc dc'
 ,  true = datacon_beq dc dc'
 -> dc = dc'.
Proof.
 intros.
 destruct dc.
 destruct dc'.
 simpl in H.
 apply beq_nat_eq in H.
 auto.
Qed.

(* Boolean negation for data constructors. *)
Lemma datacon_beq_false
 :  forall dc
 ,  false = datacon_beq dc dc
 -> False.
Proof.
 intro.
 destruct dc.
 simpl.
 intros.
  induction n.
  simpl in H. false.
  simpl in H. auto.
Qed.


(********************************************************************)
Inductive simpleType : ty -> Prop :=
| Simp_TCon : forall tc,
    simpleType (TCon tc)
| Simp_TFun : forall t1 t2,
    simpleType t1
    -> simpleType t2
    -> simpleType (TFun t1 t2)
| Simp_TNProd : forall ts,
    Forall (simpleType) ts
    -> simpleType (TNProd ts)
| Simp_TNFun : forall ts tRes,
    simpleType tRes
    -> Forall (simpleType) ts
    -> simpleType (TNFun ts tRes)
| Simp_TProp : forall pc,
    simpleType (TProp pc).
Hint Constructors simpleType.

Inductive wfT : kienv -> ty -> Prop :=
| WfT_TCon : forall ke tc,
    wfT ke (TCon tc)
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
    -> wfT ke (TExists t)
| WfT_TProp : forall ke pc,
    wfT ke (TProp pc)

with wfDef : kienv -> def -> Prop := (* unused! *)
     | WfD : forall ts tRes dc ke,
         wfT ke tRes
         -> Forall (wfT ke) ts
         -> wfDef ke (DefData dc ts tRes).

Hint Constructors wfDef.
Hint Constructors wfT.


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

  | TFun t1 t2
    => TFun    (liftTT d t1) (liftTT d t2)

  | TExists t
    => TExists (liftTT (S d) t)

  | TNProd ts
    => TNProd (map (liftTT d) ts)

  | TNFun ts tRes
    => TNFun (map (liftTT d) ts) (liftTT d tRes)

  | TProp _ => tt
  end.
Hint Unfold liftTT.

Lemma simpleLiftEq :
  forall t d,
    simpleType t
    -> t = liftTT d t.
Proof.
  intros.
  induction t; try inverts H; intros; auto.
  Case "TFun".
  spec IHt1 H2.
  spec IHt2 H3. simpl.
  rewrite <- IHt1.
  rewrite <- IHt2. auto.
  Case "TNProd". (* may be cleaner, shorter way *)
  simpl. f_equal.
  pose proof (Forall_mp _ _ _ H0 H2).
  repeat nforall.
  apply Forall2_eq.
  apply Forall2_map_right.
  apply Forall2_impl_in with (R1:=eq).
  intros; subst.
  apply H; auto.
  induction ts; eauto.
  apply Forall2_cons; auto.
  Case "TNFun". (* may be cleaner, shorter way *)
  simpl. f_equal; auto.
  pose proof (Forall_mp _ _ _ H0 H4).
  repeat nforall.
  apply Forall2_eq.
  apply Forall2_map_right.
  apply Forall2_impl_in with (R1:=eq).
  intros; subst.
  apply H; auto.
  induction ts; eauto.
  apply Forall2_cons; auto.
Qed.
Hint Rewrite simpleLiftEq.

Lemma simpleLiftMapEq :
  forall ts d,
    Forall simpleType ts
    -> ts = map (liftTT d) ts.
Proof.
  intros. induction ts; try inverts H; intros; auto.
  spec IHts H3.
  simpl. rewrite <- IHts.
  assert (a = liftTT d a). apply simpleLiftEq; auto.
  rewrite <- H; auto.
Qed.

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

    | TFun t1 t2
      => TFun (substTT d u t1) (substTT d u t2)

    | TExists t
      => TExists (substTT (S d) (liftTT 0 u) t)

    | TNProd ts
      => TNProd (map (substTT d u) ts)

    | TNFun ts tRes
      => TNFun (map (substTT d u) ts) (substTT d u tRes)

    | TProp _
      => tt
  end.

Lemma simpleSubstEq :
  forall t1 t2 d,
    simpleType t1
    -> t1 = substTT d t2 t1.
Proof.
  intros.
  induction t1; try inverts H; intros; simpl; auto.
  Case "TFun".
  spec IHt1_1 H2.
  spec IHt1_2 H3. simpl.
  rewrite <- IHt1_1.
  rewrite <- IHt1_2. auto.
  Case "TNProd".
  f_equal.
  pose proof (Forall_mp _ _ _ H0 H2).
  repeat nforall.
  apply Forall2_eq.
  apply Forall2_map_right.
  apply Forall2_impl_in with (R1:=eq).
  intros; subst.
  apply H; auto.
  induction ts; eauto.
  apply Forall2_cons; auto.
  Case "TNFun". (* may be cleaner, shorter way *)
  simpl. f_equal; auto.
  pose proof (Forall_mp _ _ _ H0 H4).
  repeat nforall.
  apply Forall2_eq.
  apply Forall2_map_right.
  apply Forall2_impl_in with (R1:=eq).
  intros; subst.
  apply H; auto.
  induction ts; eauto.
  apply Forall2_cons; auto.
Qed.

Lemma simpleSubstMapEq :
  forall ts t2 d,
    Forall simpleType ts
    -> ts = map (substTT d t2) ts.
Proof.
  intros. induction ts; try inverts H; intros; simpl; auto.
  spec IHts H3.
  simpl. rewrite <- IHts.
  assert (a = substTT d t2 a). apply simpleSubstEq; auto.
  rewrite <- H; auto.
Qed.

(********************************************************************)
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
