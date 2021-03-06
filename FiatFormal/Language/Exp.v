
Require Export FiatFormal.Language.TyEnv.
Require Export FiatFormal.Language.Ty.
Require Export FiatFormal.Language.Ki.


(* Expressions *)
Inductive exp : Type :=
 | XVar  : nat -> exp               (* deBruijn indices *)
 | XApp  : exp -> exp -> exp       (* Value application *)
 | XTup   : list exp -> exp       (* Arity n tuples *)
 | XProj  : nat -> exp -> exp        (* Projection *)
 | XNFun  : list ty -> exp -> exp  (* Arity n functions *)
 | XNApp  : exp -> list exp -> exp (* Arity n application *)
 | XFix   : ty -> ty -> exp -> exp  (* Fixpoint *)
 (* Data Types *)
 | XCon   : datacon -> list exp -> exp       (* Data constructor *)
 | XMatch : exp     -> list alt -> exp       (* Match statement *)
 | XChoice : ty -> propcon -> list exp -> exp (* Non-deterministic choice operator *)

 (* Alternatives *)
with alt     : Type :=
 | AAlt   : datacon -> list ty  -> exp -> alt (* Branches of a match statement *).

Hint Constructors alt.
Hint Constructors exp.


(* Get the data constructor of an alternative. *)
Fixpoint dcOfAlt (aa: alt) : datacon :=
 match aa with
 | AAlt dc _ _ => dc
 end.
Hint Unfold dcOfAlt.


(* Get the alternative body that matches a given constructor. *)
Fixpoint getAlt (dc: datacon) (alts: list alt) {struct alts}
                : option alt :=
 match alts with
 |  nil  => None

 |  AAlt dc' tsArgs x :: alts'
 => if datacon_beq dc dc'
     then Some (AAlt dc' tsArgs x)
     else getAlt dc alts'
 end.


(* If we get a single alternative from a list,  *)
(*    then that alternative was in the list. *)
Lemma getAlt_in
 :  forall dc alt alts
 ,  getAlt dc alts = Some alt
 -> In alt alts.
Proof.
 intros.
 induction alts.
  false.
  destruct a as [dc' tsArgs x].
  simpl in H.
  breaka (datacon_beq dc dc').
   inverts H.
   apply datacon_beq_eq in HeqX; auto.
Qed.


(* Given a data constructor, if one of the alternatives in a  *)
(*    list matches that data constructor then we can get the other *)
(*    information about the alternative from the list. *)
Lemma getAlt_exists
 :  forall d alts
 ,  In d (map dcOfAlt alts)
 -> (exists tsArgs x, getAlt d alts = Some (AAlt d tsArgs x)).
Proof.
 intros.
 induction alts.
  simpl in H. false.
  simpl in H. inverts H.
   destruct a. simpl.
   breaka (datacon_beq d d).
    exists l. exists e. auto.
    apply datacon_beq_false in HeqX. false.
   lets D: IHalts H0.
   destruct a. simpl.
    breaka (datacon_beq d d0).
     apply datacon_beq_eq in HeqX. subst. auto.
     exists l. exists e. auto.
Qed.


(********************************************************************)
(* Mutual induction principle for expressions.
   As expressions are indirectly mutually recursive with lists,
   Coq's Combined scheme command won't make us a strong enough
   induction principle, so we need to write it out by hand. *)

Theorem exp_mutind
 : forall
    (PX : exp -> Prop)
    (PA : alt -> Prop)
 ,  (forall n,                                PX (XVar n))
 -> (forall x1 x2,   PX x1 -> PX x2        -> PX (XApp x1 x2))
 -> (forall xs,      Forall PX xs         -> PX (XTup xs))
 -> (forall n x,     PX x                 -> PX (XProj n x))
 -> (forall ts x,    PX x                 -> PX (XNFun ts x))
 -> (forall x xs,    PX x -> Forall PX xs  -> PX (XNApp x xs))
 -> (forall t1 t2 x, PX x                 -> PX (XFix t1 t2 x))
 -> (forall dc xs,   Forall PX xs         -> PX (XCon dc xs))
 -> (forall x  aa,   PX x  -> Forall PA aa -> PX (XMatch x aa))
 -> (forall t pc xs, Forall PX xs         -> PX (XChoice t pc xs))
 -> (forall dc ts x, PX x                 -> PA (AAlt dc ts x))
 ->  forall x, PX x.
Proof.
  intros PX PA.
  intros var app tup proj nfun napp ffix con mmatch proof alt.
  refine (fix  IHX x : PX x := _
            with IHA a : PA a := _
                                   for  IHX).
  (* expressions *)
  case x; intros.

  Case "XVar".
  apply var.

  Case "XApp".
  apply app.
  apply IHX.
  apply IHX.

  Case "XTup".
  apply tup.
  induction l; intuition.

  Case "XProj".
  apply proj.
  apply IHX.

  Case "XNFun".
  apply nfun.
  apply IHX.

  Case "XNApp".
  apply napp.
  apply IHX.
  induction l; intuition.

  Case "XFix".
  apply ffix.
  apply IHX.

  Case "XCon".
  apply con.
  induction l; intuition.

  Case "XMatch".
  apply mmatch.
  apply IHX.
  induction l; intuition.

  Case "XCon".
  apply proof.
  induction l; intuition.

  (* alternatives *)
  case a; intros.

  Case "XAlt".
  apply alt.
  apply IHX.
Qed.

(* This is used in our modified statement
   of progress for expressions. *)
Inductive hasChoiceX : exp -> Prop :=
| HcApp1  : forall x1 x2,
    hasChoiceX x1
    -> hasChoiceX (XApp x1 x2)
| HcApp2  : forall x1 x2,
    hasChoiceX x2
    -> hasChoiceX (XApp x1 x2)
| HcTup   : forall xs,
    Exists (hasChoiceX) xs
    -> hasChoiceX (XTup xs)
| HcProj  : forall x n,
    hasChoiceX x
    -> hasChoiceX (XProj n x)
| HcNFun  : forall ts x,
    hasChoiceX x
    -> hasChoiceX (XNFun ts x)
| HcNApp1  : forall x xs,
    hasChoiceX x
    -> hasChoiceX (XNApp x xs)
| HcNApp2  : forall x xs,
    Exists hasChoiceX xs
    -> hasChoiceX (XNApp x xs)
| HcFix    : forall t1 t2 x,
    hasChoiceX x
    -> hasChoiceX (XFix t1 t2 x)
| HcCon    : forall dc xs,
    Exists hasChoiceX xs
    -> hasChoiceX (XCon dc xs)
| HcMatch1  : forall x aa,
    hasChoiceX x
    -> hasChoiceX (XMatch x aa)
| HcMatch2  : forall x aa,
    Exists hasChoiceA aa
    -> hasChoiceX (XMatch x aa)
| HcChoice  : forall t pc xs,
    hasChoiceX (XChoice t pc xs)

with hasChoiceA : alt -> Prop :=
     | HcAlt : forall dc ts x,
         hasChoiceX x
         -> hasChoiceA (AAlt dc ts x).

Hint Constructors hasChoiceX.
Hint Constructors hasChoiceA.


Record method : Type :=
  mkMethod {
      arity : nat;
      dom : list ty;
      body : exp;
      cod : ty
    }.

Inductive adt : Type :=
| IADT : ty -> list method -> list ty -> adt.
Hint Constructors adt.

(* Programs *)
Inductive prog : Type :=
| PLET : adt -> prog -> prog
| PEXP : exp -> prog.
Hint Constructors prog.

Inductive hasChoiceP : prog -> Prop :=
| HcLet : forall ad p',
    hasChoiceP p'
    -> hasChoiceP (PLET ad p')
| HcExp : forall x,
    hasChoiceX x
    -> hasChoiceP (PEXP x).
Hint Constructors hasChoiceP.

(* Weak normal forms cannot be reduced further by
   call-by-value evaluation. *)
Inductive wnfX : exp -> Prop :=
 | Wnf_XVar
   : forall i
   , wnfX (XVar i)

 | Wnf_XTup
   : forall xs,
     Forall wnfX xs
     -> wnfX (XTup xs)

 | Wnf_XNFun
   : forall ts x,
     wnfX (XNFun ts x)

 | Wnf_XFix
   : forall t1 t2 x,
     wnfX (XFix t1 t2 x)

 | Wnf_XCon
   : forall dc xs,
     Forall wnfX xs
     -> wnfX (XCon dc xs).
Hint Constructors wnfX.

(* A well formed expression is closed under the given environments *)
Inductive wfX : kienv -> tyenv -> exp -> Prop :=
| WfX_XVar : forall ke te i t,
    get i te = Some t -> wfX ke te (XVar i)
| WfX_XApp : forall ke te x1 x2,
    wfX ke te x1 -> wfX ke te x2
    -> wfX ke te (XApp x1 x2)
| WfX_XTup : forall ke te xs,
    Forall (wfX ke te) xs
    -> wfX ke te (XTup xs)
| WfX_XProj : forall ke te n x,
    wfX ke te x
    -> wfX ke te (XProj n x)
| WfX_XNFun : forall ke te ts x,
    Forall (wfT ke) ts
    -> wfX ke (te >< ts) x
    -> wfX ke te (XNFun ts x)
| WfX_XNApp : forall ke te x xs,
    wfX ke te x
    -> Forall (wfX ke te) xs
    -> wfX ke te (XNApp x xs)
| WfX_XFix : forall ke te t1 t2 x,
    wfT ke t1
    -> wfT ke t2
    -> wfX ke (te :> (TFun t1 t2) :> t1) x
    -> wfX ke te (XFix t1 t2 x)
| WfX_XCon : forall ke te dc xs,
    Forall (wfX ke te) xs
    -> wfX ke te (XCon dc xs)
| WfX_XMatch : forall ke te x aa,
    wfX ke te x
    -> Forall (wfA ke te) aa
    -> wfX ke te (XMatch x aa)
| WfX_XChoice : forall ke te t pc xs,
    wfT ke t
    -> Forall (wfX ke te) xs
    -> wfX ke te (XChoice t pc xs)

with wfA : kienv -> tyenv -> alt -> Prop :=
     | WfA_AAlt : forall ke te dc ds ts x tsArgs tRes,
         getDataDef dc ds = Some (DefData dc tsArgs tRes)
         -> wfX ke (te >< tsArgs) x
         -> wfA ke te (AAlt dc ts x).

Hint Constructors wfA.
Hint Constructors wfX.


(* Closed expressions are well formed under empty environments *)
Definition closedX (xx: exp) : Prop
 := wfX nil nil xx.
Hint Unfold closedX.


(* Values are closed expressions that cannot be reduced further. *)
Inductive value : exp -> Prop :=
 | Value
   :  forall xx
   ,  wnfX xx -> closedX xx
   -> value xx.
Hint Constructors value.


(********************************************************************)
(* Lift type indices in expressions. *)
(* Note: only ever need lift of size 1 at a time *)
Fixpoint liftTX (d: nat) (xx: exp) : exp :=
  match xx with
  | XVar _     => xx

  | XApp x1 x2
    => XApp (liftTX d x1) (liftTX d x2)

  | XTup xs
    => XTup (map (liftTX d) xs)

  | XProj n x
    => XProj n (liftTX d x)

  | XNFun ts x
    => XNFun (map (liftTT d) ts) (liftTX d x)

  | XNApp x xs
    => XNApp (liftTX d x) (map (liftTX d) xs)

  | XFix t1 t2 x
    => XFix (liftTT d t1) (liftTT d t2) (liftTX d x)

  | XCon dc xs
    => XCon dc (map (liftTX d) xs)

  | XMatch x aa
    => XMatch (liftTX d x) (map (liftTA d) aa)

  | XChoice t pc xs
    => XChoice (liftTT d t) pc (map (liftTX d) xs)
  end

with liftTA (d: nat) (a : alt) : alt :=
       match a with
       | AAlt dc ts x => AAlt dc (map (liftTT d) ts) (liftTX d x)
       end.


(* Lift value indices in expressions. *)
Fixpoint liftXX (n: nat) (d: nat) (xx: exp) : exp :=
  match xx with
  | XVar ix
    => if le_gt_dec d ix
      then XVar (n + ix)
      else xx

  | XApp x1 x2
    => XApp (liftXX n d x1) (liftXX n d x2)

  | XTup xs
    => XTup (map (liftXX n d) xs)

  | XProj n' x
    => XProj n' (liftXX n d x)

  | XNFun ts x
    => XNFun ts (liftXX n (d + length ts) x)

  | XNApp x xs
    => XNApp (liftXX n d x) (map (liftXX n d) xs)

  (* Increase value depth when moving across value abstractions. *)
  | XFix t1 t2 x
    => XFix t1 t2 (liftXX n (S (S d)) x)

  | XCon dc xs
    => XCon dc (map (liftXX n d) xs)

  | XMatch x aa
    => XMatch (liftXX n d x) (map (liftXA n d) aa)

  | XChoice t pc xs
    => XChoice t pc (map (liftXX n d) xs)
  end

with liftXA (n: nat) (d: nat) (a: alt) : alt :=
       match a with
       | AAlt dc ts x => AAlt dc ts (liftXX n (d + length ts) x)
       end.


(********************************************************************)
(* Substitution of types in expressions. *)
Fixpoint substTX (d: nat) (u: ty) (xx: exp) : exp :=
  match xx with
  | XVar _     => xx

  | XApp x1 x2
    => XApp (substTX d u x1) (substTX d u x2)

  | XTup xs
    => XTup (map (substTX d u) xs)

  | XProj n x
    => XProj n (substTX d u x)

  | XNFun ts x
    => XNFun (map (substTT d u) ts) (substTX d u x)

  | XNApp x xs
    => XNApp (substTX d u x) (map (substTX d u) xs)

  | XFix t1 t2 x
    => XFix (substTT d u t1) (substTT d u t2) (substTX d u x)

  | XCon dc xs
    => XCon dc (map (substTX d u) xs)

  | XMatch x aa
    => XMatch (substTX d u x) (map (substTA d u) aa)

  | XChoice t pc xs
    => XChoice (substTT d u t) pc (map (substTX d u) xs)
  end

with substTA (d: nat) (u: ty) (a: alt) : alt :=
       match a with
       | AAlt dc ts x => AAlt dc (map (substTT d u) ts) (substTX d u x)
       end.


(* Substitution of expressions in expressions. *)
Fixpoint substXX (d: nat) (u: exp) (xx: exp) : exp :=
  match xx with
  | XVar ix
    => match nat_compare ix d with
      | Eq => u
      | Gt => XVar (ix - 1)
      | _  => XVar  ix
      end
  | XApp x1 x2
    => XApp (substXX d u x1) (substXX d u x2)

  | XTup xs
    => XTup (map (substXX d u) xs)

  | XProj n x
    => XProj n (substXX d u x)

  | XNFun ts x
    => XNFun ts (substXX (d + length ts) (liftXX (length ts) 0 u) x)

  | XNApp x xs
    => XNApp (substXX d u x) (map (substXX d u) xs)

  (* Lift free value variables in the expression to be substituted
     when we move across value abstractions. *)
  | XFix t1 t2 x
    => XFix t1 t2 (substXX (S (S d)) (liftXX 2 0 u) x)

  | XCon dc xs
    => XCon dc (map (substXX d u) xs)

  | XMatch x aa
    => XMatch (substXX d u x) (map (substXA d u) aa)

  | XChoice t pc xs
    => XChoice t pc (map (substXX d u) xs)
  end

with substXA (d: nat) (u: exp) (a: alt) : alt :=
       match a with
       | AAlt dc ts x => AAlt dc ts (substXX (d + length ts) (liftXX (length ts) 0 u) x)
       end.

Fixpoint substXXs (d: nat) (us: list exp) (xx: exp) :=
 match us with
 | nil      => xx
 | u :: us' => substXXs d us'
                 (substXX d (liftXX (List.length us') 0 u)
                            xx)
 end.


(* The data constructor of an alternative is unchanged
   by lifting. *)
Lemma dcOfAlt_liftXA
 : forall n d a
 , dcOfAlt (liftXA n d a) = dcOfAlt a.
Proof.
 intros. destruct a. auto.
Qed.
Lemma dcOfAlt_liftTA
 : forall d a
 , dcOfAlt (liftTA d a) = dcOfAlt a.
Proof.
 intros. destruct a. auto.
Qed.
Lemma dcOfAlt_substXA
  : forall d u a,
    dcOfAlt (substXA d u a) = dcOfAlt a.
Proof.
  intros. destruct a. auto.
Qed.
Lemma dcOfAlt_substTA
  : forall d t a,
    dcOfAlt (substTA d t a) = dcOfAlt a.
Proof.
  intros. destruct a. auto.
Qed.


(* When we lift an expression by zero places,
   then the expression is unchanged. *)
Lemma liftXX_zero
  : forall d x,
    liftXX 0 d x = x.
Proof.
  intros. gen d.
  induction x using exp_mutind with
      (PA := fun a => forall d
               ,  liftXA 0 d a = a);
    rip; simpl;
      try (solve [f_equal; rewritess; burn]).

  Case "XVar".
  lift_cases; burn.

  Case "XTup".
  nforall.
  rewrite (map_ext_in (liftXX 0 d) id); auto.
  rewrite map_id; auto.

  Case "XNApp".
  nforall.
  rewrite (map_ext_in (liftXX 0 d) id); auto.
  rewrite map_id; auto. rewrite IHx; auto.

  Case "XCon".
  nforall.
  rewrite (map_ext_in (liftXX 0 d) id); auto.
  rewrite map_id; auto.

  Case "XMatch".
  nforall.
  rewrite (map_ext_in (liftXA 0 d) id); auto.
  rewrite map_id. rewrite IHx; auto.

  Case "XChoice".
  nforall.
  rewrite (map_ext_in (liftXX 0 d) id); auto.
  rewrite map_id; auto.
Qed.

(* Commutivity of expression lifting. *)
Lemma liftXX_comm
 : forall n m x d
 , liftXX n d (liftXX m d x)
 = liftXX m d (liftXX n d x).
Proof.
 intros. gen d.
 induction x using exp_mutind with
  (PA := fun a => forall d
      ,  liftXA n d (liftXA m d a)
      =  liftXA m d (liftXA n d a));
   rip; simpl;
   try (solve [f_equal; rewritess; burn]).

 Case "XVar".
 repeat (simpl; lift_cases; intros);
   try solve [f_equal; omega].

 Case "XTup".
 f_equal.
 repeat (rewrite map_map).
 rewrite Forall_forall in *.
 rewrite (map_ext_in
            (fun x0 => liftXX n d (liftXX m d x0))
            (fun x0 => liftXX m d (liftXX n d x0))); burn.

 Case "XNApp".
 f_equal. apply IHx; auto.
 repeat (rewrite map_map).
 rewrite Forall_forall in *.
 rewrite (map_ext_in
            (fun x0 => liftXX n d (liftXX m d x0))
            (fun x0 => liftXX m d (liftXX n d x0))); burn.

 Case "XCon".
 f_equal.
 repeat (rewrite map_map).
 rewrite Forall_forall in *.
 rewrite (map_ext_in
            (fun x0 => liftXX n d (liftXX m d x0))
            (fun x0 => liftXX m d (liftXX n d x0))); burn.

 Case "XMatch".
 f_equal. burn.
 repeat (rewrite map_map).
 rewrite Forall_forall in *.
 rewrite (map_ext_in
            (fun a1 => liftXA n d (liftXA m d a1))
            (fun a1 => liftXA m d (liftXA n d a1))); burn.

 Case "XChoice".
 f_equal.
 repeat (rewrite map_map).
 rewrite Forall_forall in *.
 rewrite (map_ext_in
            (fun x0 => liftXX n d (liftXX m d x0))
            (fun x0 => liftXX m d (liftXX n d x0))); burn.
Qed.


Ltac burn_liftXX_succ :=
  match goal with
  | [ H : Forall _ _ |- map _ _ = map _ _ ] =>
    repeat (rewrite map_map);
    rewrite Forall_forall in *
  end.


(* When consecutively lifting an expression, we can lift by one
   more place in the first lifting and one less in the second. *)
Lemma liftXX_succ
 : forall n m d x
 , liftXX (S n) d (liftXX m     d x)
 = liftXX n     d (liftXX (S m) d x).
Proof.
  intros. gen d.
  induction x using exp_mutind with
      (PA := fun a => forall d
               ,  liftXA (S n) d (liftXA  m    d a)
                  =  liftXA n     d (liftXA (S m) d a));
    rip; simpl;
      try (solve [f_equal; rewritess; burn]).

  Case "XVar".
  repeat (simple; lift_cases; intros);
    try (solve [f_equal; omega]).

  Case "XTup".
  f_equal.
  burn_liftXX_succ.
  rewrite (map_ext_in
             (fun x0 => liftXX (S n) d (liftXX m d x0))
             (fun x0 => liftXX n d (liftXX (S m) d x0))); burn.

  Case "XNApp".
  f_equal. apply IHx; auto.
  burn_liftXX_succ.
  rewrite (map_ext_in
             (fun x0 => liftXX (S n) d (liftXX m d x0))
             (fun x0 => liftXX n d (liftXX (S m) d x0))); burn.

  Case "XCon".
  f_equal.
  burn_liftXX_succ.
  rewrite (map_ext_in
             (fun x0 => liftXX (S n) d (liftXX m d x0))
             (fun x0 => liftXX n d (liftXX (S m) d x0))); burn.

  Case "XMatch".
  f_equal. eauto.
  burn_liftXX_succ.
  rewrite (map_ext_in
             (fun x1 => liftXA (S n) d (liftXA m d x1))
             (fun x1 => liftXA n d (liftXA (S m) d x1))); burn.

  Case "XChoice".
  f_equal.
  burn_liftXX_succ.
  rewrite (map_ext_in
             (fun x0 => liftXX (S n) d (liftXX m d x0))
             (fun x0 => liftXX n d (liftXX (S m) d x0))); burn.
Qed.


(* We can collapse two consecutive lifting expressions by lifting
   just once by the sum of the places, provided the lifting
   occurs at depth zero. *)
Lemma liftXX_plus
 : forall n m x
 , liftXX n 0 (liftXX m 0 x) = liftXX (n + m) 0 x.
Proof.
 intros. gen n.
 induction m.
  intros. rewrite liftXX_zero. nnat. burn.
  intros.
   rrwrite (n + S m = S n + m).
   rewrite liftXX_comm.
   rewrite <- IHm.
   rewrite liftXX_comm.
   rewrite liftXX_succ.
   auto.
Qed.


(* -------------------------Existential----------------------------------- *)
Definition substTM (d : nat) (u : ty) (m : method) : method :=
  match m with
  | mkMethod arity dom body cod =>
    mkMethod arity
             (map (substTT d u) dom)
             (substTX d u body)
             (substTT d u cod)
  end.

Definition substXM (d : nat) (u : exp) (m : method) : method :=
  match m with
  | mkMethod arity dom body cod =>
    mkMethod arity dom (substXX d u body) cod
  end.

Definition substTADT (d : nat) (u : ty) (ad : adt) : adt :=
  match ad with
  | IADT r ms ss => IADT (substTT d u r) (map (substTM d u) ms) (map (substTT d u) ss)
  end.

Fixpoint substTP (d : nat) (u : ty) (p : prog) : prog :=
  match p with
  | PLET ad p' => PLET (substTADT d u ad) (substTP (S d) (liftTT 0 u) p')
  | PEXP x     => PEXP (substTX d u x)
  end.

(* Substitution of expressions in ADTs. *)
Definition substXADT (d : nat) (u : exp) (ad : adt) : adt :=
  match ad with
  | IADT r ms ss => IADT r (map (substXM d u) ms) ss
  end.

(* Substitution of expressions in programs. *)
Fixpoint substXP (d : nat) (u : exp) (p : prog) : prog :=
  match p with
  | PLET ((IADT r ms ss) as ad) p'
    => PLET (substXADT d u ad)
           (substXP (d + length ms)
                    (liftXX (length ms) 0 (liftTX 0 u))
                    p')
  | PEXP x
    => PEXP (substXX d u x)
  end.

Fixpoint substXXsP (d : nat) (us : list exp) (p : prog) :=
  match us with
  | nil => p
  | u :: us' => substXXsP d us'
                         (substXP d (liftXX (List.length us') 0 u)
                                  p)
  end.

(* Weak normal forms cannot be reduced further by
   call-by-value evaluation. *)
Inductive wnfP : prog -> Prop :=
 | Wnf_PExp
   : forall x,
     wnfX x
     -> wnfP (PEXP x).
Hint Constructors wnfP.

Definition wfMethod (ke : kienv) (te : tyenv) (m : method) : Prop :=
  match m with
  | mkMethod arity dom (XNFun ts x as body) cod =>
    wfX ke te body
    /\ length ts = arity + (length dom)
    /\ wfT ke cod
  | _ => False
  end.

Definition wfADT (ke : kienv) (te : tyenv) (ad : adt) : Prop :=
  match ad with
  | IADT r ms ss => wfT ke r
                   /\ Forall (wfMethod ke te) ms
                   /\ Forall (wfT ke) ss
  end.
Hint Unfold wfADT.

Fixpoint hackyBuildStrippedTypes (ts : list ty) :=
  match ts with
  | (TExists t) :: ts' => t :: (hackyBuildStrippedTypes ts')
  | _ :: ts' => hackyBuildStrippedTypes ts'
  | nil => nil
  end.

Fixpoint wfP (ke: kienv) (te: tyenv) (p: prog) : Prop :=
  match p with
  | PLET ad p' =>
    match ad with
    | IADT r ms ss =>
      wfADT ke te ad /\ wfP (ke :> KStar) (te >< (hackyBuildStrippedTypes ss)) p'
    end
  | PEXP x => wfX ke te x
  end.
Hint Unfold wfP.

(* Closed programs are well formed under empty environments *)
Definition closedP (p : prog) : Prop
 := wfP nil nil p.
Hint Unfold closedP.

(* ValuePs are closed programs that cannot be reduced further. *)
Inductive valueP : prog -> Prop :=
 | ValueP
   : forall p,
     wnfP p -> closedP p
     -> valueP p.
Hint Constructors valueP.
