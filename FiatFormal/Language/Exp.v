
Require Export FiatFormal.Language.TyEnv.
Require Export FiatFormal.Language.Ty.
Require Export FiatFormal.Language.Ki.


(* Expressions *)
Inductive exp : Type :=
 | XVar  : nat -> exp             (* deBruijn indices *)
 (* | XLAM  : exp -> exp             (* Type abstraction *) *)
 (* | XAPP  : exp -> ty  -> exp      (* Type application *) *)
 | XLam  : ty  -> exp -> exp      (* Value abstraction *)
 | XApp  : exp -> exp -> exp      (* Value application *)

 | XTup   : list exp -> exp
 | XProj  : nat -> exp -> exp
 | XNFun  : list ty -> exp -> exp
 | XNApp  : exp -> list exp -> exp

 | XFix   : ty -> ty -> exp -> exp

 (* Data Types *)
 | XCon   : datacon -> list exp -> exp
 | XMatch : exp     -> list alt -> exp

 (* Alternatives *)
with alt     : Type :=
 | AAlt   : datacon -> list ty  -> exp -> alt.

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
 -> (forall t  x1,   PX x1                 -> PX (XLam t x1))
 -> (forall x1 x2,   PX x1 -> PX x2        -> PX (XApp x1 x2))
 -> (forall xs,      Forall PX xs         -> PX (XTup xs))
 -> (forall n x,     PX x                 -> PX (XProj n x))
 -> (forall ts x,    PX x                 -> PX (XNFun ts x))
 -> (forall x xs,    PX x -> Forall PX xs  -> PX (XNApp x xs))
 -> (forall t1 t2 x, PX x                 -> PX (XFix t1 t2 x))
 -> (forall dc xs,   Forall PX xs         -> PX (XCon dc xs))
 -> (forall x  aa,   PX x  -> Forall PA aa -> PX (XMatch x aa))
 -> (forall dc ts x, PX x                 -> PA (AAlt dc ts x))
 ->  forall x, PX x.
Proof.
  intros PX PA.
  intros var lam app tup proj nfun napp ffix con mmatch alt.
  refine (fix  IHX x : PX x := _
            with IHA a : PA a := _
                                   for  IHX).

  (* expressions *)
  case x; intros.

  Case "XVar".
  apply var.

  Case "XLam".
  apply lam.
  apply IHX.

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

  (* alternatives *)
  case a; intros.

  Case "XAlt".
  apply alt.
  apply IHX.
Qed.

Inductive hasChoiceX : exp -> Prop :=
.

(* ADTs *)
Inductive adt : Type :=
| IADT : ty -> exp -> ty -> adt.
Hint Constructors adt.

(* Programs *)
Inductive prog : Type :=
| PLET : adt -> prog -> prog
| PEXP : exp -> prog.
Hint Constructors prog.

Inductive hasChoiceP : prog -> Prop :=
.

(* Weak normal forms cannot be reduced further by
   call-by-value evaluation. *)
Inductive wnfX : exp -> Prop :=
 | Wnf_XVar
   : forall i
   , wnfX (XVar i)

 (* | Wnf_XLAM *)
 (*   : forall x1 *)
 (*   , wnfX (XLAM x1) *)

 | Wnf_XLam
   : forall t1 x2
   , wnfX (XLam t1 x2)

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
| WfX_XLam : forall ke te t x,
    wfT ke t -> wfX ke (te :> t) x
    -> wfX ke te (XLam t x)
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

with wfA : kienv -> tyenv -> alt -> Prop :=
     | WfA_AAlt : forall ke te dc ds ts x tsArgs tRes,
         getDataDef dc ds = Some (DefData dc tsArgs tRes)
         -> wfX ke (te >< tsArgs) x
         -> wfA ke te (AAlt dc ts x).

Hint Constructors wfA.
Hint Constructors wfX.

(* PMK: wfX has been made an Inductive data type above *)
(* Fixpoint wfX (ke: kienv) (te: tyenv) (xx: exp) : Prop := *)
(*  match xx with *)
(*  | XVar i     => exists t, get i te = Some t *)
(*  (* | XLAM x     => wfX (ke :> KStar) (liftTE 0 te) x *) *)
(*  (* | XAPP x t   => wfX ke te x  /\ wfT ke t *) *)
(*  | XLam t x   => wfT ke t     /\ wfX ke (te :> t) x *)
(*  | XApp x1 x2 => wfX ke te x1 /\ wfX ke te x2 *)

(*  (* | XTup xs => Forall (wfX ke te) xs *) *)
(*  (* | XProj n x => wfX ke te x *) *)
(*  (* | XNFun ts x => Forall (wfT ke) ts /\ wfX ke (te >< ts) x *) *)
(*  (* | XNApp x1 xs => wfX ke te x1 /\ Forall (wfX ke te) xs *) *)
(*  end. *)
(* Hint Unfold wfX. *)


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

  (* Increase type depth when moving across type abstractions. *)
  (* |  XLAM x *)
  (* => XLAM (liftTX (S d) x) *)

  (* |  XAPP x t *)
  (* => XAPP (liftTX d x)  (liftTT d t) *)

  | XLam t x
    => XLam (liftTT d t)  (liftTX d x)

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
  end

with liftTA (d: nat) (a : alt) : alt :=
       match a with
       | AAlt dc ts x => AAlt dc (map (liftTT d) ts) (liftTX d x)
       end.


(* PMK: Changed to include parameter for amount to lift by *)
(* Lift value indices in expressions. *)
Fixpoint liftXX (n: nat) (d: nat) (xx: exp) : exp :=
  match xx with
  | XVar ix
    => if le_gt_dec d ix
      then XVar (n + ix)
      else xx

  (* |  XLAM x *)
  (* => XLAM (liftXX d x) *)

  (* |  XAPP x t *)
  (* => XAPP (liftXX d x) t *)

  (* Increase value depth when moving across value abstractions. *)
  | XLam t x
    => XLam t (liftXX n (S d) x)

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

  | XFix t1 t2 x
    => XFix t1 t2 (liftXX n (S (S d)) x)

  | XCon dc xs
    => XCon dc (map (liftXX n d) xs)

  | XMatch x aa
    => XMatch (liftXX n d x) (map (liftXA n d) aa)
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

  (* Lift free type variables in the type to be substituted
     when we move across type abstractions. *)
  (* |  XLAM x *)
  (* => XLAM (substTX (S d) (liftTT 0 u) x) *)

  (* |  XAPP x t *)
  (* => XAPP (substTX d u x)  (substTT d u t) *)

  | XLam t x
    => XLam (substTT d u t)  (substTX d u x)

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

  (* Lift free type variables in the expression to be substituted
     when we move across type abstractions. *)
  (* |  XLAM x *)
  (* => XLAM (substXX d (liftTX 0 u) x) *)

  (* |  XAPP x t *)
  (* => XAPP (substXX d u x) t *)

  (* Lift free value variables in the expression to be substituted
     when we move across value abstractions. *)
  | XLam t x
    => XLam t (substXX (S d) (liftXX 1 0 u) x)

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

  | XFix t1 t2 x
    => XFix t1 t2 (substXX (S (S d)) (liftXX 2 0 u) x)

  | XCon dc xs
    => XCon dc (map (substXX d u) xs)

  | XMatch x aa
    => XMatch (substXX d u x) (map (substXA d u) aa)
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

 Case "XVar". (* disgusting *)
 lift_cases. intros. intros. simpl. lift_cases. intros. lift_cases. intros. f_equal. omega.
 intros. f_equal. omega. intros. lift_cases. intros; omega. intros; omega. intros.
 simpl. lift_cases; intros; try omega. auto.
 (* repeat (simpl; lift_cases; burn); *)
 (*   solve [f_equal; omega]. *)

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
 rewrite map_map.
 rewrite map_map.
 rewrite Forall_forall in *.
 rewrite (map_ext_in
            (fun a1 => liftXA n d (liftXA m d a1))
            (fun a1 => liftXA m d (liftXA n d a1))); burn.
Qed.


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
  repeat (rewrite map_map).
  rewrite Forall_forall in *.
  rewrite (map_ext_in
             (fun x0 => liftXX (S n) d (liftXX m d x0))
             (fun x0 => liftXX n d (liftXX (S m) d x0))); burn.

  Case "XNApp".
  f_equal. apply IHx; auto.
  repeat (rewrite map_map).
  rewrite Forall_forall in *.
  rewrite (map_ext_in
             (fun x0 => liftXX (S n) d (liftXX m d x0))
             (fun x0 => liftXX n d (liftXX (S m) d x0))); burn.

  Case "XCon".
  f_equal.
  repeat (rewrite map_map).
  rewrite Forall_forall in *.
  rewrite (map_ext_in
             (fun x0 => liftXX (S n) d (liftXX m d x0))
             (fun x0 => liftXX n d (liftXX (S m) d x0))); burn.

  Case "XMatch".
  f_equal. eauto.
  repeat (rewrite map_map).
  rewrite Forall_forall in *.
  rewrite (map_ext_in
             (fun x1 => liftXA (S n) d (liftXA m d x1))
             (fun x1 => liftXA n d (liftXA (S m) d x1))); burn.
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
Definition substTADT (d : nat) (u : ty) (ad : adt) : adt :=
  match ad with
  | IADT r x s => IADT (substTT d u r) (substTX d u x) (substTT d u s)
  end.

Fixpoint substTP (d : nat) (u : ty) (p : prog) : prog :=
  match p with
  | PLET ad p' => PLET (substTADT d u ad) (substTP (S d) (liftTT 0 u) p')
  | PEXP x     => PEXP (substTX d u x)
  end.

(* Substitution of expressions in ADTs. *)
Definition substXADT (d : nat) (u : exp) (ad : adt) : adt :=
  match ad with
  | IADT r x s => IADT r (substXX d u x) s
  end.

(* Substitution of expressions in programs. *)
Fixpoint substXP (d : nat) (u : exp) (p : prog) : prog :=
  match p with
  | PLET ad p' => PLET (substXADT d u ad) (substXP (S d) (liftXX 1 0 (liftTX 0 u)) p')
  | PEXP x     => PEXP (substXX d u x)
  end.

(* Weak normal forms cannot be reduced further by
   call-by-value evaluation. *)
Inductive wnfP : prog -> Prop :=
 | Wnf_PExp
   : forall x,
     wnfX x
     -> wnfP (PEXP x).
Hint Constructors wnfP.

Definition wfADT (ke : kienv) (te : tyenv) (ad : adt) : Prop :=
  match ad with
    (* perhaps here I can enforce appropriate nary function types in
       sig along with function form of method bodies similar to wfP below *)
  | IADT r x s => wfT ke r /\ wfX ke te x /\ wfT ke s
  end.
Hint Unfold wfADT.

(* A well formed program is closed under the given environments *)
Fixpoint wfP (ke: kienv) (te: tyenv) (p: prog) : Prop :=
  match p with
  | PLET ad p' => match ad with
                 | IADT r x s => match s with
                                | TExists t => wfADT ke te ad /\ wfP (ke :> KStar) ((liftTE 0 te) :> t) p'
                                | _ => False
                                end
                 end
  | PEXP x     => wfX ke te x
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
