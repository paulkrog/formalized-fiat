
Require Export FiatFormal.Language.TyEnv.
Require Export FiatFormal.Language.Ty.
Require Export FiatFormal.Language.Ki.


(* Expressions *)
Inductive exp : Type :=
 | XVar  : nat -> exp             (* deBruijn indices *)
 | XLAM  : exp -> exp             (* Type abstraction *)
 | XAPP  : exp -> ty  -> exp      (* Type application *)
 | XLam  : ty  -> exp -> exp      (* Value abstraction *)
 | XApp  : exp -> exp -> exp.      (* Value application *)

 (* | XTup   : list exp -> exp *)
 (* | XProj  : nat -> exp -> exp *)
 (* | XNFun  : list ty -> exp -> exp *)
 (* | XNApp  : exp -> exp -> exp. *)

Hint Constructors exp.

(* ADTs *)
Inductive adt : Type :=
| IADT : ty -> exp -> ty -> adt.
Hint Constructors adt.

(* Programs *)
Inductive prog : Type :=
| PLET : adt -> prog -> prog
| PEXP : exp -> prog.
Hint Constructors prog.

(* Weak normal forms cannot be reduced further by
   call-by-value evaluation. *)
Inductive wnfX : exp -> Prop :=
 | Wnf_XVar
   : forall i
   , wnfX (XVar i)

 | Wnf_XLAM
   : forall x1
   , wnfX (XLAM x1)

 | Wnf_XLam
   : forall t1 x2
   , wnfX (XLam t1 x2).

Hint Constructors wnfX.


(* A well formed expression is closed under the given environments *)
Fixpoint wfX (ke: kienv) (te: tyenv) (xx: exp) : Prop :=
 match xx with
 | XVar i     => exists t, get i te = Some t
 | XLAM x     => wfX (ke :> KStar) (liftTE 0 te) x
 | XAPP x t   => wfX ke te x  /\ wfT ke t
 | XLam t x   => wfT ke t     /\ wfX ke (te :> t) x
 | XApp x1 x2 => wfX ke te x1 /\ wfX ke te x2
 end.
Hint Unfold wfX.


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
Fixpoint liftTX (d: nat) (xx: exp) : exp :=
  match xx with
  |  XVar _     => xx

  (* Increase type depth when moving across type abstractions. *)
  |  XLAM x
  => XLAM (liftTX (S d) x)

  |  XAPP x t
  => XAPP (liftTX d x)  (liftTT d t)

  |  XLam t x
  => XLam (liftTT d t)  (liftTX d x)

  |  XApp x1 x2
  => XApp (liftTX d x1) (liftTX d x2)
 end.


(* Lift value indices in expressions. *)
Fixpoint liftXX (d: nat) (xx: exp) : exp :=
  match xx with
  |  XVar ix
  => if le_gt_dec d ix
      then XVar (S ix)
      else xx

  |  XLAM x
  => XLAM (liftXX d x)

  |  XAPP x t
  => XAPP (liftXX d x) t

  (* Increase value depth when moving across value abstractions. *)
  |  XLam t x
  => XLam t (liftXX (S d) x)

  |  XApp x1 x2
  => XApp (liftXX d x1) (liftXX d x2)
 end.


(********************************************************************)
(* Substitution of types in expressions. *)
Fixpoint substTX (d: nat) (u: ty) (xx: exp) : exp :=
  match xx with
  | XVar _     => xx

  (* Lift free type variables in the type to be substituted
     when we move across type abstractions. *)
  |  XLAM x
  => XLAM (substTX (S d) (liftTT 0 u) x)

  |  XAPP x t
  => XAPP (substTX d u x)  (substTT d u t)

  |  XLam t x
  => XLam (substTT d u t)  (substTX d u x)

  |  XApp x1 x2
  => XApp (substTX d u x1) (substTX d u x2)
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
  |  XLAM x
  => XLAM (substXX d (liftTX 0 u) x)

  |  XAPP x t
  => XAPP (substXX d u x) t

  (* Lift free value variables in the expression to be substituted
     when we move across value abstractions. *)
  |  XLam t x
  => XLam t (substXX (S d) (liftXX 0 u) x)

  |  XApp x1 x2
  => XApp (substXX d u x1) (substXX d u x2)
  end.

(* ------------------------------------------------------------ *)
(* NOTE: assuming rep types are simple, i.e. no type variables  *)
Definition substTADT (d : nat) (u : ty) (ad : adt) : adt :=
  match ad with
  | IADT r x s => IADT r (substTX d u x) (substTT d u s)
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
  | PLET ad p' => PLET (substXADT d u ad) (substXP (S d) (liftXX 0 (liftTX 0 u)) p')
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

(* NOTE: assuming rep types are simple, i.e. no type variables  *)
(* A well formed ADT is closed under the given environments *)
Definition wfADT (ke : kienv) (te : tyenv) (ad : adt) : Prop :=
  match ad with
    (* perhaps here I can enforce appropriate nary function types in sig *)
  | IADT r x s => wfX ke te x /\ wfT ke s
  end.
Hint Unfold wfADT.

(* A well formed program is closed under the given environments *)
Fixpoint wfP (ke: kienv) (te: tyenv) (p: prog) : Prop :=
  match p with
  | PLET ad p' => wfADT ke te ad /\ wfP (ke :> KStar) (liftTE 0 te) p'
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
