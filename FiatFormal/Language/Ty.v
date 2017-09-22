Require Export FiatFormal.Language.Base.


(* Naming algebraic data types *)
Inductive tycon : Type :=
 | TyConData   : nat -> tycon.
Hint Constructors tycon.

(* Naming constructors for algebraic data types *)
Inductive datacon : Type :=
 | DataCon    : nat -> datacon.
Hint Constructors datacon.

(* Naming abstract data types *)
Inductive adtcon : Type :=
| AdtCon : nat -> adtcon.
Hint Constructors adtcon.

(* Naming predicate types *)
Inductive predcon : Type :=
| PredCon : nat -> predcon.
Hint Constructors predcon.

(* Functions for testing equality of these "names" *)
Fixpoint tycon_beq t1 t2 :=
  match t1, t2 with
  | TyConData n1, TyConData n2 => beq_nat n1 n2
  end.
Fixpoint datacon_beq t1 t2 :=
  match t1, t2 with
  | DataCon n1, DataCon n2 => beq_nat n1 n2
  end.
Fixpoint adtcon_beq t1 t2 :=
  match t1, t2 with
  | AdtCon n1, AdtCon n2 => beq_nat n1 n2
  end.
Fixpoint predcon_beq t1 t2 :=
  match t1, t2 with
  | PredCon n1, PredCon n2 => beq_nat n1 n2
  end.


(* Embedded Fiat Type *)
Inductive ty : Type :=
(* Build each of first three types by
   supplying an appropriate "name" *)
 | TCon   : tycon -> ty
 | TAdt   : adtcon -> ty
 | TPred  : predcon -> ty
(* Build a function type *)
 | TFun   : ty -> ty -> ty
 | TNaryFun : list ty -> ty -> ty
 | TProd    : ty -> ty -> ty
 | TUnit    : ty.
Hint Constructors ty.


(* Type Environment *)
Definition tyenv := list ty.
(* Helpful alias -- should Rep be restricted to algebraic data types? *)
Definition Rep   := ty.

(* A Record for method signatures -- "Set" ok? *)
Record Sig : Set := mkSig
                      { ac : adtcon;
                        arity : nat;
                        dom : list ty;
                        cod : ty;
                      }.

Fixpoint tyList (n : nat) (t : ty) : list ty :=
  match n with
  | O => nil
  | S n' => (tyList n' t) :> t
  end.

Definition buildMethodTyEnv (r : ty) (s : Sig) : list ty :=
  (tyList s.(arity) r) >< s.(dom).

Definition buildMethodTyList (r : ty) (s : Sig) : list ty :=
  (tyList s.(arity) r) >< s.(dom) >< (s.(cod) :: nil).

Fixpoint typeSubst (ac : adtcon) (s : ty) (t : ty) : ty :=
  match t with
  | TFun t1 t2 => TFun (typeSubst ac s t1) (typeSubst ac s t2)
  | TNaryFun ts t2 => TNaryFun (map (typeSubst ac s) ts) (typeSubst ac s t2)
  | TCon tc => TCon tc
  | TPred pc => TPred pc
  | TAdt ac' => if adtcon_beq ac ac'
               then s
               else TAdt ac'
  | TProd t1 t2 => TProd (typeSubst ac s t1) (typeSubst ac s t2)
  | TUnit => TUnit
  end.

Definition sigToNaryFunTy (r : ty) (s : Sig) : ty :=
  TNaryFun ((tyList s.(arity) r) >< s.(dom)) s.(cod).


(* Example: naming new algebraic data types *)
Notation FiatUnitType := (TyConData 0).
Notation FiatNatType := (TyConData 1).
Notation FiatListType := (TyConData 2).
Notation FiatProdType := (TyConData 3).
Notation FiatProdData := (DataCon 0).
