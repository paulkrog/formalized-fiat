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
 | TFun   : ty    -> ty -> ty.
Hint Constructors ty.


(* Type Environment *)
Definition tyenv := list ty.
(* Helpful alias -- should Rep be restricted to algebraic data types? *)
Definition Rep   := ty.

(* A Record for method signatures -- "Set" ok? *)
Record Sig : Set := mkSig
        {arity : nat;
         dom : list ty;
         cod : ty }.

Fixpoint buildTyList (n : nat) (t : ty) : list ty :=
  match n with
  | O => nil
  | S n' => (buildTyList n' t) :> t
  end.
Definition buildMethodTyEnv (r : ty) (s : Sig) : list ty :=
  (buildTyList s.(arity) r) >< s.(dom).

(* Set Printing Projections. *)
(* Print buildMethodTyEnv. *)

(* Example: naming new algebraic data types *)
Notation FiatUnitType := (TyConData 0).
Notation FiatNatType := (TyConData 1).
Notation FiatListType := (TyConData 2).
Notation FiatProdType := (TyConData 3). (* TODO: use in signatures? *)
Notation FiatProdData := (DataCon 0).

(* (* function for replacing references to (TAdt (AdtCon n)) with Rep in a list of ty. *) *)
(* (* used to type check method bodies *) *)
(* Fixpoint replace_TAdt_by_Rep (x : ty) (ac : adtcon) (l : list ty) : list ty := *)
(*   match l with *)
(*   | nil => nil *)
(*   | (TAdt ac') :: l' => if adtcon_beq ac ac' *)
(*                        then x          :: (replace_TAdt_by_Rep x ac l') *)
(*                        else (TAdt ac') :: (replace_TAdt_by_Rep x ac l') *)
(*   | x' :: l' => x' :: (replace_TAdt_by_Rep x ac l') *)
(*   end. *)