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
(* A type for method signatures *)
Inductive Sig : Type :=
(* A list of input types and an output type *)
| C_Sig : list ty -> ty -> Sig.
Hint Constructors Sig.
(* Helpful alias -- should Rep be restricted to algebraic data types? *)
Definition Rep   := ty.


(* Example: naming new algebraic data types *)
Notation FiatUnitType := (TyConData 0).
Notation FiatNatType := (TyConData 1).
Notation FiatListType := (TyConData 2).



(* Not sure where the concept below might get used *)

(* Fixpoint tyDenote (t : ty) : Set := *)
(*   match t with *)
(*   | TCon tc => match tc with *)
(*               | FiatUnitType => unit *)
(*               | FiatNatType => nat *)
(*               | FiatListType => list nat *)
(*               | _ => unit (* TODO *) end *)
(*   | TFun t1 t2 => (tyDenote t1 -> tyDenote t2) *)
(*   | TX ac => nat (* TODO *) *)
(*   | TPred pc => nat *)
(*   end. *)
