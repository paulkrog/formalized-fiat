Require Export FiatFormal.Language.Base.


(* Type Constructors *)
Inductive tycon : Type :=
 | TyConData   : nat -> tycon.
Hint Constructors tycon.


(* Corresponds to the X's in paper *)
Inductive adtcon : Type :=
| AdtCon : nat -> adtcon.
Hint Constructors adtcon.


Fixpoint adtcon_beq t1 t2 :=
  match t1, t2 with
  | AdtCon n1, AdtCon n2 => beq_nat n1 n2
  end.

Fixpoint tycon_beq t1 t2 :=
  match t1, t2 with
  | TyConData n1, TyConData n2 => beq_nat n1 n2
  end.


(* Types *)
Inductive ty : Type :=
 | TCon   : tycon -> ty
 | TFun   : ty    -> ty -> ty
 | TX     : adtcon -> ty.
Hint Constructors ty.


(* Type Environment *)
Definition tyenv := list ty.


Notation FiatUnitType := (TyConData 0).
Notation FiatNatType := (TyConData 1).
Notation FiatListType := (TyConData 2).


Fixpoint tyDenote (t : ty) : Set :=
  match t with
  | TCon tc => match tc with
              | FiatUnitType => unit
              | FiatNatType => nat
              | FiatListType => list nat
              | _ => unit (* TODO *) end
  | TFun t1 t2 => (tyDenote t1 -> tyDenote t2)
  | TX ac => nat (* TODO *)
  end.
