
Require Import FiatFormal.Language.Step.

(* need to access all operations of these adts. *)
(* may need make use of wfP and wfADT to enforce n-ary. *)
(* functions.  *)

(* need way to specify method arity  *)

Definition getRep (a : adt) :=
  match a with
  | IADT r x s => r
  end.

(* Definition getOps (a : adt) := *)
(*   match a with *)
(*   | IADT r x s => match x with *)
(*                  | TNProd xs => match xs with *)
(*                                | TNFun ts tRes x :: xs' =>  *)

Definition ADTrefines (aOld aNew : adt) :=
  exists (absRel : getRep aOld -> getRep aNew -> Prop),
  forall op, In op (getOps aOld).
