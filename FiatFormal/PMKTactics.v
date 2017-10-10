Require Import FiatFormal.Tactics.LibTactics.
(* Require Import Coq.Init.Nat. *)

(* Print Implicit ex_intro. *)

(* Ltac ex_spec := *)
(*   match goal with *)
(*   | [ H1 : ?B, H2 : (exists n, @?A n) -> ?R |- _ ] => pose proof (H2 (ex_intro _ _ H1)) *)
(*   end. *)

(* (* Ltac ex_spec' := *) *)
(* (*   match goal with *) *)
(* (*   | [ H1 :  ] *) *)

(* Lemma foo : 3 < 6 -> forall n, even n = true -> ((exists m, even m = true) -> True) -> False. *)
(* Proof. *)
(*   intros. *)
(*   ex_spec. *)

(* Tactic Notation "gen" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5) ident(I6) ident(I7) ident(I8) ident(I9) ident(I10) := *)
(*   gen I10; gen I9; gen I8; gen I7; gen I6; gen I5; gen I4; gen I3; gen I2; gen I1. *)