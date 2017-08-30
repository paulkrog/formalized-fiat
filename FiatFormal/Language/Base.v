Require Export FiatFormal.PMKList.

Require Export FiatFormal.Data.List.
Require Export FiatFormal.Data.Nat.
Require Export FiatFormal.Norm.List.
Require Export FiatFormal.Norm.
Require Export FiatFormal.Tactics.Rip2.
Require Export FiatFormal.Tactics.Rewrite2.
Require Export FiatFormal.Tactics.Case.
Require Export FiatFormal.Tactics.Nope.
Require Export FiatFormal.Tactics.Break.
Require Export FiatFormal.Tactics.Rewrite.
Require Export FiatFormal.Tactics.Have.
Require Export FiatFormal.Tactics.Exists.
Require Export FiatFormal.Tactics.Short.
Require Export FiatFormal.Tactics.LibTactics.
Require Export Coq.Arith.EqNat.
Require Export Coq.Arith.Compare_dec.
Require Export Coq.Logic.FunctionalExtensionality.


Ltac norm
 := simpl in *;
    repeat (rip; try norm_nat; try norm_lists).

Ltac tburn0 T
 := norm; eauto using T; nope.

Ltac tburn T
 := try (solve [ tburn0 T
               | red; tburn0 T]).

Tactic Notation "burn"
 := tburn false.

Tactic Notation "burn" "using" tactic(T)
 := tburn T.

Ltac have_auto ::= burn.
