Require Import FiatFormal.Tactics.LibTactics.

Ltac ex_spec :=
  match goal with
  | [ H1 : ?P, H2 : (exists _, ?A) -> ?B |- _ ] => destruct H2; eexists; eassumption
  end.

Tactic Notation "gen" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5) ident(I6) ident(I7) ident(I8) ident(I9) ident(I10) :=
  gen I10; gen I9; gen I8; gen I7; gen I6; gen I5; gen I4; gen I3; gen I2; gen I1.