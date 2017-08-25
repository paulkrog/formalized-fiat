
(* Extensions to the Coq.Lists.List module.
   These modules are listed in order of increasing interesingness.
   For lemmas involving multiple functions, eg something combining Forall2
   with update, you'll find it in the "most interesting" module. *)
Require Export FiatFormal.Data.List.Base.
Require Export FiatFormal.Data.List.Map.
Require Export FiatFormal.Data.List.Forall.
Require Export FiatFormal.Data.List.Forall2.
Require Export FiatFormal.Data.List.Firstn.
Require Export FiatFormal.Data.List.Filter.
Require Export FiatFormal.Data.List.Insert.
Require Export FiatFormal.Data.List.Replace.
Require Export FiatFormal.Data.List.Delete.
Require Export FiatFormal.Data.List.Update.
Require Export FiatFormal.Data.List.Extends.
Require Export FiatFormal.Data.List.Elem.
Require Export FiatFormal.Data.List.Concat.
Require Export FiatFormal.Data.List.Max.
Require Export FiatFormal.Data.List.Program.
Require Import FiatFormal.Data.Nat.
Require Import FiatFormal.Tactics.
Require Import Coq.Program.Basics.


(* Intuition tactic for lists
   Does some stuff to lists that we usually want *)

(* Discharge upper bound on index used in get *)
Ltac lists_get_length_some
 := match goal with
    | [  H1 : Some _  = get ?ix ?xs
      ,  H2 : length ?xs > ?ix
      |- _] => idtac

    | [ H : Some _  = get ?ix ?xs
      |- _ ]
    => assert (length xs > ix) by
        (eapply get_length_more; eauto)
    end.


(* Discharge lower bound on index used in get *)
Ltac lists_get_length_none
 := match goal with
    | [ H1 : None    = get ?ix ?xs
      , H2 : length ?xs <= ?ix
      |- _] => idtac

    | [ H : None    = get ?ix ?xs |- _ ]
    => assert (length xs <= ix) by
        (eapply get_none_length; eauto)
    end.


(* Infer relationship between values from original and transformed list *)
Ltac lists_get_map_some_some
 := match goal with
    | [ H1 : Some ?t1 = get ?ix ?us
      , H2 : Some ?t2 = get ?ix (map ?f ?us)
      , H3 : ?t2 = ?f ?t1
      |- _] => idtac

    | [ H1 : Some ?t1 = get ?ix ?us
      , H2 : Some ?t2 = get ?ix (map ?f ?us)
      |- _]
      => assert (t2 = f t1) by
          (symmetry; eapply map_get_some_some; eauto)
    end.


(* Forall_get can't be used as a regular hint *)
Ltac lists_Forall_get
 := match goal with
    | [  H1 : Forall ?P ?xs
      ,  H2 : Some ?x = get ?ix ?xs
      |- ?P ?x ]
      => eapply Forall_get; eauto

    | [  H1 : Forall (?P ?y) ?xs
      ,  H2 : Some ?x = get ?ix ?xs
      |- (?P ?y) ?x ]
      => eapply Forall_get; eauto
    end.


(* Intuition tactic for lists *)
Ltac lists
 := try lists_get_map_some_some;
    try lists_get_length_some;
    try lists_get_length_none;
    try lists_Forall_get;
    repeat (try (rewrite map_length in *));
    repeat (try (rewrite map_map    in *);
            unfold compose in *).
