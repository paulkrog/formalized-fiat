
Require Import FiatFormal.Language.TyJudge.
Require Import FiatFormal.Language.SubstTypeType.

(* Substitution lemma for substituting ADT contents into ADTs.
   This is unnecessary if we further restrict ADTs such that method bodies may
   not contain references to previously-bound ADTs.

   Note that substituting a type into an expression can instantiate
   type variables, so we also need to perform the substitution
   to the result type.
 *)

Theorem subst_exist_exp
  : forall ke te t1 kr tr x1 t2 x,
    KIND ke tr kr
    -> TYPE ke te x1 (substTT 0 tr t1)
    -> TYPE (ke :> kr) (te :> t1) x t2
    -> TYPE ke te (substTX 0 tr (substXX 0 x1 x)) t2.
Proof.
  intros. gen ke te t1 kr tr x1 t2.
  induction x; intros; simpl.
  Case "XVar".
  lift_cases.

(* Substitution lemma for substituting ADT contents into ADTs.
   This is unnecessary if we further restrict ADTs such that method bodies may
   not contain references to previously-bound ADTs.

   Note that substituting a type into an expression can instantiate
   type variables, so we also need to perform the substitution
   to the result type.
 *)

(* Not clear that this particular statement is what I want *)
Theorem subst_exist_adt
  : forall ke te t1 kr tr x1 t2 ad,
    KIND ke tr kr (* well-kinded rep type *)
    -> TYPE ke te x1 (substTT 0 tr t1) (* existential well-typed *)
    -> TYPEADT (ke :> kr) (te :> t1) ad t2
    -> TYPEADT ke te (substTADT 0 tr (substXADT 0 x1 ad)) t2.
Proof.
Abort.

(* Main substitution lemma for substituting ADT contents into program.
   If an ADT's methods implement their abstract interfaces,
   substituting method bodies and representation types in program
   preserves type.

   Note that substituting a type into an expression can instantiate
   type variables, so we also need to perform the substitution
   to the result type.
 *)

Theorem subst_exist_prog
  : forall ke te t1 kr tr x1 t2 p,
    KIND ke tr kr (* well-kinded rep type *)
    -> TYPE ke te x1 (substTT 0 tr t1) (* existential well-typed *)
    -> TYPEPROG (ke :> kr) (te :> t1) p t2 (* program well-typed with extended contexts *)
    -> TYPEPROG ke te (substTP 0 tr (substXP 0 x1 p)) t2.
Proof.
Abort.

Theorem subst_exist_prog_ix
  : forall ix ix' ke te k t tr t2 x1 p,
    get ix ke = Some k
    -> get ix' te = Some t
    -> KIND (delete ix ke) tr k
    -> TYPEPROG ke te p t2
    (* NOTE: the liftTT-ing for taur below shouldn't be necessary, just not sure where the simple condition on rep types should ultimately be stated *)
    -> TYPE (delete ix ke) (delete ix' te) x1 (substTT 0 tr t)
    -> TYPEPROG (delete ix ke) (delete ix' te) (substTP 0 tr (substXP 0 x1 p)) t2.
Proof.
Abort.
  (* intros. *)
  (* gen ix ix' ke te k. (* TODO: ask why gen fails with all idents in a single invocation *) *)
  (* gen t tr t2 x1. *)
  (* induction p; intros. *)
  (* Case "PLet". *)
  (* simpl; destruct a; simpl. *)
  (* eapply TYLet. *)
  (* SCase "ADT". *)

(* Theorem subst_type_exp_ix *)
(*   : forall ix ke te x1 t1 t2 k2, *)
(*     get ix ke = Some k2 *)
(*     -> TYPE ke  te x1 t1 *)
(*     -> KIND (delete ix ke)  t2 k2 *)
(*     -> TYPE (delete ix ke)     (substTE ix t2 te) *)
(*            (substTX ix t2 x1) (substTT ix t2 t1). *)
(* Proof. *)

(*  intros. gen ix ke te t1 t2 k2. *)
(*  induction x1; intros; simpl; inverts H0; eauto. *)

(*  Case "XVar". *)
(*   apply TYVar. *)
(*   unfold substTE. eapply get_map. auto. *)
(*   eapply subst_type_type_ix; eauto. *)

(*  Case "XLAM". *)
(*   simpl. apply TYLAM. *)
(*   rewrite delete_rewind. *)
(*   rewrite (liftTE_substTE 0 ix). *)
(*   eapply IHx1; eauto. *)
(*    apply liftTT_weaken. auto. *)

(*  Case "XAPP". *)
(*   rewrite (substTT_substTT 0 ix). *)
(*   apply TYAPP. *)
(*    simpl. eapply (IHx1 ix) in H6; eauto. *)
(*    simpl. eapply subst_type_type_ix; eauto. *)

(*  Case "XLam". *)
(*   simpl. apply TYLam. *)
(*   eapply subst_type_type_ix; eauto. *)
(*   unfold substTE. rewrite map_rewind. *)
(*   assert ( map (substTT ix t2) (te :> t) *)
(*          = substTE ix t2 (te :> t)). auto. *)
(*   rewrite H0. *)
(*    eapply IHx1; eauto. *)

(*  Case "XApp". *)
(*   eapply TYApp. *)
(*    eapply IHx1_1 in H6; eauto. *)
(*    eapply IHx1_2 in H8; eauto. *)
(* Qed. *)

(* Theorem subst_type_value *)
(*  :  forall ke te x1 t1 t2 k2 *)
(*  ,  TYPE (ke :> k2) te x1 t1 *)
(*  -> KIND ke  t2 k2 *)
(*  -> TYPE ke                (substTE 0 t2 te) *)
(*          (substTX 0 t2 x1) (substTT 0 t2 t1). *)
(* Proof. *)
(*  intros. *)
(*  assert (ke = delete 0 (ke :> k2)). auto. rewrite H1. *)
(*  eapply subst_type_exp_ix; simpl; eauto. *)
(* Qed. *)
