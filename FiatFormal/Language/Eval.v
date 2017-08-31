
Require Export FiatFormal.Language.SubstExpExp.
Require Export FiatFormal.Language.Step.
Require Export FiatFormal.Language.Exp.
Require Import FiatFormal.Language.Preservation.
Require Import FiatFormal.Language.TyJudge.


(* Big Step Evaluation
   This is also called 'Natural Semantics'.
   It provides a relation between the expression to be reduced
   and its final value. *)
Inductive EVAL : adt_defs -> exp -> exp -> Prop :=
 | EvDone
   : forall adt_ds v2,
     wnfX  v2
     -> EVAL adt_ds v2 v2

 | EvLamApp
   :  forall adt_ds x1 t11 x12 x2 v2 v3,
     EVAL adt_ds x1 (XLam t11 x12)
     -> EVAL adt_ds x2 v2
     -> EVAL adt_ds (substX 0 v2 x12) v3
     -> EVAL adt_ds (XApp x1 x2)      v3

 | EvFixApp
   : forall adt_ds t1 t2 x0 x1 x2 v2 v3,
     EVAL adt_ds x0 (XFix t1 t2 x1)
     -> EVAL adt_ds x2 v2
     -> EVAL adt_ds (substX 0 (XFix t1 t2 x1) (substX 0 v2 x1)) v3
     -> EVAL adt_ds (XApp x0 x2) v3

 | EvCon
   : forall adt_ds dc xs vs,
     EVALS adt_ds xs vs
     -> EVAL adt_ds (XCon dc xs) (XCon dc vs)

 | EvMatch
   :  forall adt_ds x1 x2 v3 dc vs alts tsArgs,
     EVAL adt_ds x1 (XCon dc vs)
     -> Forall wnfX vs
     -> getAlt dc alts = Some (AAlt dc tsArgs x2)
     -> EVAL adt_ds (substXs 0 vs x2) v3
     -> EVAL adt_ds (XMatch x1 alts)   v3

 | EvChoice
   : forall adt_ds x1 v2 t1 xs fp,
     EVAL adt_ds x1 (XChoice t1 xs fp)
     -> wnfX v2
     (* -> fp v2 *) (* TODO *)
     -> EVAL adt_ds x1 v2

 | EvCall
   : forall adt_ds ac n xbody v1 xs vs,
     EVALS adt_ds xs vs
     -> Forall wnfX vs
     -> getADTBody ac n adt_ds = Some xbody
     -> EVAL adt_ds (substXs 0 vs xbody) v1
     -> EVAL adt_ds (XCall ac n xs) v1

 with EVALS : adt_defs -> list exp -> list exp -> Prop :=
      | EvsNil : forall adt_ds,
          EVALS adt_ds nil nil

      | EvsCons
        :  forall adt_ds x v xs vs,
          EVAL adt_ds  x  v
           -> EVALS adt_ds xs vs
           -> EVALS adt_ds (x :: xs) (v :: vs).

Hint Constructors EVAL.
Hint Constructors EVALS.


(* Invert all hypothesis that are compound eval statements. *)
Ltac inverts_eval :=
 repeat
  (match goal with
   | [ H: EVAL (XApp _ _)  _ |- _ ] => inverts H
   | [ H: EVAL (XCon _ _)  _ |- _ ] => inverts H
   | [ H: EVAL (XMatch _ _) _ |- _ ] => inverts H
   end).


(* Theorem EVAL_mutind *)
(*  :  forall (PE : exp      -> exp      -> Prop) *)
(*            (PS : list exp -> list exp -> Prop) *)

(*  ,  (forall v2 *)
(*     ,  wnfX v2 *)
(*     -> PE v2 v2) *)
(*  -> (forall x1 t11 x12 x2 v2 v3 *)
(*     ,  EVAL x1 (XLam t11 x12)    -> PE x1 (XLam t11 x12) *)
(*     -> EVAL x2 v2                -> PE x2 v2 *)
(*     -> EVAL (substX 0 v2 x12) v3 -> PE (substX 0 v2 x12) v3 *)
(*     -> PE (XApp x1 x2) v3) *)
(*  -> (forall x1 x11 t1 t2 x2 v2 v3, *)
(*        EVAL x1 (XFix t1 t2 x11) -> PE x1 (XFix t1 t2 x11) *)
(*        -> EVAL x2 v2 -> PE x2 v2 *)
(*        -> EVAL (substX 0 (XFix t1 t2 x11) (substX 0 v2 x11)) v3 -> PE (substX 0 (XFix t1 t2 x11) (substX 0 v2 x11)) v3 *)
(*        -> PE (XApp x1 x2) v3) *)
(*  -> (forall dc xs vs *)
(*     ,  EVALS xs vs               -> PS xs vs *)
(*     -> PE (XCon dc xs) (XCon dc vs)) *)
(*  -> (forall x1 x2 v3 dc vs alts tsArgs *)
(*     ,  EVAL x1 (XCon dc vs)      -> PE x1 (XCon dc vs) *)
(*     -> Forall wnfX vs *)
(*     -> getAlt dc alts = Some (AAlt dc tsArgs x2) *)
(*     -> EVAL (substXs 0 vs x2) v3 -> PE (substXs 0 vs x2) v3 *)
(*     -> PE (XMatch x1 alts) v3) *)
(*  (* -> (forall t1 t2 x1 v1 x2 pr, *) *)
(*  (*       EVAL x1 (XChoice t1 t2 pr) -> PE x1 (XChoice t1 t2 pr) *) *)
(*  (*       -> wnf v1 *) *)
(*  (*       -> pr x2 *) *)
(*  (*   ) *) *)

(*  -> (  PS nil nil) *)
(*  -> (forall x v xs vs *)
(*     ,  EVAL x v                  -> PE x  v *)
(*     -> EVALS xs vs               -> PS xs vs *)
(*     -> PS (x :: xs) (v :: vs)) *)
(*  -> forall x1 x2 *)
(*  ,  EVAL x1 x2 -> PE x1 x2. *)

(* Proof. *)
(*  intros PE PS. *)
(*  intros Hdone Hlam Hcon Hcase Hnil Hcons. *)
(*  refine (fix  IHPE x  x'  (HE: EVAL  x  x')  {struct HE} *)
(*               : PE x x'   := _ *)
(*          with IHPS xs xs' (HS: EVALS xs xs') {struct HS} *)
(*               : PS xs xs' := _ *)
(*          for  IHPE). *)

(*  case HE; intros. *)
(*  eapply Hdone; eauto. *)
(*  eapply Hlam;  eauto. *)
(*  eapply Hcon;  eauto. *)
(*  eapply Hcase; eauto. *)

(*  case HS; intros. *)
(*  eapply Hnil. *)
(*  eapply Hcons; eauto. *)
(* Qed. *)
(* Admitted. *)

(* A terminating big-step evaluation always produces a whnf.
   The fact that the evaluation terminated is implied by the fact
   that we have a finite proof of EVAL to pass to this lemma. *)
Lemma eval_produces_wnfX
 :  forall adt_ds x1 v1
 ,  EVAL adt_ds   x1 v1
 -> wnfX  v1.
Proof.
(*  intros. *)
(*  induction H using EVAL_mutind with *)
(*   (PS := fun xs vs *)
(*       => EVALS xs vs *)
(*       -> Forall wnfX vs); *)
(*   intros; eauto. *)
(* Qed. *)
Admitted.
Hint Resolve eval_produces_wnfX.


Lemma evals_produces_wnfX
 :  forall adt_ds xs vs
 ,  EVALS adt_ds xs vs
 -> Forall wnfX vs.
Proof.
  (* intros. induction H; eauto. Qed. *)
Admitted.
Hint Resolve evals_produces_wnfX.


(* Big to Small steps
   Convert a big-step evaluation into a list of individual
   machine steps. *)
Lemma steps_of_eval
  : forall alg_ds adt_ds x1 t1 x2,
    TYPE alg_ds adt_ds nil x1 t1
    -> EVAL adt_ds x1 x2
 -> STEPS adt_ds x1 x2.
Proof.
(*  intros ds x1 t1 v2 HT HE. gen t1. *)
(*  induction HE using EVAL_mutind with *)
(*   (PS := fun xs vs => forall ts *)
(*       ,  Forall2 (TYPE ds nil) xs ts *)
(*       -> EVALS xs vs *)
(*       -> Forall2 STEPS xs vs) *)
(*   ; intros. *)

(*  Case "EvDone". *)
(*   intros. apply EsNone. *)

(*  (* Function Application ***) *)
(*  Case "EvLamApp". *)
(*   intros. inverts HT. *)

(*   lets E1: IHHE1 H3. *)
(*   lets E2: IHHE2 H5. *)
(*   lets T1: preservation_steps H3 E1. inverts keep T1. *)
(*   lets T2: preservation_steps H5 E2. *)
(*   lets T3: subst_exp_exp H2 T2. *)
(*   lets E3: IHHE3 T3. *)

(*   eapply EsAppend. *)
(*     lets D: steps_context XcApp1. eapply D. eauto. *)
(*    eapply EsAppend. *)
(*     lets D: steps_context (XcApp2 (XLam t0 x12)). eauto. *)
(*     eapply D. eauto. *)
(*    eapply EsAppend. *)
(*     eapply EsStep. *)
(*      eapply EsLamApp. eauto. eauto. *)

(*  (* Constructor evaluation ***) *)
(*  Case "EvCon". *)
(*   intros. *)
(*   inverts HT. *)
(*   lets D: IHHE H8 H. *)
(*   eapply steps_in_XCon; eauto. *)


(*  (* Case selection ***) *)
(*  Case "EvCase". *)
(*   intros. inverts keep HT. *)

(*   lets Ex1: IHHE1 H3. clear IHHE1. *)

(*   eapply EsAppend. *)
(*    (* evaluate the discriminant *) *)
(*    lets HSx1: steps_context XcCase. eapply HSx1. *)
(*     eapply Ex1. *)

(*   (* choose the alternative *) *)
(*   lets HTCon: preservation_steps H3 Ex1. clear Ex1. *)
(*   inverts HTCon. *)
(*   assert (tsArgs0 = tsArgs). *)
(*    eapply getAlt_ctorArgTypesMatchDataDef; eauto. subst. *)

(*   lets HA: getAlt_in H0. *)
(*   norm. rip. *)
(*   apply H4 in HA. *)
(*   inverts HA. *)

(*    (* substitute ctor values into alternative *) *)
(*   eapply EsAppend. *)
(*    eapply EsStep. *)
(*     eapply EsCaseAlt; burn. *)
(*      burn using subst_exp_exp_list. *)

(*  Case "EvsNil". *)
(*   auto. *)

(*  Case "EvsHead". *)
(*   destruct ts. *)
(*    inverts H0. *)
(*    inverts H0. eauto. *)
(* Qed. *)
Admitted.


(* Small to Big steps
   Convert a list of individual machine steps to a big-step
   evaluation. The main part of this is the expansion lemma, which
   we use to build up the overall big-step evaluation one small-step
   at a time. The other lemmas are used to feed it small-steps. *)

(* Given an existing big-step evalution, we can produce a new one
   that does an extra step before returning the original value.
 *)
Lemma eval_expansion
  : forall alg_ds adt_ds te x1 t1 x2 v3,
    TYPE alg_ds adt_ds te x1 t1
 -> STEP adt_ds x1 x2 -> EVAL adt_ds x2 v3
 -> EVAL adt_ds x1 v3.
Proof.
(*  intros ds te x1 t1 x2 v3 HT HS. gen ds te t1 v3. *)
(*  induction HS; intros; *)
(*   try (solve [inverts H; eauto]); *)
(*   try eauto. *)

(*  Case "Context". *)
(*   destruct H; inverts_type; eauto. *)

(*    SCase "XcApp1". *)
(*     inverts_eval; burn. *)

(*    SCase "XcApp2". *)
(*     inverts_eval; burn. *)

(*    SCase "XcCon". *)
(*     assert (exists t, TYPE ds te x t). *)
(*     eapply exps_ctx_Forall2_exists_left; eauto. *)
(*     dest t. *)

(*     inverts_eval. *)
(*     inverts H2. *)
(*     eapply EvCon. clear H9. *)

(*     induction H; intros. *)
(*       inverts H5. *)
(*       eapply EvsCons. eauto. *)
(*        induction xs. *)
(*         eauto. *)
(*         inverts H6. eauto. *)
(*         inverts H5. eauto. *)

(*     eapply EvCon. *)
(*      clear H3 H4 H9. *)
(*      gen vs. *)
(*      induction H; intros. *)
(*       inverts H8. eauto. *)
(*       inverts H8. eauto. *)

(*    SCase "XcCase". *)
(*     inverts H0. inverts H. eauto. *)
(* Qed. *)
Admitted.

(* Convert a list of small steps to a big-step evaluation. *)
Lemma eval_of_stepsl
  : forall alg_ds adt_ds x1 t1 v2,
    TYPE alg_ds adt_ds nil x1 t1
    -> STEPSL adt_ds x1 v2 -> value v2
    -> EVAL adt_ds   x1 v2.
Proof.
(*  intros. *)
(*  induction H0. *)

(*  Case "EslNone". *)
(*   apply EvDone. inverts H1. auto. *)

(*  Case "EslCons". *)
(*   eapply eval_expansion; eauto. *)
(*   burn using preservation. *)
(* Qed. *)
Admitted.

(* Convert a multi-step evaluation to a big-step evaluation.
   We use stepsl_of_steps to flatten out the append constructors
   in the multi-step evaluation, leaving a list of individual
   small-steps. *)
Lemma eval_of_steps
  : forall alg_ds adt_ds x1 t1 v2,
    TYPE alg_ds adt_ds nil x1 t1
    -> STEPS adt_ds x1 v2 -> value v2
    -> EVAL adt_ds  x1 v2.
Proof.
(*  intros. *)
(*  eapply eval_of_stepsl; eauto. *)
(*  apply  stepsl_of_steps; auto. *)
(* Qed. *)
Admitted.