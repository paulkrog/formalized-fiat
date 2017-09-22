
Require Export FiatFormal.Language.StepContext.
Require Export FiatFormal.Language.StepAlt.
Require Export FiatFormal.Language.TyJudge.
Require Export FiatFormal.Language.SubstExpExp.
Require Export FiatFormal.Language.Exp.


(** * Single Small Step Evaluation *)
(** The single step rules model the individual transitions that the
     machine can make at runtime. *)

Inductive STEP : adt_defs -> exp -> exp -> Prop :=

 (* Step some sub-expression in an evaluation context *)
 | EsContext
   :  forall adt_ds C x x',
     exp_ctx C
   -> STEP adt_ds x x'
   -> STEP adt_ds (C x) (C x')

 | EsLet
   : forall adt_ds ac n  b x,
     getADTBody ac n adt_ds = Some b
     -> STEP adt_ds (XLet ac n x) (methodSubstX ac n b x) (* previously needed to subst all methods here *)

 | EsFixApp
   : forall adt_ds t1 t2 x1 v1,
     wnfX v1
     -> STEP adt_ds (XApp (XFix t1 t2 x1) v1)
            (substX 0 (XFix t1 t2 x1) (substX 0 v1 x1))

 | EsMatchAlt
   :  forall adt_ds dc vs tsArgs alts x,
     Forall wnfX vs
   -> getAlt dc alts = Some (AAlt dc tsArgs x)
   -> STEP adt_ds (XMatch (XCon dc vs) alts)
          (substXs 0 vs x)

 | EsPairFst
   : forall adt_ds v1 v2,
     wnfX v1
     -> wnfX v2
     -> STEP adt_ds (XFst (XPair v1 v2)) v1

 | EsPairSnd
   : forall adt_ds v1 v2,
     wnfX v1
     -> wnfX v2
     -> STEP adt_ds (XSnd (XPair v1 v2)) v2

 (* | EsADTCall *)
 (*   : forall adt_ds ac n vs x, *)
 (*     Forall wnfX vs *)
 (*   -> getADTBody ac n adt_ds = Some x *)
 (*   -> STEP adt_ds (XCall ac n vs) (substXs 0 vs x) *)

 | EsChoice
   : forall adt_ds t1 xs fp,
     STEP adt_ds (XChoice t1 xs fp) (XChoice t1 xs fp)
     (* fp = FiatPred t11 pr -> *)
     (* exists xDenoted v1, wnfX v1 /\ pr t1 xDenoted *)
     (*                    -> STEP (XChoice t1 xs fp) v1 *)
.

Hint Constructors STEP.


(* Multi-step evaluation
   A sequence of small step transitions.
   As opposed to STEPSL, this version has an append constructor
   ESAppend that makes it easy to join two evaluations together.
   We use this when converting big-step evaluations to small-step. *)
Inductive STEPS : adt_defs -> exp -> exp -> Prop :=

 (* After no steps, we get the same exp.
    We need this constructor to match the EVDone constructor
    in the big-step evaluation, so we can convert between big-step
    and multi-step evaluations. *)
 | EsNone
   :  forall adt_ds x1,
     STEPS adt_ds x1 x1

 (* Take a single step. *)
 | EsStep
   :  forall adt_ds x1 x2,
     STEP adt_ds x1 x2
   -> STEPS adt_ds x1 x2

 (* Combine two evaluations into a third. *)
 | EsAppend
   :  forall adt_ds x1 x2 x3,
     STEPS adt_ds x1 x2 -> STEPS adt_ds x2 x3
   -> STEPS adt_ds x1 x3.

Hint Constructors STEPS.


(* Stepping a wnf doesn't change it. *)
Lemma step_wnfX
  : forall adt_ds x v,
    wnfX x -> STEP adt_ds x v -> v = x.
Proof.
(*  intros x v HW HS. *)
(*  induction HS; nope. *)
(*   destruct H; burn. *)

(*  Case "XCon dc (C x)". *)
(*   inverts HW. *)
(*   assert (wnfX x). *)
(*   eapply exps_ctx_Forall; eauto. *)
(*   rrwrite (x' = x). auto. *)
(* Qed. *)
Admitted.


Lemma step_context_XCon_exists
  : forall adt_ds C x dc,
    exps_ctx wnfX C
    -> (exists x', STEP adt_ds x x')
    -> (exists x', STEP adt_ds (XCon dc (C x)) (XCon dc (C x'))).
Proof.
 intros adt_ds C x dc HC HS.
 shift x'.
 eapply (EsContext adt_ds (fun xx => XCon dc (C xx))); auto.
Qed.

Lemma step_context_XCall_exists_pmk
  : forall adt_ds C x ac n,
    exps_ctx wnfX C
    -> (exists x', STEP adt_ds x x')
    -> (exists x', STEP adt_ds (XOpCall ac n (C x)) (XOpCall ac n (C x'))).
Proof.
 intros adt_ds C x ac n HC HS.
 shift x'.
 eapply (EsContext adt_ds (fun xx => XOpCall ac n (C xx))); auto.
Qed.


(* Multi-step evaluating a wnf doesn't change it. *)
Lemma steps_wnfX
  : forall adt_ds x v,
    wnfX x -> STEPS adt_ds x v -> v = x.
Proof.
(*  intros x v HW HS. *)
(*  induction HS; burn. *)
(*   Case "EsStep". *)
(*    apply step_wnfX; auto. *)

(*   Case "EsAppend". *)
(*    have (x2 = x1). subst. auto. *)
(* Qed. *)
Admitted.

(* Multi-step evaluation in a context. *)
Lemma steps_context
  : forall adt_ds C x1 x1',
    exp_ctx C
    -> STEPS adt_ds x1 x1'
    -> STEPS adt_ds (C x1) (C x1').
Proof.
(*  intros C x1 x1' HC HS. *)
(*  induction HS; eauto. *)
(* Qed. *)
Admitted.

(* Multi-step evaluation of a data constructor argument. *)
Lemma steps_context_XCon
  : forall adt_ds C x v dc,
    exps_ctx wnfX C
    -> STEPS adt_ds x v
    -> STEPS adt_ds (XCon dc (C x)) (XCon dc (C v)).
Proof.
(*  intros C x v dc HC HS. *)
(*  induction HS; auto. *)

(*  Case "XCon". *)
(*   lets D: EsContext XcCon; eauto.  *)
(*   eauto. *)
(* Qed. *)
Admitted.

Lemma steps_in_XCon
  : forall adt_ds xs vs dc,
    Forall2 (STEPS adt_ds) xs vs
    -> Forall wnfX vs
    -> STEPS adt_ds (XCon dc xs) (XCon dc vs).
Proof.
(*  intros xs vs dc HS HW. *)
(*  lets HC: make_chain HS HW. *)
(*   eapply steps_wnfX. *)

(*  clear HS. clear HW. *)
(*  induction HC; auto. *)
(*   eapply (EsAppend (XCon dc (C x)) (XCon dc (C v))); auto. *)
(*   eapply steps_context_XCon; auto. *)
(* Qed. *)
Admitted.

(********************************************************************)
(* Left linearised multi-step evaluation
   As opposed to STEPS, this version provides a single step at a time
   and does not have an append constructor. This is convenient
   when converting small-step evaluations to big-step, via the
   eval_expansion lemma. *)
Inductive STEPSL : adt_defs -> exp -> exp -> Prop :=
 | EslNone
   : forall adt_ds x1,
     STEPSL adt_ds x1 x1

 | EslCons
   : forall adt_ds x1 x2 x3,
     STEP adt_ds x1 x2 -> STEPSL adt_ds x2 x3
   -> STEPSL adt_ds x1 x3.

Hint Constructors STEPSL.


(* Transitivity of left linearised multi-step evaluation.
   We use this when "flattening" a big step evaluation to the
   small step one. *)
Lemma stepsl_trans
  : forall adt_ds x1 x2 x3,
    STEPSL adt_ds x1 x2 -> STEPSL adt_ds x2 x3
 -> STEPSL adt_ds x1 x3.
Proof.
(*  intros x1 x2 x3 H1 H2. *)
(*  induction H1; eauto. *)
(* Qed. *)
Admitted.

(* Linearise a regular multi-step evaluation.
   This flattens out all the append constructors, leaving us with
   a list of individual transitions. *)
Lemma stepsl_of_steps
  : forall adt_ds x1 x2,
    STEPS adt_ds x1 x2
    -> STEPSL adt_ds x1 x2.
Proof.
(*  intros x1 x2 HS. *)
(*  induction HS;  *)
(*   eauto using stepsl_trans. *)
(* Qed. *)
Admitted.
