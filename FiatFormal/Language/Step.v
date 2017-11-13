
Require Import FiatFormal.Language.SubstTypeExp.
Require Import FiatFormal.Language.SubstExpExp.
Require Export FiatFormal.Language.Exp.
Require Import FiatFormal.Language.TyJudge.

Require Export FiatFormal.Language.StepContext.


Inductive STEP
          (ProofBuilder : propcon -> list exp -> Prop)
          (ds : defs)
          (ProofBuilderOK : forall ke te pc xs ts,
              ProofBuilder pc xs
              -> getPropDef pc ds = Some (DefProp pc ts)
              -> Forall2 (TYPE ds ke te) xs ts)
  : exp -> exp -> Prop :=
 (* Step some sub-expression in an evaluation context *)
 | EsContext
   : forall C x x',
     exp_ctx C
     -> STEP ProofBuilder ds ProofBuilderOK x x'
     -> STEP ProofBuilder ds ProofBuilderOK
            (C x) (C x')

 | EsFixApp
   : forall t11 t22 x12 v2,
     wnfX v2
     -> STEP ProofBuilder ds ProofBuilderOK
            (XApp (XFix t11 t22 x12) v2)
            (substXX 0 (XFix t11 t22 x12) (substXX 0 v2 x12))

 | EsTupProj
   : forall vs n v',
     Forall wnfX vs
     -> get n vs = Some v'
     -> STEP ProofBuilder ds ProofBuilderOK
            (XProj n (XTup vs)) v'

 | EsNFunApp
   : forall x vs ts,
     Forall wnfX vs
     -> STEP ProofBuilder ds ProofBuilderOK
            (XNApp (XNFun ts x) vs)
            (substXXs 0 vs x)

 (* Match branching. *)
 | EsMatchAlt
   : forall dc ts vs alts x,
     Forall wnfX vs
     -> getAlt dc alts = Some (AAlt dc ts x)
     -> STEP ProofBuilder ds ProofBuilderOK
            (XMatch (XCon dc vs) alts)
            (substXXs 0 vs x)

 | EsChoice
   : forall pc v vs t,
     Forall wnfX (v :: vs)
    -> ProofBuilder pc (v :: vs)
    -> STEP ProofBuilder ds ProofBuilderOK (XChoice t pc vs) v.
Hint Constructors STEP.

Lemma step_context_XCon_exists
  : forall pb ds pbOK C x dc,
    exps_ctx wnfX C
    -> (exists x', STEP pb ds pbOK x x')
    -> (exists x', STEP pb ds pbOK (XCon dc (C x)) (XCon dc (C x'))).
Proof.
 intros pb ds pbOK C x dc HC HS.
 shift x'.
 eapply (EsContext pb ds pbOK (fun xx => XCon dc (C xx))); auto.
Qed.

Lemma step_context_XTup_exists
  : forall pb ds pbOK C x,
    exps_ctx wnfX C
    -> (exists x', STEP pb ds pbOK x x')
    -> (exists x', STEP pb ds pbOK (XTup (C x)) (XTup (C x'))).
Proof.
 intros pb ds pbOK C x HC HS.
 shift x'.
 eapply (EsContext pb ds pbOK (fun xx => XTup (C xx))); auto.
Qed.

(* Small step program evaluation *)
Inductive STEPP
          (ProofBuilder : propcon -> list exp -> Prop)
          (ds : defs)
          (ProofBuilderOK : forall ke te pc xs ts,
              ProofBuilder pc xs
              -> getPropDef pc ds = Some (DefProp pc ts)
              -> Forall2 (TYPE ds ke te) xs ts)
  : prog -> prog -> Prop :=
| SP_Prog : forall r x s p,
    (* STEPP (PLET (IADT r x s) p) (substTP 0 r (substXP 0 x p)) *)
    STEPP
      ProofBuilder ds ProofBuilderOK
      (PLET (IADT r x s) p)
      (substXP 0 x (substTP 0 r p))
| SP_Exp : forall x x',
    STEP
      ProofBuilder ds ProofBuilderOK
      x x'
    -> STEPP
        ProofBuilder ds ProofBuilderOK
        (PEXP x) (PEXP x').
Hint Constructors STEPP.


(* -------------------------MULTI-STEP built upon SimpleData--------------------------------- *)

(* Multi-step evaluation
   A sequence of small step transitions.
   As opposed to STEPSL, this version has an append constructor
   ESAppend that makes it easy to join two evaluations together.
   We use this when converting big-step evaluations to small-step. *)
Inductive STEPS
  (ProofBuilder : propcon -> list exp -> Prop)
    (ds : defs)
    (ProofBuilderOK : forall ke te pc xs ts,
        ProofBuilder pc xs
        -> getPropDef pc ds = Some (DefProp pc ts)
        -> Forall2 (TYPE ds ke te) xs ts)
    : exp -> exp -> Prop :=

 (* After no steps, we get the same exp.
    We need this constructor to match the EVDone constructor
    in the big-step evaluation, so we can convert between big-step
    and multi-step evaluations. *)
 | EsNone
   : forall x1,
     STEPS ProofBuilder ds ProofBuilderOK x1 x1

 (* Take a single step. *)
 | EsStep
   : forall x1 x2,
     STEP ProofBuilder ds ProofBuilderOK x1 x2
     -> STEPS ProofBuilder ds ProofBuilderOK x1 x2

 (* Combine two evaluations into a third. *)
 | EsAppend
   : forall x1 x2 x3,
     STEPS ProofBuilder ds ProofBuilderOK x1 x2
     -> STEPS ProofBuilder ds ProofBuilderOK x2 x3
     -> STEPS ProofBuilder ds ProofBuilderOK x1 x3.
Hint Constructors STEPS.

Inductive STEPSP
  (ProofBuilder : propcon -> list exp -> Prop)
    (ds : defs)
    (ProofBuilderOK : forall ke te pc xs ts,
        ProofBuilder pc xs
        -> getPropDef pc ds = Some (DefProp pc ts)
        -> Forall2 (TYPE ds ke te) xs ts)
    : prog -> prog -> Prop :=

 | EsNoneP
   : forall p,
     STEPSP ProofBuilder ds ProofBuilderOK p p
 | EsStepP
   : forall p1 p2,
     STEPP ProofBuilder ds ProofBuilderOK p1 p2
     -> STEPSP ProofBuilder ds ProofBuilderOK p1 p2
 | EsAppendP
   : forall p1 p2 p3,
     STEPSP ProofBuilder ds ProofBuilderOK p1 p2
     -> STEPSP ProofBuilder ds ProofBuilderOK p2 p3
     -> STEPSP ProofBuilder ds ProofBuilderOK p1 p3.
Hint Constructors STEPSP.


Ltac nopes := nope; nope.

(* Stepping a wnf doesn't change it. *)
Lemma step_wnfX
  : forall pb ds pbOK x v,
    wnfX x -> STEP pb ds pbOK x v -> v = x.
Proof.
 intros pb ds pbOK x v HW HS.
 induction HS; nope.
  destruct H; nopes.

  + Case "XCon dc (C x)".
    inverts HW.
    assert (wnfX x).
    eapply exps_ctx_Forall; eauto.
    rrwrite (x' = x). auto.
  + Case "XTup".
    inverts HW.
    assert (wnfX x).
    eapply exps_ctx_Forall; eauto.
    rrwrite (x' = x). auto.
Qed.


(* Multi-step evaluating a wnf doesn't change it. *)
Lemma steps_wnfX
  : forall pb ds pbOK x v,
    wnfX x -> STEPS pb ds pbOK x v -> v = x.
Proof.
 intros pb ds pbOK x v HW HS.
 induction HS; nopes.
  Case "EsStep".
   eapply step_wnfX; eauto.

  Case "EsAppend".
   have (x2 = x1). subst. auto.
Qed.


(* Multi-step evaluation in a context. *)
Lemma steps_context
  : forall pb ds pbOK C x1 x1',
    exp_ctx C
    -> STEPS pb ds pbOK x1 x1'
    -> STEPS pb ds pbOK (C x1) (C x1').
Proof.
 intros pb ds pbOK C x1 x1' HC HS.
 induction HS; eauto.
Qed.


(* Multi-step evaluation of a data constructor argument. *)
Lemma steps_context_XCon
  : forall pb ds pbOK C x v dc,
    exps_ctx wnfX C
    -> STEPS pb ds pbOK x v
 -> STEPS pb ds pbOK (XCon dc (C x)) (XCon dc (C v)).
Proof.
 intros pb ds pbOK C x v dc HC HS.
 induction HS; auto.

 Case "XCon".
  lets D: EsContext XcCon; eauto.
  eauto.
Qed.


Lemma steps_in_XCon
  : forall pb ds pbOK xs vs dc,
    Forall2 (STEPS pb ds pbOK) xs vs
    -> Forall wnfX vs
    -> STEPS pb ds pbOK (XCon dc xs) (XCon dc vs).
Proof.
 intros pb ds pbOK xs vs dc HS HW.
 lets HC: make_chain HS HW.
  eapply steps_wnfX.

 clear HS. clear HW.
 induction HC; auto.
  eapply (EsAppend pb ds pbOK (XCon dc (C x)) (XCon dc (C v))); eauto.
  eapply steps_context_XCon; eauto.
Qed.


(********************************************************************)
(* Left linearised multi-step evaluation
   As opposed to STEPS, this version provides a single step at a time
   and does not have an append constructor. This is convenient
   when converting a small-step evaluations to big-step, via the
   eval_expansion lemma. *)
Inductive STEPSL
          (ProofBuilder : propcon -> list exp -> Prop)
          (ds : defs)
          (ProofBuilderOK : forall ke te pc xs ts,
              ProofBuilder pc xs
              -> getPropDef pc ds = Some (DefProp pc ts)
              -> Forall2 (TYPE ds ke te) xs ts)
  : exp -> exp -> Prop :=

 | EslNone
   : forall x1, STEPSL ProofBuilder ds ProofBuilderOK x1 x1

 | EslCons
   : forall x1 x2 x3,
     STEP ProofBuilder ds ProofBuilderOK x1 x2
     -> STEPSL ProofBuilder ds ProofBuilderOK x2 x3
     -> STEPSL ProofBuilder ds ProofBuilderOK x1 x3.
Hint Constructors STEPSL.

Inductive STEPSLP
          (ProofBuilder : propcon -> list exp -> Prop)
          (ds : defs)
          (ProofBuilderOK : forall ke te pc xs ts,
              ProofBuilder pc xs
              -> getPropDef pc ds = Some (DefProp pc ts)
              -> Forall2 (TYPE ds ke te) xs ts)
  : prog -> prog -> Prop :=

 | EslNoneP
   : forall p,
     STEPSLP ProofBuilder ds ProofBuilderOK p p
 | EslConsP
   : forall p1 p2 p3,
     STEPP ProofBuilder ds ProofBuilderOK p1 p2
     -> STEPSLP ProofBuilder ds ProofBuilderOK p2 p3
     -> STEPSLP ProofBuilder ds ProofBuilderOK p1 p3.
Hint Constructors STEPSLP.


(* Transitivity of left linearised multi-step evaluation.
   We use this when "flattening" a big step evaluation to the
   small step one. *)
Lemma stepsl_trans
  : forall pb ds pbOK x1 x2 x3,
    STEPSL pb ds pbOK x1 x2
    -> STEPSL pb ds pbOK x2 x3
    -> STEPSL pb ds pbOK x1 x3.
Proof.
 intros pb ds pbOK x1 x2 x3 H1 H2.
 induction H1; eauto.
Qed.


(* Linearise a regular multi-step evaluation.
   This flattens out all the append constructors, leaving us with
   a list of individual transitions. *)
Lemma stepsl_of_steps
  : forall pb ds pbOK x1 x2,
    STEPS pb ds pbOK x1 x2
    -> STEPSL pb ds pbOK x1 x2.
Proof.
 intros pb ds pbOK x1 x2 HS.
 induction HS;
  eauto using stepsl_trans.
Qed.
