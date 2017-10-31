
Require Import FiatFormal.Language.SubstTypeExp.
Require Import FiatFormal.Language.SubstExpExp.
Require Export FiatFormal.Language.Exp.

Require Export FiatFormal.Language.Context.

(* TODO: consider implications of below definition...
         esp. that nary function application requires
         value of function but only wnfX of args *)

(*  Evaluation contexts for expressions.
    This describes a place in the exp AST where the sub-expression
    there is able to take an evaluation step *)
Inductive exp_ctx : (exp -> exp) -> Prop :=

 (* Left of an application *)
 | XcApp1
   : forall x2,
     exp_ctx (fun xx => XApp xx x2)

 (* The right of an application can step only when the left is
    already a value. *)
 | XcApp2
   : forall v1,
     value v1
     -> exp_ctx (fun xx => XApp v1 xx)

 | XcCon
   : forall dc C,
     exps_ctx wnfX C
     -> exp_ctx (fun xx => XCon dc (C xx))

 (* We need to reduce the discriminant of a match to a value. *)
 | XcMatch
   : forall alts,
     exp_ctx (fun xx => XMatch xx alts)

 | XcChoice
   : forall t pc C,
     exps_ctx wnfX C
     -> exp_ctx (fun xx => XChoice t pc (C xx))

 | XcTup
   : forall C,
     exps_ctx wnfX C
     -> exp_ctx (fun xx => XTup (C xx))

 | XcProj
   : forall n,
     exp_ctx (fun xx => XProj n xx)

 | XcNApp1
   : forall xs,
     exp_ctx (fun xx => XNApp xx xs)

 | XcNApp2
   : forall v1 C,
     value v1
     -> exps_ctx wnfX C
     -> exp_ctx (fun xx => XNApp v1 (C xx)).

Hint Constructors exp_ctx.

Inductive STEP : exp -> exp -> Prop :=
 (* Step some sub-expression in an evaluation context *)
 | EsContext
   : forall C x x',
     exp_ctx C
     -> STEP x x'
     -> STEP (C x) (C x')

 | EsFixApp
   : forall t11 t22 x12 v2,
     wnfX v2
     -> STEP (XApp (XFix t11 t22 x12) v2)
            (substXX 0 (XFix t11 t22 x12) (substXX 0 v2 x12))

 | EsTupProj
   : forall vs n v',
     Forall wnfX vs
     -> get n vs = Some v'
     -> STEP (XProj n (XTup vs)) v'

 | EsNFunApp
   : forall x vs ts,
     Forall wnfX vs
     -> STEP (XNApp (XNFun ts x) vs)
            (substXXs 0 vs x)

 (* Match branching. *)
 | EsMatchAlt
   : forall dc ts vs alts x,
     Forall wnfX vs
     -> getAlt dc alts = Some (AAlt dc ts x)
     -> STEP (XMatch (XCon dc vs) alts)
            (substXXs 0 vs x)

 | EsChoice
   : forall ds t pfc vs v tsArgs prc proofs,
     Forall wnfX vs
     (* get definition of proof constructor *)
     -> getProofDef pfc ds = Some (DefProof pfc tsArgs (TProp prc))
     (* get definition of proposition that choice proof must construct *)
     -> getPropDef prc ds = Some (DefPropType prc proofs)
     (* check that choice's proof inhabits the proposition it claims to inhabit *)
     -> In pfc proofs
     -> get 0 vs = Some v
     (* Note: this stepping rule admits many steps we don't want *)
     -> STEP (XChoice t pfc vs) v.

Hint Constructors STEP.

Lemma step_context_XCon_exists
 :  forall  C x dc
 ,  exps_ctx wnfX C
 -> (exists x', STEP x x')
 -> (exists x', STEP (XCon dc (C x)) (XCon dc (C x'))).
Proof.
 intros C x dc HC HS.
 shift x'.
 eapply (EsContext (fun xx => XCon dc (C xx))); auto.
Qed.

Lemma step_context_XTup_exists
  : forall C x,
    exps_ctx wnfX C
    -> (exists x', STEP x x')
    -> (exists x', STEP (XTup (C x)) (XTup (C x'))).
Proof.
 intros C x HC HS.
 shift x'.
 eapply (EsContext (fun xx => XTup (C xx))); auto.
Qed.

(* Lemma step_context_XNApp_exists *)
(*   : forall C x xx ts, *)
(*     exps_ctx wnfX C *)
(*     -> (exists x', STEP x x') *)
(*     -> (exists x', STEP (XNApp (XNFun ts xx) (C x)) (XNApp (XNFun ts xx) (C x'))). *)
(* Proof. *)
(*  intros C x xx ts HC HS. *)
(*  shift x'. *)
(*  eapply (EsContext (fun xx' => XNApp (XNFun ts xx) (C xx'))); eauto. *)
(*  apply XcNApp2; eauto. constructor; eauto.  *)
(* Qed. *)

(* Small step program evaluation *)
Inductive STEPP : prog -> prog -> Prop :=
| SP_Prog : forall r x s p,
    (* STEPP (PLET (IADT r x s) p) (substTP 0 r (substXP 0 x p)) *)
    STEPP (PLET (IADT r x s) p) (substXP 0 x (substTP 0 r p))
| SP_Exp  : forall x x',
    STEP x x'
    -> STEPP (PEXP x) (PEXP x').

Hint Constructors STEPP.

(********************************************************************)
(* Multi-step evaluation.
   A sequence of small step transitions.
   As opposed to STEPSL, this version has an append constructor
   ESAppend that makes it easy to join two evaluations together.
   We use this when converting big-step evaluations to small-step.
 *)
Inductive STEPS : exp -> exp -> Prop :=

 (* After no steps, we get the same exp.
    We need this constructor to match the EVDone constructor
    in the big-step evaluation, so we can convert between big-step
    and multi-step evaluations. *)
 | ESNone
   :  forall x1
   ,  STEPS x1 x1

 (* Take a single step. *)
 | ESStep
   :  forall x1 x2
   ,  STEP  x1 x2
   -> STEPS x1 x2

 (* Combine two evaluations into a third. *)
 | ESAppend
   :  forall x1 x2 x3
   ,  STEPS x1 x2 -> STEPS x2 x3
   -> STEPS x1 x3.

Hint Constructors STEPS.


(* Context lemmas
   These help when proving something about a reduction in a given
   context. They're all trivial.
   TODO: Define contexts directly like in the Simple proof.
 *)
(* Lemma steps_app1 *)
(*  :  forall x1 x1' x2 *)
(*  ,  STEPS x1 x1' *)
(*  -> STEPS (XApp x1 x2) (XApp x1' x2). *)
(* Proof. *)
(*  intros. induction H; eauto. *)
(* Qed. *)
(* Hint Resolve steps_app1. *)


(* Lemma steps_app2 *)
(*  :  forall v1 x2 x2' *)
(*  ,  value v1 *)
(*  -> STEPS x2 x2' *)
(*  -> STEPS (XApp v1 x2) (XApp v1 x2'). *)
(* Proof. *)
(*  intros. induction H0; eauto. *)
(* Qed. *)
(* Hint Resolve steps_app2. *)


(* Lemma steps_APP1 *)
(*  :  forall x1 x1' t2 *)
(*  ,  STEPS x1 x1' *)
(*  -> STEPS (XAPP x1 t2) (XAPP x1' t2). *)
(* Proof. *)
(*  intros. induction H; eauto. *)
(* Qed. *)


(********************************************************************)
(* Left linearised multi-step evaluation
   As opposed to STEPS, this version provides a single step at a time
   and does not have an append constructor. This is convenient
   when converting a small-step evaluations to big-step, via the
   eval_expansion lemma.
 *)
Inductive STEPSL : exp -> exp -> Prop :=

 | ESLNone
   : forall x1
   , STEPSL x1 x1

 | ESLCons
   :  forall x1 x2 x3
   ,  STEP   x1 x2 -> STEPSL x2 x3
   -> STEPSL x1 x3.

Hint Constructors STEPSL.


(* Transitivity of left linearised multi-step evaluation.
   We use this when "flattening" a big step evaluation to the
   small step one.
 *)
Lemma stepsl_trans
 :  forall x1 x2 x3
 ,  STEPSL x1 x2 -> STEPSL x2 x3
 -> STEPSL x1 x3.
Proof.
 intros.
 induction H.
  eauto.
  eapply ESLCons. eauto. eauto.
Qed.


(* Linearise a regular multi-step evaluation.
   This flattens out all the append constructors, leaving us with
   a list of individual transitions.
 *)
Lemma stepsl_of_steps
 :  forall x1 x2
 ,  STEPS  x1 x2
 -> STEPSL x1 x2.
Proof.
 intros.
 induction H.
  auto.
  eauto.
  eapply stepsl_trans; eauto.
Qed.
