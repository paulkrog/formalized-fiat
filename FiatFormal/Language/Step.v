
Require Import FiatFormal.Language.SubstTypeExp.
Require Import FiatFormal.Language.SubstExpExp.
Require Export FiatFormal.Language.Exp.
Require Import FiatFormal.Language.TyJudge.

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
