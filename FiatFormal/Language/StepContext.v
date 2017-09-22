
Require Import FiatFormal.Language.Exp.
Require Export FiatFormal.Data.Context.
Require Export FiatFormal.Data.Chain.


(********************************************************************)
(*  Evaluation contexts for expressions.
    This describes a place in the exp AST where the sub-expression
    there is able to take an evaluation step *)
Inductive exp_ctx : (exp -> exp) -> Prop :=

 (* The top level context names the entire expression *)
 | XcTop
   : exp_ctx  (fun x => x)

 (* Left of an application *)
 | XcApp1
   :  forall x2
   ,  exp_ctx  (fun xx => XApp xx x2)

 (* The right of an application can step only when the left is
    already a value. *)
 | XcApp2
   :  forall v1
   ,  value v1
   -> exp_ctx  (fun xx => XApp v1 xx)

 (* As the XCon constructor contains a list of sub-expressions,
    we need an additional exps_ctx context to indicate which one
    we're talking about. *)
 | XcCon
   :  forall dc C
   ,  exps_ctx wnfX C
   -> exp_ctx  (fun xx => XCon dc (C xx))

 (* We need to reduce the discriminant of a case to a value. *)
 | XcMatch
   :  forall alts
   ,  exp_ctx  (fun xx => XMatch xx alts)

 | XcPair1
   : forall x2,
     exp_ctx (fun xx => XPair xx x2)

 | XcPair2
   : forall v1,
     value v1
     -> exp_ctx (fun xx => XPair v1 xx)

 | XcFst
   : exp_ctx (fun xx => XFst xx)

 | XcSnd
   : exp_ctx (fun xx => XSnd xx)

 | XcCall
   : forall ac n C,
     exps_ctx wnfX C
     -> exp_ctx (fun xs => XOpCall ac n (C xs)).

Hint Constructors exp_ctx.
