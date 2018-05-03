
Require Import FiatFormal.Language.SubstTypeExp.
Require Import FiatFormal.Language.SubstExpExp.
Require Import FiatFormal.Language.Exp.

Require Export FiatFormal.Data.Context.
Require Export FiatFormal.Data.Chain.


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

(* -- Uncomment below for CBV -- *)
 (* The right of an application can step only when the left is
    already a value. *)
 (* | XcApp2 *)
 (*   : forall v1, *)
 (*     value v1 *)
 (*     -> exp_ctx (fun xx => XApp v1 xx) *)

 | XcCon
   : forall dc C,
     exps_ctx wnfX C
     -> exp_ctx (fun xx => XCon dc (C xx))

 (* We need to reduce the discriminant of a match to a value. *)
 | XcMatch
   : forall alts,
     exp_ctx (fun xx => XMatch xx alts)

(* -- Uncomment below for strict evaluation of choice terms -- *)
 (* | XcChoice *)
 (*   : forall t pc C, *)
 (*     exps_ctx wnfX C *)
 (*     -> exp_ctx (fun xx => XChoice t pc (C xx)) *)

(* -- Uncomment below for strict evaluation of tuples -- *)
 (* | XcTup *)
 (*   : forall C, *)
 (*     exps_ctx wnfX C *)
 (*     -> exp_ctx (fun xx => XTup (C xx)) *)

 | XcProj
   : forall n,
     exp_ctx (fun xx => XProj n xx)

 | XcNApp1
   : forall xs,
     exp_ctx (fun xx => XNApp xx xs)

(* -- Uncomment below for strict evaluation of n-ary functions -- *)
 (* | XcNApp2 *)
 (*   : forall v1 C, *)
 (*     value v1 *)
 (*     -> exps_ctx wnfX C *)
 (*     -> exp_ctx (fun xx => XNApp v1 (C xx)) *)
.
Hint Constructors exp_ctx.
