
Require Export FiatFormal.Language.Ty.
Require Export FiatFormal.Language.Def.


(* Expressions *)
Inductive exp : Type :=
 (* Functions *)
 | XVar   : nat -> exp
 | XLam   : ty  -> exp -> exp
 | XFix : ty -> ty -> exp -> exp
 | XApp   : exp -> exp -> exp

 (* Data Types *)
 | XCon   : datacon -> list exp -> exp
 | XMatch : exp     -> list alt -> exp

 (* Choice and ADTs *)
 | XChoice : ty -> list exp -> fiatpred -> exp (* TODO: change other definitions to match *)
 (* | XCall   : ty -> nat -> list exp -> exp *)

 (* Alternatives *)
with alt     : Type :=
     | AAlt   : datacon -> list ty  -> exp -> alt
with fiatpred : Type :=
     | FiatPred : forall t1, (tyDenote t1 -> Prop) -> fiatpred.


Inductive myListPred : list nat -> Prop :=
| C0 : myListPred (0 :: nil)
| C1 : forall l1, myListPred l1 -> myListPred (2 :: l1).

(* Eval compute in (FiatPred (TCon (TyConData 2))). (* typing judgement does not evaluate "tyDenote" *) *)

Check (XChoice (TCon (TyConData 0)) ((XVar 1) :: nil) (FiatPred (TCon (TyConData 2)) myListPred)).


Fixpoint funTy_To_TyList (t : ty) : list ty :=
  match t with
  | TCon tc1 => nil :> (TCon tc1)
  | TFun t1 t2 => funTy_To_TyList t1 ++ funTy_To_TyList t2
  | TAdt ac1 => nil :> (TAdt ac1)
  end.

Fixpoint Predtypes (fp : fiatpred) : list ty :=
  match fp with
  | FiatPred t1 pr => funTy_To_TyList t1
  end.

Hint Constructors exp.
Hint Constructors alt.
Hint Constructors fiatpred.

Inductive Xhas_choice : exp -> Prop :=
| HC_XLam : forall t1 x1, Xhas_choice x1 -> Xhas_choice (XLam t1 x1)
| HC_XFix : forall t1 t2 x1, Xhas_choice x1 -> Xhas_choice (XFix t1 t2 x1)
| HC_XApp1 : forall x1 x2, Xhas_choice x1 -> Xhas_choice (XApp x1 x2)
| HC_XApp2 : forall x1 x2, Xhas_choice x2 -> Xhas_choice (XApp x1 x2)
| HC_XCon : forall dc le, Exists (Xhas_choice) le -> Xhas_choice (XCon dc le)
| HC_XMatch : forall x1 la, Exists (Ahas_choice) la -> Xhas_choice (XMatch x1 la)
| HC_XChoice : forall t1 le fp, Xhas_choice (XChoice t1 le fp)
with Ahas_choice : alt -> Prop :=
     | HC_AAlt : forall dc lt x1, Xhas_choice x1 -> Ahas_choice (AAlt dc lt x1).

Check FiatPred (TFun (TCon (TyConData O)) (TCon (TyConData 1))).

(* TODO: decide if this is useful given "wfX" in Exp.v*)
Inductive wf_choice : exp -> Prop :=
| WF_XChoice : forall t11 fp xs, get 0 (Predtypes fp) = Some t11
                            -> length (skipn 1 (Predtypes fp)) = length xs
                            -> wf_choice (XChoice t11 xs fp).

(********************************************************************)
(* Mutual induction principle for expressions.
   As expressions are indirectly mutually recursive with lists,
   Coq's Combined scheme command won't make us a strong enough
   induction principle, so we need to write it out by hand. *)
Theorem exp_mutind
 : forall
    (PX : exp -> Prop)
    (PA : alt -> Prop)
    (* (PF : fiatpred -> Prop) *)
 ,  (forall n,                                PX (XVar n))
    -> (forall t  x1,   PX x1                 -> PX (XLam t x1))
    -> (forall t1 t2 x1, PX x1 -> PX (XFix t1 t2 x1))
 -> (forall x1 x2,   PX x1 -> PX x2        -> PX (XApp x1 x2))
 -> (forall dc xs,            Forall PX xs -> PX (XCon dc xs))
 -> (forall x  aa,   PX x  -> Forall PA aa -> PX (XMatch x aa))
 -> (forall dc ts x, PX x                  -> PA (AAlt dc ts x))

 (* TODO: show ben  *)
 (* -> (forall t1 xs fp, PF fp -> Forall PX xs -> PX (XChoice t1 xs fp)) *)
 (* -> (forall t1 pr, PF (FiatPred t1 pr)) *)
 -> (forall t1 xs fp, PX (XChoice t1 xs fp))

 ->  forall x, PX x.
Proof.
 intros PX PA.
 intros var lam xfix app con xmatch alt choice.
 refine (fix  IHX x : PX x := _
           with IHA a : PA a := _
         for  IHX).

 (* expressions *)
 case x; intros.

 Case "XVar".
  apply var.

 Case "XLam".
  apply lam.
   apply IHX.

   Case "XFix".
   apply xfix.
   apply IHX.

 Case "XApp".
  apply app.
   apply IHX.
   apply IHX.

 Case "XCon".
 apply con.
 induction l; intuition.

 Case "XMatch".
  apply xmatch.
   apply IHX.
   induction l; intuition.

   Case "XChoice".
   apply choice.

 (* alternatives *)
 case a; intros.

 Case "XAlt".
  apply alt.
   apply IHX.
Qed.


(* ORIG *)
(* Theorem exp_mutind *)
(*  : forall *)
(*     (PX : exp -> Prop) *)
(*     (PA : alt -> Prop) *)
(*  ,  (forall n,                                PX (XVar n)) *)
(*  -> (forall t  x1,   PX x1                 -> PX (XLam t x1)) *)
(*  -> (forall x1 x2,   PX x1 -> PX x2        -> PX (XApp x1 x2)) *)
(*  -> (forall dc xs,            Forall PX xs -> PX (XCon dc xs)) *)
(*  -> (forall x  aa,   PX x  -> Forall PA aa -> PX (XCase x aa)) *)
(*  -> (forall dc ts x, PX x                  -> PA (AAlt dc ts x)) *)
(*  ->  forall x, PX x. *)
(* Proof. *)
(*  intros PX PA. *)
(*  intros var lam app con case alt. *)
(*  refine (fix  IHX x : PX x := _ *)
(*          with IHA a : PA a := _ *)
(*          for  IHX). *)

(*  (* expressions *) *)
(*  case x; intros. *)

(*  Case "XVar". *)
(*   apply var. *)

(*  Case "XLam". *)
(*   apply lam. *)
(*    apply IHX. *)

(*  Case "XApp". *)
(*   apply app. *)
(*    apply IHX. *)
(*    apply IHX. *)

(*  Case "XCon". *)
(*   apply con. *)
(*    induction l; intuition. *)

(*  Case "XCase". *)
(*   apply case. *)
(*    apply IHX. *)
(*    induction l; intuition. *)

(*  (* alternatives *) *)
(*  case a; intros. *)

(*  Case "XAlt". *)
(*   apply alt. *)
(*    apply IHX. *)
(* Qed. *)
