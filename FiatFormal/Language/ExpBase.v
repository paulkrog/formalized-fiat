(* Thoughts/Qs: *)

(* - should method bodies be typed at the point of use? i.e. as a premise
      to typing an XCall? No, let the typing entire adt be a premise
   - how should I handle product types in ADT signatures? Define
      FiatProdType and use it
   - seems a more precise treatment of Fiat would have explicit
      existential types? Yes, but very tedious *)

(* General TODO:
   - experiment with simple mutually recursive type to understand exp_mutinds that coq generates *)

Require Export FiatFormal.Language.Ty.
Require Export FiatFormal.Language.Alg.

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

 (* Choice *)
 | XChoice : ty -> list exp -> fpred -> exp
 (* ADTs *)
 | XCall   : adtcon -> nat -> list exp -> exp
 (* the nat above indexes into the list of method bodies in adt_defs *)

(* Alternatives *)
with alt     : Type :=
     | AAlt   : datacon -> list ty  -> exp -> alt

(* Predicates *)
with fpred : Type :=
     | FPred : predcon -> fpred.


Hint Constructors exp.
Hint Constructors alt.
Hint Constructors fpred.


Inductive adt_def : Type :=
(* Definition of an abstract data type *)
| DefADT
  : adtcon      (* Name of data constructor, implicitly used as a type, once defined *)
    -> Rep       (* representation type, (adtcon n) gets mapped to *)
    (*                    this type as mentioned above *)
    -> list Sig
    -> list exp
    -> adt_def.
Hint Constructors adt_def.


(* Definition environment *)
Definition adt_defs  := list adt_def.


(* Functions for looking up definitions by adtcon *)

(* Lookup the definition of a given ADT *)
Fixpoint getADTDef (ac : adtcon) (ds : adt_defs) : option adt_def :=
  match ds with
  | ds' :> DefADT ac' _ _ _ as a
    => if adtcon_beq ac ac'
      then Some a
      else getADTDef ac ds'
  | Empty => None
  end.
(* Lookup Rep type by indexing into definitions by adtcon *)
Fixpoint getADTRep (ac : adtcon) (ds : adt_defs) : option Rep :=
  match getADTDef ac ds with
  | Some (DefADT ac' r sigs xs) => Some r
  | _ => None
  end.
(* Lookup method signature by indexing into ADT def *)
Fixpoint getADTSig (ac : adtcon) (n : nat) (ds : adt_defs) : option Sig :=
  match getADTDef ac ds with
  | Some (DefADT ac' r sigs xs) => get n sigs
  | _ => None (* loss of information here, best practices in this situation? *)
  end.
(* Lookup method body by indexing into ADT def *)
Fixpoint getADTBody (ac : adtcon) (n : nat) (ds : adt_defs) : option exp :=
  match getADTDef ac ds with
  | Some (DefADT ac' r sigs xs) => get n xs
  | _ => None (* loss of information here, best practices in this situation? *)
  end.
Fixpoint getADTNumMethods (ac : adtcon) (ds : adt_defs) : option nat :=
  match getADTDef ac ds with
  | Some (DefADT ac' r sigs xs) => Some (length sigs)
  | _ => None
  end.
Fixpoint getADTSigs (ac : adtcon) (ds : adt_defs) : option (list Sig) :=
  match getADTDef ac ds with
  | Some (DefADT ac' r sigs xs) => Some sigs
  | _ => None
  end.
Fixpoint getADTBodies (ac : adtcon) (ds : adt_defs) : option (list exp) :=
  match getADTDef ac ds with
  | Some (DefADT ac' r sigs xs) => Some xs
  | _ => None
  end.
Fixpoint getRep (d : adt_def) : Rep :=
  match d with
  | DefADT ac r sigs xs => r
  end.
Fixpoint getSig (n : nat) (d : adt_def) : option Sig :=
  match d with
  | DefADT ac r sigs xs => get n sigs
  end.
Fixpoint getBody (n : nat) (d : adt_def) : option exp :=
  match d with
  | DefADT ac r sigs xs => get n xs
  end.
Fixpoint getNumMethods (d : adt_def) : nat :=
  match d with
  | DefADT ac r sigs xs => length sigs
  end.
Fixpoint getSigs (d : adt_def) : list Sig :=
  match d with
  | DefADT ac r sigs xs => sigs
  end.
Fixpoint getBodies (d : adt_def) : list exp :=
  match d with
  | DefADT ac r sigs xs => xs
  end.
Fixpoint getADTCons (ds : adt_defs) : list adtcon :=
  match ds with
  | (DefADT ac r sigs xs) :: ds' => ac :: (getADTCons ds')
  | nil => nil
  end.

(* Inductively defined "has choice" predicate *)
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


(* TODO: change this *)
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
(*  intros PX PA. *)
(*  intros var lam xfix app con xmatch alt choice. *)
(*  refine (fix  IHX x : PX x := _ *)
(*            with IHA a : PA a := _ *)
(*          for  IHX). *)

(*  (* expressions *) *)
(*  case x; intros. *)

(*  Case "XVar". *)
(*   apply var. *)

(*  Case "XLam". *)
(*   apply lam. *)
(*    apply IHX. *)

(*    Case "XFix". *)
(*    apply xfix. *)
(*    apply IHX. *)

(*  Case "XApp". *)
(*   apply app. *)
(*    apply IHX. *)
(*    apply IHX. *)

(*  Case "XCon". *)
(*  apply con. *)
(*  induction l; intuition. *)

(*  Case "XMatch". *)
(*   apply xmatch. *)
(*    apply IHX. *)
(*    induction l; intuition. *)

(*    Case "XChoice". *)
(*    apply choice. *)

(*  (* alternatives *) *)
(*  case a; intros. *)

(*  Case "XAlt". *)
(*   apply alt. *)
(*    apply IHX. *)
(* Qed. *)
Admitted.

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
