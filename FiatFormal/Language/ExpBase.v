(* Thoughts/Qs: *)
(*
   - how should I handle product types in ADT signatures? Define
      FiatProdType and use it
   - seems a more precise treatment of Fiat would have explicit
      existential types? Yes, but very tedious
*)

(* General TODO:
   - Remove XLam and everything related
 *)

Require Export FiatFormal.Language.Ty.
Require Export FiatFormal.Language.Alg.

(* Expressions *)
Inductive exp : Type :=

 (* Functions *)
 | XVar   : nat -> exp
 (* | XLam   : ty  -> exp -> exp *)
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
     | FPred : predcon -> exp -> fpred.


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
Inductive Xhas_choice : adt_defs -> exp -> Prop :=
(* | HC_XLam : forall adt_ds t1 x1, Xhas_choice adt_ds x1 -> Xhas_choice adt_ds (XLam t1 x1) *)
| HC_XFix : forall adt_ds t1 t2 x1, Xhas_choice adt_ds x1 -> Xhas_choice adt_ds (XFix t1 t2 x1)
| HC_XApp1 : forall adt_ds x1 x2, Xhas_choice adt_ds x1 -> Xhas_choice adt_ds (XApp x1 x2)
| HC_XApp2 : forall adt_ds x1 x2, Xhas_choice adt_ds x2 -> Xhas_choice adt_ds (XApp x1 x2)
| HC_XCon : forall adt_ds dc le, Exists (Xhas_choice adt_ds) le -> Xhas_choice adt_ds (XCon dc le)
| HC_XMatchX : forall adt_ds x1 la, Xhas_choice adt_ds x1 -> Xhas_choice adt_ds (XMatch x1 la)
| HC_XMatchA : forall adt_ds x1 la, Exists (Ahas_choice adt_ds) la -> Xhas_choice adt_ds (XMatch x1 la)
| HC_XChoice : forall adt_ds t1 le fp, Xhas_choice adt_ds (XChoice t1 le fp)
| HC_XCallArgs : forall adt_ds ac n xs, (* DONE: add constructor for case where choice is in method body *)
    Exists (Xhas_choice adt_ds) xs
    -> Xhas_choice adt_ds (XCall ac n xs)
| HC_XCallBody : forall adt_ds ac n xs xbody,
    getADTBody ac n adt_ds = Some xbody
    -> Xhas_choice adt_ds xbody
    -> Xhas_choice adt_ds (XCall ac n xs)
with Ahas_choice : adt_defs -> alt -> Prop :=
     | HC_AAlt : forall adt_ds dc lt x1, Xhas_choice adt_ds x1 -> Ahas_choice adt_ds (AAlt dc lt x1).
Hint Constructors Xhas_choice.

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
    (PF : fpred -> Prop)
 ,  (forall n,                                PX (XVar n))
    (* -> (forall t  x1,   PX x1                 -> PX (XLam t x1)) *)
    -> (forall t1 t2 x1, PX x1 -> PX (XFix t1 t2 x1))
 -> (forall x1 x2,   PX x1 -> PX x2        -> PX (XApp x1 x2))
 -> (forall dc xs,            Forall PX xs -> PX (XCon dc xs))
 -> (forall x  aa,   PX x  -> Forall PA aa -> PX (XMatch x aa))
 -> (forall dc ts x, PX x                  -> PA (AAlt dc ts x))

 -> (forall t1 xs fp, PF fp -> Forall PX xs -> PX (XChoice t1 xs fp)) (* TODO *)
 -> (forall pc x, PX x -> PF (FPred pc x))
 -> (forall ac n xs,  Forall PX xs -> PX (XCall ac n xs)) (* TODO: I expect
 -> this to be too weak *)

 ->  forall x, PX x.
Proof.
 intros PX PA PF.
 intros var xfix app con xmatch alt choice fpre call.
 refine (fix  IHX x : PX x := _
           with IHA a : PA a := _
           with IHF f : PF f := _
                                  for  IHX).

 (* expressions *)
 case x; intros.

 Case "XVar".
  apply var.

 (* Case "XLam". *)
 (*  apply lam. *)
 (*   apply IHX. *)

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
   apply IHF.
   induction l; intuition.

   Case "XCall".
   apply call.
   induction l; intuition.

 (* alternatives *)
 case a; intros.

 Case "XAlt".
  apply alt.
   apply IHX.

   (* fpreds *)
   case f; intros.
   Case "XFPred".
   apply fpre.
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



Lemma getADTSigInDefs_pmk : forall ac n adt_ds s d,
    getADTSig ac n adt_ds = Some s
    -> getADTDef ac adt_ds = Some d.
Proof.
  intros.
  gen s n ac d.
  induction adt_ds; intros; rip; burn.
  - destruct ac. simpl in *; nope.
  - destruct ac. simpl in H.
Admitted.

Lemma getADTSigInCons_pmk : forall ac n adt_ds s,
    getADTSig ac n adt_ds = Some s
    -> In ac (getADTCons adt_ds).
Proof.
  intros.
  gen s n ac.
  induction adt_ds; intros; rip; burn.
  - destruct ac. simpl in *; nope.
  - destruct ac. simpl in H.
    destruct a. destruct a.
    split_match; burn. simpl.
    left. symmetry in HeqH0.
    apply beq_nat_true in HeqH0; subst; auto.
Qed.