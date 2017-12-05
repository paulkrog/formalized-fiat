(* Todo: *)

(*   -list method -> list ty ==> list (method * ty)
     -write refinesADT'
*)


Require Import FiatFormal.Language.Step.
Require Import FiatFormal.Language.TyJudge.

Set Printing Projections.


Definition refines (x1 x2 : exp) :=
  forall pb ds pbOK v,
    STEPS pb ds pbOK x2 v
    -> STEPS pb ds pbOK x1 v.
Definition refinesP (p1 p2 : prog) :=
  forall pb ds pbOK v,
    STEPSP pb ds pbOK p2 v
    -> STEPSP pb ds pbOK p1 v.

Definition getRepType (a : adt) :=
  match a with
  | IADT r ms ss => r
  end.
Definition getMethods (a : adt) :=
  match a with
  | IADT r ms ss => ms
  end.
Definition getSigs (a : adt) :=
  match a with
  | IADT r ms ss => ss
  end.
Definition getArity (m : method) :=
  m.(arity).
Definition getDom (m : method) :=
  m.(dom).
Definition getCod (m : method) :=
  m.(cod).
Definition getBody (m : method) :=
  m.(body).

Inductive refinesADT
           (ProofBuilder : propcon -> list exp -> Prop)
           (ds : defs)
           (ProofBuilderOK : forall ke te pc xs ts,
               ProofBuilder pc xs
               -> getPropDef pc ds = Some (DefProp pc ts)
               -> Forall2 (TYPE ds ke te) xs ts)
  : adt -> adt -> Prop :=
| CREFINE :
    forall methodsNew repNew sigsNew methodsOld repOld sigsOld,
    (exists (R : exp -> exp -> Prop),
    forall n arity dom bodyOld bodyNew cod
      v vs repNew' repsNew repsOld,
      get n methodsOld = Some (mkMethod arity dom bodyOld cod)
      -> get n methodsNew = Some (mkMethod arity dom bodyNew cod)
      -> Forall wnfX vs
      -> Forall2 R repsOld repsNew
      -> STEPS ProofBuilder ds ProofBuilderOK
              (XNApp (bodyNew) (repsNew >< vs))
              (XTup ((nil :> v) :> repNew'))
      -> (exists repOld',
          STEPS ProofBuilder ds ProofBuilderOK
                (XNApp (bodyOld) (repsOld >< vs))
                (XTup ((nil :> v) :> repOld'))
          /\ R repOld' repNew'))
          -> refinesADT ProofBuilder ds ProofBuilderOK
                        (IADT repOld methodsOld sigsOld)
                        (IADT repNew methodsNew sigsNew).

Theorem refinementSoundess : forall pb ds pbOK ao an p,
    refinesADT pb ds pbOK ao an ->
    refinesP (PLET ao p) (PLET an p).
Proof.
  unfold refinesP.
  intros.
  inverts H.
  dest H1.
Admitted.
