(* Todo: *)

(*   -list method -> list ty ==> list (method * ty)
     -make defs a parameter to all typing relations
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

(* Definition wfRefinement (aOld aNew : adt) :=. *)

(* Inductive refinesADT'  *)
(*            (ProofBuilder : propcon -> list exp -> Prop) *)
(*            (ds : defs) *)
(*            (ProofBuilderOK : forall ke te pc xs ts, *)
(*                ProofBuilder pc xs *)
(*                -> getPropDef pc ds = Some (DefProp pc ts) *)
(*                -> Forall2 (TYPE ds ke te) xs ts) *)
(*   : adt -> adt -> Prop := *)
(* |  => *)
(*    refinesADT' _ _ _ IADT _____ IADT ______ *)

Definition refinesADT
           (ProofBuilder : propcon -> list exp -> Prop)
           (ds : defs)
           (ProofBuilderOK : forall ke te pc xs ts,
               ProofBuilder pc xs
               -> getPropDef pc ds = Some (DefProp pc ts)
               -> Forall2 (TYPE ds ke te) xs ts)
           (aOld aNew : adt) :=


  forall repTypeOld repTypeNew,
    getRepType aOld = repTypeOld
    -> getRepType aNew = repTypeNew
    -> exists (absRel : exp -> exp -> Prop), (* This is not correct? *)
      forall n mOld mNew
        methodsNew methodsOld
        mDomNew mDomOld
        arityNew arityOld
        repsNew repsOld
        bodyNew bodyOld
        vs,

        getMethods aNew = methodsNew
        -> getMethods aOld = methodsOld
        -> length methodsNew = length methodsOld
        -> get n methodsNew = Some mNew
        -> get n methodsOld = Some mOld
        -> getDom mNew = mDomNew
        -> getDom mOld = mDomOld
        -> mDomNew = mDomOld
        -> getArity mOld = arityOld
        -> getArity mNew = arityNew
        -> arityNew = arityOld
        -> getBody mNew = bodyNew
        -> getBody mOld = bodyOld

        -> length vs = length mDomNew
        -> Forall wnfX vs
        -> length repsNew = arityNew
        -> Forall2 (absRel) repsOld repsNew

        -> forall v repNew',
            STEPS ProofBuilder ds ProofBuilderOK
                  (XNApp (bodyNew) (repsNew >< vs))
                  (XTup ((nil :> v) :> repNew'))
            -> exists repOld',
              STEPS ProofBuilder ds ProofBuilderOK
                    (XNApp (bodyOld) (repsOld >< vs))
                    (XTup ((nil :> v) :> repOld'))
              /\ absRel repOld' repNew'.

(* Definition getArity (ts : list ty) (x : exp) (m : (XNFun ts x)) := *)
(*   length ts. *)

(* Definition getFuns := term. *)

(* Definition getOps (a : adt) : list (option exp) := *)
(*   match a with *)
(*   | IADT r x s => match x with *)
(*                  | XTup xs => match xs with *)
(*                                | ((XNFun ts x) as f) :: xs' => Some f :: (getOps a *)
(*                                | _ :: xs' => *)
(*                                | nil => nil *)
(*                                end *)
(*                  | _ => nil *)
(*                                                                          end. *)

(* Definition getMethods (a : adt) : list method := *)
(* match a with *)
(* | IADT r ms ts => ms *)
(* end. *)

(* Definition getArity (m : method) := *)
(* match m with. *)

(* Definition refinesADT (aOld aNew : adt) := *)
(*   getBody aOld = (XTup ms) *)
(*   -> Forall2 (fun m => exists ts x, m = (XNFun ts x)) ms *)
(*   exists (absRel : getRepType aOld -> getRepType aNew -> Prop), *)
(*     -> length ms = n *)
(*     -> *)

(*   forall methodsOld methodsNew methodOld methodNew i numMethods, *)
(*     getMethods aOld = methodsOld *)
(*     -> getMethods aNew = methodsNew *)
(*     -> length methodsOld = length methodsNew *)
(*     -> get i methodsNew = methodNew *)
(*     -> get i methodsOld = methodOld *)
(*     -> forall (reps_o : list (getRepType aOld)) (reps_n : list (getRepType aNew)) *)
(*         (arity : nat) (domSize : nat) xs vPairNew vRes vPairOld rep_n', *)
(*         arity = getArity methodNew *)
(*         -> length reps_o = arity *)
(*         -> length reps_n = arity *)
(*         -> length xs = domSize *)
(*         -> Forall2 (absRel) reps_o reps_n *)
(*         -> STEPS (XNApp opNew (reps_n >< xs)) vPairNew *)
(*         -> XProj 0 vPairNew = rep_n' *)
(*         -> XProj 1 vPairNew = vRes *)
(*         -> exists rep_o', *)
(*             (STEPS (XNApp opOld (reps_o >< xs)) vPairOld *)
(*             /\ XProj 0 vPairOld = rep_o' *)
(*             /\ XProj 1 vPairOld = vRes) *)
(*             /\ absRel rep_o' rep_n'. *)

(* Definition ADTrefines (aOld aNew : adt) := *)
(*   wfADT aOld -> wfADT aNew -> *)
(*   exists (absRel : getRepType aOld -> getRepType aNew -> Prop), *)
(*   forall methodsOld methodsNew methodOld methodNew i numMethods, *)
(*     getMethods aOld = methodsOld *)
(*     -> getMethods aNew = methodsNew *)
(*     -> length methodsOld = length methodsNew *)
(*     -> get i methodsNew = methodNew *)
(*     -> get i methodsOld = methodOld *)
(*     -> forall (reps_o : list (getRepType aOld)) (reps_n : list (getRepType aNew)) *)
(*         (arity : nat) (domSize : nat) xs vPairNew vRes vPairOld rep_n', *)
(*         arity = getArity methodNew *)
(*         -> length reps_o = arity *)
(*         -> length reps_n = arity *)
(*         -> length xs = domSize *)
(*         -> Forall2 (absRel) reps_o reps_n *)
(*         -> STEPS (XNApp opNew (reps_n >< xs)) vPairNew *)
(*         -> XProj 0 vPairNew = rep_n' *)
(*         -> XProj 1 vPairNew = vRes *)
(*         -> exists rep_o', *)
(*             (STEPS (XNApp opOld (reps_o >< xs)) vPairOld *)
(*             /\ XProj 0 vPairOld = rep_o' *)
(*             /\ XProj 1 vPairOld = vRes) *)
(*             /\ absRel rep_o' rep_n'. *)


(* Definition ADTrefines' (aOld aNew : adt) := *)
(*   exists (absRel : getRepType aOld -> getRepType aNew -> Prop), *)
(*   forall opsOld opsNew opOld opNew i numMethods, *)
(*     getOps aOld = opsOld *)
(*     -> getOps aNew = opsNew *)
(*     -> length opsOld = length opsNew *)
(*     -> get i opsNew = opNew *)
(*     -> get i opsOld = opOld *)
(*     -> forall (reps_o : list (getRepType aOld)) (reps_n : list (getRepType aNew)) *)
(*         (arity : nat) (domSize : nat) xs vPairNew vRes vPairOld rep_n', *)
(*         arity = getArity opNew *)
(*         -> length reps_o = arity *)
(*         -> length reps_n = arity *)
(*         -> length xs = domSize *)
(*         -> Forall2 (absRel) reps_o reps_n *)
(*         -> STEPS (XNApp opNew (reps_n >< xs)) vPairNew *)
(*         -> XProj 0 vPairNew = rep_n' *)
(*         -> XProj 1 vPairNew = vRes *)
(*         -> exists rep_o', *)
(*             (STEPS (XNApp opOld (reps_o >< xs)) vPairOld *)
(*             /\ XProj 0 vPairOld = rep_o' *)
(*             /\ XProj 1 vPairOld = vRes) *)
(*             /\ absRel rep_o' rep_n'. *)
