
Require Import FiatFormal.Language.Step.


Definition refines (x1 x2 : exp) :=
  forall pb ds pbOK v,
    STEPS pb ds pbOK x2 v
    -> STEPS pb ds pbOK x1 v.
Definition refinesP (p1 p2 : prog) :=
  forall pb ds pbOK v,
    STEPSP pb ds pbOK p2 v
    -> STEPSP pb ds pbOK p1 v.

(* need to access all operations of these adts. *)
(* may need make use of wfP and wfADT to enforce n-ary. *)
(* functions.  *)

(* need way to specify method arity  *)

Definition getRep (a : adt) :=
  match a with
  | IADT r x s => r
  end.
Definition getBody (a : adt) :=
  match a with
  | IADT r x s => x
  end.
Definition getSig (a : adt) :=
  match a with
  | IADT r x s => s
  end.

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
(*   exists (absRel : getRep aOld -> getRep aNew -> Prop), *)
(*     -> length ms = n *)
(*     -> *)

(*   forall methodsOld methodsNew methodOld methodNew i numMethods, *)
(*     getMethods aOld = methodsOld *)
(*     -> getMethods aNew = methodsNew *)
(*     -> length methodsOld = length methodsNew *)
(*     -> get i methodsNew = methodNew *)
(*     -> get i methodsOld = methodOld *)
(*     -> forall (reps_o : list (getRep aOld)) (reps_n : list (getRep aNew)) *)
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
(*   exists (absRel : getRep aOld -> getRep aNew -> Prop), *)
(*   forall methodsOld methodsNew methodOld methodNew i numMethods, *)
(*     getMethods aOld = methodsOld *)
(*     -> getMethods aNew = methodsNew *)
(*     -> length methodsOld = length methodsNew *)
(*     -> get i methodsNew = methodNew *)
(*     -> get i methodsOld = methodOld *)
(*     -> forall (reps_o : list (getRep aOld)) (reps_n : list (getRep aNew)) *)
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
(*   exists (absRel : getRep aOld -> getRep aNew -> Prop), *)
(*   forall opsOld opsNew opOld opNew i numMethods, *)
(*     getOps aOld = opsOld *)
(*     -> getOps aNew = opsNew *)
(*     -> length opsOld = length opsNew *)
(*     -> get i opsNew = opNew *)
(*     -> get i opsOld = opOld *)
(*     -> forall (reps_o : list (getRep aOld)) (reps_n : list (getRep aNew)) *)
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
