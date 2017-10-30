(* Require Import FiatFormal.Data.List.Base. *)


(* Set Implicit Arguments. *)

(* (* A few misc. functions *) *)

(* Fixpoint get_last {A : Type} (l : list A) : option A := *)
(*   match l with *)
(*   | nil => None *)
(*   | nil :> x => Some x *)
(*   | l'  :> x => get_last l' *)
(*   end. *)

(* Section Forall3. *)

(*   (** [Forall3]: stating that elements of three lists are pairwise related. *) *)

(*   Variables A B C : Type. *)
(*   Variable R : A -> B -> C -> Prop. *)

(*   Inductive Forall3 : list A -> list B -> list C -> Prop := *)
(*     | Forall3_nil : Forall3 nil nil nil *)
(*     | Forall3_cons : forall x y z l l' l'', *)
(*       R x y z -> Forall3 l l' l'' -> Forall3 (x::l) (y::l') (z::l''). *)

(*   Hint Constructors Forall3. *)

(*   Theorem Forall3_refl : Forall3 nil nil nil. *)
(*   Proof. intros; apply Forall3_nil. Qed. *)

(*   (* Theorem Forall2_app_inv_l : forall l1 l2 l', *) *)
(*   (*   Forall2 (l1 ++ l2) l' -> *) *)
(*   (*   exists l1' l2', Forall2 l1 l1' /\ Forall2 l2 l2' /\ l' = l1' ++ l2'. *) *)
(*   (* Proof. *) *)
(*   (*   induction l1; intros. *) *)
(*   (*     exists [], l'; auto. *) *)
(*   (*     simpl in H; inversion H; subst; clear H. *) *)
(*   (*     apply IHl1 in H4 as (l1' & l2' & Hl1 & Hl2 & ->). *) *)
(*   (*     exists (y::l1'), l2'; simpl; auto. *) *)
(*   (* Qed. *) *)

(*   (* Theorem Forall2_app_inv_r : forall l1' l2' l, *) *)
(*   (*   Forall2 l (l1' ++ l2') -> *) *)
(*   (*   exists l1 l2, Forall2 l1 l1' /\ Forall2 l2 l2' /\ l = l1 ++ l2. *) *)
(*   (* Proof. *) *)
(*   (*   induction l1'; intros. *) *)
(*   (*     exists [], l; auto. *) *)
(*   (*     simpl in H; inversion H; subst; clear H. *) *)
(*   (*     apply IHl1' in H4 as (l1 & l2 & Hl1 & Hl2 & ->). *) *)
(*   (*     exists (x::l1), l2; simpl; auto. *) *)
(*   (* Qed. *) *)

(*   (* Theorem Forall2_app : forall l1 l2 l1' l2', *) *)
(*   (*   Forall2 l1 l1' -> Forall2 l2 l2' -> Forall2 (l1 ++ l2) (l1' ++ l2'). *) *)
(*   (* Proof. *) *)
(*   (*   intros. induction l1 in l1', H, H0 |- *; inversion H; subst; simpl; auto. *) *)
(*   (* Qed. *) *)
(* End Forall3. *)

(* Hint Constructors Forall3. *)
