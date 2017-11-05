
Require Export FiatFormal.Language.Ty.
Require Export FiatFormal.Language.Ki.


(* Kind judgement assigns a kind to a type.

   With plain SystemF (not SystemF2) we only have value types.
   We could have made this a 2-place relation and omitted the
   KStar return kind, but doing it this way makes the form of the
   judgement more similar to the SystemF2 case.
 *)
Inductive KIND : kienv -> ty -> ki -> Prop :=
 | KICon
   :  forall ke c
   ,  KIND ke (TCon c) KStar

 | KIVar
   :  forall ke i k
   ,  get  i ke = Some k
   -> KIND ke (TVar i) k

 | KIFun
   :  forall ke t1 t2
   ,  KIND ke t1 KStar
   -> KIND ke t2 KStar
   -> KIND ke (TFun t1 t2) KStar

 | KIExists
   : forall ke t,
     KIND (ke :> KStar) t KStar
     -> KIND ke (TExists t) KStar

 | KINProd
   : forall ke ts,
     Forall (fun t => KIND ke t KStar) ts
     -> KIND ke (TNProd ts) KStar

 | KINFun : forall ke ts tRes,
     KIND ke tRes KStar
     -> Forall (fun t => KIND ke t KStar) ts
     -> KIND ke (TNFun ts tRes) KStar.
Hint Constructors KIND.

Ltac inverts_kind :=
  match goal with
  | [ H1 : KIND _ _ _ |- _ ] => inverts keep H1
  end.


(********************************************************************)
(* A well kinded type is well formed. *)
Lemma kind_wfT
 :  forall ke t k
 ,  KIND ke t k
 -> wfT ke t.
Proof.
 intros. gen ke k.
 induction t; intros; inverts H; simpl; eauto;
   try inverts_kind; eauto; repeat constructor; eauto.

 Case "TNProd".
 inverts keep H4. eauto.
 apply Forall_forall; intros.
 pose proof (Forall_in _ _ _ H2 H); simpl in *.
 eapply H3. inverts keep H4.
 pose proof (Forall_in _ _ _ H8 H); simpl in *.
 eassumption.

 Case "TNFun".
 inverts keep H7; eauto.
 apply Forall_forall; intros.
 pose proof (Forall_in _ _ _ H2 H); simpl in *.
 eapply H3.
 inverts keep H7.
 pose proof (Forall_in _ _ _ H9 H); simpl in *.
 eassumption.
Qed.


(* If a type is well kinded in an empty environment,
   then that type is closed. *)
Lemma kind_empty_is_closed
 :  forall t k
 ,  KIND nil t k
 -> closedT t.
Proof.
 intros. unfold closedT. eapply kind_wfT. eauto.
Qed.

(* We can insert a new type into the environment at an arbitray point
   provided we lift existing references to types higher than this
   point across the new one. *)
Lemma liftTT_insert
 :  forall ke ix t k1 k2
 ,  KIND ke t k1
 -> KIND (insert ix k2 ke) (liftTT ix t) k1.
Proof.
 intros. gen ix ke k1.
 induction t; intros; simpl; inverts H; eauto;
   simpl; try destruct k1.

 Case "TVar".
 lift_cases; intros; auto.

 Case "TExists".
 apply KIExists.
 rewrite insert_rewind.
 apply IHt. auto.

 Case "TNProd".
 apply KINProd; eauto.
 apply KINProd; eauto.
 inverts_kind. inverts keep H4.
 apply Forall_cons.
 apply H1; assumption.
 rewrite Forall_forall in H2.
 rewrite Forall_forall; intros.
 apply map_in_exists in H. destruct H as [y  [YX0  INY]].
 specialize (H2 _ INY).
 rewrite <- YX0. apply H2.
 rewrite Forall_forall in H6; eauto.

 Case "TNFun".
 apply KINFun. inverts_kind. apply IHt; eauto.
 apply Forall_nil.
 inverts_kind. inverts keep H6.
 apply KINFun; eauto.
 apply Forall_cons.
 apply H1; assumption.
 rewrite Forall_forall in H2.
 rewrite Forall_forall; intros.
 apply map_in_exists in H. destruct H as [y  [YX0  INY]].
 specialize (H2 _ INY).
 rewrite <- YX0. apply H2.
 rewrite Forall_forall in H6; eauto.
Qed.


(* Weakening the kind environment by pushing a new type onto the
   stack *)
Lemma liftTT_weaken
 :  forall ke t k1 k2
 ,  KIND  ke         t           k1
 -> KIND (ke :> k2) (liftTT 0 t) k1.
Proof.
  intros.
  assert (ke :> k2 = insert 0 k2 ke). simpl.
  destruct ke; auto.
  rewrite H0. apply liftTT_insert. auto.
Qed.
