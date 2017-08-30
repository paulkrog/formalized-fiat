
Require Export FiatFormal.Language.Ty.


(* Definitions.
   Carries meta information about type and data constructors *)
Inductive alg_def : Type :=
 (* Definition of a data type constructor *)
 | DefDataType
   :  tycon        (* Name of data type constructor *)
   -> list datacon (* Data constructors that build this type *)
   -> alg_def

 (* Definition of a data constructor *)
 | DefData
   :  datacon      (* Name of data constructor *)
   -> list ty      (* Types of arguments *)
   -> ty           (* Type  of constructed data *)
   -> alg_def.
Hint Constructors alg_def.


(* Definition environment *)
Definition alg_defs  := list alg_def.


(* Functions for looking up definitions by (tycon, datacon) *)

(* Lookup the definition of a given type constructor *)
Fixpoint getTypeDef (tc: tycon) (ds: alg_defs) : option alg_def :=
 match ds with
 | ds' :> DefDataType tc' _ as d
 => if tycon_beq tc tc'
     then  Some d
     else  getTypeDef tc ds'

 | ds' :> _ => getTypeDef tc ds'
 | Empty    => None
 end.
(* Lookup the definition of a given data constructor *)
Fixpoint getDataDef (dc: datacon) (ds: alg_defs) : option alg_def :=
 match ds with
 | ds' :> DefData dc' _ _ as d
 => if datacon_beq dc dc'
     then  Some d
     else  getDataDef dc ds'

 | ds' :> _ => getDataDef dc ds'
 | Empty    => None
 end.


(* Some proofs about equality between these "name" constructors *)
Lemma datacon_beq_eq
 :  forall dc dc'
 ,  true = datacon_beq dc dc'
 -> dc = dc'.
Proof.
 intros.
 destruct dc.
 destruct dc'.
 simpl in H.
 apply beq_nat_eq in H.
 auto.
Qed.
Lemma datacon_beq_false
 :  forall dc
 ,  false = datacon_beq dc dc
 -> False.
Proof.
 intro.
 destruct dc.
 simpl.
 intros.
  induction n.
  simpl in H. inversion H.
  simpl in H. auto.
Qed.
