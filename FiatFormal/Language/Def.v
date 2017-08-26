
Require Export FiatFormal.Language.Ty.


(* Definitions.
   Carries meta information about type and data constructors,
   Along with type information for AbsDTs *)
Inductive def  : Type :=
 (* Definition of a data type constructor *)
 | DefDataType
   :  tycon        (* Name of data type constructor *)
   -> list datacon (* Data constructors that build this type *)
   -> def

 (* Definition of a data constructor *)
 | DefData
   :  datacon      (* Name of data constructor *)
   -> list ty      (* Types of arguments *)
   -> ty           (* Type  of constructed data *)
   -> def

 (* Definition of an abstract data type *)
 | DefADTSigs
   : adtcon      (* Name of data constructor, implicitly used as a type, once defined *)
     -> Rep       (* representation type, (adtcon n) gets mapped to
                    this type as mentioned above *)
     -> list Sig
     (* Each element in this list is an ADT method *)
     (* signature. The types of each "Sig" may reference any number of
        (adtcon i), for any any i in which (TX (adtcon i)) is a well-defined
        ADT type. Such a reference will be interpreted as a placeholder for the
        "Rep" type *)
     -> def.
Hint Constructors def.


(* Definition environment.
   Holds the definitions of all:
   - algebraic data type constructors
   - ADT rep types and method signatures *)
(* Note: method bodies held separately in "ADTMethodDefs", given in ExpBase.v *)
Definition defs  := list def.


(* Functions for looking up definitions by (adtcon, tycon, datacon) *)

(* Lookup the def of a given ADT *)
Fixpoint getADTSigs (ac : adtcon) (ds : defs) : option def :=
  match ds with
  | ds' :> DefADTSigs ac' _ _ as a
    => if adtcon_beq ac ac'
      then Some a
      else getADTSigs ac ds'
  | ds' :> _ => getADTSigs ac ds'
  | Empty => None
  end.
(* Lookup the def of a given type constructor *)
Fixpoint getTypeDef (tc: tycon) (ds: defs) : option def :=
 match ds with
 | ds' :> DefDataType tc' _ as d
 => if tycon_beq tc tc'
     then  Some d
     else  getTypeDef tc ds'

 | ds' :> _ => getTypeDef tc ds'
 | Empty    => None
 end.
(* Lookup the def of a given data constructor *)
Fixpoint getDataDef (dc: datacon) (ds: defs) : option def :=
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
