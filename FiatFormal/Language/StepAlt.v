
Require Export FiatFormal.Language.TyJudge.
Require Export FiatFormal.Language.Exp.
Require Export FiatFormal.Language.SubstExpExp.


(* The body of an alternative is well typed under an environment
   that includes the arguments of the constructor being matched. *)
Lemma getAlt_bodyIsWellTyped_fromAlts
  : forall alg_ds adt_ds te tPat tResult alts dc tsArgs x,
    Forall (fun a => TYPEA alg_ds adt_ds te a tPat tResult) alts
 -> In (AAlt dc tsArgs x) alts
 -> TYPE alg_ds adt_ds (te >< tsArgs) x tResult.
Proof.
(*  intros.  *)
(*  norm. spec H H0.  *)
(*  inverts_type. auto. *)
(* Qed. *)
Admitted.

(* The body of an alternative of a case expression is well typed
   under an environment that includes the arguments of the constructor
   being matched. *)
Lemma getAlt_bodyIsWellTyped_fromCase
  : forall alg_ds adt_ds te tResult tCon alts dc tsArgs x1 x2,
    TYPE alg_ds adt_ds te (XMatch x1 alts) tResult
    -> getDataDef dc alg_ds = Some (DefData dc tsArgs tCon)
    -> getAlt     dc alts   = Some (AAlt    dc tsArgs x2)
    -> TYPE alg_ds adt_ds (te >< tsArgs) x2 tResult.
Proof.
(*  intros. *)
(*  inverts keep H. *)
(*  lets HA:  getAlt_in H1. *)
(*  lets HXT: getAlt_bodyIsWellTyped_fromAlts H5 HA. *)
(*  auto. *)
(* Qed. *)
Admitted.


(* If an alternative is well typed then the types of the ctor
   args embedded in it match those in the data type definition *)
Lemma getAlt_ctorArgTypesMatchDataDef
  : forall alg_ds adt_ds te tCon tResult alts dc x tsArgs tsArgs',
    Forall (fun alt => TYPEA alg_ds adt_ds te alt tCon tResult) alts
    -> getDataDef dc alg_ds = Some (DefData dc tsArgs  tCon)
    -> getAlt dc alts       = Some (AAlt    dc tsArgs' x)
    -> tsArgs = tsArgs'.
Proof.
(*  intros. norm. *)
(*  lets D: getAlt_in H1. spec H D. *)
(*  inverts_type. rip. *)
(* Qed. *)
Admitted.
