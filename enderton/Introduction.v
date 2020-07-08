(* We minimize the use of the Rule of Excluded Middle. *)
Axiom REM : forall (P : Prop), P \/ ~P.

(* This is a theorem of classical logic which requires the REM. We minimize its use here. *)

Axiom Not_Forall_Implies_Exists : forall (T : Type), forall (P : T -> Prop), 
  (~forall (x : T), ~ P x) -> exists (x : T) , P x.

(* Another theorem of classical logic which requires the REM. *)
Axiom DeMorgan : forall (P Q : Prop), ~(P /\ Q) <-> ~P \/ ~Q.
Axiom DeMorgan' : forall (P Q : Prop), ~(P \/ Q) <-> ~P /\ ~Q.

(* Chapter 1: Introduction *)

(* In axiomatic set theory, the notions of a set and elementhood are primitive,
and remain undefined. All the properites that are provable about sets and 
elementhood will be derived from the axioms. *)

Definition set : Type.
Admitted.

Definition In : set -> set -> Prop.
Admitted.