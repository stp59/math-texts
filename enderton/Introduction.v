(* We minimize the use of the Rule of Excluded Middle. *)
Axiom REM : forall (P : Prop), P \/ ~P.

(* Chapter 1: Introduction *)

(* In axiomatic set theory, the notions of a set and elementhood are primitive,
and remain undefined. All the properites that are provable about sets and 
elementhood will be derived from the axioms. *)

Definition set : Type.
Admitted.

Definition In : set -> set -> Prop.
Admitted.

(* This is a theorem of classical logic which requires the REM. We minimize its use here. *)

Theorem Not_Forall_Implies_Exists : forall (P : set -> Prop), 
  (~forall (x : set), ~ P x) -> exists (x : set) , P x.
Proof.
  intros P H. assert (I : (exists x, P x) \/ (~ exists x, P x)).
  { apply REM. }
  destruct I as [I | I]; try assumption.
  assert (Q : forall x, ~ P x).
  { intros x C. apply I. exists x. assumption. }
  apply H in Q. destruct Q.
Qed.

(* Another theorem of classical logic which requires the REM. *)
Theorem DeMorgan : forall (P Q : Prop), ~(P /\ Q) <-> ~P \/ ~Q.
Proof.
  intros P Q. split; intros H.
  - assert (I : P \/ ~ P). { apply REM. }
    assert (J : Q \/ ~ Q). { apply REM. }
    destruct I as [I | I]; destruct J as [J | J].
    + assert (T : P /\ Q). { split; assumption. }
      apply H in T. destruct T.
    + right. assumption.
    + left. assumption.
    + left. assumption.
  - intros C. destruct H as [H | H].
    + apply H, C.
    + apply H, C.
Qed.

Theorem DeMorgan' : forall (P Q : Prop), ~(P \/ Q) <-> ~P /\ ~Q.
Proof.
  intros P Q. split; intros H.
  - split.
    + intros C. apply H. left. assumption.
    + intros C. apply H. right. assumption.
  - intros C. destruct C as [C | C].
    + destruct H as [H1 H2]. apply H1, C.
    + apply H, C.
Qed.