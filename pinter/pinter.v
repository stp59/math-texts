Require Import Coq.ZArith.BinIntDef.
Require Import Coq.ZArith.BinInt.
Require Import Coq.QArith.QArith_base.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Raxioms.

(** Encoding Pinter's "A Book of Abstract Algebra" in Coq...*)

(** Chapter 3: The Definition of Groups *)

(** Having learned my lesson from encoding Enderton, I explicitly require a
    definition for the neutral element and inversion, rather than deducing their
    existence from the axioms. This enables us to directly compute the desired 
    value rather than destructing a bunch of pedantic existence theorems before
    getting our hands on something useful. *)

(** I have opted to use Coq's ADT features for this since it seemed the most 
    natural way to encode abstract algebraic structures. Not sure what the 
    consequences will be of this approach contrasted with something else
    involving sets and ordered tuples. However, it seems natural to use a Coq
    [dependent] type in place of a set for the group elements. *)

Module Type Group.

  Parameter G : Type.
  Parameter e : G.
  Parameter o : G -> G -> G.
  Parameter i : G -> G.

  Notation "0" := (e).
  Notation "a + b" := (o a b).
  Notation "- a" := (i a).

  Axiom Associativity : forall (a b c : G), a + (b + c) = (a + b) + c.

  Axiom Identity : forall (a : G), a + 0 = a /\ 0 + a = a.

  Axiom Inverse : forall (a : G), a + -a = 0 /\ -a + a = 0.

End Group.

(** Pinter notes that the additive group of integers is a group. We acknowledge
    that here with an implementation of the Group module on Coq Integers. *)

Module ZPlus : Group.
  Definition G := Z.t.
  Definition e := Z.zero.
  Definition o := Z.add.
  Definition i := Z.opp.

  Notation "a + b" := (o a b).
  Notation "0" := (e).
  Notation "- a" := (i a).

  Theorem Associativity : forall (a b c : G), a + (b + c) = (a + b) + c.
  Proof.
    intros a b c. apply Z.add_assoc.
  Qed.

  Theorem Identity : forall (a : G), a + 0 = a /\ 0 + a = a.
  Proof.
    intros a. split.
    - apply Z.add_0_r.
    - reflexivity.
  Qed.

  Theorem Inverse : forall (a : G), a + -a = 0 /\ -a + a = 0.
  Proof.
    intros a. split.
    - apply Z.add_opp_diag_r.
    - apply Z.add_opp_diag_l.
  Qed.
End ZPlus.

(** Similarly for the additive group of rational numbers. *)

Module QPlus : Group.
  Definition G := Q.
  Definition e := 0.
  Definition o := Qplus.
  Definition i := Qopp.

  (** This is an unfortunate necessity due to the way the Coq Library defines
      equality for rational numbers. The alternative is to introduce another
      parameter to the module type for groups, but this seems unfaithful to the
      foundational mathematics. Better to introduce and axiom which we know to
      hold if we were to do all the work to encode rational numbers as
      equivalence classes instead of defining a separate equality. *)
  Axiom rational_equality : forall (a b : G), a == b -> a = b.

  Notation "a + b" := (o a b).
  Notation "0" := (e).
  Notation "- a" := (i a).

  Theorem Associativity : forall (a b c : G), a + (b + c) = (a + b) + c.
  Proof.
    intros a b c. apply rational_equality. apply Qplus_assoc.
  Qed.

  Theorem Identity : forall (a : G), a + 0 = a /\ 0 + a = a.
  Proof.
    intros a. split; apply rational_equality.
    - apply Qplus_0_r.
    - apply Qplus_0_l.
  Qed.

  Theorem Inverse : forall (a : G), a + -a = 0 /\ -a + a = 0.
  Proof.
    intros a. split.
    - apply rational_equality. apply Qplus_opp_r.
    - apply rational_equality. rewrite Qplus_comm. apply Qplus_opp_r.
  Qed.
End QPlus.

(** Following Pinter, we repeat the process for real numbers. *)

Module RPlus : Group.
  Definition G := R.
  Definition e : G := R0.
  Definition o := Rplus.
  Definition i := Ropp.

  Notation "a + b" := (o a b).
  Notation "0" := (e).
  Notation "- a" := (i a).

  Theorem Associativity : forall (a b c : G), a + (b + c) = (a + b) + c.
  Proof.
    intros a b c. rewrite Rplus_assoc. reflexivity.
  Qed.

  Theorem Identity : forall (a : G), a + 0 = a /\ 0 + a = a.
  Proof.
    intros a. split.
    - rewrite Rplus_comm. apply Rplus_0_l.
    - apply Rplus_0_l.
  Qed.

  Theorem Inverse : forall (a : G), a + -a = 0 /\ -a + a = 0.
  Proof.
    intros a. split.
    - apply Rplus_opp_r.
    - rewrite Rplus_comm. apply Rplus_opp_r.
  Qed.

End RPlus.

(** Pinter also notes that the non-zero rationals and non-zero reals with
    multiplication are a group, along with the positive rationals and the 
    positive reals. I've chosen to go through the tedium of introducing these
    into the namespace so that we can use them in exercises later on. *)

Module QStar : Group.
  Definition G := 