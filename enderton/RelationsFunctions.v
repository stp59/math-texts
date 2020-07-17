From Enderton Require Export AxiomsOperators.

(** Chapter 3 : Relations and Functions*)

(** The first section of the chapter treats ordered pairs and Cartesian products. *)

(** The Kuratowski definition of ordered pairs: *)

Definition OrdPair (x y xy : set) : Prop :=
  forall z, In z xy <-> Singleton x z \/ Pair x y z.

Theorem OrdPair_Exists : forall x y, exists xy, OrdPair x y xy.
Proof.
  intros x y. singleton x. pair x y. pair x0 x1. exists x2.
  intros z. split; intros P.
  - apply H1 in P. destruct P as [P | P].
    + left. rewrite P. apply H.
    + right. rewrite P. apply H0.
  - apply H1. destruct P as [P | P].
    + left. apply Extensionality_Axiom. intros a. split; intros Q.
      * apply H. apply P in Q. assumption.
      * apply P. apply H in Q. assumption.
    + right. apply Extensionality_Axiom. intros a. split; intros Q.
      * apply H0. apply P in Q. assumption.
      * apply P. apply H0 in Q. assumption.
Qed.

Theorem OrdPair_Unique : forall x y A B, OrdPair x y A -> OrdPair x y B ->
  A = B.
Proof.
  intros x y A B HA HB. apply Extensionality_Axiom. intros a; split; intros.
  - apply HB. apply HA. assumption.
  - apply HA. apply HB. assumption.
Qed.

Ltac ordpair x y := destruct (OrdPair_Exists x y).

Lemma Single_And_Pair : forall x y z A, Singleton x A -> Pair y z A ->
  x = y /\ x = z.
Proof.
  intros x y z A Hs Hp. split.
  - assert (P : In y A). { apply Hp. left. trivial. }
    apply Hs in P. rewrite P. trivial.
  - assert (P : In z A). { apply Hp. right. trivial. }
    apply Hs in P. rewrite P. trivial.
Qed.

(** The fundmental propery of ordered pairs, which motivated the above definition: *)

Theorem Enderton3A : forall x y u v xy uv, OrdPair x y xy -> OrdPair u v uv ->
  xy = uv <-> x = u /\ y = v.
Proof.
  intros x y u v xy uv Hxy Huv. split; intros H.
  - unfold OrdPair in Hxy, Huv.
    singleton u. rename x0 into Su. rename H0 into HSu.
    pair u v. rename x0 into Puv. rename H0 into HPuv.
    singleton x. rename x0 into Sx. rename H0 into HSx.
    pair x y. rename x0 into Pxy. rename H0 into HPxy.
    assert (A : In Su xy). { rewrite <- H in Huv. apply Huv. left. assumption. }
    assert (B : In Puv xy). { rewrite <- H in Huv. apply Huv. right. assumption. }
    apply Hxy in A. apply Hxy in B. destruct A as [a | b].
    + destruct B as [c | d].
      * assert (P : x = u /\ x = v).
        { apply (Single_And_Pair _ _ _ Puv); assumption. }
        destruct P as [P Q].
        assert (R : Singleton Su uv).
        { intros p. split; intros I.
          - apply Extensionality_Axiom. intros z. split.
            + intros J. apply HSu. apply Huv in I.
              destruct I as [I | I].
              * apply I in J. assumption.
              * apply I in J. destruct J as [J | J].
                assumption. rewrite <- P. rewrite Q. assumption.
            + intros J. apply HSu in J. apply Huv in I.
              destruct I as [I | I].
              * apply I. assumption.
              * apply I. left. assumption.
          - apply Huv. left. rewrite I. assumption. }
        rewrite <- H in R. split; try assumption.
        assert (S : In Pxy xy). { apply Hxy. right. assumption. }
        apply R in S. assert (T : In y Pxy). apply HPxy. right. trivial.
        rewrite S in T. apply HSu in T. rewrite T. rewrite <- P. assumption.
      * assert (P : In x Su). { apply a. trivial. }
        apply HSu in P. split; try assumption.
        assert (Q : In y Puv). { apply d. right. trivial. }
        apply HPuv in Q. destruct Q as [Q | Q]; try assumption.
        assert (R : Singleton Sx xy).
        { intros f. split; intros F.
          - apply Extensionality_Axiom. intros g. split; intros G.
            + apply HSx. apply Hxy in F. destruct F.
              * apply H0 in G. assumption.
              * apply H0 in G. destruct G; try assumption.
                rewrite P. rewrite <- Q. assumption.
            + apply HSx in G. apply Hxy in F. destruct F.
              * apply H0. assumption.
              * apply H0. left. assumption.
          - apply Hxy. left. rewrite F. assumption. }
        rewrite H in R.
        assert (S : In Puv uv). { apply Huv. right. assumption. }
        apply R in S. assert (T : In v Puv).
        { apply HPuv. right. trivial. }
        rewrite S in T. apply HSx in T.
        rewrite T. rewrite Q. rewrite P. trivial.
    + destruct B as [c | d].
      * assert (P : In u Puv). { apply HPuv. left. trivial. }
        apply c in P. split; try (rewrite P; trivial).
        assert (Q : In v Puv). { apply HPuv. right. trivial. }
        apply c in Q. rewrite Q. rewrite <- P.
        assert (T : In y Su). { apply b. right. trivial. }
        apply HSu in T. assumption.
      * assert (P : In x Su). { apply b. left. trivial. }
        apply HSu in P. split; try assumption.
        assert (Q : In y Puv). { apply d. right. trivial. }
        apply HPuv in Q. destruct Q as [Q | Q]; try assumption.
        assert (R : u = v). { rewrite P in d. rewrite Q in d.
          assert (T : In v Puv). { apply HPuv. right. trivial. }
          apply d in T. destruct T as [T | T]; rewrite T; trivial. }
        rewrite <- R. assumption.
  - destruct H as [H I]. apply Extensionality_Axiom.
    intros z. split; intros J.
    + apply Huv. apply Hxy in J. destruct J as [J | J].
      * left. rewrite <- H. assumption.
      * right. rewrite <- H. rewrite <- I. assumption.
    + apply Hxy. apply Huv in J. destruct J as [J | J].
      * left. rewrite H. assumption.
      * right. rewrite H, I. assumption.
Qed.

(** This theorem allows for the following definitions: *)

Definition Fst (xy x: set) : Prop :=
  exists (y : set), OrdPair x y xy.

Definition Snd (xy y: set) : Prop :=
  exists (x : set), OrdPair x y xy.

Theorem Fst_Exists : forall x y xy, OrdPair x y xy -> exists u, Fst xy u.
Proof.
  intros x y xy Hxy. exists x. exists y. assumption.
Qed.

Theorem Snd_Exists : forall x y xy, OrdPair x y xy -> exists v, Snd xy v.
Proof.
  intros x y xy Hxy. exists y, x. assumption.
Qed.

(** The following two theorems require the fundamental property of ordered
    pairs, which is why the definitions of [Fst] and [Snd] are justified by
    the theorem above. *)

Theorem Fst_Unique : forall xy x u, Fst xy x -> Fst xy u -> x = u.
Proof.
  intros xy x u [y Hxy] [v Huv].
  apply (Enderton3A x y u v xy xy Hxy Huv). trivial.
Qed.

Theorem Snd_Unique : forall xy y v, Snd xy y -> Snd xy v -> y = v.
Proof.
  intros xy y v [x Hxy] [u Huv].
  apply (Enderton3A x y u v xy xy Hxy Huv). trivial.
Qed. 

Ltac fst xy OPxy := destruct (Fst_Exists xy).

Ltac snd xy OPxy := destruct (Snd_Exists xy).

(* Ordered pairs being well defined, cartesian products follow naturally. **)

Definition Prod (A B AxB: set) : Prop :=
  forall ab, In ab AxB <-> exists a b, In a A /\ In b B /\ OrdPair a b ab.

Lemma Enderton3B : forall x y xy C PC PPC, OrdPair x y xy -> PowerSet C PC ->
  PowerSet PC PPC -> In x C -> In y C -> In xy PPC.
Proof.
  intros x y xy C PC PPC Hxy HPC HPPC Hx Hy.
  apply HPPC. intros a Ha. apply HPC. intros b Hb.
  apply Hxy in Ha. destruct Ha as [Ha | Ha].
  - apply Ha in Hb. rewrite Hb. assumption.
  - apply Ha in Hb. destruct Hb as [Hb | Hb].
    + rewrite Hb. assumption.
    + rewrite Hb. assumption.
Qed.

Corollary Enderton3C : forall A B, exists AxB, Prod A B AxB.
Proof.
  intros A B. binary_union A B. rename x into AuB. rename H into HAuB.
  powerset AuB. rename x into PAuB. rename H into HPAuB.
  powerset PAuB. rename x into PPAuB. rename H into HPPAuB.
  build_set
    (prod set set)
    (fun (t : set * set) (c : set) (x : set) =>
      exists a b, In a (fst t) /\ In b (snd t) /\ OrdPair a b x)
    (A,B)
    PPAuB.
  rename x into AxB. rename H into HAxB. exists AxB.
  intros x. split; intros H.
  - apply HAxB. assumption.
  - apply HAxB. split; try apply H.
    destruct H as [a [b [Ha [Hb Hab]]]].
    apply (Enderton3B a b x AuB PAuB PPAuB); try assumption.
    + apply HAuB. left. assumption.
    + apply HAuB. right. assumption.
Qed.

Theorem Prod_Unique : forall A B AxB AxB',
  Prod A B AxB -> Prod A B AxB' -> AxB = AxB'.
Proof.
  intros A B AxB AxB' HAxB HAxB'.
  apply Extensionality_Axiom. intros x; split; intros H.
  - apply HAxB'. apply HAxB. assumption.
  - apply HAxB. apply HAxB'. assumption.
Qed.

Ltac prod A B := destruct (Enderton3C A B).

(** Exercise 3-1 : Suppose we attempted to extend to Kuratowski definitions
    of ordered pairs to ordered triples by defining 
    
            <x, y, z>* = {{x}, {x,y}, {x,y,z}}
  
    Show that this definition is unsuccessful by giving examples of objects
    u, v, w, x, y, z with <u,v,w>* = <x,y,z>* but with either y <> v or
    z <> w (or both). *)

Theorem Exercise3_2a : forall A B C BuC AxBuC AxB AxC AxBuAxC,
  BinaryUnion B C BuC -> Prod A BuC AxBuC -> Prod A B AxB -> Prod A C AxC ->
  BinaryUnion AxB AxC AxBuAxC -> AxBuC = AxBuAxC.
Admitted.

Theorem Exercise3_2b : forall A B C AxB AxC, Prod A B AxB -> Prod A C AxC ->
  ~Empty A -> B = C.
Admitted.

Definition Elementwise_Prod (A B exAB : set) : Prop :=
  forall x, In x exAB <-> exists X, In X B /\ Prod A X x.

Theorem Elementwise_Prod_Exists : forall A B, exists exAB,
  Elementwise_Prod A B exAB.
Admitted.

Theorem Elementwise_Prod_Unique : forall A B exAB exAB',
  Elementwise_Prod A B exAB -> Elementwise_Prod A B exAB' -> exAB = exAB'.
Admitted.

Theorem Exercise3_3 : forall A B UB AxUB exAB UexAB,
  Union B UB -> Prod A UB AxUB -> Elementwise_Prod A B exAB ->
  Union exAB UexAB -> AxUB = UexAB.
Admitted.

Theorem Exercise3_4 : ~exists XU, forall x y xy, OrdPair x y xy -> In xy XU.
Admitted.

Definition Singletonwise_Prod (A B C : set) : Prop :=
  forall y, In y C <-> exists x Sx SxB, In x A /\ Singleton x Sx /\
  Prod Sx B SxB /\ y = SxB.

Theorem Exercise3_5a : forall A B, exists C, Singletonwise_Prod A B C.
Admitted.

Theorem Singletonwise_Prod_Unique : forall A B C D,
  Singletonwise_Prod A B C -> Singletonwise_Prod A B D -> C = D.
Admitted.

Theorem Exercise3_5b : forall A B C AxB UC, Singletonwise_Prod A B C ->
  Prod A B AxB -> Union C UC -> AxB = UC.
Admitted.