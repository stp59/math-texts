From Enderton Require Export AxiomsOperators.

(** Chapter 3 : Relations and Functions*)

(** The first section of the chapter treats ordered pairs and cartesian
    products using the Kuratowski definition of ordered pairs (below).
    We show that ordered pair are well-defined under this definition. Next
    we show that it satisfies the desired fundame*)

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
Proof.
  intros A B C BuC AxBuC AxB AxC AxBuAxC HBuC HAxBuC HAxB HAxC HAxBuAxC.
  apply Extensionality_Axiom. intros x. split; intros H.
  - apply HAxBuAxC. apply HAxBuC in H. destruct H as [a [b [Ha [Hb Hab]]]].
    apply HBuC in Hb. destruct Hb as [Hb | Hb].
    + left. apply HAxB. exists a, b. repeat (split; try assumption).
    + right. apply HAxC. exists a, b. repeat (split; try assumption).
  - apply HAxBuC. apply HAxBuAxC in H. destruct H as [H | H].
    + apply HAxB in H. destruct H as [a [b [Ha [Hb Hab]]]].
      exists a, b. repeat (split; try assumption).
      apply HBuC. left. assumption.
    + apply HAxC in H. destruct H as [a [b [Ha [Hb Hab]]]].
      exists a, b. repeat (split; try assumption). apply HBuC.
      right. assumption.
Qed.

Theorem Exercise3_2b : forall A B C AxB AxC, Prod A B AxB -> Prod A C AxC ->
  ~Empty A -> AxB = AxC -> B = C.
Proof.
  intros A B C AxB AxC HAxB HAxC HA Hx.
  apply Extensionality_Axiom. intros x; split; intros H.
  - apply Member_Exists_If_NonEmpty in HA as [a HA].
    ordpair a x. rename x0 into ax. rename H0 into Hax.
    assert (P : In ax AxB).
    { apply HAxB. exists a, x. repeat (split; try assumption). }
    rewrite Hx in P. apply HAxC in P as [a' [x' [Ha' [Hx' Hax']]]].
    assert (Q : a = a' /\ x = x').
    { apply (Enderton3A a x a' x' ax ax); try assumption. trivial. }
    destruct Q as [_ Q]. rewrite Q. assumption.
  - apply Member_Exists_If_NonEmpty in HA as [a HA].
    ordpair a x. rename x0 into ax. rename H0 into Hax.
    assert (P : In ax AxC).
    { apply HAxC. exists a, x. repeat (split; try assumption). }
    rewrite <- Hx in P. apply HAxB in P.
    destruct P as [a' [x' [Ha' [Hx' Hax']]]].
    assert (Q : a = a' /\ x = x').
    { apply (Enderton3A a x a' x' ax ax); try assumption; try trivial. }
    destruct Q as [_ Q]. rewrite Q. assumption.
Qed.

Definition Elementwise_Prod (A B exAB : set) : Prop :=
  forall x, In x exAB <-> exists X, In X B /\ Prod A X x.

Theorem Elementwise_Prod_Exists : forall A B, exists exAB,
  Elementwise_Prod A B exAB.
Proof.
  intros A B.
  union B. rename x into UB. rename H into HUB.
  binary_union A UB. rename x into AuUB. rename H into HAuUB.
  powerset AuUB. rename x into PAuUB. rename H into HPAuUB.
  powerset PAuUB. rename x into PPAuUB. rename H into HPPAuUB.
  powerset PPAuUB. rename x into PPPAuUB. rename H into HPPPAuUB.
  build_set
    (prod set set)
    (fun AB (PPAuUB x : set) => exists X, In X (snd AB) /\ Prod (fst AB) X x)
    (A, B)
    PPPAuUB.
  rename x into exAB. rename H into HexAB.
  exists exAB. intros x. split; intros H.
  - apply HexAB. assumption.
  - apply HexAB. split.
    + apply HPPPAuUB. intros y Hy. apply HPPAuUB. intros z Hz.
      apply HPAuUB. intros w Hw. destruct H as [X [HX HAxX]].
      apply HAuUB. apply HAxX in Hy. destruct Hy as [a [b [Ha [Hb Hab]]]].
      apply Hab in Hz. destruct Hz as [Hz | Hz].
      * left. apply Hz in Hw. rewrite Hw. assumption.
      * apply Hz in Hw. destruct Hw as [Hw | Hw].
        { left. rewrite Hw. assumption. }
        { right. apply HUB. exists X. split.
          - rewrite Hw. assumption.
          - assumption. }
    + assumption.
Qed.

Theorem Elementwise_Prod_Unique : forall A B exAB exAB',
  Elementwise_Prod A B exAB -> Elementwise_Prod A B exAB' -> exAB = exAB'.
Proof.
  intros A B exAB exAB' HexAB HexAB'.
  apply Extensionality_Axiom. intros x; split; intros H.
  - apply HexAB'. apply HexAB. assumption.
  - apply HexAB. apply HexAB'. assumption.
Qed.

Theorem Exercise3_3 : forall A B UB AxUB exAB UexAB,
  Union B UB -> Prod A UB AxUB -> Elementwise_Prod A B exAB ->
  Union exAB UexAB -> AxUB = UexAB.
Proof.
  intros A B UB AxUB exAB UexAB HUB HAxUB HexAB HUexAB.
  apply Extensionality_Axiom. intros x. split; intros H.
  - apply HUexAB. apply HAxUB in H. destruct H as [a [b [Ha [Hb H]]]].
    apply HUB in Hb. destruct Hb as [X [Hb HX]].
    prod A X. rename x0 into AxX. rename H0 into HAxX.
    exists AxX. split.
    + apply HAxX. exists a, b. repeat (split; try assumption).
    + apply HexAB. exists X. split; assumption.
  - apply HAxUB. apply HUexAB in H. destruct H as [AxX [H HAxX]].
    apply HexAB in HAxX. destruct HAxX as [X [HX HAxX]].
    apply HAxX in H. destruct H as [a [b [Ha [Hb H]]]].
    exists a, b. repeat (split; try assumption).
    apply HUB. exists X. split; assumption.
Qed.    

Theorem Exercise3_4 : ~exists XU, forall x y xy, OrdPair x y xy -> In xy XU.
Proof.
  intros Con. destruct Con as [XU Con].
  union XU. rename x into UXU. rename H into HUXU.
  union UXU. rename x into UUXU. rename H into HUUXU.
  assert (P : forall x, In x UUXU).
  { intros x. apply HUUXU. singleton x.
    exists x0. split. apply H. trivial.
    apply HUXU. ordpair x x. exists x1. split.
    apply H0. left. assumption.
    apply (Con x x). assumption. }
  assert (Q : exists a, ~ In a UUXU).
  { apply Enderton2A. }
  destruct Q as [a Q]. apply Q. apply P.
Qed.

Definition AllSingletons (A B : set) : Prop :=
  forall Sx, In Sx B <-> exists x, In x A /\ Singleton x Sx.

Theorem AllSingletons_Exists : forall A, exists B, AllSingletons A B.
Proof.
  intros A. powerset A. rename x into PA. rename H into HPA.
  build_set
    set
    (fun (t c Sx : set) => exists x, In x t /\ Singleton x Sx)
    A
    PA.
  rename x into asA. rename H into HasA.
  exists asA. intros Sx. split; intros H.
  - apply HasA. assumption.
  - apply HasA. split.
    + apply HPA. destruct H as [x [Hx H]].
      intros y Hy. apply H in Hy. rewrite Hy. assumption.
    + assumption.
Qed.

Theorem AllSingletons_Unique : forall A B B',
  AllSingletons A B -> AllSingletons A B' -> B = B'.
Proof.
  intros A B B' HB HB'. apply Extensionality_Axiom. intros x. split; intros H.
  - apply HB', HB. assumption.
  - apply HB, HB'. assumption.
Qed.

Definition Singletonwise_Prod (A B C : set) : Prop :=
  forall y, In y C <-> exists x Sx, In x A /\ Singleton x Sx /\
  Prod Sx B y.

Theorem Exercise3_5a : forall A B, exists C, Singletonwise_Prod A B C.
Proof.
  intros A B. binary_union A B. rename x into AuB. rename H into HAuB.
  powerset AuB. rename x into PAuB. rename H into HPAuB.
  powerset PAuB. rename x into PPAuB. rename H into HPPAuB.
  powerset PPAuB. rename x into PPPAuB. rename H into HPPPAuB.
  build_set
    (prod set set)
    (fun AB (PPAuB SxxB : set) => exists x Sx, In x (fst AB) /\
      Singleton x Sx /\ Prod Sx (snd AB) SxxB)
    (A,B)
    PPPAuB.
  rename x into sxAB. rename H into HsxAB.
  exists sxAB. intros x. split; intros H.
  - apply HsxAB. assumption.
  - apply HsxAB. split.
    + apply HPPPAuB. intros y Hy.
      apply HPPAuB. intros z Hz.
      apply HPAuB. intros w Hw. apply HAuB.
      destruct H as [x' [Sx' [Hx' [HSx' H]]]].
      apply H in Hy. destruct Hy as [a [b [Ha [Hb Hy]]]].
      apply Hy in Hz. destruct Hz as [Hz | Hz].
      * left. apply Hz in Hw. rewrite Hw.
        apply HSx' in Ha. rewrite Ha. assumption.
      * apply Hz in Hw. destruct Hw as [Hw | Hw].
        { left. rewrite Hw. apply HSx' in Ha. rewrite Ha. assumption. }
        { right. rewrite Hw. assumption. }
    + assumption.
Qed.

Theorem Singletonwise_Prod_Unique : forall A B C D,
  Singletonwise_Prod A B C -> Singletonwise_Prod A B D -> C = D.
Proof.
  intros A B C D HC HD. apply Extensionality_Axiom. intros x. split; intros H.
  - apply HD, HC. assumption.
  - apply HC, HD. assumption.
Qed.

Theorem Exercise3_5b : forall A B C AxB UC, Singletonwise_Prod A B C ->
  Prod A B AxB -> Union C UC -> AxB = UC.
Proof.
  intros A B C AxB UC HC HAxB HUC.
  apply Extensionality_Axiom. intros x. split; intros H.
  - apply HUC. apply HAxB in H. destruct H as [a [b [Ha [Hb Hab]]]].
    singleton a. rename x0 into Sa. rename H into HSa.
    prod Sa B. rename x0 into SaxB. rename H into HSaxB.
    exists SaxB. split.
    + apply HSaxB. exists a, b. repeat (split; try assumption).
      apply HSa. trivial.
    + apply HC. exists a, Sa. repeat (split; try assumption).
  - apply HAxB. apply HUC in H. destruct H as [SaxB [H HSaxB]].
    apply HC in HSaxB. destruct HSaxB as [a [Sa [Ha [HSa HSaxB]]]].
    apply HSaxB in H. destruct H as [a' [b [Ha' [Hb Hab]]]].
    exists a, b. split; try assumption. split; try assumption.
    apply HSa in Ha'. rewrite <- Ha'. apply Hab.
Qed.

Definition Relation (R : set) : Prop :=
  forall xy, In xy R -> exists x y, OrdPair x y xy.

Definition Domain (R domR : set) : Prop :=
  forall x, In x domR <-> exists y xy, OrdPair x y xy /\
  In xy R.

Definition Range (R ranR : set) : Prop :=
  forall y, In y ranR <-> exists x xy, OrdPair x y xy /\
  In xy R.

Definition Field (R fldR : set) : Prop :=
  forall y, In y fldR <-> exists domR ranR domRuranR,
  Domain R domR /\ Range R ranR /\ BinaryUnion domR ranR domRuranR /\
  In y domRuranR.

Lemma Enderton3D : forall x y A xy UA UUA, OrdPair x y xy -> Union A UA ->
  Union UA UUA -> In xy A -> In x UUA /\ In y UUA.
Proof.
  intros x y A xy UA UUA Hxy HUA HUUA H. split; apply HUUA.
  - singleton x. rename x0 into Sx. rename H0 into HSx.
    exists Sx. split.
    + apply HSx. trivial.
    + apply HUA. exists xy. split.
      * apply Hxy. left. assumption.
      * assumption.
  - pair x y. rename x0 into Pxy. rename H0 into HPxy.
    exists Pxy. split.
    + apply HPxy. right. trivial.
    + apply HUA. exists xy. split.
      * apply Hxy. right. assumption.
      * assumption.
Qed.

Theorem Domain_Exists : forall R, exists domR, Domain R domR.
Proof.
  intros R. union R. rename x into UR. rename H into HUR.
  union UR. rename x into UUR. rename H into HUUR.
  build_set
    set
    (fun (t c x : set) => exists y xy, OrdPair x y xy /\ In xy t)
    R
    UUR.
  rename x into domR. rename H into HdomR.
  exists domR. intros x. split; intros H.
  - apply HdomR. assumption.
  - apply HdomR. split.
    + destruct H as [y [xy [Hxy H]]].
      apply (Enderton3D x y R xy UR UUR) in H; try assumption.
      apply H.
    + assumption.
Qed.

Theorem Domain_Unique : forall R domR domR', Domain R domR -> Domain R domR' ->
  domR = domR'.
Proof.
  intros R domR domR' HdomR HdomR'. apply Extensionality_Axiom.
  intros x; split; intros H.
  - apply HdomR', HdomR. assumption.
  - apply HdomR, HdomR'. assumption.
Qed.

Ltac domain R := destruct (Domain_Exists R).

Theorem Range_Exists : forall R, exists ranR, Range R ranR.
Proof.
  intros R. union R. rename x into UR. rename H into HUR.
  union UR. rename x into UUR. rename H into HUUR.
  build_set
    set
    (fun (t c y : set) => exists x xy, OrdPair x y xy /\ In xy t)
    R
    UUR.
  rename x into ranR. rename H into HranR. exists ranR.
  intros y; split; intros H.
  - apply HranR. assumption.
  - apply HranR. split.
    + destruct H as [x [xy [Hxy H]]].
      apply (Enderton3D x y R xy UR UUR) in H; try assumption.
      apply H.
    + assumption.
Qed.

Theorem Range_Unique : forall R ranR ranR',
  Range R ranR -> Range R ranR' -> ranR = ranR'.
Proof.
  intros R ranR ranR' HR HR'. apply Extensionality_Axiom.
  intros x; split; intros H.
  - apply HR', HR. assumption.
  - apply HR, HR'. assumption.
Qed.

Ltac range R := destruct (Range_Exists R).

Theorem Field_Exists : forall R, exists fldR, Field R fldR.
Proof.
  intros R. domain R. rename x into domR. rename H into HdomR.
  range R. rename x into ranR. rename H into HranR.
  binary_union domR ranR. rename x into domRuranR. rename H into HdomRuranR.
  exists domRuranR. intros x; split; intros H.
  - exists domR, ranR, domRuranR. repeat (split; try assumption).
  - destruct H as [domR' [ranR' [domRuranR' H]]].
    assert (P : domR = domR').
    { apply (Domain_Unique R); try apply H; try assumption. }
    assert (Q : ranR = ranR').
    { apply (Range_Unique R); try apply H; try assumption. }
    assert (S : domRuranR = domRuranR').
    { apply (BinaryUnion_Unique domR ranR). assumption. rewrite P, Q. apply H. }
    rewrite S. apply H.
Qed.

Theorem Field_Unique : forall R fldR fldR',
  Field R fldR -> Field R fldR' -> fldR = fldR'.
Proof.
  intros R fldR fldR' HR HR'.
  apply Extensionality_Axiom. intros x; split; intros H.
  - apply HR', HR. assumption.
  - apply HR, HR'. assumption.
Qed.

Ltac field R := destruct (Field_Exists R).

Theorem Exercise3_6 : forall A domA ranA domAxranA,
  Domain A domA -> Range A ranA -> Prod domA ranA domAxranA ->
  Relation A <-> Subset A domAxranA.
Proof.
  intros A domA ranA domAxranA HdomA HranA HdomAxranA.
  split; intros  H.
  - intros x HA. apply HdomAxranA. apply H in HA as Hx.
    destruct Hx as [a [b Hab]].
    exists a, b. split.
    + apply HdomA. exists b, x. split; try assumption.
    + split.
      * apply HranA. exists a, x. split; try assumption.
      * assumption.
  - intros ab Hab. apply H in Hab.
    apply HdomAxranA in Hab. destruct Hab as [a [b [Ha [Hb Hab]]]].
    exists a, b. assumption.
Qed.

Theorem Exercise3_7 : forall R fldR UR UUR,
  Field R fldR -> Union R UR -> Union UR UUR -> Relation R -> fldR = UUR.
Proof.
  intros R fldR UR UUR HfldR HUR HUUR HR.
  apply Extensionality_Axiom. intros x; split; intros H.
  - apply HUUR. apply HfldR in H.
    destruct H as [domR [ranR [domRuranR [HdomR [HranR [HdomRuranR H]]]]]].
    apply HdomRuranR in H. destruct H as [H | H].
    + apply HdomR in H. destruct H as [y [xy [Hxy H]]].
      singleton x. rename x0 into Sx. rename H0 into HSx.
      exists Sx. split.
      * apply HSx; trivial.
      * apply HUR. exists xy. split; try assumption.
        apply Hxy. left. assumption.
    + apply HranR in H. rename x into y.
      destruct H as [x [xy [Hxy H]]].
      pair x y. rename x0 into  Pxy. rename H0 into HPxy.
      exists Pxy. split.
      * apply HPxy. right. trivial.
      * apply HUR. exists xy. split; try assumption.
        apply Hxy. right. assumption.
  - apply HfldR. domain R. rename x0 into domR. rename H0 into HdomR.
    range R. rename x0 into ranR. rename H0 into HranR.
    binary_union domR ranR. rename x0 into domRuranR. rename H0 into HdomRuranR.
    exists domR, ranR, domRuranR; repeat (split; try assumption).
    apply HdomRuranR.
    apply HUUR in H. destruct H as [SP [Ha H]].
    apply HUR in H. destruct H as [OP [Hb H]].
    apply HR in H as H'. destruct H' as [a [b Hab]].
    apply Hab in Hb. destruct Hb as [Hb | Hb].
    + left. apply HdomR. exists b, OP. split.
      * apply Hb in Ha. rewrite Ha. assumption.
      * assumption.
    + apply Hb in Ha. destruct Ha as [Ha | Ha].
      * left. apply HdomR. exists b, OP. split; try assumption.
        rewrite Ha. apply Hab.
      * right. apply HranR. exists a, OP. split; try assumption.
        rewrite Ha. assumption.
Qed.

Definition AllDomains (A adA : set) : Prop :=
  forall x, In x adA <-> exists R, In R A /\ Domain R x.

Theorem AllDomains_Exists : forall A, exists adA, AllDomains A adA.
Proof.
  intros A. union A. rename x into UA. rename H into HUA.
  union UA. rename x into UUA. rename H into HUUA.
  union UUA. rename x into UUUA. rename H into HUUUA.
  powerset UUUA. rename x into PUUUA. rename H into HPUUUA.
  build_set
    set
    (fun (t c x : set) => exists R, In R t /\ Domain R x)
    A
    PUUUA.
  rename x into adA. rename H into HadA. exists adA.
  intros x. split; intros H.
  - apply HadA. assumption.
  - apply HadA. split; try assumption.
    apply HPUUUA. intros y Hy. apply HUUUA. destruct H as [R [HR H]].
    apply H in Hy. destruct Hy as [z [yz [Hyz Hy]]].
    singleton y. rename x0 into Sy. rename H0 into HSy.
    exists Sy. split. apply HSy. trivial.
    apply HUUA. exists yz. split.
    + apply Hyz. left. assumption.
    + apply HUA. exists R. split; assumption.
Qed.

Theorem AllDomains_Unique : forall A adA adA', AllDomains A adA ->
  AllDomains A adA' -> adA = adA'.
Proof.
  intros A adA adA' HA HA'.
  apply Extensionality_Axiom. intros x. split; intros H.
  - apply HA', HA. assumption.
  - apply HA, HA'. assumption.
Qed.

Theorem Exercise3_8a : forall A UA domUA adA UadA,
  Union A UA -> Domain UA domUA -> AllDomains A adA -> Union adA UadA ->
  domUA = UadA.
Proof.
  intros A UA domUA adA UadA HUA HdomUA HadA HUadA.
  apply Extensionality_Axiom. intros x. split; intros H.
  - apply HdomUA in H. destruct H as [y [xy [Hxy H]]].
    apply HUA in H. destruct H as [R [HR H]].
    apply HUadA. domain R. rename x0 into domR. rename H0 into HdomR.
    exists domR. split.
    + apply HdomR. exists y, xy. split; try assumption.
    + apply HadA. exists R. split; try assumption.
  - apply HdomUA. apply HUadA in H. destruct H as [domR [Hx H]].
    apply HadA in H. destruct H as [R [HR HdomR]].
    apply HdomR in Hx. destruct Hx as [y [xy [Hxy Hx]]].
    exists y, xy. split; try assumption. apply HUA.
    exists R. split; try assumption.
Qed.

Definition AllRanges (A arA : set) : Prop :=
  forall x, In x arA <-> exists R, In R A /\ Range R x.

Theorem AllRanges_Exists : forall A, exists arA, AllRanges A arA.
Proof.
  intros A. union A. rename x into UA. rename H into HUA.
  union UA. rename x into UUA. rename H into HUUA.
  union UUA. rename x into UUUA. rename H into HUUUA.
  powerset UUUA. rename x into PUUUA. rename H into HPUUUA.
  build_set
    set
    (fun (t c x : set) => exists R, In R t /\ Range R x)
    A
    PUUUA.
  rename x into arA. rename H into HarA.
  exists arA. intros x. split; intros H.
  - apply HarA. assumption.
  - apply HarA; split; try assumption.
    apply HPUUUA. intros y Hy. apply HUUUA.
    destruct H as [R [HR H]]. apply H in Hy.
    rename x into ranR. rename H into HranR.
    destruct Hy as [x [xy [Hxy Hy]]].
    pair x y. rename x0 into Pxy. rename H into HPxy.
    exists Pxy. split.
    + apply HPxy. right. trivial.
    + apply HUUA. exists xy. split.
      * apply Hxy. right. assumption.
      * apply HUA. exists R. split; try assumption.
Qed.

Theorem AllRanges_Unique : forall A arA arA', AllRanges A arA ->
  AllRanges A arA' -> arA = arA'.
Proof.
  intros A arA arA' HA HA'.
  apply Extensionality_Axiom. intros x; split; intros H.
  - apply HA', HA. assumption.
  - apply HA, HA'. assumption.
Qed.

Theorem Exercise3_8b : forall A UA ranUA arA UarA,
  Union A UA -> Range UA ranUA -> AllRanges A arA -> Union arA UarA ->
  ranUA = UarA.
Proof.
  intros A UA ranUA arA UarA HUA HranUA HarA HUarA.
  apply Extensionality_Axiom. intros y; split; intros H.
  - apply HUarA. apply HranUA in H. destruct H as [x [xy [Hxy H]]].
    apply HUA in H. destruct H as [R [HR H]].
    range R. rename x0 into ranR. rename H0 into HranR.
    exists ranR. split.
    + apply HranR. exists x, xy. split; try assumption.
    + apply HarA. exists R. split; try assumption.
  - apply HranUA. apply HUarA in H. destruct H as [ranR [H HranR]].
    apply HarA in HranR. destruct HranR as [R [HR HranR]].
    apply HranR in H. destruct H as [x [xy [Hxy H]]].
    exists x, xy. split; try assumption.
    apply HUA. exists R. split; try assumption.
Qed.

(** Exercise 3-9 : Discuss the result of replacing the union operation by the
    intersection operation in the preceding problem. (TODO) *)

(** We treat the brief section on N-ary relations with the following inductive
    definition and successive results.*)

Inductive NTuple : nat -> set -> Prop :=
  | BTuple : forall x, NTuple 1 x
  | STuple : forall (n : nat) (xy : set),
    (exists x y, OrdPair x y xy /\ NTuple n x) -> NTuple (S n) xy.

Definition N_ary_Relation (n : nat) (R : set) : Prop :=
  forall x, In x R <-> NTuple n x.

Theorem Exercise3_10 : forall x, NTuple 4 x -> NTuple 3 x /\ NTuple 2 x /\
  NTuple 1 x.
Proof.
  intros xy Hfour. inversion Hfour. destruct H0 as [x [y [Hxy H0]]].
  inversion H0. destruct H3 as [x' [y' [Hx'y' H3]]].
  inversion H3. destruct H6 as [x'' [y'' [Hx''y'' H6]]].
  repeat (try split).
  - apply STuple. exists x, y. split; try assumption.
    apply STuple. exists x', y'. split; try assumption.
    apply BTuple.
  - apply STuple. exists x, y. split; try assumption.
    apply BTuple.
  - apply BTuple.
Qed.

(** The first speical kind of relation examined is functions. The distinctive
    property of functions is that they are single-valued, that is, for every x
    in the domain and every y and z in the range, if xFy and xFz then y = z.
    We encode this property in the following definition. *)

Definition SingleValued (R : set) : Prop :=
  forall x y z xy xz, OrdPair x y xy -> OrdPair x z xz ->
  In xy R -> In xz R -> y = z.

Definition Func (F : set) : Prop := Relation F /\ SingleValued F.

(** The notation F(x) describes the unique y such that <x, y> is in F. This
    notation is well-defined under the assumptions that F is a function and 
    x is in the domain of F. We encode this definition below and show that the
    assumptions are sufficient for it to be well-defined. *)

Definition FunVal (F x y : set) : Prop :=
  Func F -> (exists domF, Domain F domF /\ In x domF) -> exists xy,
  OrdPair x y xy /\ In xy F.

(** Such a y exists as a consequence of x being in the domain of F. *)

Theorem FunVal_Exists : forall F x, Func F ->
  (exists domF, Domain F domF /\ In x domF) -> exists y, FunVal F x y.
Proof.
  intros F x HF HdomF.
  destruct HdomF as [domF [HdomF H]].
  apply HdomF in H. destruct H as [y [xy [Hxy H]]].
  exists y. intros _ _. exists xy. split; assumption.
Qed.

(** That y is unique follows from the fact that F is a function. *)

Theorem FunVal_Unique : forall F x y z, Func F ->
  (exists domF, Domain F domF /\ In x domF) -> FunVal F x y ->
  FunVal F x z -> y = z.
Proof.
  intros F x y z HF HdomF Hy Hz.
  apply Hy in HF as Hy'. apply Hy' in HdomF as Hy''.
  apply Hz in HF as Hz'. apply Hz' in HdomF as Hz''.
  clear Hz Hz' Hy Hy'. rename Hz'' into Hz. rename Hy'' into Hy.
  destruct Hy as [xy [Hxy Hy]]. destruct Hz as [xz [Hxz Hz]].
  destruct HF as [HRF HSVF].
  unfold SingleValued in HSVF. apply (HSVF x y z xy xz Hxy Hxz); assumption.
Qed.

Ltac funval H1 H2 F x := destruct (FunVal_Exists F x H1 H2).

(** Next, we define the notion of a function being 'into'. The follows
    Enderton's definition, though there are other uses of the same terminology
    throughout the rest of mathematics. *)

Definition FuncFromInto (F A B : set) : Prop :=
  Func F /\ Domain F A /\ exists ranF, Range F ranF /\ Subset ranF B.

(** A function is 'onto' if a slightly strong property holds (below). Note again
    that this terminology is not consistent through all of mathematics. *)

Definition FuncFromOnto (F A B : set) : Prop :=
  Func F /\ Domain F A /\ Range F B.

(** The definition of being single-rooted-ness is tied to the previous defintion
    of being single-valued in that both properties, as we defined them, may
    apply to any set. For that set to be a function [or one-to-one], it must 
    also be a relation [and a function] in addition to being single-valued
    [or single-rooted]. This somewhat unintuitive fact is due to the fact that
    domains and ranges are defined on any set, not only on relations. In
    computing the domains and ranges of sets that are not relations, the
    the elements which are not ordered pairs are simply ignored. Consequently,
    the domain and range of a set that does not include any ordered pairs as
    members are empty. *)

Definition SingleRooted (R : set) : Prop :=
  forall w x y wy xy, OrdPair w y wy -> OrdPair x y xy ->
  In wy R -> In xy R -> w = x.

Definition OneToOne (F : set) : Prop :=
  Func F /\ SingleRooted F.

(** We now define some standard operations on functions. Note that many of
    these are commonly applies to relations as well. Surprisingly,
    all of the following definitions may be given on arbitrary sets, not
    necessarily on functions or even on relations. Of course, it is typically
    the case that such operations on sets that are not relations are usually not
    useful or interesting, so there are no examples other than on functions and
    relations. *)

Definition Inverse (F F' : set) : Prop :=
  forall yx, In yx F' <-> exists x y xy, OrdPair y x yx /\ OrdPair x y xy /\
  In xy F.

Definition Composition (F G FoG : set) : Prop :=
  forall xz, In xz FoG <-> exists x z y xy yz, OrdPair x z xz /\
  OrdPair x y xy /\ OrdPair y z yz /\ In xy G /\ In yz F.

Definition Restriction (F A FlA : set) : Prop :=
  forall xy, In xy FlA <-> exists x y, OrdPair x y xy /\ In xy F /\ In x A.

Definition Image (A F F_A_ : set) : Prop :=
  forall y, In y F_A_ <-> exists x xy, OrdPair x y xy /\ In x A /\ In xy F.

(** These are all well-defined even without the assumption that F is a function
    or even a relation. This is shown below. *)

Theorem Inverse_Exists : forall F, exists F', Inverse F F'.
Proof.
  intros F.
  domain F. rename x into domF. rename H into HdomF.
  range F. rename x into ranF. rename H into HranF.
  prod ranF domF. rename x into ranFxdomF. rename H into HranFxdomF.
  build_set
    set
    (fun (t c yx : set) =>
      exists x y xy, OrdPair y x yx /\ OrdPair x y xy /\ In xy t)
    F
    ranFxdomF.
  rename x into F'. rename H into HF'.
  exists F'. intros yx. split; intros  H.
  - apply HF'. assumption.
  - apply HF'. split; try assumption.
    destruct H as [x [y [xy [Hyx [Hxy H]]]]].
    apply HranFxdomF. exists y, x. split.
    + apply HranF. exists x, xy. split; try assumption.
    + split; try assumption. apply HdomF.
      exists y, xy. split; assumption.
Qed.

Theorem Inverse_Unique : forall F F' F'', Inverse F F' -> Inverse F F'' ->
  F' = F''.
Proof.
  intros F F' F'' HF' HF''. apply Extensionality_Axiom. intros x; split; intros H.
  - apply HF'', HF'. assumption.
  - apply HF', HF''. assumption.
Qed.

Ltac inverse F := destruct (Inverse_Exists F).

Theorem Composition_Exists : forall F G, exists FoG, Composition F G FoG.
Proof.
  intros F G.
  domain F. rename x into domF. rename H into HdomF.
  domain G. rename x into domG. rename H into HdomG.
  range F. rename x into ranF. rename H into HranF.
  range G. rename x into ranG. rename H into HranG.
  prod domG ranF. rename x into domGxranF. rename H into HdomGxranF.
  build_set
    (prod set set)
    (fun FG (c xz : set) => exists x z y xy yz, OrdPair x z xz /\
      OrdPair x y xy /\ OrdPair y z yz /\ In xy (snd FG) /\ In yz (fst FG))
    (F, G)
    domGxranF.
  rename x into FoG. rename H into HFoG. exists FoG.
  intros xz. split; intros H.
  - apply HFoG. assumption.
  - apply HFoG; split; try assumption. apply HdomGxranF.
    destruct H as [x [z [y [xy [yz [Hxz [Hxy [Hyz [HG HF]]]]]]]]].
    exists x, z. repeat (split; try assumption).
    + apply HdomG. exists y, xy. split; assumption.
    + apply HranF. exists y, yz. split; assumption.
Qed.

Theorem Composition_Unique : forall F G FoG FoG',
  Composition F G FoG -> Composition F G FoG' -> FoG = FoG'.
Proof.
  intros F G FoG FoG' HFoG HFoG'.
  apply Extensionality_Axiom. intros x. split; intros H.
  - apply HFoG', HFoG. assumption.
  - apply HFoG, HFoG'. assumption.
Qed.

Ltac compose f g := destruct (Composition_Exists f g).

Theorem Restriction_Exists : forall F A, exists FlA, Restriction F A FlA.
Proof.
  intros F A.
  build_set
    set
    (fun (t c xy : set) => exists x y, OrdPair x y xy /\ In xy c /\ In x t)
    A
    F.
  rename x into FlA. rename H into HFlA. exists FlA.
  intros xy; split; intros H.
  - apply HFlA. assumption.
  - apply HFlA. split; try assumption.
    destruct H as [x [y [Hxy [HF HA]]]].
    assumption.
Qed.

Theorem Restriction_Unique : forall F A FlA FlA',
  Restriction F A FlA -> Restriction F A FlA' -> FlA = FlA'.
Proof.
  intros F A FlA FlA' H H'.
  apply Extensionality_Axiom. intros x; split; intros P.
  - apply H', H, P.
  - apply H, H', P.
Qed.

Ltac restrict F A := destruct (Restriction_Exists F A).

Theorem Image_Exists : forall A F, exists F_A_, Image A F F_A_.
Proof.
  intros A F.
  union F. rename x into UF. rename H into HUF.
  union UF. rename x into UUF. rename H into HUUF.
  build_set
    set
    (fun (t c y : set) => exists x xy, OrdPair x y xy /\ In x t /\ In xy F)
    A
    UUF.
  rename x into F_A_. rename H into HF_A_. exists F_A_.
  intros y. split; intros H.
  - apply HF_A_. assumption.
  - apply HF_A_. split; try assumption.
    apply HUUF. destruct H as [x [xy [Hxy [HA H]]]].
    pair x y. rename x0 into Pxy. rename H0 into HPxy.
    exists Pxy. split.
    + apply HPxy. right. trivial.
    + apply HUF. exists xy. split; try assumption.
      apply Hxy. right. assumption.
Qed.

Theorem Image_Unique : forall A F F_A_ F_A_',
  Image A F F_A_ -> Image A F F_A_' -> F_A_ = F_A_'.
Proof.
  intros A F F_A_ F_A_' H H'.
  apply Extensionality_Axiom. intros x; split; intros P.
  - apply H', H, P.
  - apply H, H', P.
Qed.

Ltac image A F := destruct (Image_Exists A F).

Corollary Image_Equals_RestrictionRange : forall A F FlA ranFlA F_A_,
  Restriction F A FlA -> Range FlA ranFlA -> Image A F F_A_ -> ranFlA = F_A_.
Proof.
  intros A F FlA ranFlA F_A_ HFlA HranFlA HF_A_.
  apply Extensionality_Axiom. intros y. split; intros H.
  - apply HF_A_. apply HranFlA in H. destruct H as [x [xy [Hxy H]]].
    apply HFlA in H. destruct H as [a [b [Hab [HF HA]]]].
    exists x, xy. repeat (split; try assumption).
    assert (P : x = a /\ y = b).
    { apply (Enderton3A x y a b xy xy); try assumption; trivial. }
    destruct  P as [P _]. rewrite P. assumption.
  - apply HranFlA. apply HF_A_ in H.
    destruct H as [x [xy [Hxy [HA HF]]]].
    exists x, xy. split; try assumption.
    apply HFlA. exists x, y. repeat (split; try assumption).
Qed.

(** We can now turn our attention to some of the properties of these operations.
    We start with inverses: *)

Theorem Enderton3E : forall F F' F'' domF ranF,
  Inverse F F' -> Inverse F' F'' -> Domain F domF -> Range F ranF ->
  Domain F' ranF /\ Range F' domF /\ (Relation F -> F'' = F).
Proof.
  intros F F' F'' domF ranF HF' HF'' HdomF HranF.
  split.
  - intros y; split; intros H.
    + apply HranF in H.
      destruct H as [x [xy [Hxy H]]].
      ordpair y x. rename x0 into yx. rename H0 into Hyx.
      exists x, yx. split; try assumption.
      apply HF'. exists x, y, xy. repeat (split; try assumption).
    + apply HranF. destruct H as [x [yx [Hyx H]]].
      ordpair x y. rename x0 into xy. rename H0 into Hxy.
      exists x, xy. split; try assumption.
      apply HF' in H. destruct H as [a [b [ab [Hba [Hab H]]]]].
      assert (P : y = b /\ x = a).
      { apply (Enderton3A y x b a yx yx Hyx Hba). trivial. }
      destruct P as [P1 P2]. rewrite <- P1, <- P2 in Hab.
      assert (Q : ab = xy). { apply (OrdPair_Unique x y ab xy Hab Hxy). }
      rewrite <- Q. assumption.
  - split.
    + intros x; split; intros H.
      * apply HdomF in H. destruct H as [y [xy [Hxy H]]].
        ordpair y x. rename x0 into yx. rename H0 into Hyx.
        exists y, yx. split; try assumption.
        apply HF'. exists x, y, xy. repeat (split; try assumption).
      * apply HdomF. destruct H as [y [yx [Hyx H]]].
        ordpair x y. rename x0 into xy. rename H0 into Hxy.
        exists y, xy. split; try assumption.
        apply HF' in H. destruct H as [a [b [ab [Hba [Hab H]]]]].
        assert (P : y = b /\ x = a).
        { apply (Enderton3A y x b a yx yx Hyx Hba). trivial. }
        destruct P as [P Q]. rewrite <- P in Hab. rewrite <- Q in Hab.
        assert (R : ab = xy). { apply (OrdPair_Unique x y); assumption. }
        rewrite <- R. assumption.
    + intros HF. apply Extensionality_Axiom. intros xy. split; intros H.
      * apply HF'' in H. destruct H as [y [x [yx [Hxy [Hyx H]]]]].
        apply HF' in H. destruct H as [a [b [ab [Hba [Hab H]]]]].
        assert (P : y = b /\ x = a).
        { apply (Enderton3A y x b a yx yx Hyx Hba). trivial. }
        destruct P as [P Q]. rewrite <- P in Hab. rewrite <- Q in Hab.
        assert (R : xy = ab). { apply (OrdPair_Unique x y); assumption. }
        rewrite R. assumption.
      * apply HF in H as H'. destruct H' as [x [y Hxy]].
        apply HF''. ordpair y x. rename x0 into yx. rename H0 into Hyx.
        exists y, x, yx. repeat (split; try assumption).
        apply HF'. exists x, y, xy. repeat (split; try assumption).
Qed.

Theorem Enderton3F : forall F F', Inverse F F' ->
  (Func F' <-> SingleRooted F) /\ (Relation F -> (Func F <-> SingleRooted F')).
Proof.
  intros F F' HF'. split.
  - split; intros H; try split.
    + intros w x y wy xy Hwy Hxy Hwy' Hxy'.
      destruct H as [H I].
      ordpair y x. rename x0 into yx. rename H0 into Hyx.
      ordpair y w. rename x0 into yw. rename H0 into Hyw.
      apply (I y w x yw yx); try assumption.
      * apply HF'. exists w, y, wy. repeat (split; try assumption).
      * apply HF'. exists x, y, xy. repeat (split; try assumption).
    + intros yx Hyx. apply HF' in Hyx.
      destruct Hyx as [x [y [xy [Hyx [Hxy HF]]]]].
      exists y, x. assumption.
    + intros y. intros w x yw yx Hyw Hyx Hyw' Hyx'.
      apply HF' in Hyw'. apply HF' in Hyx'.
      destruct Hyw' as [a [b [ab [Hba [Hab I]]]]].
      destruct Hyx' as [c [d [cd [Hdc [Hcd J]]]]].
      assert (P : y = b /\ w = a).
      { apply (Enderton3A y w b a yw yw Hyw Hba). trivial. }
      assert (Q : y = d /\ x = c).
      { apply (Enderton3A y x d c yx yx Hyx Hdc). trivial. }
      destruct P as [P1 P2]. destruct Q as [Q1 Q2].
      rewrite <- P1, <- P2 in Hab. rewrite <- Q1, <- Q2 in Hcd.
      apply (H w x y ab cd); assumption.
  - intros HR. split; intros H; try split.
    + unfold SingleRooted. intros y z x yx zx Hyx Hzx Hyx' Hzx'.
      apply HF' in Hyx'. apply HF' in Hzx'.
      destruct H as [_ I].
      destruct Hyx' as [a [b [ab [Hba [Hab J]]]]].
      destruct Hzx' as [c [d [cd [Hdc [Hcd K]]]]].
      assert (P : y = b /\ x = a).
      { apply (Enderton3A y x b a yx yx Hyx Hba). trivial. }
      assert (Q : z = d /\ x = c).
      { apply (Enderton3A z x d c zx zx Hzx Hdc). trivial. }
      destruct P as [P1 P2]. destruct Q as [Q1 Q2].
      rewrite <- P1, <- P2 in Hab.
      rewrite <- Q1, <- Q2 in Hcd.
      unfold SingleValued in I. apply (I x y z ab cd Hab Hcd J K).
    + assumption.
    + intros x y z xy xz Hxy Hxz Hxy' Hxz'.
      ordpair y x. rename x0 into yx. rename H0 into Hyx.
      ordpair z x. rename x0 into zx. rename H0 into Hzx.
      apply (H y z x yx zx Hyx Hzx).
      * apply HF'. exists x, y, xy. repeat (split; try assumption).
      * apply HF'. exists x, z, xz. repeat (split; try assumption).
Qed.

Theorem Enderton3G : forall x y F F' domF ranF Fx F'Fx F'y FF'y,
  Inverse F F' -> Domain F domF -> Range F ranF -> FunVal F x Fx ->
  FunVal F' Fx F'Fx -> FunVal F' y F'y -> FunVal F F'y FF'y -> OneToOne F ->
  (In x domF -> F'Fx = x) /\ (In y ranF -> FF'y = y).
Proof.
  intros x y F F' domF ranF Fx F'Fx F'y FF'y HF' HdomF HranF HFx HF'Fx HF'y HFF'y H.
  split; intros I.
  - destruct H as [H J]. apply (Enderton3F F F' HF') in J.
    apply HFx in H as HFx'. clear HFx. rename HFx' into HFx.
    assert (P : exists domF, Domain F domF /\ In x domF).
    { exists domF. split; assumption. }
    apply HFx in P as HFx'. clear HFx P. rename HFx' into HFx.
    destruct HFx as [xy [Hxy HFx]].
    apply HF'Fx in J as HF'Fx'. clear HF'Fx. rename HF'Fx' into HF'Fx.
    assert (P : exists domF', Domain F' domF' /\ In Fx domF').
    { exists ranF. split.
      - inverse F'. rename x0 into F''.
        domain F'. rename x0 into domF'.
        range F'. rename x0 into ranF'.
        apply (Enderton3E F F' F'' domF ranF); try assumption.
      - apply HranF. exists x, xy. split; assumption. }
    apply HF'Fx in P as HF'Fx'. clear HF'Fx P. rename HF'Fx' into HF'Fx.
    destruct HF'Fx as [yx [Hyx HF'Fx]].
    ordpair Fx x. rename x0 into yx'. rename H0 into Hyx'.
    assert (P : In yx' F').
    { apply HF'. exists x, Fx, xy.  repeat (split; try assumption). }
    destruct J as [_ J]. unfold SingleValued in J.
    apply (J Fx F'Fx x yx yx'); try assumption.
  - destruct H as [H J]. apply (Enderton3F F F' HF') in J.
    apply HF'y in J as HF'y'. clear HF'y. rename HF'y' into HF'y.
    assert (P : exists domF', Domain F' domF' /\ In y domF').
    { exists ranF. split.
      - inverse F'. rename x0 into F''.
        domain F'. rename x0 into domF'.
        range F'. rename x0 into ranF'.
        apply (Enderton3E F F' F'' domF ranF); try assumption.
      - assumption. }
    apply HF'y in P as HF'y'. clear HF'y P. rename HF'y' into HF'y.
    destruct HF'y as [yx [Hyx HF'y]].
    apply HFF'y in H as HFF'y'. clear HFF'y. rename HFF'y' into HFF'y.
    ordpair F'y y. rename x0 into xy. rename H0 into Hxy.
    apply HF' in HF'y. destruct HF'y as [a [b [ab [Hba [Hab HF'y]]]]].
    assert (P : y = b /\ F'y = a).
    { apply (Enderton3A y F'y b a yx yx Hyx Hba). trivial. }
    destruct P as [P1 P2]. rewrite <- P1, <- P2 in Hab.
    assert (Q : xy = ab).
    { apply (OrdPair_Unique F'y y xy ab Hxy Hab). }
    rewrite <- Q in HF'y.
    assert (P : exists domF, Domain F domF /\ In F'y domF).
    { exists domF. split; try assumption.
      apply HdomF. exists y, xy. split; try assumption. }
    apply HFF'y in P as HFF'y'. clear HFF'y P. rename HFF'y' into HFF'y.
    destruct HFF'y as [xy' [Hxy' HFF'y]].
    destruct H as [_ H]. apply (H F'y FF'y y xy' xy Hxy' Hxy HFF'y HF'y).
Qed.

Definition DomComp (F G X : set) : Prop :=
  Func G -> forall x, In x X <-> exists domG Gx domF,
  Domain G domG /\ FunVal G x Gx /\ Domain F domF /\
  In x domG /\ In Gx domF.

(** We will need the following auxiliary definition in order to state
    the next theorem. As always, we prove that it is well-defined.*)

Theorem DomComp_Exists : forall F G, Func G -> exists X, DomComp F G X.
Proof.
  intros F G H. domain G. rename x into domG. rename H0 into HdomG.
  build_set
    (prod set set)
    (fun (t : set * set) (c x : set) => exists domG Gx domF,
      Domain (snd t) domG /\ FunVal (snd t) x Gx /\ Domain (fst t) domF /\
      In x domG /\ In Gx domF)
    (F, G)
    domG.
  rename x into X. rename H0 into HX.
  exists X. intros _ x. split; intros I.
  - apply HX. assumption.
  - apply HX. split; try assumption.
    destruct I as [domG' [Gx [DomF [HdomG' [HGx [HdomF [I J]]]]]]].
    rewrite (Domain_Unique G domG domG' HdomG HdomG'). assumption.
Qed.

Theorem DomComp_Unique : forall F G, Func G -> forall X Y, DomComp F G X ->
  DomComp F G Y -> X = Y.
Proof.
  intros F G H X Y HX HY. apply Extensionality_Axiom. intros x; split; intros I.
  - apply (HY H), (HX H). assumption.
  - apply (HX H), (HY H). assumption.
Qed.

Theorem Enderton3H : forall F G FoG domFoG,
  Composition F G FoG -> DomComp F G domFoG -> Func F -> Func G ->
  (Func FoG) /\ (Domain FoG domFoG) /\ (forall x FoGx Gx FGx,
  FunVal FoG x FoGx -> FunVal G x Gx -> FunVal F Gx FGx -> In x domFoG ->
  FoGx = FGx).
Proof.
  intros F G FoG domFoG HFoG HdomFoG HF HG.
  assert (P : Func FoG).
  { split.
    - intros xz H. apply HFoG in H.
      destruct H as [x [z [y [xy [yz [Hxz [Hxy [Hyz [H I]]]]]]]]].
      exists x, z. assumption.
    - intros x z z' xz xz' Hxz Hxz' H H'.
      apply HFoG in H. apply HFoG in H'.
      destruct H as [a [c [b [ab [bc [Hac [Hab [Hbc [H1 H2]]]]]]]]].
      destruct H' as [a' [c' [b' [ab' [bc' [Hac' [Hab' [Hbc' [H1' H2']]]]]]]]].
      assert (P : a = x /\ c = z).
      { apply (Enderton3A a c x z xz xz Hac Hxz). trivial. }
      destruct P as [P1 P2].
      assert (P' : a' = x /\ c' = z').
      { apply (Enderton3A a' c' x z' xz' xz' Hac' Hxz'). trivial. }
      destruct P' as [P1' P2'].
      rewrite P1 in Hab. rewrite P2 in Hbc.
      rewrite P1' in Hab'. rewrite P2' in Hbc'.
      assert (Q : b = b').
      { destruct HG as [_ HG]. apply (HG x b b' ab ab' Hab Hab' H1 H1'). }
      rewrite <- Q in Hbc'. destruct HF as [_ HF].
      apply (HF b z z' bc bc' Hbc Hbc' H2 H2'). }
  split; try assumption.
  assert (Q : Domain FoG domFoG).
  { intros x. split; intros H.
    - apply HdomFoG in H; try assumption.
      destruct H as [domG [Gx [domF [HdomG [HGx [HdomF [H I]]]]]]].
      apply HdomF in I. destruct I as [FGx [yz [Hyz I]]].
      ordpair x FGx. rename x0 into xz. rename H0 into Hxz.
      exists FGx, xz. split; try assumption. apply HFoG.
      ordpair x Gx. rename x0 into xy. rename H0 into Hxy.
      exists x, FGx, Gx, xy, yz. repeat (split; try assumption).
      assert (Q : exists domG, Domain G domG /\ In x domG).
      { exists domG; split; try assumption. }
      destruct (HGx HG Q) as [xy' [Hxy' HGx']].
      assert (R : xy = xy'). { apply (OrdPair_Unique x Gx xy xy' Hxy Hxy'). }
      rewrite R. assumption.
    - destruct H as [z [xz [Hxz H]]]. apply (HdomFoG); try assumption.
      domain G. rename x0 into domG. rename H0 into HdomG.
      domain F. rename x0 into domF. rename H0 into HdomF.
      apply HFoG in H. destruct H as [a [c [b [ab [bc [Hac [Hab [Hbc [H I]]]]]]]]].
      assert (T : x = a /\ z = c).
      { apply (Enderton3A x z a c xz xz Hxz Hac). trivial. }
      exists domG, b, domF. repeat (split; try assumption).
      + intros _ [domG' [HdomG' J]]. exists ab.
        split; try assumption.
        destruct T as [T _]. rewrite T. assumption.
      + apply HdomG. exists b, ab. split; try assumption.
        destruct T as [T _]. rewrite T. assumption.
      + apply HdomF. exists c, bc. split; try assumption. }
  split; try assumption.
  intros x FoGx Gx FGx HFoGx HGx HFGx H.
  apply Q in H. destruct H as [z [xz [Hxz H]]].
  apply HFoG in H. destruct H as [a [c [b [ab [bc [Hac [Hab [Hbc [H I]]]]]]]]].
  assert (R : a = x /\ c = z). { apply (Enderton3A a c x z xz xz Hac Hxz). trivial. }
  destruct R as [R1 R2]. rewrite R1 in Hab. rewrite R2 in Hbc.
  apply HGx in HG as HGx'. clear HGx. rename HGx' into HGx.
  assert (S : exists domG, Domain G domG /\ In x domG).
  { domain G. exists x0. split; try assumption. apply H0.
    exists b, ab. split; try assumption.  }
  apply HGx in S. clear HGx. rename S into HGx. destruct HGx as [xy [Hxy HGx]].
  assert (S : Gx = b).
  { destruct HG as [_ HG]. apply (HG x Gx b xy ab Hxy Hab HGx H). }
  rewrite <- S in Hab. rewrite <- S in Hbc.
  apply HFGx in HF as HFGx'. clear HFGx. rename HFGx' into HGFx.
  assert (T : exists domF, Domain F domF /\ In Gx domF).
  { domain F. exists x0. split; try assumption.
    apply H0. exists z, bc. split; assumption. }
  apply HGFx in T. clear HGFx. rename T into HFGx.
  destruct HFGx as [yz [Hyz HFGx]].
  apply HFoGx in P as HFoGx'. clear HFoGx. rename HFoGx' into HFoGx.
  assert (T : exists domFoG, Domain FoG domFoG /\ In x domFoG).
  { exists domFoG. split; try assumption.
    apply Q. exists z, xz. split; try assumption. apply HFoG.
    exists x, z, Gx, ab, bc. repeat (split; try assumption). }
  apply HFoGx in T. clear HFoGx. rename T into HFoGx.
  destruct HFoGx as [xz' [Hxz' HFoGx]].
  assert (J : In xz FoG).
  { apply HFoG. exists x, z, Gx, ab, bc. repeat (split; try assumption). }
  assert (T : z = FoGx).
  { destruct P as [_ P]. apply (P x z FoGx xz xz'); try assumption. }
  assert (U : FGx = z).
  { destruct P as [_ P]. ordpair x FGx. apply (P x FGx z x0 xz); try assumption.
    apply HFoG. exists x, FGx, Gx, xy, yz. repeat (split; try assumption). }
  rewrite U. symmetry. assumption.
Qed.

Theorem Enderton3I : forall F G FoG FoG' F' G' G'oF',
  Composition F G FoG -> Inverse FoG FoG' -> Inverse F F' -> Inverse G G' ->
  Composition G' F' G'oF' -> FoG' = G'oF'.
Proof.
  intros F G FoG FoG' F' G' G'oF' HFoG HFoG' HF' HG' HG'oF'.
  apply Extensionality_Axiom. intros zx; split; intros H.
  - apply HG'oF'. apply HFoG' in H.
    destruct H as [x [z [xz [Hzx [Hxz H]]]]].
    apply HFoG in H. destruct H as [a [c [b [ab [bc [Hac [Hab [Hbc [H I]]]]]]]]].
    assert (P : a = x /\ c = z).
    { apply (Enderton3A a c x z xz xz Hac Hxz). trivial. }
    destruct P as [P1 P2]. rewrite P1 in Hab. rewrite P2 in Hbc.
    rename b into y. rename ab into xy. rename bc into yz.
    rename Hab into Hxy. rename Hbc into Hyz.
    ordpair y x. rename x0 into yx. rename H0 into Hyx.
    ordpair z y. rename x0 into zy. rename H0 into Hzy.
    exists z, x, y, zy, yx. repeat (split; try assumption).
    + apply HF'. exists y, z, yz. repeat (split; try assumption).
    + apply HG'. exists x, y, xy. repeat (split; try assumption).
  - apply HG'oF' in H. destruct H as [z [x [y [zy [yx [Hzx [Hzy [Hyx [H I]]]]]]]]].
    apply HF' in H. destruct H as [b [c [bc [Hcb [Hbc H]]]]].
    apply HG' in I. destruct I as [a [b' [ab [Hba [Hab I]]]]].
    assert (P : c = z /\ b = y).
    { apply (Enderton3A c b z y zy zy Hcb Hzy). trivial. }
    destruct P as [P1 P2].
    assert (Q : b' = y /\ a = x).
    { apply (Enderton3A b' a y x yx yx Hba Hyx). trivial. }
    destruct Q as [Q1 Q2].
    rewrite P1, P2 in Hbc. rewrite Q1, Q2 in Hab.
    rename bc into yz. rename ab into xy.
    ordpair x z. rename x0 into xz. rename H0 into Hxz.
    apply HFoG'. exists x, z, xz. repeat (split; try assumption).
    apply HFoG. exists x, z, y, xy, yz. repeat (split; try assumption).
Qed.

(** Arguably the most interesting result in this chapter, Theorem 3J is next.
    It involves left and right inverses of functions as well as more advanced
    properties of functions, for which we now given definitions. *)

Definition Identity (A IA : set) : Prop :=
  forall xx, In xx IA <-> exists x, In x A /\ OrdPair x x xx.

Theorem Identity_Exists : forall A, exists IA, Identity A IA.
Proof.
  intros A. prod A A. rename x into AxA. rename H into HAxA.
  build_set
    set
    (fun (t c xx : set) => exists x, In x t /\ OrdPair x x xx )
    A
    AxA.
  rename x into IA. rename H into HIA. exists IA.
  intros xx. split; intros H.
  - apply HIA. assumption.
  - apply HIA. split; try assumption.
    destruct H as [x [H Hxx]]. apply HAxA. exists x, x.
    repeat (split; try assumption).
Qed.

Theorem Identity_Unique : forall A IA IA', Identity A IA -> Identity A IA' ->
  IA = IA'.
Proof.
  intros A IA IA' H H'. apply Extensionality_Axiom. intros x; split; intros I.
  - apply H', H, I.
  - apply H, H', I.
Qed.

Corollary Identity_Function : forall A IA, Identity A IA -> Func IA.
Proof.
  intros A IA HIA. split.
  - intros xx Hxx. apply HIA in Hxx as [x [Hx Hxx]].
    exists x, x. assumption.
  - intros x y z xy xz Hxy Hxz H I. apply HIA in H. apply HIA in I.
    destruct H as [x0 [H0 H]]. destruct I as [x1 [H1 I]].
    assert (P : x = x0 /\ y = x0).
    { apply (Enderton3A x y x0 x0 xy xy Hxy H). trivial. }
    assert (Q : x = x1 /\ z = x1).
    { apply (Enderton3A x z x1 x1 xz xz Hxz I). trivial. }
    destruct P as [P1 P2]. destruct Q as [Q1 Q2].
    rewrite Q1 in P1. rewrite P1 in Q2. rewrite <- P2 in Q2.
    symmetry. assumption.
Qed.

Definition LeftInverse (F A B G : set) : Prop :=
  FuncFromInto F A B -> ~Empty A -> exists GoF, Composition G F GoF /\
  FuncFromInto G B A /\ Identity A GoF.

Definition RightInverse (F A B H : set) : Prop :=
  FuncFromInto F A B -> ~ Empty A -> exists FoH, Composition F H FoH /\
  FuncFromInto H B A /\ Identity B FoH.

(** The proof that the above two definitions are well-defined is absorbed by
    Theorem 3J, which makes the stronger iff. claim about existence under the
    given conditions. We also show uniqueness immediately after the theorem
    (TODO). Interestingly, the Axiom of Choice is required to show the second
    half of the theorem treating right-inverses, placing it beyond the domain of
    ZF set theory and only in the domain of ZFC. *)

Theorem Enderton3Ja : forall F A B, FuncFromInto F A B -> ~ Empty A ->
  (exists G, LeftInverse F A B G) <-> OneToOne F.
Proof.
  intros F A B HFAB HA. split; intros H.
  - destruct H as [G H]. unfold LeftInverse in H.
    destruct (H HFAB HA) as [GoF [HGoF [HGBA H']]].
    clear H; rename H' into H.
    destruct HFAB as [HF [HdomF [ranF [HranF HFAB]]]]. split; try assumption.
    intros w x y wy xy Hwy Hxy I J.
    destruct HGBA as [HG [HdomG [ranG [HranG HGBA]]]].
    assert (P : Func GoF).
    { apply (Identity_Function A). assumption. }
    assert (Q : FunVal GoF w w).
    { intros _ _. ordpair w w. rename x0 into ww. rename H0 into Hww.
      exists ww. split; try assumption.
      apply H. exists w. split; try assumption.
      apply HdomF. exists y, wy. split; try assumption. }
    assert (R : FunVal GoF x x).
    { intros _ _. ordpair x x. rename x0 into xx. rename H0 into Hxx.
      exists xx. split; try assumption.
      apply H. exists x. split; try assumption.
      apply HdomF. exists y, xy. split; try assumption. }
    apply R in P as R'. clear R. rename R' into R.
    apply Q in P as Q'. clear Q. rename Q' into Q.
    assert (T : exists domGoF, Domain GoF domGoF /\ In w domGoF).
    { domain GoF. exists x0. split; try assumption. apply H0.
      ordpair w w. exists w, x1. split; try assumption.
      apply H. exists w. split; try assumption. apply HdomF.
      exists y, wy. split; assumption. }
    apply Q in T as Q'. clear Q. rename Q' into Q. clear T.
    assert (T : exists domGoF, Domain GoF domGoF /\ In x domGoF).
    { domain GoF. exists x0. split; try assumption. apply H0.
      ordpair x x. exists x, x1. split; try assumption.
      apply H. exists x. split; try assumption.
      apply HdomF. exists y, xy. split; assumption. }
    apply R in T as R'. clear R. rename R' into R. clear T.
    destruct Q as [ww [Hww Q]]. destruct R as [xx [Hxx R]].
    apply HGoF in Q. apply HGoF in R.
    destruct Q as [w' [w'' [y' [wy' [yw' [Hww' [Hwy' [Hyw' [Q1 Q2]]]]]]]]].
    assert (T : w' = w /\ w'' = w).
    { apply (Enderton3A w' w'' w w ww ww Hww' Hww). trivial. }
    destruct T as [T1 T2]. replace w' with w in *. clear w' T1.
    replace w'' with w in *. clear w'' T2.
    assert (T : y = y').
    { destruct HF as [_ HF]. apply (HF w y y' wy wy' Hwy Hwy' I Q1). }
    replace y' with y in *. clear y' T.
    destruct R as [x' [x'' [y' [xy' [yx' [Hxx' [Hxy' [Hyx' [R1 R2]]]]]]]]].
    assert (T : x' = x /\ x'' = x).
    { apply (Enderton3A x' x'' x x xx xx Hxx' Hxx). trivial. }
    destruct T as [T1 T2]. replace x' with x in *. clear x' T1.
    replace x'' with x in *. clear x'' T2.
    assert (T : y = y').
    { destruct HF as [_ HF]. apply (HF x y y' xy xy' Hxy Hxy' J R1). }
    replace y' with y in *. clear y' T.
    destruct HG as [_ HG]. apply (HG y w x yw' yx' Hyw' Hyx' Q2 R2).
  - inverse F. rename x into F'. rename H0 into HF'.
    destruct HFAB as [HF [HdomF [ranF [HranF HFAB]]]].
    assert (P : FuncFromOnto F' ranF A).
    { split.
      - destruct H as [_ H]. apply (Enderton3F F F' HF'). assumption.
      - split.
        + inverse F'. domain F'. range F'.
          apply (Enderton3E F F' x A ranF HF' H0 HdomF HranF).
        + inverse F'. domain F'. range F'.
          apply (Enderton3E F F' x A ranF HF' H0 HdomF HranF). }
    apply Member_Exists_If_NonEmpty in HA. destruct HA as [a Ha].
    singleton a. rename x into Sa. rename H0 into HSa.
    minus B ranF. rename x into BmranF. rename H0 into  HBmranF.
    prod BmranF Sa. rename x into BmranFxSa. rename H0 into HBmranFxSa.
    binary_union F' BmranFxSa. rename x into G. rename H0 into HG.
    exists G. intros _ _. compose G F. rename x into GoF. rename H0 into HGoF.
    exists GoF. split; try assumption. split.
      + split.
        * split.
          { intros yx Hyx. apply HG in Hyx. destruct Hyx as [I | I].
            - apply HF' in I.  destruct I as [x [y [_ [I _]]]].
              exists y, x. assumption.
            - apply HBmranFxSa in I. destruct I as [b [a' [_ [_ I]]]].
              exists b, a'. assumption. }
          { intros x y z xy xz Hxy Hxz I J. apply HG in I. apply HG in J.
            destruct I as [I | I]; destruct J as [J | J].
            - destruct P as [[_ P] _]. apply (P x y z xy xz Hxy Hxz I J).
            - apply HBmranFxSa in J as [b [a' [Hb [Ha' J]]]].
              apply HBmranF in Hb as [Hb Hb'].
              assert (T : b = x /\ a' = z).
              { apply (Enderton3A b a' x z xz xz J Hxz). trivial. }
              destruct T as [T _]. replace b with x in *. clear T b.
              assert (Q : In x ranF).
              { apply HF' in I. destruct I as [y' [x' [yx' [Hxy' [Hyx' I]]]]].
                apply HranF. exists y', yx'. split; try assumption.
                replace x with x'. assumption.
                apply (Enderton3A x' y' x y xy xy Hxy' Hxy). trivial. }
              apply Hb' in Q. destruct Q.
            - apply HBmranFxSa in I as [b [a' [Hb [Ha' I]]]].
              apply HBmranF in Hb as [Hb Hb'].
              assert (T : b = x /\ a' = y).
              { apply (Enderton3A b a' x y xy xy I Hxy). trivial. }
              destruct T as [T _ ]. replace b with  x in *. clear T b.
              assert (Q : In x ranF).
              { apply HF' in J. destruct J as [z' [x' [zx' [Hxz' [Hzx' J]]]]].
                apply HranF. exists z', zx'. split; try assumption.
                replace x with x'. assumption.
                apply (Enderton3A x' z' x z xz xz Hxz' Hxz). trivial. }
              apply Hb' in Q. destruct Q.
            - apply HBmranFxSa in I. apply HBmranFxSa in J.
              destruct I as [x' [y' [Hx' [Hy' I]]]].
              destruct J as [x'' [z' [Hx'' [Hz' J]]]].
              apply HSa in Hy'. apply HSa in Hz'.
              rewrite Hy' in I. rewrite Hz' in J.
              replace y with a.
              apply (Enderton3A x'' a x z xz xz J Hxz). trivial.
              apply (Enderton3A x' a x y xy xy I Hxy). trivial. }
        * split.
          { intros y. split; intros I.
            - assert (Q : In y ranF \/ ~ In y ranF). { apply REM. }
              destruct Q as [Q | Q].
              + apply HranF in Q as [x [xy [Hxy Q]]].
                ordpair y x. exists x, x0. split; try assumption.
                apply HG. left. apply HF'. exists x, y, xy.
                repeat (split; try assumption).
              + ordpair y a. exists a, x. split; try assumption.
                apply HG. right. apply HBmranFxSa.
                exists y, a. repeat (split; try assumption).
                * apply HBmranF. split; try assumption.
                * apply HSa. trivial.
            - destruct I as [x [yx [Hyx I]]]. apply HG in I. destruct I as [I | I].
              + apply HF' in I. apply HFAB. apply HranF.
                destruct I as [x' [y' [xy [Hyx' [Hxy I]]]]].
                exists x, xy. split; try assumption.
                replace x with x'. replace y with y'. assumption.
                apply (Enderton3A y' x' y x yx yx Hyx' Hyx). trivial.
                apply (Enderton3A y' x' y x yx yx Hyx' Hyx); trivial.
              + apply HBmranFxSa in I. destruct I as [y' [x' [Hy' [Hx I]]]].
                apply HBmranF in Hy'. replace y with y'. apply Hy'.
                apply (Enderton3A y' x' y x yx yx I Hyx). trivial. }
          { range G. rename x into ranG. rename H0 into HranG.
            exists ranG. split; try assumption. intros x Hx.
            apply HranG in Hx. destruct Hx as [y [yx [Hyx Hx]]].
            ordpair x y. rename x0 into xy. rename H0 into Hxy.
            apply HG in Hx. destruct Hx as [Hx | Hx].
            - apply HdomF. exists y, xy. split; try assumption.
              apply HF' in Hx. destruct Hx as [x' [y' [xy' [Hyx' [Hxy' Hx]]]]].
              assert (T : y' = y /\ x' = x).
              { apply (Enderton3A y' x' y x yx yx Hyx' Hyx). trivial. }
              destruct T as [T1 T2]. replace y' with y in *. replace x' with x in *.
              clear T1 T2 x' y'. replace xy with xy'; try assumption.
              apply (OrdPair_Unique x y xy' xy Hxy' Hxy).
            - apply HBmranFxSa in Hx. destruct Hx as [b [a' [Hb [Ha' Hx]]]].
              assert (T : b = y /\ a' = x).
              { apply (Enderton3A b a' y x yx yx Hx Hyx). trivial. }
              destruct T as [T1 T2]. replace b with y in *.
              replace a' with x in *. clear T1 T2 a' b.
              apply HSa in Ha'. rewrite Ha'. assumption. }
      + intros xx. split; intros I.
        * apply HGoF in I.
          destruct I as [x [x' [y [xy [yx [Hxx [Hxy [Hyx [I J]]]]]]]]].
          apply HG in J. destruct J as [J | J].
          { apply HF' in J. destruct J as [u [v [xy' [Hyx' [Hxy' K]]]]].
            assert (T : y = v /\ x' = u).
            { apply (Enderton3A y x' v u yx yx Hyx Hyx'). trivial. }
            destruct T as [T1 T2]. replace v with y in *.
            replace u with x' in *. clear T1 T2 u v. exists x. split.
            - apply HdomF. exists y, xy. split; try assumption.
            - replace x' with x in Hxx. assumption.
              destruct H as [_ H]. apply (H x x' y xy xy'); try assumption. }
          { apply HBmranFxSa in J. destruct J as [b [a' [Hb [Ha' J]]]].
            assert (T : b = y /\ a' = x').
            { apply (Enderton3A b a' y x' yx yx J Hyx). trivial. }
            destruct T as [T1 T2]. replace b with y in *. replace a' with x' in *.
            clear T1 T2 a' b. apply HBmranF in Hb. destruct Hb as [Hb Hb'].
            assert (Q : In y ranF).
            { apply HranF. exists x, xy. split; assumption. }
            apply Hb' in Q. destruct Q. }
        * destruct I as [x [Hx Hxx]]. apply HGoF.
          apply HdomF in Hx. destruct Hx as [y [xy [Hxy I]]].
          ordpair y x. rename x0 into yx. rename H0 into Hyx.
          exists x, x, y, xy, yx. repeat (split; try assumption).
          apply HG. left. apply HF'. exists x, y, xy.
          repeat (split; try assumption).
Qed.

(** We now state the first form of the Axiom of Choice. *)

Definition Axiom_of_Choice1 := forall R domR, Domain R domR -> Relation R ->
  exists F, Func F /\ Subset F R /\ Domain F domR.

Axiom Axiom_of_Choice : Axiom_of_Choice1.

(** This allows us to state and prove the second half of Theorem 3J. *)

Theorem Enderton3Jb : forall F A B, FuncFromInto F A B -> ~ Empty A ->
  (exists H, RightInverse F A B H) <-> FuncFromOnto F A B.
Proof.
  intros F A B HFAB HA. split; intros H.
  - split; try apply HFAB; split; try apply HFAB.
    intros b; split; intros I.
    + destruct H as [H H0]. unfold RightInverse in H0.
      apply H0 in HFAB as H1; try assumption. clear H0. rename H1 into H0.
      destruct H0 as [FoH [HFoH [HHBA HIA]]].
      destruct HHBA as [HH [HdomH [ranH [HranH HHBA]]]].
      assert (T : exists domH, Domain H domH /\ In b domH).
      { exists B. split; try assumption. }
      funval HH T H b. rename x into a. rename H0 into J.
      apply J in HH as J'. clear J. rename J' into J.
      apply J in T. clear J. rename T into J.
      destruct J as [ba [Hba J]]. ordpair a b.
      rename x into ab. rename H0 into Hab. exists a, ab.
      split; try assumption.
      assert (T : exists domF, Domain F domF /\ In a domF).
      { exists A. destruct HFAB as [_ [P _]]. split; try assumption.
        apply HHBA. apply HranH. exists b, ba. split; try assumption. }
      destruct HFAB as [HF [HFAB]].
      funval HF T F a. rename x into b'.
      apply H1 in HF as H1'. clear H1. apply H1' in T. clear H1'.
      destruct T as [ab' [Hab' K]].
      ordpair b b'. rename x into bb. rename H1 into Hbb.
      assert (L : In bb FoH).
      { apply HFoH. exists b, b', a, ba, ab'. repeat (split; try assumption). }
      apply HIA in L. destruct L as [b'' [L Hbb']].
      assert (M : b'' = b /\ b'' = b').
      { apply (Enderton3A b'' b'' b b' bb bb Hbb' Hbb). trivial. }
      destruct M as [M1 M2]. replace b'' with b in *. replace b' with b in *.
      replace ab with ab'. assumption.
      apply (OrdPair_Unique a b ab' ab Hab' Hab).
    + destruct HFAB as [HF [HdomF [ranF [HranF HFAB]]]].
      apply HFAB. apply HranF. assumption.
  - inverse F. rename x into F'. rename H0 into HF'.
    assert (P : Domain F' B).
    { destruct H as [HF [HdomF HranF]]. inverse F'.
      apply (Enderton3E F F' x A B HF' H HdomF HranF). }
    assert (Q : Relation F').
    { intros yx I. apply HF' in I. destruct I as [x [y [_ [I _]]]].
      exists y, x. assumption. }
    rename H into H0.
    destruct (Axiom_of_Choice F' B P Q) as [H [HH [Hsub HdomH]]].
    exists H. intros _ _. compose F H.
    rename x into FoH. rename H1 into HFoH. exists FoH.
    clear HFAB. rename H0 into HFAB.
    destruct HFAB as [HF [HdomF HranF]].
    split; try assumption. split.
    + split; try assumption. split; try assumption.
      range H. rename x into ranH. rename H0 into HranH. exists ranH.
      split; try assumption.
      intros x I. apply HranH in I. destruct I as [y [yx [Hyx I]]].
      apply HdomF. ordpair x y. rename x0 into xy. rename H0 into Hxy.
      exists y, xy. split; try assumption. apply Hsub in I.
      apply HF' in I. destruct I as [a [b [ab [Hba [Hab I]]]]].
      assert (T : b = y /\ a = x).
      { apply (Enderton3A b a y x yx yx Hba Hyx). trivial. }
      destruct T as [T1 T2].
      replace b with y in *. replace a with x in *. clear T1 T2 a b.
      replace xy with ab. assumption.
      apply (OrdPair_Unique x y ab xy Hab Hxy).
    + intros yy. split; intros I.
      * apply HFoH in I. destruct I as [y [y' [x [yx [xy [Hyy [Hyx [Hxy [I J]]]]]]]]].
        exists y. split.
        { apply HdomH. exists x, yx. split; try assumption. }
        { apply Hsub in I. apply HF' in I.
          destruct I as [a [b [ab [Hba [Hab I]]]]].
          assert (T : b = y /\ a = x).
          { apply (Enderton3A b a y x yx yx Hba Hyx). trivial. }
          destruct T as [T1 T2].
          replace b with y in *. replace a with x in *. clear T1 T2 a b.
          assert (T : y' = y).
          { destruct HF as [_ HF]. apply (HF x y' y xy ab Hxy Hab J I). }
          replace y' with y in Hyy. assumption. }
      * apply HFoH. destruct I as [y [I Hyy]].
        apply HdomH in I. destruct I as [x [yx [Hyx I]]].
        apply Hsub in I as J. apply HF' in J.
        destruct J as [a [b [ab [Hba [Hab J]]]]].
        assert (T : b = y /\ a = x).
        { apply (Enderton3A b a y x yx yx Hba Hyx). trivial. }
        destruct T as [T1 T2].
        replace b with y in *. replace a with x in *. clear T1 T2 a b.
        exists y, y, x, yx, ab. repeat (split; try assumption).
Qed.

(** Informal reasoning and intuition tell me that these should hold. However,
    the proofs seems rather non-trivial. Saving for later (TODO). *)

Theorem LeftInverse_Unique : forall F A B G G', FuncFromInto F A B ->
  ~ Empty A -> OneToOne F -> LeftInverse F A B G -> LeftInverse F A B G' -> G = G'.
Proof.
  intros F A B G G' HFAB HA H HG HG'.
  destruct (HG' HFAB HA) as [G'oF [HG'oF [HG'BA IA']]].
  destruct (HG HFAB HA) as [GoF [HGoF [HGBA IA]]].
  apply Extensionality_Axiom. intros yx. split; intros I.
  -
Abort.

Theorem RightInverse_Unique : forall F A B H H', RightInverse F A B H ->
  RightInverse F A B H' -> H = H'.
Abort.

Definition Elementwise_Image F A B : Prop :=
  forall x, In x B <-> exists X, In X A /\ Image X F x.

Theorem Elementwise_Image_Exists : forall F A, exists B, Elementwise_Image F A B.
Proof.
  intros F A. union F. rename x into UF. rename H into HUF.
  union UF. rename x into UUF. rename H into HUUF.
  powerset UUF. rename x into PUUF. rename H into HPUUF.
  build_set
    set
    (fun (t c x : set) => exists A', In A' t /\ Image A' F x)
    A
    PUUF.
  rename x into eiA. rename H into HeiA.
  exists eiA. intros X. split; intros H.
  - apply HeiA. assumption.
  - apply HeiA. split; try assumption.
    apply HPUUF. intros y Hy. apply HUUF.
    destruct H as [Y [HY H]]. apply H in Hy.
    destruct Hy as [x [xy [Hxy [I J]]]].
    pair x y. rename x0 into Pxy. rename H0 into HPxy.
    exists Pxy. split.
    + apply HPxy. right. trivial.
    + apply HUF. exists xy. split; try assumption. apply Hxy.
      right. assumption.
Qed.

Theorem Elementwise_Image_Unique : forall F A B C, Elementwise_Image F A B ->
  Elementwise_Image F A C -> B = C.
Proof.
  intros F A B C HB HC. apply Extensionality_Axiom. intros x. split; intros H.
  - apply HC, HB, H.
  - apply HB, HC, H.
Qed.

Theorem Enderton3Ka : forall F A B AuB F_AuB_ F_A_ F_B_ F_A_uF_B_,
 BinaryUnion A B AuB -> Image AuB F F_AuB_ -> Image A F F_A_ ->
 Image B F F_B_ -> BinaryUnion F_A_ F_B_ F_A_uF_B_ -> F_AuB_ = F_A_uF_B_.
Proof.
  intros F A B AuB F_AuB_ F_A_ F_B_ F_A_uF_B_ HAuB HF_AuB_ HF_A_ HF_B_ HF_A_uF_B_.
  apply Extensionality_Axiom. intros y. split; intros H.
  - apply HF_A_uF_B_. apply HF_AuB_ in H.
    destruct H as [x [xy [Hxy [H I]]]]. apply HAuB in H.
    destruct H as [H | H].
    + left. apply HF_A_. exists x, xy. repeat (split; try assumption).
    + right. apply HF_B_. exists x, xy. repeat (split; try assumption).
  - apply HF_AuB_. apply HF_A_uF_B_ in H. destruct H as [H | H].
    + apply HF_A_ in H. destruct H as [x [xy [Hxy [H I]]]].
      exists x, xy. repeat (split; try assumption).
      apply HAuB. left. assumption.
    + apply HF_B_ in H. destruct H as [x [xy [Hxy [H I]]]].
      exists x, xy. repeat (split; try assumption).
      apply HAuB. right. assumption.
Qed.

Theorem Enderton3Ka' : forall F A UA F_UA_ eiA UeiA,
  Union A UA -> Image UA F F_UA_ -> Elementwise_Image F A eiA ->
  Union eiA UeiA -> F_UA_ = UeiA.
Proof.
  intros F A UA F_UA_ eiA UeiA HUA HF_UA_ HeiA HUeiA.
  apply Extensionality_Axiom. intros y. split; intros H.
  - apply HUeiA. apply HF_UA_ in H. destruct H as [x [xy [Hxy [H I]]]].
    apply HUA in H. destruct H as [X [H HX]].
    image X F. rename x0 into F_X_. rename H0 into HF_X_.
    exists F_X_. split.
    + apply HF_X_. exists x, xy. repeat (split; try assumption).
    + apply HeiA. exists X. split; try assumption.
  - apply HF_UA_. apply HUeiA in H. destruct H as [F_X_ [H I]].
    apply HeiA in I. destruct I as [X [I HF_X_]].
    apply HF_X_ in H. destruct H as [x [xy [Hxy [H J]]]].
    exists x, xy. repeat (split; try assumption).
    apply HUA. exists X. split; assumption.
Qed.

Theorem Enderton3Kb : forall F A B AnB F_AnB_ F_A_ F_B_ F_A_nF_B_,
  BinaryIntersect A B AnB -> Image AnB F F_AnB_ -> Image A F F_A_ ->
  Image B F F_B_ -> BinaryIntersect F_A_ F_B_ F_A_nF_B_ -> Subset F_AnB_ F_A_nF_B_.
Proof.
  intros F A B AnB F_AnB_ F_A_ F_B_ F_A_nF_B_ HAnB HF_AnB_ HF_A_ HF_B_ HF_A_nF_B_.
  intros y H. apply HF_AnB_ in H. destruct H as [x [xy [Hxy [H I]]]].
  apply HAnB in H. destruct H as [H J].
  apply HF_A_nF_B_. split.
  - apply HF_A_. exists x, xy. repeat (split; try assumption).
  - apply HF_B_. exists x, xy. repeat (split; try assumption).
Qed.

Theorem Enderton3Kb' : forall F A NA F_NA_ eiA NeiA,
  ~ Empty A -> Intersect A NA -> Image NA F F_NA_ -> Elementwise_Image F A eiA ->
  Intersect eiA NeiA -> Subset F_NA_ NeiA.
Proof.
  intros F A NA F_NA_ eiA NeiA HA HNA HF_NA_ HeiA HNeiA.
  intros y H. apply HNeiA.
  - intros Con. apply Member_Exists_If_NonEmpty in HA.
    destruct HA as [X HA]. image X F. assert (P : In x eiA).
    { apply HeiA. exists X. split; try assumption. }
    apply Con in P. assumption.
  - intros Y HY. apply HF_NA_ in H. destruct H as [x [xy [Hxy [H I]]]].
    assert (P : forall X, In X A -> In x X).
    { apply HNA; assumption. }
    clear H. rename P into H. apply (HeiA) in HY.
    destruct HY as [X [HX HY]]. apply HY.
    exists x, xy. repeat (split; try assumption).
    apply H. assumption.
Qed.

(** Note that in the above theorems, equality holds if F is single-rooted.
    We encode this in the below corollaries. *)

Corollary Enderton3Kbeq : forall F A B AnB F_AnB_ F_A_ F_B_ F_A_nF_B_,
  BinaryIntersect A B AnB -> Image AnB F F_AnB_ -> Image A F F_A_ ->
  Image B F F_B_ -> BinaryIntersect F_A_ F_B_ F_A_nF_B_ ->
  SingleRooted F -> F_AnB_ = F_A_nF_B_.
Proof.
  intros F A B AnB F_AnB_ F_A_ F_B_ F_A_nF_B_ HAnB HF_AnB_ HF_A_ HF_B_ HF_A_nF_B_ P.
  apply Extensionality_Axiom. intros y. split; intros H.
  - apply (Enderton3Kb F A B AnB F_AnB_ F_A_ F_B_ F_A_nF_B_); assumption.
  - apply HF_AnB_. apply HF_A_nF_B_ in H. destruct H as [H I].
    apply HF_A_ in H. apply HF_B_ in I.
    destruct H as [x [xy [Hxy [Hx H]]]].
    destruct I as [x' [xy' [Hxy' [Hx' I]]]].
    exists x, xy. repeat (split; try assumption).
    apply HAnB. split; try assumption. replace x with x'; try assumption.
    apply (P x' x y xy' xy Hxy' Hxy I H).
Qed.

Corollary Enderton3Kbeq' : forall F A NA F_NA_ eiA NeiA,
  ~ Empty A -> Intersect A NA -> Image NA F F_NA_ ->
  Elementwise_Image F A eiA -> Intersect eiA NeiA -> SingleRooted F ->
  F_NA_ = NeiA.
Proof.
  intros F A NA F_NA_ eiA NeiA HA HNA HF_NA_ HeiA HNeiA HF.
  assert (P : ~ Empty eiA).
  { intros C. apply Member_Exists_If_NonEmpty in HA. destruct HA as [X HA].
    image X F. rename x into F_X_. rename H into HF_X_.
    assert (P : In F_X_ eiA).
    { apply HeiA. exists X. split; try assumption. }
    apply C in P. assumption. }
  apply Extensionality_Axiom. intros y. split; intros H.
  - apply HNeiA. apply P. intros F_X_ I. apply HeiA in I.
    destruct I as [X [I HF_X_]]. apply HF_NA_ in H.
    destruct H as [x [xy [Hxy [H J]]]]. apply HF_X_.
    exists x, xy. repeat (split; try assumption).
    assert (Q : forall X, In X A -> In x X).
    { apply HNA; assumption. }
    apply Q. assumption.
  - apply HF_NA_. assert (Q : forall F_X_, In F_X_ eiA -> In y F_X_).
    { apply HNeiA. apply P. apply H. }
    apply Member_Exists_If_NonEmpty in P. destruct P as [F_X_ P].
    apply HeiA in P as I. destruct I as [X [I HF_X_]].
    apply Q in P. apply HF_X_ in P. destruct P as [x [xy [Hxy [P R]]]].
    exists x, xy. repeat (split; try assumption). apply HNA. assumption.
    intros X' J. image X' F. rename x0 into F_X_'. rename H0 into HF_X_'.
    assert (S : In F_X_' eiA).
    { apply HeiA. exists X'. split; try assumption. }
    apply Q in S. apply HF_X_' in S. destruct S as [x' [xy' [Hxy' [S T]]]].
    replace x with x'. assumption.
    apply (HF x' x y xy' xy Hxy' Hxy T R).
Qed.

Theorem Enderton3Kc : forall F A B F_A_ F_B_ F_A_mF_B_ AmB F_AmB_,
  Image A F F_A_ -> Image B F F_B_ -> SetMinus F_A_ F_B_ F_A_mF_B_ ->
  SetMinus A B AmB -> Image AmB F F_AmB_ -> Subset F_A_mF_B_ F_AmB_.
Proof.
  intros F A B F_A_ F_B_ F_A_mF_B_ AmB F_AmB_ HF_A_ HF_B_ HF_A_mF_B_ HAmB HF_AmB_.
  intros y H. apply HF_AmB_. apply HF_A_mF_B_ in H.
  destruct H as [H I]. apply HF_A_ in H.
  destruct H as [x [xy [Hxy [H J]]]]. exists x, xy.
  repeat (split; try assumption).
  apply HAmB. split; try assumption. intros Con. apply I.
  apply HF_B_. exists x, xy. repeat (split; try assumption).
Qed.

(** Again equality holds if F is single-rooted. See the corollary below. *)

Corollary Enderton3Kceq : forall F A B F_A_ F_B_ F_A_mF_B_ AmB F_AmB_,
  Image A F F_A_ -> Image B F F_B_ -> SetMinus F_A_ F_B_ F_A_mF_B_ ->
  SetMinus A B AmB -> Image AmB F F_AmB_ -> SingleRooted F -> F_A_mF_B_ = F_AmB_.
Proof.
  intros F A B F_A_ F_B_ F_A_mF_B_ AmB F_AmB_ HF_A_ HF_B_ HF_A_mF_B_ HAmB HF_AmB_ HF.
  apply Extensionality_Axiom. intros y. split; intros H.
  - apply (Enderton3Kc F A B F_A_ F_B_ F_A_mF_B_ AmB F_AmB_); assumption.
  - apply HF_A_mF_B_. apply HF_AmB_ in H.
    destruct H as [x [xy [Hxy [H I]]]].
    apply HAmB in H. destruct H as [H1 H2]. split.
    + apply HF_A_. exists x, xy. repeat (split; try assumption).
    + intros Con. apply H2. apply HF_B_ in Con.
      destruct Con as [x' [xy' [Hxy' [Con1 Con2]]]].
      replace x with x'. assumption.
      apply (HF x' x y xy' xy Hxy' Hxy Con2 I).
Qed.

Lemma Inverse_SingleRooted : forall F', (exists F, Func F /\ Inverse F F') ->
  SingleRooted F'.
Proof.
  intros F' HF'. destruct HF' as [F HF'].
  intros x x' y xy xy' Hxy Hxy' H I.
  apply HF' in H. apply HF' in I.
  destruct H as [b [a [ba [Hab [Hba H]]]]].
  destruct I as [d [c [dc [Hcd [Hdc I]]]]].
  assert (P : a = x /\ b = y).
  { apply (Enderton3A a b x y xy xy Hab Hxy). trivial. }
  assert (Q : c = x' /\ d = y).
  { apply (Enderton3A c d x' y xy' xy' Hcd Hxy'). trivial. }
  destruct P as [P1 P2]. replace a with x in *. replace b with y in *.
  destruct Q as [Q1 Q2]. replace c with x' in *. replace d with y in *.
  destruct HF' as [[_ HF] _]. apply (HF y x x' ba dc Hba Hdc H I).
Qed.

Corollary Enderton3La : forall G A G' UA G'_UA_ eiA UeiA,
  Func G -> Inverse G G' -> Union A UA -> Image UA G' G'_UA_ ->
  Elementwise_Image G' A eiA -> Union eiA UeiA -> G'_UA_ = UeiA.
Proof.
  intros H A G' UA G'_UA_ eiA UeiA HG HG'.
  apply (Enderton3Ka' G' A UA G'_UA_ eiA UeiA).
Qed.

Corollary Enderton3Lb : forall G A G' NA G'_NA_ eiA NeiA,
  ~Empty A -> Func G -> Inverse G G' -> Intersect A NA -> Image NA G' G'_NA_ ->
  Elementwise_Image G' A eiA -> Intersect eiA NeiA -> G'_NA_ = NeiA.
Proof.
  intros G A G' NA G'_NA_ eiA NeiA HA HG HG' HNA HG'_NA_ HeiA HNeiA.
  apply (Enderton3Kbeq' G' A NA _ eiA); try assumption.
  apply Inverse_SingleRooted. exists G. split; try assumption.
Qed.

Corollary Enderton3Lc : forall G A B G' AmB G'_AmB_ G'_A_ G'_B_ G'_A_mG'_B_,
  Func G -> Inverse G G' -> SetMinus A B AmB -> Image AmB G' G'_AmB_ ->
  Image A G' G'_A_ -> Image B G' G'_B_ -> SetMinus G'_A_ G'_B_ G'_A_mG'_B_ ->
  G'_AmB_ = G'_A_mG'_B_.
Proof.
  intros G A B G' AmB G'_AmB_ G'_A_ G'_B_ G'_A_mG'_B_ HG HG' HAmB HG'_AmB HG'_A_.
  intros HG'_B_ HG'_A_mG'_B_. symmetry.
  apply (Enderton3Kceq G' A B G'_A_ G'_B_ G'_A_mG'_B_ AmB); try assumption.
  apply Inverse_SingleRooted. exists G. split; assumption.
Qed.

Definition IndexedUnion (I F UIF : set) : Prop :=
  Func F -> (exists domF, Domain F domF /\ Subset I domF) ->
  forall x, In x UIF <-> exists i Fi, In i I /\ FunVal F i Fi /\ In x Fi.

Theorem IndexedUnion_Exists : forall I F, Func F ->
  (exists domF, Domain F domF /\ Subset I domF) ->
  exists UIF, IndexedUnion I F UIF.
Proof.
  intros I F HF HdomF. destruct HdomF as [domF [HdomF HI]].
  range F. rename x into ranF. rename H into HranF.
  union ranF. rename x into UranF. rename H into HUranF.
  build_set
    (prod set set)
    (fun (t : set * set) (c x : set) =>
      exists i Fi, In i (fst t) /\ FunVal (snd t) i Fi /\ In x Fi)
    (I, F)
    UranF.
  rename x into UIF. rename H into HUIF. exists UIF.
  intros _ _ y. split; intros H.
  - apply HUIF. assumption.
  - apply HUIF. split; try assumption. apply HUranF.
    destruct H as [i [Fi [Hi [HFi H]]]]. exists Fi. split; try assumption.
    apply HranF. ordpair i Fi. rename x into xy. rename H0 into Hxy.
    exists i, xy. split; try assumption.
    apply HFi in HF. destruct HF as [xy' [Hxy' HF]].
    exists domF. split; try assumption. apply HI. assumption.
    replace xy with xy'. assumption.
    apply (OrdPair_Unique i Fi xy' xy Hxy' Hxy).
Qed.

Theorem IndexedUnion_Unique : forall I F UIF UIF', Func F ->
  (exists domF, Domain F domF /\ Subset I domF) ->
  IndexedUnion I F UIF -> IndexedUnion I F UIF' -> UIF = UIF'.
Proof.
  intros I F UIF UIF' HF [domF [HdomF HI]] H H'.
  apply Extensionality_Axiom. intros y. split; intros P.
  - apply H'; try assumption. exists domF. split; try assumption.
    apply H; try assumption. exists domF. split; assumption.
  - apply H. try assumption. exists domF. split; assumption.
    apply H'; try assumption. exists domF. split; assumption.
Qed.

Definition IndexedIntersect (I F NIF : set) : Prop :=
  ~ Empty I -> Func F -> (exists domF, Domain F domF /\ Subset I domF) ->
  forall x, In x NIF <-> forall i, In i I -> exists Fi, FunVal F i Fi /\ In x Fi.

Theorem IndexedIntersect_Exists : forall I F, ~ Empty I -> Func F ->
  (exists domF, Domain F domF /\ Subset I domF) ->
  exists NIF, IndexedIntersect I F NIF.
Proof.
  intros I F HI HF HdomF. image I F. rename x into F_I_. rename H into HF_I_.
  assert (P : ~Empty F_I_).
  { intros Con. apply Member_Exists_If_NonEmpty in HI.
    destruct HI as [i HI]. destruct HdomF as [domF [HdomF Hsub]].
    apply Hsub in HI as HI'. apply HdomF in HI'. destruct HI' as [Fi [xy [Hxy HI']]].
    assert (T : In Fi F_I_).
    { apply HF_I_. exists i, xy. repeat (split; try assumption). }
    apply Con in T. assumption. }
  intersect F_I_ P. rename x into NF_I_. rename H into HNF_I_.
  build_set
    (prod set set)
    (fun (t : set * set) (c x : set) =>
      forall i, In i (fst t) -> exists Fi, FunVal (snd t) i Fi /\ In x Fi)
    (I, F)
    NF_I_.
  rename x into NIF. rename H into HNIF. exists NIF.
  intros _ _ _ y. split; intros J.
  - apply HNIF. assumption.
  - apply HNIF. split; try assumption.
    apply HNF_I_. assumption. intros Fi HFi. apply HF_I_ in HFi.
    destruct HFi as [i [xy [Hxy [Hi HFi]]]]. apply J in Hi as Hi'.
    destruct Hi' as [Fi' [Hfi' Hi']]. apply Hfi' in HF as HF'.
    destruct HF' as [xy' [Hxy' HF']].
    { destruct HdomF as [domF [HdomF Hsub]]. exists domF.
      split; try assumption. apply Hsub. assumption. }
    replace Fi with Fi'. assumption.
    destruct HF as [_ HF]. apply (HF i Fi' Fi xy' xy Hxy' Hxy HF' HFi).
Qed.

Theorem IndexedIntersect_Unique : forall I F NIF NIF', Func F ->
  (exists domF, Domain F domF /\ Subset I domF) ->
  IndexedUnion I F NIF -> IndexedUnion I F NIF' -> NIF = NIF'.
Proof.
  intros I F NIF NIF' HF HdomF HNIF HNIF'.
  apply Extensionality_Axiom. intros x. split; intros H.
  - apply HNIF'; try assumption. apply HNIF; try assumption.
  - apply HNIF; try assumption. apply HNIF'; try assumption.
Qed.

Definition AllFunctions (A B BpreA : set) : Prop :=
  forall x, In x BpreA <-> FuncFromInto x A B.

Theorem AllFunctions_Exists : forall A B, exists BpreA, AllFunctions A B BpreA.
Proof.
  intros A B. prod A B. rename x into AxB. rename H into HAxB.
  powerset AxB. rename x into PAxB. rename H into HPAxB.
  build_set
    (prod set set)
    (fun (t : set * set) (c x : set) => FuncFromInto x (fst t) (snd t))
    (A, B)
    PAxB.
  rename x into BpreA. rename H into HBpreA.
  exists BpreA. intros F. split; intros H.
  - apply HBpreA. assumption.
  - apply HBpreA. split; try assumption.
    apply HPAxB. intros xy HFxy. apply HAxB.
    destruct H as [[HR HSV] [HdomF [ranF [HranF Hsub]]]].
    apply HR in HFxy as Hxy. destruct Hxy as [x [y Hxy]].
    exists x, y. repeat (split; try assumption).
    + apply HdomF. exists y, xy. split; try assumption.
    + apply Hsub. apply HranF. exists x, xy. split; assumption.
Qed.

Theorem AllFunctions_Unique : forall A B BpreA BpreA', AllFunctions A B BpreA ->
  AllFunctions A B BpreA' -> BpreA = BpreA'.
Proof.
  intros A B BpreA BpreA' HBpreA HBpreA'.
  apply Extensionality_Axiom. intros F. split; intros H.
  - apply HBpreA'. apply HBpreA. assumption.
  - apply HBpreA, HBpreA'. assumption.
Qed.

Theorem Exercise3_11 : forall F G A, Func F -> Func G -> Domain F A ->
  Domain G A -> (forall x Fx, In x A -> FunVal F x Fx <-> FunVal G x Fx) ->
  F = G.
Proof.
  intros F G A HF HG HdomF HdomG HFG.
  apply Extensionality_Axiom. intros xy. split; intros H.
  - destruct HF as [HRF HSVF]. apply HRF in H as Hxy.
    destruct Hxy as [x [y Hxy]]. assert (P : In x A).
    { apply HdomF. exists y, xy. split; try assumption. }
    apply (HFG x y) in P as Q. assert (S : FunVal F x y).
    { intros _ _. exists xy. split; assumption. }
    apply Q in S. assert (T : exists A, Domain G A /\ In x A).
    { exists A. split; assumption. }
    destruct (S HG T) as [xy' [Hxy' U]].
    replace xy with xy'. assumption.
    apply (OrdPair_Unique x y xy' xy Hxy' Hxy).
  - destruct HG as [HRG SVG]. apply HRG in H as Hxy.
    destruct Hxy as [x [y Hxy]]. assert (P : In x A).
    { apply HdomG. exists y, xy. split; assumption. }
    apply (HFG x y) in P as Q. assert (S : FunVal G x y).
    { intros _ _. exists xy. split; assumption. }
    apply Q in S. assert (T : exists A, Domain F A /\ In x A).
    { exists A. split; assumption. }
    destruct (S HF T) as [xy' [Hxy' U]].
    replace xy with xy'. assumption.
    apply (OrdPair_Unique x y xy' xy Hxy' Hxy).
Qed.

Theorem Exercise3_12 : forall f g domf domg, Func f -> Func g ->
  Domain f domf -> Domain g domg -> Subset f g <-> Subset domf domg /\
  forall x fx, In x domf -> FunVal f x fx <-> FunVal g x fx.
Proof.
  intros f g domf domg Hf Hg Hdomf Hdomg. split; intros H.
  - assert (T : Subset domf domg).
    { intros x I. apply Hdomg. apply Hdomf in I.
      destruct I as [y [xy [Hxy I]]]. exists y, xy.
      split; try assumption. apply H. assumption. }
    split; try assumption.
    intros x fx Hx. split; intros I.
    + intros _ _. assert (P : exists domf, Domain f domf /\ In x domf).
      { exists domf. split; try assumption. }
      destruct (I Hf P) as [xy [Hxy Q]].
      exists xy. split; try assumption. apply H. assumption.
    + intros _ _. apply Hdomf in Hx.
      destruct Hx as [y [xy [Hxy Hx]]].
      exists xy. split; try assumption.
      apply H in Hx. replace fx with y. assumption.
      assert (J : exists domg, Domain g domg /\ In x domg).
      { exists domg. split; try assumption. apply Hdomg.
        exists y, xy. split; try assumption. } 
      destruct (I Hg J) as [xy' [Hxy' K]]. destruct Hg as [_ Hg].
      apply (Hg x y fx xy xy' Hxy Hxy' Hx K).
  - intros xy J. destruct H as [H I].
    destruct Hf as [Hf Hf']. apply Hf in J as Hxy. destruct Hxy as [x [y Hxy]].
    assert (P : In x domf).
    { apply Hdomf. exists y, xy. split; try assumption. }
    apply (I x y) in P as Q. assert (R : FunVal f x y).
    { intros _ _. exists xy. split; assumption. }
    apply Q in R. apply R in Hg.
    assert (S : exists domg, Domain g domg /\ In x domg).
    { exists domg. split; try assumption. apply H. assumption. }
    apply Hg in S. destruct S as [xy' [Hxy' S]].
    replace xy with xy'; try assumption.
    apply (OrdPair_Unique x y xy' xy Hxy' Hxy).
Qed.

Theorem Exercise3_13 : forall f g domf domg, Func f -> Func g ->
  Domain f domf -> Domain g domg -> Subset f g -> Subset domg domf -> f = g.
Proof.
  intros f g domf domg Hf Hg Hdomf Hdomg Hsub Hsub'.
  apply Extensionality_Axiom. intros xy.
  split; intros H; try (apply Hsub; assumption).
  destruct Hg as [Hg Hg']. apply Hg in H as I.
  destruct I as [x [y Hxy]]. assert (P : In x domg).
  { apply Hdomg. exists y, xy. split; assumption. }
  apply Hsub' in P. apply Hdomf in P. destruct P as [y' [xy' [Hxy' P]]].
  apply Hsub in P as Q. replace xy with xy'. assumption.
  replace y' with y in Hxy'. apply (OrdPair_Unique x y xy' xy Hxy' Hxy).
  apply (Hg' x y y' xy xy'); assumption.
Qed. 

Theorem Exercise3_14a : forall f g fng, BinaryIntersect f g fng ->
  Func f -> Func g -> Func fng.
Proof.
  intros f g fng Hfng Hf Hg. split.
  - intros xy Hxy. apply Hfng in Hxy as [_ Hxy]. destruct Hg as [Hg _].
    apply Hg in Hxy. assumption.
  - intros x y z xy xz Hxy Hxz H I. apply Hfng in H as [_ H].
    apply Hfng in I as [_ I]. destruct Hg as [_ Hg].
    apply (Hg x y z xy xz Hxy Hxz H I).
Qed.

Theorem Exericse3_14b : forall f g fug domf domg domfndomg,
  BinaryUnion f g fug -> Domain f domf -> Domain g domg ->
  BinaryIntersect domf domg domfndomg ->
  Func f -> Func g ->
  Func fug <-> forall x fx, In x domfndomg -> FunVal f x fx <-> FunVal g x fx.
Proof.
  intros f g fug domf domg domfndomg Hfug Hdomf Hdomg Hdomfndomg Hf Hg.
  split; intros H.
  - intros x fx Hx. split; intros I.
    + intros _ _. apply Hdomfndomg in Hx as [Hx Hx'].
      assert (T : exists domF, Domain f domF /\ In x domF).
      { exists domf. split; assumption. }
      apply (I Hf) in T. apply Hdomg in Hx'.
      destruct Hx' as [y' [xy' [Hxy' Hx']]].
      destruct T as [xy [Hxy T]]. exists xy'. split; try assumption.
      replace xy' with xy. assumption.
      destruct H as [_ H]. apply (OrdPair_Unique x fx xy xy' Hxy).
      replace fx with y'. assumption.
      apply (H x y' fx xy' xy Hxy' Hxy).
      * apply Hfug. right. assumption.
      * apply Hfug. left. assumption.
    + intros _ _. apply Hdomfndomg in Hx as [J K].
      apply Hdomf in J. destruct J as [y [xy [Hxy J]]].
      exists xy. split; try assumption. replace fx with y. assumption.
      assert (P : In xy fug). { apply Hfug. left. assumption. }
      assert (Q : exists domg, Domain g domg /\ In x domg).
      { exists domg. split; assumption. }
      apply (I Hg) in Q. destruct Q as [xy' [Hxy' Q]].
      assert (R : In xy' fug). { apply Hfug. right. assumption. }
      destruct H as [_ H]. apply (H x y fx xy xy' Hxy Hxy' P R).
  - split.
    + intros xy Hxy. apply Hfug in Hxy. destruct Hxy as [I | I].
      * destruct Hf as [Hf _]. apply Hf in I. apply I.
      * destruct Hg as [Hg _]. apply Hg in I. apply I.
    + intros x y z xy xz Hxy Hxz I J. apply Hfug in I. apply Hfug in J.
      destruct I as [I | I]; destruct J as [J | J].
      * destruct Hf as [_ Hf]. apply (Hf x y z xy xz Hxy Hxz I J).
      * assert (P : FunVal f x y). { intros. exists xy. split; assumption. }
        assert (Q : In x domfndomg).
        { apply Hdomfndomg. split.
          - apply Hdomf. exists y, xy. split; assumption.
          - apply Hdomg. exists z, xz. split; assumption. }
        apply (H x y) in Q. apply Q in P.
        clear Q. assert (Q : FunVal g x z).
        { intros _ _. exists xz. split; assumption. }
        assert (T : exists domg, Domain g domg /\ In x domg).
        { exists domg. split; try assumption. apply Hdomg.
          exists z, xz. split; assumption. }
        apply (P Hg) in T as R. apply (Q Hg) in T.
        destruct T as [xz' [Hxz' T]]. destruct R as [xy' [Hxy' R]].
        destruct Hg as [_ Hg]. apply (Hg x y z xy' xz' Hxy' Hxz'); assumption.
      * assert (P : FunVal f x z). { intros. exists xz. split; assumption. }
        assert (Q : In x domfndomg).
        { apply Hdomfndomg. split.
          - apply Hdomf. exists z, xz. split; assumption.
          - apply Hdomg. exists y, xy. split; assumption. }
        apply (H x z) in Q. apply Q in P.
        clear Q. assert (Q : FunVal g x y).
        { intros _ _. exists xy. split; assumption. }
        assert (T : exists domg, Domain g domg /\ In x domg).
        { exists domg. split; try assumption. apply Hdomg.
          exists y, xy. split; assumption. }
        apply (P Hg) in T as R. apply (Q Hg) in T.
        destruct T as [xy' [Hxy' T]]. destruct R as [xz' [Hxz' R]].
        destruct Hg as [_ Hg]. apply (Hg x y z xy' xz' Hxy' Hxz'); assumption.
      * destruct Hg as [_ Hg]. apply (Hg x y z xy xz Hxy Hxz); assumption.
Qed.

Theorem Exercise3_15 : forall A UA, Union A UA ->
  (forall f, In f A -> Func f) ->
  (forall f g, In f A -> In g A -> Subset f g \/ Subset g f) -> Func UA.
Proof.
  intros A UA HUA HA Hsub. split.
  - intros xy Hxy. apply HUA in Hxy. destruct Hxy as [f [Hxy Hf]].
    apply HA in Hf. destruct Hf as [Hf _]. apply Hf in Hxy.
    assumption.
  - intros x y z xy xz Hxy Hxz H I.
    apply HUA in H. apply HUA in I.
    destruct H as [f [H Hf]]. destruct I as [g [I Hg]].
    destruct (Hsub f g Hf Hg) as [J | J].
    + apply J in H. destruct (HA g Hg) as [_ K].
      apply (K x y z xy xz); assumption.
    + apply J in I. destruct (HA f Hf) as [_ K].
      apply (K x y z xy xz); assumption.
Qed.

Theorem Exercise3_16 : ~ exists UF, forall f, Func f -> In f UF.
Proof.
  intros Con. destruct Con as [UF Con].
  union UF. union x. union x0. rename x1 into U.
  destruct (Enderton2A U) as [X HX]. apply HX. apply H1.
  singleton X. exists x1. split.
  - apply H2. trivial.
  - apply H0. ordpair X X. exists x2. split.
    + apply H3. left. assumption.
    + apply H. singleton x2. exists x3. split.
      * apply H4. trivial.
      * apply Con. split.
        { intros xy Hxy. exists X, X. apply H4 in Hxy. rewrite Hxy. assumption. }
        { intros a b c ab ac Hab Hac I J. apply H4 in I. apply H4 in J.
          rewrite I in Hab. rewrite J in Hac.
          assert (X = a /\ X = b).
          { apply (Enderton3A X X a b x2 x2); try assumption. trivial. }
          assert (X = a /\ X = c).
          { apply (Enderton3A X X a c x2 x2); try assumption. trivial. }
          destruct H5 as [_ H5]. destruct H6 as [_ H6].
          rewrite <- H5, <- H6. trivial. }
Qed.

Theorem Exercise3_17 : forall A B AoB, Composition A B AoB ->
  SingleRooted A -> SingleRooted B -> SingleRooted AoB.
Proof.
  intros A B AoB HAoB HA HB. intros w x y wy xy Hwy Hxy H I.
  apply HAoB in H. apply HAoB in I.
  destruct H as [w' [y' [u [wu [uy [Hwy' [Hwu [Huy [H1 H2]]]]]]]]].
  destruct I as [x' [y'' [v [xv [vy [Hxy' [Hxv [Hvy [I1 I2]]]]]]]]].
  assert (T : w' = w /\ y' = y).
  { apply (Enderton3A w' y' w y wy wy Hwy' Hwy). trivial. }
  destruct T as [T1 T2]. replace w' with w in *. replace y' with y in *.
  clear T1 T2 w' y'. assert (T : x' = x /\ y'' = y).
  { apply (Enderton3A x' y'' x y xy xy Hxy' Hxy). trivial. }
  destruct T as [T1 T2]. replace x' with x in *. replace y'' with y in *.
  clear T1 T2 x' y''. replace v with u in *.
  - apply (HB w x u wu xv); try assumption.
  - apply (HA u v y uy vy); assumption.
Qed.

Corollary Exercise3_17' : forall F G FoG, Composition F G FoG ->
  Func F -> Func G -> OneToOne F -> OneToOne G -> OneToOne FoG.
Proof.
  intros F G FoG HFoG HF HG HF' HG'. split.
  - destruct (DomComp_Exists F G); try assumption.
    apply (Enderton3H F G FoG x); assumption.
  - apply (Exercise3_17 F G FoG HFoG). apply HF'. apply HG'.
Qed.

(** Exercise 3-18 : Let R be the set
      
      {<0, 1>, <0, 2>, <0, 3>, <1, 2>, <1, 3>, <2, 3>}.
    
    Evaluate the following: RoR, R|{1}, R'|{1}, R[{1}], R'[{1}] *)

(** Exercise 3-19 : Let A = {<{}, {{}, {{}}}>, <{{}}, {}>}.

    Evaluate: A({}), A[{}], A[{{}}], A[{{}, {{}}}], A', AoA, A|{}, A|{{}},
    A|{{}, {{}}}, UUA. *)

Theorem Exercise3_20 : forall F A FlA ranF AxranF FnAxranF,
  Restriction F A FlA -> Range F ranF -> Prod A ranF AxranF ->
  BinaryIntersect F AxranF FnAxranF -> FlA = FnAxranF.
Proof.
  intros F A FlA ranF AxranF FnAxranF HFlA HranF HAxranF HFnAxranF.
  apply Extensionality_Axiom. intros xy. split; intros H.
  - apply HFnAxranF. apply HFlA in H.
    destruct H as [x [y [Hxy [H I]]]]. split; try assumption.
    apply HAxranF. exists x, y. repeat (split; try assumption).
    apply HranF. exists x, xy. split; try assumption.
  - apply HFlA. apply HFnAxranF in H. destruct H as [H I].
    apply HAxranF in I. destruct I as [x [y [Hx [Hy I]]]].
    exists x, y. repeat (split; try assumption).
Qed.

Theorem Exercise3_21 : forall R S T RoS SoT RoSoTl RoSoTr,
  Composition R S RoS -> Composition S T SoT -> Composition RoS T RoSoTl ->
  Composition R SoT RoSoTr -> RoSoTl = RoSoTr.
Proof.
  intros R S T RoS SoT RoSoTl RoSoTr HRoS HSoT Hl Hr.
  apply Extensionality_Axiom. intros wz. split; intros H.
  - apply Hr. apply Hl in H.
    destruct H as [w [z [x [wx [xz [Hwz [Hwx [Hxz [H I]]]]]]]]]. apply HRoS in I.
    destruct I as [x' [z' [y [xy [yz [Hxz' [Hxy [Hyz [I J]]]]]]]]].
    assert (P : x' = x /\ z' = z).
    { apply (Enderton3A x' z' x z xz xz Hxz' Hxz). trivial. }
    destruct P as [P1 P2]. replace x' with x in *. replace z' with z in *.
    clear x' z' P1 P2. ordpair w y. rename x0 into wy. rename H0 into Hwy.
    exists w, z, y, wy, yz. repeat (split; try assumption).
    apply HSoT. exists w, y, x, wx, xy. repeat (split; try assumption).
  - apply Hl. apply Hr in H.
    destruct H as [w [z [y [wy [yz [Hwz [Hwy [Hyz [H I]]]]]]]]]. apply HSoT in H.
    destruct H as [w' [y' [x [wx [xy [Hwy' [Hwx [Hxy [H J]]]]]]]]].
    assert (P : w' = w /\ y' = y).
    { apply (Enderton3A w' y' w y wy wy Hwy' Hwy). trivial. }
    destruct P as [P1 P2]. replace w' with w in *. replace y' with y in *.
    clear w' y' P1 P2. ordpair x z. rename x0 into xz. rename H0 into Hxz.
    exists w, z, x, wx, xz. repeat (split; try assumption).
    apply HRoS. exists x, z, y, xy, yz. repeat (split; try assumption).
Qed.

Theorem Exercise3_22a : forall F A B F_A_ F_B_,
  Image A F F_A_ -> Image B F F_B_ -> Subset A B -> Subset F_A_ F_B_.
Proof.
  intros F A B F_A_ F_B_ HF_A_ HF_B_ Hsub y H.
  apply HF_B_. apply HF_A_ in H. destruct H as [x [xy [Hxy [H I]]]].
  apply Hsub in H. exists x, xy. repeat (split; try assumption).
Qed.

Theorem Exercise3_22b : forall F G A FoG FoG_A_ G_A_ F_G_A__,
  Composition F G FoG -> Image A FoG FoG_A_ -> Image A G G_A_ ->
  Image G_A_ F F_G_A__ -> FoG_A_ = F_G_A__.
Proof.
  intros F G A FoG FoG_A_ G_A_ F_G_A__ HFoG HFoG_A_ HG_A_ HF_G_A__.
  apply Extensionality_Axiom. intros z. split; intros H.
  - apply HF_G_A__. apply HFoG_A_ in H.
    destruct H as [x [xz [Hxz [H I]]]]. apply HFoG in I.
    destruct I as [x' [z' [y [xy [yz [Hxz' [Hxy [Hyz [I J]]]]]]]]].
    assert (P : x' = x /\ z' = z).
    { apply (Enderton3A x' z' x z xz xz Hxz' Hxz). trivial. }
    destruct P as [P1 P2]. replace x' with x in *. replace z' with z in *.
    clear P1 P2 x' z'. exists y, yz. repeat (split; try assumption).
    apply HG_A_. exists x, xy. repeat (split; try assumption).
  - apply HF_G_A__ in H. destruct H as [y [yz [Hyz [H I]]]].
    apply HFoG_A_. apply HG_A_ in H. destruct H as [x [xy [Hxy [H J]]]].
    ordpair x z. rename x0 into xz. rename H0 into Hxz.
    exists x, xz. repeat (split; try assumption).
    apply HFoG. exists x, z, y, xy, yz. repeat (split; try assumption).
Qed.

Theorem Exercise3_22c : forall Q A B AuB QlAuB QlA QlB QlAuQlB,
  BinaryUnion A B AuB -> Restriction Q AuB QlAuB -> Restriction Q A QlA ->
  Restriction Q B QlB -> BinaryUnion QlA QlB QlAuQlB -> QlAuB = QlAuQlB.
Proof.
  intros Q A B AuB QlAuB QlA QlB QlAuQlB HAuB HQlAuB HQlA HQlB HQlAuQlB.
  apply Extensionality_Axiom. intros xy. split; intros H.
  - apply HQlAuQlB. apply HQlAuB in H.
    destruct H as [x [y [Hxy [H I]]]]. apply HAuB in I.
    destruct I as [I | I].
    + left. apply HQlA. exists x, y. repeat (split; try assumption).
    + right. apply HQlB. exists x, y. repeat (split; try assumption).
  - apply HQlAuB. apply HQlAuQlB in H. destruct H as [H | H].
    + apply HQlA in H. destruct H as [x [y [Hxy [H I]]]].
      exists x, y. repeat (split; try assumption).
      apply HAuB. left. assumption.
    + apply HQlB in H. destruct H as [x [y [Hxy [H I]]]].
      exists x, y. repeat (split; try assumption).
      apply HAuB. right. assumption.
Qed.

Theorem Exercise3_23a : forall A B IA BoIA BlA,
  Identity A IA -> Composition B IA BoIA -> Restriction B A BlA ->
  BoIA = BlA.
Proof.
  intros A B IA BoIA BlA HIA HBoIA HBlA.
  apply Extensionality_Axiom. intros xz. split; intros H.
  - apply HBoIA in H. destruct H as [x [z [y [xy [yz [Hxz [Hxy [Hyz [H I]]]]]]]]].
    apply HIA in H. destruct H as [x' [H Hxx]].
    apply HBlA. assert (P : x' = x /\ x' = y).
    { apply (Enderton3A x' x' x y xy xy Hxx Hxy). trivial. }
    destruct P as [P1 P2]. rewrite P1 in P2. rewrite P1 in H.
    rewrite P2 in H. exists x, z. repeat (split; try assumption).
    replace xz with yz. assumption. rewrite <- P2 in Hyz.
    apply (OrdPair_Unique x z yz xz Hyz Hxz).
    rewrite <- P2 in H. assumption.
  - apply HBoIA. apply HBlA in H. destruct H as [x [z [Hxz [H I]]]].
    ordpair x x. rename x0 into xx. rename H0 into Hxx.
    exists x, z, x, xx, xz. repeat (split; try assumption).
    apply HIA. exists x. split; assumption.
Qed.

Theorem Exercise3_23b : forall A C IA IA_C_ AnC,
  Identity A IA -> Image C IA IA_C_ -> BinaryIntersect A C AnC -> IA_C_ = AnC.
Proof.
  intros A C IA IA_C_ AnC HIA HIA_C_ HAnC.
  apply Extensionality_Axiom. intros x. split; intros H.
  - apply HAnC. apply HIA_C_ in H.
    destruct H as [x' [xx [Hxx [H I]]]].
    apply HIA in I. destruct I as [x'' [I Hxx']].
    assert (P : x'' = x' /\ x'' = x).
    { apply (Enderton3A x'' x'' x' x xx xx Hxx' Hxx). trivial. }
    replace  x' with x in *. replace x'' with x in *. split; assumption.
    symmetry. apply P. destruct P as [P1 P2]. rewrite <- P1. symmetry; assumption.
  - apply HIA_C_. apply HAnC in H. destruct H as [H I].
    ordpair x x. rename x0 into xx. rename H0 into Hxx.
    exists x, xx. repeat (split; try assumption).
    apply HIA. exists x. split; assumption.
Qed.

Theorem Exercise3_24 : forall F A F' domF F'_A_, Func F -> Inverse F F' ->
  Image A F' F'_A_ -> Domain F domF ->
  forall x, In x F'_A_ <-> In x domF /\ forall Fx, FunVal F x Fx -> In Fx A.
Proof.
  intros F A F' domF F'_A_ HF HF' HF'_A_ HdomF x. split; intros H.
  - apply HF'_A_ in H. destruct H as [y [yx [Hyx [H I]]]].
    apply HF' in I. destruct I as [x' [y' [xy [Hyx' [Hxy I]]]]].
    assert (P : y' = y /\ x' = x).
    { apply (Enderton3A y' x' y x yx yx Hyx' Hyx). trivial. }
    destruct P as [P1 P2]. replace y' with y in *. replace x' with x in *.
    split.
    + apply HdomF. exists y, xy. split; assumption.
    + intros Fx. intros HFx. replace Fx with y. assumption.
      assert (Q : exists domF, Domain F domF /\ In x domF).
      { exists domF. split; try assumption. apply HdomF.
        exists y, xy. split; assumption. }
      apply (HFx HF) in Q. destruct Q as [xy' [Hxy' Q]].
      destruct HF as [_ HF]. apply (HF x y Fx xy xy'); assumption.
  - apply HF'_A_. destruct H as [H I].
    apply HdomF in H. destruct H as [y [xy [Hxy H]]].
    ordpair y x. rename x0 into yx. rename H0 into Hyx.
    exists y, yx. repeat (split; try assumption).
    + apply I. intros _ _. exists xy. split; assumption.
    + apply HF'. exists x, y, xy. repeat (split; try assumption).
Qed.

Theorem Exercise3_25a : forall G G' GoG' ranG IranG,
  Inverse G G' -> Composition G G' GoG' -> Range G ranG -> Identity ranG IranG ->
  OneToOne G -> GoG' = IranG.
Proof.
  intros G G' GoG' ranG IranG HG' HGoG' HranG HIranG HG.
  apply Extensionality_Axiom. intros xx. split; intros H.
  - apply HIranG. apply HGoG' in H.
    destruct H as [x [x' [y [xy [yx [Hxx [Hxy [Hyx [H I]]]]]]]]].
    apply HG' in H. destruct H as [b' [a' [yx' [Hxy' [Hyx' H]]]]].
    assert (P : a' = x /\ b' = y).
    { apply (Enderton3A a' b' x y xy xy Hxy' Hxy). trivial. }
    destruct P as [P1 P2].
    replace a' with x in *. replace b' with y in *.
    exists x. split.
    + apply HranG. exists y, yx'. split; try assumption.
    + replace x' with x in Hxx. assumption.
      destruct HG as [[_ HG] _]. apply (HG y x x' yx' yx); assumption.
  - apply HGoG'. apply HIranG in H. destruct H as [x [H Hxx]].
    apply HranG in H. destruct H as [y [yx [Hyx H]]].
    ordpair x y. rename x0 into xy. rename H0 into Hxy.
    exists x, x, y, xy, yx. repeat (split; try assumption).
    apply HG'. exists y, x, yx. repeat (split; try assumption).
Qed.

Theorem Exercise3_25b : forall G G' GoG' ranG IranG, Inverse G G' ->
  Composition G G' GoG' -> Range G ranG -> Identity ranG IranG -> Func G ->
  GoG' = IranG.
Proof.
  intros G G' GoG' ranG IranG HG' HGoG' HranG HIranG HG.
  apply Extensionality_Axiom. intros xx. split; intros H.
  - apply HIranG. apply HGoG' in H.
    destruct H as [x [x' [y [xy [yx [Hxx [Hxy [Hyx [H I]]]]]]]]].
    apply HG' in H. destruct H as [b' [a' [yx' [Hxy' [Hyx' H]]]]].
    assert (P : a' = x /\ b' = y).
    { apply (Enderton3A a' b' x y xy xy Hxy' Hxy). trivial. }
    destruct P as [P1 P2].
    replace a' with x in *. replace b' with y in *.
    exists x. split.
    + apply HranG. exists y, yx'. split; try assumption.
    + replace x' with x in Hxx. assumption.
      destruct HG as [_ HG]. apply (HG y x x' yx' yx); assumption.
  - apply HGoG'. apply HIranG in H. destruct H as [x [H Hxx]].
    apply HranG in H. destruct H as [y [yx [Hyx H]]].
    ordpair x y. rename x0 into xy. rename H0 into Hxy.
    exists x, x, y, xy, yx. repeat (split; try assumption).
    apply HG'. exists y, x, yx. repeat (split; try assumption).
Qed.

(** Exercise 3-26 (prove parts of Theorem 3K) is omitted. *)

Theorem Exercise3_27 : forall F G FoG domFoG G' domF G'_domF_,
  Composition F G FoG -> Domain FoG domFoG -> Inverse G G' ->
  Domain F domF -> Image domF G' G'_domF_ -> domFoG = G'_domF_.
Proof.
  intros F G FoG domFoG G' domF G'_domF_ HFoG HdomFoG HG' HdomF HG'_domF_.
  apply Extensionality_Axiom. intros x. split; intros H.
  - apply HG'_domF_. apply HdomFoG in H.
    destruct H as [z [xz [Hxz H]]]. apply HFoG in H.
    destruct H as [x' [z' [y [xy [yz [Hxz' [Hxy [Hyz [H I]]]]]]]]].
    ordpair y x. rename x0 into yx. rename H0 into Hyx.
    assert (P : x' = x /\ z' = z).
    { apply (Enderton3A x' z' x z xz xz Hxz' Hxz). trivial. }
    exists y, yx. repeat (split; try assumption).
    + apply HdomF. exists z, yz. split; try assumption.
      replace z with z'. assumption. apply P.
    + apply HG'. exists x, y, xy. split; try assumption. split; try assumption.
      replace x with x'. assumption. apply P.
  - apply HdomFoG. apply HG'_domF_ in H.
    destruct H as [y [yx [Hyx [H I]]]].
    apply HdomF in H. destruct H as [z [yz [Hyz H]]].
    ordpair x z. rename x0 into xz. rename H0 into Hxz. exists z, xz.
    split; try assumption. apply HFoG. apply HG' in I.
    destruct I as [x' [y' [xy [Hyx' [Hxy I]]]]]. exists x, z, y, xy, yz.
    split; try assumption. split.
    + assert (P : y' = y /\ x' = x).
      { apply (Enderton3A y' x' y x yx yx Hyx' Hyx). trivial. }
      replace y with y'. replace x with x'. assumption. apply P. apply P.
    + repeat (split; try assumption).
Qed.

Definition GivenByImage (f A B G : set) : Prop := FuncFromInto f A B ->
  forall XY, In XY G <-> exists X Y, OrdPair X Y XY /\ Subset X A /\
  Subset Y B /\ Image X f Y.

Theorem GivenByImage_Exists : forall (f A B : set), FuncFromInto f A B ->
  exists G, GivenByImage f A B G.
Proof.
  intros f A B HfAB. powerset A. rename x into PA. rename H into HPA.
  powerset B. rename H into HPB. rename x into PB.
  prod PA PB. rename x into PAxPB. rename H into HPAxPB.
  build_set
    (prod (prod set set) set)
    (fun (t : set * set * set) (c x : set) => exists X Y, OrdPair X Y x /\
      Subset X (snd (fst t)) /\ Subset Y (snd t) /\ Image X (fst (fst t)) Y)
    ((f, A), B)
    PAxPB.
  rename x into G. rename H into HG.
  exists G. intros _ XY. split; intros H.
  - apply HG, H.
  - apply HG. split; try assumption.
    apply HPAxPB. destruct H as [X [Y [HXY [HXA [HYB _]]]]].
    exists X, Y. split; try split; try assumption.
    + apply HPA, HXA.
    + apply HPB, HYB.
Qed.

Theorem GivenByImage_Unique : forall f A B G G', FuncFromInto f A B ->
  GivenByImage f A B G -> GivenByImage f A B G' -> G = G'.
Proof.
  intros f A B G G' HfAB H H'.
  apply Extensionality_Axiom. intros x. split; intros I.
  - apply (H' HfAB), (H HfAB), I.
  - apply (H HfAB), (H' HfAB), I.
Qed.

Lemma GivenByImage_Into : forall f A B G PA PB, FuncFromInto f A B ->
  GivenByImage f A B G -> PowerSet A PA -> PowerSet B PB -> FuncFromInto G PA PB.
Proof.
  intros f A B G PA PB HfAB HG HPA HPB. split; try split.
  - intros XY H. apply (HG HfAB) in H. destruct H as [X [Y [HXY _]]].
    exists X, Y. assumption.
  - intros X Y Z XY XZ HXY HXZ H I.
    apply Extensionality_Axiom. intros y.
    apply (HG HfAB) in H. apply (HG HfAB) in I.
    destruct H as [X' [Y' [HXY' [HXA [HYB HY]]]]].
    assert (T : X' = X /\ Y' = Y).
    { apply (Enderton3A X' Y' X Y XY XY HXY' HXY). trivial. }
    destruct T as [T1 T2]. replace X' with X in *. replace Y' with Y in *.
    clear T1 T2 X' Y'.
    destruct I as [X' [Z' [HXZ' [_ [HZY HZ]]]]].
    assert (T : X' = X /\ Z' = Z).
    { apply (Enderton3A X' Z' X Z XZ XZ HXZ' HXZ). trivial. }
    destruct T as [T1 T2]. replace X' with X in *. replace Z' with Z in *.
    clear T1 T2 Z' X'. split; intros H.
    + apply HY in H. apply HZ. assumption.
    + apply HY. apply HZ. assumption.
  - intros X. split; intros H.
    + image X f. rename x into Y. rename H0 into HY.
      ordpair X Y. rename x into XY. rename H0 into HXY.
      exists Y, XY. split; try assumption. apply (HG HfAB).
      exists X, Y. split; try assumption. split; try (apply HPA; assumption).
      split; try assumption. intros y Hy. apply HY in Hy.
      destruct HfAB as [Hf [Hdomf [ranf [Hranf Hsub]]]].
      apply Hsub. apply Hranf. destruct Hy as [x [xy [Hxy [_ Hy]]]].
      exists x, xy. split; assumption.
    + destruct H as [Y [XY [HXY H]]]. apply (HG HfAB) in H.
      destruct H as [X' [Y' [HXY' [HXA [HYB H]]]]].
      assert (P : X' = X /\ Y' = Y).
      { apply (Enderton3A X' Y' X Y XY XY HXY' HXY). trivial. }
      apply HPA. replace X with X'; try assumption; apply P.
  - range G. rename x into ranG. rename H into HranG.
    exists ranG. split; try assumption.
    intros Y HY. apply HranG in HY. destruct HY as [X [XY [HXY H]]].
    apply (HG HfAB) in H. destruct H as [X' [Y' [HXY' [_ [HYB _]]]]].
    apply HPB. replace Y with Y'. assumption.
    apply (Enderton3A X' Y' X Y XY XY HXY' HXY). trivial.
Qed.

Theorem Exercise3_28 : forall f A B G PA PB, FuncFromInto f A B ->
  GivenByImage f A B G -> PowerSet A PA -> PowerSet B PB -> OneToOne f ->
  FuncFromInto G PA PB /\ OneToOne G.
Proof.
  intros f A B G PA PB HfAB HG HPA HPB Hf. split.
  - apply (GivenByImage_Into f A B G PA PB HfAB HG HPA HPB).
  - split; try apply (GivenByImage_Into f A B G PA PB HfAB HG HPA HPB).
    intros W X Y WY XY HWY HXY H I. apply (HG HfAB) in H. apply (HG HfAB) in I. apply Extensionality_Axiom. intros x.
    destruct Hf as [Hf HSRf]. destruct H as [W' [Y' [HWY' [HWA [HYB HF_W_]]]]].
    assert (T : W' = W /\ Y' = Y).
    { apply (Enderton3A W' Y' W Y WY WY HWY' HWY). trivial. }
    destruct T as [T1 T2]. replace W' with W in *. replace Y' with Y in *.
    clear T1 T2 W' Y'.
    destruct I as [X' [Y' [HXY' [HXA [_ HF_X_]]]]].
    assert (T : X' = X /\ Y' = Y).
    { apply (Enderton3A X' Y' X Y XY XY HXY' HXY). trivial. }
    destruct T as [T1 T2]. replace X' with X in *. replace Y' with Y in *.
    clear T1 T2 Y' X'. split; intros H.
    + assert (P : exists domf, Domain f domf /\ In x domf).
      { exists A. split. apply HfAB. apply HWA. assumption. }
      funval Hf P f x. rename x0 into fx. rename H0 into Hfx.
      apply (Hfx Hf) in P. destruct P as [xy [Hxy P]]. clear Hfx.
      assert (Q : In fx Y).
      { apply HF_W_. exists x, xy. repeat (split; try assumption). }
      apply HF_X_ in Q. destruct Q as [x' [xy' [Hxy' [Q1 Q2]]]].
      replace x with x'. assumption.
      apply (HSRf x' x fx xy' xy); assumption.
    + assert (P : exists domf, Domain f domf /\ In x domf).
      { exists A. split. apply HfAB. apply HXA. assumption. }
      funval Hf P f x. rename x0 into fx. rename H0 into Hfx.
      apply (Hfx Hf) in P. destruct P as [xy [Hxy P]]. clear Hfx.
      assert (Q : In fx Y).
      { apply HF_X_. exists x, xy. repeat (split; try assumption). }
      apply HF_W_ in Q. destruct Q as [x' [xy' [Hxy' [Q1 Q2]]]].
      replace x with x'. assumption. apply (HSRf x' x fx xy' xy); try assumption.
Qed.      

Definition GivenByInverse (f A B G : set) : Prop := FuncFromInto f A B ->
  forall yX, In yX G <-> exists y X, OrdPair y X yX /\ In y B /\
  forall x, In x X <-> In x A /\ FunVal f x y.

Theorem GivenByInverse_Exists : forall f A B,
  FuncFromInto f A B -> exists G, GivenByInverse f A B G.
Proof.
  intros f A B HfAB. powerset A. rename x into PA. rename H into HPA.
  prod B PA. rename x into BxPA. rename H into HBxPA.
  build_set
    set
    (fun (f c yX : set) => exists y X, OrdPair y X yX /\ In y B /\
      forall x, In x X <-> In x A /\ FunVal f x y)
    f
    BxPA.
  rename x into G. rename H into HG. exists G.
  intros _ yX. split; intros H.
  - apply HG. assumption.
  - apply HG. split; try assumption.
    destruct H as [y [X [HyX [Hy H]]]]. apply HBxPA. exists y, X.
    split; try assumption. split; try assumption.
    apply HPA. intros x Hx. apply H in Hx. apply Hx.
Qed.

Theorem GivenByInverse_Unique : forall f A B G H, FuncFromInto f A B ->
  GivenByInverse f A B G -> GivenByInverse f A B H -> G = H.
Proof.
  intros f A B G H HfAB HG HH. apply Extensionality_Axiom. intros x; split; intros I.
  - apply (HH HfAB). apply (HG HfAB). assumption.
  - apply (HG HfAB). apply (HH HfAB). assumption.
Qed.

Theorem GivenByInverse_Into : forall f A B G PA, PowerSet A PA ->
  FuncFromInto f A B -> GivenByInverse f A B G -> FuncFromInto G B PA.
Proof.
  intros f A B G PA HPA HfAB HG. split; try split.
  - intros yX H. apply (HG HfAB) in H. destruct H as [y [X [HyX _]]].
    exists y, X. assumption.
  - intros y W X yW yX HyW HyX H I. apply Extensionality_Axiom. intros x.
    split; intros J.
    + apply (HG HfAB) in H as [y' [W' [HyW' [H1 H2]]]].
      apply (HG HfAB) in I as [y'' [X' [HyX' [I1 I2]]]].
      assert (P : y' = y /\ W' = W).
      { apply (Enderton3A y' W' y W yW yW); try assumption. trivial. }
      assert (Q : y'' = y /\ X' = X).
      { apply (Enderton3A y'' X' y X yX yX); try assumption. trivial. }
      destruct P as [P1 P2]. destruct Q as [Q1 Q2].
      replace y'' with y in *. replace y' with y in *.
      replace X' with X in *. replace W' with W in *.
      apply I2. apply H2. assumption.
    + apply (HG HfAB) in H as [y' [W' [HyW' [H1 H2]]]].
      apply (HG HfAB) in I as [y'' [X' [HyX' [I1 I2]]]].
      assert (P : y' = y /\ W' = W).
      { apply (Enderton3A y' W' y W yW yW); try assumption. trivial. }
      assert (Q : y'' = y /\ X' = X).
      { apply (Enderton3A y'' X' y X yX yX); try assumption. trivial. }
      destruct P as [P1 P2]. destruct Q as [Q1 Q2].
      replace y'' with y in *. replace y' with y in *.
      replace X' with X in *. replace W' with W in *.
      apply H2, I2. assumption.
  - intros y. split; intros H.
    + range f. rename x into ranf. rename H0 into Hranf.
      assert (P : In y ranf \/ ~ In y ranf). { apply REM. }
      destruct P as [P | P].
      * build_set
          (prod set set)
          (fun t (c x : set) => FunVal (fst t) x (snd t))
          (f, y)
          A.
        rename x into X. rename H0 into HX.
        ordpair y X. rename x into yX. rename H0 into HyX. 
        exists X, yX. split; try assumption. apply (HG HfAB).
        exists y, X. repeat (split; try assumption).
      * empty. rename x into X. rename H0 into HX.
        ordpair y X. rename x into yX. rename H0 into HyX.
        exists X, yX. split; try assumption. apply (HG HfAB).
        exists y, X. split; try assumption. split; try assumption.
        intros x. split; intros Con.
        { apply HX in Con. destruct Con. }
        { assert (Q : In y ranf). apply Hranf.
          ordpair x y. exists x, x0. split; try assumption.
          destruct Con as [HA Con]. destruct HfAB as [Hf HfAB].
          assert (T : exists domf, Domain f domf /\ In x domf).
          { exists A. split; try assumption. apply HfAB. }
          apply (Con Hf) in T. destruct T as [xy [Hxy T]].
          replace x0 with xy. assumption.
          apply (OrdPair_Unique x y xy x0); assumption.
          apply P in Q. destruct Q. }
    + destruct H as [X [yX [HyX H]]]. apply (HG HfAB) in H.
      destruct H as [y' [X' [HyX' [H I]]]].
      replace y with y'. assumption.
      apply (Enderton3A y' X' y X yX yX HyX' HyX). trivial.
  - range G. rename x into ranG. rename H into HranG. exists ranG.
    split; try assumption. intros X HX. apply HPA.
    intros x Hx. apply HranG in HX. destruct HX as [y [yX [HyX HX]]].
    apply (HG HfAB) in HX. destruct HX as [y' [X' [HyX' [H I]]]].
    apply I. replace X' with X. assumption.
    apply (Enderton3A y X y' X' yX yX); try assumption. trivial.
Qed.

Theorem Exercise3_29 : forall f A B G, FuncFromInto f A B ->
  GivenByInverse f A B G -> FuncFromOnto f A B -> OneToOne G.
Proof.
  intros f A B G HfAB' HG HfAB.
  powerset A. rename x into PA. rename H into HPA. split.
  - apply (GivenByInverse_Into f A B G PA HPA HfAB' HG).
  - intros y z X yX zX HyX HzX H I. apply (HG HfAB') in H. apply (HG HfAB') in I.
    destruct H as [y' [X' [HyX' [H1 H2]]]]. destruct I as [z' [X'' [HzX' [I1 I2]]]].
    destruct HfAB as [Hf [Hdomf Hranf]].
    assert (P : y' = y /\ X' = X).
    { apply (Enderton3A y' X' y X yX yX HyX' HyX). trivial. }
    assert (Q : z' = z /\ X'' = X).
    { apply (Enderton3A z' X'' z X zX zX HzX' HzX). trivial. }
    destruct P as [P1 P2]. destruct Q as [Q1 Q2].
    replace X' with X in *. replace X'' with X in *.
    replace y' with y in *. replace z' with z in *.
    clear X' X'' y' z' P1 P2 Q1 Q2 HyX' HzX'.
    apply Hranf in I1. destruct I1 as [x [xz [Hxz I1]]].
    assert (P : In x X).
    { apply I2. split.
      - apply Hdomf. exists z, xz. split; assumption.
      - intros _ _. exists xz. split; assumption. }
    apply H2 in P. destruct P as [_ P].
    assert (Q : exists domf, Domain f domf /\ In x domf).
    { exists A. split; try assumption. apply Hdomf. exists z, xz. split; assumption. }
    apply (P Hf) in Q. destruct Q as [xy [Hxy Q]].
    destruct Hf as [HR HSV]. apply (HSV x y z xy xz); try assumption.
Qed.

Definition Monotonic (F A PA : set) : Prop := PowerSet A PA ->
  FuncFromInto F PA PA ->
  forall X Y, Subset X Y -> Subset Y A -> forall FX FY, FunVal F X FX ->
  FunVal F Y FY -> Subset FX FY.

Definition IspreB (F A PA preB : set) : Prop := PowerSet A PA ->
  FuncFromInto F PA PA ->
  forall X, In X preB <-> Subset X A /\ forall FX, FunVal F X FX -> Subset FX X.

Definition IspreC (F A PA preC : set) : Prop := PowerSet A PA ->
  FuncFromInto F PA PA ->
  forall X, In X preC <-> Subset X A /\ forall FX, FunVal F X FX -> Subset X FX.

Theorem preB_Exists : forall (F A PA : set), PowerSet A PA ->
  FuncFromInto F PA PA -> exists preB, IspreB F A PA preB.
Proof.
  intros F A PA HPA HF.
  build_set
    set
    (fun (t c x : set) => forall FX, FunVal t x FX -> Subset FX x)
    F
    PA.
  rename x into preB. rename H into HpreB. exists preB.
  intros _ _ X. split.
  - intros H. split.
    + apply HPA. apply HpreB. assumption.
    + apply HpreB. assumption.
  - intros [H I]. apply HpreB. split.
    + apply HPA. assumption.
    + assumption.
Qed.

Theorem preC_Exists : forall (F A PA : set), PowerSet A PA ->
  FuncFromInto F PA PA -> exists preC, IspreC F A PA preC.
Proof.
  intros F A PA HPA HF.
  build_set
    set
    (fun (t c x : set) => forall FX, FunVal t x FX -> Subset x FX)
    F
    PA.
  rename x into preC. rename H into HpreC. exists preC.
  intros _ _ X. split.
  - intros H. split.
    + apply HPA. apply HpreC. assumption.
    + apply HpreC. assumption.
  - intros [H I]. apply HpreC. split; try assumption.
    apply HPA. assumption.
Qed.

Theorem preB_Unique : forall F A PA preB preB', PowerSet A PA ->
  FuncFromInto F PA PA -> IspreB F A PA preB -> IspreB F A PA preB' -> preB = preB'.
Proof.
  intros F A PA preB preB' HPA HF H H'.
  apply Extensionality_Axiom. intros x. split; intros I.
  - apply (H' HPA HF), (H HPA HF), I.
  - apply (H HPA HF), (H' HPA HF), I.
Qed.

Theorem preC_Unique : forall F A PA preC preC', PowerSet A PA ->
  FuncFromInto F PA PA -> IspreC F A PA preC -> IspreC F A PA preC' -> preC = preC'.
Proof.
  intros F A PA preC preC' HPA HF H H'.
  apply Extensionality_Axiom. intros x. split; intros I.
  - apply (H' HPA HF), (H HPA HF), I.
  - apply (H HPA HF), (H' HPA HF), I.
Qed.

Lemma SubsetSymmetric_iff_Equal : forall A B, 
  (Subset A B /\ Subset B A) <-> A = B.
Proof.
  intros A B. split; intros H.
  - apply Extensionality_Axiom. intros x.
    split; intros I; apply H; assumption.
  -  rewrite H. split; apply Subset_Reflexive.
Qed.

Lemma preB_NonEmpty : forall F A PA preB, PowerSet A PA ->
  FuncFromInto F PA PA -> IspreB F A PA preB -> ~Empty preB.
Proof.
  intros F A PA preB HPA HF HpreB Con. apply (Con A), (HpreB HPA HF). split.
  - apply Subset_Reflexive.
  - intros FA HFA y Hy. assert (P : In FA PA).
    { destruct HF as [HF [HdomF [ranF [HranF Hsub]]]]. apply Hsub.
      apply HranF. exists A. apply HFA. apply HF.
      exists PA. split; try assumption. apply HPA. apply Subset_Reflexive. }
    apply HPA in P. apply P. assumption.
Qed.

Lemma Exercise3_30aB : forall F A PA preB B,  PowerSet A PA ->
  FuncFromInto F PA PA -> Monotonic F A PA -> IspreB F A PA preB ->
  Intersect preB B -> FunVal F B B.
Proof.
  intros F A PA preB B HPA HF Hmono HpreB HB.
  assert (Hne : ~ Empty preB). 
  { apply (preB_NonEmpty F A PA preB); assumption. }
  assert (HBsub : Subset B A).
  { intros b Hb. assert (T : forall y, In y preB -> In b y).
    { apply HB. apply Hne. apply Hb. }
    apply Member_Exists_If_NonEmpty in Hne. destruct Hne as [X HX].
    assert (U : In b X). { apply T. assumption. }
    apply (HpreB HPA HF) in HX. apply HX. assumption. }
  intros _ _. apply HPA in HBsub.
  assert (HdomF : Domain F PA). { apply HF. }
  apply HdomF in HBsub as P. destruct P as [FB [BFB [HBFB P]]].
  exists BFB. split; try assumption. replace FB with B in HBFB. assumption.
  symmetry. assert (Q : Subset FB B).
  { intros b Hb.
    assert (Q : forall FX,
      (exists X, Subset X A /\ FunVal F X FX /\ Subset FX X) -> In b FX).
    { intros FX [X [HXA [HFX HFXX]]]. assert (T : Subset FB FX).
      { apply (Hmono HPA HF B X); try assumption.
        - intros x Hx. assert (T : forall b', In b' preB -> In x b').
          { apply HB. apply Hne. assumption. }
          apply T. apply (HpreB HPA HF). split; try assumption.
          intros FX' HFX'. replace FX' with FX. assumption.
          apply (FunVal_Unique F X FX FX'); try assumption.
          apply HF. exists PA. split; try assumption.
          apply HPA. assumption.
        - intros _ _. exists BFB. split; assumption. }
      apply T. assumption. }
    apply (HB Hne). intros X HX. apply (HpreB HPA HF) in HX.
    destruct HX as [HXA HX]. apply HPA in HXA.
    assert (T : exists domF, Domain F domF /\ In X domF).
    { exists PA. split; try assumption. }
    destruct HF as [HF _]. funval HF T F X. rename x into FX. rename H into HFX.
    apply HX in HFX as Hsub. apply Hsub. apply Q. exists X.
    repeat (split; try assumption). apply HPA. assumption. }
  apply SubsetSymmetric_iff_Equal. split; try assumption.
  assert (R : In FB preB).
  { apply (HpreB HPA HF). apply HPA in HBsub. split.
    - intros x Hx. apply Q in Hx. apply HBsub. assumption.
    - intros FFB HFFB. apply (Hmono HPA HF FB B); try assumption. intros _ _.
      exists BFB. split; assumption. }
  intros x Hx.  assert (T : forall y, In y preB -> In x y).
  { apply (HB Hne). assumption. }
  apply T. assumption.
Qed.

Lemma Exercise3_30aC : forall F A PA preC C, PowerSet A PA ->
  FuncFromInto F PA PA -> Monotonic F A PA -> IspreC F A PA preC ->
  Union preC C -> FunVal F C C.
Proof.
  intros F A PA preC C HPA HF Hmono HpreC HC.
  assert (HCsub : Subset C A).
  { intros c Hc. apply HC in Hc as [X [Hc HX]].
    apply (HpreC HPA HF) in HX as [HXsub HX]. apply HXsub. assumption. }
  apply HPA in HCsub. assert (HdomF : Domain F PA). { apply HF. }
  apply HdomF in HCsub as HFC. destruct HFC as [FC [CFC [HCFC P]]].
  replace FC with C in HCFC. intros _ _. exists CFC. split; assumption.
  assert (Q : Subset C FC).
  { intros c H.
    assert (Q : exists FX X, Subset X A /\ FunVal F X FX /\ Subset X FX /\ In c FX).
    { apply HC in H. destruct H as [X [H I]].
      apply (HpreC HPA HF) in I as [HXA I]. apply HPA in HXA as J.
      apply HdomF in J as [FX [XFX [HXFX H']]]. exists FX, X.
      repeat (split; try assumption).
      - intros _ _. exists XFX. split; assumption.
      - apply I. intros _ _. exists XFX. split; assumption.
      - apply I. intros _ _. exists XFX. split; assumption. assumption. }
    destruct Q as [FX [X [HXA [HFX [Hsub Q]]]]].
    assert (T : Subset FX FC).
    { apply (Hmono HPA HF X C); try assumption.
      - intros x Hx. apply HC. exists X. split; try assumption.
        apply (HpreC HPA HF). split; try assumption. intros FX' HFX'.
        replace FX' with FX. assumption.
        apply (FunVal_Unique F X FX FX'); try assumption; try apply HF.
        exists PA. split; try assumption. apply HPA. assumption.
      - apply HPA. assumption.
      - intros _ _. exists CFC. split; assumption. }
    apply T. assumption. }
  apply SubsetSymmetric_iff_Equal. split; try assumption.
  intros c Hc. apply HC. exists FC. split; try assumption.
  apply (HpreC HPA HF). assert (T : Subset FC A).
  { destruct HF as [HF [_ [ranF [HranF Hsub]]]]. apply HPA. apply Hsub.
    apply HranF. exists C, CFC. split; assumption. }
  split; try assumption. intros FFC HFFC.
  apply (Hmono HPA HF C FC); try assumption. intros _ _. exists CFC.
  split; assumption.
Qed.

Theorem Exercise3_30a : forall F A PA preB preC B C, PowerSet A PA ->
  FuncFromInto F PA PA -> Monotonic F A PA -> IspreB F A PA preB ->
  IspreC F A PA preC -> Intersect preB B -> Union preC C ->
  FunVal F B B /\ FunVal F C C.
Proof.
  intros F A PA preB preC B C HPA HF Hmono HpreB HpreC HB HC. split.
  - apply (Exercise3_30aB F A PA preB B); assumption.
  - apply (Exercise3_30aC F A PA preC C); assumption.
Qed.

Theorem Exercise3_30b : forall F A PA preB preC B C X, PowerSet A PA ->
  FuncFromInto F PA PA -> Monotonic F A PA -> IspreB F A PA preB ->
  IspreC F A PA preC -> Intersect preB B -> Union preC C -> Subset X A ->
  FunVal F X X -> Subset B X /\ Subset X C.
Proof.
  intros F A PA preB preC B C X HPA HF Hmono HpreB HpreC HB HC HXA HFX. split.
  - assert (P : In X preB).
    { apply (HpreB HPA HF). split; try assumption.
      intros FX HFX'. replace FX with X. apply Subset_Reflexive.
      apply (FunVal_Unique F X); try assumption; try apply HF.
      exists PA. split; try (apply HPA; assumption); try apply HF. }
    assert (Hne : ~ Empty preB). { apply (preB_NonEmpty F A PA preB HPA HF HpreB). }
    intros b Hb. assert (Q : forall y, In y preB -> In b y).
    { apply (HB Hne). assumption. }
    apply Q. assumption.
  - assert (P : In X preC).
    { apply (HpreC HPA HF). split; try assumption. intros FX HFX'.
      replace FX with X. apply Subset_Reflexive.
      apply (FunVal_Unique F X); try assumption; try apply HF.
      exists PA. split; try apply HPA; try assumption; try apply HF. }
    intros c Hc. apply HC. exists X. split; assumption.
Qed.

(** Next we introduce an alternative definition for n-ary tuples which is
    isomorphic to our current definition in the finite case, but extends into
    the infinite case. We prove that it is well-defined, however, it is not
    clear that the definition is non-trivial. For this, we introduce a new
    formulation of the Axiom of Choice and prove it equivalent to the first.  *)

Definition IndexedProd (I H XIH : set) : Prop :=
  Func H -> (exists domH, Domain H domH /\ Subset I domH) ->
  forall f, In f XIH <-> Func f /\ Domain f I /\
  forall i, In i I -> forall fi Hi, FunVal f i fi -> FunVal H i Hi -> In fi Hi.

Theorem IndexedProd_Exists : forall I H, Func H ->
  (exists domH, Domain H domH /\ Subset I domH) -> exists XIH, IndexedProd I H XIH.
Proof.
  intros I H HH HI. destruct (IndexedUnion_Exists I H HH HI).
  rename x into UIH. rename H0 into HUIH. destruct (AllFunctions_Exists I UIH).
  rename x into UIHpreI. rename H0 into HUIHpreI.
  build_set
    (prod set set)
    (fun (t : set * set) (c x : set) => Func x /\ Domain x (fst t) /\
      forall i, In i (fst t) ->
      forall fi Hi, FunVal x i fi -> FunVal (snd t) i Hi -> In fi Hi)
    (I, H)
    UIHpreI.
  rename x into XIH. rename H0 into HXIH. exists XIH.
  intros _ _ f. split; intros P.
  - apply HXIH. assumption.
  - apply HXIH. split; try assumption. apply HUIHpreI.
    split; try apply P. split; try apply P.
    range f. rename x into ranf. rename H0 into Hranf. exists ranf.
    split; try assumption. intros fi Hfi. apply HUIH; try assumption.
    apply Hranf in Hfi. destruct Hfi as [i [ifi [Hifi Hfi]]].
    assert (Q : exists domH, Domain H domH /\ In i domH).
    { destruct HI as [domH [HdomH HI]]. exists domH.
      split; try assumption. apply HI. apply P. exists fi, ifi.
      split; try assumption. }
    funval HH Q H i. rename x into Hi. apply (H0 HH) in Q. clear H0.
    destruct Q as [iHi [HiHi Q]]. exists i, Hi. repeat split.
    + destruct HI as [domH [HdomH HI]].
      apply P. exists fi, ifi. split; assumption.
    + intros _ _. exists iHi. split; assumption.
    + destruct P as [_ [Hdomf P]]. apply (P i).
      * apply Hdomf. exists fi, ifi. split; assumption.
      * intros _ _. exists ifi. split; assumption.
      * intros _ _. exists iHi. split; assumption.
Qed.

Theorem IndexedProd_Unique : forall H I XIH XIH', Func H ->
  (exists domH, Domain H domH /\ Subset I domH) -> IndexedProd I H XIH ->
  IndexedProd I H XIH' -> XIH = XIH'.
Proof.
  intros H I XIH XIH' HH HI HXIH HXIH'.
  apply Extensionality_Axiom. intros f. split; intros P.
  - apply (HXIH' HH HI), (HXIH HH HI), P.
  - apply (HXIH HH HI), (HXIH' HH HI), P.
Qed.

Theorem IndexProd_Empty_if_EltEmpty : forall (H I XIH : set),
  Func H -> (exists domH, Domain H domH /\ Subset I domH) ->
  IndexedProd I H XIH -> (exists i Hi, In i I /\ FunVal H i Hi /\ Empty Hi) ->
  Empty XIH.
Proof.
  intros H I XIH HH HI HXIH He f Con. destruct He as [i [Hi [HHi [HHi' He]]]].
  apply (HXIH HH HI) in Con. destruct Con as [Hf [Hdomf P]].
  destruct HI as [domH [HdomH HI]].
  assert (Q : exists domf, Domain f domf /\ In i domf).
  { exists I. split; try assumption. }
  funval Hf Q f i. rename x into fi. rename H0 into Hfi. apply (Hfi Hf) in Q.
  destruct Q as [ifi [Hifi Q]]. apply (P i HHi fi Hi Hfi) in HHi'.
  apply He in HHi'. assumption.
Qed.

Definition Axiom_of_Choice2 := forall I H XIH, Func H -> Domain H I ->
  IndexedProd I H XIH -> (forall i Hi, In i I -> FunVal H i Hi -> ~ Empty Hi) ->
  ~ Empty XIH.

Theorem AC1_iff_AC2 : Axiom_of_Choice1 <-> Axiom_of_Choice2.
Admitted. (* TODO *)

(** Next, we treat the subject of equivalence relations and show the connection
    with partitions. We start with the basic definitions. Note that the
    reflexivity property must be define with respect to a set A. Otherwise, we
    would get a contradiction with UUR being the universal set. *)

Definition RelationOn (R A : set) : Prop :=
  forall xy, In xy R -> exists x y, OrdPair x y xy /\ In x A /\ In y A.
 
Definition Reflexive (R A : set) : Prop :=
  forall x xx, OrdPair x x xx -> In x A -> In xx R.

Definition Symmetric (R : set) : Prop :=
  forall x y xy yx, OrdPair x y yx -> OrdPair y x yx -> In xy R -> In yx R.

Definition Transitive (R : set) : Prop :=
  forall x y z xy yz xz, OrdPair x y xy -> OrdPair y z yz -> OrdPair x z xz ->
  In xy R -> In yz R -> In xz R.

Definition EquivalenceRelation (R A : set) : Prop :=
  RelationOn R A /\ Reflexive R A /\ Symmetric R /\ Transitive R.

Theorem Enderton3M : forall R fldR, Field R fldR -> Symmetric R ->
  Transitive R -> EquivalenceRelation R fldR.
Admitted.

(** The following definition of an equivalence class does not require R to be
    an equivalence relation. In fact, it is well-defined on any set R. However,
    they are only of interest in the case that R is an equivalence relation, and
    all of our interesting theorems regarding these sets take R to be an
    equivalence relation by assumption. *)

Definition EquivalenceClass (x R xmodR : set) : Prop :=
  forall t, In t xmodR <-> exists xt, OrdPair x t xt /\ In xt R.

Theorem EquivalenceClass_Exists : forall x R, exists xmodR,
  EquivalenceClass x R xmodR.
Admitted.

Theorem EquivalenceClass_Unique : forall x R xmodR xmodR',
  EquivalenceClass x R xmodR -> EquivalenceClass x R xmodR' -> xmodR = xmodR'.
Admitted.

Lemma Enderton3N : forall R A x y xmodR ymodR xy, EquivalenceRelation R A ->
  In x A -> In y A -> EquivalenceClass x R xmodR -> EquivalenceClass y R ymodR ->
  OrdPair x y xy -> xmodR = ymodR <-> In xy R.
Admitted.

(** Now we give the definition of a partition in anticipation of the main
    result of this section. *)

Definition Partition (A PI : set) : Prop :=
  (forall a, In a PI <-> Subset a A /\ ~ Empty a) /\
  forall a b, In a PI -> In b PI -> (exists x, In x a /\ In x b) -> a = b /\
  forall a, In a A -> exists b, In b PI /\ In a b.

Definition Quotient (A R AmodR : set) : Prop :=
  forall xmodR, In xmodR AmodR <-> exists x, In x A /\ EquivalenceClass x R xmodR.

Theorem Quotient_Exists : forall A R, exists AmodR, Quotient A R AmodR.
Admitted.

Theorem Quotient_Unique : forall A R AmodR AmodR', Quotient A R AmodR ->
  Quotient A R AmodR' -> AmodR = AmodR'.
Admitted.

Theorem Enderton3P : forall R A AmodR, EquivalenceRelation R A ->
  Quotient A R AmodR -> Partition A AmodR.
Admitted.

Definition NaturalQuotientMap (A R phi : set) : Prop :=
  forall xx, In xx phi <-> exists x xmodR, OrdPair x xmodR xx /\
  EquivalenceClass x R xmodR.

Theorem NaturalQuotientMap_Exists : forall A R, exists phi,
  NaturalQuotientMap A R phi.
Admitted.

Theorem NaturalQuotientMap_Unique : forall A R phi phi',
  NaturalQuotientMap A R phi -> NaturalQuotientMap A R phi' -> phi = phi'.
Admitted.

Definition Compatible (F R A : set) : Prop :=
  EquivalenceRelation R A -> FuncFromInto F A A ->
  forall x y xy Fx Fy FxFy, In x A -> In y A -> OrdPair x y xy ->
  FunVal F x Fx -> FunVal F y Fy -> OrdPair Fx Fy FxFy -> In xy R -> In FxFy R.

(** The full statement of the theorem is slightly different. For instance, the
    right-to-left direction is stated as a contrapositive. Also, the uniqueness
    of F' is asserted as part of the theorem. However, the book leaves the proof
    as an exericse, so I've chosen to delay the statement of uniqueness until
    then as well. There are also 'analogous results' for when F is not
    F : A -> A  but F : AxA -> A, which are discussed in an exercise. *)

Theorem Enderton3Q : forall R A F AmodR, EquivalenceRelation R A ->
  FuncFromInto F A A -> Compatible F R A <->
  (exists F', FuncFromInto F' AmodR AmodR /\ forall x xmodR Fx FxmodR F'xmodR,
  In x A -> EquivalenceClass x R xmodR -> FunVal F x Fx ->
  EquivalenceClass Fx R FxmodR -> FunVal F' xmodR F'xmodR -> F'xmodR = FxmodR).
Admitted.

Theorem Exercise3_32a : forall R R', Inverse R R' ->
  Symmetric R <-> Subset R' R.
Admitted.

Theorem Exercise3_32b : forall R RoR, Composition R R RoR ->
  Transitive R <-> Subset RoR R.
Admitted.

Theorem Exercise3_33 : forall R R' R'oR, Inverse R R' -> Composition R' R R'oR ->
  (Symmetric R /\ Transitive R /\ Relation R) <-> R = R'oR.
Admitted.

Theorem Exercise3_34a : forall A NA, ~ Empty A ->
  (forall R, In R A -> Transitive R /\ Relation R) -> Intersect A NA ->
  Transitive NA /\ Relation NA.
Admitted.

Theorem Exercise3_34b : exists A UA, ~ Empty A /\
  (forall R, In R A -> Transitive R /\ Relation R) /\ Union A UA /\
  Relation UA /\ ~ Transitive A.
Admitted.

Theorem Exercise3_35 : forall R x xmodR Sx R_Sx_,
  EquivalenceClass x R xmodR -> Singleton x Sx -> Image Sx R R_Sx_ ->
  xmodR = R_Sx_.
Admitted.

Definition GivenByRangeER (f A B R Q : set) : Prop :=
  FuncFromInto f A B -> EquivalenceRelation R B ->
  forall xy, In xy Q <-> exists x y fx fy fxfy,
  OrdPair x y xy /\ FunVal f x fx /\ FunVal f y fy /\ OrdPair fx fy fxfy /\
  In fxfy R.

Theorem GivenByRangeER_Exists : forall f A B R, FuncFromInto f A B ->
  EquivalenceRelation R B -> exists Q, GivenByRangeER f A B R Q.
Admitted.

Theorem GivenByRangeER_Unique : forall f A B R Q Q',
  FuncFromInto f A B -> EquivalenceRelation R B -> GivenByRangeER f A B R Q ->
  GivenByRangeER f A B R Q' -> Q = Q'.
Admitted.

Theorem Exercise3_36 : forall f A B R Q, FuncFromInto f A B ->
  EquivalenceRelation R B -> GivenByRangeER f A B R Q -> EquivalenceRelation Q A.
Admitted.

Definition GivenByPartition (PI Rpi: set) : Prop :=
  forall xy, In xy Rpi <-> exists x y B,
  OrdPair x y xy /\ In B PI /\ In x B /\ In y B.

Theorem GivenByPartition_Exists : forall PI, exists Rpi, GivenByPartition PI Rpi.
Admitted.

Theorem GivenByPartition_Unique : forall PI R R', GivenByPartition PI R ->
  GivenByPartition PI R' -> R = R'.
Admitted.

Theorem Exercise3_37 : forall A PI Rpi, Partition A PI ->
  GivenByPartition PI Rpi -> EquivalenceRelation Rpi A.
Admitted.

(** The following two theorems are the primary results of interest in this
    section. Intuitively, they say that our construction of a partition of A
    from a relation on A given earlier in the chapter and our construction of
    a relation on A from a partition of A given in Exercise 37 commute. *)

Theorem Exercise3_38 : forall A PI Rpi AmodRpi, Partition A PI ->
  GivenByPartition PI Rpi -> Quotient A Rpi AmodRpi -> PI = AmodRpi.
Admitted.

Theorem Exercise3_39 : forall A R AmodR Rpi, EquivalenceRelation R A ->
  Quotient A R AmodR -> GivenByPartition AmodR Rpi -> R = Rpi.
Admitted.

(** Exercises 40 and 41 treat sets that we have yet to define, so we can only
    treat them informally (TODO). *)

(** Exercise 42 : State precisely the 'analogous results' mentioned in
    Theorem 3Q. (This will require extending the concept of compatibility in a
    suitable way.) *)

(** Proving the stated theorem in this exercise is not part of the work
    prescribed by the the book. We leave is as TODO. *)

(** The next section of the book gives a brief treatment of (linear) orderings. *)

Definition Trichotomous (R A : set) : Prop :=
  forall x y xy yx, In x A -> In y A -> OrdPair x y xy -> OrdPair y x yx ->
  (In xy R /\ x <> y /\ ~ In yx R) \/
  (~ In xy R /\ x = y /\ ~ In yx R) \/
  (~ In xy R /\ x <> y /\ In yx R).

Definition LinearOrdering (R A : set) : Prop :=
  RelationOn R A /\ Transitive R /\ Trichotomous R A.

Definition Irreflexive (R : set) : Prop :=
  ~ exists x xx, OrdPair x x xx /\ In xx R.

Definition Connected (R A : set) : Prop :=
  forall x y, In x A -> In y A -> x <> y ->
  (exists xy, OrdPair x y xy /\ In xy R) \/
  (exists yx, OrdPair y x yx /\ In yx R).

Theorem Enderton3R : forall A R, LinearOrdering R A ->
  Irreflexive R /\ Connected R A.
Admitted.

Theorem Exercise3_43 : forall R A R', LinearOrdering R A -> Inverse R R' ->
  LinearOrdering R' A.
Admitted.

Theorem Exercise3_44 : forall R A f, LinearOrdering R A -> FuncFromInto f A A ->
  (forall x y xy fx fy fxfy, OrdPair x y xy -> In x A -> In y A -> FunVal f x fx ->
    FunVal f y fy -> OrdPair fx fy fxfy -> In xy R -> In fxfy R) ->
  OneToOne f /\ forall x y xy fx fy fxfy, OrdPair x y xy -> In x A -> In y A ->
  FunVal f x fx -> FunVal f y fy -> OrdPair fx fy fxfy -> In fxfy R -> In xy R.
Admitted.

Definition LexicographicOrdering (A B RA RB L : set) : Prop :=
  forall abcd, In abcd L <-> exists a b ab c d cd ac bd, In a A /\ In b B /\
  OrdPair a b ab /\ In c A /\ In d B /\ OrdPair c d cd /\ OrdPair ab cd abcd /\
  OrdPair a c ac /\ OrdPair b d bd /\
  (In ac RA \/ (a = c /\ In bd RB)).

Theorem LexicographicOrdering_Exists : forall A B RA RB, exists L,
  LexicographicOrdering A B RA RB L.
Admitted.

Theorem LexicographicOrdering_Unique : forall A B RA RB L L',
  LexicographicOrdering A B RA RB L -> LexicographicOrdering A B RA RB L' ->
  L = L'.
Admitted.

Theorem Exercise3_45 : forall A B RA RB L AxB, Prod A B AxB ->
  LinearOrdering RA A -> LinearOrdering RB B ->
  LexicographicOrdering A B RA RB L -> LinearOrdering L AxB.
Admitted.