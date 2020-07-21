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