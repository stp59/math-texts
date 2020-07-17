From Enderton Require Export Introduction.

(* Chapter 2: Axioms and Operations *)

(* The Axiom of Extensionality defines equality between sets. *)
Axiom Extensionality_Axiom : forall (A B : set), (forall (x : set),
  In x A <-> In x B) -> A = B.
  
(* In general, when a new definition is given in mathematics, we must show that 
  the defined object is well-defined. This means proving the existence and 
  uniqueness of the defined object. However, for certain sets, an axiom must be 
  introduced in order to show their existence. This is the case for the empty
  set below.*)

Definition Empty (A : set) : Prop := 
  forall (x : set), ~ (In x A).

Axiom Empty_Set_Axiom : exists (x : set), Empty x.

Theorem Empty_Unique : forall (A B : set), Empty A -> Empty B -> A = B.
Proof.
  intros A B HA HB.
  apply Extensionality_Axiom. intros x. split.
  - intros H. apply HA in H. inversion H.
  - intros H. apply HB in H. inversion H.
Qed.

(** A useful property of emptiness that is used in later proofs. TODO: currently
    makes use of an unproved axiom from (classical?) logic. *)

Lemma Member_Exists_If_NonEmpty : forall (A : set),
  ~Empty A -> exists (x : set), In x A.
Proof.
  intros A H. unfold Empty in H.
  apply (Not_Forall_Implies_Exists set (fun x => In x A)).
  apply H.
Qed.

Ltac empty := destruct (Empty_Set_Axiom).

(** Pair sets are another fundamental feature of set theory which requires an
    additional axiom. This will allow us to build elementary sets using ones 
    already shown to exist. *)

Definition Pair (u: set) (v : set) (B : set) : Prop :=
  forall (x : set), In x B <-> x = u \/ x = v.

Axiom Pairing_Axiom : forall (u v : set), exists (B : set), Pair u v B.

Theorem Pair_Unique : forall (u v A B : set),
  Pair u v A -> Pair u v B -> A = B.
Proof.
  intros u b A B HA HB. apply Extensionality_Axiom.
  intros x. split.
  - intros H. apply HA in H. destruct H.
    + apply HB. left. apply H.
    + apply HB. right. apply H.
  - intros H. apply HB in H. destruct H.
    + apply HA. left. apply H.
    + apply HA. right. apply H.
Qed.

Ltac pair a b := destruct (Pairing_Axiom a b).

(** Next, we define the notion of a subset, in preparation for the introduction
    of the power set axiom. *)

Definition Subset (A : set) (B : set) : Prop :=
  forall (x : set), In x A -> In x B.

(** We also prove a useful property of subsets. *)

Lemma Subset_Reflexive : forall (A : set), Subset A A.
Proof.
  intros A x H. apply H.
Qed.

(** Now we are ready to introduce power sets, using a new axiom to show their
    existence. Like pair sets, this will allow us to construct many new sets
    from existing ones, only in a much more powerful way. *)

Definition PowerSet (A : set) (B : set) : Prop :=
  forall (x : set), In x B <-> Subset x A.

Axiom Power_Set_Axiom : forall (a : set), exists (B : set), PowerSet a B.

Theorem Power_Set_Unique : forall (a A B : set),
  PowerSet a A -> PowerSet a B -> A = B.
Proof.
  intros a A B HA HB. apply Extensionality_Axiom. intros x. split.
  - intros H. apply HA in H. apply HB in H. apply H.
  - intros H. apply HB in H. apply HA in H. apply H.
Qed.

Ltac powerset A := destruct (Power_Set_Axiom A).

(** The existence of singleton sets is a useful consequence of the pairing axiom. *)

Definition Singleton (a : set) (A : set) : Prop := 
  forall (x : set), In x A <-> x = a.

Lemma Singleton_Equals_Pair : forall (x A : set),
  Singleton x A <-> Pair x x A.
Proof.
  intros x A. split.
  - intros H. intros y. split.
    + intros H'. apply H in H'. right. apply H'.
    + intros H'. destruct H'; apply H in H0; apply H0.
  - intros H. intros y. split.
    + intros H'. apply H in H'. destruct H'; apply H0.
    + intros H'. apply H. right. apply H'.
Qed.

Theorem Singleton_Exists : forall (a : set), exists (A : set), 
  Singleton a A.
Proof.
  intros a. destruct (Pairing_Axiom a a).
  apply Singleton_Equals_Pair in H.
  exists x. apply H. 
Qed.

Theorem Singleton_Unique : forall (a A B : set),
  Singleton a A -> Singleton a B -> A = B.
Proof.
  intros a A B HA HB. apply Singleton_Equals_Pair in HA.
  apply Singleton_Equals_Pair in HB. apply (Pair_Unique a a).
  apply HA. apply HB.
Qed.

Ltac singleton a := destruct (Singleton_Exists a).

(** Now for the most interesting axiom up to this point. Underneath all of the
    intricate logical language, the intuition behind the family of subset axioms
    is that, given a set we know to exist, subsets exist whose members satisfy
    all kinds of different properties. This captures an important notion from
    naive set theory without introducing any paradoxes or contradictions into
    the system. *)

Axiom Subset_Axiom : forall (T : Type), forall (Phi : T -> set -> set -> Prop),
  forall (t : T), forall (c : set), exists (B : set), forall (x : set),
  In x B <-> In x c /\ Phi t c x.

Ltac build_set T Phi t c := destruct (Subset_Axiom T Phi t c).

(** The theorem that follows is meant to show that Russel's Paradox has been
    successfully avoided in the current axiomatic approach. *)

Theorem Enderton2A : forall (A : set), exists (B : set), ~In B A.
Proof.
  intros A. destruct (Subset_Axiom set (fun t c x => ~In x x) A A) as [B].
  exists B. intros C. assert (P : In B B <-> In B A /\ ~In B B).
  { apply H. }
  assert (Q : In B B <-> ~In B B).
  { split.
    - intros J. apply P in J. apply J.
    - intros J. apply P. split. apply C. apply J. }
  apply Q. apply Q. intros D. apply Q in D as R. apply R in D. apply D.
  apply Q. intros D. apply Q in D as R. apply R in D. apply D.
Qed.

(** Set unions are another important feature of set theory which require the
    addition of a new axiom. Note that this is a unary operator on set, and that
    the familiar binary union is actually a special case of this definition. *)

Definition Union (A B : set) : Prop := 
  forall (x : set), In x B <-> exists (a : set), In x a /\ In a A.

Axiom Union_Axiom : forall (A : set), exists (B : set), Union A B.

Theorem Union_Unique : forall (A B C : set), Union A B -> Union A C -> B = C.
Proof.
  intros A B C HB HC. apply Extensionality_Axiom. intros x. split.
  - intros H. apply HC. apply HB. apply H.
  - intros H. apply HB. apply HC. apply H.
Qed.

Ltac union A := destruct (Union_Axiom A).

(** That binary unions are well-defined follows from the pairing axiom and the
    union axiom. We take the pair of two sets via the pairing axiom, then
    the unary union of the pair to get the binary union. We start with a
    lemma to show this equality, then use it to show that binary unions are
    well-defined. *)

Definition BinaryUnion (a b C : set) : Prop :=
  forall (x : set), In x C <-> In x a \/ In x b.

Lemma BinaryUnion_Equals_Union : forall (a b A B : set),
  Pair a b A -> BinaryUnion a b B <-> Union A B.
Proof.
  intros a b A B H. split.
  - intros HB. intros x. split.
    + intros HC. apply (HB x) in HC. destruct HC.
      * exists a. split. apply H0. apply H. left. reflexivity.
      * exists b. split. apply H0. apply H. right. reflexivity.
    + intros [X [HxX HXA]]. apply H in HXA. destruct HXA.
      * apply HB. left. rewrite <- H0. apply HxX.
      * apply HB. right. rewrite <- H0. apply HxX.
  - intros HB. intros x. split.
    + intros HC. apply HB in HC. destruct HC. destruct H0.
      apply H in H1. destruct H1.
      * left. rewrite <- H1. apply H0.
      * right. rewrite <- H1. apply H0.
    + intros [Ha | Hb].
      * apply HB. exists a. split. apply Ha. apply H. left. reflexivity.
      * apply HB. exists b. split. apply Hb. apply H. right. reflexivity.
Qed.

Theorem BinaryUnion_Exists : forall (a b : set), exists (C : set),
  BinaryUnion a b C.
Proof.
  intros a b.
  destruct (Pairing_Axiom a b).
  destruct (Union_Axiom x).
  exists x0.
  apply (BinaryUnion_Equals_Union a b x x0).
  apply H. apply H0.
Qed.

Theorem BinaryUnion_Unique : forall (a b C D: set),
  BinaryUnion a b C -> BinaryUnion a b D -> C = D.
Proof.
  intros a b C D HC HD. destruct (Pairing_Axiom a b).
  apply (Union_Unique x C D).
  apply (BinaryUnion_Equals_Union a b x C). apply H. apply HC.
  apply (BinaryUnion_Equals_Union a b x D). apply H. apply HD.
Qed.

Ltac binary_union A B := destruct (BinaryUnion_Exists A B).

(** Set intersections are more difficult to treat, due to the fact that the
    unary intersect of the empty set does not exist. Thus all definitions
    must assert that a given set is not empty. *)

Definition PreIntersect (A B : set) : Prop :=
  forall (x : set), In x B <-> forall (y : set), In y A -> In x y.

Definition Intersect (A B : set) : Prop := ~ Empty A ->
  PreIntersect A B.

(** The existence of the unary intersect of a non-empty set is a non-trivial
    consequence of the axioms we already have. We use a subset axiom on the
    unary union to produce the unary intersect. *)

Theorem Enderton2B : forall (A : set),
  ~Empty A -> exists (B : set), Intersect A B.
Proof.
  intros A H. destruct (Member_Exists_If_NonEmpty A). apply H.
  destruct (Subset_Axiom set (fun t c x => forall (y : set), In y t -> In x y) A x).
  exists x0. split.
  - intros I y J. apply H1 in I. apply I. apply J.
  - intros I. apply H1. split.
    + apply I. apply H0.
    + intros y J. apply I. apply J.
Qed.

Theorem Intersect_Unique : forall (A B C : set),
  ~ Empty A -> Intersect A B -> Intersect A C -> B = C.
Proof.
  intros A B C He HB HC. apply Extensionality_Axiom. intros x. split.
  - intros H. apply HC. assumption. apply HB. assumption. apply H.
  - intros H. apply HB, HC, H; assumption.
Qed.

Ltac intersect H A := destruct (Enderton2B H A).

(** This theorem shows why the unary intersect of the empty set is not a set. *)

Theorem Intersect_Empty : forall (A : set),
  Empty A -> ~exists (B : set), PreIntersect A B.
Proof.
  intros A E. intros C. destruct C as [C].
  assert (J : exists (B : set), forall (x : set), In x B).
  - exists C. intros x. apply H. intros y Hy. apply E in Hy. inversion Hy.
  - destruct J as [B HB]. destruct (Enderton2A B) as [x Hx]. apply Hx in HB.
    assumption. 
Qed.

(** Similar to binary union, binary intersect is a special case of unary 
    intersect. Binary intersects are much convenient than unary intersects
    due to the fact that they need not check that the operand sets are
    empty; the pair will always have at least one member. Like binary union,
    we start with a lemma which is used to prove well-definedness. *)

Definition BinaryIntersect (a b C : set) : Prop :=
  forall (x : set), In x C <-> In x a /\ In x b.

Lemma BinaryIntersect_Equals_Intersect : forall (a b A B : set),
  Pair a b A -> BinaryIntersect a b B <-> Intersect A B.
Proof.
  intros a b A B P. split.
  - intros H x. split.
    + intros I y J. apply H in I. destruct I as [Ia Ib]. apply P in J.
      destruct J as [J | J].
      * rewrite J. apply Ia.
      * rewrite J. apply Ib.
    + intros I. apply H. split.
      * apply I. apply P. left. reflexivity.
      * apply I. apply P. right. reflexivity.
  - intros H x. assert (Q : ~Empty A).
    { intros C. apply (C a). apply P. left. trivial. } split.
    + intros I. split.
      * apply H. assumption. apply I. apply P. left. trivial.
      * apply H. assumption. apply I. apply P. right. trivial.
    + intros [Ia Ib]. apply H. assumption. intros y. intros J. apply P in J.
      destruct J as [J | J].
      * rewrite J. apply Ia.
      * rewrite J. apply Ib.
Qed.

Theorem BinaryIntersect_Exists : forall (a b : set), exists (A : set),
  BinaryIntersect a b A.
Proof.
  intros a b.
  destruct (Pairing_Axiom a b).
  destruct (Enderton2B x).
  { intros C. unfold Empty in C. apply (C a). apply H. left. trivial. }
  exists x0. apply (BinaryIntersect_Equals_Intersect a b x x0).
  apply H. apply H0.
Qed.

Theorem BinaryIntersect_Unique : forall (a b A B: set),
  BinaryIntersect a b A -> BinaryIntersect a b B -> A = B.
Proof.
  intros a b A B Ha Hb.
  destruct (Pairing_Axiom a b) as [x].
  apply (Intersect_Unique x A B).
  intros C. apply (C a). apply H. left. trivial.
  apply (BinaryIntersect_Equals_Intersect a b x A).
  apply H. apply Ha.
  apply (BinaryIntersect_Equals_Intersect a b x B).
  apply H. apply Hb.
Qed.

Ltac binary_intersect A B := destruct (BinaryIntersect_Exists A B).

(** This is a useful lemma for proving some of the exercises below. *)

Lemma Pair_Extensionality : forall (a b c d A : set),
  Pair a b A -> Pair c d A -> (a = c /\ b = d) \/ (a = d /\ b = c).
Proof.
  intros a b c d A Hab Hcd. unfold Pair in Hab, Hcd.
  assert (J : c = a \/ c = b). apply Hab. apply Hcd. left. trivial.
  assert (K : d = a \/ d = b). apply Hab. apply Hcd. right. trivial.
  destruct J as [ J | J ]; destruct K as [K | K].
  - left. rewrite J. split. trivial. rewrite K.
    assert (L : b = c \/ b = d). apply Hcd. apply Hab. right. trivial.
    destruct L. rewrite H. rewrite J. trivial.
    rewrite H. rewrite K. trivial.
  - left. rewrite J. split. trivial. rewrite K. trivial.
  - right. split. rewrite K. trivial. rewrite J. trivial.
  - right. split. assert (L : a = c \/ a = d). apply Hcd. apply Hab.
    left. trivial. destruct L. rewrite K. rewrite <- J. apply H.
    apply H. rewrite J. trivial.
Qed.

(** Exercise 2_1: Assume that A is the set of integers divisible by 4. Similarly
    assume that B and C are the sets of integers divisible by 9 and 10,
    respectively. What is A intersect B intersect C? *)

(** It is the set of integers divisible by 4, 9, and 10, that is, by 180. *)

Theorem Exercise2_2 : exists (A B C : set), Union A C /\ Union B C /\ A <> B.
Proof.
  empty. singleton x. singleton x0.
  pair x x1. pair x0 x1. pair x2 x1. pair x3 x0.
  union x4. exists x4. exists x5. exists x6. split. apply H6. split.
  - intros y. split.
    + intros I. apply H6 in I. destruct I as [z [Ia Ib]].
      apply H4 in Ib. destruct Ib as [ Ib | Ib].
      * rewrite Ib in Ia. apply H2 in Ia. destruct Ia as [ Ia | Ia ].
        rewrite Ia. exists x0. split. apply H0. reflexivity.
        apply H5. right. trivial.
        rewrite Ia. exists x3. split. apply H3. right. trivial.
        apply H5. left. trivial.
      * rewrite Ib in Ia. apply H1 in Ia. rewrite Ia. exists x3.
        split. apply H3. left. trivial. apply H5. left. trivial.
    + intros [a0 [J K]]. apply H5 in K. destruct K.
      * rewrite H7 in J. apply H3 in J. destruct J. rewrite H8. apply H6.
        exists x1. split. apply H1. trivial. apply H4. right. trivial.
        rewrite H8. apply H6. exists x2. split. apply H2. right. trivial.
        apply H4. left. trivial.
      * rewrite H7 in J. apply H0 in J. rewrite J. apply H6. exists x2. split.
        apply H2. left. trivial. apply H4. left. trivial.
  - intros Contra. rewrite <- Contra in H5.
    assert (J : (x3 = x2 /\ x0 = x1) \/ (x3 = x1 /\ x0 = x2)).
    { apply (Pair_Extensionality _ _ _ _ x4). apply H5. apply H4. }
    destruct J as [ [Ja Jb] | [Ja Jb] ].
    + rewrite Ja in H3.
      assert (K : (x = x0 /\ x1 = x1) \/ (x = x1 /\ x1 = x0)).
      { apply (Pair_Extensionality x x1 x0 x1 x2). apply H2. apply H3. }
      destruct K. destruct H7. rewrite H7 in H. unfold Empty in H.
      apply (H x). apply H0. trivial.
      destruct H7. rewrite H7 in H. apply (H x0). apply H1. trivial.
    + rewrite Jb in H0. assert (K : x1 = x). apply (H0 x1). apply H2.
     right. trivial. rewrite <- K in H. unfold Empty in H. apply (H x0).
     apply H1. trivial.
Qed.

Theorem Exercise2_3 : forall (A B: set), Union A B -> 
  forall (x : set), In x A -> Subset x B.
Proof.
  intros A B H x I. intros y Hy. apply H. exists x. split.
  apply Hy. apply I.
Qed.

Theorem Exercise2_4 : forall (A B uA uB : set), Union A uA -> Union B uB ->
  Subset A B -> Subset uA uB.
Proof.
  intros A B uA uB HA HB H x I.
  apply HB. apply HA in I. destruct I as [a [Ia Ib]].
  apply H in Ib. exists a. split. apply Ia. apply Ib.
Qed.

Theorem Exercise2_5 : forall (A uA B : set),
  Union A uA -> (forall (x : set), In x A -> Subset x B) -> Subset uA B.
Proof.
  intros A uA B HA HB x I.
  apply HA in I. destruct I as [a [Ia Ib]].
  apply HB in Ib. apply Ib. apply Ia.
Qed.

Theorem Exercise2_6a : forall (A PA uPA : set),
  PowerSet A PA -> Union PA uPA -> uPA = A.
Proof.
  intros A PA uPA HP HU. apply Extensionality_Axiom. split.
  - intros H. apply HU in H. destruct H as [a [Ha Hb]].
    apply HP in Hb. apply Hb. apply Ha.
  - intros H. apply HU. exists A. split.
    apply H. apply HP. apply Subset_Reflexive.
Qed.

Theorem Exercise2_6b : forall (A uA PuA : set),
  PowerSet uA PuA -> Union A uA -> Subset A PuA.
Proof.
  intros A uA PuA HP HU x H. apply HP.
  intros y Hy. apply HU. exists x. split.
  apply Hy. apply H.
Qed.

(** Follow-up question to 6b, under what conditions does equality hold? *)

(** TODO: It's kinda tricky to do it in a way that doesn't just assert that A is 
    the powerset of UA... *)

Theorem Exercise2_7a : forall (A B PA PB AnB PAnPB PAnB: set),
  PowerSet A PA -> PowerSet B PB -> BinaryIntersect A B AnB ->
  BinaryIntersect PA PB PAnPB -> PowerSet AnB PAnB -> PAnB = PAnPB.
Proof.
  intros A B PA PB AnB PAnPB PAnB HA HB Hn HnP HPn.
  apply Extensionality_Axiom. intros x. split.
  - intros H. apply HnP. split.
    + apply HA. intros y I. apply HPn in H. apply H in I.
      apply Hn. apply I.
    + apply HPn in H. apply HB. intros y I. apply H in I.
      apply Hn in I as [ _ I ]. apply I.
  - intros H. apply HPn. intros y I. apply Hn. split.
    + apply HnP in H as [ H _ ]. apply HA in H. apply H in I. assumption.
    + apply HnP in H as [ _ H ]. apply HB in H. apply H in I. assumption.
Qed.

Theorem Exercise2_7b : forall (A B PA PB AuB PAuPB PAuB : set),
  PowerSet A PA -> PowerSet B PB -> BinaryUnion A B AuB ->
  BinaryUnion PA PB PAuPB -> PowerSet AuB PAuB -> Subset PAuPB PAuB.
Proof.
  intros A B PA PB AuB PAuPB PAuB HA HB Hu HuP HPu x H.
  apply HPu. intros y I. apply Hu. apply HuP in H. destruct H.
  - apply HA in H. apply H in I. left. assumption.
  - apply HB in H. apply H in I. right. assumption.
Qed.

(** Follow-up question to 7b, under what conditions does equality hold? *)

(** TODO : Again tricky for the same reason. *)

Theorem Exercise2_8 : ~ exists (A : set), forall (x : set), exists (X : set),
  In X A /\ Singleton x X.
Proof.
  intros C. destruct C as [A C].
  union A. destruct (Enderton2A x).
  apply H0. apply H. destruct (C x0) as [X [Ha Hb]].
  exists X. split. apply Hb. reflexivity. apply Ha.
Qed.

Theorem Exercise2_9 : exists (a B Pa PB : set), PowerSet a Pa -> PowerSet B PB ->
  In a B /\ ~ In Pa PB.
Proof.
  empty. singleton x. pair x x0. singleton x1.
  powerset x1. powerset x2.
  exists x1. exists x2. exists x3. exists x4.
  intros I J. split.
  - apply H2. trivial.
  - intros C. apply H4 in C.
    assert (K : In x x3). apply H3.
    intros y Hy. apply H in Hy. inversion Hy. apply C in K.
    apply H2 in K. rewrite K in H. 
    assert (L : In x x1). apply H1. left. trivial.
    apply H in L. inversion L.
Qed.

Theorem Exercise2_10 : forall (a B Pa uB PuB PPuB : set), 
  PowerSet a Pa -> Union B uB -> PowerSet uB PuB -> PowerSet PuB PPuB ->
  In a B -> In Pa PPuB.
Proof.
  intros a B Pa uB PuB PPub HPa HuB HPub HPPub H.
  apply HPPub. intros x. intros Hx.
  apply HPub. intros y Hy.
  apply HuB. exists a. split.
  - apply HPa in Hx. apply Hx in Hy. apply Hy.
  - apply H.
Qed.

(** Next, we define set difference or relative complement. We show that A \ B is
    well-defined by using a subset axiom on A. *)

Definition SetMinus (A B C : set) : Prop :=
  forall (x : set), In x C <-> In x A /\ ~ In x B.

Theorem SetMinus_Exists : forall (A B : set), exists (C : set), SetMinus A B C.
Proof.
  intros A B.
  build_set set (fun (t c x : set) => ~In x t) B A.
  exists x. intros y. split.
  - intros Hy. apply H. apply Hy.
  - intros Hy. apply H. apply Hy.
Qed.

Theorem SetMinus_Unique : forall (A B C D: set),
  SetMinus A B C -> SetMinus A B D -> C = D.
Proof.
  intros A B C D HC HD. apply Extensionality_Axiom. intros x. split.
  - intros H. apply HD. apply HC in H. apply H.
  - intros H. apply HC. apply HD in H. apply H.
Qed.

Ltac minus A B := destruct (SetMinus_Exists A B).

(** While relative complements are well-defined, absolute complements are not.
    This is a consequence of the fact that there is no universal set. *)

Theorem No_Absolute_Complement : forall (A : set), ~ exists (B : set),
  forall (x : set), In x B <-> ~ In x A.
Proof.
  intros A [B HB]. binary_union A B.
  destruct (Enderton2A x) as [y Hy].
  apply Hy. apply H. assert (P : In y A \/ ~ In y A).
  apply (REM (In y A)). destruct P.
  - left. assumption.
  - right. apply HB. apply H0.
Qed.

(** We now turn our attention to some elementary properties of the algebra of
    sets. That is, we treat union, intersect, and complement as algebraic
    operators and prove some important algebraic properites. *)

Theorem Union_Commutative : forall (A B AuB BuA : set),
  BinaryUnion A B AuB -> BinaryUnion B A BuA -> AuB = BuA.
Proof.
  intros A B AuB BuA HAuB HBuA. apply Extensionality_Axiom. intros x. split.
  - intros H. apply HBuA. apply HAuB in H. destruct H as [ H | H ].
    + right. apply H.
    + left. apply H.
  - intros H. apply HAuB. apply HBuA in H. destruct H as [ H | H ].
    + right. assumption.
    + left. assumption.
Qed.

Theorem Intersect_Commutative : forall (A B AnB BnA : set),
  BinaryIntersect A B AnB -> BinaryIntersect B A BnA -> AnB = BnA.
Proof.
  intros A B AnB BnA HAnB HBnA. apply Extensionality_Axiom. intros x. split; intros H.
  - apply HBnA. apply HAnB in H. split. apply H. apply H.
  - apply HAnB. apply HBnA in H. split. apply H. apply H.
Qed.

Theorem Union_Associative : forall (A B C AuB BuC AuBC ABuC : set),
  BinaryUnion A B AuB -> BinaryUnion B C BuC -> BinaryUnion A BuC AuBC ->
  BinaryUnion AuB C ABuC -> AuBC = ABuC.
Proof.
  intros A B C AuB BuC AuBC ABuC HAuB HBuC HAuBC HABuC.
  apply Extensionality_Axiom. intros x. split; intros H.
  - apply HABuC. apply HAuBC in H. destruct H as [ H | H ].
    + left. apply HAuB. left. apply H.
    + apply HBuC in H. destruct H as [ H | H ].
      * left. apply HAuB. right. assumption.
      * right. apply H.
  - apply HAuBC. apply HABuC in H. destruct H as [ H | H ].
    + apply HAuB in H. destruct H as [ H | H ].
      * left. assumption.
      * right. apply HBuC. left. assumption.
    + right. apply HBuC. right. assumption.
Qed.

Theorem Intersect_Associative : forall (A B C AnB BnC AnBC ABnC : set),
  BinaryIntersect A B AnB -> BinaryIntersect B C BnC ->
  BinaryIntersect A BnC AnBC -> BinaryIntersect AnB C ABnC -> AnBC = ABnC.
Proof.
  intros A B C AnB BnC AnBC ABnC HAnB HBnC HAnBC HABnC.
  apply Extensionality_Axiom. intros x. split; intros H.
  - apply HABnC. split.
    + apply HAnB. split.
      * apply HAnBC in H as [H _]. apply H.
      * apply HAnBC in H as [_ H]. apply HBnC in H as [H _]. apply H.
    + apply HAnBC in H as [_ H]. apply HBnC in H as [_ H]. assumption.
  - apply HAnBC. apply HABnC in H as [H HC]. apply HAnB in H as [HA HB]. split.
    + assumption.
    + apply HBnC. split; assumption.
Qed.

Theorem Intersect_Distributes_Over_Union : forall (A B C BuC AnBuC AnB AnC AnBuAnC : set),
  BinaryUnion B C BuC -> BinaryIntersect A BuC AnBuC -> BinaryIntersect A B AnB ->
  BinaryIntersect A C AnC -> BinaryUnion AnB AnC AnBuAnC -> AnBuC = AnBuAnC.
Proof.
  intros A B C BuC AnBuC AnB AnC AnBuAnC HBuC HAnBuC HAnB HAnC HAnBuAnC.
  apply Extensionality_Axiom. intros x. split; intros H.
  - apply HAnBuAnC. apply HAnBuC in H as [HA H]. apply HBuC in H as [H | H].
    + left. apply HAnB. split; assumption.
    + right. apply HAnC. split; assumption.
  - apply HAnBuC. apply HAnBuAnC in H as [H | H].
    + apply HAnB in H as [HA HB]. split; try (apply HBuC; left); assumption.
    + apply HAnC in H as [HA HC]. split; try (apply HBuC; right); assumption.
Qed.

Theorem Union_Distributes_Over_Intersect : forall (A B C BnC AuBnC AuB AuC AuBnAuC : set),
  BinaryIntersect B C BnC -> BinaryUnion A BnC AuBnC -> BinaryUnion A B AuB ->
  BinaryUnion A C AuC -> BinaryIntersect AuB AuC AuBnAuC -> AuBnC = AuBnAuC.
Proof.
  intros A B C BnC AuBnC AuB AuC AuBnAuC HBnC HAuBnC HAuB HAuC HAuBnAuC.
  apply Extensionality_Axiom. intros x. split; intros H.
  - apply HAuBnAuC. apply HAuBnC in H as [H | H].
    + split; try apply HAuB; try apply HAuC; left; assumption.
    + apply HBnC in H as [HB HC]. split.
      * apply HAuB. right. assumption.
      * apply HAuC. right. assumption.
  - apply HAuBnC. apply HAuBnAuC in H as [HB HC].
    apply HAuB in HB as [ HB | HB ];
    apply HAuC in HC as [ HC | HC ]; try (left; assumption).
    right. apply HBnC. split; assumption.
Qed.

Theorem DeMorgan_For_Union : forall (A B C AuB AuB' A' B' A'nB' : set),
  BinaryUnion A B AuB -> SetMinus C AuB AuB' -> SetMinus C A A' ->
  SetMinus C B B' -> BinaryIntersect A' B' A'nB' -> AuB' = A'nB'.
Proof.
  intros A B C AuB AuB' A' B' A'nB' HAuB HAuB' HA' HB' HA'nB'.
  apply Extensionality_Axiom. intros x. split; intros H.
  - apply HA'nB'. apply HAuB' in H as [ HC  HAB ]. split;
    try apply HA'; try apply HB'; split; try assumption; intros Contra;
    apply HAB; apply HAuB; try (left; assumption); try (right; assumption).
  - apply HAuB'. apply HA'nB' in H as [HA HB].
    apply HA' in HA as [HC HA]. apply HB' in HB as [_ HB].
    split; try assumption. intros Contra. apply HAuB in Contra as [Contra | Contra].
    + apply HA. assumption.
    + apply HB. assumption.
Qed.

Theorem DeMorgan_For_Intersect : forall (A B C AnB AnB' A' B' A'uB' : set),
  BinaryIntersect A B AnB -> SetMinus C AnB AnB' -> SetMinus C A A' ->
  SetMinus C B B' -> BinaryUnion A' B' A'uB' -> AnB' = A'uB'.
Proof.
  intros A B C AnB AnB' A' B' A'uB' HAnB HAnB' HA' HB' HA'uB'.
  apply Extensionality_Axiom. intros x. split; intros H.
  - apply HA'uB'. apply HAnB' in H as [ HC HAB].
    assert (I : ~ (In x A /\ In x B)).
    intros Contra. apply HAnB in Contra. apply HAB in Contra. assumption.
    apply DeMorgan in I. destruct I as [ I | I ].
    + left. apply HA'. split; assumption.
    + right. apply HB'. split; assumption.
  - apply HAnB'. apply HA'uB' in H. destruct H as [ H | H ].
    + apply HA' in H as [ HC HA ]. split; try assumption.
      intros Contra. apply HAnB in Contra as [H _]. apply HA in H.
      assumption.
    + apply HB' in H as [ HC HB ]. split; try assumption. intros Contra.
      apply HAnB in Contra as [ _ Contra]. apply HB in Contra. assumption.
Qed.

Theorem Empty_Identity : forall (A B AuB : set), 
  BinaryUnion A B AuB -> Empty B -> AuB = A.
Proof.
  intros A B AuB Hu He. apply Extensionality_Axiom. intros x. split; intros H.
  - apply Hu in H as [ H | H ]; try assumption. apply He in H. inversion H.
  - apply Hu. left. assumption.
Qed.

Theorem Empty_Annihilator : forall (A B AnB : set),
  BinaryIntersect A B AnB -> Empty B -> Empty AnB.
Proof.
  intros A B AnB Hn He x C. apply Hn in C as [_ C].
  apply He in C. assumption.
Qed.

Theorem Relative_Inverse : forall (A B A' AnA' : set),
  SetMinus B A A' -> BinaryIntersect A A' AnA' -> Empty AnA'.
Proof.
  intros A B A' AnA' Hm Hn x C.
  apply Hn in C as [C C']. apply Hm in C' as [_ C'].
  apply C' in C. assumption.
Qed.

Theorem SuperSet_Annihilator : forall (A S AuS : set),
  BinaryUnion A S AuS -> Subset A S -> AuS = S.
Proof.
  intros A S AuS Hu Hs. apply Extensionality_Axiom. intros x. split; intros H.
  - apply Hu in H as [H|H].
    + apply Hs in H. assumption.
    + assumption.
  - apply Hu. right. assumption.
Qed.

Theorem SuperSet_Identity : forall (A S AnS : set),
  BinaryIntersect A S AnS -> Subset A S -> AnS = A.
Proof. 
  intros A S AnS Hn Hs. apply Extensionality_Axiom. intros x. split; intros H.
  - apply Hn in H as [Ha Hb]. assumption.
  - apply Hn. split; try apply Hs; assumption.
Qed.

(** Having finished with elementary algebraic properties, we mention some
    ordering properties, treating subset as a partial ordering relation on sets. *)

Theorem BinaryUnion_Monotonic : forall (A B C AuC BuC : set),
  BinaryUnion A C AuC -> BinaryUnion B C BuC -> Subset A B -> Subset AuC BuC.
Proof.
  intros A B C AuC BuC HAuC HBuC Hsub x Hx.
  apply HBuC. apply HAuC in Hx as [Hx|Hx].
  - apply Hsub in Hx. left. assumption.
  - right. assumption.
Qed.

Theorem BinaryIntersect_Monotonic : forall (A B C AnC BnC : set),
  BinaryIntersect A C AnC -> BinaryIntersect B C BnC -> Subset A B -> Subset AnC BnC.
Proof.
  intros A B C AnC BnC HAnC HBnC Hsub x Hx.
  apply HBnC. apply HAnC in Hx as [Hx Hx']. split; try assumption.
  apply Hsub in Hx. assumption.
Qed.

Theorem Union_Monotonic : forall (A B UA UB : set),
  Union A UA -> Union B UB -> Subset A B -> Subset UA UB.
Proof.
  intros A B UA UB HA HB Hsub x Hx.
  apply HB. apply HA in Hx as [a [Hx Ha]].
  exists a. split; try assumption. apply Hsub in Ha. assumption.
Qed.

Theorem SetMinus_Antimonotonic : forall (A B C A' B' : set),
  SetMinus C A A' -> SetMinus C B B' -> Subset A B -> Subset B' A'.
Proof.
  intros A B C A' B' HA HB Hsub x Hx.
  apply HA. apply HB in Hx as [Hx Hx']. split; try assumption.
  intros Contra. apply Hsub in Contra. apply Hx' in Contra. assumption.
Qed.

Theorem Intersect_Antimonotonic : forall (A B nA nB : set),
  ~Empty A -> Intersect A nA -> Intersect B nB -> Subset A B -> Subset nB nA.
Proof.
  intros A B nA nB Hpre HA HB Hsub x Hx.
  apply HA. apply Hpre. intros y H.
  assert (J : forall y : set, In y B -> In x y).
  apply HB. intros C. apply (C y). apply Hsub. assumption.
  apply Hx. apply J. apply Hsub in H. assumption.
Qed.

(** This done, we want to generalize some of the algebraic properties to
    unary union and unary intersection. Doing so requires some rather elaborate
    definitions. *)


(** This is the set { A u X | X in B }, which we prove to be well-defined below. *)
Definition Elementwise_Union (A B D : set) : Prop :=
  forall (x : set), In x D <-> exists (X : set), In X B /\ BinaryUnion A X x.

Theorem Elementwise_Union_Exists : forall (A B : set), exists (D : set),
  Elementwise_Union A B D.
Proof.
  intros A B.
  union B. binary_union A x. powerset x0.
  build_set
    (prod set set)
    (fun (t : set * set) (c x : set) => exists (X : set), In X (snd t) /\ BinaryUnion (fst t) X x)
    (A, B)
    x1.
  exists x2. intros y. split; intros I.
  - apply H2 in I. apply I.
  - apply H2. split; try apply I. apply H1. intros z Hz. apply H0.
    destruct I as [ X [Ia Ib]]. apply Ib in Hz. destruct Hz as [Hz | Hz].
    + left. assumption.
    + right. apply H. exists X. split; assumption.
Qed.

Theorem Elementwise_Union_Unique : forall A B C D,
  Elementwise_Union A B C -> Elementwise_Union A B D -> C = D.
Proof.
  intros A B C D HC HD. apply Extensionality_Axiom. intros x. split; intros H.
  - apply HD. apply HC. assumption.
  - apply HC. apply HD. assumption.
Qed.

(** We are now ready to prove (at length) a generalized version of the fact
    that union distributes over intersection. *)

Theorem Generalized_Union_Distributivity : forall (A B nB AunB euAB neuAB : set),
  ~ Empty B -> Intersect B nB -> BinaryUnion A nB AunB ->
  Elementwise_Union A B euAB -> Intersect euAB neuAB -> AunB = neuAB.
Proof.
  intros A B nB AunB euAB neuAB HB HnB HAunB HeuAB HneuAB.
  apply Extensionality_Axiom. intros x. 
  assert (I : ~Empty euAB).
  { intros C. apply Member_Exists_If_NonEmpty in HB as [y Hy].
    binary_union A y. apply (C x0). apply HeuAB. exists y. split; assumption. }
  split; intros H.
  - apply HneuAB. assumption. intros y Hy. apply HeuAB in Hy.
    destruct Hy as [X [Hya Hyb]]. apply Hyb.
    apply HAunB in H. destruct H as [ H | H ].
    + left. assumption.
    + right. apply HnB in HB. unfold PreIntersect in HB.
      assert (J : forall y: set, In y B -> In x y).
      apply HB. apply H. apply J. apply Hya.
  - assert (P : forall y, In y euAB -> In x y).
    { apply HneuAB; assumption. }
    clear H. rename P into H.
    apply Member_Exists_If_NonEmpty in I as [AuX I].
    apply HeuAB in I. destruct I as [X [HX HAuX]].
    assert (P : In x AuX). { apply H. apply HeuAB. exists X; split; assumption. }
    apply HAuX in P. destruct P as [P | P].
    + apply HAunB. left. assumption.
    + assert (Q : forall y Auy, BinaryUnion A y Auy -> In y B -> In x Auy).
      { intros y Auy HAuy Hy. apply H. apply HeuAB. exists y. split; assumption. }
      assert (R : forall y, In y B -> In x A \/ In x y).
      { intros y Hy. binary_union A y. assert (R : In x x0).
        { apply (Q y); assumption. }
        apply H0 in R. destruct R as [R | R].
        - left. assumption.
        - right. assumption. }
      apply HAunB. assert (S : In x A \/ ~ In x A). {apply REM. }
      destruct S as [S | S].
      * left; assumption.
      * right. apply (HnB HB). intros y Hy. destruct (R y Hy) as [R' | R'].
        { apply S in R'. inversion R'. }
        { apply R'. }
Qed.

(** Again, some elaborate definitions are required for the generalized form of
    these theorems. *)

(** This is the set { A n X | X in B }. *)
Definition Elementwise_Intersect (A B D : set) : Prop :=
  forall (x : set), In x D <-> exists (X : set), In X B /\ BinaryIntersect A X x.

Theorem Elementwise_Intersect_Exists : forall (A B : set), exists (D : set),
  Elementwise_Intersect A B D.
Proof.
  intros A B. union B. binary_union A x. powerset x0.
  build_set
    (prod set set)
    (fun (t : set * set) (c x : set) => exists (X : set), In X (snd t) /\ BinaryIntersect (fst t) X x)
    (A, B)
    x1.
  exists x2. intros y. split; intros I.
  - apply H2. assumption.
  - apply H2. split; try assumption. apply H1. intros z Hz.
    destruct I as [X [Ia Ib]]. apply Ib in Hz. apply H0. left. apply Hz.
Qed.

Theorem Elementwise_Intersect_Unique : forall (A B C D : set),
  Elementwise_Intersect A B C -> Elementwise_Intersect A B D -> C = D.
Proof.
  intros A B C D HC HD. apply Extensionality_Axiom. intros x. split; intros H.
  - apply HD. apply HC. assumption.
  - apply HC, HD; assumption.
Qed.

(** We can now state and prove the general form of the fact that intersection
    distributes over union. *)

Theorem Generalized_Intersect_Distributivity : forall (A B uB AnuB enAB uenAB : set),
  Union B uB -> BinaryIntersect A uB AnuB -> Elementwise_Intersect A B enAB ->
  Union enAB uenAB -> AnuB = uenAB.
Proof.
  intros A B uB AnuB enAB uenAB HuB HAnuB HenAB HuenAB.
  apply Extensionality_Axiom. intros x. split; intros H.
  - apply HuenAB. apply HAnuB in H as [H I].
    apply HuB in I as [a [Ha Ha']].
    binary_intersect A a. exists x0. split.
    + apply H0. split; assumption.
    + apply HenAB. exists a. split; assumption.
  - apply HAnuB. apply HuenAB in H as [a [H I]].
    apply HenAB in I as [X [HX HX']].
    apply HX' in H. destruct H as [H I].
    split. assumption. apply HuB. exists X. split; assumption.
Qed.

(** We also wish to give a generalize account of the DeMorgan equalities for
    relative complements. This requires yet another elborate definition. *)

(** This is the set { C \ X | X in A }. *)
Definition Elementwise_Complement (C A D : set) : Prop :=
  forall (x : set), In x D <-> exists (X : set), In X A /\ SetMinus C X x.

Theorem Elementwise_Complement_Exists : forall (C A : set), exists (D : set), 
  Elementwise_Complement C A D.
Proof.
  intros C A. powerset C.
  build_set
    (prod set set)
    (fun (t : set * set) (c x : set) => exists (X : set), In X (snd t) /\ SetMinus (fst t) X x)
    (C, A)
    x.
  exists x0. intros y. split; intros I.
  -  apply H0. assumption.
  - apply H0. split; try assumption. apply H. intros z Hz.
    destruct I as [X [Ia Ib]]. apply Ib in Hz. apply Hz.
Qed.

Theorem Generalized_Union_DeMorgan : forall (C A uA CuA ecCA necCA : set),
  ~Empty A -> Union A uA -> SetMinus C uA CuA ->
  Elementwise_Complement C A ecCA -> Intersect ecCA necCA -> CuA = necCA.
Proof.
  intros C A uA CuA ecCA necCA He HuA HCuA HecCA HnecCA.
  apply Extensionality_Axiom. intros x. split; intros H.
  - apply HnecCA.
    { apply Member_Exists_If_NonEmpty in He as [y Hy].
      intros Ctra. minus C y. apply (Ctra x0).
      apply HecCA. exists y. split; assumption. }
    intros y Hy. apply HecCA in Hy. destruct Hy as [X [HX HX']].
    apply HX'. apply HCuA in H. split.
    + apply H.
    + intros Ctra. destruct H as [_ H]. apply H. apply HuA.
      exists X. split; assumption.
  - assert (P : ~ Empty ecCA).
    { intros Con. apply He. intros y. intros Hy.
      minus C y. assert (T : In x0 ecCA).
      { apply HecCA. exists y. split; assumption. }
      apply Con in T. apply T. }
    assert (Q : forall y, In y ecCA -> In x y). { apply HnecCA; assumption. }
    assert (R : forall X CmX, SetMinus C X CmX -> In X A -> In x CmX).
    { intros X CmX HCmX HX. apply Q. apply HecCA. exists X. split; assumption. }
    apply Member_Exists_If_NonEmpty in P. destruct P as [CmX HCmX].
    apply HecCA in HCmX. destruct HCmX as [X [HX HCmX]].
    assert (R' : In x CmX). apply (R X CmX HCmX HX). apply HCmX in R'.
    destruct R' as [S T]. apply HCuA. split; try assumption.
    intros Con. apply HuA in Con. destruct Con as [a [Ha Con]].
    minus C a. assert (U : In x x0). apply (R a). assumption. assumption.
    apply H0 in U. destruct U as [_ U]. apply U in Ha. assumption.
Qed.

Theorem Generalized_Intersect_DeMorgan : forall (C A nA CnA ecCA uecCA : set),
  ~Empty A -> Intersect A nA -> SetMinus C nA CnA ->
  Elementwise_Complement C A ecCA -> Union ecCA uecCA -> CnA = uecCA.
Proof.
  intros C A nA CnA ecCA uecCA He HnA HCnA HecCA HuecCA.
  apply Extensionality_Axiom. intros x. split; intros H.
  - apply HCnA in H. apply HuecCA. destruct H as [H I].
    assert (P : exists y, In y A /\ ~ In x y).
    { apply Not_Forall_Implies_Exists. intros Con.
      apply I. apply HnA. apply He. intros y Hy.
      assert (T : In x y \/ ~ In x y). apply REM.
      destruct T as [T | T].
      - assumption.
      - assert (U : In y A /\ ~ In x y). split; assumption. apply Con in U.
        inversion U. }
    destruct P as [X [HX P]]. minus C X.
    rename x0 into CmX. rename H0 into HCmX. exists CmX. split.
    + apply HCmX. split; assumption.
    + apply HecCA. exists X. split; assumption.
  - apply HuecCA in H.
    destruct H as [CmX [H HCmX]]. apply HecCA in HCmX.
    destruct HCmX as [X [HX HCmX]].
    apply HCmX in H. destruct H as [H I].
    apply HCnA. split; try assumption. intros Con.
    assert (P : forall y, In y A -> In x y). { apply HnA. apply He. apply Con. }
    apply I. apply P. assumption.
Qed.

Theorem Exercise2_11a : forall (A B AnB AmB AnBuAmB : set),
  BinaryIntersect A B AnB -> SetMinus A B AmB -> BinaryUnion AnB AmB AnBuAmB ->
  A = AnBuAmB.
Proof.
  intros A B AnB AmB AnBuAmB HAnB HAmB Hu.
  apply Extensionality_Axiom. intros x. split; intros H.
  - apply Hu. assert (I : In x B \/ ~ In x B). { apply REM. }
    destruct I as [I | I].
    + left. apply HAnB. split; assumption.
    + right. apply HAmB. split; assumption.
  - apply Hu in H. destruct H as [H | H].
    + apply HAnB in H. apply H.
    + apply HAmB. assumption.
Qed.

Theorem Exercise2_11b : forall (A B BmA AuBmA AuB : set),
  SetMinus B A BmA -> BinaryUnion A BmA AuBmA -> BinaryUnion A B AuB ->
  AuBmA = AuB.
Proof.
  intros A B BmA AuBmA AuB HBmA HAuBmA HAuB.
  apply Extensionality_Axiom. intros x. split; intros H.
  - apply HAuBmA in H. apply HAuB. destruct H as [H | H].
    + left. assumption.
    + right. apply HBmA in H. apply H.
  - apply HAuBmA. apply HAuB in H. destruct H as [H | H].
    + left. assumption.
    + assert (I : In x A \/ ~ In x A). { apply REM. }
      destruct I as [I | I].
      * left; assumption.
      * right. apply HBmA. split; assumption.
Qed.

Theorem Exercise2_12 : forall (A B C AnB AnB' A' B' A'uB' : set),
  BinaryIntersect A B AnB -> SetMinus C AnB AnB' -> SetMinus C A A' ->
  SetMinus C B B' -> BinaryUnion A' B' A'uB' -> AnB' = A'uB'.
Proof.
  apply DeMorgan_For_Intersect.
Qed.

Theorem Exercise2_13 : forall (A B C A' B' : set),
  SetMinus C A A' -> SetMinus C B B' -> Subset A B -> Subset B' A'.
Proof.
  apply SetMinus_Antimonotonic.
Qed.

Theorem Exercise2_14 : exists (A B C AmB BmC l r : set),
  SetMinus A B AmB /\ SetMinus B C BmC /\ SetMinus AmB C l /\
  SetMinus A BmC r /\ r <> l.
Proof.
  empty. singleton x. pair x x0. singleton x1. binary_union x1 x2.
  rename x0 into A. rename H0 into HA. rename x1 into B. rename x3 into C.
  rename H1 into HB. rename H3 into HC. rename x into empty. rename H into He.
  rename x2 into sB. rename H2 into HsB.
  exists A. exists B. exists C.
  minus A B. exists x. minus B C. exists x0. minus x C. exists x1.
  minus A x0. exists x2.
  split; try assumption.
  split; try assumption.
  split; try assumption.
  split; try assumption.
  intros Con. rename x into AmB. rename H into HAmB.
  rename x0 into BmC. rename H0 into HBmC.
  rename x1 into l. rename H1 into Hl.
  rename x2 into r. rename H2 into Hr.
  assert (I : In empty r).
  { apply Hr. split.
    - apply HA. reflexivity.
    - intros Con2. apply HBmC in Con2 as [ Con2 Con2'].
      apply Con2'. apply HC. left. apply HB. left. trivial.  }
  assert (J : ~ In empty l).
  { intros Con2. apply Hl in Con2. destruct Con2 as [Con2 Con2'].
    apply Con2'. apply HC. left. apply HB. left. trivial. }
  rewrite Con in I. apply J in I. apply I.
Qed.

Definition SymDiff (A B C : set) : Prop :=
  exists (AmB BmA u : set), SetMinus A B AmB /\ SetMinus B A BmA /\
  BinaryUnion AmB BmA u /\ forall (x : set), In x C <-> In x u.

Theorem SymDiff_Exists : forall (A B : set), exists (C : set), SymDiff A B C.
Proof.
  intros A B. minus A B. minus B A. binary_union x x0. exists x1.
  exists x. exists x0. exists x1.
  split; try assumption.
  split; try assumption.
  split; try assumption. intros y. split; intros; assumption.
Qed.

Theorem SymDiff_Unique : forall (A B C D : set), SymDiff A B C ->
  SymDiff A B D ->  C = D.
Proof.
  intros A B C D HC HD.
  destruct HC as [AmB [BmA [u [HAmB [HBmA [Hu HC]]]]]].
  destruct HD as [AmB' [BmA' [u' [HAmB' [HBmA' [Hu' HD]]]]]].
  assert (M1 : AmB' = AmB).
  { apply (SetMinus_Unique A B); assumption. }
  assert (M2 : BmA' = BmA).
  { apply (SetMinus_Unique B A); assumption. }
  rewrite M1 in Hu'. rewrite M2 in Hu'.
  assert (I : u' = u).
  { apply (BinaryUnion_Unique AmB BmA); assumption. }
  rewrite I in HD. apply Extensionality_Axiom. intros x. split; intros H.
  - apply HD. apply HC. assumption.
  - apply HC. apply HD. assumption.
Qed.  

Ltac symdiff A B := destruct (SymDiff_Exists A B).

Theorem Exercise2_15a : forall A B C BpC AnBpC AnB AnC AnBpAnC,
  SymDiff B C BpC -> BinaryIntersect A BpC AnBpC -> BinaryIntersect A B AnB ->
  BinaryIntersect A C AnC -> SymDiff AnB AnC AnBpAnC -> AnBpC = AnBpAnC.
Proof.
  intros A B C BpC AnBpC AnB AnC AnBpAnC HBpC HAnBpC HAnB HAnC HAnBpAnC.
  destruct HBpC as [BmC [CmB [BmCuCmB [HBmC [HCmB [HBmCuCmB HBpC]]]]]].
  destruct HAnBpAnC as [AnBmAnC [AnCmAnB [u [HAnBmAnC [HAnCmAnB [Hu HAnBpAnC]]]]]].
  apply Extensionality_Axiom. intros x. split; intros H.
  - apply HAnBpAnC. apply Hu. apply HAnBpC in H.
    destruct H as [H H']. apply HBpC in H'.
    apply HBmCuCmB in H'. destruct H' as [H' | H'].
    + left. apply HAnBmAnC. split.
      * apply HAnB. split; try assumption. apply HBmC in H'. apply H'.
      * intros Con. apply HBmC in H'. destruct H' as [I J].
        apply J. apply HAnC in Con. apply Con.
    + right. apply HAnCmAnB. split.
      * apply HAnC. split; try assumption. apply HCmB in H'. apply H'.
      * intros Con. apply HCmB in H'. destruct H' as [I J].
        apply J. apply HAnB in Con. apply Con.
  - apply HAnBpAnC in H. apply Hu in H. apply HAnBpC. split.
    + destruct H as [H | H].
      * apply HAnBmAnC in H. destruct H as [H _]. apply HAnB in H. apply H.
      * apply HAnCmAnB in H. destruct H as [H _]. apply HAnC in H. apply H.
    + destruct H as [H | H].
      * apply HBpC. apply HBmCuCmB. apply HAnBmAnC in H.
        destruct H as [H I]. left. apply HBmC.
        apply HAnB in H. split; try apply H. intros Con. apply I.
        apply HAnC. split; try assumption. apply H.
      * apply HBpC. apply HBmCuCmB. apply HAnCmAnB in H.
        destruct H as [H I]. right. apply HCmB.
        apply HAnC in H. split; try apply H. intros Con.
        apply I. apply HAnB. split; try assumption. apply H.
Qed.

Theorem Exercise2_15b : forall A B C ApB BpC r l, 
  SymDiff A B ApB -> SymDiff B C BpC -> SymDiff A BpC r -> SymDiff ApB C l ->
  r = l.
Proof.
  intros A B C ApB BpC r l HApB HBpC Hr Hl.
  destruct HApB as [AmB [BmA [AmBuBmA [HAmB [HBmA [HAmBuBmA HApB]]]]]].
  destruct HBpC as [BmC [CmB [BmCuCmB [HBmC [HCmB [HBmCuCmB HBpC]]]]]].
  destruct Hr as [AmBpC [BpCmA [ur [HAmBpC [HBpCmA [Hur Hr]]]]]].
  destruct Hl as [ApBmC [BmCpA [ul [HApBmC [HBmCpA [Hul Hl]]]]]].
  apply Extensionality_Axiom. intros x. split; intro H.
  - apply Hl. apply Hul. apply Hr in H. apply Hur in H. destruct H as [H | H].
    + apply HAmBpC in H as [H I].
      assert (J : In x C \/ ~ In x C). { apply REM. }
      destruct J as [J | J].
      * right. apply HBmCpA. split; try assumption.
        intros Con. apply I. apply HBpC.
        apply HApB in Con. apply HAmBuBmA in Con.
        apply HBmCuCmB. destruct Con as [Con | Con].
        { right. apply HCmB. split; try assumption. apply HAmB in Con.
          apply Con. }
        { right. apply HCmB. split; try assumption. apply HBmA in Con.
          destruct Con as [_  Con]. intros Con'. apply Con. assumption. }
      * left. apply HApBmC. split; try assumption.
        apply HApB. apply HAmBuBmA. left. apply HAmB. split; try assumption.
        intros Con. apply I. apply HBpC. apply HBmCuCmB.
        left. apply HBmC. split; try assumption.
    + apply HBpCmA in H as [H I].
      apply HBpC in H. apply HBmCuCmB in H. destruct H as [H | H].
      * left. apply HApBmC. split.
        { apply HApB. apply HAmBuBmA. right. apply HBmA. split; try assumption.
          apply HBmC in H. apply H. }
        { apply HBmC in H. apply H. }
      * right. apply HBmCpA. apply HCmB in H as [H H']. split; try assumption.
        intros Con. apply HApB in Con. apply HAmBuBmA in Con.
        destruct Con as [Con | Con].
        { apply HAmB in Con. apply I, Con. }
        { apply HBmA in Con. apply H', Con. }
  - apply Hr. apply Hl in H. apply Hur. apply Hul in H.
    destruct H as [H | H].
    + apply HApBmC in H as [H I]. apply HApB in H. apply HAmBuBmA in H.
      destruct H as [H | H].
      * left. apply HAmBpC. apply HAmB in H. destruct H as [H H'].
        split; try assumption. intros Con. apply HBpC in Con.
        apply HBmCuCmB in Con. destruct Con as [Con | Con].
        { apply HBmC in Con. apply H', Con. }
        { apply HCmB in Con. apply I, Con. }
      * apply HBmA in H. right. destruct H as [H H'].
        apply HBpCmA. split; try assumption. apply HBpC. apply HBmCuCmB.
        left. apply HBmC. split; assumption.
    + apply HBmCpA in H as [H I].
      assert (J : In x A \/ ~ In x A). {apply REM. }
      destruct J as [J | J].
      * left. apply HAmBpC. split; try assumption. intros Con.
        apply I. apply HApB. apply HAmBuBmA. apply HBpC in Con.
        apply HBmCuCmB in Con. destruct Con as [Con | Con].
        { apply HBmC in Con as [_ Con]. apply Con in H. inversion H. }
        { left. apply HAmB. apply HCmB in Con as [_ Con]. split; try assumption. }
      * right. apply HBpCmA. split; try assumption. apply HBpC.
        apply HBmCuCmB. right. apply HCmB. split; try assumption.
        intros Con. apply I. apply HApB. apply HAmBuBmA.
        right. apply HBmA. split; assumption.
Qed.

(** Excercise 2-16 : Simplify [(A u B u C) n (A u B)] \ [(A u (B \ C)) n A] *)

(** Solution : TODO *)

Lemma A_Implies_B : forall A B AmB E, SetMinus A B AmB -> Empty E ->
  Subset A B -> AmB = E.
Proof.
  intros A B AmB E HAmB HE HB.
  apply Extensionality_Axiom. intros x. split; intros H.
  - apply HAmB in H as [H I]. apply HB in H. apply I in H. inversion H.
  - apply HE in H. inversion H.
Qed.

Lemma B_Implies_C : forall A B AmB E AuB, SetMinus A B AmB -> Empty E ->
  BinaryUnion A B AuB -> AmB = E -> AuB = B.
Proof.
  intros A B AmB E AuB HAmB HE HAuB H. apply Extensionality_Axiom.
  intros x. split; intros I.
  - apply HAuB in I. assert (J : In x B \/ ~ In x B).
    { apply REM. } destruct J as [J | J].
    + assumption.
    + destruct I as [I | I].
      * rewrite <- H in HE. assert (K : In x AmB).
        { apply HAmB. split; assumption. }
        apply HE in K. inversion K.
      * assumption.
  - apply HAuB. right. assumption.
Qed.

Lemma C_Implies_D : forall A B AuB AnB, BinaryUnion A B AuB -> 
  BinaryIntersect A B AnB -> AuB = B -> AnB = A.
Proof.
  intros A B AuB AnB HAuB HAnB Heq. apply Extensionality_Axiom.
  intros x. split; intros H.
  - apply HAnB in H. apply H.
  - apply HAnB. split; try assumption. rewrite <- Heq.
    apply HAuB. left. assumption.
Qed.

Lemma D_Implies_A : forall A B AnB, BinaryIntersect A B AnB ->
  AnB = A -> Subset A B.
Proof.
  intros A B AnB HAnB Heq x H.
  rewrite <- Heq in H. apply HAnB in H. apply H.
Qed.

Theorem Exercise2_17 : forall (A B AuB AmB E AnB : set),
  BinaryUnion A B AuB -> SetMinus A B AmB -> Empty E -> BinaryIntersect A B AnB ->
  (Subset A B <-> AmB = E) /\ (AmB = E <-> AuB = B) /\ (AuB = B <-> AnB = A).
Proof.
  intros A B AuB AmB E AnB HAuB HAmB HE HAnB. split.
  - split. apply A_Implies_B; assumption. intros H.
    apply (D_Implies_A A B AnB); try assumption.
    apply (C_Implies_D A B AuB); try assumption.
    apply (B_Implies_C A B AmB E); try assumption.
  - split.
    + split. apply (B_Implies_C A); assumption. intros H.
      apply (A_Implies_B A B); try assumption.
      apply (D_Implies_A A B AnB); try assumption.
      apply (C_Implies_D A B AuB); try assumption.
    + split. apply (C_Implies_D); assumption. intros H.
      apply (B_Implies_C A B AmB E); try assumption.
      apply (A_Implies_B A B); try assumption.
      apply (D_Implies_A A B AnB); try assumption.
Qed.

(** Exercise 2-18 : Assume A and B are subsets of S. List all the different sets
    that can be made from these three by use of binary union, binary intersect,
    and set difference. *)

(** Solution : TODO *)

(** Is P(A \ B) always equal to PA \ PB? Is it ever equal? *)
Theorem Exercise2_19 : forall A B PA PB AmB PAmB PAmPB, 
  PowerSet A PA -> PowerSet B PB -> SetMinus A B AmB -> PowerSet AmB PAmB ->
  SetMinus PA PB PAmPB -> PAmB <> PAmPB.
Proof.
  intros A B PA PB AmB PAmB PAmPB HPA HPB HAmB HPAmB HPAmPB C.
  empty. rename x into empty. rename H into He.
  assert (P : In empty PAmB).
  { apply HPAmB. intros x Con. apply He in Con. inversion Con. }
  assert (Q : ~ In empty PAmPB).
  { intros Con. apply HPAmPB in Con as [Con Con'].
    apply Con'. apply HPB. intros x T. apply He in T.
    inversion T. }
  rewrite C in P. apply Q in P. inversion P.
Qed.

Theorem Exercise2_20 : forall (A B C AuB AuC AnB AnC : set),
  BinaryUnion A B AuB -> BinaryUnion A C AuC -> BinaryIntersect A B AnB ->
  BinaryIntersect A C AnC -> AuB = AuC -> AnB = AnC -> B = C.
Proof.
  intros A B C AuB AuC AnB AnC HAuB HAuC HAnB HAnC Hueq Hneq.
  apply Extensionality_Axiom. intros x. split; intros H.
  - assert (P : In x AuB). { apply HAuB. right. assumption. }
    rewrite Hueq in P. apply HAuC in P. destruct P as [P | P]; try assumption.
    + assert (Q : In x AnB). { apply HAnB; split; assumption. }
      rewrite Hneq in Q. apply HAnC in Q. apply Q.
  - assert (P : In x AuC). { apply HAuC. right. assumption. }
    rewrite <- Hueq in P. apply HAuB in P. destruct P as [P | P]; try assumption.
    assert (Q : In x AnC). { apply HAnC; split; assumption. }
    rewrite <- Hneq in Q. apply HAnB in Q. apply Q.
Qed.

Theorem Exercise2_21 : forall (A B AuB UAuB UA UB UAuUB : set),
  BinaryUnion A B AuB -> Union AuB UAuB -> Union A UA -> Union B UB ->
  BinaryUnion UA UB UAuUB -> UAuB = UAuUB.
Proof.
  intros A B AuB UAuB UA UB UAuUB HAuB HUAuB HUA HUB HUAuUB.
  apply Extensionality_Axiom. intros x. split; intros H.
  - apply HUAuUB. apply HUAuB in H as [a[Ha H]].
    apply HAuB in H. destruct H as [H | H].
    + left. apply HUA. exists a. split; assumption.
    + right. apply HUB. exists a. split; assumption.
  - apply HUAuB. apply HUAuUB in H. destruct H as [H | H].
    + apply HUA in H as [a [Ha H]]. exists a. split.
      * assumption.
      * apply HAuB. left. assumption.
    + apply HUB in H as [a [Ha H]]. exists a.
      split; try apply HAuB; try right; try assumption.
Qed.

Theorem Exercise2_22 : forall (A B AuB NAuB NA NB NAnNB : set),
  BinaryUnion A B AuB -> Intersect AuB NAuB -> Intersect A NA ->
  Intersect B NB -> BinaryIntersect NA NB NAnNB -> ~ Empty A -> ~ Empty B ->
  NAuB = NAnNB.
Proof.
  intros A B AuB NAuB NA NB NAnNB HAuB HNAuB HNA HNB HNAnNB HneA HneB.
  assert (P : ~Empty AuB). { intros C. apply HneA. intros y Cy.
    assert (T: In y AuB). { apply HAuB. left. assumption. }
    apply C in T. apply T. }
  apply Extensionality_Axiom. intros x. split; intros H.
  - apply HNAnNB. assert (Q : forall y, In y AuB -> In x y).
    { apply HNAuB; assumption. } split.
    + apply HNA; try assumption. intros y Hy. apply Q.
      apply HAuB. left. assumption.
    + apply HNB; try assumption. intros y Hy. apply Q.
      apply HAuB. right. assumption.
  - apply HNAuB; try assumption. apply HNAnNB in H.
    destruct H as [H I].
    assert (H' : forall y, In y A -> In x y).
    { apply HNA; assumption. }
    assert (I' : forall y, In y B -> In x y).
    { apply HNB; assumption. }
    clear H. clear I. rename H' into H. rename I' into I.
    intros y Hy. apply HAuB in Hy. destruct Hy as [Hy | Hy].
    + apply H. assumption.
    + apply I. assumption.
Qed.

Theorem Exercise2_23 : forall (A B nB AunB euAB neuAB : set),
  ~ Empty B -> Intersect B nB -> BinaryUnion A nB AunB ->
  Elementwise_Union A B euAB -> Intersect euAB neuAB -> AunB = neuAB.
Proof.
  apply Generalized_Union_Distributivity.
Qed.

Definition Elementwise_PowerSet (a A : set) : Prop :=
  forall (X : set), In X A <-> exists (x : set), In x a /\ PowerSet x X.

Theorem Elementwise_PowerSet_Exists : forall A, exists epA,
  Elementwise_PowerSet A epA.
Proof.
  intros A. union A. powerset x. powerset x0.
  rename x into UA. rename H into HUA.
  rename x0 into PUA. rename H0 into HPUA.
  rename x1 into PPUA. rename H1 into HPPUA.
  build_set
   set
   (fun (t c x : set) => exists X, In X t /\ PowerSet X x)
   A
   PPUA.
  rename x into epA. rename H into HepA.
  exists epA. intros x. split; intros H.
  - apply HepA. assumption.
  - apply HepA. split.
    + apply HPPUA. intros y Hy. apply HPUA.
      intros z Hz. apply HUA.
      destruct H as [a [HA Ha]].
      apply Ha in Hy. exists a. split; try assumption.
      apply Hy. assumption.
    + apply H.
Qed.

Theorem Elementwise_PowerSet_Unique : forall a A A', Elementwise_PowerSet a A ->
  Elementwise_PowerSet a A' -> A = A'.
Proof.
  intros a A A' HA HA'. apply Extensionality_Axiom. intros x. split; intros H.
  - apply HA'. apply HA in H. assumption.
  - apply HA. apply HA' in H. assumption.
Qed.

Theorem Exercise2_24a : forall A NA PNA epA NepA,
  Intersect A NA -> PowerSet NA PNA -> Elementwise_PowerSet A epA ->
  Intersect epA NepA -> ~ Empty A -> PNA = NepA.
Proof.
  intros A NA PNA epA NepA HNA HPNA HepA HNepA HneA.
  assert (NE : ~ Empty epA). { intros Con.
    apply HneA. intros y Hy. powerset y.
    assert (T : In x epA). apply HepA. exists y. split; assumption.
    apply Con in T. assumption. }
  apply Extensionality_Axiom. intros x. split; intros H.
  - apply HPNA in H. apply HNepA. assumption.
    intros PX HPX. apply HepA in HPX.
    destruct HPX as [X [HX HPX]]. apply HPX.
    intros y Hy. apply H in Hy.
    assert (P : forall z, In z A -> In y z). { apply HNA; assumption. }
    apply P. assumption.
  - assert (P : forall y, In y epA -> In x y).
    { apply HNepA; assumption. }
    assert (R : forall X PX, PowerSet X PX -> In X A -> In x PX).
    { intros X PX HPX HX. apply P. apply HepA. exists X. split; assumption. }
    apply HPNA. intros Am HAm. apply HNA. apply HneA.
    intros a Ha. powerset a. assert (S : In x x0).
    { apply (R a); assumption. }
    apply H0 in S. apply S. assumption.
Qed.

Theorem Exercise2_24b : forall (A UA PUA epA UepA : set),
  Union A UA -> PowerSet UA PUA -> Elementwise_PowerSet A epA ->
  Union epA UepA -> Subset UepA PUA.
Proof.
  intros A UA PUA epA UepA HUA HPUA HepA HUepA x H.
  apply HPUA. intros y Hy. apply HUA.
  apply HUepA in H. destruct H as [PX [H HPX]].
  apply HepA in HPX. destruct HPX as [X [HX HPX]].
  exists X. split; try assumption. apply HPX in H.
  apply H in Hy. assumption.
Qed.

(** Follow-up question to 24b, under what conditions does equality hold? *)

(** Is A u UB always the same as U{A u X | X in B}? Under what conditions do
    equality hold? *)
Theorem Exercise2_25 : forall A B UB AuUB euAB UeuAB,
  Union B UB -> BinaryUnion A UB AuUB -> Elementwise_Union A B euAB ->
  Union euAB UeuAB -> ~Empty B -> AuUB = UeuAB.
Proof.
  intros A B UB AuUB euAB UeuAB HUB HAuUB HeuAB HUeuAB HBne.
  apply Extensionality_Axiom. intros x. split; intros H.
  - apply HUeuAB. apply HAuUB in H. destruct H as [H | H].
    + apply Member_Exists_If_NonEmpty in HBne. destruct HBne as [b Hb].
      binary_union A b. exists x0. split.
      apply H0. left. assumption. apply HeuAB. exists b. split; assumption.
    + apply HUB in H. destruct H as [b [Hb H]].
      binary_union A b. exists x0. split.
      apply H0. right. assumption.
      apply HeuAB. exists b. split; assumption.
  - apply HAuUB. apply HUeuAB in H. destruct H as [Aub [Hb HAub]].
    apply HeuAB in HAub. destruct HAub as [b [H HAub]].
    apply HAub in Hb. destruct Hb as [Hb | Hb].
    + left; assumption.
    + right. apply HUB. exists b. split; assumption.
Qed.

(** Equality holds if both A and B or neither A nor B is empty. *)

(** Exercise 26 : Consider the following sets:
    A = {3, 4}.
    B = {4, 3} u {},
    C = {4, 3} u { {} },
    D = { x | x^2 - 7x + 12 = 0 },
    E = { {}, 3, 4},
    F = {4, 4, 3},
    G = {4, {}, {}, 3}.
    For each pair of sets, specify whether or not the sets are equal. *)

(** Solution : A = B = D = F and C = E = G. *)

Theorem Exercise2_27 : exists A B AnB NA NB NAnNB NAnB,
  BinaryIntersect A B AnB /\ Intersect A NA /\ Intersect B NB /\
  BinaryIntersect NA NB NAnNB /\ Intersect AnB NAnB /\ ~ Empty AnB /\
  NAnNB <> NAnB.
Proof.
  empty. rename x into empty. rename H into He.
  singleton empty. rename x into SE. rename H into HSE.
  pair empty SE. rename x into A. rename H into HA.
  pair SE A. rename x into B. rename H into HB.
  binary_intersect A B. rename x into AnB. rename H into HAnB.
  assert (P : ~ Empty A).
  { intros Con. assert (T: In empty A). apply HA.
    left. trivial. apply Con in T. assumption. }
  intersect A P. rename x into NA. rename H into HNA.
  assert (Q : ~Empty B).
  { intros Con. assert (T : In SE B). apply HB.
    left. trivial. apply Con in T. assumption. }
  intersect B Q. rename x into NB. rename H into HNB.
  binary_intersect NA NB. rename x into NAnNB. rename H into HNAnNB.
  assert (R : ~ Empty AnB).
  { intros Con. assert (T : In SE AnB). { apply HAnB. split.
    - apply HA. right. trivial.
    - apply HB. left. trivial. }
    apply Con in T. apply T. }
  intersect AnB R. rename x into NAnB. rename H into HNAnB.
  exists A, B, AnB, NA, NB, NAnNB, NAnB. repeat (split; try assumption).
  intros C. assert (J : In empty NAnB).
  { apply HNAnB. apply R. intros y Hy. apply HAnB in Hy as [Hy Hy'].
    apply HA in Hy as [Hy | Hy].
    - apply HB in Hy' as [Hy' | Hy'].
      + rewrite Hy'. apply HSE. trivial.
      + rewrite Hy'. apply HA. left. trivial.
    - rewrite Hy. apply HSE. trivial. }
  assert (K : Empty NAnNB).
  { intros y Cy. apply HNAnNB in Cy as [Cy Cy'].
    assert (T : forall z, In z A -> In y z). { apply HNA; assumption. }
    clear Cy. rename T into Cy.
    assert (T : forall z, In z B -> In y z). { apply HNB; assumption. }
    clear Cy'. rename T into Cy'.
    assert (T : In empty A). { apply HA. left. trivial. }
    assert (T' : In y empty). { apply Cy. assumption. }
    apply He in T'. assumption. }
  rewrite C in K. apply K in J. assumption.
Qed.
      

(** Exercise 28 : Simplify U{{3, 4}, {{3}, {4}}, {3, {4}}, {{3}, 4}}. *)

(** Solution : TODO *)

(** Exercise 29a : Simplify N{PPP{}, PP{}, P{}, {}}. *)

(** Solution : TODO *)

(** *Exercise 29b : Simplify N{PPP{{}}, PP{{}}m P{{}}}. *)

(** Solution : TODO *)

(** Exercise 30 : Let A = {{{}}, {{{}}}}. Evaluate: 
    a) PA = TODO
    b) UA = TODO
    c) PUA = TODO
    d) UPA = TODO *)

(** Exercise 31 : Let B = {{1, 2}, {2, 3}, {1, 3}, {{}}}. Evaluate:
    a) UB = TODO
    b) NB = TODO
    c) NUB = TODO
    d) UNB = TODO *)

(** Exercise 32 : Let S = {{a}, {a, b}}. Evaluate and simplify:
    a) UUS = TODO 
    b) NNS = TODO 
    c) NUS u (UUS \ UNS) = TODO *)

(** Exercise 33 : With S as in (32), evaluate U(US \ NS) assuming a <> b
    and then assuming a = b. *)

(** Solution : TODO *)

Theorem Exercise2_34 : forall E SE DESE S PS PPS PPPS,
  Empty E -> Singleton E SE -> Pair E SE DESE -> PowerSet S PS ->
  PowerSet PS PPS -> PowerSet PPS PPPS -> In DESE PPPS.
Proof.
  intros E SE DESE S PS PPS PPPS HE HSE HDESE HPS HPPS HPPPS.
  apply HPPPS. intros x Hx. apply HDESE in Hx. destruct Hx as [Hx | Hx].
  + rewrite Hx. apply HPPS. intros e C. apply HE in C.
    inversion C.
  + apply HPPS. intros y Hy. rewrite Hx in Hy.
    apply HSE in Hy. rewrite Hy. apply HPS. intros e He.
    apply HE in He. inversion He.
Qed.

Theorem Exercise2_35 : forall A B PA PB,
  PowerSet A PA -> PowerSet B PB -> PA = PB -> A = B.
Proof.
  intros A B PA PB HPA HPB Heq. apply Extensionality_Axiom. intros x. split; intros H.
  - rewrite <- Heq in HPB. apply HPB in H; try assumption.
    apply HPA. intros a. intros; assumption.
  - rewrite Heq in HPA. apply HPA in H; try assumption.
    apply HPB. intros a P; assumption.
Qed.

Theorem Exercise2_36a : forall A B AnB AmB AmAnB,
  BinaryIntersect A B AnB -> SetMinus A B AmB -> SetMinus A AnB AmAnB ->
  AmAnB = AmB.
Proof.
  intros A B AnB AmB AmAnB HAnB HAmB HAmAnB.
  apply Extensionality_Axiom. intros x. split; intros H.
  - apply HAmB. apply HAmAnB in H as [H I]. split; try assumption.
    intros C. apply I. apply HAnB. split; assumption.
  - apply HAmAnB. apply HAmB in H as [H I].
    split; try assumption. intros C. apply I.
    apply HAnB. assumption.
Qed.

Theorem Exercise2_36b : forall A B AmB AnB AmAmB,
  SetMinus A B AmB -> BinaryIntersect A B AnB -> SetMinus A AmB AmAmB ->
  AmAmB = AnB.
Proof.
  intros A B AmB AnB AmAmB HAmB HAnB HAmAmB.
  apply Extensionality_Axiom. intros x. split; intros H.
  - apply HAnB. apply HAmAmB in H as [H I].
    split; try assumption. assert (P : In x B \/ ~ In x B).
    { apply REM. } destruct P as [P | P].
    + assumption.
    + assert (Q : In x A /\ ~ In x B). { split; assumption. }
      apply HAmB in Q. apply I in Q. destruct Q.
  - apply HAmAmB. apply HAnB in H as [H I]. split; try assumption.
    intros C. apply HAmB in C as [C D]. apply D in I. assumption.
Qed.

Theorem Exercise2_37a : forall A B C AuB AuBmC AmC BmC AmCuBmC,
  BinaryUnion A B AuB -> SetMinus AuB C AuBmC -> SetMinus A C AmC ->
  SetMinus B C BmC -> BinaryUnion AmC BmC AmCuBmC -> AuBmC = AmCuBmC.
Proof.
  intros A B C AuB AuBmC AmC BmC AmCuBmC HAuB HAuBmC HAmC HBmC HAmCuBmC.
  apply Extensionality_Axiom. intros x. split; intros H.
  - apply HAmCuBmC. apply HAuBmC in H as [H I].
    apply HAuB in H as [H | H].
    + left. apply HAmC; split; assumption.
    + right. apply HBmC; split; assumption.
  - apply HAmCuBmC in H. apply HAuBmC. destruct H as [H | H].
    + apply HAmC in H as [H I]. split; try assumption.
      apply HAuB. left. assumption.
    + apply HBmC in H as [H I]. split; try assumption.
      apply HAuB. right. assumption.
Qed.

Theorem Exercise2_37b : forall A B C BmC AmBmC AmB AnC AmBuAnC,
  SetMinus B C BmC -> SetMinus A BmC AmBmC -> SetMinus A B AmB ->
  BinaryIntersect A C AnC -> BinaryUnion AmB AnC AmBuAnC ->
  AmBmC = AmBuAnC.
Proof.
  intros A B C BmC AmBmC AmB AnC AmBuAnC HBmC HAmBmC HAmB HAnC HAmBuAnC.
  apply Extensionality_Axiom. intros x. split; intros H.
  - apply HAmBuAnC. apply HAmBmC in H as [H I].
    assert (P : In x C \/ ~ In x C). { apply REM. }
    destruct P as [P | P].
    + right. apply HAnC. split; assumption.
    + left. apply HAmB. split; try assumption.
      intros Con. apply I. apply HBmC. split; assumption.
  - apply HAmBuAnC in H. apply HAmBmC. destruct H as [H | H].
    + apply HAmB in H as [H I]. split; try assumption.
      intros Con. apply I. apply HBmC in Con. apply Con.
    + apply HAnC in H as [H I]. split; try assumption.
      intros Con. apply HBmC in Con as [D E].
      apply E in I. assumption.
Qed.

Theorem Exercise2_37c : forall A B C AmB AmBmC BuC AmBuC,
  SetMinus A B AmB -> SetMinus AmB C AmBmC -> BinaryUnion B C BuC ->
  SetMinus A BuC AmBuC -> AmBmC = AmBuC.
Proof.
  intros A B C AmB AmBmC BuC AmBuC HAmB HAmBmC HBuC HAmBuC.
  apply Extensionality_Axiom. intros x. split; intros H.
  - apply HAmBmC in H as [H I]. apply HAmBuC.
    apply HAmB in H as [H J]. split; try assumption.
    intros Con. apply HBuC in Con. destruct Con as [Con | Con].
    + apply J. assumption.
    + apply I. assumption.
  - apply HAmBuC in H as [H I]. apply HAmBmC. split.
    + apply HAmB. split; try assumption. intros Con.
      apply I. apply HBuC. left. assumption.
    + intros Con. apply I. apply HBuC. right. assumption.
Qed.

Theorem Exercise2_38a : forall A B C AuB, BinaryUnion A B AuB ->
  ((Subset A C /\ Subset B C) <-> Subset AuB C).
Proof.
  intros A B C AuB HAuB. split; intros H.
  - destruct H as [H I]. intros x Hx.
    apply HAuB in Hx. destruct Hx as [Hx | Hx].
    + apply H. assumption.
    + apply I. assumption.
  - split.
    + intros x Hx. apply H. apply HAuB. left. assumption.
    + intros x Hx. apply H. apply HAuB. right. assumption.
Qed.

Theorem Exercise2_38b : forall A B C AnB, BinaryIntersect A B AnB ->
  ((Subset C A /\ Subset C B) <-> Subset C AnB).
Proof.
  intros A B C AnB HAnB. split; intros H.
  - destruct H as [H I]. intros x Hx. apply HAnB.
    split.
    + apply H, Hx.
    + apply I, Hx.
  - split.
    + intros x Hx. apply H in Hx. apply HAnB in Hx. apply Hx.
    + intros x Hx. apply H in Hx. apply HAnB in Hx. apply Hx.
Qed.