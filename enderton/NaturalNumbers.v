From Enderton Require Export RelationsFunctions.

(** This chapter focuses on embedding the natural numbers into set theory.
    We start with a few supporting definitions and a new axiom, then define the
    set omega of all natural numbers. We include a few basic properties of
    omega for future use.*)

Definition Succ (a aplus : set) : Prop :=
  exists Sa, Singleton a Sa /\ BinaryUnion a Sa aplus.

Theorem Succ_Exists : forall a, exists aplus, Succ a aplus.
Proof.
  intros a. singleton a. binary_union a x. exists x0.
  exists x. split; try assumption.
Qed.

Theorem Succ_Unique : forall a aplus aplus', Succ a aplus -> Succ a aplus' ->
  aplus = aplus'.
Proof.
  intros a aplus aplus' Haplus Haplus'. destruct Haplus as [Sa [HSa Haplus]].
  destruct Haplus' as [Sa' [HSa' Haplus']]. apply Extensionality_Axiom.
  intros x. split; intros H.
  - apply Haplus'. replace Sa' with Sa. apply Haplus. assumption.
    apply (Singleton_Unique a Sa Sa'); try assumption.
  - apply Haplus. replace Sa with Sa'. apply Haplus'. assumption.
    apply (Singleton_Unique a Sa' Sa); try assumption.
Qed.

Ltac succ n := destruct (Succ_Exists n).

Definition Inductive (A : set ) : Prop :=
  (exists empty, Empty empty /\ In empty A) /\
  forall a aplus, Succ a aplus -> In a A -> In aplus A.

Axiom Infinity_Axiom : exists A, Inductive A.

Definition NaturalNumber (x : set) : Prop :=
  forall A, Inductive A -> In x A.

Definition Nats (omga : set) : Prop :=
  forall x, In x omga <-> NaturalNumber x.

Theorem Enderton4A : exists omga, Nats omga.
Proof.
  destruct Infinity_Axiom as [A HA].
  build_set
    set
    (fun (t c x : set) => NaturalNumber x)
    A
    A.
  rename x into omga. rename H into Homga. exists omga.
  intros n. split; intros H.
  - apply Homga, H.
  - apply Homga. split; try assumption. apply H, HA.
Qed.

Theorem Nats_Unique : forall omga omga', Nats omga -> Nats omga' -> omga = omga'.
Proof.
  intros omga omga' H H'. apply Extensionality_Axiom. intros n. split; intros I.
  - apply H', H, I.
  - apply H, H', I.
Qed.

Ltac omga := destruct Enderton4A as [omga Homga].

Ltac zero := empty.

Theorem Enderton4B : forall omga, Nats omga -> Inductive omga /\
  forall A, Inductive A -> Subset omga A.
Proof.
  intros omga Homga. split.
  - split.
    + empty. exists x. split; try assumption. apply Homga.
      intros A HA. destruct HA as [HA HA']. destruct HA as [x' [Hx' HA]].
      replace x with x'; try assumption. apply Empty_Unique; assumption.
    + intros a a' Ha' Ha. apply Homga. apply Homga in Ha.
      intros A HA. destruct HA as [HA HA'].
      apply (HA' a a'); try assumption. apply Ha. split; assumption.
  - intros A HA n Hn. apply Homga; assumption.
Qed.

Theorem Induction_Principle_for_Omega : forall A omga, Nats omga ->
  Inductive A -> Subset A omga -> A = omga.
Proof.
  intros A omga Homga HA Hsub. apply SubsetSymmetric_iff_Equal.
  split; try assumption. apply Enderton4B; assumption.
Qed.

Lemma Zero_NaturalNumber : forall x, Empty x -> NaturalNumber x.
Proof.
  intros x Hx A HA. destruct HA as [[x' [Hx' HA]] _].
  replace x with x'; try assumption. apply Empty_Unique; try assumption.
Qed.

Lemma Succ_NaturalNumber : forall m n, NaturalNumber m -> Succ m n ->
  NaturalNumber n.
Proof.
  intros m n Hm Hn A [HA HA']. apply (HA' m n Hn). apply Hm. split; assumption.
Qed.

Lemma Succ_Inversion : forall m n p, Succ m p -> Succ n p -> m = n.
Proof.
  intros m n p Hp Hp'. destruct Hp as [Sm [HSm Hp]].
  destruct Hp' as [Sn [HSn Hp']].
Abort.

Theorem Enderton4C : forall x, NaturalNumber x -> ~ Empty x ->
  exists w, NaturalNumber w /\ Succ w x.
Proof.
  omga.
  build_set set
    (fun (t c x : set) => ~Empty x -> exists w, NaturalNumber w /\ Succ w x)
    omga omga.
  rename x into A. rename H into HA. intros n Hn.
  destruct (Enderton4B omga Homga) as [[He Hind] Hsub].
  apply HA. replace A with omga; try apply Homga; try assumption.
  symmetry. apply Induction_Principle_for_Omega; try assumption.
  - split.
    + empty. exists x. split; try assumption. apply HA. split.
      * apply Homga. apply Zero_NaturalNumber; try assumption.
      * intros C. apply C in H. destruct H.
    + intros a a' Ha' Ha. apply HA. split.
      * apply (Hind a a' Ha'). apply HA; assumption.
      * intros C. exists a. split; try assumption. apply Homga. apply HA, Ha.
  - intros a Ha. apply HA. assumption.
Qed.

(** Exercise 4-1 : Show that 1 <> 3. TODO *)

(** Next, we embed Peano's postulates in ZF[C]. Peano's postulates are a
    minimal axiomatization of the natural numbers which are provable in ZF[C].
    We will later use this result to prove familiar properites of the natural
    numbers with addition, multiplication, and exponentiation. *)

Definition Peano1 (N S e : set) : Prop :=
  forall ranS, Range S ranS -> ~ In e ranS.

Definition Peano2 (N S e : set) : Prop :=
  OneToOne S.

Definition Peano3 (N S e : set) : Prop :=
  forall A, Subset A N -> In e A ->
  (forall n Sn, FunVal S n Sn -> In n A -> In Sn A) -> A = N.

Definition PeanoSystem (P : set) : Prop :=
  exists N S NS e, OrdPair N S NS /\ OrdPair NS e P /\
  FuncFromInto S N N /\ In e N /\ Peano1 N S e /\ Peano2 N S e /\ Peano3 N S e.

Definition SuccessorFunc (sigma : set) : Prop :=
  forall nn', In nn' sigma <-> exists n n', OrdPair n n' nn' /\
  NaturalNumber n /\ Succ n n'.

Theorem SuccessorFunc_Exists : exists sigma, SuccessorFunc sigma.
Proof.
  omga. prod omga omga. rename x into omgaxomga. rename H into Homgaxomga.
  build_set
    set
    (fun (t c nm : set) => exists n m, OrdPair n m nm /\ NaturalNumber n /\ Succ n m)
    omga
    omgaxomga.
  rename x into sigma. rename H into Hsigma. exists sigma.
  intros nn'. split; intros H; try apply Hsigma, H.
  apply Hsigma. split; try assumption.
  apply Homgaxomga. destruct H as [n [n' [Hnn' [Hn Hn']]]].
  exists n, n'. repeat (split; try assumption).
  - apply Homga, Hn.
  - apply Homga. intros A [HA' HA]. apply (HA n n' Hn'). apply Homga.
    + apply Homga, Hn.
    + split; assumption.
Qed.

Theorem SuccessorFunc_Unique : forall sigma sigma',
  SuccessorFunc sigma -> SuccessorFunc sigma' -> sigma = sigma'.
Proof.
  intros sigma sigma' H H'. apply Extensionality_Axiom. intros x. split; intros I.
  - apply H', H, I.
  - apply H, H', I.
Qed.

Lemma SuccessorFunc_Into : forall sigma omga, SuccessorFunc sigma ->
  Nats omga -> FuncFromInto sigma omga omga.
Proof.
  intros sigma omga Hsigma Homga. split; try split.
  - intros mn Hmn. apply Hsigma in Hmn. destruct Hmn as [m [n [Hmn _]]].
    exists m, n. assumption.
  - intros m n p mn mp Hmn Hmp H I. apply Hsigma in H. apply Hsigma in I.
    destruct H as [m' [n' [Hmn' [_ Hn]]]].
    replace m' with m in *;
    try (apply (Enderton3A m n m' n' mn mn Hmn Hmn'); trivial).
    replace n' with n in *;
    try (apply (Enderton3A m n m n' mn mn Hmn Hmn'); trivial).
    clear m' n' Hmn'. destruct I as [m' [p' [Hmp' [_ Hp]]]].
    replace m' with m in *;
    try (apply (Enderton3A m p m' p' mp mp Hmp Hmp'); trivial).
    replace p' with p in *;
    try (apply (Enderton3A m p m p' mp mp Hmp Hmp'); trivial).
    clear m' p' Hmp'. apply (Succ_Unique m n p); assumption.
  - intros m. split; intros H.
    + succ m. rename x into m'. rename H0 into Hm'.
      ordpair m m'. rename x into mm'. rename H0 into Hmm'.
      exists m', mm'. split; try assumption. apply Hsigma.
      exists m, m'. repeat (split; try assumption). apply Homga, H.
    + destruct H as [m' [mm' [Hmm' H]]]. apply Hsigma in H.
      destruct H as [n [n' [Hnn' [Hn Hn']]]]. replace m with n.
      apply Homga, Hn. apply (Enderton3A n n' m m' mm' mm' Hnn' Hmm'). trivial.
  - range sigma. rename x into ransigma. rename H into Hransigma.
    exists ransigma. split; try assumption.
    intros n H. apply Homga. apply Hransigma in H.
    destruct H as [m [mn [Hmn H]]]. apply Hsigma in H.
    destruct H as [m' [n' [Hmn' [Hm Hn]]]]. replace n with n'.
    apply (Succ_NaturalNumber m' n'); try assumption.
    apply (Enderton3A m' n' m n mn mn Hmn' Hmn). trivial.
Qed.

Ltac sigma := destruct (SuccessorFunc_Exists) as [sigma Hsigma].

Definition PeanoSystem_of_NaturalNumbers (P : set) : Prop :=
  exists N S NS e, OrdPair N S NS /\ OrdPair NS e P /\
  Nats N /\ SuccessorFunc S /\ Empty e.

Theorem PeanoSystem_of_NaturalNumbers_Exists : exists P,
  PeanoSystem_of_NaturalNumbers P.
Proof.
  empty. rename x into e. rename H into He. omga. sigma.
  ordpair omga sigma. rename x into os. rename H into Hos.
  ordpair os e. rename x into P. rename H into HP. exists P.
  exists omga, sigma, os, e. repeat (split; try assumption).
Qed.

Theorem PeanoSystem_of_NaturalNumbers_Unique : forall P P',
  PeanoSystem_of_NaturalNumbers P -> PeanoSystem_of_NaturalNumbers P' -> P = P'.
Proof.
  intros P P' H H'. destruct H as [N [S [NS [e [HNS [HP [HN [HS He]]]]]]]].
  destruct H' as [N' [S' [NS' [e' [HNS' [HP' [HN' [HS' He']]]]]]]].
  apply (OrdPair_Unique NS e P P'); try assumption.
  replace NS with NS'. replace e with e'. assumption.
  - apply Empty_Unique; try assumption.
  - apply (OrdPair_Unique N S NS' NS); try assumption.
    replace N with N'. replace S with S'. assumption.
    + apply SuccessorFunc_Unique; assumption.
    + apply Nats_Unique; assumption.
Qed.

(** Theorem 4D states that the Peano System of Natural Numbers is, in fact,
    a Peano System. It is state here by Enderton, but the full proof requires
    some of the following results concerning transitive sets. For this reason,
    we will delary the theorem statement for now. *)

Definition TransitiveSet (A : set) : Prop :=
  forall a x, In a A -> In x a -> In x A.

Theorem Enderton4E : forall a a' Ua', Succ a a' ->
  Union a' Ua' -> TransitiveSet a -> Ua' = a.
Proof.
  intros a a' Ua' Ha' HUa' Ha.
  apply Extensionality_Axiom. intros x. split; intros H.
  - apply HUa' in H. destruct H as [y [H I]].
    destruct Ha' as [Sa [HSa Ha']]. apply Ha' in I. destruct I as [I | I].
    + apply (Ha y x); try assumption.
    + apply HSa in I. rewrite <- I. assumption.
  - apply HUa'. exists a. split; try assumption.
    destruct Ha' as [Sa [HSa Ha']]. apply Ha'.
    right. apply HSa. trivial.
Qed.

Theorem Enderton4F : forall n, NaturalNumber n -> TransitiveSet n.
Proof.
  omga. build_set set (fun (t c x : set) => TransitiveSet x) omga omga.
  rename x into A. rename H into HA.
  intros n Hn. apply HA. replace A with omga. apply Homga, Hn.
  symmetry. apply Induction_Principle_for_Omega; try assumption.
  - split.
    + empty. exists x. split; try assumption. apply HA. split.
      * apply Homga. apply (Zero_NaturalNumber x H).
      * intros z y Hz Hy. apply H in Hz. destruct Hz.
    + intros a a' Ha' Ha. apply HA. apply HA in Ha as [Ha Htrans]. split.
      * apply Homga in Ha. apply Homga. apply (Succ_NaturalNumber a a' Ha Ha').
      * intros y x Hy Hx. destruct Ha' as [Sa [HSa Ha']].
        apply Ha' in Hy. destruct Hy as [Hy | Hy].
        { apply Ha'. left. apply (Htrans y x Hy Hx). }
        { apply HSa in Hy. replace y with a in Hx. apply Ha'. left. assumption. }
  - intros a Ha. apply HA, Ha.
Qed.

Theorem Enderton4D : forall P, PeanoSystem_of_NaturalNumbers P -> PeanoSystem P.
Proof.
  intros P HP. destruct HP as [N [S [NS [e [HNS [HP [HN [HS He]]]]]]]].
  exists N, S, NS, e. split; try assumption. split; try assumption.
  split; try apply (SuccessorFunc_Into S N HS HN).
  split; try apply HN, (Zero_NaturalNumber e), He.
  split; try split.
  - intros ranS HranS C. apply HranS in C. destruct C as [d [de [Hde C]]].
    apply (He d). apply HS in C. destruct C as [d' [e' [Hde' [Hd' He']]]].
    replace d with d'. replace e with e'. destruct He' as [Sd [HSd He']].
    apply He'. right. apply HSd. trivial.
    + apply (Enderton3A d' e' d e de de Hde' Hde). trivial.
    + apply (Enderton3A d' e' d e de de Hde' Hde). trivial.
  - split; try apply (SuccessorFunc_Into S N HS HN).
    intros m n p mp np Hmp Hnp H I. apply HS in H. apply HS in I.
    destruct H as [m' [p' [Hmp' [Hm Hp]]]].
    assert (T : m = m' /\ p = p').
    { apply (Enderton3A m p m' p' mp mp Hmp Hmp'). trivial. }
    replace m' with m in *; replace p' with p in *; try apply T.
    clear m' p' T. destruct I as [n' [p' [Hnp' [Hn Hp']]]].
    assert (T : n = n' /\ p = p').
    { apply (Enderton3A n p n' p' np np Hnp Hnp'). trivial. }
    replace n' with n in *; replace p' with p in *; try apply T.
    clear n' p' T Hmp' Hnp'. union p. rename x into Up. rename H into HUp.
    transitivity Up.
    + symmetry. apply (Enderton4E m p Up Hp HUp).
      apply Enderton4F. assumption.
    + apply (Enderton4E n p Up Hp' HUp). apply Enderton4F. assumption.
  - intros A Hsub HeA Hind.
    apply Induction_Principle_for_Omega; try assumption. split.
    + exists e. split; assumption.
    + intros a a' Ha' Ha. apply (Hind a a'); try assumption.
      intros _ _. ordpair a a'. rename x into aa'. rename H into Haa'.
      exists aa'. split; try assumption. apply HS.
      exists a, a'. split; try assumption. split; try assumption.
      apply HN. apply Hsub. assumption.
Qed.

Theorem Enderton4G : forall omga, Nats omga -> TransitiveSet omga.
Proof.
  intros omga Homga n m Hn Hm.
  build_set set (fun (t c x : set) => Subset x t) omga omga.
  rename x into T. rename H into HT.
  assert (P : T = omga).
  { apply Induction_Principle_for_Omega; try assumption; try split.
    - empty. exists x. split; try assumption. apply HT. split.
      + apply Homga, Zero_NaturalNumber, H.
      + intros y Hy. apply H in Hy. destruct Hy.
    - intros a a' Ha' Ha. apply HT in Ha. destruct Ha as [Ha1 Ha2].
      apply HT. split.
      + apply Homga, (Succ_NaturalNumber a a'); try assumption.
        apply Homga, Ha1.
      + intros x Hx. destruct Ha' as [Sa [HSa Ha']].
        apply Ha' in Hx. destruct Hx as [Hx | Hx].
        * apply Ha2. assumption.
        * replace x with a; try assumption. symmetry. apply HSa. assumption.
    - intros x H. apply HT. assumption. }
  rewrite <- P in Hn. apply HT in Hn. destruct Hn as [Hn Hn'].
  apply Hn'. assumption.
Qed.

Theorem Exercise4_2 : forall a a', Succ a a' ->
  TransitiveSet a -> TransitiveSet a'.
Proof.
  intros a a' Ha' Ha. destruct Ha' as [Sa [HSa Ha']].
  intros y x Hy Hx. apply Ha' in Hy. destruct Hy as [Hy | Hy].
  - apply Ha'. left. apply (Ha y x); assumption.
  - apply Ha'. apply HSa in Hy. rewrite Hy in Hx. left. assumption.
Qed.

Theorem Exercise4_3a : forall a Pa, PowerSet a Pa ->
  TransitiveSet a -> TransitiveSet Pa.
Proof.
  intros a Pa HPa Ha. intros Y X HY HX. apply HPa in HY.
  apply HPa. intros x Hx. apply HY in HX.
  apply (Ha X x); assumption.
Qed.

Theorem Exercise4_3b : forall a Pa, PowerSet a Pa ->
  TransitiveSet Pa -> TransitiveSet a.
Proof.
  intros a Pa HPa H y x Hy Hx. assert (P : Subset y a).
  { apply HPa. singleton y. rename x0 into Sy. rename H0 into HSy.
    apply (H Sy y).
    - apply HPa. intros u Hu. apply HSy in Hu. replace u with y. assumption.
    - apply HSy. trivial. }
  apply P. assumption.
Qed.

Theorem Exercise4_4 : forall a Ua, Union a Ua ->
  TransitiveSet a -> TransitiveSet Ua.
Proof.
  intros a Ua HUa H y x Hy Hx. apply HUa. apply HUa in Hy.
  destruct Hy as [Y [Hy HY]]. exists y. split; try assumption.
  apply (H Y y); try assumption.
Qed.

Theorem Exercise4_5a : forall A UA, Union A UA ->
  (forall a, In a A -> TransitiveSet a) -> TransitiveSet UA.
Proof.
  intros A UA HUA HA. intros y x Hy Hx. apply HUA. apply HUA in Hy.
  destruct Hy as [Y [Hy HY]]. apply HA in HY as HY'.
  exists Y. split; try assumption. apply (HY' y x); try assumption.
Qed.

Theorem Exercise4_5b : forall A NA, ~Empty A -> Intersect A NA ->
  (forall a, In a A -> TransitiveSet a) -> TransitiveSet NA.
Proof.
  intros A NA Hne HNA HA y x Hy Hx. apply (HNA Hne).
  intros Y HY. assert (Hy' : forall z, In z A -> In y z).
  { apply (HNA Hne). assumption. }
  apply HA in HY as HY'. apply (HY' y x); try assumption.
  apply Hy'. assumption.
Qed.

Theorem Exercise4_6 : forall a a' Ua', Succ a a' -> Union a' Ua' ->
  a = Ua' -> TransitiveSet a.
Proof.
  intros a a' Ua' Ha' HUa' Heq y x Hy Hx. replace a with Ua'.
  apply HUa'. destruct Ha' as [Sa [HSa Ha']].
  exists y. split; try assumption.
  apply Ha'. left. assumption.
Qed.

(** What follows is arguably the most interesting result so far. If we recall
    to the beginning of the book the concept of proving sets to be
    well-defined, we can extend this notion to our Peano systems. Peano's
    postulates were intended to be an axiomatization of the natural numbers, 
    that is to say, they fully describe all the known/provable properties of
    the natural numbers, and they don't describe any other structure. We have
    already acheived the first part of the well-definedness proof; that there is
    a Peano system embedded in ZF[C]. This is Theorem 4D, that our definition
    for the natural numbers extendeds into a Peano system. Later, we will prove
    that many important theorems of Peano's postulates hold for our own
    construction of the natural numbers. Next, however, we need to show the
    second part of well-definedness, that every other Peano system besides our
    own cannonical example is isomorphic to our own, i.e. that our natural
    numbers are unique. This will require the Recursion Theorem, which is the
    main goal of the next stretch of definitions and theorems. The uniqueness
    result (isomorphism result) is a corollary of the Recursion Theorem on omega. *)

Definition RecursiveFunction (A a F h : set) : Prop :=
  exists omga zero, Nats omga /\ Empty zero /\ FuncFromInto h omga A /\
  FunVal h zero a /\ forall n n' hn hn' Fhn, In n omga -> Succ n n' ->
  FunVal h n hn -> FunVal h n' hn' -> FunVal F hn Fhn -> hn' = Fhn.

Lemma RecursiveFunction_Exists : forall A a F,
  In a A -> FuncFromInto F A A -> exists h, RecursiveFunction A a F h.
Proof.
  intros A a F Ha HFAA. omga.
  prod omga A. rename x into omgaxA. rename H into HomgaxA.
  powerset omgaxA. rename x into PomgaxA. rename H into HPomgaxA.
  build_set
    (prod (prod set set) (prod set set))
    (fun (t : (set * set) * (set * set)) (c v : set) => Func v /\
      exists domv ranv e, Domain v domv /\ Range v ranv /\ Empty e /\
      Subset domv (fst (fst t)) /\ Subset ranv (snd (fst t)) /\
      (In e domv -> FunVal v e (snd (snd t))) /\
      (forall n n' vn', In n (fst (fst t)) -> Succ n n' -> FunVal v n' vn' ->
      In n' (fst (fst t)) -> In n' domv -> In n domv /\ exists vn Fvn,
      FunVal v n vn /\ FunVal (fst (snd t)) vn Fvn /\ vn' = Fvn))
    ((omga, A), (F, a))
    PomgaxA.
  rename H into HH. rename x into H.
  union H. rename x into h. rename H0 into Hh.
  empty. rename x into o. rename H0 into Ho. exists h, omga, o.
  range h. rename x into ranh. rename H0 into Hranh.
  assert (P : Subset ranh A).
  { intros x Hx. apply Hranh in Hx. destruct Hx as [n [nx [Hnx Hx]]].
    apply Hh in Hx. destruct Hx as [v [I J]]. apply HH in J.
    destruct J as [J _]. apply HPomgaxA in J. apply J in I.
    apply HomgaxA in I. destruct I as [n' [x' [Hn [Hx Hnx']]]].
    replace x with x'; try assumption.
    apply (Enderton3A n' x' n x nx nx Hnx'); try trivial. }
  assert (Q : Func h). {
    split.
    - intros na I. apply Hh in I. destruct I as [v [I J]].
      apply HH in J. destruct J as [J _]. apply HPomgaxA in J.
      apply J in I. apply HomgaxA in I. destruct I as [x [y [_ [_ Hna]]]].
      exists x, y. assumption.
    - intros x y z xy xz Hxy Hxz I J. build_set 
        set
        (fun (t c x : set) => forall y z xy xz, OrdPair x y xy -> OrdPair x z xz ->
          In xy t -> In xz t -> y = z)
        h
        omga.
      rename x0 into S. rename H0 into HS. apply Hh in I as I'.
      destruct I' as [v [I1 I2]]. apply HH in I2 as [I2 _].
      apply HPomgaxA in I2. apply I2 in I1. apply HomgaxA in I1.
      destruct I1 as [x' [y' [Hx [Hy Hxy']]]]. assert (T : x = x' /\ y = y').
      { apply (Enderton3A x y x' y' xy xy Hxy Hxy'). trivial. }
      replace x' with x in *; replace y' with y in *; try apply T.
      clear x' y' T. replace omga with S in Hx. apply HS in Hx.
      destruct Hx as [_ Hx]. apply (Hx y z xy xz); try assumption.
      apply Induction_Principle_for_Omega; try assumption; try split.
      + exists o. split; try assumption. apply HS.
        split; try apply Homga, Zero_NaturalNumber, Ho.
        intros a' a'' oa' oa'' Hoa' Hoa'' K L.
        apply Hh in K. apply Hh in L. destruct K as [v1 [K1 K2]].
        destruct L as [v2 [L1 L2]]. apply HH in K2. apply HH in L2.
        destruct K2 as [_ [Hv1 [domv1 [_ [e1 [Hdomv1 [_ [He1 [_ [_ [K2 _]]]]]]]]]]].
        destruct L2 as [_ [Hv2 [domv2 [_ [e2 [Hdomv2 [_ [He2 [_ [_ [L2 _]]]]]]]]]]].
        transitivity a.
        * apply (FunVal_Unique v1 o a' a); try assumption.
          { exists domv1. split; try assumption. apply Hdomv1.
            exists a', oa'. split; try assumption. }
          { intros _ _. exists oa'. split; assumption. }
          { replace e1 with o in *; try (apply Empty_Unique; assumption).
            apply K2. apply Hdomv1. exists a', oa'. split; assumption. }
        * apply (FunVal_Unique v2 o a a''); try assumption.
          { exists domv2. split; try assumption. apply Hdomv2.
            exists a'', oa''. split; assumption. }
          { replace e2 with o in *; try (apply Empty_Unique; assumption).
            apply L2. apply Hdomv2. exists a'', oa''. split; assumption. }
          { intros _ _. exists oa''. split; try assumption. }
      + intros m n Hn Hm. apply HS. apply HS in Hm. destruct Hm as [Hm Hm'].
        apply Homga in Hm. split; try (apply Homga, (Succ_NaturalNumber m); assumption).
        intros hn hn' nhn nhn' Hnhn Hnhn' K L. apply Hh in K. apply Hh in L.
        destruct K as [v1 [K1 K2]]. destruct L as [v2 [L1 L2]].
        apply HH in K2 as K2'. apply HH in L2 as L2'.
        destruct K2' as [_ [Hv1 [domv1 [ranv1 [_ [Hdomv1 [Hranv1 [_ [_ [Hsub [_ K2']]]]]]]]]]].
        destruct L2' as [_ [Hv2 [domv2 [_ [_ [Hdomv2 [_ [_ [_ [_ [_ L2']]]]]]]]]]].
        apply Homga in Hm.
        destruct (K2' m n hn Hm Hn) as [Hmv1 [v1m [Fv1m [Hv1m [HFv1m K2'']]]]].
        { intros _ _. exists nhn. split; assumption. }
        { simpl. apply Homga. apply (Succ_NaturalNumber m n); try assumption.
          apply Homga. assumption. }
        { apply Hdomv1. exists hn, nhn. split; assumption. }
        destruct (L2' m n hn' Hm Hn) as [Hmv2 [v2m [Fv2m [Hv2m [HFv2m L2'']]]]].
        { intros _ _. exists nhn'. split; try assumption. }
        { simpl. apply Homga. apply (Succ_NaturalNumber m n); try assumption.
          apply Homga. assumption. }
        { apply Hdomv2. exists hn', nhn'. split; assumption. }
        rewrite K2''. rewrite L2''. destruct HFAA as [HF [HdomF _]].
        replace v2m with v1m in HFv2m. apply (FunVal_Unique F v1m); try assumption.
        exists A. split; try assumption. apply Hsub. apply Hranv1. exists m.
        apply Hv1m; try assumption. exists domv1. split; try assumption.
        destruct Hv1m as [mv1m [Hmv1m Hmv1m']]; try assumption.
        { exists domv1. split; try assumption. }
        destruct Hv2m as [mv2m [Hmv2m Hmv2m']]; try assumption.
        { exists domv2. split; try assumption. }
        apply (Hm' v1m v2m mv1m mv2m); try assumption.
        * apply Hh. exists v1. split; try assumption.
        * apply Hh. exists v2. split; assumption.
      + intros s. apply HS. }
    domain h. rename x into domh. rename H0 into Hdomh.
    assert (R : Domain h omga).
    { intros x. split.
      - build_set set (fun (t c x : set) => exists y xy, OrdPair x y xy /\ In xy t) h omga.
        rename x0 into S. rename H0 into HS. intros Hx. replace omga with S in Hx.
        apply HS. assumption.
        apply Induction_Principle_for_Omega; try assumption; try split.
        + exists o. split; try assumption. apply HS.
          split; try (apply Homga, (Zero_NaturalNumber); assumption).
          ordpair o a. rename x0 into oa. rename H0 into Hoa.
          exists a, oa. split; try assumption. apply Hh.
          singleton oa. rename x0 into v. rename H0 into Hv. exists v.
          split; try (apply Hv; trivial). apply HH. repeat split.
          * apply HPomgaxA. intros oa' Hoa'. apply HomgaxA.
            exists o, a. split; try (apply Homga, (Zero_NaturalNumber o Ho)).
            split; try assumption. apply Hv in Hoa'. rewrite Hoa'; assumption.
          * intros oa' Hoa'. exists o, a. replace oa' with oa; try assumption.
            apply Hv in Hoa'. symmetry. assumption.
          * intros x' y z xy xz Hxy Hxz I J. transitivity a.
            { apply (Enderton3A x' y o a oa oa); try  assumption; try trivial.
              apply Hv in I. rewrite <- I. assumption. }
            { apply (Enderton3A o a x' z oa oa); try assumption; try trivial.
              apply Hv in J. rewrite <- J. assumption. }
          * domain v. rename x0 into domv. rename H0 into Hdomv.
            range v. rename x0 into ranv. rename H0 into Hranv.
            exists domv, ranv, o. repeat (split; try assumption).
            { intros o' Ho'. apply Homga.
              replace o' with o; try (apply (Zero_NaturalNumber o Ho)).
              apply Hdomv in Ho'. destruct Ho' as [a' [oa' [Hoa' Ho']]].
              apply (Enderton3A o a o' a' oa oa Hoa); try trivial.
              apply Hv in Ho'. rewrite <- Ho'. assumption. }
            { intros a' Ha'. replace a' with a; try assumption.
              apply Hranv in Ha'. destruct Ha' as [o' [oa' [Hoa' Ho']]].
              apply (Enderton3A o a o' a' oa oa Hoa); try trivial.
              apply Hv in Ho'. rewrite <- Ho'. assumption. }
            { intros I. intros _ _. apply Hdomv in I. destruct I as [a' I].
              replace a with a'; try assumption. destruct I as [oa' [Hoa' I]].
              apply (Enderton3A o a' o a oa' oa' Hoa'); try trivial.
              apply Hv in I. rewrite I. assumption. }
            { destruct (Ho n). replace o with n'.
              destruct H1 as [Sn [HSn H1]]. apply H1. right. apply HSn. trivial.
              apply Hdomv in H4. destruct H4 as [a' [oa' [Hoa' H4]]].
              apply (Enderton3A n' a' o a oa' oa' Hoa'); try trivial.
              apply Hv in H4. rewrite H4. assumption. }
            { destruct (Ho n). replace o with n'.
              destruct H1 as [Sn [HSn H1]]. apply H1. right. apply HSn. trivial.
              apply Hdomv in H4. destruct H4 as [a' [oa' [Hoa' H4]]].
              apply (Enderton3A n' a' o a oa' oa' Hoa'); try trivial.
              apply Hv in H4. rewrite H4. assumption. }
        + intros n n' Hn' Hn. apply HS. apply HS in Hn.
          destruct Hn as [Hn [hn [nhn [Hnhn I]]]]. apply Homga in Hn.
          split; try (apply Homga, (Succ_NaturalNumber n n' Hn Hn')).
          destruct (FunVal_Exists F hn); try apply HFAA.
          { exists A. split. apply HFAA. apply P. apply Hranh.
            exists n, nhn. split; try assumption. }
          rename x0 into Fhn. rename H0 into HFhn. apply Hh in I.
          destruct I as [v [I Hv]]. apply HH in Hv.
          ordpair n' Fhn. rename x0 into n'hn'. rename H0 into Hn'hn'.
          exists Fhn, n'hn'. split; try assumption. apply Hh.
          singleton n'hn'. rename x0 into Sn'hn'. rename H0 into HSn'hn'.
          binary_union v Sn'hn'. rename x0 into v'. rename H0 into Hv'.
          exists v'. split. apply Hv'. right. apply HSn'hn'. trivial.
          assert (U : Func v'). {
            split.
            - intros xy Hxy. apply Hv' in Hxy. destruct Hxy as [Hxy | Hxy].
              { apply Hv. assumption. }
              { exists n', Fhn. apply HSn'hn' in Hxy. rewrite Hxy. assumption. }
            - intros s t u st su Hst Hsu J K. apply Hv' in J. apply Hv' in K.
              destruct J as [J | J]; destruct K as [K | K].
              { destruct Hv as [_ [[Hv1 Hv2] _]]. apply (Hv2 s t u st su); assumption. }
              { apply HSn'hn' in K. assert (T : n' = s /\ Fhn = u).
                { apply (Enderton3A n' Fhn s u su su); try trivial; try assumption.
                  rewrite K. assumption. }
                replace s with n' in *; replace u with Fhn in *; try apply T.
                clear T s u. replace su with n'hn' in *. clear K Hsu.
                destruct Hv as [Hv1 [Hfv [domv [ranv [e [Hdomv [Hranv [He [Hsuv' [Hsub [Hev Hv]]]]]]]]]]].
                destruct (Hv n n' t) as [H1 H2]; try assumption.
                - apply Homga. apply Hn.
                - intros _ _. exists st. split; assumption.
                - apply Homga. apply (Succ_NaturalNumber n); assumption.
                - apply Hdomv. exists t, st. split; try assumption.
                - destruct H2 as [vn [Fvn [Hvn [HFvn H2]]]].
                  transitivity Fvn; try assumption.
                  apply (FunVal_Unique F vn Fvn Fhn); try assumption; try apply HFAA.
                  exists A. split. try apply HFAA. apply Hsub. apply Hranv. exists n.
                  apply Hvn; try assumption. exists domv. split; try assumption.
                  replace vn with hn. assumption. destruct Q as [Q1 Q2].
                  destruct Hvn as [nvn [Hnvn Hnvn']]; try assumption.
                  { exists domv. split; try assumption. }
                  apply (Q2 n hn vn nhn nvn); try assumption.
                  + apply Hh. exists v. split; try assumption. apply HH.
                    repeat (split; try assumption). exists domv, ranv, e.
                    repeat (split; try assumption).
                  + apply Hh. exists v. split; try assumption. apply HH.
                    repeat (split; try assumption). exists domv, ranv, e.
                    repeat (split; try assumption). }
              { rename t into tmp. rename u into t. rename tmp into u.
                rename st into tmp. rename su into st. rename tmp into su.
                rename J into tmp. rename K into J. rename tmp into K.
                apply HSn'hn' in K. assert (T : n' = s /\ Fhn = u).
                { apply (Enderton3A n' Fhn s u su su); try trivial; try assumption.
                  rewrite K. assumption. }
                replace s with n' in *; replace u with Fhn in *; try apply T.
                clear T s u. replace su with n'hn' in *. clear K Hst.
                destruct Hv as [Hv1 [Hfv [domv [ranv [e [Hdomv [Hranv [He [Hsuv' [Hsub [Hev Hv]]]]]]]]]]].
                destruct (Hv n n' t) as [H1 H2]; try assumption.
                - apply Homga. apply Hn.
                - intros _ _. exists st. split; assumption.
                - apply Homga. apply (Succ_NaturalNumber n); assumption.
                - apply Hdomv. exists t, st. split; try assumption.
                - destruct H2 as [vn [Fvn [Hvn [HFvn H2]]]].
                  transitivity Fvn; try (symmetry; assumption).
                  apply (FunVal_Unique F vn Fhn Fvn); try assumption; try apply HFAA.
                  exists A. split. try apply HFAA. apply Hsub. apply Hranv. exists n.
                  apply Hvn; try assumption. exists domv. split; try assumption.
                  replace vn with hn. assumption. destruct Q as [Q1 Q2].
                  destruct Hvn as [nvn [Hnvn Hnvn']]; try assumption.
                  { exists domv. split; try assumption. }
                  apply (Q2 n hn vn nhn nvn); try assumption.
                  + apply Hh. exists v. split; try assumption. apply HH.
                    repeat (split; try assumption). exists domv, ranv, e.
                    repeat (split; try assumption).
                  + apply Hh. exists v. split; try assumption. apply HH.
                    repeat (split; try assumption). exists domv, ranv, e.
                    repeat (split; try assumption). }
              { apply HSn'hn' in J. apply HSn'hn' in K. replace st with n'hn' in *.
                replace su with n'hn' in *. clear J K. transitivity Fhn.
                - apply (Enderton3A s t n' Fhn n'hn' n'hn' Hst Hn'hn'). trivial.
                - apply (Enderton3A n' Fhn s u n'hn' n'hn' Hn'hn' Hsu). trivial. } }
          apply HH. repeat (split; try assumption).
          * apply HPomgaxA. intros xy Hxy. apply Hv' in Hxy. destruct Hxy as [Hxy | Hxy].
            { destruct Hv as [Hv _]. apply HPomgaxA in Hv. apply Hv. assumption. }
            { apply HomgaxA. exists n', Fhn. split; try split.
              - apply Homga. apply (Succ_NaturalNumber n n' Hn Hn').
              - destruct HFAA as [HF [HdomF [ranF [HranF Hsub]]]]. apply Hsub.
                apply HranF. exists hn. apply HFhn; try assumption.
                exists A. split; try assumption. apply P. apply Hranh.
                exists n, nhn. split; try assumption. apply Hh. exists v.
                split; try assumption. apply HH. assumption.
              - apply HSn'hn' in Hxy. rewrite Hxy. assumption. }
          * domain v'. rename x0 into domv'. rename H0 into Hdomv'.
            range v'. rename x0 into ranv'. rename H0 into Hranv'.
            destruct Hv as [HvP [Hfv [domv [ranv [e [Hdomv [Hranv [He [Hsubd [Hsubr [Hv1 Hv2]]]]]]]]]]].
            exists domv', ranv', o. repeat (split; try assumption).
            { intros m Hm. simpl. apply Hdomv' in Hm.
              destruct Hm as [vm [mvm [Hmvm Hmvm']]]. apply Hv' in Hmvm'.
              destruct Hmvm' as [Hmvm' | Hmvm'].
              - apply Hsubd. apply Hdomv. exists vm, mvm. split; assumption.
              - apply HSn'hn' in Hmvm'. replace m with n'.
                + apply Homga. apply (Succ_NaturalNumber n n'); try assumption.
                + apply (Enderton3A n' Fhn m vm n'hn' n'hn' Hn'hn').
                  rewrite <- Hmvm'; try assumption. trivial. }
            { intros vm Hvm. simpl. apply Hranv' in Hvm.
              destruct Hvm as [m [mvm [Hmvm Hvm]]]. apply Hv' in Hvm.
              destruct Hvm as [Hvm | Hvm].
              - apply Hsubr. apply Hranv. exists m, mvm. split; assumption.
              - apply HSn'hn' in Hvm. replace mvm with n'hn' in *.
                replace vm with Fhn. destruct HFAA as [HF [HdomF [ranF [HranF Hsub]]]].
                apply Hsub. apply HranF. exists hn. apply HFhn; try assumption.
                exists A. split; try assumption. apply P. apply Hranh.
                exists n, nhn. split; try assumption. apply Hh.
                exists v. split; try assumption. apply HH. repeat (split; try assumption).
                exists domv, ranv, e. repeat (split; try assumption).
                apply (Enderton3A n' Fhn m vm n'hn' n'hn'); try assumption. }
            { intros C. apply Hdomv' in C. destruct C as [a' [oa' [Hoa' C]]].
              apply Hv' in C. destruct C as [C | C].
              - intros _ _. exists oa'. split.
                + replace a with a'; try assumption. apply (FunVal_Unique v o a' a).
                  assumption. exists domv. split; try assumption.
                  apply Hdomv. exists a', oa'. split; try assumption.
                  intros _ _. exists oa'. split; try assumption.
                  replace o with e in *; try apply Hv1, Hdomv.
                  exists a', oa'. split; try assumption.
                  apply Empty_Unique; assumption.
                + apply Hv'. left. trivial.
              - intros _ _. apply HSn'hn' in C. replace oa' with n'hn' in *.
                clear C. destruct (Ho n). replace o with n'.
                + destruct Hn' as [Sn [HSn Hn']]. apply Hn'. right.
                  apply HSn. trivial.
                + apply (Enderton3A n' Fhn o a' n'hn' n'hn'); try assumption. trivial. }
            { simpl in *. rename n0 into m. rename n'0 into m'. rename vn' into vm'.
              apply Hdomv'. destruct H2 as [m'vm' [Hm'vm' H2]]; try assumption.
              exists domv'. split; try assumption.
              apply Hv' in H2. destruct H2 as [H2 | H2].
              - destruct (Hv2 m m' vm') as [Hv2' _]; try assumption.
                + intros _ _. exists m'vm'. split; try assumption.
                + apply Hdomv. exists vm', m'vm'. split; assumption.
                + apply Hdomv in Hv2'. destruct Hv2' as [vm [mvm [Hmvm Hv2']]].
                  exists vm, mvm. split; try assumption. apply Hv'. left. assumption.
              - exists hn, nhn. split.
                + replace m with n. assumption. apply HSn'hn' in H2.
                  replace m'vm' with n'hn' in *. clear H2.
                  replace m' with n' in *;
                  try (apply (Enderton3A n' Fhn m' vm' n'hn' n'hn' Hn'hn' Hm'vm'); trivial).
                  union n'. transitivity x0.
                  * symmetry. apply (Enderton4E n n'); try assumption.
                    apply (Enderton4F). assumption.
                  * apply (Enderton4E m n'); try assumption.
                    apply Enderton4F. apply Homga. assumption.
                + apply Hv'. left. assumption. }
            { simpl in *. rename n0 into m. rename n'0 into m'. rename vn' into vm'.
              destruct H2 as [m'vm' [Hm'vm' H2]]; try assumption.
              exists domv'. split; try assumption.
              apply Hv' in H2. destruct H2 as [H2 | H2].
              - destruct (Hv2 m m' vm') as [Y Hv2']; try assumption.
                + intros _ _. exists m'vm'. split; try assumption.
                + apply Hdomv. exists vm', m'vm'. split; assumption.
                + destruct Hv2' as [vm [Fvm [Hvm [HFvm Hv2']]]]. 
                  exists vm, Fvm. repeat (split; try assumption).
                  intros _ _. destruct Hvm as [mvm [Hmvm Hmvm']]; try assumption.
                  exists domv. split; try assumption.
                  exists mvm. split; try assumption. apply Hv'. left. assumption.
              - exists hn, Fhn. replace m with n in *. split; try split.
                + intros _ _. exists nhn. split; try assumption.
                  apply Hv'. left. assumption.
                + assumption.
                + apply (Enderton3A m' vm' n' Fhn m'vm' n'hn' Hm'vm' Hn'hn').
                  apply HSn'hn' in H2. assumption.
                + union n'. transitivity x0.
                  * symmetry. apply (Enderton4E n n'); try assumption.
                    apply (Enderton4F). assumption.
                  * apply (Enderton4E m n'); try assumption.
                    replace n' with m'; try assumption.
                    apply (Enderton3A m' vm' n' Fhn m'vm' n'hn' Hm'vm' Hn'hn').
                    apply HSn'hn' in H2. assumption.
                    apply (Enderton4F). apply Homga. assumption. }
        + intros s Hs. apply HS. assumption.
      - intros I. destruct I as [y [xy [Hxy I]]].
        apply Hh in I. destruct I as [v [I J]].
        apply HH in J. destruct J as [J _].
        apply HPomgaxA in J. apply J in I. apply HomgaxA in I.
        destruct I as [x' [y' [Hx [Hy Hxy']]]]. replace x with x'; try assumption.
        apply (Enderton3A x' y' x y xy xy Hxy' Hxy). trivial. }
    repeat (split; try assumption).
  - exists ranh. split; assumption.
  - intros _ [domh' [Hdomh' I]]. apply Hdomh' in I.
    destruct I as [a' [oa' [Hoa' I]]]. exists oa'. split; try assumption.
    apply Hh in I. destruct I as [v [I J]]. apply HH in J.
    destruct J as [_ [Hfv [domv [_ [e [Hdomv [_ [He [_ [_ [Hv _]]]]]]]]]]].
    assert (T : o = e). { apply Empty_Unique; assumption. }
    replace o with e in *. clear T o Ho.
    assert (T : In e domv).
    { apply Hdomv. exists a', oa'. split; try assumption. }
    apply Hv in T. simpl in *. destruct T as [ea [Hea Hea']]; try assumption.
    exists domv. split; try assumption. apply Hdomv.
    exists a', oa'. split; try assumption. replace a with a'. assumption.
    destruct Hfv as [_ Hfv]. apply (Hfv e a' a oa' ea); try assumption.
  - intros m n hm hn Fhm Hm Hn Hhm Hhn HFhm.
    destruct Hhn as [nhn [Hnhn Hnhn']]; try assumption.
    exists omga. split; try assumption. apply Homga. apply Homga in Hm.
    apply (Succ_NaturalNumber m n); try assumption.
    apply Hh in Hnhn'. destruct Hnhn' as [v [I J]]. apply HH in J as J'.
    destruct J' as [_ [Hfv [domv [_ [_ [Hdomv [_ [_ [_ [_ [_ Hv]]]]]]]]]]].
    destruct (Hv m n hn) as [J' [vm [Fvm [Hvm [HFvm Hv']]]]]; try assumption.
    + intros _ _. exists nhn. split; try assumption.
    + simpl. apply Homga. apply Homga in Hm. apply (Succ_NaturalNumber m n).
      assumption. assumption.
    + apply Hdomv. exists hn, nhn. split; assumption.
    + simpl in *. transitivity Fvm; try assumption.
      destruct Hvm as [mvm [Hmvm Hmvm']]; try assumption.
      { exists domv. split; try assumption. }
      destruct Hhm as [mhm [Hmhm Hmhm']]; try assumption.
      { exists omga. split; assumption. }
      destruct HFAA as [[HF HF'] [HdomF [ranF [HranF Hsub]]]].
      destruct HFvm as [vmFvm [H0 H1]]; try (split; assumption).
      { exists A. split; try assumption. apply P. apply Hranh.
        exists m, mvm. split; try assumption. apply Hh.
        exists v. split; try assumption. }
      destruct HFhm as [hmFhm [H2 H3]]; try (split; assumption).
      { exists A. split; try assumption. apply P. apply Hranh.
        exists m, mhm. split; try assumption. }
      apply (HF' hm Fvm Fhm vmFvm hmFhm); try assumption.
      replace hm with vm; try assumption.
      destruct Q as [Q1 Q2]. apply (Q2 m vm hm mvm mhm); try assumption.
      apply Hh. exists v. split; try assumption.
Qed.

Lemma RecursiveFunction_Unique : forall A a F h h' , In a A ->
  FuncFromInto F A A -> RecursiveFunction A a F h ->
  RecursiveFunction A a F h' -> h = h'.
Proof.
  intros A a F h h' Ha [Hf [Hdomf [ranf [Hranf Hsub]]]] Hh Hh'.
  omga. build_set
    (prod set set )
    (fun (t : set * set) (c x : set) => forall b c, FunVal (fst t) x b ->
      FunVal (snd t) x c -> b = c)
    (h, h')
    omga.
  destruct Hh as [omga' [o [Homga' [Ho [HhomgaA [Hho Hhn']]]]]].
  replace omga' with omga in *; try (apply Nats_Unique; assumption).
  clear omga' Homga'.
  destruct Hh' as [omga' [o' [Homga' [Ho' [Hh'omgaA [Hh'o Hh'n']]]]]].
  replace omga' with omga in *; try (apply Nats_Unique; assumption).
  replace o' with o in *; try (apply Empty_Unique; assumption).
  rename x into S. rename H into HS. assert (P : S = omga).
  { apply Induction_Principle_for_Omega; try assumption; try split.
    - empty. exists x. split; try assumption. apply HS.
      split; try (apply Homga, (Zero_NaturalNumber), H).
      intros b c Hb Hc. simpl in *. transitivity a.
      + apply (FunVal_Unique h x b a); try assumption; try apply HhomgaA.
        { exists omga. split.
          - try apply HhomgaA.
          - apply Homga, Zero_NaturalNumber, H. }
        replace x with o; try assumption. apply (Empty_Unique); assumption.
      + apply (FunVal_Unique h' x a c); try assumption; try apply Hh'omgaA.
        { exists omga. split.
          - apply Hh'omgaA.
          - apply Homga, Zero_NaturalNumber, H. }
        replace x with o; try assumption. apply (Empty_Unique); assumption.
    - intros m n Hn Hm. apply HS. apply HS in Hm. destruct Hm as [Hm Hm'].
      apply Homga in Hm.
      split; try (apply Homga, (Succ_NaturalNumber m n); assumption).
      intros b c Hb Hc. simpl in *.
      assert (H0 : exists domh, Domain h domh /\ In m domh).
      { exists omga. split; try (apply Homga; assumption). apply HhomgaA. }
      assert (H1 : exists domh', Domain h' domh' /\ In m domh').
      { exists omga. split; try (apply Homga; assumption). apply Hh'omgaA. }
      assert (H0' : Func h). { apply HhomgaA. }
      assert (H1' : Func h'). { apply Hh'omgaA. }
      funval H0' H0 h m. rename x into hm. rename H into Hhm.
      funval H1' H1 h' m. rename x into h'm. rename H into Hh'm.
      assert (P : hm = h'm). { apply Hm'; assumption. }
      replace h'm with hm in *. clear h'm P.
      assert (H3 : exists domF, Domain F domF /\ In hm domF).
      { exists A. split; try assumption.
        destruct HhomgaA as [_ [_ [ranh [Hranh Hsub']]]].
        apply Hsub'. apply Hranh. exists m. apply Hhm; try assumption. }
      funval Hf H3 F hm. rename x into Fhm. rename H into HFhm.
      transitivity Fhm.
      + apply (Hhn' m n hm b Fhm); try assumption. apply Homga. assumption.
      + symmetry. apply (Hh'n' m n hm c Fhm); try assumption. apply Homga. assumption.
    - intros s Hs. apply HS, Hs. }
  apply Extensionality_Axiom. intros xy. split; intros H.
  - destruct HhomgaA as [[Hhr Hhf] HhomgaA].
    apply Hhr in H as I. destruct I as [x [y Hxy]].
    assert (T : In x omga).
    { destruct HhomgaA as [Hdomh _]. apply Hdomh. exists y, xy.
      split; assumption. }
    assert (H0 : Func h'). { apply Hh'omgaA. }
    assert (H1 : exists domh', Domain h' domh' /\ In x domh').
    { exists omga. split. apply Hh'omgaA. assumption. }
    funval H0 H1 h' x. rename x0 into h'x. rename H2 into Hh'x.
    rewrite <- P in T. apply HS in T. destruct T as [T1 T2].
    destruct (Hh'x H0 H1) as [xy' [Hxy' Hxy'']].
    replace xy with xy'; try assumption.
    apply (OrdPair_Unique x y xy' xy); try assumption.
    replace y with h'x; try assumption. symmetry. apply T2.
    + intros _ _. exists xy. split; try assumption.
    + assumption.
  - destruct Hh'omgaA as [[Hh'r Hh'f] Hh'omgaA].
    apply Hh'r in H as I. destruct I as [x [y Hxy]].
    assert (T : In x omga).
    { destruct Hh'omgaA as [Hdomh' _]. apply Hdomh'. exists y, xy.
      split; assumption. }
    assert (H0 : Func h). { apply HhomgaA. }
    assert (H1 : exists domh, Domain h domh /\ In x domh).
    { exists omga. split. apply HhomgaA. assumption. }
    funval H0 H1 h x. rename x0 into hx. rename H2 into Hhx.
    rewrite <- P in T. apply HS in T. destruct T as [T1 T2].
    destruct (Hhx H0 H1) as [xy' [Hxy' Hxy'']].
    replace xy with xy'; try assumption.
    apply (OrdPair_Unique x y xy' xy); try assumption.
    replace y with hx; try assumption. apply T2.
    + assumption.
    + intros _ _. exists xy. split; assumption.
Qed.

Ltac recursion A a F Ha HFAA := destruct (RecursiveFunction_Exists A a F Ha HFAA).

Theorem Recursion_Theorem_on_Omega : forall A a F, In a A -> FuncFromInto F A A ->
  exists h, RecursiveFunction A a F h /\ forall h', RecursiveFunction A a F h' ->
  h = h'.
Proof.
  intros A a F Ha HFAA. recursion A a F Ha HFAA. exists x.
  split; try assumption. intros h' H'.
  apply (RecursiveFunction_Unique A a F x h' Ha HFAA H H').
Qed.

Corollary Enderton4H : forall N S e NS P omga sigma empty os Q,
  OrdPair N S NS -> OrdPair NS e P -> PeanoSystem P ->
  OrdPair omga sigma os -> OrdPair os empty Q -> PeanoSystem_of_NaturalNumbers Q ->
  exists h, FuncFromOnto h omga N /\ OneToOne h /\
  (forall n sn hsn hn Shn, In n omga -> FunVal sigma n sn -> FunVal h sn hsn ->
  FunVal h n hn -> FunVal S hn Shn -> hsn = Shn) /\
  forall ho, FunVal h empty ho -> ho = e.
Proof.
  intros N S e NS PN omga sigma empty os Pw HNS HNSe HPN Hos Hose HPw.
  destruct HPw as [omga' [sigma' [os' [empty' [Hos' [Hose' [Homga [Hsigma He]]]]]]]].
  assert (T : os = os' /\ empty = empty').
  { apply (Enderton3A os empty os' empty' Pw Pw Hose Hose'). trivial. }
  replace os' with os in *; replace empty' with empty in *; try apply T.
  clear os' empty' T. rename empty into o. rename He into Ho.
  assert (T : omga = omga' /\ sigma = sigma').
  { apply (Enderton3A omga sigma omga' sigma' os os Hos Hos'). trivial. }
  replace omga' with omga in *; replace sigma' with sigma in *; try apply T.
  clear omga' sigma' Hos' T Hose'.
  destruct HPN as [N' [S' [NS' [e' [HNS' [HNSe' [HS [He [HP1 [HP2 HP3]]]]]]]]]].
  assert (T : NS = NS' /\ e = e').
  { apply (Enderton3A NS e NS' e' PN PN HNSe HNSe'). trivial. }
  replace NS' with NS in *; replace e' with e in *; try apply T.
  clear NS' e' T. assert (T : N = N' /\ S = S').
  { apply (Enderton3A N S N' S' NS NS HNS HNS'). trivial. }
  replace N' with N in *; replace S' with S in *; try apply T.
  clear N' S' HNS' T HNSe'. recursion N e S He HS.
  rename x into h. rename H into Hh. exists h.
  destruct Hh as [omga' [o' [Homga' [Ho' [HhomgaN [Hho Hhsn]]]]]].
  assert (T : o = o'). { apply Empty_Unique; try assumption. }
  replace o' with o in *; try apply T. clear o' T Ho'.
  assert (T : omga = omga'). { apply Nats_Unique; try assumption. }
  replace omga' with omga in *; try apply T. clear omga' T Homga'.
  destruct HhomgaN as [Hfh [Hdomh [ranh [Hranh Hsub]]]].
  assert (P : ranh = N).
  { apply (HP3 ranh Hsub). unfold Peano3 in HP3.
    - apply Hranh. exists o. apply Hho; try assumption.
      exists omga. split; try assumption.
      apply Homga, Zero_NaturalNumber, Ho.
    - intros hn Shn HShn Hhn. apply Hranh in Hhn.
      destruct Hhn as [n [nhn [Hnhn Hnhn']]].
      succ n. rename x into n'. rename H into Hn'.
      assert (T : exists domh, Domain h domh /\ In n' domh).
      { exists omga. split; try assumption. apply Homga.
        apply (Succ_NaturalNumber n n'); try assumption.
        apply Homga. apply Hdomh. exists hn, nhn. split; assumption. }
      funval Hfh T h n'. rename x into hn'. rename H into Hhn'.
      replace Shn with hn'.
      + apply Hranh. exists n'. apply Hhn'; assumption.
      + apply (Hhsn n n' hn hn' Shn); try assumption.
        * apply Hdomh. exists hn, nhn. split; assumption.
        * intros _ _. exists nhn. split; assumption. }
  repeat (split; try assumption).
  - intros H. rewrite <- P in H. apply Hranh in H. assumption.
  - intros H. apply Hsub. apply Hranh. assumption.
  - build_set set (fun (h c n : set) => forall m a na ma, OrdPair n a na ->
      OrdPair m a ma -> In na h -> In ma h -> n = m) h omga.
    rename x into T. rename H into HT. intros n m a na ma Hna Hma I J.
    assert (Q : In n omga).
    { apply Hdomh. exists a, na. split; assumption. }
    replace omga with T in Q. apply HT in Q. destruct Q as [_ Q].
    apply (Q m a na ma); try assumption.
    clear n m a na ma Hna Hma I J Q. 
    apply Induction_Principle_for_Omega; try assumption; try split.
    + exists o. split; try assumption. apply HT.
      split; try (apply Homga, (Zero_NaturalNumber), Ho).
      intros m' hm' ohm' m'hm' Hohm' Hm'ho H I.
      assert (Q : o = m' \/ o <> m'). { apply REM. }
      destruct Q as [Q | Q]; try trivial.
      destruct (Enderton4C m') as [m [Hm Hm']].
      { apply Homga, Hdomh. exists hm', m'hm'. split; assumption. }
      { intros c. apply Q. apply Empty_Unique; assumption. }
      range S. rename x into ranS. rename H0 into HranS.
      destruct (HP1 ranS HranS). apply HranS. apply Homga in Hm.
      assert (H0 : exists domh, Domain h domh /\ In m domh).
      { exists omga. split; try assumption. }
      funval Hfh H0 h m. rename x into hm. rename H1 into Hhm.
      exists hm. destruct (FunVal_Exists S hm); try apply HS.
      { exists N. split. apply HS. apply Hsub. apply Hranh. exists m.
        apply Hhm; try assumption. }
      rename x into Shm. rename H1 into HShm.
      replace e with Shm. apply HShm; try apply HS.
      { exists N. split. apply HS. apply Hsub. apply Hranh. exists m.
        apply Hhm; assumption. }
      transitivity hm'.
      * symmetry. apply (Hhsn m m' hm hm' Shm Hm Hm'); try assumption.
        intros _ _. exists m'hm'. split; assumption.
      * apply (FunVal_Unique h o hm' e); try assumption.
        { exists omga. split; try assumption. apply Homga, Zero_NaturalNumber, Ho. }
        { intros _ _. exists ohm'. split; try assumption. }
    + intros n n' Hn' Hn. apply HT. apply HT in Hn.
      destruct Hn as [Hn1 Hn2]. apply Homga in Hn1.
      split; try (apply Homga, (Succ_NaturalNumber n n'); assumption).
      intros m' hn' n'hn' m'hn' Hn'hn' Hm'hn' H I.
      destruct (Enderton4C m') as [m [Hm Hm']].
      { apply Homga, Hdomh. exists hn', m'hn'. split; assumption. }
      { intros C. range S. rename x into ranS. rename H0 into HranS.
        destruct (HP1 ranS HranS). apply HranS. apply Homga in Hn1.
        assert (H0 : exists domh, Domain h domh /\ In n domh).
        { exists omga. split; try assumption. }
        funval Hfh H0 h n. rename x into hn. rename H1 into Hhn.
        exists hn. destruct (FunVal_Exists S hn); try apply HS.
        { exists N. split. apply HS. apply Hsub. apply Hranh. exists n.
          apply Hhn; try assumption. }
        rename x into Shn. rename H1 into HShn.
        replace e with Shn. apply HShn; try apply HS.
        { exists N. split. apply HS. apply Hsub. apply Hranh. exists n.
          apply Hhn; assumption. }
        transitivity hn'.
        * symmetry. apply (Hhsn n n' hn hn' Shn Hn1 Hn'); try assumption.
          intros _ _. exists n'hn'. split; assumption.
        * apply (FunVal_Unique h m' hn' e); try assumption.
          { exists omga. split; try assumption. apply Homga, Zero_NaturalNumber, C. }
          { intros _ _. exists m'hn'. split; try assumption. }
          replace m' with o; try assumption. apply Empty_Unique; assumption. }
      assert (H0 : exists domh, Domain h domh /\ In n domh).
      { exists omga. split; try assumption. apply Homga; assumption. }
      assert (H1 : exists domh, Domain h domh /\ In m domh).
      { exists omga. split; try assumption. apply Homga; assumption. }
      funval Hfh H0 h n. rename x into hn. rename H2 into Hhn.
      funval Hfh H1 h m. rename x into hm. rename H2 into Hhm.
      assert (H2 : exists domS, Domain S domS /\ In hn domS).
      { exists N. split. apply HS. apply Hsub. apply Hranh.
        exists n. apply Hhn; assumption. }
      assert (H3 : exists domS, Domain S domS /\ In hm domS).
      { exists N. split. apply HS. apply Hsub. apply Hranh.
        exists m. apply Hhm; assumption. }
      destruct HS as [HfS HS].
      funval HfS H2 S hn. rename x into Shn. rename H4 into HShn.
      funval HfS H3 S hm. rename x into Shm. rename H4 into HShm.
      apply (Succ_Unique m); try assumption. replace m with n; try assumption.
      assert (Q : Shn = Shm).
      { transitivity hn'.
        - symmetry. apply (Hhsn n n' hn hn' Shn); try assumption.
          + apply Homga; assumption.
          + intros _ _. exists n'hn'. split; assumption.
        - apply (Hhsn m m' hm hn' Shm); try assumption.
          + apply Homga; assumption.
          + intros _ _. exists m'hn'. split; assumption. }
      assert (R : hn = hm).
      { destruct HP2 as [_ HP2].
        destruct HShn as [hnShn [HhnShn HhnShn']]; try assumption.
        destruct HShm as [hmShm [HhmShm HhmShm']]; try assumption.
        ordpair hm Shn. rename x into hmShn. rename H into HhmShn.
        apply (HP2 hn hm Shn hnShn hmShn); try assumption.
        replace hmShn with hmShm; try assumption.
        apply (OrdPair_Unique hm Shm); try assumption. rewrite <- Q. assumption. }
      destruct Hhn as [nhn [Hnhn Hnhn']]; try assumption.
      destruct Hhm as [mhm [Hmhm Hmhm']]; try assumption.
      ordpair m hn. rename x into mhn. rename H4 into Hmhn.
      apply (Hn2 m hn nhn mhn); try assumption.
      replace mhn with mhm; try assumption.
      apply (OrdPair_Unique m hm mhm mhn); try assumption.
      rewrite <- R. assumption.
    + intros t Ht. apply HT in Ht as [Ht _]. assumption.
  - intros n sn hsn hn Shn Hsn Hhsn' Hhn HShn.
    apply (Hhsn n sn hn hsn Shn); try assumption.
    destruct Hhsn' as [nsn [Hnsn Hnsn']].
    + destruct (SuccessorFunc_Into sigma omga); try assumption.
    + exists omga. split; try assumption.
      destruct (SuccessorFunc_Into sigma omga) as [_ [H0 _]]; try assumption.
    + apply Hsigma in Hnsn'. destruct Hnsn' as [n' [sn' [Hnsn' [Hn Hn']]]].
      assert (T : n' = n /\ sn' = sn).
      { apply (Enderton3A n' sn' n sn nsn nsn Hnsn' Hnsn). trivial. }
      replace n with n'; replace sn with sn'; try apply T. assumption.
  - intros ho Hho'. apply (FunVal_Unique h o ho e); try assumption.
    exists omga. split; try assumption. apply Homga.
    apply Zero_NaturalNumber. apply Ho.
Qed.

(** Exercise 4 - 7 : Complete part of the proof of the recusion theorem. *)

Theorem Exercise4_8 : forall f A c ranf Amranf h, FuncFromInto f A A ->
  OneToOne f -> Range f ranf -> SetMinus A ranf Amranf -> In c Amranf ->
  RecursiveFunction A c f h -> OneToOne h.
Proof.
  intros f A c ranf Amranf h HfAA Hf Hranf HAmranf Hc Hh.
  destruct Hh as [omga [o [Homga [Ho [HhomgaA [Hho Hhn']]]]]].
  split; try apply HhomgaA. intros m n hm mhm nhm Hmhm Hnhm H I.
  build_set set (fun (h c m : set) => forall n hm mhm nhm, OrdPair m hm mhm ->
    OrdPair n hm nhm -> In mhm h -> In nhm h -> m = n) h omga.
  rename x into S. rename H0 into HS. assert (P : In m omga).
  { apply HhomgaA. exists hm, mhm. split; assumption. }
  replace omga with S in P. apply HS in P. destruct P as [_ P].
  apply (P n hm mhm nhm); try assumption.
  clear Hnhm Hmhm n hm mhm nhm H I P m.
  apply Induction_Principle_for_Omega; try assumption; try split;
  try (intros s Hs; apply HS in Hs; destruct Hs as [Hs _]; assumption).
  - exists o. split; try assumption. apply HS. split.
    + apply Homga, Zero_NaturalNumber. assumption.
    + intros n' hm mhm n'hm Hmhm Hn'hm H I.
      assert (Q : o = n' \/ o <> n'). { apply REM. }
      destruct Q as [Q | Q]; try assumption. apply HAmranf in Hc.
      destruct Hc as [Hc Hc']. destruct Hc'. apply Hranf.
      destruct (Enderton4C n') as [n [Hn Hn']].
      { apply Homga, HhomgaA. exists hm, n'hm. split; assumption. }
      { intros C. apply Q. apply Empty_Unique; try assumption. }
      assert (R : hm = c).
      { apply (FunVal_Unique h o hm c); try apply  HhomgaA; try assumption.
        - exists omga. split. apply HhomgaA.
          apply Homga, Zero_NaturalNumber, Ho.
        - intros _ _. exists mhm. split; assumption. }
      replace hm with c in *. clear R.
      assert (H0 : exists domh, Domain h domh /\ In n domh).
      { exists omga. split. try apply HhomgaA. apply Homga. assumption. }
      destruct HhomgaA as [Hfh HhomgaA].
      funval Hfh H0 h n. rename x into hn. rename H1 into Hhn.
      destruct Hhn as [nhn [Hnhn Hnhn']]; try assumption.
      destruct HhomgaA as [Hdomh [rnah [Hranh Hsub]]].
      exists hn. destruct (FunVal_Exists f hn); try apply HfAA.
      { exists A. split. apply HfAA. apply Hsub. apply Hranh.
        exists n, nhn. split; try assumption. }
      rename x into fhn. rename H1 into Hfhn.
      destruct Hfhn as [hnfhn [Hhnfhn Hhnfhn']]; try apply HfAA.
      { exists A. split. apply HfAA. apply Hsub. apply Hranh.
        exists n, nhn. split; try assumption. }
      exists hnfhn. split; try assumption. replace c with fhn; try assumption.
      symmetry. apply (Hhn' n n' hn c fhn); try assumption.
      * apply Homga; assumption.
      * intros _ _. exists nhn. split; assumption.
      * intros _ _. exists n'hm. split; assumption.
      * intros _ _. exists hnfhn. split; assumption.
  - intros n n' Hn' Hn. apply HS. apply HS in Hn. destruct Hn as [Hn1 Hn2].
    apply Homga in Hn1. split; try (apply Homga, (Succ_NaturalNumber n n'); assumption).
    intros m' hm' n'hm' m'hm' Hn'hm' Hm'hm' H I.
    destruct HhomgaA as [Hfh [Hdomh [ranh [Hranh Hsub]]]].
    destruct (Enderton4C m') as [m [Hm Hm']].
    { apply Homga, Hdomh. exists hm', m'hm'. split; assumption. }
    { intros C. apply HAmranf in Hc. destruct Hc as [Hc Hc']. apply Hc'.
      apply Hranf. assert (T : hm' = c).
      { apply (FunVal_Unique h o hm' c); try assumption.
        - exists omga. split; try assumption. apply Homga, Zero_NaturalNumber, Ho.
        - intros _ _. exists m'hm'. split; try assumption.
          replace o with m'; try assumption. apply Empty_Unique; try assumption. }
      replace hm' with c in *. clear T.
      assert (H0 : exists domh, Domain h domh /\ In n domh).
      { exists omga. split; try assumption. apply Homga. assumption. }
      funval Hfh H0 h n. rename x into hn. rename H1 into Hhn.
      destruct Hhn as [nhn [Hnhn Hnhn']]; try assumption.
      exists hn. destruct (FunVal_Exists f hn); try apply HfAA.
      { exists A. split. apply HfAA. apply Hsub. apply Hranh.
        exists n, nhn. split; try assumption. }
      rename x into fhn. rename H1 into Hfhn.
      destruct Hfhn as [hnfhn [Hhnfhn Hhnfhn']]; try apply HfAA.
      { exists A. split. apply HfAA. apply Hsub. apply Hranh.
        exists n, nhn. split; try assumption. }
      exists hnfhn. split; try assumption. replace c with fhn; try assumption.
      symmetry. apply (Hhn' n n' hn c fhn); try assumption.
      * apply Homga; assumption.
      * intros _ _. exists nhn. split; try assumption.
      * intros _ _. exists n'hm'. split; assumption.
      * intros _ _. exists hnfhn. split; assumption. }
    assert (H0 : exists domh, Domain h domh /\ In n domh).
    { exists omga. split; try assumption. apply Homga. assumption. }
    assert (H1 : exists domh, Domain h domh /\ In m domh).
    { exists omga. split; try assumption. apply Homga. assumption. }
    funval Hfh H0 h n. rename x into hn. rename H2 into Hhn.
    funval Hfh H1 h m. rename x into hm. rename H2 into Hhm.
    destruct Hhn as [nhn [Hnhn Hnhn']]; try assumption.
    destruct Hhm as [mhm [Hmhm Hmhm']]; try assumption.
    assert (H2 : exists domf, Domain f domf /\ In hm domf).
    { exists A. split. apply HfAA. apply Hsub. apply Hranh.
      exists m, mhm. split; assumption. }
    assert (H3 : exists domf, Domain f domf /\ In hn domf).
    { exists A. split. apply HfAA. apply Hsub. apply Hranh.
      exists n, nhn. split; assumption. }
    destruct HfAA as [Hff HfAA].
    funval Hff H2 f hm. rename x into fhm. rename H4 into Hfhm.
    funval Hff H3 f hn. rename x into fhn. rename H4 into Hfhn.
    assert (P : fhm = fhn).
    { transitivity hm'.
      - symmetry. apply (Hhn' m m' hm hm' fhm); try assumption.
        + apply Homga. assumption.
        + intros _ _. exists mhm. split; assumption.
        + intros _ _. exists m'hm'. split; assumption.
      - apply (Hhn' n n' hn hm' fhn); try assumption.
        + apply Homga. assumption.
        + intros _ _. exists nhn. split; assumption.
        + intros _ _. exists n'hm'. split; assumption. }
    assert (Q : hm = hn).
    { destruct Hf as [_ Hf].
      destruct Hfhm as [hmfhm [Hhmfhm Hhmfhm']]; try assumption.
      destruct Hfhn as [hnfhn [Hhnfhn Hfnhfn']]; try assumption.
      apply (Hf hm hn fhm hmfhm hnfhn); try assumption.
      replace fhm with fhn; try assumption. }
    apply (Succ_Unique n n' m'); try assumption.
    replace n with m; try assumption.
    ordpair n hm. rename x into nhm. rename H2 into Hnhm.
    symmetry. apply (Hn2 m hm nhm mhm); try assumption.
    replace nhm with nhn; try assumption.
    apply (OrdPair_Unique n hn nhn nhm); try assumption.
    replace hn with hm; try assumption.
Qed. 

Definition preClosure1 (f B A preC1 : set) : Prop :=
  forall X, In X preC1 <-> Subset A X /\ Subset X B /\
  forall fX, Image X f fX -> Subset fX X.

Theorem preClosure1_Exists : forall f B A, exists preC1, preClosure1 f B A preC1.
Proof.
  intros f B A. powerset B. rename x into PB. rename H into HPB.
  build_set
    (prod (prod set set) set)
    (fun (t : set * set * set) (c X : set) => Subset (snd t) X /\
      Subset X (snd (fst t)) /\ forall fX, Image X (fst (fst t)) fX -> Subset fX X)
    (f, B, A)
    PB.
  rename x into preC1. rename H into HpreC1. exists preC1.
  intros X. split; intros H; try apply HpreC1; try assumption.
  split; try apply H. apply HPB. intros x Hx.
  destruct H as [_ [H _]]. apply H. assumption.
Qed.

Theorem preClosure1_Unique : forall f B A C C', preClosure1 f B A C ->
  preClosure1 f B A C' -> C = C'.
Proof.
  intros f B A C C' HC HC'.
  apply Extensionality_Axiom. intros x. split; intros H.
  - apply HC', HC, H.
  - apply HC, HC', H.
Qed.

Definition GivenByImageClosure (f B F : set) : Prop :=
  forall XY, In XY F <-> exists X Y fX, OrdPair X Y XY /\
  Subset X B /\ Subset Y B /\ Image X f fX /\ BinaryUnion X fX Y.

Theorem GivenByImageClosure_Exists : forall f B, exists F, GivenByImageClosure f B F.
Proof.
  intros f B. powerset B. rename x into PB. rename H into HPB.
  prod PB PB. rename x into PBxPB. rename H into HPBxPB.
  build_set
    (prod set set)
    (fun (t : set * set) (c x : set) => exists X Y fX, OrdPair X Y x /\
      Subset X (fst t) /\ Subset Y (fst t) /\ Image X (snd t) fX /\
      BinaryUnion X fX Y)
    (B, f)
    PBxPB.
  rename x into F. rename H into HF. exists F. intros XY. split; intros H.
  - apply HF, H.
  - apply HF. split; try assumption. apply HPBxPB.
    destruct H as [X [Y [fX [HXY [HX [HY [HfX H]]]]]]].
    exists X, Y. repeat (split; try assumption; try apply HPB; try assumption).
Qed.

Theorem GivenByImageClosure_Unique : forall f B F G,
  GivenByImageClosure f B F -> GivenByImageClosure f B G -> F = G.
Proof.
  intros f B F G HF HG. apply Extensionality_Axiom. intros x; split; intros H.
  - apply HG, HF, H.
  - apply HF, HG, H.
Qed.

Theorem GivenByImageClosure_Into : forall f B PB F, FuncFromInto f B B ->
  PowerSet B PB -> GivenByImageClosure f B F -> FuncFromInto F PB PB.
Proof.
  intros f B PB F [Hf [Hdomf [ranf [Hranf Hsub]]]] HPB HF. repeat split.
  - intros xy H. apply HF in H. destruct H as [X [Y [_ [HXY _]]]].
    exists X, Y. assumption.
  - intros X Y Z XY XZ HXY HXZ H I. apply HF in H. apply HF in I.
    destruct H as [X' [Y' [fX [HXY' [HX [HY [HfX H]]]]]]].
    assert (T : X = X' /\ Y = Y').
    { apply (Enderton3A X Y X' Y' XY XY HXY HXY'). trivial. }
    replace X' with X in *; replace Y' with Y in *; try apply T.
    clear X' Y' T HXY'. destruct I as [X' [Z' [fX' [HXZ' [HX' [HY' [HfX' I]]]]]]].
    assert (T : X = X' /\ Z = Z').
    { apply (Enderton3A X Z X' Z' XZ XZ HXZ HXZ'). trivial. }
    replace X' with X in *; replace Z' with Z in *; try apply T.
    clear X' Z' T HXZ'. apply (BinaryUnion_Unique X fX Y Z); try assumption.
    replace fX with fX'; try assumption.
    apply (Image_Unique X f fX' fX); assumption.
  - rename x into X. intros HX. image X f. rename x into fX. rename H into HfX.
    binary_union X fX. rename x into Y. rename H into HY.
    ordpair X Y. rename x into XY. rename H into HXY.
    exists Y, XY. split; try assumption. apply HF.
    exists X, Y, fX. repeat (split; try assumption).
    + apply HPB; assumption.
    + intros y H. apply HY in H. destruct H as [H | H].
      * apply HPB in HX. apply HX, H.
      * apply HfX in H. destruct H as [x [xy [Hxy [H I]]]].
        apply Hsub. apply Hranf. exists x, xy. split; try assumption.
  - rename x into X. intros [Y [XY [HXY H]]]. apply HF in H.
    destruct H as [X' [Y' [fX [HXY' [HX [HY [HfX H]]]]]]].
    apply HPB. replace X with X'; try assumption.
    apply (Enderton3A X' Y' X Y XY XY HXY' HXY). trivial.
  - range F. rename x into ranF. rename H into HranF.
    exists ranF. split; try assumption.
    intros Y H. apply HranF in H. destruct H as [X [XY [HXY H]]].
    apply HF in H. destruct H as [X' [Y' [fX [HXY' [_ [HY _]]]]]].
    apply HPB. replace Y with Y'; try assumption.
    apply (Enderton3A X' Y' X Y XY XY HXY' HXY). trivial.
Qed.

Definition preClosure2 (f B A preC2 : set) : Prop := FuncFromInto f B B ->
  Subset A B -> exists PB F h, GivenByImageClosure f B F /\ PowerSet B PB /\
  RecursiveFunction PB A F h /\ Range h preC2.

Theorem preClosure2_Exists : forall f B A, FuncFromInto f B B -> Subset A B ->
  exists C, preClosure2 f B A C.
Proof.
  intros f B A HfBB HAB. powerset B. rename x into PB. rename H into HPB.
  destruct (GivenByImageClosure_Exists f B). rename x into F. rename H into HF.
  assert (HFPBPB : FuncFromInto F PB PB).
  { apply (GivenByImageClosure_Into f B); try assumption. }
  assert (HA : In A PB).
  { apply HPB. assumption. }
  recursion PB A F HA HFPBPB. rename x into h. rename H into Hh.
  range h. rename x into ranh. rename H into Hranh.
  exists ranh. intros _ _. exists PB, F, h. repeat (split; try assumption).
Qed.

Theorem preClosure2_Unique : forall f B A C C', FuncFromInto f B B ->
  Subset A B -> preClosure2 f B A C ->
  preClosure2 f B A C' -> C = C'.
Proof.
  intros f B A C C' HfBB HAB HC HC'.
  destruct HC as [PB [F [h [HF [HPB [Hh Hranh]]]]]]; try assumption.
  destruct HC' as [PB' [F' [h' [HF' [HPB' [Hh' Hranh']]]]]]; try assumption.
  apply (Range_Unique h C C'); try assumption.
  replace h with h'; try assumption.
  apply (RecursiveFunction_Unique PB A F h' h); try assumption.
  { apply HPB; assumption. }
  { apply (GivenByImageClosure_Into f B); try assumption. }
  replace PB with PB'.
  - replace F with F'; try assumption.
    apply (GivenByImageClosure_Unique f B); try assumption.
  - apply (Power_Set_Unique B PB' PB); try assumption.
Qed.

Lemma Subset_Transitive : forall A B C, Subset A B -> Subset B C -> Subset A C.
Proof.
  intros A B C HAB HBC. intros a H. apply HBC, HAB, H.
Qed.

Theorem Exercise4_9 : forall f B A C1 C2 NC1 UC2, FuncFromInto f B B ->
  Subset A B -> preClosure1 f B A C1 -> preClosure2 f B A C2 -> 
  Intersect C1 NC1 -> Union C2 UC2 -> NC1 = UC2.
Proof.
  intros f B A C1 C2 NC1 UC2 HfBB HAB HC1 HC2 HNC1 HUC2.
  assert (Hne : ~ Empty C1).
  { intros C. apply (C B). apply HC1. split; try assumption.
    split; try apply Subset_Reflexive. intros fB HfB b H.
    apply HfB in H. destruct H as [a [ab [Hab [Ha H]]]].
    destruct HfBB as [Hf [Hdomf [ranf [Hranf Hsub]]]].
    apply Hsub, Hranf. exists a, ab. split; try assumption. }
  apply (SubsetSymmetric_iff_Equal). split.
  - image UC2 f. rename x into fUC2. rename H into HfUC2.
    assert (P : Subset fUC2 UC2).
    { intros y H. apply HUC2. apply HfUC2 in H.
      destruct H as [x [xy [Hxy [Hx H]]]]. apply HUC2 in Hx.
      destruct Hx as [X [Hx HX]].
      destruct HC2 as [PB [F [h [HF [HPB [Hh Hranh]]]]]]; try assumption.
      apply Hranh in HX. destruct HX as [n [nX [HnX HX]]].
      destruct Hh as [omga [e [Homga [He [[Hfh [Hdomh Hranh']] [Hhe Hhn']]]]]].
      destruct Hranh' as [ranh' [Hranh' Hsub]].
      succ n. rename x0 into n'. rename H0 into Hn'.
      assert (H0 : exists domh, Domain h domh /\ In n' domh).
      { exists omga. split; try assumption. apply Homga.
        apply (Succ_NaturalNumber n n'); try assumption.
        apply Homga. apply Hdomh. exists X, nX. split; assumption. }
      assert (H1 : exists domF, Domain F domF /\ In X domF).
      { exists PB. split. apply (GivenByImageClosure_Into f B); try assumption.
        apply Hsub. apply Hranh'. exists n, nX. split; assumption. }
      destruct (GivenByImageClosure_Into f B PB F) as [HfF _]; try assumption.
      funval Hfh H0 h n'. rename x0 into Y. rename H2 into HY.
      funval HfF H1 F X. rename x0 into Y'. rename H2 into HY'.
      destruct HY' as [XY [HXY HXY']]; try assumption.
      apply HF in HXY'. destruct HXY' as [X' [Y'' [fX [HXY' [HX' [HY' [HfX I]]]]]]].
      exists Y''. split.
      - apply I. right. apply HfX. exists x, xy. repeat (split; try assumption).
        replace X' with X; try assumption.
        apply (Enderton3A X Y' X' Y'' XY XY HXY HXY'). trivial.
      - replace Y'' with Y. apply Hranh. exists n'. apply HY; try assumption.
        transitivity Y'.
        + apply (Hhn' n n' X Y Y'); try assumption.
          * apply Hdomh. exists X, nX. split; try assumption.
          * intros _ _. exists nX. split; try assumption.
          * intros _ _. exists XY. split; try assumption.
            apply HF. exists X', Y'', fX. repeat (split; try assumption).
        + apply (Enderton3A X Y' X' Y'' XY XY HXY HXY'). trivial. }
    assert (Q : In UC2 C1).
    { apply HC1. 
      destruct HC2 as [PB [F [h [HF [HPB [Hh Hranh]]]]]]; try assumption.
      destruct Hh as [omga [o [Homga [Ho [Hh [Hho Hhn']]]]]]. split; try split.
      - intros a H. apply HUC2. exists A. split; try assumption.
        apply Hranh. exists o. apply Hho; try apply Hh.
        exists omga. split; try (apply Homga, Zero_NaturalNumber, Ho); apply Hh.
      - intros b H. apply HUC2 in H. destruct H as [Y [H I]].
        apply Hranh in I. destruct I as [X [XY [HXY I]]].
        destruct Hh as [Hh [Hdomh [ranh [Hranh' Hsub]]]].
        assert (T : In Y PB).
        { apply Hsub. apply Hranh'. exists X, XY. split; assumption. }
        apply HPB in T. apply T. assumption.
      - intros fX HfX. replace fX with fUC2; try assumption.
        apply (Image_Unique UC2 f); try assumption. }
    intros x H. assert (R : forall X, In X C1 -> In x X).
    { apply HNC1; try assumption. }
    apply R, Q.
  - intros y H. apply HUC2 in H. destruct H as [Y [H I]].
    destruct HC2 as [PB [F [h [HF [HPB [Hh HC2]]]]]]; try assumption.
    destruct Hh as [omga [o [Homga [Ho [Hh [Hho Hhn']]]]]].
    build_set set
      (fun (t c x : set) => forall hx, FunVal t x hx -> Subset hx NC1) h omga.
    rename x into T. rename H0 into HT.
    apply HC2 in I. destruct I as [n [nY [HnY I]]].
    assert (P : In n omga).
    { destruct Hh as [Hh [Hdomh _]]. apply Hdomh.
      exists Y, nY. split; assumption. }
    replace omga with T in P.
    { apply HT in P. destruct P as [_ P]. apply (P Y); try assumption.
      intros _ _. exists nY. split; assumption. }
    apply Induction_Principle_for_Omega; try assumption; try split.
    + exists o. split; try assumption. apply HT.
      split; try apply Homga, Zero_NaturalNumber, Ho.
      intros A' HA' a J. apply HNC1; try assumption.
      intros X HX. apply HC1 in HX. destruct HX as [HX _].
      apply HX. replace A with A'; try assumption.
      apply (FunVal_Unique h o A' A); try assumption; try apply Hh.
      exists omga. split. apply Hh. apply Homga, Zero_NaturalNumber, Ho.
    + intros m m' Hm' Hm. apply HT in Hm. destruct Hm as [Hm IH].
      apply HT. apply Homga in Hm.
      split; try (apply Homga, (Succ_NaturalNumber m m'); try assumption).
      intros X HX. destruct (GivenByImageClosure_Into f B PB F); try assumption.
      destruct Hh as [Hh [Hdomh [ranh [Hranh Hsub]]]].
      assert (H3 : exists domh, Domain h domh /\ In m domh).
      { exists omga. split; try assumption. apply Homga. assumption. }
      funval Hh H3 h m. rename H2 into Hhm. rename x into hm.
      assert (H2 : exists domF, Domain F domF /\ In hm domF).
      { exists PB; split. try apply H1. apply Hsub. apply Hranh.
        exists m. apply Hhm; try assumption. }
      funval H0 H2 F hm. rename x into Fhm. rename H4 into HFhm.
      destruct HFhm as [hmFhm [HhmFhm HhmFhm']]; try assumption.
      apply HF in HhmFhm' as [hm' [Fhm' [fhm [HhmFhm' [HhmB [HFhmB [Hfhm Q]]]]]]].
      intros x J. replace X with Fhm' in J. apply Q in J.
      assert (T0 : hm = hm' /\ Fhm = Fhm').
      { apply (Enderton3A hm Fhm hm' Fhm' hmFhm hmFhm HhmFhm HhmFhm'). trivial. }
      replace hm' with hm in *; replace Fhm' with Fhm in *; try apply T0.
      clear T0 hm' Fhm' HhmFhm'. destruct J as [J | J]; 
      try (apply (IH hm); assumption). apply Hfhm in J.
      destruct J as [w [wx [Hwx [J K]]]]. apply HNC1; try assumption.
      intros W HW. apply HC1 in HW.
      image W f. rename x0 into fW. rename H4 into HfW.
      destruct HW as [HW1 [HW2 HW]]. apply (HW fW); try assumption.
      apply HfW. exists w, wx. repeat (split; try assumption).
      apply IH in J; try assumption. assert (J' : forall y, In y C1 -> In w y).
      { apply HNC1; try assumption. }
      apply J'. apply HC1. repeat (split; try assumption).
      { transitivity Fhm.
        - apply (Enderton3A hm' Fhm' hm Fhm hmFhm hmFhm); try assumption. trivial.
        - symmetry. apply (Hhn' m m' hm X Fhm); try assumption.
          + apply Homga; try assumption.
          + intros _ _. exists hmFhm. split; try assumption.
            apply HF. exists hm', Fhm', fhm. repeat (split; try assumption). }
    + intros t J. apply HT in J. apply J.
Qed.

(** Exercise 4-10 : In exercise 9, assume that B is the set of real numbers,
    f(x) = x^2, and A is the closed interval [0.5, 1]. What is the set called
    NC1 or UC2?  TODO *)

(** Exercise 4-11 : In exercise 9, assume that B is the set of real numbers,
    f(x) = x - 1, and A = {0}. What is the set called NC1 or UC2? TODO *)

(** Exercise 4-12 : Formulate an analog to Exercise 9 for a function f : BxB -> B.*)

(** Having acheived the axiomatic basis for the natural numbers via Peano's
    Postulates, we now turn our attention to the familiar arithmetic operations
    on the natural numbers. We will given a set-theoretic definition of the
    operations addition (+ : omega x omega -> omega), multiplication
    ( * : omega x omega -> omega), and exponentiation (^ : omega x omega -> omega)
    using the recursion theorem. We also prove some familiar algebraic
    properties of these operations, which follow from Peano's postulates. *)

Definition Addn (n An : set) : Prop :=
  NaturalNumber n -> exists omga sigma, Nats omga /\ SuccessorFunc sigma /\
  RecursiveFunction omga n sigma An.

Theorem Addn_Exists : forall n, NaturalNumber n -> exists An, Addn n An.
Proof.
  intros n Hn. omga. sigma. apply Homga in Hn.
  recursion omga n sigma Hn (SuccessorFunc_Into sigma omga Hsigma Homga).
  rename x into An. rename H into HAn. exists An. intros _.
  exists omga, sigma. repeat (split; try assumption).
Qed.

Theorem Addn_Unique : forall n An Bn, NaturalNumber n -> Addn n An ->
  Addn n Bn -> An = Bn.
Proof.
  intros n An Bn Hn HAn HBn.
  destruct HAn as [omga [sigma [Homga [Hsigma HAn]]]]; try assumption.
  destruct HBn as [omga' [sigma' [Homga' [Hsigma' HBn]]]]; try assumption.
  apply (RecursiveFunction_Unique omga n sigma); try assumption.
  - apply Homga, Hn.
  - apply SuccessorFunc_Into; try assumption.
  - replace omga with omga'. replace sigma with sigma'; try assumption.
    apply (SuccessorFunc_Unique); try assumption.
    apply Nats_Unique; try assumption.
Qed.

Definition BinaryOperator (op A : set) : Prop :=
  exists AxA, Prod A A AxA /\ FuncFromInto op AxA A.

Definition Addition_w (add : set) : Prop :=
  forall mnp, In mnp add <-> exists mn p m n Am, OrdPair mn p mnp /\
  OrdPair m n mn /\ NaturalNumber m /\ NaturalNumber n /\ Addn m Am /\
  FunVal Am n p.

Theorem Addition_w_Exists : exists add, Addition_w add.
Proof.
  omga. prod omga omga. rename x into wxw. rename H into Hwxw.
  prod wxw omga. rename x into wxwxw. rename H into Hwxwxw.
  build_set
    set
    (fun (t c x : set) => exists mn p m n Am, OrdPair mn p x /\
      OrdPair m n mn /\ NaturalNumber m /\ NaturalNumber n /\ Addn m Am /\
      FunVal Am n p)
    omga
    wxwxw.
  rename x into add. rename H into Hadd. exists add.
  intros mnp. split; intros H; try apply Hadd, H.
  apply Hadd. split; try assumption.
  apply Hwxwxw. destruct H as [mn [p [m [n [Am [Hmnp [Hmn [Hm [Hn [HAm Hp]]]]]]]]]].
  exists mn, p. split; try split; try assumption.
  - apply Hwxw. exists m, n.
    repeat (split; try assumption); try apply Homga; assumption.
  - destruct HAm as [omga' [sigma [Homga' [Hsigma HAm]]]]; try apply Hm.
    replace omga' with omga in *; try (apply Nats_Unique; assumption).
    clear omga' Homga'.
    destruct HAm as [omga' [o [Homga' [Ho [HAm [HAmo HAmn']]]]]].
    replace omga' with omga in *; try (apply Nats_Unique; assumption).
    clear omga' Homga'. destruct HAm as [HAm [HdomAm [ranAm [HranAm Hsub]]]].
    apply Hsub. apply HranAm. exists n. apply Hp; try assumption.
    exists omga. split; try assumption. apply Homga; assumption.
Qed. 

Theorem Addition_w_Unique : forall add add', Addition_w add -> Addition_w add' ->
  add = add'.
Proof.
  intros add add' H H'. apply Extensionality_Axiom. intros x. split; intros I.
  - apply H', H, I.
  - apply H, H', I.
Qed.

Lemma Addition_w_BinaryOperation : forall add omga, Addition_w add -> Nats omga ->
  BinaryOperator add omga.
Proof.
  intros add omga Hadd Homga.
  prod omga omga. rename x into omgaxomga. rename H into Homgaxomga.
  exists omgaxomga. split; try assumption. split; split.
  - intros mnp Hmnp. apply Hadd in Hmnp.
    destruct Hmnp as [mn [p [_ [_ [_ [Hmnp _]]]]]].
    exists mn, p. assumption.
  - intros mn p q mnp mnq Hmnp Hmnq H I.
    apply Hadd in H. apply Hadd in I.
    destruct H as [mn' [p' [m [n [Am [Hmnp' [Hmn [Hm [Hn [HAm Hp]]]]]]]]]].
    assert (T : mn = mn' /\ p = p').
    { apply (Enderton3A mn p mn' p' mnp mnp Hmnp Hmnp'). trivial. }
    replace mn' with mn in *; replace p' with p in *; try apply T.
    clear T Hmnp' mn' p'.
    destruct I as [mn' [q' [m' [n' [Am' [Hmnq' [Hmn' [_ [_ [HAm' Hq]]]]]]]]]].
    assert (T : mn = mn' /\ q = q').
    { apply (Enderton3A mn q mn' q' mnq mnq Hmnq Hmnq'). trivial. }
    replace mn' with mn in *; replace q' with q in *; try apply T.
    clear T Hmnq' mn' q'.
    assert (T : m = m' /\ n = n').
    { apply (Enderton3A m n m' n' mn mn Hmn Hmn'). trivial. }
    replace m' with m in *; replace n' with n in *; try apply T.
    clear m' n' T Hmn'.
    replace Am' with Am in *; try apply (Addn_Unique m Am Am' Hm HAm HAm').
    clear HAm' Am'.
    destruct (HAm Hm) as [omga' [sigma [Homga' [Hsigma HAm']]]].
    replace omga' with omga in *; try (apply Nats_Unique; assumption).
    clear Homga' omga'. destruct HAm' as [omga' [_ [Homga' [_ [HAm' _]]]]].
    replace omga' with omga in *; try (apply Nats_Unique; assumption).
    apply (FunVal_Unique Am n p q); try assumption; try apply HAm'.
    exists omga. split. apply HAm'. apply Homga, Hn.
  - intros mn. split; intros H.
    + apply Homgaxomga in H. destruct H as [m [n [Hm [Hn Hmn]]]].
      apply Homga in Hm. destruct (Addn_Exists m Hm) as [Am HAm].
      destruct (HAm Hm) as [omga' [sigma [Homga' [Hsigma HAm']]]].
      replace omga' with omga in *; try (apply Nats_Unique; assumption).
      clear Homga' omga'. destruct HAm' as [omga' [_ [Homga' [_ [HAm' _]]]]].
      replace omga' with omga in *; try (apply Nats_Unique; assumption).
      destruct HAm' as [HAm' [HdomAm _]].
      assert (T : exists domAm, Domain Am domAm /\ In n domAm).
      { exists omga. split; try assumption. }
      funval HAm' T Am n. rename x into p. rename H into Hp.
      ordpair mn p. rename x into mnp. rename H into Hmnp.
      exists p, mnp. split; try assumption. apply Hadd.
      exists mn, p, m, n, Am. repeat (split; try assumption). apply Homga, Hn.
    + destruct H as [p [mnp [Hmnp H]]]. apply Homgaxomga. apply Hadd in H.
      destruct H as [mn' [p' [m [n [Am [Hmnp' [Hmn [Hm [Hn [HAm Hp]]]]]]]]]].
      assert (T : mn = mn' /\ p = p').
      { apply (Enderton3A mn p mn' p' mnp mnp Hmnp Hmnp'). trivial. }
      replace mn' with mn in *; replace p' with p in *; try apply T.
      clear T mn' p' Hmnp'. exists m, n.
      repeat (split; try assumption; try apply Homga; try assumption).
  - exists omga. split; try apply Subset_Reflexive. intros p; split; intros H.
    + zero. rename x into o. rename H0 into Ho.
      ordpair p o. rename x into po. rename H0 into Hpo.
      ordpair po p. rename x into pop. rename H0 into Hpop.
      exists po, pop. split; try assumption. apply Hadd.
      destruct (Addn_Exists p) as [Ap HAp]; try (apply Homga; assumption).
      exists po, p, p, o, Ap. repeat (split; try apply Homga; try assumption).
      * apply Homga, Zero_NaturalNumber, Ho.
      * intros _ _. ordpair o p. rename x into op. rename H0 into Hop.
        exists op. split; try assumption. apply Homga in H.
        destruct (HAp H) as [omga' [sigma [Homga' [Hsigma HAp']]]].
        replace omga' with omga in *; try apply Nats_Unique; try assumption.
        clear omga' Homga'.
        destruct HAp' as [omga' [o' [Homga' [Ho' [HAp' [HApo HApn']]]]]].
        replace omga' with omga in *; try apply Nats_Unique; try assumption.
        replace o' with o in *; try apply Empty_Unique; try assumption.
        destruct HAp' as [HAp' [HdomAp _]].
        assert (T : exists domAp, Domain Ap domAp /\ In o domAp).
        { exists omga. split; try assumption. apply Homga, Zero_NaturalNumber, Ho. }
        destruct (HApo HAp' T) as [op' [Hop' Hop'']].
        replace op with op'; try assumption.
        apply (OrdPair_Unique o p op' op); try assumption.
    + destruct H as [mn [mnp [Hmnp H]]]. apply Hadd in H.
      destruct H as [mn' [p' [m [n [Am [Hmnp' [Hmn [Hm [Hn [HAm Hp]]]]]]]]]].
      assert (T : mn = mn' /\ p = p').
      { apply (Enderton3A mn p mn' p' mnp mnp Hmnp Hmnp'). trivial. }
      replace mn' with mn in *; replace p' with p in *; try apply T.
      clear T mn' p' Hmnp'.
      destruct (HAm Hm) as [omga' [sigma [Homga' [Hsigma HAm']]]].
      replace omga' with omga in *; try apply Nats_Unique; try assumption.
      clear omga' Homga'.
      destruct HAm' as [omga' [o [Homga' [Ho [HAm' [HAmo HAmn']]]]]].
      replace omga' with omga in *; try apply Nats_Unique; try assumption.
      clear omga' Homga'.
      destruct HAm' as [Ham' [HdomAm [ranAm [HranAm Hsub]]]].
      apply Hsub. apply HranAm. exists n. apply Hp; try assumption.
      exists omga. split; try assumption. apply Homga, Hn.
Qed.

Ltac add_w := destruct (Addition_w_Exists) as [add Hadd].

Definition Sum_w (m n p : set) : Prop := NaturalNumber m -> NaturalNumber n ->
  exists add mn mnp, Addition_w add /\ OrdPair m n mn
  /\ OrdPair mn p mnp /\ In mnp add.

Theorem Sum_w_Exists : forall m n, NaturalNumber m -> NaturalNumber n ->
  exists p, Sum_w m n p.
Proof.
  intros m n Hm Hn. ordpair m n. rename x into mn. rename H into Hmn.
  add_w. omga. destruct (Addition_w_BinaryOperation add omga Hadd Homga) as
    [omgaxomga [Homgaxomga H]].
  destruct H as [Haddf [Hdomadd _]].
  assert (P : In mn omgaxomga).
  { apply Homgaxomga. exists m, n. repeat (split; try apply Homga; try assumption). }
  apply Hdomadd in P. destruct P as [p [mnp [Hmnp P]]].
  exists p. intros _ _. exists add, mn, mnp. repeat (split; try assumption).
Qed.

Theorem Sum_w_Unique : forall m n p q, NaturalNumber m -> NaturalNumber n ->
  Sum_w m n p -> Sum_w m n q -> p = q.
Proof.
  intros m n p q Hm Hn Hp Hq.
  destruct (Hp Hm Hn) as [add [mn [mnp [Hadd [Hmn [Hmnp Hp']]]]]].
  destruct (Hq Hm Hn) as [add' [mn' [mnq [Hadd' [Hmn' [Hmnq Hq']]]]]].
  replace add' with add in *; try (apply (Addition_w_Unique add add'); assumption).
  replace mn' with mn in *; try (apply (OrdPair_Unique m n mn mn'); assumption).
  clear add' mn' Hadd' Hmn'. omga.
  destruct (Addition_w_BinaryOperation add omga Hadd Homga)
    as [omgaxomga [Homgaxomga H]].
  destruct H as [[_ Haddf] _]. apply (Haddf mn p q mnp mnq); try assumption.
Qed.

Ltac sum_w m n Hm Hn := destruct (Sum_w_Exists m n Hm Hn).

Definition A1 : Prop := forall m o, NaturalNumber m -> Empty o -> Sum_w m o m.

Definition A2 : Prop := forall m n n' mn mn' mn'', NaturalNumber m ->
  NaturalNumber n -> Succ n n' -> Sum_w m n mn -> Sum_w m n' mn' -> Succ mn mn'' ->
  mn' = mn''.

Theorem Enderton4I : A1 /\ A2.
Proof.
  split.
  - intros m o Hm Ho. intros _ _. add_w. exists add.
    ordpair m o. rename x into mo. rename H into Hmno. exists mo.
    ordpair mo m. rename x into mom. rename H into Hmom. exists mom.
    repeat (split; try assumption). apply Hadd.
    destruct (Addn_Exists m Hm) as [Am HAm]. exists mo, m, m, o, Am.
    repeat (split; try assumption; try apply Zero_NaturalNumber, Ho).
    intros _ _. destruct (HAm Hm) as [omga [sigma [Homga [Hsigma HAm']]]].
    destruct HAm' as [omga' [o' [Homga' [Ho' [HAm' [HAmo _]]]]]].
    replace omga' with omga in *; try apply Nats_Unique; try assumption.
    clear omga' Homga'.
    replace o' with o in *; try apply Empty_Unique; try assumption.
    clear o' Ho'. apply HAmo; try apply HAm'.
    exists omga. split. apply HAm'. apply Homga, Zero_NaturalNumber, Ho.
  - intros m n n' mn mn' mn'' Hm Hn Hn' Hmn Hmn' Hmn''.
    destruct (Hmn Hm Hn) as [add [mn0 [mn0mn [Hadd [Hmn0 [Hmnp H]]]]]].
    apply Hadd in H.
    destruct H as [mn0' [mn1 [m0 [n0 [Am [Hmn0mn' [Hmn0' [_ [_ [HAm HAmn]]]]]]]]]].
    assert (T : mn0 = mn0' /\ mn = mn1).
    { apply (Enderton3A mn0 mn mn0' mn1 mn0mn mn0mn); try assumption. trivial. }
    replace mn0' with mn0 in *; replace mn1 with mn in *; try apply T.
    clear T mn0' mn1 Hmn0mn'.
    assert (T : m = m0 /\ n = n0).
    { apply (Enderton3A m n m0 n0 mn0 mn0); try assumption. trivial. }
    replace m0 with m in *; replace n0 with n in *; try apply T.
    clear T m0 n0 Hmn0'.
    assert (P : NaturalNumber n').
    { apply (Succ_NaturalNumber n n'); try assumption. }
    destruct (Hmn' Hm P) as [add' [mn'0 [mn'0mn' [Hadd' [Hmn'0 [Hmn'p I]]]]]].
    replace add' with add in *; try (apply (Addition_w_Unique); assumption).
    clear Hadd' add'. apply Hadd in I.
    destruct I as [mn'0' [mn'1 [m0 [n'0 [Am' [Hmn'0mn'' [Hmn'0' [_ [_ [HAm' HAmn']]]]]]]]]].
    assert (T : mn'0 = mn'0' /\ mn' = mn'1).
    { apply (Enderton3A mn'0 mn' mn'0' mn'1 mn'0mn' mn'0mn'); try assumption. trivial. }
    replace mn'0' with mn'0 in *; replace mn'1 with mn' in *; try apply T.
    clear T mn'0' mn'1 Hmn'0mn''.
    assert (T : m = m0 /\ n' = n'0).
    { apply (Enderton3A m n' m0 n'0 mn'0 mn'0); try assumption. trivial. }
    replace m0 with m in *; replace n'0 with n' in *; try apply T.
    clear T m0 n'0 Hmn'0'.
    replace Am' with Am in *; try (apply (Addn_Unique m Am Am'); assumption).
    clear HAm' Am'. destruct (HAm Hm) as [omga [sigma [Homga [Hsigma HAm']]]].
    destruct HAm' as [omga' [o [Homga' [Ho [HAm' [HAmo HAmsn]]]]]].
    replace omga' with omga in *; try (apply Nats_Unique; assumption).
    apply (HAmsn n n' mn mn' mn''); try assumption; try apply Homga, Hn.
    intros _ _. ordpair mn mn''. rename x into mnmn''. rename H into Hmnmn''.
    exists mnmn''. split; try assumption. apply Hsigma.
    exists mn, mn''. repeat (split; try assumption).
    destruct HAm' as [HAm' [HdomAm [ranAm [HranAm Hsub]]]].
    apply Homga, Hsub. apply HranAm. exists n. apply HAmn; try assumption.
    exists omga. split; try assumption. apply Homga, Hn.
Qed.

Definition Multn (n Mn : set) : Prop :=
  NaturalNumber n -> exists omga An o, Nats omga /\ Addn n An /\ Empty o /\
  RecursiveFunction omga o An Mn.

Theorem Multn_Exists : forall n, NaturalNumber n -> exists Mn, Multn n Mn.
Proof.
  intros n Hn. destruct (Addn_Exists n Hn) as [An HAn].
  destruct (HAn Hn) as [omga [sigma [Homga [Hsigma HAn']]]].
  destruct HAn' as [omga' [o [Homga' [Ho [HAn' [HAno HAnn']]]]]].
  replace omga' with omga in *; try (apply Nats_Unique; assumption).
  assert (T : In o omga). { apply Homga, Zero_NaturalNumber, Ho. }
  recursion omga o An T HAn'. rename x into Mn. rename H into HMn.
  exists Mn. intros _. exists omga, An, o. repeat (split; try assumption).
Qed.

Theorem Multn_Unique : forall n Mn Nn, NaturalNumber n ->
  Multn n Mn -> Multn n Nn -> Mn = Nn.
Proof.
  intros n Mn Nn Hn HMn HNn.
  destruct (HMn Hn) as [omga [An [o [Homga [HAn [Ho HMn']]]]]].
  destruct (HNn Hn) as [omga' [Bn [o' [Homga' [HBn [Ho' HNn']]]]]].
  replace o' with o in *; try (apply Empty_Unique; assumption).
  replace omga' with omga in *; try (apply Nats_Unique; assumption).
  clear omga' Homga' o' Ho'.
  replace Bn with An in *; try
    (apply (RecursiveFunction_Unique omga o An Mn);
    try assumption;
    try apply Homga, Zero_NaturalNumber, Ho).
  - destruct (HAn Hn) as [omga' [sigma [Homga' [Hsigma HAn']]]].
    replace omga' with omga in *; try (apply Nats_Unique; assumption).
    clear omga' Homga'. destruct HAn' as [omga' [o' [Homga' [Ho' [HAn' _]]]]].
    replace omga' with omga in *; try (apply Nats_Unique; assumption).
    assumption.
  - apply (Addn_Unique n An Bn Hn); assumption.
Qed.

Definition Multiplication_w (mult : set) : Prop :=
  forall mnp, In mnp mult <-> exists mn p m n Mm, OrdPair mn p mnp /\
  OrdPair m n mn /\ NaturalNumber m /\ NaturalNumber n /\ Multn m Mm /\
  FunVal Mm n p.

Theorem Multiplication_w_Exists : exists mult, Multiplication_w mult.
Proof.
  omga. prod omga omga. rename x into wxw. rename H into Hwxw.
  prod wxw omga. rename x into wxwxw. rename H into Hwxwxw.
  build_set
    set
    (fun (t c x : set) => exists mn p m n Mm, OrdPair mn p x /\
      OrdPair m n mn /\ NaturalNumber m /\ NaturalNumber n /\ Multn m Mm /\
      FunVal Mm n p)
    omga
    wxwxw.
  rename x into mult. rename H into Hmult. exists mult.
  intros mnp. split; intros H; try apply Hmult; try assumption.
  split; try apply H.
  destruct H as [mn [p [m [n [Mm [Hmnp [Hmn [Hm [Hn [HMm H]]]]]]]]]].
  apply Hwxwxw. exists mn, p. repeat (split; try assumption).
  - apply Hwxw. exists m, n. repeat (split; try apply Homga; try assumption).
  - destruct (HMm Hm) as [omga' [Am [o [Homga' [HAm [Ho HMm']]]]]].
    replace omga' with omga in *; try (apply Nats_Unique; assumption).
    clear omga' Homga'. destruct HMm' as [omga' [o' [Homga' [Ho' [HMm' _]]]]].
    replace omga' with omga in *; try (apply Nats_Unique; assumption).
    destruct HMm' as [HMm' [HdomMm [ranMm [HranMm Hsub]]]].
    apply Hsub. apply HranMm. exists n. apply H; try assumption.
    exists omga. split; try assumption. apply Homga, Hn.
Qed.

Theorem Multiplication_w_Unique : forall mult mult',
  Multiplication_w mult -> Multiplication_w mult' -> mult = mult'.
Proof.
  intros mult mult' Hmult Hmult'.
  apply Extensionality_Axiom. intros mnp. split; intros H.
  - apply Hmult', Hmult, H.
  - apply Hmult, Hmult', H.
Qed.

Lemma Multiplication_w_BinaryOperation : forall mult omga,
  Multiplication_w mult -> Nats omga -> BinaryOperator mult omga.
Proof.
  intros mult omga Hmult Homga.
  prod omga omga. rename x into wxw. rename H into Hwxw.
  exists wxw. split; try assumption. split; split.
  - intros mnp Hmnp. apply Hmult in Hmnp.
    destruct Hmnp as [mn [p [m [n [Mm [Hmnp [Hmn [Hm [Hn [HMm Hp]]]]]]]]]].
    exists mn, p. assumption.
  - intros mn p q mnp mnq Hmnp Hmnq H I.
    apply Hmult in H.
    destruct H as [mn' [p' [m [n [Mm [Hmnp' [Hmn [Hm [Hn [HMm Hp]]]]]]]]]].
    assert (T : mn = mn' /\ p = p').
    { apply (Enderton3A mn p mn' p' mnp mnp Hmnp Hmnp'). trivial. }
    replace mn' with mn in *; replace p' with p in *; try apply T.
    clear mn' Hmnp' p' T. apply Hmult in I.
    destruct I as [mn' [q' [m' [n' [Mm' [Hmnq' [Hmn' [_ [_ [HMm' Hq]]]]]]]]]].
    assert (T : mn = mn' /\ q = q').
    { apply (Enderton3A mn q mn' q' mnq mnq Hmnq Hmnq'). trivial. }
    replace mn' with mn in *; replace q' with q in *; try apply T.
    clear mn' q' Hmnq' T.
    assert (T : m = m' /\ n = n').
    { apply (Enderton3A m n m' n' mn mn Hmn Hmn'). trivial. }
    replace m' with m in *; replace n' with n in *; try apply T.
    clear m' n' T Hmn'.
    replace Mm' with Mm in *; try (apply (Multn_Unique m Mm Mm'); assumption).
    clear Mm' HMm'.
    destruct (HMm Hm) as [omga' [Am [o [Homga' [HAm [Ho HMm']]]]]].
    replace omga' with omga in *; try (apply Nats_Unique; assumption).
    clear omga' Homga'. destruct HMm' as [omga' [o' [Homga' [Ho' [HMm' _]]]]].
    apply (FunVal_Unique Mm n p q); try assumption; try apply HMm'.
    exists omga'. split. apply HMm'. apply Homga'. apply Hn.
  - intros mn. split; intros H.
    + apply Hwxw in H. destruct H as [m [n [Hm [Hn Hmn]]]].
      apply Homga in Hm. destruct (Multn_Exists m Hm).
      rename x into Mm. rename H into HMm.
      destruct (HMm Hm) as [omga' [Am [o [Homga' [HAm [Ho HMm']]]]]].
      replace omga' with omga in *; try (apply Nats_Unique; assumption).
      clear omga' Homga'. destruct HMm' as [omga' [o' [Homga' [Ho' [HMm' _]]]]].
      replace omga' with omga in *; try (apply Nats_Unique; assumption).
      clear omga' Homga'. destruct HMm' as [HMm' [domMm' [ranMm' [HranMm' Hsub]]]].
      replace o' with o in *; try (apply Empty_Unique; assumption).
      clear o' Ho'. assert (P : exists domMm, Domain Mm domMm /\ In n domMm).
      { exists omga. split; try assumption. }
      funval HMm' P Mm n. rename x into p. rename H into Hp.
      destruct (Hp HMm' P) as [np [Hnp Hnp']].
      ordpair mn p. rename x into mnp. rename H into Hmnp.
      exists p, mnp. split; try assumption. apply Hmult.
      exists mn, p, m, n, Mm. repeat (split; try assumption).
      apply Homga; try assumption.
    + destruct H as [p [mnp [Hmnp H]]]. apply Hmult in H.
      destruct H as [mn' [p' [m [n [Mm [Hmnp' [Hmn [Hm [Hn [HMm Hp]]]]]]]]]].
      assert (T : mn = mn' /\ p = p').
      { apply (Enderton3A mn p mn' p' mnp mnp Hmnp Hmnp'). trivial. }
      replace mn' with mn in *; replace p' with p in *; try apply T.
      clear mn' p' Hmnp' T. apply Hwxw. exists m, n.
      repeat (split; try apply Homga; try assumption).
  - range mult. rename x into ranmult. rename H into Hranmult.
    exists ranmult. split; try assumption. intros p Hp.
    apply Hranmult in Hp. destruct Hp as [mn [mnp [Hmnp H]]]. apply Hmult in H.
    destruct H as [mn' [p' [m [n [Mm [Hmnp' [Hmn [Hm [Hn [HMm Hp]]]]]]]]]].
    assert (T : mn = mn' /\ p = p').
    { apply (Enderton3A mn p mn' p' mnp mnp Hmnp Hmnp'). trivial. }
    replace mn' with mn in *; replace p' with p in *; try apply T.
    clear mn' p' Hmnp' T.
    destruct (HMm Hm) as [omga' [Am [o [Homga' [HAm [Ho HMm']]]]]].
    replace omga' with omga in *; try (apply Nats_Unique; assumption).
    clear omga' Homga'. destruct HMm' as [omga' [o' [Homga' [Ho' [HMm' _]]]]].
    replace omga' with omga in *; try (apply Nats_Unique; assumption).
    clear omga' Homga'. destruct HMm' as [HMm' [HdomMm [ranMm [HranMm Hsub]]]].
    apply Hsub. apply HranMm. exists n. apply Hp; try assumption.
    exists omga. split; try assumption. apply Homga. assumption.
Qed.

Ltac mult_w := destruct (Multiplication_w_Exists) as [mult Hmult].

Definition Prod_w (m n p : set) : Prop := NaturalNumber m -> NaturalNumber n ->
  exists mult mn mnp, Multiplication_w mult /\ OrdPair m n mn
  /\ OrdPair mn p mnp /\ In mnp mult.

Theorem Prod_w_Exists : forall m n, NaturalNumber m -> NaturalNumber n ->
  exists p, Prod_w m n p.
Proof.
  intros m n Hm Hn. mult_w. omga.
  destruct (Multiplication_w_BinaryOperation mult omga Hmult Homga) as [wxw [Hwxw H]].
  destruct H as [Hmultf [Hdommult [ranmult [Hranmult Hsub]]]].
  ordpair m n. rename x into mn. rename H into Hmn.
  assert (P : In mn wxw).
  { apply Hwxw. exists m, n. repeat (split; try apply Homga; try assumption). }
  apply Hdommult in P. destruct P as [p [mnp [Hmnp P]]].
  exists p. intros _ _. exists mult, mn, mnp. repeat (split; try assumption).
Qed.

Theorem Prod_w_Unique : forall m n p q, NaturalNumber m -> NaturalNumber n ->
  Prod_w m n p -> Prod_w m n q -> p = q.
Proof.
  intros m n p q Hm Hn Hp Hq. omga.
  destruct (Hp Hm Hn) as [mult [mn [mnp [Hmult [Hmn [Hmnp H]]]]]].
  destruct (Hq Hm Hn) as [mult' [mn' [mnq [Hmult' [Hmn' [Hmnq I]]]]]].
  replace mult' with mult in *;
    try (apply (Multiplication_w_Unique mult mult'); assumption).
  replace mn' with mn in *; try (apply (OrdPair_Unique m n mn mn'); assumption).
  clear mn' Hmult' Hmn' mult'.
  destruct (Multiplication_w_BinaryOperation mult omga Hmult Homga) as [wxw [Hwxw P]].
  destruct P as [Hmultf [Hdommult [ranmult [Hranmult Hsub]]]].
  destruct Hmultf as [_ Hmultf].
  apply (Hmultf mn p q mnp mnq Hmnp Hmnq H I).
Qed.

Ltac prod_w m n Hm Hn := destruct (Prod_w_Exists m n Hm Hn).

Definition M1 : Prop := forall m o, NaturalNumber m -> Empty o -> Prod_w m o o.

Definition M2 : Prop := forall m n mtn n' mtn' mpmtn, NaturalNumber m ->
  NaturalNumber n -> Prod_w m n mtn -> Succ n n' -> Prod_w m n' mtn' -> Sum_w m mtn mpmtn ->
  mtn' = mpmtn.

Theorem Enderton4J : M1 /\ M2.
Proof.
  split.
  - intros m o Hm Ho _ _. mult_w.
    ordpair m o. rename x into mo. rename H into Hmo. exists mult, mo.
    ordpair mo o. rename x into moo. rename H into Hmoo. exists moo.
    repeat (split; try assumption).
    destruct (Multn_Exists m Hm). rename x into Mm. rename H into HMm.
    apply Hmult. exists mo, o, m, o, Mm. repeat (split; try assumption).
    + apply (Zero_NaturalNumber). assumption.
    + destruct (HMm Hm) as [omga [Am [o' [Homga [HAm [Ho' HMm']]]]]].
      replace o' with o in *; try (apply Empty_Unique; assumption).
      clear o' Ho'. destruct HMm' as [omga' [o' [Homga' [Ho' [HMm' [HMmo _]]]]]].
      replace o' with o in *; try (apply Empty_Unique; assumption).
      clear o' Ho'. assumption.
  - intros m n mtn n' mtn' mpmtn Hm Hn Hmtn Hn' Hmtn' Hmpmtn.
    destruct (Hmtn Hm Hn) as [mult [mn [mnp [Hmult [Hmn [Hmnp H]]]]]].
    apply Hmult in H.
    destruct H as [mn' [mtn0 [m0 [n0 [Mm [Hmnp' [Hmn' [_ [_ [HMm Hp]]]]]]]]]].
    assert (T : mn = mn' /\ mtn = mtn0).
    { apply (Enderton3A mn mtn mn' mtn0 mnp mnp); try assumption. trivial. }
    replace mn' with mn in *; replace mtn0 with mtn in *; try apply T.
    clear T mn' mtn0 Hmnp'. assert (T : m = m0 /\ n = n0).
    { apply (Enderton3A m n m0 n0 mn mn Hmn Hmn'). trivial. }
    replace m0 with m in *; replace n0 with n in *; try apply T.
    clear T m0 n0 Hmn'. destruct (HMm Hm) as [omga [Am [o [Homga [HAm [Ho HMm']]]]]].
    destruct HMm' as [omga' [o' [Homga' [Ho' [HMm' [_ HMmn']]]]]].
    replace o' with o in *; try (apply Empty_Unique; assumption).
    clear o' Ho'.
    replace omga' with omga in *; try (apply Nats_Unique; assumption).
    clear omga' Homga'.
    apply (HMmn' n n' mtn mtn' mpmtn); try assumption; try apply Homga, Hn.
    + destruct (Hmtn' Hm) as [mult' [mn' [mn'p [Hmult' [Hmn' [Hmn'p I]]]]]];
        try (apply (Succ_NaturalNumber n n'); assumption).
      replace mult' with mult in *; try (apply Multiplication_w_Unique; assumption).
      clear mult' Hmult'. apply Hmult in I.
      destruct I as [mn'0 [mtn'0 [m0 [n'0 [Mm0 [Hmn'p' [Hmn'0 [_ [_ [HMm0 Hp']]]]]]]]]].
      assert (T : mn' = mn'0 /\ mtn' = mtn'0).
      { apply (Enderton3A mn' mtn' mn'0 mtn'0 mn'p mn'p); try assumption. trivial. }
      replace mn'0 with mn' in *; replace mtn'0 with mtn' in *; try apply T.
      clear mn'0 mtn'0 T Hmn'p'. assert (T : m = m0 /\ n' = n'0).
      { apply (Enderton3A m n' m0 n'0 mn' mn' Hmn' Hmn'0). trivial. }
      replace m0 with m in *; replace n'0 with n' in *; try apply T.
      clear m0 n'0 T Hmn'0. replace Mm with Mm0; try assumption.
      apply (Multn_Unique m); try assumption.
    + destruct Hmpmtn as [add [mp [mpq [Hadd [Hmp [Hmpq I]]]]]]; try assumption.
      { destruct HMm' as [HMm' [HdomMm [ranMm [HranMm Hsub]]]].
        apply Homga. apply Hsub. apply HranMm. exists n.
        apply Hp; try assumption. exists omga. split; try assumption.
        apply Homga. assumption. }
      apply Hadd in I.
      destruct I as [mp' [mpmtn0 [m0 [mtn0 [Am' [Hmpq' [Hmn0 [_ [_ [HMm0 Hq]]]]]]]]]].
      assert (T : mp = mp' /\ mpmtn = mpmtn0).
      { apply (Enderton3A mp mpmtn mp' mpmtn0 mpq mpq); try assumption. trivial. }
      replace mp' with mp in *; replace mpmtn0 with mpmtn in *; try apply T.
      clear mp' mpmtn0 T Hmpq'. assert (T : m = m0 /\ mtn = mtn0).
      { apply (Enderton3A m mtn m0 mtn0 mp mp); try assumption. trivial. }
      replace mtn0 with mtn in *; replace m0 with m in *; try apply T.
      clear mtn0 m0 T Hmn0. replace Am with Am'; try assumption.
      apply (Addn_Unique m); try assumption.
Qed.

Definition Expn (n En : set) : Prop :=
  NaturalNumber n -> exists omga Mn o o', Nats omga /\ Multn n Mn /\ Empty o /\
  Succ o o' /\ RecursiveFunction omga o' Mn En.

Theorem Expn_Exists : forall n, NaturalNumber n -> exists En, Expn n En.
Proof.
  intros n Hn. destruct (Multn_Exists n Hn) as [Mn HMn].
  destruct (HMn Hn) as [omga [An [o [Homga [HAn [Ho HMn']]]]]].
  destruct HMn' as [omga' [o' [Homga' [Ho' [HMn' [HMno HMnn']]]]]].
  replace omga' with omga in *; try (apply Nats_Unique; assumption).
  replace o' with o in *; try (apply Empty_Unique; assumption).
  clear o' Ho' omga' Homga'.
  succ o. rename x into o'. rename H into Ho'. assert (T : In o' omga).
  { apply Homga, (Succ_NaturalNumber o o'); try assumption.
    apply Zero_NaturalNumber. assumption. }
  recursion omga o' Mn T HMn'. rename x into En. rename H into HEn.
  exists En. intros _. exists omga, Mn, o, o'. repeat (split; try assumption).
Qed.

Theorem Expn_Unique : forall n En Fn, NaturalNumber n ->
  Expn n En -> Expn n Fn -> En = Fn.
Proof.
  intros n En Fn Hn HEn HFn.
  destruct (HEn Hn) as [omga [Mn [o [o' [Homga [HMn [Ho [Ho' HEn']]]]]]]].
  destruct (HFn Hn) as [omga' [Nn [o0 [o'0 [Homga' [HNn [Ho0 [Ho'0 HFn']]]]]]]].
  replace o0 with o in *; try (apply Empty_Unique; assumption).
  replace o'0 with o' in *; try (apply (Succ_Unique o); assumption).
  replace omga' with omga in *; try (apply Nats_Unique; assumption).
  clear omga' Homga' o0 Ho0 o'0 Ho'0.
  replace Nn with Mn in *; try
    (apply (RecursiveFunction_Unique omga o' Mn En);
    try assumption).
  - apply Homga. apply (Succ_NaturalNumber o o'); try assumption.
    apply Zero_NaturalNumber, Ho.
  - destruct (HMn Hn) as [omga' [An [o0 [Homga' [HAn [Ho0 HMn']]]]]].
    replace omga' with omga in *; try (apply Nats_Unique; assumption).
    replace o0 with o in *; try (apply Empty_Unique; assumption).
    clear omga' Homga' o0 Ho0. destruct HMn' as [omga' [o0 [Homga' [Ho0 [HMn' _]]]]].
    replace omga' with omga in *; try (apply Nats_Unique; assumption).
    replace o0 with o in *; try (apply Empty_Unique; assumption).
    assumption.
  - apply (Multn_Unique n Mn Nn Hn); assumption.
Qed.

Definition Exponentiation_w (exp : set) : Prop :=
  forall mnp, In mnp exp <-> exists mn p m n Em, OrdPair mn p mnp /\
  OrdPair m n mn /\ NaturalNumber m /\ NaturalNumber n /\ Expn m Em /\
  FunVal Em n p.

Theorem Exponentiation_w_Exists : exists exp, Exponentiation_w exp.
Proof.
  omga. prod omga omga. rename x into wxw. rename H into Hwxw.
  prod wxw omga. rename x into wxwxw. rename H into Hwxwxw.
  build_set
    set
    (fun (t c x : set) => exists mn p m n Em, OrdPair mn p x /\
      OrdPair m n mn /\ NaturalNumber m /\ NaturalNumber n /\ Expn m Em /\
      FunVal Em n p)
    omga
    wxwxw.
  rename x into exp. rename H into Hexp. exists exp.
  intros mnp. split; intros H; try apply Hexp; try apply H.
  split; try apply H.
  destruct H as [mn [p [m [n [En [Hmnp [Hmn [Hm [Hn [HEn H]]]]]]]]]].
  apply Hwxwxw. exists mn, p. repeat (split; try assumption).
  - apply Hwxw. exists m, n. repeat (split; try apply Homga; try assumption).
  - destruct (HEn Hm) as [omga' [Mn [o [o' [Homga' [HMn [Ho [Ho' HEn']]]]]]]].
    replace omga' with omga in *; try (apply Nats_Unique; assumption).
    clear omga' Homga'. destruct HEn' as [omga' [o'0 [Homga' [Ho'0 [HEn' _]]]]].
    replace omga' with omga in *; try (apply Nats_Unique; assumption).
    destruct HEn' as [HEn' [HdomEn [ranEn [HranEn Hsub]]]].
    apply Hsub. apply HranEn. exists n. apply H; try assumption.
    exists omga. split; try assumption. apply Homga, Hn.
Qed.

Theorem Exponentiation_w_Unique : forall exp exp',
  Exponentiation_w exp -> Exponentiation_w exp' -> exp = exp'.
Proof.
  intros exp exp' Hexp Hexp'.
  apply Extensionality_Axiom. intros mnp. split; intros H.
  - apply Hexp', Hexp, H.
  - apply Hexp, Hexp', H.
Qed.

Lemma Exponentiation_w_BinaryOperation : forall exp omga,
  Exponentiation_w exp -> Nats omga -> BinaryOperator exp omga.
Proof.
  intros exp omga Hexp Homga.
  prod omga omga. rename x into wxw. rename H into Hwxw.
  exists wxw. split; try assumption. split; split.
  - intros mnp Hmnp. apply Hexp in Hmnp.
    destruct Hmnp as [mn [p [m [n [En [Hmnp [Hmn [Hm [Hn [HEn Hp]]]]]]]]]].
    exists mn, p. assumption.
  - intros mn p q mnp mnq Hmnp Hmnq H I.
    apply Hexp in H.
    destruct H as [mn' [p' [m [n [En [Hmnp' [Hmn [Hm [Hn [HEn Hp]]]]]]]]]].
    assert (T : mn = mn' /\ p = p').
    { apply (Enderton3A mn p mn' p' mnp mnp Hmnp Hmnp'). trivial. }
    replace mn' with mn in *; replace p' with p in *; try apply T.
    clear mn' Hmnp' p' T. apply Hexp in I.
    destruct I as [mn' [q' [m' [n' [En' [Hmnq' [Hmn' [_ [_ [HEn' Hq]]]]]]]]]].
    assert (T : mn = mn' /\ q = q').
    { apply (Enderton3A mn q mn' q' mnq mnq Hmnq Hmnq'). trivial. }
    replace mn' with mn in *; replace q' with q in *; try apply T.
    clear mn' q' Hmnq' T.
    assert (T : m = m' /\ n = n').
    { apply (Enderton3A m n m' n' mn mn Hmn Hmn'). trivial. }
    replace m' with m in *; replace n' with n in *; try apply T.
    clear m' n' T Hmn'.
    replace En' with En in *; try (apply (Expn_Unique m En En'); assumption).
    clear En' HEn'.
    destruct (HEn Hm) as [omga' [Mn [o [o' [Homga' [HMn [Ho [Ho' HEn']]]]]]]].
    replace omga' with omga in *; try (apply Nats_Unique; assumption).
    clear omga' Homga'. destruct HEn' as [omga' [o0 [Homga' [Ho0 [HEn' _]]]]].
    apply (FunVal_Unique En n p q); try assumption; try apply HEn'.
    exists omga'. split. apply HEn'. apply Homga'. apply Hn.
  - intros mn. split; intros H.
    + apply Hwxw in H. destruct H as [m [n [Hm [Hn Hmn]]]].
      apply Homga in Hm. destruct (Expn_Exists m Hm).
      rename x into En. rename H into HEn.
      destruct (HEn Hm) as [omga' [Mn [o [o' [Homga' [HMn [Ho [Ho' HEn']]]]]]]].
      replace omga' with omga in *; try (apply Nats_Unique; assumption).
      clear omga' Homga'. destruct HEn' as [omga' [o0 [Homga' [Ho0 [HEn' _]]]]].
      replace omga' with omga in *; try (apply Nats_Unique; assumption).
      clear omga' Homga'. destruct HEn' as [HEn' [domEn' [ranEn' [HranEn' Hsub]]]].
      replace o0 with o in *; try (apply Empty_Unique; assumption).
      clear o0 Ho0. assert (P : exists domEn, Domain En domEn /\ In n domEn).
      { exists omga. split; try assumption. }
      funval HEn' P En n. rename x into p. rename H into Hp.
      destruct (Hp HEn' P) as [np [Hnp Hnp']].
      ordpair mn p. rename x into mnp. rename H into Hmnp.
      exists p, mnp. split; try assumption. apply Hexp.
      exists mn, p, m, n, En. repeat (split; try assumption).
      apply Homga; try assumption.
    + destruct H as [p [mnp [Hmnp H]]]. apply Hexp in H.
      destruct H as [mn' [p' [m [n [En [Hmnp' [Hmn [Hm [Hn [HEn Hp]]]]]]]]]].
      assert (T : mn = mn' /\ p = p').
      { apply (Enderton3A mn p mn' p' mnp mnp Hmnp Hmnp'). trivial. }
      replace mn' with mn in *; replace p' with p in *; try apply T.
      clear mn' p' Hmnp' T. apply Hwxw. exists m, n.
      repeat (split; try apply Homga; try assumption).
  - range exp. rename x into ranexp. rename H into Hranexp.
    exists ranexp. split; try assumption. intros p Hp.
    apply Hranexp in Hp. destruct Hp as [mn [mnp [Hmnp H]]]. apply Hexp in H.
    destruct H as [mn' [p' [m [n [En [Hmnp' [Hmn [Hm [Hn [HEn Hp]]]]]]]]]].
    assert (T : mn = mn' /\ p = p').
    { apply (Enderton3A mn p mn' p' mnp mnp Hmnp Hmnp'). trivial. }
    replace mn' with mn in *; replace p' with p in *; try apply T.
    clear mn' p' Hmnp' T.
    destruct (HEn Hm) as [omga' [Mn [o [o' [Homga' [HMn [Ho [Ho' HEn']]]]]]]].
    replace omga' with omga in *; try (apply Nats_Unique; assumption).
    clear omga' Homga'. destruct HEn' as [omga' [o0 [Homga' [Ho0 [HEn' _]]]]].
    replace omga' with omga in *; try (apply Nats_Unique; assumption).
    clear omga' Homga'. destruct HEn' as [HMm' [HdomEn [ranEn [HranEn Hsub]]]].
    apply Hsub. apply HranEn. exists n. apply Hp; try assumption.
    exists omga. split; try assumption. apply Homga. assumption.
Qed.

Ltac exp_w := destruct (Exponentiation_w_Exists) as [exp Hexp].

Definition Pow_w (m n p : set) : Prop := NaturalNumber m -> NaturalNumber n ->
  exists exp mn mnp, Exponentiation_w exp /\ OrdPair m n mn
  /\ OrdPair mn p mnp /\ In mnp exp.

Theorem Pow_w_Exists : forall m n, NaturalNumber m -> NaturalNumber n ->
  exists p, Pow_w m n p.
Proof.
  intros m n Hm Hn. exp_w. omga.
  destruct (Exponentiation_w_BinaryOperation exp omga Hexp Homga) as [wxw [Hwxw H]].
  destruct H as [Hmultf [Hdommult [ranmult [Hranmult Hsub]]]].
  ordpair m n. rename x into mn. rename H into Hmn.
  assert (P : In mn wxw).
  { apply Hwxw. exists m, n. repeat (split; try apply Homga; try assumption). }
  apply Hdommult in P. destruct P as [p [mnp [Hmnp P]]].
  exists p. intros _ _. exists exp, mn, mnp. repeat (split; try assumption).
Qed.

Theorem Pow_w_Unique : forall m n p q, NaturalNumber m -> NaturalNumber n ->
  Pow_w m n p -> Pow_w m n q -> p = q.
Proof.
  intros m n p q Hm Hn Hp Hq. omga.
  destruct (Hp Hm Hn) as [exp [mn [mnp [Hexp [Hmn [Hmnp H]]]]]].
  destruct (Hq Hm Hn) as [exp' [mn' [mnq [Hexp' [Hmn' [Hmnq I]]]]]].
  replace exp' with exp in *;
    try (apply (Exponentiation_w_Unique exp exp'); assumption).
  replace mn' with mn in *; try (apply (OrdPair_Unique m n mn mn'); assumption).
  clear mn' Hexp' Hmn' exp'.
  destruct (Exponentiation_w_BinaryOperation exp omga Hexp Homga) as [wxw [Hwxw P]].
  destruct P as [Hexpf [Hdomexp [ranexp [Hranexp Hsub]]]].
  destruct Hexpf as [_ Hexpf].
  apply (Hexpf mn p q mnp mnq Hmnp Hmnq H I).
Qed.

Ltac pow_w m n Hm Hn := destruct (Pow_w_Exists m n Hm Hn).

Definition E1 : Prop := forall m o o', NaturalNumber m -> Empty o ->
  Succ o o' -> Pow_w m o o'.

Definition E2 : Prop := forall m n men n' men' mtmen, NaturalNumber m ->
  NaturalNumber n -> Pow_w m n men -> Succ n n' -> Pow_w m n' men' ->
  Prod_w m men mtmen -> men' = mtmen.

Theorem Enderton4J' : E1 /\ E2.
Proof.
  split.
  - intros m o o' Hm Ho Ho'. assert (P : NaturalNumber o).
    { apply Zero_NaturalNumber. assumption. }
    assert (Q : NaturalNumber o').
    { apply (Succ_NaturalNumber o o'); assumption. }
    intros _ _. exp_w. ordpair m o. rename x into mo. rename H into Hmo.
    ordpair mo o'. rename x into moo'. rename H into Hmoo'.
    exists exp, mo, moo'. repeat (split; try assumption).
    apply Hexp. destruct (Expn_Exists m Hm). rename x into Em. rename H into HEm.
    exists mo, o', m, o, Em. repeat (split; try assumption). intros _ _.
    ordpair o o'. rename x into oo'. rename H into Hoo'.
    exists oo'. split; try assumption.
    destruct (HEm Hm) as [omga [Mm [o0 [o'0 [Homga [HMm [Ho0 [Ho'0 HEm']]]]]]]].
    replace o0 with o in *; try (apply Empty_Unique; assumption).
    replace o'0 with o' in *; try (apply (Succ_Unique o); assumption).
    clear o0 o'0 Ho0 Ho'0.
    destruct HEm' as [omga' [o0 [Homga' [Ho0 [HEm' [HEmo _]]]]]].
    replace o0 with o in *; try (apply Empty_Unique; assumption).
    replace omga' with omga in *; try (apply Nats_Unique; assumption).
    destruct HEmo as [oo'0 [Hoo'0 Hoo'0']].
    { apply HEm'. }
    { exists omga. split. apply HEm'. apply Homga, Zero_NaturalNumber, Ho. }
    replace oo' with oo'0; try assumption.
    apply (OrdPair_Unique o o'); try assumption.
  - intros m n men n' men' mtmen Hm Hn Hmen Hn' Hmen' Hmentm.
    destruct (Hmen Hm Hn) as [exp [mn [mnp [Hexp [Hmn [Hmnp H]]]]]].
    apply Hexp in H.
    destruct H as [mn' [p' [m' [n0 [Em [Hmnp' [Hmn' [_ [_ [HEm Hp]]]]]]]]]].
    assert (T : mn = mn' /\ men = p').
    { apply (Enderton3A mn men mn' p' mnp mnp Hmnp Hmnp'). trivial. }
    replace mn' with mn in *; replace p' with men in *; try apply T.
    clear mn' p' T Hmnp'. assert (T : m = m' /\ n = n0).
    { apply (Enderton3A m n m' n0 mn mn Hmn Hmn'). trivial. }
    replace m' with m in *; replace n0 with n in *; try apply T.
    clear m' n0 T Hmn'.
    destruct (Hmen' Hm) as [exp' [mn' [mn'p [Hexp' [Hmn' [Hmn'p H]]]]]].
    { apply (Succ_NaturalNumber n n'); assumption. }
    apply Hexp' in H.
    destruct H as [mn'' [p' [m' [n0 [Em' [Hmn'p' [Hmn'' [_ [_ [HEm' Hp']]]]]]]]]].
    assert (T : mn' = mn'' /\ men' = p').
    { apply (Enderton3A mn' men' mn'' p' mn'p mn'p Hmn'p Hmn'p'). trivial. }
    replace mn'' with mn' in *; replace p' with men' in *; try apply T.
    clear mn'' p' T Hmn'p'. assert (T : m = m' /\ n' = n0).
    { apply (Enderton3A m n' m' n0 mn' mn' Hmn' Hmn''). trivial. }
    replace m' with m in *; replace n0 with n' in *; try apply T.
    replace Em' with Em in *; try (apply (Expn_Unique m); assumption).
    clear m' n0 T Hmn'' Em' HEm'.
    destruct (HEm Hm) as [omga [Mm [o [o' [Homga [HMm' [Ho [Ho' HEm']]]]]]]].
    destruct HEm' as [omga' [o0 [Homga' [Ho0 [HEm' [_ HEmn']]]]]].
    replace omga' with omga in *; try (apply (Nats_Unique); assumption).
    apply (HEmn' n n' men men' mtmen); try apply Homga; try assumption.
    destruct (Hmentm Hm) as [mult [mp [mpq [Hmult [Hmp [Hmpq H]]]]]].
    { destruct HEm' as [HEm' [HdomEm [ranEm [HranEm Hsub]]]]. apply Homga, Hsub.
      apply HranEm. exists n. apply Hp; try assumption.
      exists omga. split; try assumption. apply Homga; assumption. }
    apply Hmult in H.
    destruct H as [mp' [q' [m' [p' [Mm' [Hmpq' [Hmp' [_ [Hp0 [HMm0 Hp1]]]]]]]]]].
    assert (T : mp = mp' /\ mtmen = q').
    { apply (Enderton3A mp mtmen mp' q' mpq mpq Hmpq Hmpq'). trivial. }
    replace mp' with mp in *; replace q' with mtmen in *; try apply T.
    clear Hmpq' T mp' q'.
    assert (T : m = m' /\ men = p').
    { apply (Enderton3A m men m' p' mp mp Hmp Hmp'). trivial. }
    replace m' with m in *; replace p' with men in *; try apply T.
    clear m' p' Hmp' T. replace Mm with Mm'; try assumption.
    apply (Multn_Unique m); assumption.
Qed.

Definition Addition_Associative_w : Prop :=
  forall m n p np mn r l, NaturalNumber m -> NaturalNumber n -> NaturalNumber p ->
  Sum_w n p np -> Sum_w m n mn -> Sum_w m np r -> Sum_w mn p l -> r = l.

Definition Addition_Commutative_w : Prop :=
  forall m n mn nm, NaturalNumber m -> NaturalNumber n -> Sum_w m n mn ->
  Sum_w n m nm -> mn = nm.

Definition Distributive_w : Prop :=
  forall m n p np mnp mn mp mnmp, NaturalNumber m ->  NaturalNumber n ->
  NaturalNumber p -> Sum_w n p np -> Prod_w m np mnp -> Prod_w m n mn -> Prod_w m p mp ->
  Sum_w mn mp mnmp -> mnp = mnmp.

Definition Multiplication_Associative_w : Prop :=
  forall m n p np mn r l, NaturalNumber m -> NaturalNumber n -> NaturalNumber p ->
  Prod_w n p np -> Prod_w m n mn -> Prod_w m np r -> Prod_w mn p l -> r = l.

Definition Multiplication_Commutative_w : Prop :=
  forall m n mn nm, NaturalNumber m -> NaturalNumber n -> Prod_w m n mn ->
  Prod_w n m nm -> mn = nm.

Theorem Enderton4K1 : Addition_Associative_w.
Proof.
  intros m n p np mn r l Hm Hn Hp. generalize dependent l. generalize dependent r.
  generalize dependent mn. generalize dependent np. omga.
  build_set (prod set set)
    (fun (t : set * set) (c p : set) => forall np mn r l, Sum_w (snd t) p np ->
      Sum_w (fst t) (snd t) mn -> Sum_w (fst t) np r -> Sum_w mn p l -> r = l)
    (m, n) omga.
  rename x into A. rename H into HA. apply HA.
  replace A with omga; try (apply Homga; assumption).
  symmetry. apply Induction_Principle_for_Omega; try assumption; try split.
  - empty. rename x into e. rename H into He.
    exists e. split; try assumption. apply HA. split.
    + apply Homga, Zero_NaturalNumber, He.
    + intros np mn r l Hnp Hmn Hr Hl. simpl in *.
      destruct (Enderton4I) as [A1 A2]. replace l with mn in *.
      replace np with n in *. apply (Sum_w_Unique m n r mn); try assumption.
      * apply (Sum_w_Unique n e n np); try assumption;
        try apply Zero_NaturalNumber, He. apply (A1 n e); assumption.
      * destruct Hmn as [add [Pmn [Pmnp [Hadd [HPmn [HPmnp H]]]]]]; try assumption.
        destruct (Addition_w_BinaryOperation add omga) as [wxw [Hwxw Haddf]];
        try assumption.
        destruct Haddf as [Haddf [Hdomadd [ranadd [Hranadd Hsub]]]].
        apply (Sum_w_Unique mn e mn l); try assumption;
        try apply Zero_NaturalNumber, He.
        apply Homga, Hsub. apply Hranadd. exists Pmn, Pmnp. split; try assumption.
        apply (A1 mn e); try assumption.
        apply Homga, Hsub, Hranadd. exists Pmn, Pmnp. split; try assumption.
  - intros a a' Ha' Ha. apply HA in Ha. destruct Ha as [Ha0 Ha1].
    apply Homga in Ha0. apply HA.
    split; try (apply Homga, (Succ_NaturalNumber a a'); assumption).
    intros np mn r l Hnp Hmn Hr Hl. simpl in *.
    sum_w n a Hn Ha0. rename x into na. rename H into Hna.
    assert (P : NaturalNumber na).
    { apply Homga.
      destruct Hna as [add [Pmn [Pmnp [Hadd [HPmn [HPmnp H]]]]]]; try assumption.
      destruct (Addition_w_BinaryOperation add omga) as [wxw [Hwxw Haddf]]; try assumption.
      destruct Haddf as [Haddf [Hdomadd [ranadd [Hranadd Hsub]]]].
      apply Hsub. apply Hranadd. exists Pmn, Pmnp. split; try assumption. }
    sum_w m na Hm P. rename x into mna. rename H into Hmna.
    succ mna. rename x into Smna. rename H into HSmna. transitivity Smna.
    + succ na. rename x into Sna. rename H into HSna.
      assert (Q : NaturalNumber Sna).
      { apply (Succ_NaturalNumber na Sna); try assumption. }
      sum_w m Sna Hm Q. rename x into mSna. rename H into HmSna.
      transitivity mSna.
      * apply (Sum_w_Unique m Sna r mSna); try assumption.
        replace Sna with np; try assumption.
        destruct (Enderton4I) as [_ R].
        apply (R n a a' na np Sna); try assumption.
      * destruct Enderton4I as [_ R].
        apply (R m na Sna mna mSna Smna); try assumption.
    + assert (Q : NaturalNumber mn).
      { apply Homga.
        destruct Hmn as [add [Pmn [Pmnp [Hadd [HPmn [HPmnp H]]]]]]; try assumption.
        destruct (Addition_w_BinaryOperation add omga) as [wxw [Hwxw Haddf]]; try assumption.
        destruct Haddf as [Haddf [Hdomadd [ranadd [Hranadd Hsub]]]].
        apply Hsub. apply Hranadd. exists Pmn, Pmnp. split; try assumption. }
      sum_w mn a Q Ha0. rename x into mna0. rename H into Hmna0.
      succ mna0. rename x into Smna0. rename H into HSmna0.
      transitivity Smna0.
      * apply (Succ_Unique mna Smna Smna0); try assumption.
        replace mna with mna0; try assumption. symmetry.
        apply (Ha1 na mn mna mna0); try assumption.
      * destruct Enderton4I as [_ R]. symmetry.
        apply (R mn a a' mna0); try assumption.
  - intros a Ha. apply HA; assumption.
Qed.

Lemma A1_Commutative : forall o n, Empty o -> NaturalNumber n ->
  Sum_w o n n.
Proof.
  intros o n Ho Hn. generalize dependent n. omga.
  build_set
    set
    (fun (o c n : set) => NaturalNumber n -> Sum_w o n n)
    o
    omga.
  rename x into A. rename H into HA. intros n Hn. apply HA; try assumption.
  replace A with omga; try apply Homga, Hn; try assumption.
  symmetry. apply Induction_Principle_for_Omega; try assumption; try split.
  - exists o. split; try assumption. apply HA.
    split; try apply Homga, Zero_NaturalNumber, Ho.
    intros Ho'. destruct Enderton4I as [A1 _].
    apply A1; try assumption.
  - intros a a' Ha' Ha. apply HA. apply HA in Ha. destruct Ha as [Ha IH].
    apply Homga in Ha.
    split; try (apply Homga, (Succ_NaturalNumber a a'); try assumption).
    intros Ha'0. sum_w o a (Zero_NaturalNumber o Ho) Ha.
    rename x into oa. rename H into Hoa.
    succ oa. rename x into Soa. rename H into HSoa.
    sum_w o a' (Zero_NaturalNumber o Ho) Ha'0. rename x into oa'. rename H into Hoa'.
    replace oa' with a' in Hoa'; try assumption. transitivity Soa.
    + apply (Succ_Unique a a' Soa); try assumption.
      replace a with oa; try assumption.
      apply (Sum_w_Unique o a oa a); try apply (Zero_NaturalNumber o); try assumption.
      apply IH; assumption.
    + destruct Enderton4I as [_ P]. symmetry.
      apply (P o a a' oa oa' Soa); try assumption.
      apply Zero_NaturalNumber. assumption.
  - intros a Ha. apply HA, Ha.
Qed.

Lemma A2_Commutative : forall m n m' mn m'n mn', NaturalNumber m ->
  NaturalNumber n -> Succ m m' -> Sum_w m n mn -> Sum_w m' n m'n -> Succ mn mn' ->
  m'n = mn'.
Proof.
  intros m n m' mn m'n mn' Hm Hn. omga. generalize dependent mn'.
  generalize dependent m'n. generalize dependent mn. generalize dependent m'.
  build_set set
    (fun (m c n : set) => forall m' mn m'n mn',
      Succ m m' -> Sum_w m n mn -> Sum_w m' n m'n -> Succ mn mn' -> m'n = mn')
    m omga.
  rename x into A. rename H into HA. apply HA.
  replace A with omga; try apply Homga, Hn. symmetry.
  apply Induction_Principle_for_Omega; try assumption; try split.
  - empty. exists x. split; try assumption. rename x into o. rename H into Ho.
    apply HA. split; try (apply Homga; apply Zero_NaturalNumber; assumption).
    intros m' mn m'n mn' Hm' Hmn Hm'n Hmn'.
    replace mn with m in *. replace m'n with m' in *.
    apply (Succ_Unique m m' mn'); try assumption.
    + apply (Sum_w_Unique m' o m' m'n); try assumption;
      try (apply Zero_NaturalNumber; assumption);
      try (apply (Succ_NaturalNumber m m'); assumption).
      destruct Enderton4I as [A1 _]. apply A1; try assumption;
      try (apply (Succ_NaturalNumber m m'); assumption).
    + apply (Sum_w_Unique m o m mn); try assumption;
      try (apply Zero_NaturalNumber; assumption).
      destruct Enderton4I as [A1 _]. apply A1; assumption.
  - intros a a' Ha' Ha. apply HA in Ha. destruct Ha as [Ha IH]. apply Homga in Ha.
    apply HA. split; try (apply Homga, (Succ_NaturalNumber a a'); assumption).
    intros m' mn m'n mn' Hm' Hmn Hm'n Hmn'.
    assert (P : NaturalNumber m').
    { apply (Succ_NaturalNumber m m'); try assumption. }
    sum_w m' a P Ha. rename x into m'a. rename H into Hm'a.
    succ m'a. rename x into Sm'a. rename H into HSm'a.
    transitivity Sm'a.
    + destruct Enderton4I as [_ A2].
      apply (A2 m' a a' m'a m'n Sm'a); try assumption.
    + sum_w m a Hm Ha. rename x into ma. rename H into Hma.
      succ ma. rename x into Sma. rename H into HSma.
      succ Sma. rename x into SSma. rename H into HSSma. transitivity SSma.
      * apply (Succ_Unique m'a Sm'a SSma); try assumption.
        replace m'a with Sma; try assumption.
        symmetry. apply (IH m' ma m'a Sma); try assumption.
      * apply (Succ_Unique mn SSma mn'); try assumption.
        replace mn with Sma; try assumption.
        destruct Enderton4I as [_ A2]. symmetry.
        apply (A2 m a a' ma); try assumption.
  - intros a Ha. apply HA, Ha.
Qed.

Theorem Enderton4K2 : Addition_Commutative_w.
Proof.
  intros m n mn nm Hm Hn. omga. generalize dependent nm. generalize dependent mn.
  build_set set
    (fun (m c n : set) => forall mn nm, Sum_w m n mn -> Sum_w n m nm -> mn = nm)
    m omga.
  rename x into A. rename H into HA. apply HA.
  replace A with omga; try apply Homga, Hn. symmetry.
  apply Induction_Principle_for_Omega; try assumption; try split;
  try (intros a Ha; apply HA, Ha).
  - empty. rename x into o. rename H into Ho. exists o. split; try assumption.
    apply HA. split; try (apply Homga, Zero_NaturalNumber; assumption).
    intros mn nm Hmn Hnm. replace mn with m in *. replace nm with m in *.
    trivial.
    + apply (Sum_w_Unique o m m nm); try assumption;
      try (apply Zero_NaturalNumber, Ho).
      apply (A1_Commutative); assumption.
    + apply (Sum_w_Unique m o m mn); try assumption;
      try (apply Zero_NaturalNumber, Ho).
      destruct Enderton4I as [A1 _].
      apply A1; assumption.
  - intros a a' Ha' Ha. apply HA in Ha. destruct Ha as [Ha IH]. apply Homga in Ha.
    apply HA. split; try (apply Homga, (Succ_NaturalNumber a a'); assumption).
    intros mn nm Hmn Hnm.
    sum_w a m Ha Hm. rename x into am. rename H into Ham.
    sum_w m a Hm Ha. rename x into ma. rename H into Hma.
    succ am. rename x into Sam. rename H into HSam.
    succ ma. rename x into Sma. rename H into HSma.
    transitivity Sma.
    + destruct Enderton4I as [_ A2].
      apply (A2 m a a' ma mn Sma); try assumption.
    + transitivity Sam.
      * apply (Succ_Unique ma Sma Sam); try assumption.
        replace ma with am; try assumption.
        symmetry. apply IH; try assumption.
      * symmetry. apply (A2_Commutative a m a' am nm Sam); try assumption.
Qed.

Lemma Sum_NaturalNumber : forall n m p, NaturalNumber n -> NaturalNumber m ->
  Sum_w n m p -> NaturalNumber p.
Proof.
  intros n m p Hn Hm Hp. omga.
  destruct (Hp Hn Hm) as [add [mn [mnp [Hadd [Hmn [Hmnp H]]]]]].
  destruct (Addition_w_BinaryOperation add omga) as [wxw [Hwxw Hfadd]]; try assumption.
  destruct Hfadd as [Hfadd [Hdomadd [ranadd [Hranadd Hsub]]]].
  apply Homga, Hsub, Hranadd. exists mn, mnp. split; assumption.
Qed.

Lemma Prod_NaturalNumber : forall n m p, NaturalNumber n -> NaturalNumber m ->
  Prod_w n m p -> NaturalNumber p.
Proof.
  intros n m p Hn Hm Hp. omga.
  destruct (Hp Hn Hm) as [mult [mn [mnp [Hadd [Hmn [Hmnp H]]]]]].
  destruct (Multiplication_w_BinaryOperation mult omga) as [wxw [Hwxw Hfmult]]; try assumption.
  destruct Hfmult as [Hfmult [Hdommult [ranmult [Hranmult Hsub]]]].
  apply Homga, Hsub, Hranmult. exists mn, mnp. split; assumption.
Qed.

Theorem Enderton4K3 : Distributive_w.
Proof.
  intros m n p np mnp mn mp mnmp Hm Hn Hp. omga.
  generalize dependent mnmp. generalize dependent mp. generalize dependent mn.
  generalize dependent mnp. generalize dependent np.
  build_set (prod set set)
    (fun (t : set * set) (c p : set) => forall np mnp mn mp mnmp,
      Sum_w (snd t) p np -> Prod_w (fst t) np mnp -> Prod_w (fst t) (snd t) mn ->
      Prod_w (fst t) p mp -> Sum_w mn mp mnmp -> mnp = mnmp)
    (m, n) omga.
  rename x into T. rename H into HT. apply HT.
  replace T with omga; try (apply Homga, Hp). symmetry.
  apply Induction_Principle_for_Omega; try assumption; try split;
  try (intros a Ha; apply HT, Ha).
  - zero. rename x into o. rename H into Ho. exists o. split; try assumption.
    apply HT. split; try (apply Homga, Zero_NaturalNumber, Ho).
    intros np mnp mn mp mnmp Hnp Hmnp Hmn Hmp Hmnmp. simpl in *.
    replace np with n in *. replace mp with o in *. replace mnmp with mn in *.
    apply (Prod_w_Unique m n mnp mn); try assumption.
    + destruct Enderton4I as [A1 A2].
      apply (Sum_w_Unique mn o mn mnmp); try assumption.
      * destruct (Hmn Hm Hn) as [mult [Pmn [Pmnp [Hmult [HPmn [HPmnp H]]]]]].
        destruct (Multiplication_w_BinaryOperation mult omga) as [wxw [Hwxw Hfmult]];
        try assumption.
        destruct Hfmult as [Hfmult [Hdommult [ranmult [Hranmult Hsub]]]].
        apply Homga, Hsub, Hranmult. exists Pmn, Pmnp. split; assumption.
      * apply Zero_NaturalNumber, Ho.
      * apply A1; try assumption.
        destruct (Hmn Hm Hn) as [mult [Pmn [Pmnp [Hmult [HPmn [HPmnp H]]]]]].
        destruct (Multiplication_w_BinaryOperation mult omga) as [wxw [Hwxw Hfmult]];
        try assumption.
        destruct Hfmult as [Hfmult [Hdommult [ranmult [Hranmult Hsub]]]].
        apply Homga, Hsub, Hranmult. exists Pmn, Pmnp. split; assumption.
    + apply (Prod_w_Unique m o o mp); try assumption; try (apply Zero_NaturalNumber, Ho).
      destruct Enderton4J as [M1 M2]. apply M1; assumption.
    + destruct (Sum_w_Unique n o n np); try assumption; try trivial;
      try (apply Zero_NaturalNumber, Ho).
      destruct Enderton4I as [A1 A2]. apply A1; assumption.
  - clear p Hp. intros p p' Hp' Hp. apply HT in Hp. destruct Hp as [Hp IH].
    apply HT. apply Homga in Hp.
    split; try (apply Homga, (Succ_NaturalNumber p p'); assumption).
    intros np' mnp' mn mp' mnmp' Hnp' Hmnp' Hmn Hmp' Hmnmp'. simpl in *.
    prod_w m p Hm Hp. rename H into Hmp. rename x into mp.
    sum_w mn mp (Prod_NaturalNumber m n mn Hm Hn Hmn)
      (Prod_NaturalNumber m p mp Hm Hp Hmp).
    rename H into Hmnmp. rename x into mnmp.
    sum_w m mnmp Hm (Sum_NaturalNumber mn mp mnmp
      (Prod_NaturalNumber m n mn Hm Hn Hmn)
      (Prod_NaturalNumber m p mp Hm Hp Hmp) Hmnmp).
    rename x into mmnmp. rename H into Hmmnmp. transitivity mmnmp.
    + sum_w n p Hn Hp. rename x into np. rename H into Hnp.
      prod_w m np Hm (Sum_NaturalNumber n p np Hn Hp Hnp).
      rename x into mnp. rename H into Hmnp.
      sum_w m mnp Hm
        (Prod_NaturalNumber m np mnp Hm (Sum_NaturalNumber n p np Hn Hp Hnp) Hmnp).
      rename x into mmnp. rename H into Hmmnp. transitivity mmnp.
      * succ np. rename x into Snp. rename H into HSnp.
        prod_w m Snp Hm (Succ_NaturalNumber np Snp (Sum_NaturalNumber n p np Hn Hp Hnp) HSnp).
        rename x into mSnp. rename H into HmSnp. transitivity mSnp.
        { apply (Prod_w_Unique m np' mnp' mSnp); try assumption;
          try apply (Sum_NaturalNumber n p' np' Hn (Succ_NaturalNumber p p' Hp Hp') Hnp').
          replace np' with Snp; try assumption.
          destruct Enderton4I as [A1 A2]. symmetry.
          apply (A2 n p p' np); assumption. }
        { destruct Enderton4J as [M1 M2]. apply (M2 m np mnp Snp); try assumption.
          apply (Sum_NaturalNumber n p np Hn Hp Hnp). }
      * apply (Sum_w_Unique m mnp mmnp mmnmp); try assumption;
        try apply (Prod_NaturalNumber m np mnp Hm 
          (Sum_NaturalNumber n p np Hn Hp Hnp) Hmnp).
        replace mnp with mnmp; try assumption.
        symmetry; apply (IH np mnp mn mp mnmp); assumption.
    + sum_w mnmp m (Sum_NaturalNumber mn mp mnmp
        (Prod_NaturalNumber m n mn Hm Hn Hmn)
        (Prod_NaturalNumber m p mp Hm Hp Hmp) Hmnmp) Hm.
      rename x into mnmpm. rename H into Hmnmpm. transitivity mnmpm.
      * apply (Sum_w_Unique m mnmp mmnmp mnmpm); try assumption.
        { apply (Sum_NaturalNumber mn mp); try assumption.
          - apply (Prod_NaturalNumber m n); try assumption.
          - apply (Prod_NaturalNumber m p); try assumption. }
        replace mnmpm with mmnmp; try assumption.
        apply (Enderton4K2 m mnmp mmnmp mnmpm); try assumption.
        apply (Sum_NaturalNumber mn mp); try assumption.
        apply (Prod_NaturalNumber m n); try assumption.
        apply (Prod_NaturalNumber m p); try assumption.
      * sum_w mp m (Prod_NaturalNumber m p mp Hm Hp Hmp) Hm.
        rename x into mpm. rename H into Hmpm.
        sum_w mn mpm (Prod_NaturalNumber m n mn Hm Hn Hmn)
          (Sum_NaturalNumber mp m mpm (Prod_NaturalNumber m p mp Hm Hp Hmp) Hm Hmpm).
        rename x into mnmpm'. rename H into Hmnmpm'. transitivity mnmpm'.
        { symmetry. apply (Enderton4K1 mn mp m mpm mnmp); try assumption.
          - apply (Prod_NaturalNumber m n mn Hm Hn Hmn).
          - apply (Prod_NaturalNumber m p mp Hm Hp Hmp). }
        { apply (Sum_w_Unique mn mpm mnmpm' mnmp'); try assumption.
          - apply (Prod_NaturalNumber m n mn Hm Hn Hmn).
          - apply (Sum_NaturalNumber mp m); try assumption.
            apply (Prod_NaturalNumber m p); try assumption.
          - replace mpm with mp'; try assumption.
            sum_w m mp Hm (Prod_NaturalNumber m p mp Hm Hp Hmp).
            rename x into mmp. rename H into Hmmp. transitivity mmp.
            + destruct Enderton4J as [M1 M2]. apply (M2 m p mp p'); try assumption.
            + apply (Enderton4K2 m mp mmp mpm);  try assumption.
              apply (Prod_NaturalNumber m p); try assumption. }
Qed.

Theorem Enderton4K4 : Multiplication_Associative_w.
Proof.
  intros m n p np mn r l Hm Hn Hp. omga.
  generalize dependent l. generalize dependent r. generalize dependent mn.
  generalize dependent np. build_set (prod set set)
    (fun (t : set * set) (c p : set) => forall np mn r l, Prod_w (snd t) p np ->
      Prod_w (fst t) (snd t) mn -> Prod_w (fst t) np r -> Prod_w mn p l -> r = l)
    (m,n) omga.
  rename x into T. rename H into HT. apply HT.
  replace T with omga; try (apply Homga, Hp). symmetry. clear p Hp.
  apply Induction_Principle_for_Omega; try assumption; try split;
  try (intros a Ha; apply HT, Ha).
  - zero. rename x into o. rename H into Ho. exists o. split; try assumption.
    apply HT. split; try (apply Homga, Zero_NaturalNumber, Ho).
    intros np mn r l Hnp Hmn Hr Hl. simpl in *.
    destruct (Enderton4J) as [M1 M2].
    replace np with o in *. replace l with o in *.
    replace r with o in *. trivial.
    + apply (Prod_w_Unique m o o r); try assumption;
      try apply (Zero_NaturalNumber), Ho.
      apply M1; try assumption.
    + apply (Prod_w_Unique mn o o l); try apply (Zero_NaturalNumber), Ho;
      try apply (Prod_NaturalNumber m n); try assumption.
      apply M1; try assumption.
      apply (Prod_NaturalNumber m n); try assumption.
    + apply (Prod_w_Unique n o o np); try assumption;
      try apply Zero_NaturalNumber; try assumption.
      apply M1; assumption.
  - intros p p' Hp' Hp. apply HT in Hp. destruct Hp as [Hp IH].
    apply HT. apply Homga in Hp.
    split; try (apply Homga, (Succ_NaturalNumber p p'); assumption).
    intros np' mn r l Hnp' Hmn Hr Hl. simpl in *.
    prod_w n p Hn Hp. rename x into np. rename H into Hnp.
    prod_w m np Hm (Prod_NaturalNumber n p np Hn Hp Hnp).
    rename x into mnp. rename H into Hmnp.
    sum_w mn mnp (Prod_NaturalNumber m n mn Hm Hn Hmn)
      (Prod_NaturalNumber m np mnp Hm (Prod_NaturalNumber n p np Hn Hp Hnp) Hmnp).
    rename x into mnmnp. rename H into Hmnmnp. transitivity mnmnp.
    + sum_w n np Hn (Prod_NaturalNumber n p np Hn Hp Hnp).
      rename x into nnp. rename H into Hnnp.
      prod_w m nnp Hm (Sum_NaturalNumber n np nnp Hn
        (Prod_NaturalNumber n p np Hn Hp Hnp) Hnnp).
      rename x into mnnp. rename H into Hmnnp. transitivity mnnp.
      * destruct Enderton4J as [M1 M2].
        apply (Prod_w_Unique m np' r mnnp); try assumption.
        { apply (Prod_NaturalNumber n p'); try assumption.
          apply (Succ_NaturalNumber p p'); try assumption. }
        replace np' with nnp; try assumption.
        symmetry. apply (M2 n p np p' np'); try assumption.
      * apply (Enderton4K3 m n np nnp mnnp mn mnp mnmnp); try assumption.
        apply (Prod_NaturalNumber n p); try assumption.
    + prod_w mn p (Prod_NaturalNumber m n mn Hm Hn Hmn) Hp.
      rename x into mnp0. rename H into Hmnp0.
      sum_w mn mnp0 (Prod_NaturalNumber m n mn Hm Hn Hmn)
        (Prod_NaturalNumber mn p mnp0 (Prod_NaturalNumber m n mn Hm Hn Hmn) Hp Hmnp0).
      rename x into mnmnp0. rename H into Hmnmnp0. transitivity mnmnp0.
      * apply (Sum_w_Unique mn mnp mnmnp mnmnp0); try assumption.
        { apply (Prod_NaturalNumber m n); try assumption. }
        { apply (Prod_NaturalNumber m np); try assumption.
          apply (Prod_NaturalNumber n p); try assumption. }
        replace mnp with mnp0; try assumption.
        symmetry. apply (IH np mn mnp mnp0); try assumption.
      * destruct Enderton4J as [M1 M2]. symmetry.
        apply (M2 mn p mnp0 p'); try assumption.
        apply (Prod_NaturalNumber m n); assumption.
Qed.

Lemma M1_Commutative : forall o m, Empty o -> NaturalNumber m ->
  Prod_w o m o.
Proof.
  intros o m Ho Hm. omga. build_set set
    (fun (o c m : set) => Prod_w o m o) o omga.
  rename x into T. rename H into HT. apply HT.
  replace T with omga; try (apply Homga, Hm). clear m Hm. symmetry.
  apply Induction_Principle_for_Omega; try assumption; try split;
  try (intros a Ha; apply HT, Ha).
  - exists o. split; try assumption. apply HT.
    split; try (apply Homga, Zero_NaturalNumber, Ho).
    destruct Enderton4J as [M1 _]. apply M1; try assumption.
    apply Zero_NaturalNumber. assumption.
  - intros m m' Hm' Hm. apply HT in Hm. destruct Hm as [Hm IH].
    apply HT. apply Homga in Hm.
    split; try (apply Homga, (Succ_NaturalNumber m m'); assumption).
    prod_w o m' (Zero_NaturalNumber o Ho) (Succ_NaturalNumber m m' Hm Hm').
    rename x into om'. rename H into Hom'.
    replace om' with o in Hom'; try assumption.
    destruct Enderton4J as [_ M2]. symmetry.
    apply (M2 o m o m'); try assumption; try apply Zero_NaturalNumber, Ho.
    destruct Enderton4I as [A1 _].
    apply A1; try apply Zero_NaturalNumber; assumption.
Qed.

Lemma M2_Commutative : forall m n mn m' m'n mnn,
  NaturalNumber m -> NaturalNumber n -> Prod_w m n mn -> Succ m m' ->
  Prod_w m' n m'n -> Sum_w mn n mnn -> m'n = mnn.
Proof.
  intros m n mn m' m'n mnn Hm Hn. omga.
  generalize dependent mnn. generalize dependent m'n.
  generalize dependent m'. generalize dependent mn.
  build_set set
    (fun (m c n : set) => forall mn m' m'n mnn, Prod_w m n mn -> Succ m m' ->
      Prod_w m' n m'n -> Sum_w mn n mnn -> m'n = mnn)
    m omga.
  rename x into T. rename H into HT. apply HT.
  replace T with omga; try (apply Homga, Hn). symmetry. clear n Hn.
  apply Induction_Principle_for_Omega; try assumption; try split;
  try (intros a Ha; apply HT, Ha).
  - zero. rename x into o. rename H into Ho. exists o. split; try assumption.
    apply HT. split; try (apply Homga, Zero_NaturalNumber, Ho).
    intros mn m' m'n mnn Hmn Hm' Hm'n Hmnn.
    destruct Enderton4J as [M1 _].
    replace mn with o in *. replace mnn with o in *.
    replace m'n with o in *. trivial.
    + apply (Prod_w_Unique m' o o m'n); try assumption;
      try (apply Zero_NaturalNumber, Ho);
      try (apply (Succ_NaturalNumber m m' Hm Hm')).
      apply M1; try assumption.
      apply (Succ_NaturalNumber m); try assumption.
    + apply (Sum_w_Unique o o o mnn); try apply Zero_NaturalNumber; try assumption.
      destruct Enderton4I as [A1 _].
      apply A1; try assumption. apply Zero_NaturalNumber, Ho.
    + apply (Prod_w_Unique m o o mn); try assumption;
      try apply Zero_NaturalNumber, Ho.
      apply M1; try assumption.
  - intros n n' Hn' Hn. apply HT in Hn. destruct Hn as [Hn IH].
    apply HT. apply Homga in Hn.
    split; try (apply Homga, (Succ_NaturalNumber n n' Hn Hn')).
    intros mn' m' m'n' mn'n' Hmn' Hm' Hm'n' Hmn'n'.
    prod_w m n Hm Hn. rename x into mn. rename H into Hmn.
    sum_w m n Hm Hn. rename x into mpn. rename H into Hmpn.
    succ mpn. rename x into Smpn. rename H into HSmpn.
    assert (T0 : NaturalNumber mn).
    { apply (Prod_NaturalNumber m n); try assumption. }
    assert (T1 : NaturalNumber Smpn).
    { apply (Succ_NaturalNumber mpn); try assumption.
      apply (Sum_NaturalNumber m n); try assumption. }
    sum_w mn Smpn T0 T1. rename x into mnSmpn. rename H into HmnSmpn.
    transitivity mnSmpn.
    + sum_w mn n T0 Hn. rename x into mnn. rename H into Hmnn.
      sum_w mnn m' (Sum_NaturalNumber mn n mnn T0 Hn Hmnn)
        (Succ_NaturalNumber m m' Hm Hm').
      rename x into mnnm. rename H into Hmnnm. transitivity mnnm.
      * sum_w m' mnn (Succ_NaturalNumber m m' Hm Hm')
          (Sum_NaturalNumber mn n mnn T0 Hn Hmnn).
        rename x into mmnn. rename H into Hmmnn. transitivity mmnn.
        { prod_w m' n (Succ_NaturalNumber m m' Hm Hm') Hn.
          rename x into m'n. rename H into Hm'n.
          sum_w m' m'n (Succ_NaturalNumber m m' Hm Hm')
            (Prod_NaturalNumber m' n m'n (Succ_NaturalNumber m m' Hm Hm') Hn Hm'n).
          rename x into m'm'n. rename H into Hm'm'n. transitivity m'm'n.
          - destruct Enderton4J as [_ M2]. apply (M2 m' n m'n n'); try assumption.
            apply (Succ_NaturalNumber m m'); try assumption.
          - apply (Sum_w_Unique m' m'n m'm'n mmnn); try assumption;
            try apply (Succ_NaturalNumber m m' Hm Hm').
            + apply (Prod_NaturalNumber m' n); try assumption.
              apply (Succ_NaturalNumber m m'); try assumption.
            + replace m'n with mnn; try assumption.
              symmetry. apply (IH mn m' m'n mnn); try assumption. }
        { apply (Enderton4K2 m' mnn mmnn mnnm); try assumption.
          apply (Succ_NaturalNumber m m'); try assumption.
          apply (Sum_NaturalNumber mn n); try assumption. }
      * sum_w n m Hn Hm. rename x into npm. rename H into Hnpm.
        sum_w mn npm T0 (Sum_NaturalNumber n m npm Hn Hm Hnpm).
        rename x into mnnpm. rename H into Hmnnpm.
        succ mnnpm. rename x into Smnnpm. rename H into HSmnnpm.
        transitivity Smnnpm.
        { sum_w mnn m (Sum_NaturalNumber mn n mnn T0 Hn Hmnn) Hm.
          rename x into mnnm'. rename H into Hmnnm'.
          succ mnnm'. rename x into Smnnm. rename H into HSmnnm.
          transitivity Smnnm.
          - destruct Enderton4I as [A1 A2].
            apply (A2 mnn m m' mnnm'); try assumption.
            apply (Sum_NaturalNumber mn n); try assumption.
          - apply (Succ_Unique mnnm' Smnnm Smnnpm); try assumption.
            replace mnnm' with mnnpm; try assumption.
            apply (Enderton4K1 mn n m npm mnn); try assumption. }
        { sum_w mn mpn T0 (Sum_NaturalNumber m n mpn Hm Hn Hmpn).
          rename x into mnmpn. rename H into Hmnmpn.
          succ mnmpn. rename x into Smnmpn. rename H into HSmnmpn.
          transitivity Smnmpn.
          - apply (Succ_Unique mnnpm); try assumption.
            replace mnnpm with mnmpn; try assumption.
            apply (Sum_w_Unique mn mpn); try assumption;
            try apply (Sum_NaturalNumber m n); try assumption.
            replace mpn with npm; try assumption.
            apply (Enderton4K2 n m npm mpn); assumption.
          - destruct Enderton4I as [A1 A2]. symmetry.
            apply (A2 mn mpn Smpn mnmpn); try assumption.
            apply (Sum_NaturalNumber m n); assumption. }
    + sum_w mn m T0 Hm. rename x into mnm. rename H into Hmnm.
      sum_w mnm n' (Sum_NaturalNumber mn m mnm T0 Hm Hmnm)
        (Succ_NaturalNumber n n' Hn Hn').
      rename x into mnmn'. rename H into Hmnmn'. transitivity mnmn'.
      * sum_w m n' Hm (Succ_NaturalNumber n n' Hn Hn').
        rename x into mpn'. rename H into Hmpn'.
        sum_w mn mpn' T0 (Sum_NaturalNumber m n' mpn' Hm
          (Succ_NaturalNumber n n' Hn Hn') Hmpn').
        rename x into mnmpn'. rename H into Hmnmpn'. transitivity mnmpn'.
        { apply (Sum_w_Unique mn Smpn); try assumption.
          replace Smpn with mpn'; try assumption.
          destruct Enderton4I as [A1 A2]. apply (A2 m n n' mpn); try assumption. }
        { apply (Enderton4K1 mn m n' mpn' mnm); try assumption.
          apply (Succ_NaturalNumber n n'); assumption. }
      * apply (Sum_w_Unique mnm n'); try assumption;
        try apply (Sum_NaturalNumber mn m mnm T0 Hm Hmnm);
        try apply (Succ_NaturalNumber n n' Hn Hn').
        replace mnm with mn'; try assumption.
        destruct Enderton4J as [M1 M2]. apply (M2 m n mn n'); try assumption.
        sum_w m mn Hm T0. rename x into mmn. rename H into Hmmn.
        replace mnm with mmn; try assumption.
        apply (Enderton4K2 m mn); try assumption.
Qed.

Theorem Enderton4K5 : Multiplication_Commutative_w.
Proof.
  intros m n mn nm Hm Hn. omga. generalize dependent nm. generalize dependent mn.
  build_set set
    (fun (m c n : set) => forall mn nm, Prod_w m n mn -> Prod_w n m nm -> mn = nm)
    m omga.
  rename x into T. rename H into HT. apply HT.
  replace T with omga; try (apply Homga, Hn). symmetry. clear n Hn.
  apply Induction_Principle_for_Omega; try assumption; try split;
  try (intros a Ha; apply HT, Ha).
  - zero. rename x into o. rename H into Ho. exists o. split; try assumption.
    apply HT. split; try (apply Homga, Zero_NaturalNumber, Ho).
    intros mn nm Hmn Hnm. replace mn with o in *. replace nm with o in *.
    trivial.
    + apply (Prod_w_Unique o m o nm); try assumption;
      try (apply Zero_NaturalNumber, Ho).
      apply (M1_Commutative); try assumption.
    + apply (Prod_w_Unique m o o mn); try assumption;
      try (apply Zero_NaturalNumber, Ho).
      destruct Enderton4J as [M1 M2]. apply M1; assumption.
  - intros n n' Hn' Hn. apply HT in Hn. destruct Hn as [Hn IH].
    apply HT. apply Homga in Hn.
    split; try (apply Homga, (Succ_NaturalNumber n n' Hn Hn')).
    intros mn' n'm Hmn' Hn'm.
    prod_w n m Hn Hm. rename x into nm. rename H into Hnm.
    prod_w m n Hm Hn. rename x into mn. rename H into Hmn.
    sum_w m nm Hm (Prod_NaturalNumber n m nm Hn Hm Hnm).
    rename x into mnm. rename H into Hmnm. transitivity mnm.
    + sum_w m mn Hm (Prod_NaturalNumber m n mn Hm Hn Hmn).
      rename x into mmn. rename H into Hmmn. transitivity mmn.
      * destruct Enderton4J as [M1 M2]. apply (M2 m n mn n'); try assumption.
      * apply (Sum_w_Unique m mn); try assumption;
        try apply (Prod_NaturalNumber m n mn Hm Hn Hmn).
        replace mn with nm; try assumption. symmetry.
        apply (IH mn nm Hmn Hnm).
    + sum_w nm m (Prod_NaturalNumber n m nm Hn Hm Hnm) Hm.
      rename x into nmm. rename H into Hnmm. transitivity nmm.
      * apply (Enderton4K2 m nm); try assumption;
        try apply (Prod_NaturalNumber n m nm Hn Hm Hnm).
      * symmetry. apply (M2_Commutative n m nm n'); try assumption.
Qed.

Lemma SumZero_implies_BothZero : forall m n o, NaturalNumber m ->
  NaturalNumber n -> Empty o -> Sum_w m n o -> Empty m /\ Empty n.
Proof.
  intros m n o Hm Hn Ho. omga. generalize dependent n. build_set set
    (fun (o c m : set) => forall n, NaturalNumber n -> Sum_w m n o ->
      Empty m /\ Empty n)
    o omga.
  rename x into T. rename H into HT. apply HT.
  replace T with omga; try (apply Homga, Hm). symmetry. clear m Hm.
  apply Induction_Principle_for_Omega; try assumption; try split;
  try (intros t Ht; apply HT, Ht).
  - exists o. split; try assumption. apply HT.
    split; try (apply Homga, Zero_NaturalNumber, Ho).
    intros n Hn H. split; try assumption. replace n with o; try assumption.
    apply (Sum_w_Unique o n o n); try assumption;
    try (apply Zero_NaturalNumber, Ho).
    apply A1_Commutative; try assumption.
  - intros m m' Hm' Hm. apply HT in Hm. destruct Hm as [Hm IH].
    apply HT. apply Homga in Hm.
    split; try (apply Homga, (Succ_NaturalNumber m m' Hm Hm')).
    intros n Hn Hm'n. succ n. rename x into n'. rename H into Hn'.
    sum_w m n Hm Hn. rename x into mn. rename H into Hmn.
    sum_w m n' Hm (Succ_NaturalNumber n n' Hn Hn').
    rename x into mn'. rename H into Hmn'.
    sum_w m' n (Succ_NaturalNumber m m' Hm Hm') Hn.
    rename x into m'n. rename H into Hm'n0.
    assert (P : Sum_w m n' o).
    { replace o with mn'; try assumption. transitivity m'n.
      - succ mn. rename x into Smn. transitivity Smn.
        + destruct Enderton4I as [A1 A2]. apply (A2 m n n' mn); assumption.
        + symmetry. apply (A2_Commutative m n m' mn); try assumption.
      - apply (Sum_w_Unique m' n m'n o); try assumption.
        apply (Succ_NaturalNumber m m'); assumption. }
    destruct (IH n' (Succ_NaturalNumber n n' Hn Hn') P) as [IH1 IH2].
    destruct (IH2 n). destruct Hn' as [Sn [HSn Hn']]. apply Hn'. right.
    apply HSn. trivial.
Qed.

Theorem Exercise4_13 : forall m n o, NaturalNumber m -> NaturalNumber n ->
  Empty o -> Prod_w m n o -> m = o \/ n = o.
Proof.
  intros m n o Hm Hn Ho. generalize dependent n. omga.
  build_set set
    (fun (o c m : set) => forall n, NaturalNumber n -> Prod_w m n o -> m = o \/ n = o)
    o omga.
  rename x into T. rename H into HT. apply HT.
  replace T with omga; try (apply Homga, Hm). symmetry. clear Hm m.
  apply Induction_Principle_for_Omega; try assumption; try split;
  try (intros t Ht; apply HT, Ht).
  - exists o. split; try assumption. apply HT.
    split; try (apply Homga, Zero_NaturalNumber, Ho).
    intros n Hn Hon. left. trivial.
  - intros m m' Hm' Hm. apply HT in Hm. destruct Hm as [Hm IH].
    apply HT. apply Homga in Hm.
    split; try (apply Homga, (Succ_NaturalNumber m m' Hm Hm')).
    intros n Hn Hm'n. right.
    prod_w m n Hm Hn. rename x into mn. rename H into Hmn.
    apply (Empty_Unique); try assumption.
    destruct (SumZero_implies_BothZero mn n o) as [_ H];
    try apply H; try assumption; try apply (Prod_NaturalNumber m n mn Hm Hn Hmn).
    sum_w mn n (Prod_NaturalNumber m n mn Hm Hn Hmn) Hn.
    rename x into mnn. rename H into Hmnn. replace o with mnn; try assumption.
    prod_w m' n (Succ_NaturalNumber m m' Hm Hm') Hn.
    rename x into m'n. rename H into Hm'n0. transitivity m'n.
    + symmetry. apply (M2_Commutative m n mn m'); try assumption.
    + apply (Prod_w_Unique m' n m'n o); try assumption.
      apply (Succ_NaturalNumber m m' Hm Hm').
Qed.

Definition Even_w (n : set) : Prop :=
  exists p o o' o'', NaturalNumber p /\ Empty o /\ Succ o o' /\ Succ o' o'' /\
  Prod_w o'' p n.

Definition Odd_w (n : set) : Prop :=
  exists p o o' o'' tp, NaturalNumber p /\ Empty o /\ Succ o o' /\ Succ o' o'' /\
  Prod_w o'' p tp /\ Succ tp n.

Theorem Exercise4_14 : forall n, NaturalNumber n -> Odd_w n \/ Even_w n.
Proof.
  intros n Hn. omga. destruct Enderton4I as [A1 A2].
  build_set set (fun (t c n : set) => Odd_w n \/ Even_w n) omga omga.
  rename x into T. rename H into HT. apply HT.
  replace T with omga; try (apply Homga, Hn). clear n Hn. symmetry.
  apply Induction_Principle_for_Omega; try assumption; try split;
  try (intros t Ht; apply HT, Ht).
  - zero. exists x. split; try assumption. rename x into o. rename H into Ho.
    apply HT. split; try apply Homga, Zero_NaturalNumber, Ho.
    right. succ o. rename x into o'. rename H into Ho'.
    succ o'. rename x into o''. rename H into Ho''.
    exists o, o, o', o''; repeat (split; try assumption);
    try apply Zero_NaturalNumber, Ho.
    destruct Enderton4J as [M1 _]. apply M1; try assumption.
    apply (Succ_NaturalNumber o' o''); try assumption.
    apply (Succ_NaturalNumber o o'); try assumption.
    apply Zero_NaturalNumber, Ho.
  - intros n n' Hn' Hn. apply HT in Hn. destruct Hn as [Hn IH].
    apply HT. apply Homga in Hn.
    split; try apply Homga, (Succ_NaturalNumber n n' Hn Hn').
    destruct IH as [IH | IH].
    + right. destruct IH as [p [o [o' [o'' [tp [Hp [Ho [Ho' [Ho'' [Htp IH]]]]]]]]]].
      succ p. rename x into p'. rename H into Hp'.
      exists p', o, o', o''. repeat (split; try assumption);
      try apply (Succ_NaturalNumber p p' Hp Hp').
      assert (T0 : NaturalNumber o'').
      { apply (Succ_NaturalNumber o' o''); try assumption.
        apply (Succ_NaturalNumber o o'); try assumption.
        apply Zero_NaturalNumber, Ho. }
      prod_w o'' p' T0 (Succ_NaturalNumber p p' Hp Hp').
      rename x into tp'. rename H into Htp'.
      replace n' with tp'; try assumption.
      sum_w o'' tp T0 (Prod_NaturalNumber o'' p tp T0 Hp Htp).
      rename x into ttp. rename H into Http. transitivity ttp.
      * destruct Enderton4J as [M1 M2]. apply (M2 o'' p tp p'); try assumption.
      * sum_w tp o'' (Prod_NaturalNumber o'' p tp T0 Hp Htp) T0.
        rename H into Htpt. rename x into tpt.
        replace ttp with tpt.
        sum_w tp o' (Prod_NaturalNumber o'' p tp T0 Hp Htp)
          (Succ_NaturalNumber o o' (Zero_NaturalNumber o Ho) Ho').
        rename H into Htpo'. rename x into tpo'.
        succ tpo'. rename x into Stpo'. rename H into HStpo'.
        replace tpt with Stpo'. apply (Succ_Unique tpo'); try assumption.
        replace tpo' with n; try assumption.
        apply (Succ_Unique tp); try assumption.
        succ tp. rename x into Stp. rename H into HStp.
        replace tpo' with Stp; try assumption.
        sum_w tp o (Prod_NaturalNumber o'' p tp T0 Hp Htp) (Zero_NaturalNumber o Ho).
        rename x into tpo. rename H into Htpo. symmetry.
        apply (A2 tp o o' tpo); try assumption;
        try apply Zero_NaturalNumber, Ho;
        try apply (Prod_NaturalNumber o'' p); try assumption.
        replace tpo with tp; try assumption.
        apply (Sum_w_Unique tp o tp tpo); try assumption;
        try apply Zero_NaturalNumber, Ho;
        try apply (Prod_NaturalNumber o'' p); try assumption.
        apply A1; try assumption;
        try apply (Prod_NaturalNumber o'' p); try assumption.
        symmetry. apply (A2 tp o' o'' tpo'); try assumption;
        try apply (Succ_NaturalNumber o o'); try assumption;
        try apply Zero_NaturalNumber, Ho;
        try apply (Prod_NaturalNumber o'' p); try assumption.
        apply (Enderton4K2 tp o''); try assumption;
        try apply (Prod_NaturalNumber o'' p); assumption.
    + left. destruct IH as [p [o [o' [o'' [Hp [Ho [Ho' [Ho'' IH]]]]]]]].
      exists p, o, o', o'', n; repeat (split; try assumption).
Qed.

Lemma Pred_Unique : forall m n m' n', NaturalNumber m -> NaturalNumber n ->
  Succ m m' -> Succ n n' -> m' = n' -> m = n.
Proof.
  intros m n m' n' Hm Hn Hm' Hn' H.
  union m'. rename x into Um'. rename H0 into HUm'.
  union n'. rename x into Un'. rename H0 into HUn'.
  apply (Union_Unique m').
  - replace m with Um'; try assumption.
    apply (Enderton4E m m'); try assumption.
    apply (Enderton4F); assumption.
  - replace m' with n'; try assumption.
    replace n with Un'; try assumption.
    apply (Enderton4E n n'); try assumption.
    apply Enderton4F; assumption.
Qed.

Theorem Exercise4_14' : forall n, NaturalNumber n -> ~ (Odd_w n /\ Even_w n).
Proof.
  intros n Hn. omga. destruct Enderton4J as [M1 M2]. destruct Enderton4I as [A1 A2].
  build_set set (fun (t c n : set) => ~ (Odd_w n /\ Even_w n)) omga omga.
  rename x into T. rename H into HT. apply HT.
  replace T with omga; try apply Homga, Hn. symmetry. clear Hn n.
  apply Induction_Principle_for_Omega; try assumption; try split;
  try (intros t Ht; apply HT, Ht).
  - empty. rename x into o. rename H into Ho. exists o. split; try assumption.
    apply HT. split; try apply Homga, Zero_NaturalNumber, Ho.
    intros C. destruct C as [C1 C2].
    destruct C1 as [p [o0 [o' [o'' [tp [Hp [Ho0 [Ho' [Ho'' [Htp H]]]]]]]]]].
    replace o0 with o in *; try apply (Empty_Unique); try assumption.
    clear o0 Ho0. apply (Ho tp). destruct H as [Stp [HStp H]].
    apply H. right. apply HStp. trivial.
  - intros n n' Hn' Hn. apply HT in Hn. destruct Hn as [Hn IH].
    apply HT. apply Homga in Hn.
    split; try apply Homga, (Succ_NaturalNumber n n' Hn Hn').
    intros [C1 C2]. apply IH. split.
    + destruct C2 as [p' [o [o' [o'' [Hp' [Ho [Ho' [Ho'' C2]]]]]]]].
      assert (T0 : NaturalNumber o'').
      { try apply (Succ_NaturalNumber o' o''
          (Succ_NaturalNumber o o' (Zero_NaturalNumber o Ho) Ho') Ho''). }
      destruct (Enderton4C p' Hp') as [p [Hp Hp'0]].
      { intros C. apply (Ho n). replace o with n'.
        - destruct Hn' as [Sn [HSn Hn']]. apply Hn'. right.
          apply HSn. trivial.
        - apply (Prod_w_Unique o'' p' n' o); try assumption.
          replace p' with o; try apply M1; try assumption.
          apply (Empty_Unique o p'); assumption. }
      prod_w o'' p T0 Hp. rename x into tp. rename H into Htp.
      assert (T1 : NaturalNumber tp).
      { apply (Prod_NaturalNumber o'' p); try assumption. }
      exists p, o, o', o'', tp. repeat (split; try assumption).
      succ tp. rename x into Stp. rename H into HStp.
      replace n with Stp; try assumption.
      apply (Pred_Unique Stp n n' n'); try assumption; try trivial.
      { apply (Succ_NaturalNumber tp); try assumption. }
      succ Stp. rename x into SStp. rename H into HSStp.
      replace n' with SStp; try assumption.
      sum_w tp o'' T1 T0. rename x into tpt. rename H into Htpt.
      transitivity tpt.
      * sum_w tp o T1 (Zero_NaturalNumber o Ho).
        rename x into tpo. rename H into Htpo.
        succ tpo. rename H into HStpo. rename x into Stpo.
        succ Stpo. rename H into HSStpo. rename x into SStpo.
        transitivity SStpo.
        { apply (Succ_Unique Stp); try assumption.
          replace Stp with Stpo; try assumption.
          apply (Succ_Unique tp); try assumption.
          replace tp with tpo; try assumption.
          apply (Sum_w_Unique tp o tpo tp); try assumption;
          try apply Zero_NaturalNumber, Ho.
          apply A1; assumption. }
        { sum_w tp o' T1 (Succ_NaturalNumber o o' (Zero_NaturalNumber o Ho) Ho').
          rename x into tpo'. rename H into Htpo'.
          succ tpo'. rename x into Stpo'. rename H into HStpo'.
          transitivity Stpo'.
          - apply (Succ_Unique Stpo); try assumption.
            replace Stpo with tpo'; try assumption.
            apply (A2 tp o o' tpo); try assumption.
            apply Zero_NaturalNumber, Ho.
          - symmetry. apply (A2 tp o' o'' tpo'); try assumption.
            apply (Succ_NaturalNumber o o'); try assumption.
            apply Zero_NaturalNumber, Ho. }
      * sum_w o'' tp T0 T1. rename x into ttp. rename H into Http.
        transitivity ttp.
        { apply (Enderton4K2 tp o''); try assumption. }
        { symmetry. apply (M2 o'' p tp p'); try assumption. }
    + destruct C1 as [p [o [o' [o'' [tp [Hp [Ho [Ho' [Ho'' [Htp C1]]]]]]]]]].
      exists p, o, o', o''. repeat (split; try assumption).
      replace n with tp; try assumption.
      apply (Pred_Unique tp n n' n'); try assumption; try trivial.
      apply (Prod_NaturalNumber o'' p); try assumption.
      apply (Succ_NaturalNumber o' o''); try assumption.
      apply (Succ_NaturalNumber o o'); try assumption.
      apply Zero_NaturalNumber, Ho.
Qed.

(** Exercise 4-15 : Prove part 1 of 4K. *)

(** Exercise 4-16 : Prove part 5 of 4K. *)

Lemma Pow_NaturalNumber : forall m n mn, NaturalNumber m -> NaturalNumber n ->
  Pow_w m n mn -> NaturalNumber mn.
Proof.
  intros m n mn Hm Hn Hmn. omga.
  destruct (Hmn Hm Hn) as [exp [Pmn [Pmnmn [Hexp [HPmn [HPmnmn H]]]]]].
  destruct (Exponentiation_w_BinaryOperation exp omga) as [wxw [Hwxw Hfexp]];
  try assumption.
  destruct Hfexp as [Hfexp [Hdomexp [ranexp [Hranexp Hsub]]]].
  apply Homga, Hsub, Hranexp. exists Pmn, Pmnmn. split; assumption.
Qed.

Theorem Exercise4_17 : forall m n p np mnp mn mp mnmp,
  NaturalNumber m -> NaturalNumber n -> NaturalNumber p -> Sum_w n p np ->
  Pow_w m np mnp -> Pow_w m n mn -> Pow_w m p mp -> Prod_w mn mp mnmp ->
  mnp = mnmp.
Proof.
  intros m n p np mnp mn mp mnmp Hm Hn Hp. omga. destruct Enderton4J as [M1 M2].
  destruct Enderton4I as [A1 A2]. destruct Enderton4J' as [E1 E2].
  generalize dependent mnmp. generalize dependent mp. generalize dependent mn.
  generalize dependent mnp. generalize dependent np.
  build_set (prod set set)
    (fun (t : set * set) (c p : set) => forall np mnp mn mp mnmp,
      Sum_w (snd t) p np -> Pow_w (fst t) np mnp -> Pow_w (fst t) (snd t) mn ->
      Pow_w (fst t) p mp -> Prod_w mn mp mnmp -> mnp = mnmp) (m,n) omga.
  rename x into T. rename H into HT. apply HT.
  replace T with omga; try apply Homga, Hp. clear p Hp. symmetry.
  apply Induction_Principle_for_Omega; try assumption; try split;
  try (intros t Ht; apply HT, Ht).
  - empty. rename x into o. rename H into Ho. exists o. split; try assumption.
    apply HT. split; try apply Homga, Zero_NaturalNumber, Ho.
    intros np mnp mn mp mnmp Hnp Hmnp Hmn Hmp Hmnmp. simpl in *.
    succ o. rename x into o'; rename H into Ho'.
    replace np with n in *. replace mnp with mn in *.
    replace mp with o' in *. replace mnmp with mn in *. trivial.
    + sum_w mn o (Pow_NaturalNumber m n mn Hm Hn Hmn) (Zero_NaturalNumber o Ho).
      rename x into mno. rename H into Hmno. transitivity mno.
      * apply (Sum_w_Unique mn o mn mno); try assumption;
        try apply (Pow_NaturalNumber m n mn Hm Hn Hmn);
        try apply Zero_NaturalNumber, Ho.
        apply A1; try assumption.
        apply (Pow_NaturalNumber m n mn Hm Hn Hmn).
      * prod_w mn o (Pow_NaturalNumber m n mn Hm Hn Hmn) (Zero_NaturalNumber o Ho).
        rename x into mnto. rename H into Hmnto. replace o with mnto in Hmno.
        { symmetry. apply (M2 mn o mnto o'); try assumption;
          try apply Zero_NaturalNumber, Ho.
          apply (Pow_NaturalNumber m n mn Hm Hn Hmn). }
        { apply (Prod_w_Unique mn o mnto o); try assumption;
          try apply Zero_NaturalNumber, Ho;
          try apply (Pow_NaturalNumber m n mn Hm Hn Hmn).
          apply M1; try assumption.
          apply (Pow_NaturalNumber m n mn Hm Hn Hmn). }
    + apply (Pow_w_Unique m o o' mp); try assumption;
      try apply Zero_NaturalNumber, Ho. apply E1; try assumption.
    + apply (Pow_w_Unique m n mn mnp); try assumption.
    + apply (Sum_w_Unique n o n np); try assumption;
      try apply Zero_NaturalNumber, Ho.
      apply A1; try assumption.
  - intros p p' Hp' Hp. apply HT in Hp. destruct Hp as [Hp IH].
    apply HT. apply Homga in Hp.
    split; try apply Homga, (Succ_NaturalNumber p p'); try assumption.
    intros np' mnp' mn mp' mnmp' Hnp' Hmnp' Hmn Hmp' Hmnmp'. simpl in *.
    pow_w m p Hm Hp. rename x into mp. rename H into Hmp.
    prod_w mp mn (Pow_NaturalNumber m p mp Hm Hp Hmp)
      (Pow_NaturalNumber m n mn Hm Hn Hmn).
    rename x into mpmn. rename H into Hmpmn.
    prod_w m mpmn Hm (Prod_NaturalNumber mp mn mpmn
      (Pow_NaturalNumber m p mp Hm Hp Hmp) (Pow_NaturalNumber m n mn Hm Hn Hmn) Hmpmn).
    rename x into mmpmn. rename H into Hmmpmn. transitivity mmpmn.
    + sum_w n p Hn Hp. rename x into np. rename H into Hnp.
      pow_w m np Hm (Sum_NaturalNumber n p np Hn Hp Hnp).
      rename x into mnp. rename H into Hmnp.
      prod_w m mnp Hm (Pow_NaturalNumber m np mnp Hm
        (Sum_NaturalNumber n p np Hn Hp Hnp) Hmnp).
      rename x into mmnp. rename H into Hmmnp. transitivity mmnp.
      * succ np. rename x into Snp. rename H into HSnp.
        pow_w m Snp Hm (Succ_NaturalNumber np Snp
          (Sum_NaturalNumber n p np Hn Hp Hnp) HSnp).
        rename x into mSnp. rename H into HmSnp. transitivity mSnp.
        { apply (Pow_w_Unique m np' mnp' mSnp); try assumption;
          try apply (Sum_NaturalNumber n p'); try assumption;
          try apply (Succ_NaturalNumber p p'); try assumption.
          replace np' with Snp; try assumption. symmetry.
          apply (A2 n p p' np); try assumption. }
        { apply (E2 m np mnp Snp); try assumption.
          apply (Sum_NaturalNumber n p); try assumption. }
      * prod_w mn mp (Pow_NaturalNumber m n mn Hm Hn Hmn)
          (Pow_NaturalNumber m p mp Hm Hp Hmp).
        rename x into mnmp. rename H into Hmnmp.
        prod_w m mnmp Hm (Prod_NaturalNumber mn mp mnmp
          (Pow_NaturalNumber m n mn Hm Hn Hmn)
          (Pow_NaturalNumber m p mp Hm Hp Hmp) Hmnmp).
        rename x into mmnmp. rename H into Hmmnmp. transitivity mmnmp.
        { apply (Prod_w_Unique m mnp); try assumption.
          try apply (Pow_NaturalNumber m np); try assumption;
          try apply (Sum_NaturalNumber n p); try assumption.
          replace mnp with mnmp; try assumption. symmetry.
          apply (IH np mnp mn mp mnmp); try assumption. }
        { apply (Prod_w_Unique m mnmp); try assumption;
          try apply (Prod_NaturalNumber mn mp); try assumption;
          try apply (Pow_NaturalNumber m n mn); try assumption;
          try apply (Pow_NaturalNumber m p mp); try assumption.
          replace mnmp with mpmn; try assumption.
          apply (Enderton4K5 mp mn); try assumption;
          try apply (Pow_NaturalNumber m p mp); try assumption;
          try apply (Pow_NaturalNumber m n mn); try assumption. }
    + prod_w mp' mn (Pow_NaturalNumber m p' mp' Hm (Succ_NaturalNumber p p' Hp Hp')
        Hmp') (Pow_NaturalNumber m n mn Hm Hn Hmn).
      rename x into mp'mn. rename H into Hmp'mn. transitivity mp'mn.
      * prod_w m mp Hm (Pow_NaturalNumber m p mp Hm Hp Hmp).
        rename x into mmp0. rename H into Hmmp0.
        prod_w mmp0 mn (Prod_NaturalNumber m mp mmp0 Hm
          (Pow_NaturalNumber m p mp Hm Hp Hmp) Hmmp0)
          (Pow_NaturalNumber m n mn Hm Hn Hmn).
        rename x into mmp0mn. rename H into Hmmp0mn. transitivity mmp0mn.
        { apply (Enderton4K4 m mp mn mpmn mmp0); try assumption;
          try apply (Pow_NaturalNumber m p mp); try assumption;
          try apply (Pow_NaturalNumber m n); try assumption. }
        { apply (Prod_w_Unique mmp0 mn); try assumption;
          try apply (Prod_NaturalNumber m mp mmp0); try assumption;
          try apply (Pow_NaturalNumber m p mp); try assumption;
          try apply (Pow_NaturalNumber m n mn); try assumption.
          replace mmp0 with mp'; try assumption.
          apply (E2 m p mp p'); try assumption. }
      * apply (Enderton4K5 mp' mn); try assumption;
        try apply (Pow_NaturalNumber m p' mp'); try assumption;
        try apply (Succ_NaturalNumber p p'); try assumption;
        try apply (Pow_NaturalNumber m n); try assumption.
Qed.

(** Now we have the basic algebraic operations on omega and corresponding
    results. We next turn our attention to ordering on omega, and show that the
    relation < is linear ordering as in the previous chapter. *)

Definition LessThan_w (lt : set) : Prop :=
  forall mn, In mn lt <-> exists m n, OrdPair m n mn /\ NaturalNumber m /\
  NaturalNumber n /\ In m n.

Theorem LessThan_w_Exists : exists lt, LessThan_w lt.
Proof.
  omga. prod omga omga. rename x into wxw. rename H into Hwxw.
  build_set set
    (fun (t c mn : set) => exists m n, OrdPair m n mn /\ NaturalNumber m /\
      NaturalNumber n /\ In m n)
    omga wxw.
  rename x into lt. rename H into Hlt. exists lt.
  intros mn. split; intros H; try apply Hlt, H.
  apply Hlt. split; try assumption.
  apply Hwxw. destruct H as [m [n [Hmn [Hm [Hn H]]]]].
  exists m, n. repeat (split; try apply Homga; try assumption).
Qed.

Theorem LessThan_w_Unique : forall lt lt', LessThan_w lt ->
  LessThan_w lt' -> lt = lt'.
Proof.
  intros lt lt' Hlt Hlt'.
  apply Extensionality_Axiom. intros x. split; intros H.
  - apply Hlt', Hlt, H.
  - apply Hlt, Hlt', H.
Qed.

Ltac lt_w := destruct (LessThan_w_Exists) as [lt Hlt].

Definition In_ (x A : set) : Prop :=
  In x A \/ x = A.

Definition LessThanEq_w (le : set) : Prop :=
  forall mn, In mn le <-> exists m n, OrdPair m n mn /\ NaturalNumber m /\
  NaturalNumber n /\ In_ m n.

Theorem LessThanEq_w_Exists : exists le, LessThanEq_w le.
Proof.
  omga. prod omga omga. rename x into wxw. rename H into Hwxw.
  build_set set
    (fun (t c mn : set) => exists m n, OrdPair m n mn /\ NaturalNumber m /\
      NaturalNumber n /\ In_ m n)
    omga wxw.
  rename x into le. rename H into Hle. exists le.
  intros mn. split; intros H; try apply Hle, H.
  apply Hle. split; try assumption.
  destruct H as [m [n [Hmn [Hm [Hn H]]]]].
  apply Hwxw. exists m, n. repeat (split; try apply Homga; try assumption).
Qed.

Theorem Le_w_Unique : forall le le', LessThanEq_w le -> LessThanEq_w le' ->
  le = le'.
Proof.
  intros le le' Hle Hle'. apply Extensionality_Axiom. intros mn. split; intros H.
  - apply Hle', Hle, H.
  - apply Hle, Hle', H.
Qed.

Ltac le_w := destruct (LessThanEq_w_Exists) as [le Hle].

Lemma lt_w_succ_iff_le_w : forall lt le p k k' pk' pk,
  LessThan_w lt -> LessThanEq_w le -> NaturalNumber p -> NaturalNumber k ->
  Succ k k' -> OrdPair p k' pk' -> OrdPair p k pk -> In pk' lt <-> In pk le.
Proof.
  intros lt le p k k' pk' pk Hlt Hle Hp Hk Hk' Hpk' Hpk. split; intros H.
  - apply Hle. apply Hlt in H. destruct H as [p0 [k'0 [Hpk'o [Hp0 [Hk'0 H]]]]].
    assert (T : p = p0 /\ k' = k'0).
    { apply (Enderton3A p k' p0 k'0 pk' pk'); try assumption; try trivial. }
    replace p0 with p in *; replace k'0 with k' in *; try apply T.
    clear T p0 Hp0 k'0 Hk'0. exists p, k.
    repeat (split; try assumption). destruct Hk' as [Sk [HSk Hk']].
    apply Hk' in H. destruct H as [H | H].
    + left. assumption.
    + right. apply HSk in H. assumption.
  - apply Hle in H. destruct H as [p0 [k0 [Hpk0 [Hp0 [Hk0 H]]]]].
    assert (T : p = p0 /\ k = k0).
    { apply (Enderton3A p k p0 k0 pk pk); try assumption; trivial. }
    replace p0 with p in *; replace k0 with k in *; try apply T.
    clear T p0 k0 Hp0 Hk0. apply Hlt. exists p, k'.
    repeat (split; try assumption); try apply (Succ_NaturalNumber k k' Hk Hk').
    destruct Hk' as [Sk [HSk Hk']]. apply Hk'. destruct H as [H | H].
    + left. assumption.
    + right. apply HSk. assumption.
Qed.

Definition Lt_w (m n : set) : Prop :=
  exists lt mn, LessThan_w lt /\ OrdPair m n mn /\ In mn lt.

Definition Le_w (m n : set) : Prop :=
  exists le mn, LessThanEq_w le /\ OrdPair m n mn /\ In mn le.

Corollary Nats_sets_of_smaller_nats : forall n x, NaturalNumber n ->
  In x n <-> NaturalNumber n /\ Lt_w x n.
Proof.
  intros n x Hn. split; intros H.
  - split; try assumption. lt_w. ordpair x n. rename x0 into xn. rename H into Hxn.
    exists lt, xn. repeat (split; try assumption).
    apply Hlt. exists x, n. repeat (split; try assumption).
    omga. apply Homga. apply (Enderton4G omga Homga n x); try assumption.
    apply Homga, Hn.
  - destruct H as [_ [lt [xn [Hlt [Hxn H]]]]].
    apply Hlt in H. destruct H as [x' [n' [Hxn' [Hx' [Hn' H]]]]].
    assert (T : x = x' /\ n = n').
    { apply (Enderton3A x n x' n' xn xn Hxn Hxn'); trivial. }
    replace x' with x in *; replace n' with n in *; try apply T; assumption.
Qed.

Lemma lt_relation_on_omega : forall lt omga, LessThan_w lt -> Nats omga ->
  RelationOn lt omga.
Proof.
  intros lt omga Hlt Homga. intros mn Hmn.
  apply Hlt in Hmn. destruct Hmn as [m [n [Hmn [Hm [Hn H]]]]].
  exists m, n. repeat (split; try assumption); apply Homga; assumption.
Qed.

Lemma lt_transitive : forall lt, LessThan_w lt -> Transitive lt.
Proof.
  intros lt Hlt m n p mn np mp Hmn Hnp Hmp H I.
  apply Hlt. apply Hlt in H. apply Hlt in I.
  destruct H as [m' [n' [Hmn' [Hm [Hn H]]]]].
  assert (T : m = m' /\ n = n').
  { apply (Enderton3A m n m' n' mn mn Hmn Hmn'); trivial. }
  replace m' with m in *; replace n' with n in *; try apply T.
  clear T m' n' Hmn'. destruct I as [n' [p' [Hnp' [_ [Hp I]]]]].
  assert (T : n = n' /\ p = p').
  { apply (Enderton3A n p n' p' np np Hnp Hnp'); trivial. }
  replace n' with n in *; replace p' with p in *; try apply T.
  clear T n' p' Hnp'. exists m, p. repeat (split; try assumption).
  apply (Enderton4F p Hp n m); try assumption.
Qed.

Lemma Enderton4La : forall lt m n m' n' mn m'n', LessThan_w lt ->
  NaturalNumber m -> NaturalNumber n -> Succ m m' -> Succ n n' ->
  OrdPair m n mn -> OrdPair m' n' m'n' -> In mn lt <-> In m'n' lt.
Proof.
  intros lt m n m' n' mn m'n' Hlt Hm Hn Hm' Hn' Hmn Hm'n'. split; intros H.
  - generalize dependent m'n'. generalize dependent mn. generalize dependent n'.
    generalize dependent m'. generalize dependent m.
    omga. build_set set
      (fun (lt c n : set) => forall m, NaturalNumber m -> forall m', Succ m m' ->
        forall n', Succ n n' -> forall mn, OrdPair m n mn -> In mn lt ->
        forall m'n', OrdPair m' n' m'n' -> In m'n' lt) lt omga.
    rename x into T. rename H into HT. apply HT.
    replace T with omga; try apply Homga, Hn. symmetry. clear n Hn.
    apply Induction_Principle_for_Omega; try assumption; try split;
    try (intros t Ht; apply HT, Ht).
    + empty. rename x into o. rename H into Ho. exists o. split; try assumption.
      apply HT. split; try apply Homga, Zero_NaturalNumber, Ho.
      intros m Hm m' Hm' n' Hn' mn Hmn H m'n' Hm'n'.
      apply Hlt. exists m', n'. repeat (split; try assumption).
      * apply (Succ_NaturalNumber m m'); try assumption.
      * apply (Succ_NaturalNumber o n'); try assumption;
        apply (Zero_NaturalNumber), Ho.
      * apply Hlt in H. destruct H as [m0 [n0 [Hmn0 [Hm0 [Hn0 H]]]]].
        assert (P : m = m0 /\ o = n0).
        { apply (Enderton3A m o m0 n0 mn mn Hmn Hmn0); trivial. }
        replace m0 with m in *; replace n0 with o in *; try apply P.
        destruct (Ho m); try assumption.
    + intros n n' Hn' Hn. apply HT in Hn. destruct Hn as [Hn IH].
      apply HT. apply Homga in Hn.
      split; try apply Homga, (Succ_NaturalNumber n n' Hn Hn').
      intros m Hm m' Hm' n'' Hn'' mn' Hmn' H m'n'' Hm'n''.
      apply Hlt. exists m', n''. split; try assumption.
      split; try apply (Succ_NaturalNumber m m' Hm Hm').
      split; try apply (Succ_NaturalNumber n' n''
        (Succ_NaturalNumber n n' Hn Hn') Hn'').
      apply Hlt in H. destruct H as [m0 [n'0 [Hmn'0 [Hm0 [Hn'0 H]]]]].
      assert (P : m = m0 /\ n' = n'0).
      { apply (Enderton3A m n' m0 n'0 mn' mn' Hmn' Hmn'0); trivial. }
      replace m0 with m in *; replace n'0 with n' in *; try apply P.
      clear P m0 n'0 Hmn'0 Hm0.
      destruct Hn'' as [Sn' [HSn' Hn'']]. apply Hn''.
      destruct Hn' as [Sn [HSn Hn']]. apply Hn' in H.
      destruct H as [H | H].
      * left. ordpair m n. rename x into mn. rename H0 into Hmn.
        ordpair m' n'. rename x into m'n'. rename H0 into Hm'n'.
        assert (P : In mn lt).
        { apply Hlt. exists m, n. repeat (split; try assumption). }
        assert (Q : Succ n n').
        { exists Sn. split; assumption. }
        assert (R : In m'n' lt).
        { apply (IH m Hm m' Hm' n' Q mn Hmn P m'n' Hm'n'). }
        apply Hlt in R. destruct R as [m'0 [n'0 [Hm'n'0 [Hm'0 [Hn'0' R]]]]].
        assert (S : m' = m'0 /\ n' = n'0).
        { apply (Enderton3A m' n' m'0 n'0 m'n' m'n' Hm'n' Hm'n'0); trivial. }
        replace m'0 with m' in *; replace n'0 with n' in *; try apply S; apply R.
      * right. apply HSn'. apply (Succ_Unique m m' n'); try assumption.
        apply HSn in H. replace m with n; try assumption.
        exists Sn. split; assumption.
  - apply Hlt. exists m, n. repeat (split; try assumption).
    apply Hlt in H. destruct H as [m'0 [n'0 [Hm'n'0 [_ [_ H]]]]].
    assert (P : m' = m'0 /\ n' = n'0).
    { apply (Enderton3A m' n' m'0 n'0 m'n' m'n' Hm'n' Hm'n'0); trivial. }
    replace m'0 with m' in *; replace n'0 with n' in *; try apply P.
    destruct Hn' as [Sn [HSn Hn']]. destruct Hm' as [Sm [HSm Hm']].
    apply Hn' in H. destruct H as [H | H].
    + apply (Enderton4F n Hn m' m); try assumption.
      apply Hm'. right. apply HSm. trivial.
    + apply HSn in H. replace n with m'. apply Hm'. right. apply HSm. trivial.
Qed.

Lemma Enderton4Lb : forall m, NaturalNumber m -> ~ In m m.
Proof.
  intros m Hm. omga. build_set set (fun (t c m : set) => ~ In m m) omga omga.
  rename x into T. rename H into HT. apply HT.
  replace T with omga; try apply Homga, Hm. clear m Hm. symmetry.
  apply Induction_Principle_for_Omega; try assumption; try split;
  try (intros t Ht; apply HT, Ht).
  - empty. rename x into o. rename H into Ho. exists o. split; try assumption.
    apply HT. split; try apply Homga, Zero_NaturalNumber, Ho.
    intros C. apply (Ho o). assumption.
  - intros m m' Hm' Hm. apply HT in Hm. destruct Hm as [Hm IH].
    apply HT. apply Homga in Hm.
    split; try apply Homga, (Succ_NaturalNumber m m' Hm Hm').
    intros C. apply IH. lt_w. ordpair m m. rename x into mm. rename H into Hmm.
    ordpair m' m'. rename x into m'm'. rename H into Hm'm'.
    assert (P : In mm lt).
    { apply (Enderton4La lt m m m' m' mm m'm'); try assumption.
      apply Hlt. exists m', m'. repeat (split; try assumption);
      apply (Succ_NaturalNumber m m' Hm Hm'). }
    apply Hlt in P. destruct P as [m0 [m0' [Hmm0 [_ [_ P]]]]].
    assert (Q : m = m0 /\ m = m0').
    { apply (Enderton3A m m m0 m0' mm mm Hmm Hmm0); trivial. }
    replace m0 with m in *; replace m0' with m in *; try assumption; try apply Q.
Qed.

Lemma Zero_Leq_N : forall o n, Empty o -> NaturalNumber n -> In_ o n.
Proof.
  intros o n Ho Hn. generalize dependent o. omga.
  build_set set (fun (t c n : set) => forall o, Empty o -> In_ o n) omga omga.
  rename x into T. rename H into HT. apply HT.
  replace T with omga; try apply Homga, Hn. symmetry. clear n Hn.
  apply Induction_Principle_for_Omega; try assumption; try split;
  try (intros t Ht; apply HT, Ht).
  - empty. rename x into o. rename H into Ho. exists o. split; try assumption.
    apply HT. split; try apply Homga, Zero_NaturalNumber, Ho.
    intros o' Ho'. replace o' with o; try (right; trivial).
    apply Empty_Unique; assumption.
  - intros n n' Hn' Hn. apply HT in Hn. destruct Hn as [Hn IH].
    apply HT. apply Homga in Hn.
    split; try apply Homga, (Succ_NaturalNumber n n' Hn Hn').
    intros o Ho. destruct (IH o Ho) as [IHo | IHo].
    + left. apply (Enderton4F n'
        (Succ_NaturalNumber n n' Hn Hn') n o); try assumption.
      destruct Hn' as [Sn [HSn Hn']]. apply Hn'. right. apply HSn. trivial.
    + destruct Hn' as [Sn [HSn Hn']]. left. apply Hn'. right.
      apply HSn. assumption.
Qed.

Lemma Trichotomous_w : forall omga lt, Nats omga -> LessThan_w lt ->
  Trichotomous lt omga.
Proof.
  intros omga lt Homga Hlt m n mn nm Hm. generalize dependent nm.
  generalize dependent mn. generalize dependent n.
  build_set set
    (fun (lt omga m : set) => forall n mn nm, In n omga -> OrdPair m n mn ->
      OrdPair n m nm -> In mn lt /\ m <> n /\ ~ In nm lt \/
      ~ In mn lt /\ m = n /\ ~ In nm lt \/ ~ In mn lt /\ m <> n /\ In nm lt)
    lt omga.
  rename x into T. rename H into HT. apply HT.
  replace T with omga; try assumption. clear m Hm. symmetry.
  apply Induction_Principle_for_Omega; try assumption; try split;
  try (intros t Ht; apply HT, Ht).
  - empty. rename x into o. rename H into Ho. exists o. split; try assumption.
    apply HT. split; try apply Homga, Zero_NaturalNumber, Ho.
    intros n on no Hn Hon Hno. apply Homga in Hn.
    destruct (Zero_Leq_N o n Ho Hn) as [H | H].
    + left. split; try split.
      * apply Hlt. exists o, n. repeat (split; try assumption).
        apply Zero_NaturalNumber, Ho.
      * intros C. rewrite C in H. apply (Enderton4Lb n); assumption.
      * intros C. apply (Ho n). apply Hlt in C.
        destruct C as [n' [o' [Hno' [_ [_ C]]]]].
        assert (P : n = n' /\ o = o').
        { apply (Enderton3A n o n' o' no no Hno Hno'). trivial. }
        replace n' with n in *; replace o' with o in *; try apply P. apply C.
    + right. left. split; try split; try assumption.
      * intros C. apply (Enderton4Lb n); try assumption.
        apply Hlt in C. destruct C as [o' [n' [Hon' [_ [_ C]]]]].
        assert (T0 : o = o' /\ n = n').
        { apply (Enderton3A o n o' n' on on); try assumption; trivial. }
        replace o' with o in *; replace n' with n in *; try apply T0.
        rewrite H in C. assumption.
      * intros C. apply (Enderton4Lb n); try assumption.
        apply Hlt in C. destruct C as [n' [o' [Hno' [_ [_ C]]]]].
        assert (T0 : n = n' /\ o = o').
        { apply (Enderton3A n o n' o' no no); try assumption; trivial. }
        replace o' with o in *; replace n' with n in *; try apply T0.
        rewrite H in C. assumption.
  - intros m m' Hm' Hm. apply HT in Hm. destruct Hm as [Hm IH].
    apply HT. apply Homga in Hm.
    split; try apply Homga, (Succ_NaturalNumber m m' Hm Hm').
    intros n m'n nm' Hn Hm'n Hnm'.
    ordpair m n. rename H into Hmn. rename x into mn.
    ordpair n m. rename H into Hnm. rename x into nm.
    destruct (IH n mn nm Hn Hmn Hnm) as [IH0 | [IH0 | IH0]];
    destruct IH0 as [IH0 [IH1 IH2]].
    + apply Homga in Hn. succ n. rename x into n'. rename H into Hn'. le_w.
      ordpair m' n'. rename x into m'n'. rename H into Hm'n'.
      assert (P : Lt_w m' n').
      { exists lt, m'n'. repeat (split; try assumption).
        apply (Enderton4La lt m n m' n' mn m'n' Hlt Hm Hn Hm' Hn' Hmn Hm'n').
        assumption. }
      destruct (lt_w_succ_iff_le_w lt le m' n n' m'n' m'n) as [H _];
      try assumption; try (apply (Succ_NaturalNumber m m'); assumption).
      assert (Q : In m'n' lt).
      { destruct P as [lt' [m'n'0 [Hlt' [Hm'n'o P]]]].
        replace lt with lt'; try (apply (LessThan_w_Unique lt' lt Hlt' Hlt)).
        replace m'n' with m'n'0; try assumption.
        apply (OrdPair_Unique m' n'); try assumption. }
      apply H in Q. apply Hle in Q.
      destruct Q as [m'0 [n0 [Hm'n0 [_ [_ Q]]]]].
      assert (R : m' = m'0 /\ n = n0).
      { apply (Enderton3A m' n m'0 n0 m'n m'n Hm'n Hm'n0). trivial. }
      replace m'0 with m' in *; replace n0 with n in *; try apply R.
      clear R m'0 n0 Hm'n0. destruct Q as [Q | Q].
      * left. split; try split.
        { apply Hlt. exists m', n. repeat (split; try assumption);
          try (apply (Succ_NaturalNumber m); assumption);
          try (apply Homga; assumption). }
        { intros C. rewrite C in Q. apply (Enderton4Lb n); assumption. }
        { intros C. apply (Enderton4Lb m');
          try (apply (Succ_NaturalNumber m); assumption).
          apply (Enderton4F m' (Succ_NaturalNumber m m' Hm Hm') n m'); try assumption.
          apply Hlt in C. destruct C as [n0 [m'0 [Hnm'0 [_ [_ C]]]]].
          assert (R : n = n0 /\ m' = m'0).
          { apply (Enderton3A n m' n0 m'0 nm' nm' Hnm' Hnm'0). trivial. }
          replace n0 with n in *; replace m'0 with m' in *; try apply R. apply C. }
      * right. left. split; try split; try assumption.
        { intros C. apply (Enderton4Lb n); try assumption.
          apply Hlt in C. destruct C as [m'0 [n0 [Hm'n0 [_ [_ C]]]]].
          replace m'0 with m' in C;
          try (apply (Enderton3A m' n m'0 n0 m'n m'n Hm'n Hm'n0); try trivial).
          replace n0 with n in *;
          try (apply (Enderton3A m' n m'0 n0 m'n m'n Hm'n Hm'n0); try trivial).
          rewrite Q in C. assumption. }
        { intros C. apply (Enderton4Lb m'); try assumption.
          try (apply (Succ_NaturalNumber m); assumption).
          apply Hlt in C. destruct C as [n0 [m'0 [Hnm'0 [_ [_ C]]]]].
          replace m'0 with m' in C;
          try (apply (Enderton3A n m' n0 m'0 nm' nm' Hnm' Hnm'0); try trivial).
          replace n0 with n in *;
          try (apply (Enderton3A n m' n0 m'0 nm' nm' Hnm' Hnm'0); try trivial).
          rewrite <- Q in C. assumption. }
    + apply Homga in Hn. right. right. split; try split.
      * intros C. apply (Enderton4Lb n); try assumption;
        try (apply (Succ_NaturalNumber m); assumption).
        apply (Enderton4F n Hn m' n).
        { apply Hlt in C. destruct C as [m'0 [n0 [Hm'n0 [_ [_ C]]]]].
          replace m'0 with m' in C;
          try (apply (Enderton3A m' n m'0 n0 m'n m'n Hm'n Hm'n0); try trivial).
          replace n0 with n in *;
          try (apply (Enderton3A m' n m'0 n0 m'n m'n Hm'n Hm'n0); try trivial).
          assumption. }
        { replace n with m. destruct Hm' as [Sm [HSm Hm']].
          apply Hm'. right. apply HSm. trivial. }
      * intros C. apply (Enderton4Lb n); try assumption.
        apply (Enderton4F n Hn m' n).
        { replace m' with m. replace n with m'. destruct Hm' as [Sm [HSm Hm']].
          apply Hm'. right. apply HSm. trivial.
          transitivity n; try assumption; symmetry; assumption. }
        { replace n with m. destruct Hm' as [Sm [HSm Hm']].
          apply Hm'. right. apply HSm. trivial. }
      * apply Hlt. exists n, m'. repeat (split; try assumption).
        { apply (Succ_NaturalNumber m m'); assumption. }
        { replace n with m. destruct Hm' as [Sm [HSm Hm']].
          apply Hm'. right. apply HSm. trivial. }
    + apply Homga in Hn. right. right. split; try split.
      * intros C. apply (Enderton4Lb n); try assumption.
        ordpair n n. rename x into nn. rename H into Hnn.
        assert (P : In nn lt).
        { apply (lt_transitive lt Hlt n m' n nm' m'n nn); try assumption.
          ordpair m m'. rename x into mm'. rename H into Hmm'.
          apply (lt_transitive lt Hlt n m m' nm mm' nm'); try assumption.
          apply Hlt. exists m, m'. repeat (split; try assumption).
          try (apply (Succ_NaturalNumber m); try assumption).
          destruct Hm' as [Sm [HSm Hm']]. apply Hm'.
          right. apply HSm. trivial. }
        apply Hlt in P. destruct P as [n0 [n1 [Hnn' [_ [_ P]]]]].
        assert (Q : n = n0 /\ n = n1).
        { apply (Enderton3A n n n0 n1 nn nn Hnn Hnn'). trivial. }
        replace n0 with n in *; replace n1 with n in *; try apply Q; assumption.
      * intros C. apply (Enderton4Lb m); try assumption.
        apply (Enderton4F m Hm m' m).
        { replace m' with n. apply Hlt in IH2.
          destruct IH2 as [n0 [m0 [Hnm0 [_ [_ IH2]]]]].
          assert (P : n = n0 /\ m = m0).
          { apply (Enderton3A n m n0 m0 nm nm Hnm Hnm0). trivial. }
          replace n0 with n in *; replace m0 with m in *; try apply P; assumption. }
        { destruct Hm' as [Sm [HSm Hm']]. apply Hm'. right. apply HSm. trivial. }
      * le_w. apply (lt_w_succ_iff_le_w lt le n m m' nm' nm); try assumption.
        apply Hle. exists n, m. repeat (split; try assumption).
        left. apply Hlt in IH2. destruct IH2 as [n0 [m0 [Hnm0 [_ [_ IH2]]]]].
        assert (P : n = n0 /\ m = m0).
        { apply (Enderton3A n m n0 m0 nm nm Hnm Hnm0). trivial. }
        replace n0 with n in *; replace m0 with m in *; try apply P; assumption.
Qed.

Corollary Nats_LinearOrdered : forall omga lt, Nats omga -> LessThan_w lt ->
  LinearOrdering lt omga.
Proof.
  intros omga lt Homga Hlt. split; try split.
  - apply (lt_relation_on_omega); try assumption.
  - apply lt_transitive; assumption.
  - apply Trichotomous_w; try assumption.
Qed.

Definition ProperSubset (A B : set) : Prop := Subset A B /\ A <> B.

Corollary Enderton4M : forall m n, NaturalNumber m -> NaturalNumber n -> 
  In m n <-> ProperSubset m n.
Proof.
  intros m n Hm Hn. split; intros H.
  - split.
    + intros p Hp. apply (Enderton4F n Hn m p); try assumption.
    + intros C. rewrite C in H. apply (Enderton4Lb n); assumption.
  - lt_w. omga. ordpair m n. rename x into mn. rename H0 into Hmn.
    ordpair n m. rename x into nm. rename H0 into Hnm.
    apply Homga in Hm. apply Homga in Hn.
    destruct (Trichotomous_w omga lt Homga Hlt m n mn nm Hm Hn Hmn Hnm) as
      [[H0 [H1 H2]] | [[H0 [H1 H2]] | [H0 [H1 H2]]]].
    + apply Hlt in H0. destruct H0 as [m' [n' [Hmn' [_ [_ H0]]]]].
      assert (T : m = m' /\ n = n').
      { apply (Enderton3A m n m' n' mn mn Hmn Hmn'). trivial. }
      replace m' with m in *; replace n' with n in *; try assumption; try apply T.
    + destruct H as [_ H]. destruct (H H1).
    + apply Homga in Hn. destruct (Enderton4Lb n); try assumption.
      destruct H as [H _]. apply H. apply Hlt in H2.
      destruct H2 as [n' [m' [Hnm' [_ [_ H2]]]]].
      assert (T : n = n' /\ m = m').
      { apply (Enderton3A n m n' m' nm nm Hnm Hnm'). trivial. }
      replace n' with n in *; replace m' with m in *; try assumption; apply T.
Qed.

Corollary Enderton4M' : forall m n, NaturalNumber m -> NaturalNumber n ->
  In_ m n <-> Subset m n.
Proof.
  intros m n Hm Hn. split; intros H.
  - destruct H as [H | H].
    + apply (Enderton4M m n Hm Hn). assumption.
    + rewrite H. apply Subset_Reflexive.
  - assert (P : m = n \/ m <> n). { apply REM. }
    destruct P as [P | P].
    + right. assumption.
    + left. apply (Enderton4M m n Hm Hn). split; try assumption.
Qed.

Theorem Enderton4N : forall m n p mp np, NaturalNumber m -> NaturalNumber n ->
  NaturalNumber p -> Sum_w m p mp -> Sum_w n p np -> In m n <-> In mp np.
Proof.
  destruct Enderton4I as [A1 A2].
  assert (I : forall m n p mp np, NaturalNumber m -> NaturalNumber n ->
    NaturalNumber p -> Sum_w m p mp -> Sum_w n p np -> In m n -> In mp np).
  { intros m n p mp np Hm Hn Hp. omga.
    generalize dependent np. generalize dependent mp.
    build_set (prod set set)
      (fun (t : set * set) (c p : set) => forall mp np, Sum_w (fst t) p mp ->
        Sum_w (snd t) p np -> In m n -> In mp np) (m, n) omga.
    rename x into T. rename H into HT. simpl in HT. apply HT.
    replace T with omga; try apply Homga, Hp. symmetry. clear p Hp.
    apply Induction_Principle_for_Omega; try assumption; try split;
    try (intros t Ht; apply HT, Ht).
    + empty. exists x. split; try assumption. apply HT.
      split; try apply Homga, Zero_NaturalNumber; try assumption.
      intros mp np Hmp Hnp P. simpl in *.
      replace mp with m. replace np with n. assumption.
      * apply (Sum_w_Unique n x n np); try assumption;
        try (apply Zero_NaturalNumber, H).
        apply A1; assumption.
      * apply (Sum_w_Unique m x m mp); try assumption;
        try (apply Zero_NaturalNumber, H).
        apply A1; assumption.
    + intros p p' Hp' Hp. apply HT in Hp. destruct Hp as [Hp IH].
      apply HT. apply Homga in Hp.
      split; try apply Homga, (Succ_NaturalNumber p p' Hp Hp').
      intros mp' np' Hmp' Hnp' H. simpl in *.
      sum_w m p Hm Hp. rename x into mp. rename H0 into Hmp.
      sum_w n p Hn Hp. rename x into np. rename H0 into Hnp. lt_w.
      ordpair mp np. rename x into mpnp. rename H0 into Hmpnp.
      succ mp. rename x into Smp. rename H0 into HSmp.
      succ np. rename x into Snp. rename H0 into HSnp.
      ordpair Smp Snp. rename x into SmpSnp. rename H0 into HSmpSnp.
      assert (P : In mpnp lt).
      { apply Hlt. exists mp, np. repeat (split; try assumption);
        try apply (IH mp np Hmp Hnp H);
        try (apply (Sum_NaturalNumber m p); assumption);
        try (apply (Sum_NaturalNumber n p); assumption). }
      apply (Enderton4La lt mp np Smp Snp mpnp SmpSnp) in P; try assumption;
      try (apply (Sum_NaturalNumber m p); assumption);
      try (apply (Sum_NaturalNumber n p); assumption). 
      apply Hlt in P. destruct P as [Smp' [Snp' [HSmpSnp' [HSmp' [HSnp' P]]]]].
      assert (Q : Smp = Smp' /\ Snp = Snp').
      { apply (Enderton3A Smp Snp Smp' Snp' SmpSnp SmpSnp); try assumption; trivial. }
      replace Smp' with Smp in *; replace Snp' with Snp in *; try apply Q.
      replace mp' with Smp. replace np' with Snp. assumption.
      * symmetry. apply (A2 n p p' np); try assumption.
      * symmetry. apply (A2 m p p' mp); try assumption. }
  intros m n p mp np Hm Hn Hp Hmp Hnp.
  split; try (apply (I m n p mp np); assumption).
  intros H. ordpair m n. rename x into mn. rename H0 into Hmn.
  ordpair n m. rename x into nm. rename H0 into Hnm. lt_w. omga.
  destruct (Trichotomous_w omga lt Homga Hlt m n mn nm) as [P | [P | P]];
  try assumption; try apply Homga, Hn; try apply Homga, Hm;
  destruct P as [P0 [P1 P2]].
  + apply Hlt in P0. destruct P0 as [m' [n' [Hmn' [Hm' [Hn' P0]]]]].
    assert (Q : m = m' /\ n = n').
    { apply (Enderton3A m n m' n' mn mn Hmn Hmn'); trivial. }
    replace m' with m in *; replace n' with n in *; try apply Q; assumption.
  + destruct (Enderton4Lb np); try (apply (Sum_NaturalNumber n p); assumption).
    replace mp with np in H; try assumption.
    apply (Sum_w_Unique n p); try assumption.
    replace n with m. assumption.
  + assert (Q : In np mp).
    { apply (I n m p); try assumption. apply Hlt in P2.
      destruct P2 as [n' [m' [Hnm' [Hn' [Hm' P2]]]]].
      assert (R : n = n' /\ m = m').
      { apply (Enderton3A n m n' m' nm nm Hnm Hnm'); trivial. }
      replace n' with n in *; replace m' with m in *; try apply R; assumption. }
    destruct (Enderton4Lb mp); try (apply (Sum_NaturalNumber m p); assumption).
    apply (Enderton4F mp (Sum_NaturalNumber m p mp Hm Hp Hmp) np mp); assumption.
Qed.

Theorem Enderton4N' : forall m n p mp np, NaturalNumber m -> NaturalNumber n ->
  NaturalNumber p -> ~Empty p -> Prod_w m p mp -> Prod_w n p np ->
  In m n <-> In mp np.
Proof.
  omga. lt_w. destruct Enderton4I as [A1 A2]. destruct Enderton4J as [M1 M2].
  assert (I : forall m n p mp np, NaturalNumber m -> NaturalNumber n ->
    NaturalNumber p -> ~ Empty p -> Prod_w m p mp -> Prod_w n p np ->
    In m n -> In mp np).
  { intros m n p mp np Hm Hn Hp. generalize dependent np. generalize dependent mp.
    build_set (prod set set)
      (fun (t : set * set) (c p : set) => forall mp np, ~Empty p ->
        Prod_w (fst t) p mp -> Prod_w (snd t) p np -> In (fst t) (snd t) ->
        In mp np)
      (m, n) omga.
    rename x into T. rename H into HT. apply HT.
    replace T with omga; try apply Homga, Hp. symmetry. clear p Hp.
    apply Induction_Principle_for_Omega; try assumption; try split;
    try (intros t Ht; apply HT, Ht).
    - empty. rename x into o. rename H into Ho. exists o. split; try assumption.
      apply HT. split; try apply Homga, Zero_NaturalNumber, Ho.
      intros mp np C. apply C in Ho. destruct Ho.
    - intros p p' Hp' Hp. apply HT in Hp. destruct Hp as [Hp IH].
      apply HT. apply Homga in Hp.
      split; try apply Homga, (Succ_NaturalNumber p p' Hp Hp').
      assert (P : Empty p \/ ~ Empty p). { apply REM. }
      intros mp' np' Hne Hmp' Hnp' H. simpl in *. destruct P as [P | P].
      + replace mp' with m. replace np' with n. assumption.
        * prod_w n p Hn Hp. rename x into np. rename H0 into Hnp.
          sum_w n np Hn (Prod_NaturalNumber n p np Hn Hp Hnp).
          rename x into nnp. rename H0 into Hnnp. transitivity nnp.
          { sum_w n p Hn Hp. rename x into npp. rename H into Hnpp.
            transitivity npp.
            - apply (Sum_w_Unique n p); try assumption. apply A1; assumption.
            - apply (Sum_w_Unique n p); try assumption.
              replace p with np; try assumption.
              apply (Prod_w_Unique n p); try assumption. apply M1; assumption. }
          { symmetry. apply (M2 n p np p'); try assumption. }
        * prod_w m p Hm Hp. rename x into mp. rename H0 into Hmp.
          sum_w m mp Hm (Prod_NaturalNumber m p mp Hm Hp Hmp).
          rename x into mmp. rename H0 into Hmmp. transitivity mmp.
          { sum_w m p Hm Hp. rename x into mpp. rename H into Hmpp.
            transitivity mpp.
            - apply (Sum_w_Unique m p); try assumption. apply A1; assumption.
            - apply (Sum_w_Unique m p); try assumption.
              replace p with mp; try assumption.
              apply (Prod_w_Unique m p); try assumption. apply M1; assumption. }
          { symmetry. apply (M2 m p mp p'); try assumption. }
      + prod_w m p Hm Hp. rename x into mp. rename H0 into Hmp.
        prod_w n p Hn Hp. rename x into np. rename H0 into Hnp.
        sum_w m mp Hm (Prod_NaturalNumber m p mp Hm Hp Hmp).
        rename x into mmp. rename H0 into Hmmp.
        sum_w n np Hn (Prod_NaturalNumber n p np Hn Hp Hnp).
        rename x into nnp. rename H0 into Hnnp.
        sum_w n mp Hn (Prod_NaturalNumber m p mp Hm Hp Hmp).
        rename x into nmp. rename H0 into Hnmp.
        replace mp' with mmp. replace np' with nnp.
        apply (Enderton4F nnp (Sum_NaturalNumber n np nnp Hn
          (Prod_NaturalNumber n p np Hn Hp Hnp) Hnnp) nmp).
        * sum_w mp n (Prod_NaturalNumber m p mp Hm Hp Hmp) Hn.
          rename x into mpn. rename H0 into Hmpn. replace nmp with mpn.
          sum_w np n (Prod_NaturalNumber n p np Hn Hp Hnp) Hn.
          rename x into npn. rename H0 into Hnpn. replace nnp with npn.
          apply (Enderton4N mp np n mpn npn); try assumption;
          try (apply (Prod_NaturalNumber m p); assumption);
          try (apply (Prod_NaturalNumber n p); assumption).
          apply (IH mp np P Hmp Hnp H).
          { apply (Enderton4K2 np n); try assumption.
            apply (Prod_NaturalNumber n p); assumption. }
          { apply (Enderton4K2 mp n); try assumption.
            apply (Prod_NaturalNumber m p); assumption. }
        * apply (Enderton4N m n mp); try assumption.
          apply (Prod_NaturalNumber m p); assumption.
        * symmetry. apply (M2 n p np p'); try assumption.
        * symmetry. apply (M2 m p mp p'); assumption. }
  intros m n p mp np Hm Hn Hp Hne Hmp Hnp.
  split; try apply (I m n p mp np); try assumption.
  intros H. ordpair m n. rename x into mn. rename H0 into Hmn.
  ordpair n m. rename x into nm. rename H0 into Hnm.
  destruct (Trichotomous_w omga lt Homga Hlt m n mn nm) as [P | [P | P]];
  try assumption; try (apply Homga; apply Hn); try (apply Homga; apply Hm);
  destruct P as [P0 [P1 P2]].
  - apply Hlt in P0. destruct P0 as [m' [n' [Hmn' [_ [_ P0]]]]].
    assert (P : m = m' /\ n = n').
    { apply (Enderton3A m n m' n' mn mn Hmn Hmn'); trivial. }
    replace m' with m in *; replace n' with n in *; try apply P; assumption.
  - replace np with mp in H. destruct (Enderton4Lb mp); try assumption;
    try (apply (Prod_NaturalNumber m p); assumption).
    apply (Prod_w_Unique m p); try assumption. replace m with n; assumption.
  - assert (Q : In n m).
    { apply Hlt in P2. destruct P2 as [n' [m' [Hnm' [_ [_ P2]]]]].
      assert (P : n = n' /\ m = m').
      { apply (Enderton3A n m n' m' nm nm Hnm Hnm'); trivial. }
      replace m' with m in *; replace n' with n in *; try apply P; assumption. }
    destruct (Enderton4Lb mp (Prod_NaturalNumber m p mp Hm Hp Hmp)).
    apply (Enderton4F mp (Prod_NaturalNumber m p mp Hm Hp Hmp) np); try assumption.
    apply (I n m p np mp); try assumption.
Qed.    

Corollary Enderton4P : forall m n p mp np, NaturalNumber m -> NaturalNumber n ->
  NaturalNumber p -> Sum_w m p mp -> Sum_w n p np -> mp = np -> m = n.
Proof.
  intros m n p mp np Hm Hn Hp Hmp Hnp H. omga. lt_w.
  ordpair m n. rename x into mn. rename H0 into Hmn.
  ordpair n m. rename x into nm. rename H0 into Hnm.
  destruct (Trichotomous_w omga lt Homga Hlt m n mn nm) as [P | [P | P]];
  try assumption; try apply Homga; try assumption; destruct P as [P0 [P1 P2]].
  - assert (P : In m n).
    { apply Hlt in P0. destruct P0 as [m' [n' [Hmn' [_ [_ P0]]]]].
      assert (T : m = m' /\ n = n').
      { apply (Enderton3A m n m' n' mn mn Hmn Hmn'); trivial. }
      replace m' with m in *; replace n' with n in *; try apply T; assumption. }
    assert (Q : In mp np).
    { apply (Enderton4N m n p mp np); try assumption. }
    rewrite H in Q. destruct (Enderton4Lb np); try assumption.
    apply (Sum_NaturalNumber n p); assumption.
  - assumption.
  - assert (P : In n m).
    { apply Hlt in P2. destruct P2 as [n' [m' [Hnm' [_ [_ P2]]]]].
      assert (T : n = n' /\ m = m').
      { apply (Enderton3A n m n' m' nm nm Hnm Hnm'); trivial. }
      replace m' with m in *; replace n' with n in *; try apply T; assumption. }
    assert (Q : In np mp).
    { apply (Enderton4N n m p np mp); try assumption. }
    rewrite H in Q. destruct (Enderton4Lb np); try assumption.
    apply (Sum_NaturalNumber n p); assumption.
Qed.

Corollary Enderton4P' : forall m n p mp np, NaturalNumber m -> NaturalNumber n ->
  NaturalNumber p -> Prod_w m p mp -> Prod_w n p np -> mp = np -> ~Empty p -> m = n.
Proof.
  intros m n p mp np Hm Hn Hp Hmp Hnp H Hne. omga. lt_w.
  ordpair m n. rename x into mn. rename H0 into Hmn.
  ordpair n m. rename x into nm. rename H0 into Hnm.
  destruct (Trichotomous_w omga lt Homga Hlt m n mn nm) as [P | [P | P]];
  try assumption; try apply Homga; try assumption; destruct P as [P0 [P1 P2]].
  - assert (P : In m n).
    { apply Hlt in P0. destruct P0 as [m' [n' [Hmn' [_ [_ P0]]]]].
      assert (T : m = m' /\ n = n').
      { apply (Enderton3A m n m' n' mn mn Hmn Hmn'); trivial. }
      replace m' with m in *; replace n' with n in *; try apply T; assumption. }
    assert (Q : In mp np).
    { apply (Enderton4N' m n p mp np); try assumption. }
    rewrite H in Q. destruct (Enderton4Lb np); try assumption.
    apply (Prod_NaturalNumber n p); assumption.
  - assumption.
  - assert (P : In n m).
    { apply Hlt in P2. destruct P2 as [n' [m' [Hnm' [_ [_ P2]]]]].
      assert (T : n = n' /\ m = m').
      { apply (Enderton3A n m n' m' nm nm Hnm Hnm'); trivial. }
      replace m' with m in *; replace n' with n in *; try apply T; assumption. }
    assert (Q : In np mp).
    { apply (Enderton4N' n m p np mp); try assumption. }
    rewrite H in Q. destruct (Enderton4Lb np); try assumption.
    apply (Prod_NaturalNumber n p); assumption.
Qed.

Definition LeastElt (a A : set) : Prop :=
  In a A /\ forall n, In n A -> In_ a n.

Theorem Well_Ordering_of_w: forall A omga, Nats omga -> Subset A omga ->
  ~ Empty A -> exists m, LeastElt m A.
Proof.
  intros A omga Homga HA. apply ContrapositiveLaw.
  intros C C'. apply C'. lt_w.
  build_set set (fun (A c m : set) => forall n, In n m -> ~ In n A) A omga.
  rename x into B. rename H into HB. intros a Ha.
  apply HA in Ha as Ha'. replace omga with B in Ha'. apply HB in Ha'.
  apply C. exists a. split; try assumption.
  intros n. apply ContrapositiveLaw. intros H C0.
  destruct Ha' as [_ Ha']. apply (Ha' n); try assumption.
  ordpair n a. rename x into na. rename H0 into Hna.
  ordpair a n. rename x into an. rename H0 into Han.
  destruct (Trichotomous_w omga lt Homga Hlt n a na an) as [P | [P | P]];
  try assumption; try apply HA; try assumption;
  destruct P as [P0 [P1 P2]].
  - apply Hlt in P0. destruct P0 as [n' [a' [Hna' [Hn' [Ha0 P0]]]]].
    assert (T : n = n' /\ a = a').
    { apply (Enderton3A n a n' a' na na Hna Hna'); trivial. }
    replace n' with n in *; replace a' with a in *; try apply T; assumption.
  - destruct H. right. symmetry. assumption.
  - destruct H. left. apply Hlt in P2.
    destruct P2 as [a' [n' [Han' [Ha0 [Hn' P2]]]]].
    assert (T : a = a' /\ n = n').
    { apply (Enderton3A a n a' n' an an Han Han'); trivial. }
    replace n' with n in *; replace a' with a in *; try apply T; assumption.
  - apply Induction_Principle_for_Omega; try assumption; try split;
    try (intros t Ht; apply HB, Ht).
    + empty. exists x. split; try assumption. apply HB.
      split; try apply Homga, Zero_NaturalNumber, H.
      intros n Hn. destruct (H n). assumption.
    + intros n n' Hn' Hn. apply HB in Hn. destruct Hn as [Hn IH].
      apply HB. apply Homga in Hn.
      split; try apply Homga, (Succ_NaturalNumber n n' Hn Hn').
      intros m Hm. destruct Hn' as [Sn [HSn Hn']].
      apply Hn' in Hm. destruct Hm as [Hm | Hm].
      * apply IH. assumption.
      * intros D. apply C. exists m. split; try assumption.
        intros p Hp. replace m with n in *;
        try (apply HSn in Hm; symmetry; assumption).
        ordpair n p. rename x into np. rename H into Hnp.
        ordpair p n. rename x into pn. rename H into Hpn.
        destruct (Trichotomous_w omga lt Homga Hlt n p np pn) as [P | [P | P]];
        try assumption; try apply HA; try assumption;
        destruct P as [P0 [P1 P2]].
        { left. apply Hlt in P0. destruct P0 as [n0 [p' [Hnp' [Hn0 [Hp' P0]]]]].
        assert (T : n = n0 /\ p = p').
        { apply (Enderton3A n p n0 p' np np Hnp Hnp'); trivial. }
          replace n0 with n in *; replace p' with p in *; try apply T; assumption. }
        { right. assumption. }
        { destruct (IH p); try assumption. apply Hlt in P2.
          destruct P2 as [p' [n0 [Hpn' [Hn0 [Hp' P2]]]]].
          assert (T : p = p' /\ n = n0).
          { apply (Enderton3A p n p' n0 pn pn Hpn Hpn'); trivial. }
        replace n0 with n in *; replace p' with p in *; try apply T; assumption. }
Qed.

Corollary Enderton4Q : forall omga, Nats omga ->
  ~ exists f, FuncFromInto f omga omga /\ forall n n' fn fn', NaturalNumber n ->
  Succ n n' -> FunVal f n fn -> FunVal f n' fn' -> In fn' fn.
Proof.
  intros omga Homga C. destruct C as [f [[Hf [Hdomf [ranf [Hranf Hsub]]]] H]].
  destruct (Well_Ordering_of_w ranf omga); try assumption.
  - intros C. zero. rename x into o. rename H0 into Ho.
    assert (T : exists domf, Domain f domf /\ In o domf).
    { exists omga. split; try assumption. apply Homga, Zero_NaturalNumber, Ho. }
    funval Hf T f o. rename x into fo. rename H0 into Hfo.
    apply (C fo). apply Hranf. exists o. apply Hfo; assumption.
  - rename x into fn. rename H0 into Hfn.
    destruct Hfn as [I J]. apply Hranf in I.
    destruct I as [n [nfn [Hnfn I]]].
    succ n. rename x into n'. rename H0 into Hn'.
    assert (T : exists domf, Domain f domf /\ In n' domf).
    { exists omga. split; try assumption.
      apply Homga, (Succ_NaturalNumber n); try assumption.
      apply Homga. apply Hdomf. exists fn, nfn. split; assumption. }
    funval Hf T f n'. rename x into fn'. rename H0 into Hfn'.
    destruct (J fn'); try (apply Hranf; exists n'; apply Hfn'; assumption).
    + destruct (Enderton4Lb fn); try apply Homga, Hsub.
      { apply Hranf. exists n, nfn. split; assumption. }
      assert (P : NaturalNumber fn).
      { apply Homga. apply Hsub. apply Hranf. exists n, nfn. split; assumption. }
      apply (Enderton4F fn P fn'); try assumption.
      apply (H n n' fn fn'); try assumption.
      * apply Homga. apply Hdomf. exists fn, nfn. split; assumption.
      * intros _ _. exists nfn. split; assumption.
    + apply (Enderton4Lb fn); try apply Homga, Hsub.
      { apply Hranf. exists n, nfn. split; assumption. }
      apply (H n n' fn fn); try assumption.
      * apply Homga. apply Hdomf. exists fn, nfn. split; assumption.
      * intros _ _. exists nfn. split; assumption.
      * replace fn with fn'. assumption.
Qed.

Theorem Strong_Induction_Principle_for_w : forall omga A, Nats omga ->
  Subset A omga ->
  (forall n, In n omga -> (forall x, In x n -> In x A) -> In n A) ->
  A = omga.
Proof.
  intros omga A Homga HA H. lt_w. assert (P : A = omga \/ A <> omga).
  { apply REM. }
  destruct P as [P | P]; try assumption.
  minus omga A. rename x into wmA. rename H0 into HwmA.
  destruct (Well_Ordering_of_w wmA omga) as [m Hm]; try assumption.
  - intros x I. apply HwmA in I. apply I.
  - intros C. apply P. apply SubsetSymmetric_iff_Equal. split; try assumption.
    intros a Ha. assert (Q : In a A \/ ~ In a A). { apply REM. }
    destruct Q as [Q | Q]; try assumption.
    destruct (C a). apply HwmA. split; assumption.
  - destruct Hm as [I J]. apply HwmA in I as [I1 I2].
    destruct I2. apply H; try assumption.
    intros n Hn. assert (Q : In n A \/ ~ In n A). { apply REM. }
    destruct Q as [Q | Q]; try assumption.
    destruct (J n) as [L | L].
    + apply HwmA. split; try assumption.
      apply (Enderton4G omga Homga m n I1 Hn).
    + destruct (Enderton4Lb m); try apply Homga, I1. apply Homga in I1.
      apply (Enderton4F m I1 n); assumption.
    + destruct (Enderton4Lb m); try apply Homga, I1.
      rewrite <- L in Hn. assumption.
Qed.

(** Exercise 4-18 : Simplify: <_{-1}[{7,8}]. (The image of {7, 8} under the
    inverse less-than relation. *)

Theorem Exercise4_19 : forall m d, NaturalNumber m -> NaturalNumber d ->
  ~ Empty d -> exists q r dq dqr, NaturalNumber q /\ NaturalNumber r /\
  Prod_w d q dq /\ Sum_w dq r dqr /\ m = dqr /\ Lt_w r d.
Proof.
  intros m d Hm. generalize dependent d. omga. le_w. lt_w.
  destruct Enderton4I as [A1 A2]. destruct Enderton4J as [M1 M2].
  build_set set (fun (t c m : set) => forall d, NaturalNumber d ->
    ~ Empty d -> exists q r dq dqr, NaturalNumber q /\ NaturalNumber r /\
    Prod_w d q dq /\ Sum_w dq r dqr /\ m = dqr /\ Lt_w r d) omga omga.
  rename x into T. rename H into HT. apply HT.
  replace T with omga; try apply Homga, Hm. symmetry. clear m Hm.
  apply Induction_Principle_for_Omega; try assumption; try split;
  try (intros t Ht; apply HT, Ht).
  empty. rename x into o. rename H into Ho. exists o. split; try assumption.
  - apply HT. split; try apply Homga, Zero_NaturalNumber, Ho.
    intros d Hd Hne. exists o, o, o, o. split; try split;
    try apply (Zero_NaturalNumber o Ho). repeat split.
    + apply M1; assumption.
    + apply A1; try assumption; try apply (Zero_NaturalNumber o Ho).
    + ordpair o d. rename x into od. rename H into Hod.
      exists lt, od. repeat (split; try assumption). apply Hlt.
      exists o, d. repeat (split; try assumption);
      try (apply Zero_NaturalNumber; assumption).
      apply (Enderton4M o d); try assumption;
      try apply Zero_NaturalNumber; try assumption. split.
      * intros x Hx. destruct (Ho x). assumption.
      * intros C. apply Hne. replace d with o. assumption.
  - intros n n' Hn' Hn. apply HT in Hn. destruct Hn as [Hn IH].
    apply HT. apply Homga in Hn.
    split; try (apply Homga, (Succ_NaturalNumber n n' Hn Hn')). intros d Hd Hne.
    destruct (IH d Hd Hne) as [q [r [dq [dqr [Hq [Hr [Hdq [Hdqr [Heq Hlt']]]]]]]]].
    destruct Hlt' as [lt' [rd [Hlt' [Hrd Hrd']]]].
    succ dqr. rename x into Sdqr. rename H into HSdqr.
    succ r. rename x into r'. rename H into Hr'.
    sum_w dq r' (Prod_NaturalNumber d q dq Hd Hq Hdq)
      (Succ_NaturalNumber r r' Hr Hr').
    rename x into dqr'. rename H into Hdqr'.
    succ d. rename x into d'. rename H into Hd'.
    ordpair r' d. rename x into r'd. rename H into Hr'd.
    assert (P : In r'd le).
    { ordpair r' d'. rename x into r'd'. rename H into Hr'd'.
      apply (lt_w_succ_iff_le_w lt le r' d d' r'd' r'd); try assumption;
      try apply (Succ_NaturalNumber r r' Hr Hr').
      apply (Enderton4La lt r d r' d' rd r'd'); try assumption.
      replace lt with lt'; try assumption; apply LessThan_w_Unique; assumption. }
    apply Hle in P. destruct P as [r'0 [d0 [Hr'd0 [Hr'0 [Hd0 P]]]]].
    assert (Q : r' = r'0 /\ d = d0).
    { apply (Enderton3A r' d r'0 d0 r'd r'd Hr'd Hr'd0). trivial. }
    replace r'0 with r' in *; replace d0 with d in *; try apply Q.
    clear r'0 d0 Hr'd0 Q. destruct P as [P | P].
    + exists q, r', dq, dqr'. repeat (split; try assumption).
      * apply (Succ_Unique n); try assumption. replace n with dqr.
        replace dqr' with Sdqr; try assumption.
        symmetry. apply (A2 dq r r' dqr); try assumption.
        apply (Prod_NaturalNumber d q); try assumption.
      * exists lt, r'd. repeat (split; try assumption).
        apply Hlt. exists r', d. repeat (split; try assumption).
    + succ q. rename x into q'. rename H into Hq'.
      zero. rename x into o. rename H into Ho.
      prod_w d q' Hd (Succ_NaturalNumber q q' Hq Hq').
      rename x into dq'. rename H into Hdq'.
      exists q', o, dq', dq'. repeat (split ; try assumption).
      * apply (Succ_NaturalNumber q); assumption.
      * apply Zero_NaturalNumber. assumption.
      * apply A1; try assumption.
        apply (Prod_NaturalNumber d q'); try assumption.
        apply (Succ_NaturalNumber q); try assumption.
      * sum_w d dq Hd (Prod_NaturalNumber d q dq Hd Hq Hdq).
        rename x into ddq. rename H into Hddq.
        sum_w dq d (Prod_NaturalNumber d q dq Hd Hq Hdq) Hd.
        rename x into dqd. rename H into Hdqd.
        replace dq' with ddq. replace ddq with dqd. replace n' with Sdqr.
        replace dqd with dqr'.
        { symmetry. apply (A2 dq r r' dqr); try assumption.
          apply (Prod_NaturalNumber d q); assumption. }
        { apply (Sum_w_Unique dq r'); try assumption;
          try (apply (Prod_NaturalNumber d q); assumption).
          replace r' with d. assumption. }
        { apply (Succ_Unique dqr); try assumption. replace dqr with n. assumption. }
        { apply (Enderton4K2 dq d); try assumption;
          try (apply (Prod_NaturalNumber d q); assumption). }
        { symmetry. apply (M2 d q dq q'); try assumption. }
      * ordpair o d. rename x into od. rename H into Hod.
        exists lt, od. repeat (split; try assumption). apply Hlt.
        exists o, d. repeat (split; try assumption);
        try (apply Zero_NaturalNumber; assumption).
        apply (Enderton4M o d); try assumption;
        try apply Zero_NaturalNumber; try assumption. split.
        { intros x Hx. destruct (Ho x). assumption. }
        { intros C. apply Hne. replace d with o. assumption. }
Qed.

Theorem Exercise4_20 : forall A UA omga, ~ Empty A -> Union A UA -> Nats omga ->
  Subset A omga -> UA = A -> A = omga.
Proof.
  intros A UA omga Hne HUA Homga Hsub Heq. lt_w. le_w.
  destruct (Well_Ordering_of_w A omga Homga Hsub Hne) as [m [H Hm]].
  apply Induction_Principle_for_Omega; try assumption; try split.
  - empty. exists x. split; try assumption. rename x into o. rename H0 into Ho.
    ordpair o m. rename x into om. rename H0 into Hom.
    ordpair m o. rename x into mo. rename H0 into Hmo.
    apply Hsub in H as Hm'.
    destruct (Trichotomous_w omga lt Homga Hlt o m om mo) as [P | [P | P]];
    try assumption; try apply Homga, Zero_NaturalNumber, Ho;
    destruct P as [P [Q R]].
    + apply Hlt in P. destruct P as [o' [m' [Hom' [Ho' [_ P]]]]].
      rewrite <- Heq. apply HUA. exists m. split; try assumption.
      assert (T : o = o' /\ m = m').
      { apply (Enderton3A o m o' m' om om Hom Hom'). trivial. }
      replace o' with o in *; replace m' with m in *; try apply T; assumption.
    + rewrite Q. assumption.
    + destruct (Ho m). apply Hlt in R. destruct R as [m' [o' [Hmo' [_ [Ho' R]]]]].
      assert (T : m = m' /\ o = o').
      { apply (Enderton3A m o m' o' mo mo Hmo Hmo'). trivial. }
      replace o' with o in *; replace m' with m in *; try apply T; assumption.
  - intros n n' Hn' Hn. rename Hn into IH. apply Hsub in IH as Hn.
    rewrite <- Heq in IH. apply HUA in IH. destruct IH as [p [Hp IH]].
    succ p. rename x into p'. rename H0 into Hp'.
    ordpair n p. rename x into np. rename H0 into Hnp.
    ordpair n' p'. rename x into n'p'. rename H0 into Hn'p'.
    ordpair n' p. rename x into n'p. rename H0 into Hn'p.
    apply Homga in Hn. apply Hsub in IH as Hp0. apply Homga in Hp0.
    assert (P : In n'p' lt).
    { apply (Enderton4La lt n p n' p' np n'p' Hlt Hn Hp0 Hn' Hp' Hnp Hn'p').
      apply Hlt. exists n, p. repeat (split; try assumption). }
    assert (R : In n'p le).
    { apply (lt_w_succ_iff_le_w lt le n' p p' n'p' n'p) ; try assumption.
      apply (Succ_NaturalNumber n n' Hn Hn'). }
    apply Hle in R. destruct R as [n'0 [p0 [Hn'p0 [_ [Hp'0 R]]]]].
    assert (T : n' = n'0 /\ p = p0).
    { apply (Enderton3A n' p n'0 p0 n'p n'p Hn'p Hn'p0). trivial. }
    replace n'0 with n' in *; replace p0 with p in *; try apply T.
    destruct R as [R | R].
    + rewrite <- Heq. apply HUA. exists p. split; assumption.
    + replace n' with p; assumption.
Qed.    

Theorem Exercise4_21 : forall n x, NaturalNumber n -> In x n -> ~ Subset n x.
Proof.
  intros n m Hn Hm C. omga. assert (Hm' : NaturalNumber m).
  { apply (Nats_sets_of_smaller_nats n m Hn) in Hm.
    destruct Hm as [_ Hm]. destruct Hm as [lt [mn [Hlt [Hmn P]]]].
    destruct (lt_relation_on_omega lt omga Hlt Homga mn P) as
      [m' [n' [Hmn' [Hm' Hn']]]].
    replace m with m'; try apply Homga, Hm'.
    apply (Enderton3A m' n' m n mn mn Hmn' Hmn). trivial. }
  apply (Enderton4M m n Hm' Hn); try assumption.
  apply SubsetSymmetric_iff_Equal. split; try assumption.
  intros x Hx. apply (Enderton4F n Hn m x); assumption.
Qed.

Theorem Exercise4_22 : forall m p p' mp', NaturalNumber m -> NaturalNumber p ->
  Succ p p' -> Sum_w m p' mp' -> In m mp'.
Proof.
  intros m p p' mp' Hm Hp Hp' Hmp'. zero. rename x into o. rename H into Ho.
  destruct (Zero_Leq_N o p' Ho (Succ_NaturalNumber p p' Hp Hp')) as [P | P].
  - apply (Enderton4N o p' m m mp') in P; try assumption;
    try apply (Zero_NaturalNumber o Ho);
    try apply (Succ_NaturalNumber p); try assumption.
    + apply A1_Commutative; assumption.
    + sum_w p' m (Succ_NaturalNumber p p' Hp Hp') Hm.
      rename x into p'm. rename H0 into Hp'm.
      replace mp' with p'm; try assumption.
      apply (Enderton4K2 p' m); try assumption.
      apply (Succ_NaturalNumber p p'); assumption.
  - destruct (Ho p). rewrite P. destruct Hp' as [Sp [HSp Hp']].
    apply Hp'. right. apply HSp. trivial.
Qed.

Theorem Exercise4_23 : forall m n, NaturalNumber m -> NaturalNumber n ->
  Lt_w m n -> exists p p' mp', NaturalNumber p /\ Succ p p' /\ Sum_w m p' mp' /\
  mp' = n.
Admitted.

Theorem Exercise4_24 : forall m n p q mn pq, NaturalNumber m ->
  NaturalNumber n -> NaturalNumber p -> NaturalNumber q -> Sum_w m n mn ->
  Sum_w p q pq -> In m p <-> In q n.
Admitted.

Theorem Exercise4_25 : forall m n p q mq np mp nq mqnp mpnq,
  NaturalNumber m -> NaturalNumber n -> NaturalNumber p -> NaturalNumber q ->
  Prod_w m q mq -> Prod_w n p np -> Prod_w m p mp -> Prod_w n q nq -> Sum_w mq np mqnp ->
  Sum_w mp nq mpnq -> In mqnp mpnq.
Admitted.

Theorem Exercise4_26 : forall n n' omga f ranf, NaturalNumber n -> Succ n n' ->
  Nats omga -> FuncFromInto f n' omga -> Range f ranf -> exists x, In x ranf /\
  forall x', In x' ranf -> In x' x.
Admitted.

Theorem Exercise4_27 : forall A G f1 f2 omga, Func G -> Nats omga ->
  FuncFromInto f1 omga A -> FuncFromInto f2 omga A ->
  (forall n f1ln f2ln domG f1n f2n Gf1ln Gf2ln, NaturalNumber n ->
  Restriction f1 n f1ln -> Restriction f2 n f2ln -> Domain G domG ->
  FunVal f1 n f1n -> FunVal f2 n f2n -> FunVal G f1ln Gf1ln ->
  FunVal G f2ln Gf2ln -> In f1ln domG /\ In f2ln domG /\ f1n = Gf1ln /\
  f2n = Gf2ln) -> f1 = f2.
Admitted.

(** Exercise 4-28 : Rewrite the proof of Theorem 4G using, place of induction,
    the well-ordering of omega. TODO *)

(** Exercise 4-29 : Write an expression for the set named 4 using only the
    empty set symbole, left and right curly braces, and commas. *)

(** Exercise 4-30 : What is U4? What is N4? *)

(** Exercise 4-31 : What is UU7? *)

(** Exercise 4-32 :
    
    a) Let A = {1}. Calculate A+ and U(A+).
    b) What is U({2}+)?  *)

(** Exercise 4-33 : Which of the following sets are transitive? (For each set S
    that is not transitive, specify a member of US not belonging to S.)
    
    a) {0, 1, {1}}
    b) {1}
    c) <0, 1> *)

(** Exercise 4-34 : Find a suitable a, b, etc. making each of the following sets
    transitive. 
    
    a) { {{0}}, a, b }
    b) { {{{0}}}, c, d, e} *)

(** Exercise 4-35 : Let S be the set <1, 0>. 

    a) Find a transitive set T1 for which S is a subset of T1.
    b) Find a transitive set T2 for which S is a member of T2. *)

(** Exercise 4-36 : By the Recursion Theorem, there is a function
    h : omega -> omega for which h(0) = 3 and h(n+) = 2 * h(n). What is h(4)? *)


Definition Has_n_Elts (S n : set) : Prop := NaturalNumber n /\
  exists f, FuncFromOnto f n S /\ OneToOne f.

Definition Disjoint (A B : set) : Prop :=
  exists AnB, BinaryIntersect A B AnB /\ Empty AnB.

Theorem Exercise4_36a : forall A B m n AuB mn, NaturalNumber m ->
  NaturalNumber n -> Has_n_Elts A m -> Has_n_Elts B n -> BinaryUnion A B AuB ->
  Sum_w m n mn -> Disjoint A B -> Has_n_Elts AuB mn.
Admitted.

Theorem Exercise4_37b : forall A B m n AxB mn, NaturalNumber m ->
  NaturalNumber n -> Has_n_Elts A m -> Has_n_Elts B n -> Prod A B AxB ->
  Prod_w m n mn -> Has_n_Elts AxB mn.
Admitted.

(** Exercise 4-38 : Assume that h is the function from omega into omega for which
    h(0) = 1 and h(n+) = h(n) + 3 (and note that h exists by the Recursion
    Theorem). Give an explicit (non-recursive) expression for h(n). *)

(** Exercise 4-39 : Assume that h is the function from omega into omega for which
    h(0) = 1 and h(n+) = h(n) + (2 * n) + 1 (and note that h exists by the
    Recursion Theorem). Give an explicit (non-recursive) expression for h(n). *)

(** Exercise 4-40 : Assume that h is the function from omega into omega defined
    by h(n) = 5 * n + 2 (and note that h exists by the Recursion Theorem).
    Express h(n+) in terms of h(n) as simply as possible.  *)