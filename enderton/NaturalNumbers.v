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
  (forall n sn hsn hn Shn, FunVal sigma n sn -> FunVal h sn hsn -> FunVal h n hn ->
  FunVal S hn Shn -> hsn = Shn) /\
  forall ho, FunVal h empty ho -> ho = e.
Admitted.

(** Exercise 4 - 7 : Complete part of the proof of the recusion theorem. *)

Theorem Exercise4_8 : forall f A c ranf h, FuncFromInto f A A -> In c A ->
  ~ In c ranf -> Range f ranf -> RecursiveFunction A c f h -> OneToOne h.
Admitted.

Definition preClosure1 (f B A preC1 : set) : Prop :=
  FuncFromInto f B B -> Subset A B ->
  forall X, In X preC1 <-> Subset A X /\ Subset X B /\
  forall fX, Image X f fX -> Subset fX X.

Theorem preClosure1_Exists : forall f B A, exists preC1, preClosure1 f B A preC1.
Admitted.

Theorem preClosure1_Unique : forall f B A C C', preClosure1 f B A C ->
  preClosure1 f B A C' -> C = C'.
Admitted.

Definition preClosure2 (f B A preC2 : set) : Prop :=
  exists PB F h, GivenByImage f B B F /\ PowerSet B PB /\
  RecursiveFunction PB A F h /\ Range h preC2.

Theorem preClosure2_Exists : forall f B A, exists C, preClosure2 f B A C.
Admitted.

Theorem preClosure2_Unique : forall f B A C C', preClosure2 f B A C ->
  preClosure2 f B A C' -> C = C'.
Admitted.

Theorem Exercise4_9 : forall f B A C1 C2 NC1 UC2, FuncFromInto f B B ->
  Subset A B -> preClosure1 f B A C1 -> preClosure2 f B A C2 -> 
  Intersect C1 NC1 -> Union C2 UC2 -> NC1 = UC2.
Admitted.

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
    ( * : omega x omega -> omega), and exponentiation (^ : omega x omega -> omega).
    We also prove some familiar algebraic properties of these operations. *)

Definition Addn (n An : set) : Prop :=
  NaturalNumber n -> exists omga sigma, Nats omga /\ SuccessorFunc sigma /\
  RecursiveFunction omga n sigma An.

Theorem Addn_Exists : forall n, exists An, Addn n An.
Admitted.

Theorem Addn_Unique : forall n An Bn, Addn n An -> Addn n Bn -> An = Bn.
Admitted.

Definition BinaryOperator (op A : set) : Prop :=
  exists AxA, Prod A A AxA /\ FuncFromInto op AxA A.

Definition Addition (add : set) : Prop :=
  forall mnp, In mnp add <-> exists mn p m n omga Am, OrdPair mn p mnp /\
  OrdPair m n mn /\ Nats omga /\ In m omga /\ In n omga /\ Addn m Am /\
  FunVal Am n p.

Theorem Addition_Exists : exists add, Addition add.
Admitted.

Theorem Addition_Unique : forall add add', Addition add -> Addition add' ->
  add = add'.
Admitted.

Lemma Addition_BinaryOperation : forall add omga, Addition add -> Nats omga ->
  BinaryOperator add omga.
Admitted.

Ltac add_omega := destruct (Addition_Exists) as [add Hadd].

Definition Add (m n p : set) : Prop := NaturalNumber m -> NaturalNumber n ->
  NaturalNumber p -> exists add mn mnp, Addition add /\ OrdPair m n mn
  /\ OrdPair mn p mnp /\ In mnp add.

Definition A1 : Prop := forall m o, NaturalNumber m -> Empty o -> Add m o m.

Definition A2 : Prop := forall m n n' mn mn' mn'', NaturalNumber m ->
  NaturalNumber n -> Succ n n' -> Add m n mn -> Add m n' mn' -> Succ mn mn'' ->
  mn' = mn''.

Theorem Enderton4I : A1 /\ A2.
Admitted.

Definition Multn (n Mn : set) : Prop :=
  NaturalNumber n -> exists omga An o, Nats omga /\ Addn n An /\ Empty o /\
  RecursiveFunction omga o An Mn.

Theorem Multn_Exists : forall n, NaturalNumber n -> exists Mn, Multn n Mn.
Admitted.

Theorem Multn_Unique : forall n Mn Nn, NaturalNumber n ->
  Multn n Mn -> Multn n Nn -> Mn = Nn.
Admitted.

Definition Multiplication (mult : set) : Prop :=
  forall mnp, In mnp mult <-> exists mn p m n omga Mm, OrdPair mn p mnp /\
  OrdPair m n mn /\ Nats omga /\ In m omga /\ In n omga /\ Multn m Mm /\
  FunVal Mm n p.

Theorem Multiplication_Exists : exists mult, Multiplication mult.
Admitted.

Theorem Multiplication_Unique : forall mult mult',
  Multiplication mult -> Multiplication mult' -> mult = mult'.
Admitted.

Lemma Multiplication_BinaryOperation : forall mult omga,
  Multiplication mult -> Nats omga -> BinaryOperator mult omga.
Admitted.

Ltac mult_omega := destruct (Multiplication_Exists) as [mult Hmult].

Definition Mult (m n p : set) : Prop := NaturalNumber m -> NaturalNumber n ->
  NaturalNumber p -> exists mult mn mnp, Multiplication mult /\ OrdPair m n mn
  /\ OrdPair mn p mnp /\ In mnp mult.

Definition M1 : Prop := forall m o, NaturalNumber m -> Empty o -> Mult m o o.

Definition M2 : Prop := forall m n mn n' mn' mnm, NaturalNumber m ->
  NaturalNumber n -> Mult m n mn -> Succ n n' -> Mult m n' mn' -> Add mn m mnm ->
  mn' = mnm.

Theorem Enderton4J : M1 /\ M2.
Admitted.

Definition Expn (n En : set) : Prop :=
  NaturalNumber n -> exists omga Mn o o', Nats omga /\ Multn n Mn /\ Empty o /\
  Succ o o' /\ RecursiveFunction omga o' Mn En.

Theorem Expn_Exists : forall n, NaturalNumber n -> exists En, Expn n En.
Admitted.

Theorem Expn_Unique : forall n En Fn, NaturalNumber n ->
  Expn n En -> Expn n Fn -> En = Fn.
Admitted.

Definition Exponentiation (exp : set) : Prop :=
  forall mnp, In mnp exp <-> exists mn p m n omga En, OrdPair mn p mnp /\
  OrdPair m n mn /\ Nats omga /\ In m omga /\ In n omga /\ Expn n En /\
  FunVal En m p.

Theorem Exponentiation_Exists : exists exp, Exponentiation exp.
Admitted.

Theorem Exponentiation_Unique : forall exp exp',
  Multiplication exp -> Multiplication exp' -> exp = exp'.
Admitted.

Lemma Exponentiation_BinaryOperation : forall exp omga,
  Multiplication exp -> Nats omga -> BinaryOperator exp omga.
Admitted.

Ltac exp_omega := destruct (Exponentiation_Exists) as [exp Hexp].

Definition Exp (m n p : set) : Prop := NaturalNumber m -> NaturalNumber n ->
  NaturalNumber p -> exists exp mn mnp, Exponentiation exp /\ OrdPair m n mn
  /\ OrdPair mn p mnp /\ In mnp exp.

Definition E1 : Prop := forall m o o', NaturalNumber m -> Empty o ->
  Succ o o' -> Exp m o o'.

Definition E2 : Prop := forall m n mn n' mn' mnm, NaturalNumber m ->
  NaturalNumber n -> Exp m n mn -> Succ n n' -> Exp m n' mn' -> Mult mn m mnm ->
  mn' = mnm.

Theorem Enderton4J' : E1 /\ E2.
Admitted.

Definition Omega_Addition_Associative : Prop :=
  forall m n p np mn r l, NaturalNumber m -> NaturalNumber n -> NaturalNumber p ->
  Add n p np -> Add m n mn -> Add m np r -> Add mn p l -> r = l.

Definition Omega_Addition_Commutative : Prop :=
  forall m n mn nm, NaturalNumber m -> NaturalNumber n -> Add m n mn ->
  Add n m nm -> mn = nm.

Definition Omega_Distributive : Prop :=
  forall m n p np mnp mn mp mnmp, NaturalNumber m ->  NaturalNumber n ->
  NaturalNumber p -> Add n p np -> Mult m np mnp -> Mult m n mn -> Mult m p mp ->
  Add mn mp mnmp -> mnp = mnmp.

Definition Omega_Multiplication_Associative : Prop :=
  forall m n p np mn r l, NaturalNumber m -> NaturalNumber n -> NaturalNumber p ->
  Mult n p np -> Mult m n mn -> Mult m np r -> Mult mn p l -> r = l.

Definition Omega_Multiplication_Commutative : Prop :=
  forall m n mn nm, NaturalNumber m -> NaturalNumber n -> Mult m n mn ->
  Mult n m nm -> mn = nm.

Theorem Enderton4K1 : Omega_Addition_Associative.
Admitted.

Theorem Enderton4K2 : Omega_Addition_Commutative.
Admitted.

Theorem Enderton4K3 : Omega_Distributive.
Admitted.

Theorem Enderton4K4 : Omega_Multiplication_Associative.
Admitted.

Theorem Enderton4K5 : Omega_Multiplication_Commutative.
Admitted.

Theorem Exercise4_13 : forall m n o, NaturalNumber m -> NaturalNumber n ->
  Empty o -> Mult m n o -> m = o \/ n = o.
Admitted.

Definition Omega_Even (n : set) : Prop :=
  exists p o o' o'', NaturalNumber p /\ Empty o /\ Succ o o' /\ Succ o' o'' /\
  Mult o'' p n.

Definition Omega_Odd (n : set) : Prop :=
  exists p o o' o'' tp, NaturalNumber p /\ Empty o /\ Succ o o' /\ Succ o' o'' /\
  Mult o'' p tp /\ Add tp o' n.

Theorem Exercise4_14 : forall n, NaturalNumber n -> Omega_Odd n \/ Omega_Even n.
Admitted.

Theorem Exercise4_14' : forall n, NaturalNumber n -> ~ (Omega_Odd n /\ Omega_Even n).
Admitted.

(** Exercise 4-15 : Prove part 1 of 4K. *)

(** Exercise 4-16 : Prove part 5 of 4K. *)

Theorem Exercise4_17 : forall m n p np mnp mn mp mnmp,
  NaturalNumber m -> NaturalNumber n -> NaturalNumber p -> Add n p np ->
  Exp m np mnp -> Exp m n mn -> Exp m p mp -> Mult mn mp mnmp ->
  mnp = mnmp.
Admitted.

(** Now we have the basic algebraic operations on omega and corresponding
    results about their basic properties. We next turn our attention to
    order on omega, and show that the relation < is linear ordering as in
    the previous chapter. *)

Definition Omega_LT (lt : set) : Prop :=
  forall mn, In mn lt <-> exists m n, OrdPair m n mn /\ NaturalNumber m /\
  NaturalNumber n /\ In m n.

Theorem Omega_LT_Exists : exists lt, Omega_LT lt.
Admitted.

Theorem Omega_LT_Unique : forall lt lt', Omega_LT lt -> Omega_LT lt' -> lt = lt'.
Admitted.

Ltac lt_omega := destruct (Omega_LT_Exists) as [lt Hlt].

Definition In_ (x A : set) : Prop :=
  In x A \/ x = A.

Definition Omega_LE (le : set) : Prop :=
  forall mn, In mn le <-> exists m n, OrdPair m n mn /\ NaturalNumber m /\
  NaturalNumber n /\ In_ m n.

Theorem Omega_LE_Exists : exists le, Omega_LE le.
Admitted.

Theorem Omega_LE_Unique : forall le le', Omega_LE le -> Omega_LE le' -> le = le'.
Admitted.

Ltac le_omega := destruct (Omega_LE_Exists) as [le Hle].

Lemma lt_succ_iff_le : forall lt le p k k' pk' pk,
  Omega_LT lt -> Omega_LE le -> NaturalNumber p -> NaturalNumber k -> Succ k k' ->
  OrdPair p k' pk' -> OrdPair p k pk -> In pk' lt <-> In pk le.
Admitted.

Definition Lt (m n : set) : Prop :=
  exists lt mn, Omega_LT lt /\ OrdPair m n mn /\ In mn lt.

Definition Le (m n : set) : Prop :=
  exists le mn, Omega_LE le /\ OrdPair m n mn /\ In mn le.

Corollary Nats_sets_of_smaller_nats : forall n x, NaturalNumber n ->
  In x n <-> NaturalNumber n /\ Lt x n.
Admitted.

Lemma lt_relation_on_omega : forall lt omga, Omega_LT lt -> Nats omga ->
  RelationOn lt omga.
Admitted.

Lemma lt_transitive : forall lt, Omega_LT lt -> Transitive lt.
Admitted.

Lemma Enderton4La : forall lt m n m' n' mn m'n', Omega_LT lt ->
  NaturalNumber m -> NaturalNumber n -> Succ m m' -> Succ n n' ->
  OrdPair m n mn -> OrdPair m' n' m'n' -> In mn lt <-> In m'n' lt.
Admitted.

Lemma Enderton4Lb : forall m, NaturalNumber m -> ~ In m m.
Admitted.

Print Trichotomous.

Lemma Omega_Trichotomous : forall omga lt m n, Nats omga -> Omega_LT lt ->
  NaturalNumber m -> NaturalNumber n -> Trichotomous lt omga.
Admitted.

Corollary Nats_LinearOrdered : forall omga lt, Nats omga -> Omega_LT lt ->
  LinearOrdering lt omga.
Admitted.

Definition ProperSubset (A B : set) : Prop := Subset A B /\ A <> B.

Corollary Enderton4M : forall m n, NaturalNumber m -> NaturalNumber n -> 
  In m n <-> ProperSubset m n.
Admitted.

Corollary Enderton4M' : forall m n, NaturalNumber m -> NaturalNumber n ->
  In_ m n <-> Subset m n.
Admitted.

Theorem Enderton4N : forall m n p mp np, NaturalNumber m -> NaturalNumber n ->
  NaturalNumber p -> Add m p mp -> Add n p np -> In m n <-> In mp np.
Admitted.

Theorem Enderton4N' : forall m n p mp np, NaturalNumber m -> NaturalNumber n ->
  NaturalNumber p -> ~Empty p -> Mult m p mp -> Mult n p np ->
  In m n <-> In mp np.
Admitted.

Corollary Enderton4P : forall m n p mp np, NaturalNumber m -> NaturalNumber n ->
  NaturalNumber p -> Add m p mp -> Add n p np -> mp = np -> m = n.
Admitted.

Corollary Enderton4P' : forall m n p mp np, NaturalNumber m -> NaturalNumber n ->
  NaturalNumber p -> Mult m p mp -> Mult n p np -> mp = np -> ~Empty p -> m = n.
Admitted.

Theorem Well_Ordering_of_Omega : forall A omga, Nats omga -> Subset A omga ->
  ~ Empty A -> exists m, In m A /\ forall n, In n A -> In_ m n.
Admitted.

Corollary Enderton4Q : forall omga, Nats omga ->
  ~ exists f, FuncFromInto f omga omga /\ forall n n' fn fn', NaturalNumber n ->
  Succ n n' -> FunVal f n fn -> FunVal f n' fn' -> In fn' fn.
Admitted.

Theorem Strong_Induction_Principle_for_Omega : forall omga A, Nats omga ->
  Subset A omga ->
  (forall n, In n omga -> (forall x, In x n -> In x A) -> In n A) ->
  A = omga.
Admitted.

(** Exercise 4-18 : Simplify: <_{-1}[{7,8}]. (The image of {7, 8} under the
    inverse less-than relation. *)

Theorem Exercise4_19 : forall m d, NaturalNumber m -> NaturalNumber d ->
  ~ Empty d -> exists q r dq dqr, NaturalNumber q /\ NaturalNumber r /\
  Mult d q dq /\ Add dq r dqr /\ m = dqr /\ Lt r d.
Admitted.

Theorem Exercise4_20 : forall A UA omga, ~ Empty A -> Union A UA -> Nats omga ->
  Subset A omga -> UA = A -> A = omga.
Admitted.

Theorem Exercise4_21 : forall n x, NaturalNumber n -> In x n -> ~ Subset n x.
Admitted.

Theorem Exercise4_22 : forall m p p' mp', NaturalNumber m -> NaturalNumber p ->
  Succ p p' -> Add m p' mp' -> In m mp'.
Admitted.

Theorem Exercise4_23 : forall m n, NaturalNumber m -> NaturalNumber n ->
  Lt m n -> exists p p' mp', NaturalNumber p /\ Succ p p' /\ Add m p' mp' /\
  mp' = n.
Admitted.

Theorem Exercise4_24 : forall m n p q mn pq, NaturalNumber m ->
  NaturalNumber n -> NaturalNumber p -> NaturalNumber q -> Add m n mn ->
  Add p q pq -> In m p <-> In q n.
Admitted.

Theorem Exercise4_25 : forall m n p q mq np mp nq mqnp mpnq,
  NaturalNumber m -> NaturalNumber n -> NaturalNumber p -> NaturalNumber q ->
  Mult m q mq -> Mult n p np -> Mult m p mp -> Mult n q nq -> Add mq np mqnp ->
  Add mp nq mpnq -> In mqnp mpnq.
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
  Add m n mn -> Disjoint A B -> Has_n_Elts AuB mn.
Admitted.

Theorem Exercise4_37b : forall A B m n AxB mn, NaturalNumber m ->
  NaturalNumber n -> Has_n_Elts A m -> Has_n_Elts B n -> Prod A B AxB ->
  Mult m n mn -> Has_n_Elts AxB mn.
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