From Enderton Require Export NaturalNumbers.

(** In this chapter, Enderton embeds the real numbers into the axiomatic set
    theory. He begins by constructing the integers as equivalence classes of
    ordered pairs of natural numbers. *)

Definition NatPair_Equivalence (r : set) : Prop :=
  forall x, In x r <-> exists m n mn p q pq mq pn,
      NaturalNumber m /\ NaturalNumber n /\ OrdPair m n mn /\
      NaturalNumber p /\ NaturalNumber q /\ OrdPair p q pq /\
      Sum_w m q mq /\ Sum_w p n pn /\ mq = pn /\ OrdPair mn pq x.

Theorem NatPair_Equivalence_Exists : exists x, NatPair_Equivalence x.
Proof.
  omga. prod omga omga. rename x into wxw. rename H into Hwxw.
  prod wxw wxw. rename x into wxwxwxw. rename H into Hwxwxwxw.
  build_set unit
    (fun (_ : unit) (wxwxwxw ab : set) => exists m n mn p q pq mq pn, 
      NaturalNumber m /\ NaturalNumber n /\ OrdPair m n mn /\
      NaturalNumber p /\ NaturalNumber q /\ OrdPair p q pq /\
      Sum_w m q mq /\ Sum_w p n pn /\ mq = pn /\ OrdPair mn pq ab)
    tt wxwxwxw.
  rename x into eq. rename H into Heq. exists eq. intros x. split; intros H.
  - apply Heq. assumption.
  - apply Heq. split; try assumption.
    apply Hwxwxwxw. destruct H as [m [n [mn [p [ q [pq [mq [pn H]]]]]]]].
    destruct H as [Hm [Hn [Hmn [Hp [Hq [Hpq [_ [_ [_ H]]]]]]]]].
    exists mn. exists pq. split; try (split; try assumption).
    + apply Hwxw. exists m. exists n. split; try apply Homga; try assumption.
      split; try apply Homga; try assumption.
    + apply Hwxw. exists p. exists q. split; try split; try apply Homga; try assumption.
Qed.

Theorem NatPair_Equivalence_Unique : forall x y, NatPair_Equivalence x ->
                                            NatPair_Equivalence y -> x = y.
Proof.
  intros A B HA HB. apply Extensionality_Axiom. intros x. split; intros H.
  - apply HB. apply HA. assumption.
  - apply HA; apply HB; assumption.
Qed.

Ltac natpair_eq := destruct NatPair_Equivalence_Exists.

Lemma NatPair_Equivalence_On_NatPairs : forall eq w wxw,
    NatPair_Equivalence eq -> Nats w -> Prod w w wxw -> RelationOn eq wxw.
Proof.
  intros eq w wxw Heq Hw Hwxw ab H. apply Heq in H.
  destruct H as [m [n [mn [p [q [pq [_ [_ [Hm [Hn [Hmn [Hp [Hq [Hpq [_ [_ [_ H]]]]]]]]]]]]]]]]].
  exists mn, pq. split; try assumption. split.
    + apply Hwxw. exists m, n. repeat (split; try assumption; try apply Hw; try assumption).
    + apply Hwxw. exists p, q. repeat (split; try assumption; try apply Hw; try assumption).
Qed.  

Theorem Enderton5ZA : forall x w wxw, NatPair_Equivalence x -> Nats w ->
                                 Prod w w wxw -> EquivalenceRelation x wxw.
Proof.
  intros eq w wxw Heq Hw Hwxw. repeat (try split).
  - apply (NatPair_Equivalence_On_NatPairs eq w wxw); try assumption.
  - intros a aa Haa H. apply Heq. apply Hwxw in H. destruct H as [x [y [Hx [Hy Ha]]]].
    apply Hw in Hx, Hy. exists x, y, a, x, y, a.
    sum_w x y Hx Hy. rename x0 into xy. rename H into Hxy. exists xy, xy.
    repeat (split; try assumption).
  - intros x y xy yx Hxy Hyx H. apply Heq in H. apply Heq.
    destruct H as [m [n [mn [p [q [pq [mq [pn H]]]]]]]].
    destruct H as [Hm [Hn [Hmn [Hp [Hq [Hpq [Hmq [Hpn [H Hxy']]]]]]]]].
    exists p, q, pq, m, n, mn, pn, mq.
    assert (P : mn = x /\ pq = y). {
      apply (Enderton3A mn pq x y xy xy Hxy' Hxy). reflexivity. }
    destruct P as [P1 P2]. replace y with pq in Hyx. replace x with mn in Hyx.
    repeat (split; try assumption). symmetry. assumption.
  - intros x y z xy yz xz Hxy Hyz Hxz H1 H2.
    apply Heq. apply Heq in H1, H2.
    destruct H1 as [m [n [mn [p [q [pq [mq [pn H1]]]]]]]].
    destruct H1 as [Hm [Hn [Hmn [Hp [Hq [Hpq [Hmq [Hpn [H1 Hxy']]]]]]]]].
    destruct H2 as [p' [q' [pq' [r [s [rs [ps [rq H2]]]]]]]].
    destruct H2 as [Hp' [Hq' [Hpq' [Hr [Hs [Hrs [Hps [Hrq [H2 Hyz']]]]]]]]].
    replace p' with p in *. replace q' with q in *. replace pq' with pq in *.
    sum_w m s Hm Hs. rename x0 into ms. rename H into Hms.
    sum_w r n Hr Hn. rename x0 into rn. rename H into Hrn.
    exists m, n, mn, r, s, rs, ms, rn.
    replace x with mn in Hxz. replace z with rs in Hxz. repeat (split; try assumption).
    sum_w ms p (Sum_NaturalNumber m s ms Hm Hs Hms) Hp.
    rename x0 into msp. rename H into Hmsp.
    sum_w rn p (Sum_NaturalNumber r n rn Hr Hn Hrn) Hp.
    rename x0 into rnp. rename H into Hrnp.
    apply (Enderton4P ms rn p msp rnp).
    { apply (Sum_NaturalNumber m s ms Hm Hs Hms). }
    { apply (Sum_NaturalNumber r n rn Hr Hn Hrn). }
    apply Hp. apply Hmsp.  apply Hrnp.
    sum_w n p Hn Hp. rename x0 into np. rename H into Hnp.
    sum_w r np Hr (Sum_NaturalNumber n p np Hn Hp Hnp). rename x0 into rnp'. rename H into Hrnp'.
    transitivity rnp'. sum_w s p Hs Hp. rename x0 into sp. rename H into Hsp.
    sum_w m sp Hm (Sum_NaturalNumber s p sp Hs Hp Hsp). rename x0 into msp'. rename H into Hmsp'.
    transitivity msp'. symmetry. Print Enderton4K1.
    apply (Enderton4K1 m s p sp ms msp' msp Hm Hs Hp Hsp Hms Hmsp' Hmsp).
    sum_w r pn Hr (Sum_NaturalNumber p n pn Hp Hn Hpn). rename x0 into rpn. rename H into Hrpn.
    transitivity rpn.
    sum_w m ps Hm (Sum_NaturalNumber p s ps Hp Hs Hps). rename x0 into mps. rename H into Hmps.
    transitivity mps.
    apply (Sum_w_Unique m ps msp' mps Hm (Sum_NaturalNumber p s ps Hp Hs Hps)); try assumption.
    replace ps with sp. assumption. apply (Enderton4K2 s p sp ps Hs Hp Hsp Hps).
    sum_w r mq Hr (Sum_NaturalNumber m q mq Hm Hq Hmq). rename x0 into rmq. rename H into Hrmq.
    transitivity rmq. sum_w q m Hq Hm. rename x0 into qm. rename H into Hqm.
    sum_w r qm Hr (Sum_NaturalNumber q m qm Hq Hm Hqm). rename x0 into rqm. rename H into Hrqm.
    transitivity rqm.
    sum_w rq m (Sum_NaturalNumber r q rq Hr Hq Hrq) Hm. rename x0 into rqm'. rename H into Hrqm'.
    transitivity rqm'.
    sum_w m rq Hm (Sum_NaturalNumber r q rq Hr Hq Hrq). rename x0 into mrq. rename H into Hmrq.
    transitivity mrq. apply (Sum_w_Unique m ps mps mrq); try assumption.
    apply (Sum_NaturalNumber p s ps Hp Hs Hps). replace ps with rq; try assumption.
    apply (Enderton4K2 m rq mrq rqm'); try assumption.
    apply (Sum_NaturalNumber r q rq); try assumption.
    symmetry. apply (Enderton4K1 r q m qm rq); try assumption.
    apply (Sum_w_Unique r qm rqm rmq); try assumption.
    apply (Sum_NaturalNumber q m qm); try assumption.
    replace qm with mq; try assumption.
    apply (Enderton4K2 m q mq qm); try assumption.
    apply (Sum_w_Unique r mq rmq rpn); try assumption.
    apply (Sum_NaturalNumber m q mq); try assumption.
    replace mq with pn; try assumption.
    apply (Sum_w_Unique r pn rpn rnp'); try assumption.
    apply (Sum_NaturalNumber p n pn); try assumption.
    replace pn with np; try assumption.
    apply (Enderton4K2 n p np pn); try assumption.
    apply (Enderton4K1 r n p np rn); try assumption.
    assert (P : pq = y /\ rs = z). {
      apply (Enderton3A pq rs y z yz yz); try assumption. trivial. }
    apply P.
    assert (P : mn = x /\ pq = y). {
      apply (Enderton3A mn pq x y xy xy); try assumption. trivial. }
    apply P.
    transitivity y.
    assert (P : mn = x /\ pq = y). {
      apply (Enderton3A mn pq x y xy xy); try assumption. trivial. }
    apply P.
    assert (P : pq' = y /\ rs = z). {
      apply (Enderton3A pq' rs y z yz yz); try assumption. trivial. }
    symmetry. apply P.
    assert (P : pq' = y /\ rs = z). {
      apply (Enderton3A pq' rs y z yz yz); try assumption. trivial. }
    assert (Q : mn = x /\ pq = y). {
      apply (Enderton3A mn pq x y xy xy); try assumption. trivial. }
    assert (R : pq = pq'). {
      transitivity y; try apply Q; try (symmetry; apply P). }
    assert (S : p = p /\ q = q'). {
      apply (Enderton3A p q p q' pq pq'); try assumption. }
    apply S.
    assert (P : pq' = y /\ rs = z). {
      apply (Enderton3A pq' rs y z yz yz); try assumption. trivial. }
    assert (Q : mn = x /\ pq = y). {
      apply (Enderton3A mn pq x y xy xy); try assumption. trivial. }
    assert (R : pq = pq'). {
      transitivity y; try apply Q; try (symmetry; apply P). }
    assert (S : p = p' /\ q = q'). {
      apply (Enderton3A p q p' q' pq pq'); try assumption. }
    apply S.
Qed.

Definition Ints (Z : set) : Prop :=
  forall w wxw natpair_eq, Nats w -> Prod w w wxw -> NatPair_Equivalence natpair_eq ->
                      Quotient wxw natpair_eq Z.

Theorem Ints_Exists : exists Z, Ints Z.
Proof.
  natpair_eq. rename x into eq. rename H into Heq.
  omga. prod omga omga. rename x into wxw. rename H into Hwxw.
  assert (P : RelationOn eq wxw). {
    destruct (Enderton5ZA eq omga wxw Heq Homga Hwxw). assumption. }
  quotient P wxw eq. exists x. intros w wxw' eq' Hw Hwxw' Heq'.
  replace wxw' with wxw; replace eq' with eq; try assumption;
    try (apply NatPair_Equivalence_Unique; assumption).
  - apply (Prod_Unique omga omga); try assumption.
    replace omga with w; try assumption.
    apply (Nats_Unique); assumption.
Qed.  

Theorem Ints_Unique : forall Z Z', Ints Z -> Ints Z' -> Z = Z'.
Proof.
  intros Z Z' HZ HZ'. omga.
  prod omga omga. rename x into wxw. rename H into Hwxw.
  natpair_eq. rename x into eq. rename H into Heq.
  apply (Quotient_Unique wxw eq);
    try apply (NatPair_Equivalence_On_NatPairs eq omga wxw); try assumption.
  - apply (HZ omga wxw eq); try assumption.
  - apply (HZ' omga wxw eq); try assumption.
Qed.

Ltac Z := destruct (Ints_Exists) as [Z HZ].

Definition Int (a : set) : Prop :=
  forall Z, Ints Z -> In a Z.

Definition Addition_Z (add : set) : Prop :=
  forall abc, In abc add <-> exists ab c a b m n p q mn pq mp nq mpnq eq,
      OrdPair ab c abc /\ OrdPair a b ab /\ Int a /\ Int b /\
      NaturalNumber m /\ NaturalNumber n /\ NaturalNumber p /\ NaturalNumber q /\
      OrdPair m n mn /\ OrdPair p q pq /\ Sum_w m p mp /\ Sum_w n q nq /\
      OrdPair mp nq mpnq /\ NatPair_Equivalence eq /\ EquivalenceClass mn eq a /\
      EquivalenceClass pq eq b /\ EquivalenceClass mpnq eq c.

Theorem Addition_Z_Exists : exists add_Z, Addition_Z add_Z.
Proof.
  Z. prod Z Z. rename x into ZxZ. rename H into HZxZ.
  prod ZxZ Z. rename x into ZxZxZ. rename H into HZxZxZ.
  build_set unit
    (fun (_ : unit) (ZxZxZ abc : set) => exists ab c a b m n p q mn pq mp nq mpnq eq,
      OrdPair ab c abc /\ OrdPair a b ab /\ Int a /\ Int b /\
      NaturalNumber m /\ NaturalNumber n /\ NaturalNumber p /\ NaturalNumber q /\
      OrdPair m n mn /\ OrdPair p q pq /\ Sum_w m p mp /\ Sum_w n q nq /\
      OrdPair mp nq mpnq /\ NatPair_Equivalence eq /\ EquivalenceClass mn eq a /\
      EquivalenceClass pq eq b /\ EquivalenceClass mpnq eq c)
    tt ZxZxZ.
  rename x into add. rename H into Hadd. exists add. intros abc. split; intros H.
  - apply Hadd. assumption.
  - apply Hadd. split; try assumption.
    destruct H as [ab [c [a [b [m [n [p [q [mn [pq [mp [nq [mpnq [eq H]]]]]]]]]]]]]].
    destruct H as [Habc [Hab [Ha [Hb [Hm [Hn [Hp [Hq [Hmn [Hpq [Hmp [Hnq [Hmpnq [Heq [HCa [HCb HCc]]]]]]]]]]]]]]]].
    apply HZxZxZ. exists ab, c. split; try (split; try assumption).
    apply HZxZ. exists a, b. repeat (split; try assumption).
    + apply Ha; try assumption.
    + apply Hb; try assumption.
    + omga. prod omga omga. rename x into wxw. rename H into Hwxw.
      apply (HZ omga wxw eq Homga Hwxw Heq
                (NatPair_Equivalence_On_NatPairs eq omga wxw Heq Homga Hwxw)).
      exists mpnq. split; try assumption. apply Hwxw.
      exists mp, nq. split; try split; try assumption. Check Sum_NaturalNumber.
      * apply Homga. apply (Sum_NaturalNumber m p mp Hm Hp Hmp).
      * apply Homga. apply (Sum_NaturalNumber n q nq Hn Hq Hnq).
Qed.

Theorem Addition_Z_Unique : forall add_Z add_Z', Addition_Z add_Z -> Addition_Z add_Z' ->
                                            add_Z = add_Z'.
Proof.
  intros Z Z' HZ HZ'. apply Extensionality_Axiom. intros abc. split; intros H.
  - apply HZ'. apply HZ in H. apply H.
  - apply HZ. apply HZ' in H. apply H.
Qed.  

Theorem Addition_Z_BinaryOperation : forall Z add_Z, Ints Z -> Addition_Z add_Z ->
                                                BinaryOperator add_Z Z.
Proof.
  intros Z add_Z HZ Hadd_Z. prod Z Z. rename x into ZxZ. rename H into HZxZ.
  exists ZxZ. split; try assumption. split; try split.
  - intros abc Habc. apply Hadd_Z in Habc.
    destruct Habc as [ab [c [a [b [m [n [p [q [mn [pq [mp [nq [mpnq [eq Habc]]]]]]]]]]]]]].
    destruct Habc as [Habc _]. exists ab, c. assumption.
  - intros ab c d abc abd Habc Habd H1 H2.
    apply Hadd_Z in H1, H2.
Admitted.

Ltac add_Z := destruct Addition_Z_Exists as [addZ HaddZ].

Definition Sum_Z (a b c : set) : Prop :=
  exists add ab abc, Addition_Z add /\ OrdPair a b ab /\ OrdPair ab c abc /\
                In abc add.

Theorem Sum_Z_Exists : forall a b, Int a -> Int b -> exists c, Sum_Z a b c.
Proof.
Admitted.

Lemma Enderton5ZB : forall m n m' n' p q p' q' mp nq m'p' n'q' mn m'n' pq p'q' mpnq,
  forall m'p'n'q' A B C eq,
  NaturalNumber m -> NaturalNumber n -> NaturalNumber m' -> NaturalNumber n' ->
  NaturalNumber p -> NaturalNumber q -> NaturalNumber p' -> NaturalNumber q' ->
  Sum_w m p mp -> Sum_w n q nq -> Sum_w m' p' m'p' -> Sum_w n' q' n'q' ->
  OrdPair m n mn -> OrdPair m' n' m'n' -> OrdPair p q pq -> OrdPair p' q' p'q' ->
  OrdPair mp nq mpnq -> OrdPair m'p' n'q' m'p'n'q' ->
  OrdPair mn m'n' A -> OrdPair pq p'q' B -> OrdPair mpnq m'p'n'q' C ->
  NatPair_Equivalence eq ->
  In A eq -> In B eq -> In C eq.
Proof.
Admitted.

(* should follow from Enderton3Q and previous lemma *)
Theorem Sum_Z_Unique : forall a b c c', Int a -> Int b -> Sum_Z a b c ->
                                   Sum_Z a b c' -> c = c'.
Proof.
Admitted.

Ltac sum_w a b Ha Hb := destruct (Sum_Z_Exists a b Ha Hb).

Definition Add_Z_Associative : Prop := forall a b c ab bc r l,
  Int a -> Int b -> Int c -> Sum_Z a b ab -> Sum_Z b c bc ->
  Sum_Z a bc r -> Sum_Z ab c l -> r = l.

Definition Add_Z_Commutative : Prop := forall a b ab ba,
  Int a -> Int b -> Sum_Z a b ab -> Sum_Z b a ba -> ab = ba.

Theorem Enderrton5ZC1 : Add_Z_Associative.
Proof.
Admitted.

Theorem Enderton5ZC2 : Add_Z_Commutative.
Proof.
Admitted.

Definition Zero_Z (z : set) : Prop :=
  forall o oo eq, Empty o -> OrdPair o o oo -> NatPair_Equivalence eq -> EquivalenceClass oo eq z.

Theorem Zero_Z_Exists : exists z, Zero_Z z.
Proof.
Admitted.

Theorem Zero_Z_Unique : forall z z', Zero_Z z -> Zero_Z z' -> z = z'.
Proof.
Admitted.

Ltac zero_z := destruct Zero_Z_Exists.

Theorem Enderton5ZDa : forall a o, Int a -> Zero_Z o -> Sum_Z a o a.
Proof.
Admitted.

Theorem Enderton5ZDb : forall a o, Int a -> Zero_Z o -> exists b, Sum_Z a b o.
Proof.
Admitted.

Theorem Add_Z_Inverse_Unique : forall a b b' o,
  Int a -> Int b -> Int b' -> Zero_Z o -> Sum_Z a b o -> Sum_Z a b' o -> b = b'.
Proof.
Admitted.

