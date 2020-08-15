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

Definition Inductive (A : set ) : Prop :=
  (exists empty, Empty empty /\ In empty A) /\
  forall a aplus, Succ a aplus -> In a A -> In aplus A.

Axiom Infinity_Axiom : exists A, Inductive A.

Definition NaturalNumber (x : set) : Prop :=
  forall A, Inductive A -> In x A.

Definition Nats (omga : set) : Prop :=
  forall x, In x omga <-> NaturalNumber x.

Theorem Enderton4A : exists omga, forall x, In x omga <-> NaturalNumber x.
Admitted.

Theorem Nats_Unique : forall omga omga', Nats omga -> Nats omga' -> omga = omga.
Admitted.

Ltac omga := destruct Enderton4A as [omga Homga].

Ltac zero := empty.

Theorem Enderton4B : forall omga, Nats omga -> Inductive omga /\
  forall A, Inductive A -> Subset omga A.
Admitted.

Theorem Induction_Principle_for_Omega : forall A omga, Nats omga ->
  Inductive A -> Subset A omga -> A = omga.
Admitted.

Theorem Enderton4C : forall x, NaturalNumber x -> ~ Empty x ->
  exists w, NaturalNumber w /\ Succ w x.
Admitted.

Theorem Exercise4_1 : True (* TODO *).
Admitted.

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
Admitted.

Theorem SuccessorFunc_Unique : forall sigma sigma',
  SuccessorFunc sigma -> SuccessorFunc sigma' -> sigma = sigma'.
Admitted.

Definition PeanoSystem_of_NaturalNumbers (P : set) : Prop :=
  exists N S NS e, OrdPair N S NS /\ OrdPair NS e P /\
  Nats N /\ SuccessorFunc S /\ Empty e.

Theorem PeanoSystem_of_NaturalNumbers_Exists : exists P,
  PeanoSystem_of_NaturalNumbers P.
Admitted.

Theorem PeanoSystem_of_NaturalNumbers_Unique : forall P P',
  PeanoSystem_of_NaturalNumbers P -> PeanoSystem_of_NaturalNumbers P' -> P = P'.
Admitted.

Definition TransitiveSet (A : set) : Prop :=
  forall a x, In a A -> In x a -> In x A.

Theorem Enderton4E : forall a a' Ua', Succ a a' ->
  Union a' Ua' -> TransitiveSet a -> Ua' = a.
Admitted.

Theorem Enderton4F : forall n, NaturalNumber n -> TransitiveSet n.
Admitted.

Theorem Enderton4D : forall P, PeanoSystem_of_NaturalNumbers P ->
  PeanoSystem P.
Admitted.

Theorem Enderton4G : forall omga, Nats omga -> TransitiveSet omga.
Admitted.

Theorem Exercise4_2 : forall a a', Succ a a' ->
  TransitiveSet a -> TransitiveSet a'.
Admitted.

Theorem Exercise4_3a : forall a Pa, PowerSet a Pa ->
  TransitiveSet a -> TransitiveSet Pa.
Admitted.

Theorem Exercise4_3b : forall a Pa, PowerSet a Pa ->
  TransitiveSet Pa -> TransitiveSet a.
Admitted.

Theorem Exercise4_4 : forall a Ua, Union a Ua ->
  TransitiveSet a -> TransitiveSet Ua.
Admitted.

Theorem Exercise4_5a : forall A UA, Union A UA ->
  (forall a, In a A -> TransitiveSet a) -> TransitiveSet UA.
Admitted.

Theorem Exercise4_5b : forall A NA, ~Empty A -> Intersect A NA ->
  (forall a, In a A -> TransitiveSet a) -> TransitiveSet NA.
Admitted.

Theorem Exercise4_6 : forall a a' Ua', Succ a a' -> Union a' Ua' ->
  a = Ua' -> TransitiveSet a.
Admitted.

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

Theorem Recursion_Theorem_on_Omega : forall A a F, In a A -> FuncFromInto F A A ->
  exists h, RecursiveFunction A a F h /\ forall h', RecursiveFunction A a F h ->
  h = h'.
Admitted.

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

Theorem Enderton4_36a : forall A B m n AuB mn, NaturalNumber m ->
  NaturalNumber n -> Has_n_Elts A m -> Has_n_Elts B n -> BinaryUnion A B AuB ->
  Add m n mn -> Disjoint A B -> Has_n_Elts AuB mn.
Admitted.

Theorem Enderton4_37b : forall A B m n AxB mn, NaturalNumber m ->
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