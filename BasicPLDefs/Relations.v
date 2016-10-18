(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(* Borrowed from Sofware Foundations, v.4 

   Last Update: Tue, 18 Oct 2016
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 


(* ***************************************************************** *)
(** * Relations *)
(* ***************************************************************** *)
(* ***************************************************************** *)

(** We will be working with several different single-step relations,
    so it is helpful to generalize a bit and state a few definitions
    and theorems about relations in general.) 

    A _binary relation_ on a set [X] is a family of propositions
    parameterized by two elements of [X] -- i.e., a proposition about
    pairs of elements of [X].  *)

Definition relation (X : Type) := X -> X -> Prop.


(* ################################################################# *)
(** ** Basic Properties of Relations *)

(* ----------------------------------------------------------------- *)
(** *** Deterministic Relations *)

(** One simple property of the [==>] relation is that, like the
    big-step evaluation relation for Imp, it is _deterministic_.

    _Theorem_: For each [t], there is at most one [t'] such that [t]
    steps to [t'] ([t ==> t'] is provable).  Formally, this is the
    same as saying that [==>] is deterministic. *)

Definition deterministic {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

(* Or, alternatively, deterministic relations are called... *)
(* Partial Functions *)

(** A relation [R] on a set [X] is a _partial function_ if, for every
    [x], there is at most one [y] such that [R x y] -- i.e., [R x y1]
    and [R x y2] together imply [y1 = y2]. *)

Definition partial_function {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

(* ----------------------------------------------------------------- *)
(** *** Normal Form *)

(** Let's begin by giving a name to terms that cannot make progress.  
    We'll call them _normal forms_.  *)

Definition normal_form {X : Type} (R : relation X) (t : X) : Prop :=
  ~ exists t', R t t'.

(* ----------------------------------------------------------------- *)
(** *** Reflexive Relations *)

(** A _reflexive_ relation on a set [X] is one for which every element
    of [X] is related to itself. *)

Definition reflexive {X : Type} (R : relation X) : Prop :=
  forall a : X, R a a.

(* ----------------------------------------------------------------- *)
(** *** Transitive Relations *)

(** A relation [R] is _transitive_ if [R a c] holds whenever [R a b]
    and [R b c] do. *)

Definition transitive {X : Type} (R : relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).


(* ################################################################# *)
(** * Reflexive, Transitive Closure *)

(** The _reflexive, transitive closure_ of a relation [R] is the
    smallest relation that contains [R] and that is both reflexive and
    transitive.  Formally, it is defined like this in the Relations
    module of the Coq standard library: *)

Inductive clos_refl_trans {X : Type} (R : relation X) : relation X :=
    | rt_step  : forall x y, R x y -> clos_refl_trans R x y
    | rt_refl  : forall x, clos_refl_trans R x x
    | rt_trans : forall x y z,
          clos_refl_trans R x y ->
          clos_refl_trans R y z ->
          clos_refl_trans R x z.

(** For the purposes of PL development,
    since we'll want to reuse the idea of multi-step reduction many
    times, let's give it another name and define in shorter way.

    Given a relation [R], we define a relation [multi R], called the
    _multi-step closure of [R]_ as follows. *)

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
        R x y ->
        multi R y z ->
        multi R x z.

(** Our new definition of reflexive, transitive closure "bundles"
    the [rt_step] and [rt_trans] rules into the single rule step.
    The left-hand premise of this step is a single use of [R],
    leading to a much simpler induction principle.

    Before we go on, we should check that the two definitions do
    indeed define the same relation...

    First, we prove two lemmas showing that [multi] mimics
    the behavior of the two "missing" [clos_refl_trans]
    constructors.  *)

Lemma multi_R : forall (X : Type) (R : relation X) (x y : X),
       R x y -> multi R x y.
Proof.
  intros X R x y H.
  eapply multi_step.
    apply H. apply multi_refl.
Qed.  

Theorem multi_trans : forall (X : Type) (R : relation X),
    transitive (multi R).
Proof.
  unfold transitive.
  intros X R x y z G H.
  induction G.
    - (* multi_refl *) assumption.
    - (* multi_step *)
      apply multi_step with y. assumption.
      apply IHG. assumption.
Qed.

Theorem rtc_multi_coincide :
  forall (X : Type) (R : relation X) (x y : X),
  clos_refl_trans R x y <-> multi R x y.
Proof.
  intros X R x y. split.
  - (* -> *)
    intros H. induction H.
    + (* R x y *)
      eapply multi_step.
      apply H. apply multi_refl.
    + (* reflexive step *)
      apply multi_refl.
    + (* transitive step *)
      apply multi_trans with y; auto.
  - (* <- *)
    intros H. induction H.
    + (* reflexive step *)
      apply rt_refl.
    + (* transitive step *)
      apply rt_step in H.
      apply rt_trans with y; auto.
Qed.
      
(* ################################################################# *)
(** ** Basic Properties of Relations *)

(* ----------------------------------------------------------------- *)
(** *** Symmetric and Antisymmetric Relations *)

(** A relation [R] is _symmetric_ if [R a b] implies [R b a]. *)

Definition symmetric {X : Type} (R : relation X) :=
  forall a b : X, (R a b) -> (R b a).

(** A relation [R] is _antisymmetric_ if [R a b] and [R b a] together
    imply [a = b] -- that is, if the only "cycles" in [R] are trivial
    ones. *)

Definition antisymmetric {X : Type} (R : relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

(* ----------------------------------------------------------------- *)
(** *** Equivalence Relations *)

(** A relation is an _equivalence_ if it's reflexive, symmetric, and
    transitive.  *)

Definition equivalence {X : Type} (R : relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

(* ----------------------------------------------------------------- *)
(** *** Partial Orders and Preorders *)

(** A relation is a _partial order_ when it's reflexive,
    _anti_-symmetric, and transitive.  In the Coq standard library
    it's called just "order" for short. *)

Definition order {X : Type} (R : relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).

(** A preorder is almost like a partial order, but doesn't have to be
    antisymmetric. *)

Definition preorder {X : Type} (R : relation X) :=
  (reflexive R) /\ (transitive R).