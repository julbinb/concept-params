(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(* Mainly borrowed from Sofware Foundations, v.4 
   $Date: 2015-12-11 17:17:29 -0500 (Fri, 11 Dec 2015) $

   Last Update: Mon, 27 Mar 2017
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 


(* ***************************************************************** *)
(** * Maps: Total and Partial Maps *)
(* ***************************************************************** *)
(* ***************************************************************** *)

Require Import Identifier.

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.

Require Import Coq.Logic.FunctionalExtensionality.
(* for t_update proof *)

Require Import Coq.MSets.MSets.

(** Maps (or dictionaries) are ubiquitous data structures, both in
    software construction generally and in the theory of programming
    languages in particular.

    We'll define two flavors of maps: _total_ maps, which include a
    "default" element to be returned when a key being looked up
    doesn't exist, and _partial_ maps, which return an [option] to
    indicate success or failure.  The latter is defined in terms of
    the former, using [None] as the default element. *)


(* ################################################################# *)
(** * Total Maps *)
(* ################################################################# *)

(** We build partial maps in two steps.  First, we define a type of
    _total maps_ that return a default value when we look up a key
    that is not present in the map. *)

Definition total_map (A : Type) := id -> A. 

(** Intuitively, a total map over an element type [A] _is_ just a
    function that can be used to look up [id]s, yielding [A]s.

    The function [t_empty] yields an empty total map, given a default
    element; this map always returns the default element when applied
    to any id. *)

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

(** More interesting is the [update] function, which (as before) takes
    a map [m], a key [x], and a value [v] and returns a new map that
    takes [x] to [v] and takes every other key to whatever [m] does. *)

Definition t_update {A : Type} (m : total_map A)
                    (x : id) (v : A)
  := fun x' => if beq_id x x' then v else m x'.

(** For building examples easier, we define a function that creates
    total map from a list of pairs.
    [xs] : list of pairs, [dv] : default value.
*)

Definition t_from_list {A : Type} (xs : list (id * A)) (dv : A) : total_map A
  := fold_left
       (fun m xv => match xv with (x, v) => t_update m x v end)
       xs (t_empty dv).

(* ----------------------------------------------------------------- *)
(** ** Properties of Total Maps *)
(* ----------------------------------------------------------------- *)

(** First, the empty map returns its default element for all keys: *)
Lemma t_apply_empty:  forall A x v, @t_empty A v x = v.
Proof.
  intros A x v.
  unfold t_empty. reflexivity.
Qed.  

(** Next, if we update a map [m] at a key [x] with a new value [v]
    and then look up [x] in the map resulting from the [update], we
    get back [v]: *)

Lemma t_update_eq : forall A (m : total_map A) x v,
  (t_update m x v) x = v.
Proof.
  intros A m x v.
  unfold t_update. rewrite <- beq_id_refl. reflexivity.
Qed.  
  
(** On the other hand, if we update a map [m] at a key [x1] and then
    look up a _different_ key [x2] in the resulting map, we get the
    same result that [m] would have given: *)

Theorem t_update_neq : forall (X : Type) v x1 x2
                              (m : total_map X),
  x1 <> x2 ->
  (t_update m x1 v) x2 = m x2.
Proof.
  intros X v x1 x2 m.
  intros neq. unfold t_update.
  apply false_beq_id in neq. rewrite -> neq. reflexivity.
Qed.

(** If we update a map [m] at a key [x] with a value [v1] and then
    update again with the same key [x] and another value [v2], the
    resulting map behaves the same (gives the same result when applied
    to any key) as the simpler map obtained by performing just
    the second [update] on [m]: *)

Lemma t_update_shadow : forall A (m : total_map A) v1 v2 x,
    t_update (t_update m x v1) x v2
  = t_update m x v2.
Proof.
  intros A M v1 v2 x.
  unfold t_update.
  apply functional_extensionality. intros x'.
  destruct (beq_id x x') eqn:H.
  - (* x = x' *) reflexivity.
  - (* x <> x' *) reflexivity.
Qed.                  

(** Using the example in chapter [IndProp] as a template, use
    [beq_idP] to prove the following theorem, which states that if we
    update a map to assign key [x] the same value as it already has in
    [m], then the result is equal to [m]: *)

Theorem t_update_same : forall X x (m : total_map X),
  t_update m x (m x) = m.
Proof.
  intros X x m. unfold t_update.
  apply functional_extensionality. intro x'.
  destruct (beq_idP x x') as [H | H].
  - rewrite H. reflexivity.
  - reflexivity.
Qed.    
  
(** Use [beq_idP] to prove one final property of the [update]
    function: If we update a map [m] at two distinct keys, it doesn't
    matter in which order we do the updates. *)

Theorem t_update_permute : forall (X:Type) v1 v2 x1 x2
                             (m : total_map X),
  x2 <> x1 ->
    (t_update (t_update m x2 v2) x1 v1)
  = (t_update (t_update m x1 v1) x2 v2).
Proof.
  intros X v1 v2 x1 x2 m.
  intros H. apply beq_id_false_iff in H as H'.
  unfold t_update. apply functional_extensionality.
  intros x. destruct (beq_idP x1 x) as [H1 | H1].
  - destruct (beq_idP x2 x) as [H2 | H2].
    + rewrite <- H1 in H2. apply H in H2. inversion H2.
    + reflexivity.
  - destruct (beq_idP x2 x) as [H2 | H2].
    + reflexivity.
    + reflexivity.
Qed.  

(* ################################################################# *)
(** * Partial Maps *)
(* ################################################################# *)

(** Finally, we define _partial maps_ on top of total maps.  A partial
    map with elements of type [A] is simply a total map with elements
    of type [option A] and default element [None]. *)

Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A :=
  t_empty None.

Definition update {A : Type} (m : partial_map A)
                  (x : id) (v : A) :=
  t_update m x (Some v).

(** Similarly to total maps, we define a function for creating 
    maps from lists. *)

Definition from_list {A : Type} (xs : list (id * A)) : partial_map A
  := fold_left
       (fun m xv => match xv with (x, v) => update m x v end)
       xs empty.

(** We can now lift all of the basic lemmas about total maps to
    partial maps. *)

Lemma apply_empty : forall A x, @empty A x = None.
Proof.
  intros. unfold empty. rewrite t_apply_empty.
  reflexivity.
Qed.

Lemma update_eq : forall A (m: partial_map A) x v,
  (update m x v) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.

Theorem update_neq : forall (X:Type) v x1 x2
                       (m : partial_map X),
  x2 <> x1 ->
  (update m x2 v) x1 = m x1.
Proof.
  intros X v x1 x2 m H.
  unfold update. rewrite t_update_neq. reflexivity.
  apply H. Qed.

Lemma update_shadow : forall A (m: partial_map A) v1 v2 x,
  update (update m x v1) x v2 = update m x v2.
Proof.
  intros A m v1 v2 x1. unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.

Theorem update_same : forall X v x (m : partial_map X),
  m x = Some v ->
  update m x v = m.
Proof.
  intros X v x m H. unfold update. rewrite <- H.
  apply t_update_same.
Qed.

Theorem update_permute : forall (X:Type) v1 v2 x1 x2
                                (m : partial_map X),
  x2 <> x1 ->
    (update (update m x2 v2) x1 v1)
  = (update (update m x1 v1) x2 v2).
Proof.
  intros X v1 v2 x1 x2 m. unfold update.
  apply t_update_permute.
Qed.

