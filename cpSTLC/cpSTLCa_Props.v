(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(* Simply Typed Lambda Calculus with simple Concept Parameters
   :: version a
   Properties

   Properties of STLC are based on
   Sofware Foundations, v.4 
  
   Last Update: Fri, 29 Oct 2016
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 


(* ***************************************************************** *)
(** * cpSTLCa Properties
      (Simply Typed Lambda Calculus with simple Concept Parameters  
       :: version a) *)
(* ***************************************************************** *)
(* ***************************************************************** *)


Add LoadPath "../..".

Require Import ConceptParams.BasicPLDefs.Maps.
Require Import ConceptParams.BasicPLDefs.Relations.

Require Import ConceptParams.AuxTactics.LibTactics.
Require Import ConceptParams.AuxTactics.BasicTactics.

Require Import ConceptParams.cpSTLC.cpSTLCa_Defs.

Require Import MSets.MSetFacts.

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Bool.Bool.

Require Import Coq.omega.Omega.


(* ################################################################# *)
(** ** Program Well-definedness and Typing *)

(* ================================================================= *)
(** *** Checking Concepts *)

(* ----------------------------------------------------------------- *)
(** **** Concept Well-definedness *)

(** First of all we want to prove that [ids_are_unique] is correct, 
    i.e. if it returns true, than there is no duplicates in the list.    

    A bunch of auxiliary lemmas is needed to prove the main theorem.  
*)

(* We need some facts from sets... *)

Module IdSetFacts := MSetFacts.WFacts IdSet.
Module IdSetProps := MSetProperties.WProperties IdSet.

Import IdSet.
Import IdSetFacts.

Lemma mem_empty__false : forall (x : id),
    ids_mem x ids_empty = false.
Proof.
  reflexivity.
Qed.

Lemma add_eq__mem_true : forall (x : id) (s : id_set),
    ids_mem x (ids_add x s) = true.
Proof.
  intros x s. rewrite mem_1.
  reflexivity.
  apply add_1. reflexivity.
Qed.

Lemma add_neq__mem_ignore : forall (x y : id) (s : id_set),
    x <> y ->
    ids_mem y (ids_add x s) = ids_mem y s.
Proof.
  intros x y s. intros H. 
  remember (add_neq_iff s H) as Hneq. clear HeqHneq.
  repeat (rewrite <- IdSet.mem_spec in Hneq). 
  unfold ids_mem, ids_add in *.
  destruct (IdSet.mem y s) eqn:Hmem.
  - apply Hneq. reflexivity.
  - destruct (IdSet.mem y (ids_add x s)) eqn:Hmem'.
    apply Hneq in Hmem'. inversion Hmem'.
    assumption.
Qed.

Lemma mem_add_false__mem_false : forall (x y : id) (s : id_set),
    ids_mem y (ids_add x s) = false ->
    ids_mem y s = false.
Proof.
  intros x y s H.
  rewrite <- not_mem_iff in H.
  rewrite <- not_mem_iff. intros Hin.
  apply add_2 with (x := x) in Hin. auto.
Qed.  

Lemma add_elem_into_eq__eq : forall (s s' : id_set) (x : id),
    IdSet.Equal s s' ->
    IdSet.Equal (ids_add x s) (ids_add x s').
Proof.
  intros s s' x Heq.
  unfold Equal. intros y.
  split; intros Hin;
    (destruct (beq_idP x y);
       [subst; rewrite <- mem_spec;
        apply add_eq__mem_true
       |remember (add_3 n Hin) as Hyins;
        apply add_2; apply Heq; assumption]).
(* 
add_2: forall (s : t) (x y : elt), In y s -> In y (add x s)
add_3: forall (s : t) (x y : elt), x <> y -> In y (add x s) -> In y s 
*)
Qed.  
  
Lemma ids_are_unique_recur__eq_sets_eq : forall (l : list id) (s s' : id_set),
    IdSet.Equal s s' ->
    ids_are_unique_recur l s = ids_are_unique_recur l s'.
Proof.
  intros l.
  induction l as [| h l' IHl'];
    intros s s' Heq.
  - (* l = nil *)
    reflexivity.
  - (* l = h :: l' *)
    simpl.
    destruct (ids_mem h s) eqn:Hhs.
    + (* h in s *)
      rewrite mem_spec in Hhs.
      unfold Equal in Heq. apply Heq in Hhs as Hhs'.
      rewrite <- mem_spec in Hhs'. unfold ids_mem. rewrite -> Hhs'.
      reflexivity.
    + (* h not in s' *)
      rewrite <- not_mem_iff in Hhs.
      (* unfold Equal in Heq. *)
      destruct (ids_mem h s') eqn:Hhs'.
      * rewrite mem_spec in Hhs'. apply Heq in Hhs'.
        apply Hhs in Hhs'. contradiction.
      * rewrite <- not_mem_iff in Hhs'.
        assert (H: Equal (ids_add h s) (ids_add h s'))
               by (apply add_elem_into_eq__eq; assumption).
        apply IHl'. assumption.
Qed.       

Lemma ids_are_unique_recur__set_permute : forall (l : list id) (s : id_set) (x y : id),
  ids_are_unique_recur l (ids_add x (ids_add y s))
  = ids_are_unique_recur l (ids_add y (ids_add x s)).
Proof.
  intros l s x y.
  apply ids_are_unique_recur__eq_sets_eq.
  apply IdSetProps.add_add.
(*
IdSetProps.add_add: forall (s : t) (x x' : elt), Equal (add x (add x' s)) (add x' (add x s))
*) 
Qed.           

Lemma ids_are_unique_recur_add_true__true : forall (l : list id) (s : id_set) (x : id),
    ids_are_unique_recur l (ids_add x s) = true -> 
    ids_are_unique_recur l s = true.
Proof.
  intros l. induction l as [| h l' IHl'].
  - (* l = nil *)
    intros. reflexivity.
  - (* l = h :: l' *)
    intros s x. simpl. 
    destruct (ids_mem h (ids_add x s)) eqn:Hmem.
    + intros Hcontra. inversion Hcontra.
    + rewrite -> ids_are_unique_recur__set_permute.
      apply mem_add_false__mem_false in Hmem. rewrite -> Hmem.
      apply IHl'.
Qed.    

Lemma ids_are_unique_permute : forall (x y : id) (l : list id),
    ids_are_unique (x :: y :: l) = ids_are_unique (y :: x :: l).
Proof.
  intros x y l.
  destruct (beq_idP x y).
  - (* x = y *)
    subst. reflexivity.
  - (* x <> y *)
    unfold ids_are_unique. simpl.
    rewrite ids_are_unique_recur__set_permute.
    repeat (rewrite add_neq__mem_ignore; simpl).
    reflexivity. auto. assumption.
Qed.    

Lemma ids_are_unique_recur_cons__add : forall (l : list id) 
                                              (x : id) (s : id_set),
    ids_mem x s = false ->
    ids_are_unique_recur (x :: l) s 
    = ids_are_unique_recur l (ids_add x s).
Proof.
  intros. simpl.
  rewrite H. reflexivity.
Qed.
    
Lemma ids_are_unique_cons : forall (x : id) (l : list id),
    ids_are_unique (x :: l) = true ->
    ids_are_unique l = true.
Proof.
  intros x [| h l'].
  - (* l = nil *)
    intros []. reflexivity. 
  - (* l = h :: l' *)
    (* intros x. *)
    unfold ids_are_unique in *. 
    unfold ids_mem, ids_add, ids_empty in *.
    simpl in *.
    destruct (beq_idP h x).
    + (* h = x *)
      subst h. rewrite -> add_eq__mem_true.
      intros Hcontra. inversion Hcontra.
    + (* h <> x *)
      rewrite -> add_neq__mem_ignore. simpl.
      intros H. rewrite ids_are_unique_recur__set_permute in H.
      apply ids_are_unique_recur_add_true__true in H.
      assumption.
      apply not_eq_sym; assumption.
Qed.      

Lemma ids_are_unique_cons__not_in : forall (l : list id) (x : id),
    ids_are_unique (x :: l) = true ->
    ~ List.In x l.
Proof.
  intros l. induction l as [| h l'].
  - (* l = nil *)
    intros x _ H. inversion H. 
  - (* l = h :: l' *)
    intros x H Hin.
    inversion Hin as [Hxh | Hxl'].
    + (* h = x *)
      subst. unfold ids_are_unique in H.
      simpl in H. rewrite -> add_eq__mem_true in H.
      inversion H.
    + (* h in l' *)
      rewrite ids_are_unique_permute in H.
      apply ids_are_unique_cons in H.
      apply IHl' in H. apply H in Hxl'. contradiction.
Qed.            

(** Here is the main [ids_are_unique] correctness theorem: *)

Theorem ids_are_unique__correct : forall (l : list id),
    ids_are_unique l = true -> NoDup l.
Proof.
  intros l. induction l as [ | h l' IHl'].
  - (* l = nil *)
    intros H. apply NoDup_nil.
  - (* l = h :: l' *)
    intros H. apply ids_are_unique_cons in H as H'.
    apply IHl' in H'.
    apply NoDup_cons.
    apply ids_are_unique_cons__not_in in H. assumption.
    assumption.
Qed.

(** And the final steps to prove that [concept_well_defined_b]
    is correct. *)

Lemma type_valid_b__correct : forall (cst : cptcontext) (T : ty),
    type_valid_b cst T = true ->
    type_valid cst T.
Proof.
  intros cst T. generalize dependent cst.
  induction T; intros cst H;
    (* simple cases like TNat *)
    try constructor;
    (* using assumption *)
    try (simpl in H; rewrite -> andb_true_iff in H;
         inversion H as [H1 H2]; clear H).
  - (* T1 -> T2 ... T1 *) apply IHT1 in H1. assumption.
  - (* T1 -> T2 ... T2 *) auto.
  - (* concept_defined *)
    unfold concept_defined.
    intros Hcontra. unfold concept_defined_b in H1.
    destruct (cst i); tryfalse.
  - (* type_valid *)
    apply IHT in H2. assumption.
Qed.

Print types_valid_b.

Lemma types_valid_b__correct : forall (cst : cptcontext) (ts : list ty),
    types_valid_b cst ts = true ->
    List.Forall (fun ftype => type_valid cst ftype) ts.
Proof.
  intros cst ts. unfold types_valid_b.
  induction ts as [| t ts'];
    intros H.
  - (* ts = nil *)
    apply Forall_nil.
  - (* ts = t :: ts' *)
    simpl in H. rewrite -> andb_true_iff in H.
    inversion H as [Ht Hts']; clear H.
    apply IHts' in Hts'. apply type_valid_b__correct in Ht.
    apply Forall_cons; auto.
Qed.

Theorem concept_well_defined_b__correct : forall (cst : cptcontext) (C : conceptdef),
    concept_welldefined_b cst C = true ->
    concept_welldefined   cst C.
Proof.
  intros cst C. intros H.
  unfold concept_welldefined_b in H. destruct C.
  unfold concept_welldefined.
  destruct (split (map namedecl_to_pair n)).
  rewrite -> andb_true_iff in H. inversion H as [Hid Hty].
  apply ids_are_unique__correct in Hid.
  apply types_valid_b__correct in Hty.
  split; auto.
Qed.


(** But we also have to prove the opposite side, soundness.
    
    Let's start with soundness of [ids_are_unique]:
    if there is no dups in the list, then ids_are_unique is true. *)

Lemma ids_are_unique_recur_cons : forall (l : list id) (x : id) (s : id_set),
    ids_are_unique_recur (x :: l) s = true ->
    ids_are_unique_recur l s = true.
Proof.
  intros [| h l'].
  - (* l = nil *)
    intros x s Hrec. reflexivity.
  - (* l = h :: l' *)
    intros x s Hxh.
    inversion Hxh. rewrite -> H0.
    destruct (ids_mem x s) eqn: Hmemxs. 
      inversion H0.
    destruct (ids_mem h (ids_add x s)) eqn: Hmemhxs.
      inversion H0.
    remember Hmemhxs as Hmemhxs'; clear HeqHmemhxs'.
    apply ids_are_unique_recur_cons__add with (l := l') (s := (ids_add x s)) in Hmemhxs.
    rewrite -> H0 in Hmemhxs.
    apply ids_are_unique_recur_add_true__true in Hmemhxs.
    assumption.
Qed.

Lemma ids_are_unique_recur_cons__mem_false : forall (l : list id) 
                                                    (x : id) (s : id_set),
    ids_are_unique_recur (x :: l) s = true ->
    ids_mem x s = false.
Proof.
  intros [| h l'].
  - (* l = nil *)
    intros x s H.
    inversion H as [H'].
    destruct (ids_mem x s) eqn: Hxs; auto. 
  - (* l = h :: l' *)
    intros x s H. 
    simpl in H. destruct (ids_mem x s) eqn: Hxs; auto.
Qed.

Lemma not_in_list_cons : forall (l : list id) (h : id) (x : id),
    ~ List.In x (h :: l) ->
    (~ List.In x l) /\ (x <> h).
Proof.
  intros l h x Hh.
  split.
  - (* ~ List.In x l *)
    intros H. assert (contra: List.In x (h :: l)). 
    { simpl. right. assumption. }
    apply Hh in contra. auto.                                       
  - (* x <> h *)
    intros H. assert (contra: List.In x (h :: l)). 
    { simpl. left. symmetry. assumption. }    
    tauto.
Qed.

Lemma ids_are_unique_recur__not_mem_add : forall (l : list id) 
                                                 (x : id) (s : id_set),
    ids_are_unique_recur l s = true ->
    ~ List.In x l ->
    ids_mem x s = false ->
    ids_are_unique_recur l (ids_add x s) = true.
Proof.
  intros l. induction l as [| h l' IHl'].
  - (* l = nil *)
    intros. reflexivity.
  - (* l = h :: l' *)
    intros x s Hrecs Hin Hmem.    
    simpl.

    assert (Hin' := Hin). apply not_in_list_cons in Hin'.
    inversion Hin' as [Hinl' Hneqxh].

    assert (Hhs: ids_mem h s = false) 
      by (apply ids_are_unique_recur_cons__mem_false with l'; apply Hrecs).
    assert (Hmemf: ids_mem h (ids_add x s) = false) by
        (rewrite (add_neq__mem_ignore x h s Hneqxh); rewrite Hhs; auto).

    rewrite Hmemf.
    rewrite ids_are_unique_recur__set_permute.
    rewrite (ids_are_unique_recur_cons__add l' h s Hhs) in Hrecs.

    apply IHl'. 
    + assumption.
    + assumption.
    + rewrite add_neq__mem_ignore; auto.
Qed.

Lemma ids_are_unique_recur_true__cons_true : forall (l : list id) 
                                                    (s : id_set) (x : id),
    ids_are_unique_recur l s = true ->
    ~ List.In x l ->
    ids_mem x s = false ->
    ids_are_unique_recur (x :: l) s = true.
Proof. 
  intros l s x H Hin Hmem.
  simpl.
  rewrite Hmem.
  apply ids_are_unique_recur__not_mem_add; auto.
Qed.

(** Here is the main [ids_are_unique] soundness theorem: *)

Theorem ids_are_unique__sound : forall (l : list id),
    NoDup l -> ids_are_unique l = true.
Proof.
  intros l. induction l as [ | h l' IHl'].
  - (* l = nil *)
    intros H. reflexivity.
  - (* l = h :: l' *)
    intros H. inversion H; subst.
    apply IHl' in H3.
    unfold ids_are_unique in *. 
    apply ids_are_unique_recur_true__cons_true.
    + assumption.
    + assumption.
    + reflexivity.
Qed.


(* ----------------------------------------------------------------- *)
(** **** Concept Typing *)

Theorem concept_type_check__correct : forall (cst : cptcontext) 
                                             (C : conceptdef) (CT : cty),  
    concept_type_check cst C = Some CT ->
    concept_has_type cst C CT.
Proof.
  intros cst C CT. intros H.
  unfold concept_type_check in H.
  destruct (concept_welldefined_b cst C). 
  destruct C.
  
  (* unfold concept_has_type in H. inversion H as [Hwd HCT]. clear H. *)

Abort.

(*

Lemma id_set_In__add_permute : forall (x y z : id) (s : id_set),
    IdSet.In x (ids_add y (ids_add z s)) ->
    IdSet.In x (ids_add z (ids_add y s)).
n__add_permute.
Qed.

Lemma mem_add_permute : forall (x y z : id) (s : id_set),
    ids_mem x (ids_add y (ids_add z s))
    = ids_mem x (ids_add z (ids_add y s)).
Proof.
  intros x y z s.
  destruct (ids_mem x (ids_add y (ids_add z s))) eqn:Hmem.
  - (* mem x (add y (add z s)) = true *)
    symmetry.
    apply mem_true__add_permute. assumption.
  - (* mem x (add y (add z s)) = false *)
    apply not_mem_iff in Hmem. unfold not in Hmem.
    symmetry. apply not_mem_iff.
    intros Hin. apply id_set_In__add_permute in Hin.
    apply Hmem in Hin; inversion Hin.
Qed.

(** [id_list_to_id_set] builds set from a list of ids. *)

Definition id_list_to_id_set (l : list id) :=
  fold_left (fun acc x => ids_add x acc) l ids_empty.

*)