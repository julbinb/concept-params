(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(* Transformation of
     List of (unique) Elements
   into
     Set of Elements (AVL-based)   
  
   Last Update: Fri, 12 May 2017
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 

Add LoadPath "../..".

Require Import ConceptParams.AuxTactics.LibTactics.
Require Import ConceptParams.AuxTactics.BasicTactics.

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Bool.Bool.

Require Import Coq.Structures.Orders.
Require Import Coq.MSets.MSets.
Require Import Coq.MSets.MSetInterface.

(* ***************************************************************** *)
(** * List-to-Set 

      [MSet]-based transformations of [List] *)

(** This module provides: 
    1) functions for analysis and transformation of [List] 
       into [MSet];
    2) properties of these functions;
    3) proofs of the properties.  
 *)
(* ***************************************************************** *)
(* ***************************************************************** *)

(* ################################################################# *)
(** ** Module Type [List2Set] *)
(* ################################################################# *)

(** [List2Set] functor takes [id_UOT : UsualOrderedType] module, 
    which provides ordering for type [id_UOT.t] of "identifiers".

    It provides functionality and proofs about transformations
    of lists into sets. *)

Module Type List2MSet 
       (id_UDT : UsualDecidableType)
       (id_Set : MSetInterface.WSets
           with Definition E.t := id_UDT.t
           with Definition E.eq := id_UDT.eq)
.

  (** Ordering of ids *)
  Module IdDT := id_UDT.
  (** Set of ids *)
  Module IdSet := id_Set. (*MSetAVL.Make IdDT*)

  (** Type of Identifiers *)
  Definition id := IdDT.t.

  (** Type of Set-of-Identifiers *)
  Definition id_set := IdSet.t.

  (** [ids_are_unique] checks if all ids in the list are unique *)
  Parameter ids_are_unique : list id -> bool.

  (** [set_from_list] builds a set of ids from the list of ids *)
  Parameter set_from_list : list id -> id_set.

  (** Properties of the module functions *)
  Module Props.
    Axiom ids_are_unique__sound : forall (l : list id),
      ids_are_unique l = true -> NoDup l.
    
    Axiom ids_are_unique__complete : forall (l : list id),
        NoDup l -> ids_are_unique l = true.

    Axiom ids_are_unique__cons : forall (l : list id) (x : id),
        ids_are_unique (x :: l) = true ->
        ids_are_unique l = true.
  End Props.

End List2MSet.


(* ################################################################# *)
(** ** Module [MList2Set] *)
(* ################################################################# *)

(** [MList2Set] functor takes [id_UOT : UsualOrderedType] module, 
    which provides ordering for type [id_UOT.t] of "identifiers",
    and returns a module with 
    functions for [MSet] based transformation of [List],
    together with their proven properties. *)

Module MList2MSet
       (id_UDT : UsualDecidableType)
       (id_Set : MSetInterface.WSets
           with Definition E.t := id_UDT.t
           with Definition E.eq := id_UDT.eq)
<: List2MSet id_UDT id_Set.

  (** Ordering of ids *)
  Module IdDT := id_UDT.
  (** AVL Set of ids *)
  Module IdSet := id_Set. (*MSetAVL.Make IdDT*)

  (** Type of Identificators *)
  Definition id : Type := IdDT.t.

  (** Type of Set-of-Identifiers *)
  Definition id_set := IdSet.t.

(* ================================================================= *)
(** *** Helper Functions *)
(* ================================================================= *)

  Module HelperFuns.

    (** Aux recursive function for [ids_are_unique] *)
    Fixpoint ids_are_unique_recur (nmlist : list id) (nmset : id_set) : bool :=
      match nmlist with
      | nil => true
      | nm :: nms => if IdSet.mem nm nmset 
                     then false
                     else ids_are_unique_recur nms (IdSet.add nm nmset)
      end.

    Definition set_from_list' (xs : list id) (s : id_set) : id_set
    := fold_left
         (fun s x => IdSet.add x s)
         xs s.

  End HelperFuns.

(* ================================================================= *)
(** *** Main Functions *)
(* ================================================================= *)

  (** [ids_are_unique] checks if all ids in the list are unique *)
  Definition ids_are_unique (names : list id) : bool :=
    HelperFuns.ids_are_unique_recur names IdSet.empty.

  (** [set_from_list] builds a set of ids from the list of ids *)
  Definition set_from_list (xs : list id) : id_set
    := HelperFuns.set_from_list' xs IdSet.empty.

(* ================================================================= *)
(** *** Properties *)
(* ================================================================= *)

  Module Props.

    Module IdSetFacts := MSetFacts.WFacts IdSet.
    Module IdSetProps := MSetProperties.WProperties IdSet.

    Import IdDT.
    Import IdSet.
    Import IdSetFacts.
    Import IdSetProps.
    Import HelperFuns.

    Module Helper.

(* ----------------------------------------------------------------- *)
(** *** Simple aux facts about sets *)
(* ----------------------------------------------------------------- *)

    Lemma not_IdDT_eq__sym : forall x y,
        ~ IdDT.eq x y ->
        ~ IdDT.eq y x.
    Proof.
      intros x y H Heq. 
      symmetry in Heq. tauto.
    Qed.

    Lemma add_eq__mem_true : forall (x y : id) (s : id_set),
        IdDT.eq x y ->
        mem x (add y s) = true.
    Proof.
      intros x y s H.
      rewrite mem_1. reflexivity.
      apply add_1. symmetry. assumption.
    Qed.

    Lemma add_neq__mem_ignore : forall (x y : id) (s : id_set),
        x <> y ->
        mem y (add x s) = mem y s.
    Proof.
      intros x y s. intros H. 
      remember (add_neq_iff s H) as Hneq. clear HeqHneq.
      repeat (rewrite <- IdSet.mem_spec in Hneq). 
      destruct (IdSet.mem y s) eqn:Hmem.
      - apply Hneq. reflexivity.
      - destruct (IdSet.mem y (add x s)) eqn:Hmem'.
        assert (Htriv : true = true) by reflexivity.
        apply Hneq in Htriv; auto.
        reflexivity.
    Qed.

    Lemma mem_add_false__mem_false : forall (x y : id) (s : id_set),
        mem y (add x s) = false ->
        mem y s = false.
    Proof.
      intros x y s H.
      rewrite <- not_mem_iff in H.
      rewrite <- not_mem_iff. intros Hin.
      apply add_2 with (x := x) in Hin. auto.
    Qed. 

    Lemma add_elem_into_eq__eq : forall (s s' : id_set) (x : id),
        IdSet.Equal s s' ->
        IdSet.Equal (add x s) (add x s').
    Proof.
      intros s s' x Heq.
      unfold Equal. intros y.
      split; intros Hin;
        (destruct (IdDT.eq_dec x y);
         [rewrite <- mem_spec;
          apply add_eq__mem_true;
          apply eq_sym; assumption
         |remember (add_3 n Hin) as Hyins;
          apply add_2; apply Heq; assumption]).
    Qed. 

(* ----------------------------------------------------------------- *)
(** *** Aux facts about [ids_are_unique*] for soundness *)
(* ----------------------------------------------------------------- *)

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
        destruct (mem h s) eqn:Hhs.
        + (* h in s *)
          rewrite mem_spec in Hhs.
          unfold Equal in Heq. apply Heq in Hhs as Hhs'.
          rewrite <- mem_spec in Hhs'. rewrite -> Hhs'.
          reflexivity.
        + (* h not in s' *)
          rewrite <- not_mem_iff in Hhs.
          (* unfold Equal in Heq. *)
          destruct (mem h s') eqn:Hhs'.
          * rewrite mem_spec in Hhs'. apply Heq in Hhs'.
            apply Hhs in Hhs'. contradiction.
          * rewrite <- not_mem_iff in Hhs'.
            assert (H: Equal (add h s) (add h s'))
              by (apply add_elem_into_eq__eq; assumption).
            apply IHl'. assumption.
    Qed. 

    Lemma ids_are_unique_recur__set_permute : 
      forall (l : list id) (s : id_set) (x y : id),
        ids_are_unique_recur l (add x (add y s))
        = ids_are_unique_recur l (add y (add x s)).
    Proof.
      intros l s x y.
      apply ids_are_unique_recur__eq_sets_eq.
      apply IdSetProps.add_add.
    Qed.  

    Lemma ids_are_unique_recur_add_true__true : 
      forall (l : list id) (s : id_set) (x : id),
        ids_are_unique_recur l (add x s) = true -> 
        ids_are_unique_recur l s = true.
    Proof.
      intros l. induction l as [| h l' IHl'].
      - (* l = nil *)
        intros. reflexivity.
      - (* l = h :: l' *)
        intros s x. simpl. 
        destruct (mem h (add x s)) eqn:Hmem.
        + intros Hcontra. inversion Hcontra.
        + rewrite -> ids_are_unique_recur__set_permute.
          apply mem_add_false__mem_false in Hmem. rewrite -> Hmem.
          apply IHl'.
    Qed. 

    Lemma ids_are_unique_permute : forall (x y : id) (l : list id),
        ids_are_unique (x :: y :: l) = ids_are_unique (y :: x :: l).
    Proof.
      intros x y l.
      unfold ids_are_unique. simpl.
      destruct (eq_dec x y) as [Heq | Heq].
      - (* x = y *)
        rewrite (add_eq__mem_true _ _ _ Heq).
        apply eq_sym in Heq. rewrite (add_eq__mem_true _ _ _ Heq).
        subst. reflexivity.
      - (* x <> y *)    
        rewrite ids_are_unique_recur__set_permute.
        rewrite add_neq_b, empty_b. rewrite add_neq_b, empty_b.
        rewrite empty_b. reflexivity.
        apply not_IdDT_eq__sym; assumption.
        assumption.
    Qed.  

    Lemma ids_are_unique_cons : forall (x : id) (l : list id),
        ids_are_unique (x :: l) = true ->
        ids_are_unique l = true.
    Proof.
      intros x [| h l'].
      - (* l = nil *)
        intros []. unfold ids_are_unique. simpl. 
        rewrite empty_b. reflexivity. 
      - (* l = h :: l' *)
        (* intros x. *)
        unfold ids_are_unique in *. 
        simpl in *.
        destruct (IdDT.eq_dec h x) as [Heq | Heq].
        + (* h = x *)
          rewrite -> add_eq__mem_true.
          intros Hcontra. rewrite empty_b in *. 
          inversion Hcontra. 
          subst. reflexivity.
        + (* h <> x *)
          apply not_IdDT_eq__sym in Heq.
          rewrite -> (add_neq_b _ Heq).
          rewrite empty_b. rewrite empty_b. 
          intros H. rewrite ids_are_unique_recur__set_permute in H.
          apply ids_are_unique_recur_add_true__true in H.
          assumption.
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
          rewrite empty_b in H.
          inversion H. apply eq_refl.
        + (* h in l' *)
          rewrite ids_are_unique_permute in H.
          apply ids_are_unique_cons in H.
          apply IHl' in H. apply H in Hxl'. contradiction.
    Qed.   

(* ----------------------------------------------------------------- *)
(** *** Aux facts about [ids_are_unique*] for completeness *)
(* ----------------------------------------------------------------- *)

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

    Lemma ids_are_unique_recur_cons__mem_false : 
      forall (l : list id) (x : id) (s : id_set),
        ids_are_unique_recur (x :: l) s = true ->
        mem x s = false.
    Proof.
      intros [| h l'].
      - (* l = nil *)
        intros x s H.
        inversion H as [H'].
        destruct (mem x s) eqn: Hxs; auto. 
      - (* l = h :: l' *)
        intros x s H. 
        simpl in H. destruct (mem x s) eqn: Hxs; auto.
    Qed.

    Lemma ids_are_unique_recur_cons__add : 
      forall (l : list id) (x : id) (s : id_set),
        mem x s = false ->
        ids_are_unique_recur (x :: l) s 
        = ids_are_unique_recur l (add x s).
    Proof.
      intros. simpl.
      rewrite H. reflexivity.
    Qed.

    Lemma ids_are_unique_recur__not_mem_add : 
      forall (l : list id) (x : id) (s : id_set),
        ids_are_unique_recur l s = true ->
        ~ List.In x l ->
        mem x s = false ->
        ids_are_unique_recur l (add x s) = true.
    Proof.
      intros l. induction l as [| h l' IHl'].
      - (* l = nil *)
        intros. reflexivity.
      - (* l = h :: l' *)
        intros x s Hrecs Hin Hmem.    
        simpl.
        assert (Hin' := Hin). apply not_in_list_cons in Hin'.
        inversion Hin' as [Hinl' Hneqxh].
        assert (Hhs: mem h s = false) 
          by (apply ids_are_unique_recur_cons__mem_false with l'; apply Hrecs).
        assert (Hmemf: mem h (add x s) = false) by
            (rewrite (add_neq__mem_ignore x h s Hneqxh); rewrite Hhs; auto).
        rewrite Hmemf.
        rewrite ids_are_unique_recur__set_permute.
        rewrite (ids_are_unique_recur_cons__add l' h s Hhs) in Hrecs.
        apply IHl'. 
        + assumption.
        + assumption.
        + rewrite add_neq__mem_ignore; auto.
    Qed.

    Lemma ids_are_unique_recur_true__cons_true : 
      forall (l : list id) (s : id_set) (x : id),
        ids_are_unique_recur l s = true ->
        ~ List.In x l ->
        mem x s = false ->
        ids_are_unique_recur (x :: l) s = true.
    Proof. 
      intros l s x H Hin Hmem.
      simpl. rewrite Hmem.
      apply ids_are_unique_recur__not_mem_add; auto.
    Qed.

(* ----------------------------------------------------------------- *)
(** *** Aux facts about [set_from_list] *)
(* ----------------------------------------------------------------- *)

    Lemma in_set_from_list'__in_list : 
      forall (l : list id) (x : id) (s : id_set),
        ~ IdSet.In x s ->
        IdSet.In x (set_from_list' l s) ->
        List.In x l.
    Proof.
      intros l; induction l as [| h l' IHl'].
      - (* l = nil *)
        unfold set_from_list;
        intros x s H; simpl in *.
        assumption.
      - (* l = h :: l' *)
        intros x s Hin. simpl in *.
        intros H.
        destruct (IdDT.eq_dec x h) eqn:Heq; subst.
        + left; reflexivity.
        + right.
          assert (Hin' : ~ In x (add h s)).
          { intros Hins. rewrite add_spec in Hins.
            inversion Hins as [Hcontra | Hcontra].
            apply n in Hcontra; contradiction.
            apply Hin in Hcontra; contradiction. }
          specialize (IHl' x (add h s) Hin' H).
          assumption.
    Qed.

    Lemma in_set_from_list'_spec : 
      forall (l : list id) (x : id) (s : id_set),
        IdSet.In x (set_from_list' l s) ->
        List.In x l \/ IdSet.In x s.
    Proof.
      intros l; induction l as [| h l' IHl'].
      - (* l = nil *)
        intros x s Hin. simpl in Hin.  
        right. assumption.
      - (* l = h :: l' *)
        intros x s Hin.
        simpl in Hin. 
        specialize (IHl' x _ Hin).
        inversion IHl' as [Hin' | Hin'].
        left. right. assumption.
        destruct (IdDT.eq_dec x h) eqn:Heq.
        + subst. left. left. reflexivity.
        + clear Heq.
          right. apply add_3 with (s := s) (x := h). 
          intros contra. symmetry in contra.
          apply n in contra. contradiction.
          assumption.
    Qed.

    Lemma in_set__in_set_from_list' :
      forall (l : list id) (x : id) (s : id_set),
        IdSet.In x s ->
        In x (set_from_list' l s).
    Proof.
      intros l. induction l as [| h l' IHl'].
      - (* l = nil *)
        intros x s Hin. simpl. assumption.
      - (* l = h :: l' *)
        intros x s Hin.
        simpl. apply IHl'.
        destruct (IdDT.eq_dec x h) eqn:Heq.
        + subst. apply add_1. reflexivity.
        + apply add_2. assumption.
    Qed.

    Lemma in_list__in_set_from_list' :
      forall (l : list id) (x : id) (s : id_set),
        List.In x l ->
        IdSet.In x (set_from_list' l s).
    Proof.
      intros l. induction l as [| h l' IHl'].
      - (* l = nil *)
        intros x s Hin. inversion Hin.
      - (* l = h :: l' *)
        intros x s Hin.
        inversion Hin as [Heq | Hin'].        
        + subst. simpl.
          apply in_set__in_set_from_list'.
          apply add_1. reflexivity.
        + simpl. apply IHl'; assumption.
    Qed.

    End Helper.

(* ================================================================= *)
(** *** Main Properties *)
(* ================================================================= *)

(* ----------------------------------------------------------------- *)
(** *** About [ids_are_unique] *)
(* ----------------------------------------------------------------- *)

    (** Here is the main [ids_are_unique] soundness theorem: *)

    Theorem ids_are_unique__sound : forall (l : list id),
        ids_are_unique l = true -> NoDup l.
    Proof.
      intros l. induction l as [ | h l' IHl'].
      - (* l = nil *)
        intros H. apply NoDup_nil.
      - (* l = h :: l' *)
        intros H. apply Helper.ids_are_unique_cons in H as H'.
        apply IHl' in H'.
        apply NoDup_cons.
        apply Helper.ids_are_unique_cons__not_in in H. assumption.
        assumption.
    Qed.

    (** Here is the main [ids_are_unique] completeness theorem: *)

    Theorem ids_are_unique__complete : forall (l : list id),
        NoDup l -> ids_are_unique l = true.
    Proof.
      intros l. induction l as [ | h l' IHl'].
      - (* l = nil *)
        intros H. reflexivity.
      - (* l = h :: l' *)
        intros H. inversion H; subst.
        apply IHl' in H3.
        unfold ids_are_unique in *. 
        apply Helper.ids_are_unique_recur_true__cons_true.
        + assumption.
        + assumption.
        + rewrite empty_b. reflexivity.
    Qed.

    Theorem ids_are_unique__cons : forall (l : list id) (x : id),
        ids_are_unique (x :: l) = true ->
        ids_are_unique l = true.
    Proof.
      intros l x H.
      apply ids_are_unique__complete.
      apply ids_are_unique__sound in H.
      inversion H; assumption.
    Qed.

(* ----------------------------------------------------------------- *)
(** *** About [set_from_list] *)
(* ----------------------------------------------------------------- *)

    Theorem in_set_from_list__in_list : 
      forall (l : list id) (x : id),
        IdSet.In x (set_from_list l) ->
        List.In x l.
    Proof.
      intros.
      apply Helper.in_set_from_list'__in_list with (s := IdSet.empty).
      intros Hcontra. rewrite empty_iff in Hcontra. assumption.
      assumption.
    Qed.

    Theorem in_list__in_set_from_list :
      forall (l : list id) (x : id),
        List.In x l ->
        IdSet.In x (set_from_list l).
    Proof.
      intros.
      apply Helper.in_list__in_set_from_list'; assumption.
    Qed.  
    
  End Props.

End MList2MSet.


(* ################################################################# *)
(** ** Module [MList2MSetAVL] *)
(* ################################################################# *)

Module MList2MSetAVL (id_UOT : UsualOrderedType).
  Module IdSetAVL := MSetAVL.Make id_UOT.
  Module M := MList2MSet id_UOT IdSetAVL.
End MList2MSetAVL.



