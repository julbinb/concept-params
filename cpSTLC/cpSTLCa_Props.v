(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(* Simply Typed Lambda Calculus with simple Concept Parameters
   :: version a
   Properties

   Properties of STLC are based on
   Sofware Foundations, v.4 
  
   Last Update: Tue, 28 Mar 2017
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

Require Import ConceptParams.BasicPLDefs.Utils.

Require Import ConceptParams.AuxTactics.LibTactics.
Require Import ConceptParams.AuxTactics.BasicTactics.

Require Import ConceptParams.cpSTLC.cpSTLCa_Defs.
Require Import ConceptParams.cpSTLC.cpSTLCa_Interpreter.

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Bool.Bool.

Require Import Coq.omega.Omega.


(* ################################################################# *)
(** ** Syntax *)
(* ################################################################# *)

(* ----------------------------------------------------------------- *)
(** **** Types *)
(* ----------------------------------------------------------------- *)

Lemma beq_ty_refl : forall T1, beq_ty T1 T1 = true.
Proof.
  intros T1. induction T1; (simpl; auto).
  - (* T1 -> T2 *)
    rewrite -> IHT1_1. rewrite -> IHT1_2. reflexivity.
  - (* C # T *)
    rewrite -> IHT1. rewrite <- beq_id_refl. reflexivity.
Qed.

(* beq_ty__eq *)

Lemma beq_ty_true_iff : forall T1 T2,
    beq_ty T1 T2 = true <-> T1 = T2.
Proof.
  intros T1. induction T1;
  (intros T2; induction T2; split; intros H);
    (* in some cases it's just reflexivity *)
    try reflexivity;
    (* in other cases we have impossible equalities as assumptions 
       (such as TNat = TBool) *)
    try solve_by_invert.
  - (* T1_1 -> T1_2 = T2_1 -> T2_2 *)
    simpl in H. apply andb_true_iff in H.
    inversion H as [H1 H2].
    apply IHT1_1 in H1. apply IHT1_2 in H2.
    subst. reflexivity.
  - (* T1_1 -> T1_2 = T2_1 -> T2_2 *)
    inversion H. subst. 
    simpl. apply andb_true_iff.
    split. rewrite (IHT1_1 T2_1); auto. rewrite (IHT1_2 T2_2); auto.
  - (* C1 # T1 = C2 # T2 *)
    simpl in H. apply andb_true_iff in H.
    inversion H as [HC HT].
    rewrite -> beq_id_true_iff in HC. subst.
    apply IHT1 in HT. subst.
    reflexivity.
  - (* C1 # T1 = C2 # T2 *)
    inversion H. subst.
    simpl. apply andb_true_iff.
    split. symmetry. apply beq_id_refl.
    apply beq_ty_refl.
Qed.  

Lemma beq_tyP : forall T1 T2, reflect (T1 = T2) (beq_ty T1 T2).
Proof.
  intros T1 T2. 
  apply iff_reflect. split.
  - (* T1 = T2 -> beq_ty T1 T2 = true *)
    intros H. 
    destruct T1; destruct T2;
      (* in simple cases reflexivity *)
      try reflexivity;
      (* some cases give contra in assumption *)
      try (inversion H).
    + (* T2_1 -> T2_2 = T2_1 -> T2_2 *)
      simpl. apply andb_true_iff. split.
      apply beq_ty_refl. apply beq_ty_refl.
    + (* C # T2 = C # T2 *)
      rename i0 into C. simpl. apply andb_true_iff. split.
      symmetry. apply beq_id_refl. apply beq_ty_refl. 
  - (* beq_ty T1 T2 = true -> T1 = T2 *)
    apply beq_ty_true_iff.
Qed.

(** Decidability of types' equivalence *)
Lemma eq_ty_dec : forall x y : ty, {x = y} + {x <> y}.
Proof.
  intros x y.
  destruct (beq_tyP x y).
  left; assumption.
  right; assumption.
Qed.

(* ################################################################# *)
(** ** Program Well-definedness and Typing *)
(* ################################################################# *)

(* ================================================================= *)
(** *** Checking Concepts *)
(* ================================================================= *)

(* ----------------------------------------------------------------- *)
(** **** Checking Ids' Uniqueness *)
(* ----------------------------------------------------------------- *)

(** First of all we want to prove that [ids_are_unique] is sound, 
    i.e. if it returns true, than there is no duplicates in the list.    

    A bunch of auxiliary lemmas is needed to prove the main theorem.  
*)

(* We need some facts from sets... *)

Module IdSetFacts := MSetFacts.WFacts IdSet.
Module IdSetProps := MSetProperties.WProperties IdSet.

Section IdSetProofs.

Import IdSet.
Import IdSetFacts.
Import IdSetProps.

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

(* ----------------------------------------------------------------- *)

(** We prove the main [ids_are_unique] soundness theorem below. *)

(** And we also have to prove the opposite side, completeness.
    If there is no dups in the list, then ids_are_unique is true. *)

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

(* ----------------------------------------------------------------- *)

(** Here is the main [ids_are_unique] soundness theorem: *)

Theorem ids_are_unique__sound : forall (l : list id),
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
    apply ids_are_unique_recur_true__cons_true.
    + assumption.
    + assumption.
    + reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(** **** Types Validity *)
(* ----------------------------------------------------------------- *)

(** We need to prove that type-validity checks are also
  * sound and complete. *)

(** Soundness. *)

Lemma type_valid_b__sound : forall (cst : cptcontext) (T : ty),
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

(* Print types_valid_b. *)

Lemma types_valid_b__sound : forall (cst : cptcontext) (ts : list ty),
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
    apply IHts' in Hts'. apply type_valid_b__sound in Ht.
    apply Forall_cons; auto.
Qed.

(* ----------------------------------------------------------------- *)

(** Completeness. *)

Lemma type_valid_b__complete : forall (cst : cptcontext) (T : ty),
    type_valid cst T ->
    type_valid_b cst T = true.
Proof.
  intros cst T. generalize dependent cst.
  induction T; intros cst H;
    (* simple cases like TNat *)
    try reflexivity.
  - (* T1 -> T2 *) 
    inversion H; subst. apply IHT1 in H2. apply IHT2 in H3.
    simpl. apply andb_true_iff. auto.
  - (* concept param *)
    inversion H; subst. apply IHT in H3.
    simpl. apply andb_true_iff. split.
    (* concept_defined *)
    unfold concept_defined_b.
    unfold concept_defined in H2.
    destruct (cst i); tauto.
    (* type_valid *) assumption.
Qed.

Lemma types_valid_b__complete : forall (cst : cptcontext) (ts : list ty),
    List.Forall (fun ftype => type_valid cst ftype) ts ->
    types_valid_b cst ts = true.
Proof.
  intros cst ts. unfold types_valid_b.
  induction ts as [| t ts' IHts'];
    intros H.
  - (* ts = nil *)
    reflexivity.
  - (* ts = t :: ts' *)
    inversion H; subst.
    simpl. rewrite -> andb_true_iff. split.
    + apply type_valid_b__complete. assumption.
    + apply IHts'. assumption.
Qed.

(* ----------------------------------------------------------------- *)
(** **** Concept Well-definedness *)
(* ----------------------------------------------------------------- *)

(** And the final steps to prove that [concept_well_defined_b]
    is sound and complete. *)

Theorem concept_well_defined_b__sound : forall (cst : cptcontext) (C : conceptdef),
    concept_welldefined_b cst C = true ->
    concept_welldefined   cst C.
Proof.
  intros cst C. intros H.
  unfold concept_welldefined_b in H. destruct C.
  unfold concept_welldefined.
  destruct (split (map namedecl_to_pair n)).
  rewrite -> andb_true_iff in H. inversion H as [Hid Hty].
  apply ids_are_unique__sound in Hid.
  apply types_valid_b__sound in Hty.
  split; auto.
Qed.

Theorem concept_well_defined_b__complete : forall (cst : cptcontext) (C : conceptdef),
    concept_welldefined   cst C ->
    concept_welldefined_b cst C = true.
Proof.
  intros cst C. intros H.
  unfold concept_welldefined_b.
  unfold concept_welldefined in H.
  destruct C. destruct (split (map namedecl_to_pair n)).
  inversion H as [Hdup Htys].
  rewrite -> andb_true_iff. split.
  apply ids_are_unique__complete in Hdup. assumption.
  apply types_valid_b__complete. assumption.
Qed.

End IdSetProofs.

(* ----------------------------------------------------------------- *)
(** **** Concept Typing *)
(* ----------------------------------------------------------------- *)

(** Now we want to prove that the function [concept_type_check] 
  * is sound and complete. *)

(** Similarly to IdSets, we need some auxiliary 
  * lemmas to connect AVL maps with lists presenting AST. *)

Module IdMapFacts := FMapFacts.WFacts IdMap.
Module IdMapProps := FMapFacts.WProperties IdMap.

Section IdMapProofs.

Import IdMapFacts.
Import IdMapProps.

Lemma map_from_list_not_in__preserves_mapping : 
  forall (pnds : list (prod id ty)) (nm : id) (tp : ty)(m : id_map ty),  
(* JB | cannot figure out how to write [list (id * type)], scoping problems *)
    IdMap.MapsTo nm tp m ->
    ~ List.In nm (map fst pnds) ->
    IdMap.MapsTo nm tp (map_from_list' pnds m).
Proof.
  intros pnds. induction pnds as [| pnd pnds' IHpnds'].
  - (* pnds = nil *)
    intros nm tp m Hmaps Hnin. simpl. assumption. 
  - (* pnds = pnd :: pnds' *)
    intros nm tp m Hmaps Hin.
    unfold map_from_list' in *. simpl. simpl in IHpnds'.
    apply IHpnds'.
    + (* IdMap.MapsTo nm tp (m += pnd) *)    
      destruct pnd as [x v]. destruct (beq_idP nm x). subst.
      assert (contra: List.In x (map fst ((x, v) :: pnds'))) 
        by (simpl; left; reflexivity).
      apply Hin in contra. contradiction.
      apply IdMap.add_2. intros H. symmetry in H. apply n in H. 
      contradiction.
      assumption.
    + (* ~ List.In nm (map fst pnds') *)
      intros H. 
      assert (contra: List.In nm (map fst (pnd :: pnds')))
        by (simpl; right; assumption).
      apply Hin in contra. contradiction.
Qed.

Lemma map_from_list_add_unique__preserves_mapping : 
  forall (pnds : list (prod id ty)) (nm : id) (tp : ty) (m : id_map ty),  
(* JB | cannot figure out how to write [list (id * type)], scoping problems *)
    ~ List.In nm (map fst pnds) ->
    IdMap.MapsTo nm tp (map_from_list' ((nm, tp) :: pnds) m).
Proof. 
  intros pnds nm tp m. intros Hin.
  simpl. apply map_from_list_not_in__preserves_mapping.
  apply IdMap.add_1. reflexivity.
  assumption.
Qed.

(*
IdMap.add_1:
  forall (elt : Type) (m : IdMap.t elt) (x y : IdMap.key) (e : elt),
  x = y -> IdMap.MapsTo y e (IdMap.add x e m)

IdMap.find_1:
  forall (elt : Type) (m : IdMap.t elt) (x : IdMap.key) (e : elt),
  IdMap.MapsTo x e m -> IdMap.find (elt:=elt) x m = Some e
*)

Lemma map_from_list__find_cons__true : forall (nm : id) (tp : ty) 
                                              (nds : list namedecl),
    let pnds := map namedecl_to_pair nds in
    ~ List.In nm (List.map fst pnds) ->
    find_ty nm (map_from_list ((nm, tp) :: pnds)) = Some tp.
Proof.
  intros nm tp nds. intros pnds. intros Hin.
  unfold find_ty, mids_find. 
  apply IdMap.find_1.
  apply map_from_list_add_unique__preserves_mapping. auto.
Qed.

Lemma split_fst__map_fst : forall {A B : Type} (l : list (prod A B)) 
                                  (xs : list A) (ys : list B),
    split l = (xs, ys) -> 
    map fst l = xs.
Proof.
  intros A B l. induction l as [| h l' IHl'].
  - (* l = nil *)
    intros xs ys H. simpl in H. inversion H; subst.
    reflexivity.
  - (* l = h :: l' *)
    intros xs ys H. destruct h eqn:eqh.
    simpl in H. destruct (split l'). simpl. 
    destruct xs as [| x xs']. destruct ys as [| y ys'].
    + inversion H.
    + inversion H.
    + inversion H; subst. apply f_equal.
      apply IHl' with (ys := l0). reflexivity.
Qed.

Lemma map_from_list'__eq_maps : 
  forall (pnds : list (id * ty)%type) (nm : id) (tp : ty) (m m': id_ty_map), 
    IdMap.Equal m' m ->
    IdMap.MapsTo nm tp (map_from_list' pnds m)
    -> 
    IdMap.MapsTo nm tp (map_from_list' pnds m').
Proof.
  intros pnds. induction pnds as [|pnd pnds' IHpnds'].
  - (* pnds = nil *)
    intros nm tp m m' Heq Hmaps. 
    simpl in *. 
    eapply Equal_mapsto_iff; eauto.
  - (* pnds = pnd :: pnds' *)
    intros nm tp m m' Heq Hmaps.
    destruct pnd as [x v]; simpl in *.
    eapply IHpnds'.
    assert (H : IdMap.Equal (mids_add ty x v m') (mids_add ty x v m)).
    { apply add_m; tauto. }
    eassumption.
    assumption.
Qed.

Lemma permute_add__eq_maps :
  forall (nm x : id) (tp v : ty) (m : id_ty_map), 
  x <> nm ->
  IdMap.Equal (mids_add ty x v (mids_add ty nm tp m))
              (mids_add ty nm tp (mids_add ty x v m)).
Proof.
  intros nm x tp v m Hneq.
  apply Equal_mapsto_iff.
  intros k e. split.
    + intros H1.
      apply add_mapsto_iff in H1; propositional.
      subst. apply add_mapsto_iff.
      right.
      pose proof (eq_id_dec nm k) as Hid.
      inversion Hid. subst. simpl in *.
      assert (contra : k = k) by reflexivity.
      apply Hneq in contra.
      contradiction.
      split; auto.
      apply add_mapsto_iff.
      left. split; auto.
      apply add_mapsto_iff in H1; propositional.
      subst. apply add_mapsto_iff.
      left. split; reflexivity.
      apply add_mapsto_iff.
      right. split; auto.
      apply add_mapsto_iff.
      right. split; auto.
    + intros H1.
      apply add_mapsto_iff in H1; propositional.
      subst. apply add_mapsto_iff.
      right.
      pose proof (eq_id_dec x k) as Hid.
      inversion Hid. subst. simpl in *.
      assert (contra : k = k) by reflexivity.
      apply Hneq in contra.
      contradiction.
      split; auto.
      apply add_mapsto_iff.
      left. split; auto.
      apply add_mapsto_iff in H1; propositional.
      subst. apply add_mapsto_iff.
      left. split; reflexivity.
      apply add_mapsto_iff.
      right. split; auto.
      apply add_mapsto_iff.
      right. split; auto.
Qed.

Lemma map_from_list'__ignore_list_add :
  forall (pnds : list (id * ty)%type) (nm : id) (tp : ty) (m : id_ty_map),  
  ~ List.In nm (map fst pnds) ->
  IdMap.MapsTo nm tp (map_from_list' pnds (mids_add ty nm tp m)).
Proof.
  intros pnds. induction pnds as [|pnd pnds' IHpnds'].
  - intros. simpl.
    apply IdMap.add_1. reflexivity.
  - intros nm tp m H.
    destruct pnd as [x v]. simpl. 
    apply map_from_list'__eq_maps with
      (m := (mids_add ty nm tp (mids_add ty x v m))).
    apply permute_add__eq_maps.
    simpl in H. unfold not. intros contra.
    eapply or_introl in contra.
    apply H in contra. contradiction.
    apply IHpnds'.
    unfold not in *. intros contra.
    assert (H1 : List.In nm (map fst ((x, v) :: pnds')))
      by (simpl; right;  assumption).
    tauto.
Qed.

Lemma map_from_list'__ignore_list' :
  forall (pnds : list (id * ty)%type) (nm : id) (tp : ty) (m : id_ty_map),  
  ~ List.In nm (map fst pnds) ->
  IdMap.MapsTo nm tp m ->
  IdMap.MapsTo nm tp (map_from_list' pnds m).
Proof.
  intros pnds. induction pnds as [|pnd pnds' IHpnds'].
  - intros. simpl. assumption.
  - intros nm tp m Hin Hmaps.
    destruct pnd as [x v]. simpl. 
    apply IHpnds'.
    simpl in Hin. unfold not in *.
    intros H.
    assert (contra : x = nm \/ List.In nm (map fst pnds'))
      by (right; assumption).
    tauto.
    apply add_mapsto_iff.
    pose proof (eq_id_dec x nm) as Heq. inversion Heq.
    unfold not in *. simpl in *.
    assert (contra : x = nm \/ List.In nm (map fst pnds'))
      by (left; assumption).
    tauto.
    right. split; auto.
Qed.

Lemma map_from_list'__ignore_list :
  forall (pnds : list (id * ty)%type) (nm : id) (tp : ty) (m : id_ty_map),  
  ~ List.In nm (map fst pnds) ->
  IdMap.MapsTo nm tp (map_from_list' pnds m) ->
  IdMap.MapsTo nm tp m.
Proof.
  intros pnds. induction pnds as [|pnd pnds' IHpnds'].
  - intros. simpl in *. assumption.
  - intros nm tp m Hin Hmaps.
    destruct pnd as [x v]. simpl in *. 
    assert (Hin' : ~ List.In nm (map fst pnds')).
    { unfold not in *. intros contra.
      apply Hin. tauto. }  
    specialize (IHpnds' nm tp (mids_add ty x v m) Hin' Hmaps).
    apply add_mapsto_iff in IHpnds'.
    inversion IHpnds'.
    tauto.
    tauto.
Qed.

Lemma map_from_list__any_map : 
  forall (pnds : list (id * ty)%type) (nm : id) (tp : ty) (m m' : id_ty_map),  
    List.In nm (map fst pnds) ->
    (*List.NoDup (map fst pnds)  -> *)
    IdMap.MapsTo nm tp (map_from_list' pnds m) ->
    IdMap.MapsTo nm tp (map_from_list' pnds m').
Proof.
  intros pnds. induction pnds as [|pnd pnds' IHpnds'].
  - (* pnds = nil *)
    intros nm tp m m' Hin (* Hdup *) Hmaps. 
    simpl in Hin. contradiction.
  - (* pnds = pnd :: pnds' *)
    intros nm tp m m' Hin (* Hdup *) Hmaps.
    simpl. simpl in Hmaps.
    destruct pnd as [x v].       
    pose proof (in_dec eq_id_dec nm (map fst pnds')) as Hindec.
    inversion Hindec as [Hinnm | Hinnm].
    + eapply IHpnds'.
      assumption.
      eassumption.
    + simpl in Hin. inversion Hin.
      { subst.
        pose proof (map_from_list'__ignore_list 
                      pnds' nm tp (mids_add ty nm v m) Hinnm Hmaps) as Hnm.
        apply add_mapsto_iff in Hnm; propositional.
        subst.
        apply map_from_list'__ignore_list_add.
        assumption. } 
      tauto.
Qed.

Lemma elem_in_map'__elem_in_list' :
  forall (pnds : list (id * ty)%type) (nm : id) (tp : ty) (m : id_ty_map),
    IdMap.MapsTo nm tp
                 (map_from_list' pnds m) ->
    ~ (IdMap.In nm m) ->
    List.In nm (map fst pnds).
Proof.
  intros pnds. 
  induction pnds as [| pnd pnds' IHpnds'].
  - intros. simpl in H. 
    apply IdMap.find_1 in H.
    assert (Hfind : IdMap.find (elt:=ty) nm m <> None).
    equality.    
    rewrite <- in_find_iff in Hfind.
    apply H0 in Hfind. contradiction.
  - intros. destruct pnd as [x v].
    simpl in *.
    destruct (beq_idP nm x).
    + equality.
    + right.
      apply IHpnds' with (tp := tp) (m := (mids_add ty x v m)).
      assumption.
      unfold "~". intro Hin.
(*
add_in_iff:
  forall (elt : Type) (m : IdMap.t elt) (x y : IdMap.key) (e : elt),
  IdMap.In (elt:=elt) y (IdMap.add x e m) <-> x = y \/ IdMap.In (elt:=elt) y m
*)      
      rewrite add_in_iff in Hin.
      inversion Hin. equality.
      apply H0 in H1.
      assumption.
Qed.

Lemma elem_in_map'__elem_in_list :
  forall (pnds : list (id * ty)%type) (nm : id) (tp : ty),
    IdMap.MapsTo nm tp
                 (map_from_list' pnds (mids_empty ty)) ->
    List.In nm (map fst pnds).
Proof.
  intros pnds nm tp Hmaps.
  apply elem_in_map'__elem_in_list' with (tp := tp) (m := (mids_empty ty)).
  assumption.
  unfold not. 
  intros contra. rewrite empty_in_iff in contra.
  assumption.
Qed.

Lemma map_from_list'_preserves_eq :
  forall (pnds : list (id * ty)%type) (m m' : id_ty_map),
    IdMap.Equal m m' ->
    IdMap.Equal (map_from_list' pnds m) (map_from_list' pnds m').
Proof.
  intros pnds. induction pnds as [|pnd pnds' IHpnds'].
  - (* pnds = nil *)
    intros m m' Heq. simpl.
    assumption.
  - (* pnds = pnd :: pnds' *)
    intros m m' Heq. destruct pnd as [x v].
    simpl.
    apply IHpnds'.
    apply F.add_m; tauto.
Qed.

Lemma map_from_list_cons_cardinal' :
  forall (pnds : list (id * ty)%type) (nm : id) (tp : ty) (m : id_ty_map),
    ~ List.In nm (map fst pnds) ->
    ~ IdMap.In nm m ->
    IdMap.cardinal (elt:=ty) (map_from_list' ((nm, tp) :: pnds) m)
    = S (IdMap.cardinal (elt:=ty) (map_from_list' pnds m)).
Proof.
  intros pnds. induction pnds as [|pnd pnds' IHpnds'].
  - (* pnds = nil *)
    intros nm tp m Hin Hmap. simpl.
    rewrite <- cardinal_2 with (m' := (mids_add ty nm tp m))
                              (x := nm) (e := tp).
    reflexivity.
    assumption.
    unfold Add. intros y.
    reflexivity.
  - (* pnds = pnd :: pnds' *)
    intros nm tp m Hin Hmap. destruct pnd as [x v].
    simpl in *.
    assert (Heq : IdMap.Equal 
                    (map_from_list' pnds' (mids_add ty x v (mids_add ty nm tp m)))
                    (map_from_list' pnds' (mids_add ty nm tp (mids_add ty x v m)))).
    { apply map_from_list'_preserves_eq.
      apply permute_add__eq_maps.
      tauto. }
    rewrite Heq.
    apply IHpnds'.
    tauto. 
    unfold not. intros contra.
    rewrite F.add_in_iff in contra.
    inversion contra; tauto.
Qed.

Lemma map_from_list_cons_cardinal :
  forall (pnds : list (id * ty)%type) (nm : id) (tp : ty),
    ~ List.In nm (map fst pnds) ->
    IdMap.cardinal (elt:=ty) (map_from_list ((nm, tp) :: pnds))
    = S (IdMap.cardinal (elt:=ty) (map_from_list pnds)).
Proof.
  intros pnds. induction pnds as [|pnd pnds' IHpnds'].
  - (* pnds = nil *)
    intros nm tp Hin. 
    reflexivity.
  - (* pnds = pnd :: pnds' *)
    intros nm tp Hin. destruct pnd as [x v].
    assert (Heq : 
    IdMap.cardinal (elt:=ty) (map_from_list ((nm, tp) :: (x, v) :: pnds'))
    = S (IdMap.cardinal (elt:=ty) (map_from_list ((x, v) :: pnds')))).
    { change (IdMap.cardinal (elt:=ty) 
                (map_from_list' ((nm, tp) :: (x, v) :: pnds') (mids_empty ty)) 
              =
              S (IdMap.cardinal (elt:=ty) (
                   map_from_list' ((x, v) :: pnds') (mids_empty ty)))).
      apply map_from_list_cons_cardinal'.
      assumption.
      unfold not. intros contra.
      rewrite F.empty_in_iff in contra. 
      tauto. }
    rewrite Heq.
    unfold map_from_list in *. reflexivity.
Qed.

Lemma concept_welldefined_b__cons :
  forall cst Cnm nd nds,
    concept_welldefined_b cst (cpt_def Cnm (nd :: nds)) = true ->
    concept_welldefined_b cst (cpt_def Cnm nds) = true.
Proof.
  intros cst Cnm nd nds H.
  simpl in *.
  destruct (namedecl_to_pair nd) as [nm tp].
  destruct (split (map namedecl_to_pair nds)) as [fnames' ftypes'].
  apply andb_true_iff.
  apply andb_true_iff in H.
  propositional.
  apply ids_are_unique__sound in H0. 
    inversion H0. apply ids_are_unique__complete in H4.
    assumption.
  simpl in H1.  
    apply andb_true_iff in H1; propositional.
Qed.

(* ----------------------------------------------------------------- *)

Lemma in_list__in_map_from_list' :
  forall (pnds : list (id * ty)%type) (nm : id) (tp : ty) (m : id_ty_map),
    NoDup (map fst pnds) ->
    List.In (nm, tp) pnds ->
    IdMap.MapsTo nm tp (map_from_list' pnds m). 
Proof.
  intros pnds. induction pnds as [|pnd pnds' IHpnds'].
  - (* pnds = nil *)
    intros nm tp m Hdup Hin. simpl in *.
    contradiction.
  - (* pnds = pnd :: pnds' *)
    intros nm tp m Hdup Hin. destruct pnd as [x v].
    simpl.
    inversion Hdup.
    inversion Hin.
    inversion H3. subst.
      apply map_from_list'__ignore_list_add.
      unfold not. intros contra.
      tauto.
    apply IHpnds'; tauto.
Qed.

Lemma in_list__in_map_from_list :
  forall (pnds : list (id * ty)%type) (nm : id) (tp : ty),
    NoDup (map fst pnds) ->
    List.In (nm, tp) pnds ->
    IdMap.MapsTo nm tp (map_from_list pnds). 
Proof.
  intros.
  change (IdMap.MapsTo nm tp (map_from_list' pnds (mids_empty ty))).
  apply in_list__in_map_from_list'; assumption.
Qed.


Lemma concept_welldefined__cons : 
  forall cst Cnm nd nds,
    concept_welldefined cst (cpt_def Cnm (nd :: nds)) ->
    concept_welldefined cst (cpt_def Cnm nds).
Proof.
  intros cst Cnm nd nds H.
  simpl in *.
  destruct (namedecl_to_pair nd) as [nm tp].
  destruct (split (map namedecl_to_pair nds)) as [fnames' ftypes'].
  propositional.
  inversion H0. assumption.
  simpl in H1.  
  inversion H1; propositional.
Qed.

Lemma list_elems_in_map__remove_unused :
  forall nds f CT CT',
    Forall
      (fun nmdecl : namedecl =>
         match nmdecl with
         | nm_decl f T => find_ty f CT = Some T
         end) nds ->
    ~ In f (map fst (map namedecl_to_pair nds)) ->
    CT' = IdMap.remove (elt:=ty) f CT ->
    Forall
      (fun nmdecl : namedecl =>
         match nmdecl with
         | nm_decl f0 T0 => find_ty f0 CT' = Some T0
         end) nds.
Proof.
  intros nds. induction nds as [| nd nds' IHnds' ].
  - (* nds = nil *)
    intros f CT CT' Htypes Hin Heq.
    constructor.
  - (* nds = nd :: nds' *)
    intros f CT CT' Htypes Hin Heq.
    destruct nd as [nm tp]. simpl in *.
    inversion Htypes; clear Htypes; subst.
    apply Forall_cons.
    + pose proof (eq_id_dec nm f).
      inversion H.
      { eapply or_introl in H0.
        eapply Hin in H0. contradiction. }
      clear H.
      apply F.find_mapsto_iff.
      apply F.remove_mapsto_iff.
      split. equality.
      apply F.find_mapsto_iff. assumption.
    + apply IHnds' with (f := f) (CT := CT).
      assumption.
      unfold not. intros contra.
      eapply or_intror in contra.
      apply Hin in contra. contradiction.
      reflexivity.
Qed.

Lemma nd_in_map__nd_in_list :
  forall nds nm tp CT,
    Forall
      (fun nmdecl : namedecl =>
         match nmdecl with
         | nm_decl f T => find_ty f CT = Some T
         end) 
      nds ->
    NoDup (map fst (map namedecl_to_pair nds)) ->
    length nds = IdMap.cardinal (elt:=ty) CT ->
    IdMap.MapsTo nm tp CT ->
    List.In (nm_decl nm tp) nds.    
Proof.
  intros nds. induction nds as [| nd nds' IHnds' ].
  - (* nds = nil *)
    intros nm tp CT Htypes Hdup Hcard Hmaps. simpl in *.
    symmetry in Hcard. apply cardinal_Empty in Hcard. 
    unfold IdMap.Empty in *.
    unfold IdMap.AvlProofs.Raw.Proofs.Empty in *.
    apply Hcard in Hmaps; contradiction.
  - (* nds = nd :: nds' *)
    intros nm tp CT Htypes Hdup Hcard Hmaps.
    inversion Htypes; subst; simpl in *. clear Htypes.
    destruct nd as [f T].
    simpl in Hdup. inversion Hdup. subst.
    assert (Hfind := Hmaps).
    rewrite (F.find_mapsto_iff CT nm tp) in Hfind.
    unfold find_ty, mids_find in H1.
    pose proof (eq_id_dec f nm).
    inversion H; clear H.
    + subst.
      rewrite -> H1 in Hfind. inversion Hfind.
      left; trivial.
    + right.
      (* To apply IH, we need smaller map *)
      remember (IdMap.remove f CT) as CT'.
      apply IHnds' with (CT := CT').
      subst CT'.
      apply list_elems_in_map__remove_unused with (f := f) (CT := CT); trivial.
      assumption.
      assert (Hnotin : ~ IdMap.In f CT').
      { subst. intros contra.
        apply F.remove_in_iff in contra.
        inversion contra; tauto. }
      assert (Hcard' : IdMap.cardinal (elt:=ty) CT 
                       = S (IdMap.cardinal (elt:=ty) CT')).
      { apply cardinal_2 with (x := f) (e := T).
        assumption. unfold Add. subst.
        intros y. 
        pose proof (eq_id_dec f y) as Hyf. inversion Hyf.
        subst.
        rewrite H1. 
        rewrite (F.add_eq_o _ _ (eq_refl y)). reflexivity.
        rewrite (F.add_neq_o _ _ H).
        symmetry. apply F.remove_neq_o. assumption. }
      rewrite <- Hcard in Hcard'.
      inversion Hcard'. reflexivity.
      subst. apply F.remove_neq_mapsto_iff. assumption. assumption.
Qed.      

Lemma concept_has_type_iso : 
  forall (cst : cptcontext) (C : conceptdef) (CT CT' : id_ty_map),  
    concept_has_type cst C (CTdef CT) ->
    concept_has_type cst C (CTdef CT') ->
    IdMap.Equal CT CT'.
Proof.
  intros cst C. 
  destruct C as [Cnm nmtps].
  induction nmtps as [| nmtp nmtps' IHnmtps' ];
    intros CT CT' HCT HCT';
    unfold concept_has_type in *; propositional.
  - (* nil *)
    simpl in *. symmetry in H4, H5.
    apply cardinal_Empty in H4. apply cardinal_Empty in H5.
    unfold IdMap.Empty in *.
    unfold IdMap.AvlProofs.Raw.Proofs.Empty in H4, H5.
    apply F.Equal_mapsto_iff.
    intros k e. split; intros contra.
    + unfold IdMap.MapsTo in contra. apply H4 in contra. contradiction.
    + unfold IdMap.MapsTo in contra. apply H5 in contra. contradiction.
  - (* nmtps = nmtp :: nmtps' *)

    unfold concept_welldefined in H.
    destruct (split (map namedecl_to_pair (nmtp :: nmtps'))) 
      as [fnames ftypes] eqn:Heq.
    propositional.
    apply split_fst__map_fst in Heq. subst.

    apply F.Equal_mapsto_iff.
    intros k e. split; intros Hmaps.
    
    assert (Hin : List.In (nm_decl k e) (nmtp :: nmtps')).
    apply nd_in_map__nd_in_list with (CT := CT).
    assumption. assumption. assumption. assumption.
    rewrite Forall_forall in H0.
    specialize (H0 (nm_decl k e) Hin).
    inversion H0.
    apply F.find_mapsto_iff. assumption.

    assert (Hin : List.In (nm_decl k e) (nmtp :: nmtps')).
    apply nd_in_map__nd_in_list with (CT := CT').
    assumption. assumption. assumption. assumption.
    rewrite Forall_forall in H3.
    specialize (H3 (nm_decl k e) Hin).
    inversion H3.
    apply F.find_mapsto_iff. assumption.
Qed.    

(* ----------------------------------------------------------------- *)

(** Here is the main [concept_type_check] soundness theorem. *)

Theorem concept_type_check__sound : 
  forall (cst : cptcontext) (C : conceptdef) (CT : cty),  
    concept_type_check cst C = Some CT ->
    concept_has_type cst C CT.
Proof.
  intros cst C CT.
  unfold concept_type_check. 
  destruct (concept_welldefined_b cst C) eqn: HCdef; 
    [ idtac | 
      (* the second goal goes away: None = Some _ *)
      simplify; try solve_by_invert ].  
  (* C welldefined_b -> concept_has_type *)
  destruct C as [Cnm nds]. 
  intros H. inversion H; subst. clear H.
  pose proof (concept_well_defined_b__sound cst _ HCdef) as Hsound.
  unfold concept_has_type. split.
  (* concept_welldefined *) 
  assumption.
  (* all types are presented and valid,
   * and length is correct *)
  unfold concept_welldefined (*, concept_welldefined_b *) in *.
  split. 
  - (* forall find_ty*)
    induction nds as [| d nds' IHnds']. 
    apply Forall_nil.
    (* Forall_cons *)
    destruct d; simpl in HCdef.
    remember (map namedecl_to_pair nds') as pnds'.
    destruct (split pnds') as [nms tps] eqn:eqpnds'.
    rewrite andb_true_iff in HCdef. inversion HCdef as [Huniq Hvalid].
    clear HCdef.
    apply ids_are_unique__sound in Huniq. 
    apply Forall_cons(*; destruct d; simpl in HCdef*).
    + (* head *)
      simpl. apply map_from_list__find_cons__true.
      (* ~ List.In i (map fst (map namedecl_to_pair nds')) *)
      inversion Huniq; subst.
      replace (map fst (map namedecl_to_pair nds')) with nms.
      assumption. 
      apply split_fst__map_fst in eqpnds'. auto.
(*
Forall_impl:
  forall (A : Type) (P Q : A -> Prop),
  (forall a : A, P a -> Q a) -> forall l : list A, Forall P l -> Forall Q l
 *)
    + (* tail *)
      subst.
      apply Forall_impl with (P := fun nmdecl : namedecl =>
              match nmdecl with
              | nm_decl f T =>
                  find_ty f (map_from_list (map namedecl_to_pair nds')) = Some T
              end).
      intros [f T] H.
      simpl.
      apply IdMap.find_2 in H.
      apply IdMap.find_1.
      change (IdMap.MapsTo f T 
             (map_from_list' ((i, t) :: map namedecl_to_pair nds') 
                             (mids_empty ty))).
      change (IdMap.MapsTo f T 
             (map_from_list' (map namedecl_to_pair nds') 
                             (mids_empty ty))) in H.
      simpl.
      apply map_from_list__any_map with (m := (mids_empty ty)).     
      apply elem_in_map'__elem_in_list with (tp := T).
      assumption. assumption.
      (* forall implication *)
      inversion Huniq; subst; simpl in *.
      apply IHnds'.
      unfold concept_welldefined_b.
      destruct (split (map namedecl_to_pair nds')) as [fnames ftypes].
      inversion eqpnds'. subst.
      apply andb_true_iff; split.
      apply ids_are_unique__complete. assumption.
      apply andb_true_iff in Hvalid. inversion Hvalid; auto.
      split; auto.
      destruct (split (map namedecl_to_pair nds')) as [fnames' ftypes'].
      inversion Hsound.
      inversion H0. inversion eqpnds'. subst.
      assumption.
  - (* length *)
    induction nds as [| d nds' IHnds']. 
    reflexivity.
    destruct d as [nm tp].
    simpl.
    rewrite map_from_list_cons_cardinal.
    apply f_equal.
    apply IHnds'.
    apply concept_welldefined_b__cons with (nd := nm_decl nm tp); assumption.
    simpl in Hsound.
    destruct (split (map namedecl_to_pair nds')) as [fnames ftypes].
    propositional.
    inversion H; tauto.
    inversion H0; tauto.
    (* ~ List.In *)
    simpl in Hsound.
    destruct (split (map namedecl_to_pair nds')) as [fnames ftypes] eqn:Heq.
    propositional.
    inversion H0. apply split_fst__map_fst in Heq. subst.
    tauto.
Qed.

(** Here is the main [concept_type_check] completeness theorem. *)

Theorem concept_type_check__complete : 
  forall (cst : cptcontext) (C : conceptdef) (CT CT' : id_ty_map),  
    concept_has_type cst C (CTdef CT) ->
    concept_type_check cst C = Some (CTdef CT') ->
    IdMap.Equal CT CT'.
Proof.
  intros cst C CT CT' Hhas Hcheck.
  apply concept_type_check__sound in Hcheck.
  apply concept_has_type_iso with (cst := cst) (C := C);
    assumption.
(*
  (* simplify [has] hypothesis *)
  destruct C as [Cnm nds].
  unfold concept_has_type in Hhas.
  inversion Hhas as [Hwell Hbody]. clear Hhas.
  inversion Hbody as [Htys Hlen]. clear Hbody.
  (* simplify [check] hypothesis *)
  unfold concept_type_check in Hcheck.
  pose proof (concept_well_defined_b__complete _ _ Hwell) as Hwell'.
  rewrite Hwell' in Hcheck.
  inversion Hcheck as [Hcheck']. clear Hcheck. 
  (* Main goal: map_from_list (map namedecl_to_pair nds) = nmtps *)

  unfold concept_welldefined in Hwell.
  destruct (split (map namedecl_to_pair nds)) as [fnames ftypes] eqn:Hnds.
  assert (Hnds' := Hnds).
  apply split_fst__map_fst in Hnds. subst.
  inversion Hwell as [Hdup Htys'].

  apply F.Equal_mapsto_iff.
  intros k e.
  repeat rewrite -> F.find_mapsto_iff.
  split.
  + intros H.
    unfold concept_welldefined_b in Hwell'.
    rewrite <- F.find_mapsto_iff.
    apply in_list__in_map_from_list.
    assumption.
 *)   
Qed.

End IdMapProofs.


(* ================================================================= *)
(** *** Checking Types *)
(* ================================================================= *)

Theorem type_check__sound :
  forall (cst : cptcontext) (mst : mdlcontext)
         (Gamma : context) (t : tm) (T : ty),
    type_check cst mst Gamma t = Some T ->
    has_type cst mst Gamma t T.
Proof.
  intros cst mst Gamma t.
  generalize dependent Gamma.
  generalize dependent mst. generalize dependent cst. 
  (* Induction on term t *)
  induction t; intros cst mst Gamma T H; 
    simpl in *;
    unfold context_get_type, option_handle, 
      context_get_concept in *;
    repeat 
      match goal with
      | [H : context[match ?x with _ => _ end] |- _] => cases x; subst; simpl
      | [H : ?C _ = ?C _ |- _] => inversion H; subst; clear H; auto
      | [H : beq_ty _ _ = true |- _] => apply beq_ty_true_iff in H; subst
      | [H : beq_id _ _ = true |- _] => apply beq_id_true_iff in H; subst
      end;
    try solve_by_invert;
    repeat 
      match goal with
      | [IH : context[type_check _ _ _ ?t = Some _ -> _],
              H : type_check _ _ _ ?t = Some _
         |- has_type _ _ _ _ _ ] => specialize (IH _ _ _ _ H)
      end.
  (* App *)
  econstructor; eassumption.
  (*eapply T_App; eassumption.*)
  (* MApp *)
  econstructor; eassumption.
  (* CAbs *)
  destruct c as [Cbody].
  apply T_CAbs with (Cbody := Cbody). assumption.
  assumption.
  (* CInvk for c#C *)
  apply T_CInvk with (C := i1). eassumption.
  unfold concept_fun_member. rewrite Eq0. assumption.
  (* CInvk for M *)
  apply T_MInvk with (C := i1) (Mbody := i2).
  assumption. assumption.
  unfold concept_fun_member. rewrite Eq1. assumption.
  (* tif *)
  constructor; assumption.
  (* tlet *)
  econstructor; eassumption.
Qed.


Theorem type_check__complete :
  forall (cst : cptcontext) (mst : mdlcontext)
         (Gamma : context) (t : tm) (T : ty),
    has_type cst mst Gamma t T ->
    type_check cst mst Gamma t = Some T.
Proof.
  intros cst mst Gamma t T Hty.
  induction Hty; simpl;
    unfold context_get_type, option_handle, concept_fun_member in *;
    repeat 
      match goal with
      | [H : ?x = _ |- context[?x] ] => rewrite H; try trivial
(*           |[H : _ = ?x |- context[?x] ] => rewrite <- H; try auto  *)
      | [ |- context[beq_ty ?x ?x]] => 
        rewrite beq_ty_refl; simpl; try equality
      | [ |- context[beq_id ?x ?x]] => 
        rewrite <- beq_id_refl; simpl; try equality
      | [H : context[match ?x with _ => _ end] |- _] => 
        cases x; subst; simpl                
      end;
    tauto.
Qed.




(*
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