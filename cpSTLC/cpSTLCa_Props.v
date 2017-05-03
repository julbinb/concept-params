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

Require Import ConceptParams.BasicPLDefs.Identifier.
Require Import ConceptParams.BasicPLDefs.Maps.
Require Import ConceptParams.BasicPLDefs.Relations.

Require Import ConceptParams.BasicPLDefs.Utils.

Require Import ConceptParams.AuxTactics.LibTactics.
Require Import ConceptParams.AuxTactics.BasicTactics.

Require Import ConceptParams.cpSTLC.cpSTLCa_Defs.
Require Import ConceptParams.cpSTLC.cpSTLCa_Interpreter.

Require Import ConceptParams.GenericModuleLib.MIntrfs1.

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
*)

Theorem ids_are_unique__sound : forall (l : list id),
    IdLS.ids_are_unique l = true -> NoDup l.
Proof.
  apply IdLS.Props.ids_are_unique__sound.
Qed.

(** And we also have to prove the opposite side, completeness.
    If there are no dups in the list, then [ids_are_unique] gives true. *)

Theorem ids_are_unique__complete : forall (l : list id),
    NoDup l -> IdLS.ids_are_unique l = true.
Proof.
  apply IdLS.Props.ids_are_unique__complete.
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
(*
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
*)

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

(*
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
*)


(* !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *)

Module ty_DataOkProp <: DataOkProp ty_Data ty_DataOkDef ty_DataOkInterp.
  Definition is_ok_b__sound := type_valid_b__sound.
  Definition is_ok_b__complete := type_valid_b__complete.
End ty_DataOkProp.

Module conceptProps := MIntrfs1Props 
                         ty_Intrfs1Base 
                         ty_DataOkDef ty_DataOkInterp ty_DataOkProp.

(*
Lemma types_valid_b__sound' : forall (cst : cptcontext) (ts : list ty),
    types_valid_b' cst ts = true ->
    types_valid' cst ts.
Proof.
  apply concept.types_ok_b__sound.
Qed.

Lemma types_valid_b__complete' : forall (cst : cptcontext) (ts : list ty),
    types_valid'   cst ts ->
    types_valid_b' cst ts = true.
Proof.
  apply conceptProps.types_ok_b__complete.
Qed.
*)

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
  destruct C as [nm body]. simpl in *. 
  apply conceptProps.intrfs_ok_b__sound. assumption.
Qed.

Theorem concept_well_defined_b__complete : forall (cst : cptcontext) (C : conceptdef),
    concept_welldefined   cst C ->
    concept_welldefined_b cst C = true.
Proof.
  intros cst C. intros H.
  destruct C as [nm body]. simpl in *.
  apply conceptProps.intrfs_ok_b__complete. assumption.
Qed.


(* !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *)





(*

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

*)

(* ----------------------------------------------------------------- *)
(** **** Concept Typing *)
(* ----------------------------------------------------------------- *)

(** Now we want to prove that the function [concept_type_check] 
  * is sound and complete. *)

(** Similarly to IdSets, we need some auxiliary 
  * lemmas to connect AVL maps with lists presenting AST. *)

(*

*)

Module IdLPMProps := IdLPM.Props.
Module IdMapFacts := FMapFacts.WFacts IdLPM.IdMap.
Module IdMapProps := FMapFacts.WProperties IdLPM.IdMap.

Section IdMapProofs.
  Import IdLPMProps.
  Import IdMapFacts.
  Import IdMapProps.

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

(* ----------------------------------------------------------------- *)

Lemma concept_welldefined_b__cons :
  forall (cst : cptcontext) (Cnm : id) (nd : namedecl) (nds : list namedecl),
    concept_welldefined_b cst (cpt_def Cnm (nd :: nds)) = true ->
    concept_welldefined_b cst (cpt_def Cnm nds) = true.
Proof.
  intros cst Cnm nd nds H.
  simpl in *. unfold conceptInterp.intrfs_ok_b in *.
  destruct (namedecl_to_pair nd) as [nm tp]. simpl in *.
  destruct (split (map namedecl_to_pair nds)) as [fnames' ftypes'] eqn:Heq.
  rewrite Heq at 1. rewrite Heq in H at 1.
  apply andb_true_iff.
  apply andb_true_iff in H.
  propositional.
  apply ids_are_unique__sound in H0. 
    inversion H0. apply ids_are_unique__complete in H4.
    assumption.
  simpl in H1.  
    apply andb_true_iff in H1; propositional.
Qed.

Lemma concept_welldefined__cons : 
  forall (cst : cptcontext) (Cnm : id) (nd : namedecl) (nds : list namedecl),
    concept_welldefined cst (cpt_def Cnm (nd :: nds)) ->
    concept_welldefined cst (cpt_def Cnm nds).
Proof.
  intros cst Cnm nd nds. simpl.
  unfold conceptDefs.intrfs_ok.
  simpl in *. 
  destruct (split (map namedecl_to_pair nds)) as [fnames' ftypes'] eqn:Heq.
  rewrite Heq at 1. 
  destruct (namedecl_to_pair nd) as [nm tp]. simpl.  
  rewrite Heq at 1.
  intros H.
  propositional.
  inversion H0. assumption.  
  inversion H1; propositional.
Qed.

(* ----------------------------------------------------------------- *)

(** As our IdLPM framework works with list of pairs, and
    our syntax tree contains [namedecl] instead of pairs,
    we need a way to convert [namedecl] to pair. *)

Definition namedecl_prop (P : id -> ty -> Prop) :=
  fun nmdecl : namedecl => 
    match nmdecl with 
    | nm_decl f T => P f T 
    end. 
Definition namedecl_pair_prop (P : id -> ty -> Prop) :=
  fun pnd : id * ty => 
    match pnd with 
    | (f, T) => P f T 
    end.

Lemma namedecl_prop__pair : 
  forall (P : id -> ty -> Prop) (nd : namedecl),
    namedecl_prop P nd ->
    namedecl_pair_prop P (namedecl_to_pair nd).
Proof.
  intros P nd H. destruct nd as [f T].
  simpl. assumption.
Qed.
Lemma pair_prop__namedecl : 
  forall (P : id -> ty -> Prop) (nd : namedecl),
    namedecl_pair_prop P (namedecl_to_pair nd) ->
    namedecl_prop P nd.
Proof.
  intros P nd H. destruct nd as [f T].
  simpl in *. assumption.
Qed.

Lemma forall_namedecl__forall_pair : 
  forall (P : id -> ty -> Prop) (nds : list namedecl),
    Forall (namedecl_prop P) nds ->
    Forall (namedecl_pair_prop P) (map namedecl_to_pair nds).
Proof.
  intros P nds. induction nds as [| nd nds' IHnds'].
  - intros _. simpl. constructor.
  - intros H. inversion H; subst. 
    simpl. constructor.
    apply namedecl_prop__pair; assumption.
    apply IHnds'; assumption.
Qed.
Lemma forall_pair__forall_namedecl : 
  forall (P : id -> ty -> Prop) (nds : list namedecl),
    Forall (namedecl_pair_prop P) (map namedecl_to_pair nds) ->
    Forall (namedecl_prop P) nds.
Proof.
  intros P nds. induction nds as [| nd nds' IHnds'].
  - intros _. simpl. constructor.
  - intros H. inversion H; subst. 
    simpl. constructor.
    apply pair_prop__namedecl; assumption.
    apply IHnds'; assumption.
Qed.

Lemma in_pair__in_namedecl : 
  forall (nds : list namedecl) (nd : namedecl),
    In (namedecl_to_pair nd) (map namedecl_to_pair nds) ->
    In nd nds.
Proof.
  intros nds. induction nds as [| nd' nds' IHnds'].
  - intros nd H. inversion H. 
  - intros nd H. 
    simpl. simpl in H. 
    inversion H as [H' | H'].
    + left. unfold namedecl_to_pair in H'. 
      cases nd'. cases nd. subst. 
      inversion H'. subst. reflexivity.
    + right.    
      auto.
Qed.

(* ----------------------------------------------------------------- *)

Lemma concept_has_type_iso : 
  forall (cst : cptcontext) (C : conceptdef) (CT CT' : id_ty_map),  
    concept_has_type cst C (CTdef CT) ->
    concept_has_type cst C (CTdef CT') ->
    IdLPM.IdMap.Equal CT CT'.
Proof.
  intros cst C. 
  destruct C as [Cnm nmtps]. 
  unfold concept_has_type.
  unfold concept_welldefined, conceptDefs.intrfs_ok.
  destruct (split (map namedecl_to_pair nmtps)) as [nms tps] eqn:Heq.
  intros CT CT'.
  rewrite Heq at 1. rewrite Heq at 1.
  intros HCT HCT'.
  propositional.
  apply Equal_mapsto_iff.
  remember (map namedecl_to_pair nmtps) as pnds.
  assert (Hdup : NoDup (IdLPM.get_ids pnds)).
  { apply split_fst__map_fst in Heq. subst.
    assumption. }
  intros k T. split; intros Hmaps.
  - (* CT -> CT'*)    
    pose proof (elem_in_map_eq_length__elem_in_list
                  ty pnds k T CT H Hdup H5 Hmaps) as Hin.
    assert (HCT' := H1).
    rewrite Forall_forall in HCT'.
    specialize (HCT' (k, T) Hin). simpl in HCT'.
    apply IdMapProps.F.find_mapsto_iff.
    assumption.
  - (* CT' -> CT *)
    pose proof (elem_in_map_eq_length__elem_in_list
                  ty pnds k T CT' H1 Hdup H7 Hmaps) as Hin.
    assert (HCT := H).
    rewrite Forall_forall in HCT.
    specialize (HCT (k, T) Hin). simpl in HCT.
    apply IdMapProps.F.find_mapsto_iff.
    assumption.
Qed.
(*
  (* unfold Equal *)
  unfold IdLPM.IdMap.Equal.
  intros y.
  remember (map namedecl_to_pair nmtps) as pnds.
  destruct (IdLPM.IdMap.find y CT) as [T|] eqn:Hfind.
  - (* y in C *)
    assert (Hmaps := Hfind).
    rewrite <- IdMapProps.F.find_mapsto_iff in Hmaps.
    assert (Hdup : NoDup (IdLPM.get_ids pnds)).
    { apply split_fst__map_fst in Heq. subst.
      assumption. }
    pose proof (elem_in_map_eq_length__elem_in_list
                  ty pnds y T CT H Hdup H5 Hmaps) as Hin.
    assert (HCT' := H1).
    rewrite Forall_forall in HCT'.
    specialize (HCT' (y, T) Hin). simpl in HCT'.
    rewrite <- HCT'. reflexivity.
  - (* y not in C *)
    

  elem_in_map_eq_length__elem_in_list

  destruct (

  apply Equal_mapsto_iff.


  remember (split (map namedecl_to_pair nmtps)) as pnds.
  match goal with
  |[ |- context[split (map namedecl_to_pair nmtps)]] => idtac
  end.
  rewrite <- Heqpnds at 3.
  cases (split (map namedecl_to_pair nmtps)).


  induction nmtps as [| nmtp nmtps' IHnmtps' ];
    intros CT CT' HCT HCT';
    unfold concept_has_type in *; propositional.
  - (* nil *)
    simpl in *. symmetry in H4, H5.
    apply cardinal_Empty in H4. apply cardinal_Empty in H5.
    unfold IdLPM.IdMap.Empty in *.
(*    unfold IdLPM.IdMap.Proofs.Empty in H4, H5. *)
    apply Equal_mapsto_iff.
    intros k e. split; intros contra.
    + unfold IdLPM.IdMap.MapsTo in contra. apply H4 in contra. contradiction.
    + unfold IdLPM.IdMap.MapsTo in contra. apply H5 in contra. contradiction.
  - (* nmtps = nmtp :: nmtps' *)
    unfold concept_welldefined in H.
    unfold conceptDefs.intrfs_ok in H.
    destruct (split (map namedecl_to_pair (nmtp :: nmtps'))) 
      as [fnames ftypes] eqn:Heq.
    rewrite Heq in H at 1.
    propositional.
    apply split_fst__map_fst in Heq. subst.
    remember (map namedecl_to_pair (nmtp :: nmtps')) as pnds.
    apply F.Equal_mapsto_iff.
    (* IdLPM.IdMap.MapsTo k e CT <-> IdLPM.IdMap.MapsTo k e CT' *)
    intros k e. split; intros Hmaps;
                  assert (Hin : List.In (k, e) pnds).
    (* CT -> CT' *)
    unfold conceptDefs.intrfs_ok in *.
    destruct (split pnds) in H.
    apply elem_in_map_eq_length__elem_in_list with (CT := CT).
    subst pnds.
    apply forall_namedecl__forall_pair. apply H3. assumption. 
    subst. rewrite map_length. assumption.
    assumption.
    rewrite Forall_forall in H0.
    subst. 
    change (In (namedecl_to_pair (nm_decl k e)) (map namedecl_to_pair (nmtp :: nmtps'))) in Hin.
    apply in_pair__in_namedecl in Hin.
    specialize (H0 (nm_decl k e) Hin).
    apply F.find_mapsto_iff. assumption.
    (* CT' -> CT *)
    apply elem_in_map_eq_length__elem_in_list with (CT := CT').
    subst pnds.
    apply forall_namedecl__forall_pair. apply H0. assumption. 
    subst. rewrite map_length. assumption.
    assumption.
    rewrite Forall_forall in H3.
    subst. 
    change (In (namedecl_to_pair (nm_decl k e)) (map namedecl_to_pair (nmtp :: nmtps'))) in Hin.
    apply in_pair__in_namedecl in Hin.
    specialize (H3 (nm_decl k e) Hin).
    apply F.find_mapsto_iff. assumption.
Qed.    
*)

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
  (*unfold concept_welldefined, conceptDefs.intrfs_ok in Hsound.
  destruct (split (map namedecl_to_pair nds)) as [nms tps] eqn:Heq.
  Show Proof.
  rewrite Heq in Hsound at 1.
*)
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
    unfold conceptInterp.intrfs_ok_b in *.
    remember (map namedecl_to_pair nds') as pnds'. simpl in *.
    destruct (split pnds') as [nms tps] eqn:eqpnds'.
    rewrite eqpnds' in HCdef at 1.
    rewrite andb_true_iff in HCdef. inversion HCdef as [Huniq Hvalid].
    clear HCdef.
    apply ids_are_unique__sound in Huniq. 
    apply Forall_cons(*; destruct d; simpl in HCdef*).
    + (* head *)
      simpl. apply map_from_list__find_cons___true.
      (* ~ List.In i (map fst (map namedecl_to_pair nds')) *)
      inversion Huniq; subst.
      replace (IdLPM.get_ids (map namedecl_to_pair nds')) with nms.
      assumption. 
      apply split_fst__map_fst in eqpnds'. auto.
(*
Forall_impl:
  forall (A : Type) (P Q : A -> Prop),
  (forall a : A, P a -> Q a) -> forall l : list A, Forall P l -> Forall Q l
 *)
    + (* tail *)
      subst.
      apply Forall_impl with (P := fun pnd : id * ty =>
              match pnd with (f, T) =>
                  find_ty f (IdLPM.map_from_list (map namedecl_to_pair nds')) 
                  = Some T
              end).    
(*
      apply Forall_impl with (P := fun nmdecl : namedecl =>
              match nmdecl with
              | nm_decl f T =>
                  find_ty f (IdLPM.map_from_list (map namedecl_to_pair nds')) = Some T
              end).
*)
      intros [f T] H.
      simpl.
      apply IdLPM.IdMap.find_2 in H.
      apply IdLPM.IdMap.find_1. 
      apply map_from_list_cons__preserves_mapping. assumption.
      (* forall implication *)
      inversion Huniq; subst; simpl in *.
      apply IHnds'.
      (* bool -> prop *)
      unfold conceptInterp.intrfs_ok_b.
      rewrite eqpnds' at 1.
      apply andb_true_iff; split.
      apply ids_are_unique__complete. assumption.
      apply andb_true_iff in Hvalid. inversion Hvalid; auto.
      (* prop -> bool *)
      apply conceptProps.intrfs_ok__cons with (nm := i) (tp := t).
      assumption.
  - (* length *)
    remember (map namedecl_to_pair nds) as pnds.
(*    assert (Hlen : length pnds = length nds).
    { subst pnds. rewrite map_length. reflexivity. }
    rewrite -> Hlen. *)
    apply map_from_list__length_cardinal_eq.
    unfold concept_welldefined_b in HCdef.
    unfold conceptInterp.intrfs_ok_b in HCdef.
    destruct (split pnds) as [fnames ftypes] eqn:Hpnds. subst.
    rewrite Hpnds in HCdef at 1.
    apply andb_true_iff in HCdef. inversion HCdef as [Huniq _].
    apply ty_Intrfs1Base.IdLS.Props.ids_are_unique__sound in Huniq.
    apply split_fst__map_fst in Hpnds.
    subst. assumption.
(*    unfold conceptDefs.intrfs_ok in Hsound.
    destruct (split pnds) as [fnames ftypes] eqn:Hpnds. 
    rewrite Hpnds in Hsound at 1.
propositional.
    apply split_fst__map_fst in Hpnds.
    unfold IdLPM.get_ids. subst fnames. assumption.*)
Qed.

(** Here is the main [concept_type_check] completeness theorem. *)

Theorem concept_type_check__complete : 
  forall (cst : cptcontext) (C : conceptdef) (CT CT' : id_ty_map),  
    concept_has_type cst C (CTdef CT) ->
    concept_type_check cst C = Some (CTdef CT') ->
    IdLPM.IdMap.Equal CT CT'.
Proof.
  intros cst C CT CT' Hhas Hcheck.
  apply concept_type_check__sound in Hcheck.
  apply concept_has_type_iso with (cst := cst) (C := C);
    assumption.
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


(* ################################################################# *)
(** ** Soundness *)
(* ################################################################# *)

(*
MultiStep.

Lemma test : forall (t t' : tm),
    t #==>* t'.


Lemma test : forall (t t' : tm),
    step_fixed t t'.


Theorem progress : forall t T,
     empty |- t \in T ->
     value t \/ exists t', t ==> t'.
*)


