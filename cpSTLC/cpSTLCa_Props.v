(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(* Simply Typed Lambda Calculus with simple Concept Parameters
   :: version a
   Properties

   Properties of STLC are based on
   Sofware Foundations, v.4 
  
   Last Update: Wed, 18 Jun 2017
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

Require Import ConceptParams.GenericModuleLib.SharedDataDefs.
Require Import ConceptParams.GenericModuleLib.SimpleModule.
Require Import ConceptParams.GenericModuleLib.SinglePassModule.
Require Import ConceptParams.GenericModuleLib.SinglePassImplModule.

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
    destruct (IdLPM.IdMap.find i cst); tryfalse.
  - (* type_valid *)
    apply IHT in H2. assumption.
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
    destruct (IdLPM.IdMap.find i cst); tauto.
    (* type_valid *) assumption.
Qed.

(* !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *)
(** This part is using GenericModulesLib  *)
(* !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *)

Module MCptMem_DataCOkProp 
<: DataCOkProp MCptMem_DataC MCptMem_DataCOkDef MCptMem_DataCOkInterp. 

  Definition is_ok_b__sound := type_valid_b__sound.
  Definition is_ok_b__complete := type_valid_b__complete.
End MCptMem_DataCOkProp.

(** SimpleModule proofs about checking concept members. *)
Module MCptMem_Props := 
  SimpleModuleProps MCptMem_SimpleMBase 
                    MCptMem_DataCOkDef MCptMem_DataCOkInterp
                    MCptMem_DataCOkProp.


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
  apply MCptMem_Props.module_ok_b__sound. assumption.
Qed.

Theorem concept_well_defined_b__complete : forall (cst : cptcontext) (C : conceptdef),
    concept_welldefined   cst C ->
    concept_welldefined_b cst C = true.
Proof.
  intros cst C. intros H.
  destruct C as [nm body]. simpl in *.
  apply MCptMem_Props.module_ok_b__complete. assumption.
Qed.

(* ----------------------------------------------------------------- *)
(** **** Concept Typing *)
(* ----------------------------------------------------------------- *)

(** Now we want to prove that the function [concept_type_check] 
    is sound and complete. *)

(** For this, we are going to use the list-map machinery of IdLPM. *)

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

Lemma concept_has_type_iso : 
  forall (cst : cptcontext) (C : conceptdef) (CT CT' : id_ty_map),  
    concept_has_type cst C (CTdef CT) ->
    concept_has_type cst C (CTdef CT') ->
    IdLPM.IdMap.Equal CT CT'.
Proof.
  intros cst C. 
  destruct C as [Cnm nmtps]. 
  unfold concept_has_type.
  unfold concept_welldefined, MCptMem_Defs.module_ok.
(*  destruct (split (map namedecl_to_pair nmtps)) as [nms tps] eqn:Heq.
  (* For some reason, just [rewrite] cannot handle [split (map ...)] *) *)
  intros CT CT'. 
(*  rewrite Heq at 1. rewrite Heq at 1. *)
  intros HCT HCT'. propositional.
  apply IdLPM.Props.eq_list_map__same_list__eq_maps
  with (ps := map namedecl_to_pair nmtps);
    assumption.
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
  intros H. inversion H; clear H H1.
  pose proof (concept_well_defined_b__sound cst _ HCdef) as Hsound.
  unfold concept_has_type. split.
  (* concept_welldefined *) 
  assumption.
  (* eq_list_map *)
  apply eq_list_map_from_list.
  (* For some reason, the following does not work: *)
  (*
    unfold concept_welldefined in Hsound.
    unfold conceptDefs.intrfs_ok in Hsound.
    destruct (split (map namedecl_to_pair nds)) as [nms tps] eqn:Heq.
    rewrite Heq in Hsound at 1.
  *)
  (* So we do a bit roundabout proof... *)
  unfold concept_welldefined_b in *.
  unfold MCptMem_Interp.module_ok_b, 
  MCptMem_Interp.HelperI.MGM.module_ok_b in *.
  rewrite andb_true_iff in HCdef. inversion HCdef as [Hun Hok].
  apply IdLS.Props.ids_are_unique__sound in Hun.
  assumption.
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

(* !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *)


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
  (* CInvk for M with Gamma(M) = tmtype *)
  apply T_MInvk with (C := i1) (Mbody := i2);
    try assumption.
  intros contra. destruct contra as [MC contra].
  rewrite Eq in contra. inversion contra.
  unfold concept_fun_member. rewrite Eq1. assumption.
  (* CInvk for c#C *)  
  apply T_CInvk with (C := i1). eassumption.
  unfold concept_fun_member. rewrite Eq0. assumption.
  (* CInvk for M with Gamma(M) = None *)
  apply T_MInvk with (C := i1) (Mbody := i2);
    try assumption. 
  intros contra. destruct contra as [MC contra].
  rewrite Eq in contra. inversion contra.
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
    try tauto.
  (* tcinvk *)
  destruct (Gamma M) eqn:HeqM;
    try reflexivity.
  destruct c eqn:Heqc;
    try reflexivity.
  exfalso. apply H.
  exists i0. reflexivity.
Qed.




(* ################################################################# *)
(** ** Soundness *)
(* ################################################################# *)

(* ----------------------------------------------------------------- *)
(** **** Aux Props about Contexts *)
(* ----------------------------------------------------------------- *)

Definition appears_free_in (CTbl : cptcontext) (MTbl : mdlcontext)
           (x : id) (t : tm) : Prop :=
  IdLS.IdSet.In x (free_vars CTbl MTbl t).

Hint Unfold appears_free_in.

Lemma context_invariance : forall CTbl MTbl Gamma Gamma' t T,
    CTbl $ MTbl ; Gamma |- t \in T  ->
    (forall x, appears_free_in CTbl MTbl x t -> Gamma x = Gamma' x) ->
    CTbl $ MTbl ; Gamma' |- t \in T.
Proof.
  intros CTbl MTbl Gamma Gamma' t T (*HCTOk HMTOk*) HT.
  generalize dependent Gamma'.
  induction HT; intros Gamma' Hfree; 
    unfold appears_free_in in *; simpl; auto;
    simpl in *;
    (* for regular cases such as [if] or [tsucc]
       we can use automation *)
    try solve 
    [constructor;
    repeat
    match goal with
      [IHHT  : forall Gamma' : id -> option ctxvarty,
               _ -> has_type _ _ _ ?t ?T ,
       Hfree : forall x : id, _ -> ?Gamma x = ?Gamma' x 
       |- ?CTable $ ?MTable; ?Gamma' |- ?t \in ?T]
      => apply IHHT; intros x Hin; apply Hfree;
         auto using IdLS.Props.IdSetProps.Dec.F.union_2,
                    IdLS.Props.IdSetProps.Dec.F.union_3
    end].
  - (* tvar *)
    specialize (Hfree x). unfold free_vars in Hfree.
    assert (Hin : IdLS.IdSet.In x (IdLS.IdSet.singleton x)).
    apply IdLS.Props.IdSetProps.Dec.F.singleton_2. reflexivity.
    apply Hfree in Hin. rewrite H in Hin.
    constructor. symmetry. assumption.
  - (* tapp t1 t2 *)
    apply T_App with T11.
    + apply IHHT1.
      intros x H. apply Hfree. 
      apply IdLS.Props.IdSetProps.FM.union_2; assumption.
    + apply IHHT2.
      intros x H. apply Hfree.
      apply IdLS.Props.IdSetProps.FM.union_3; assumption.
  - (* tabs *)
    apply T_Abs.
    apply IHHT.
    intros y Hin.
    destruct (beq_idP x y).
    + subst. rewrite update_eq. rewrite update_eq.
      reflexivity.
    + assert (Hin' : IdLS.IdSet.In y 
                     (IdLS.IdSet.remove x (free_vars CTable MTable t12))).
      { apply IdLS.Props.IdSetProps.Dec.F.remove_2;
          assumption. }
      specialize (Hfree y Hin').
      rewrite (update_neq _ _ _ _ _ n). rewrite (update_neq _ _ _ _ _ n).
      assumption.
  - (* tmapp *)
    econstructor. eassumption.
    apply IHHT. assumption.
  - (* tcabs *)
    apply T_CAbs with Cbody. assumption.
    apply IHHT.
    intros y Hin.
    destruct (beq_idP y c).
    + subst. rewrite update_eq. rewrite update_eq.
      reflexivity.
    + assert (Hin' : IdLS.IdSet.In y 
                     (IdLS.IdSet.remove c (free_vars CTable MTable t1))).
      { apply IdLS.Props.IdSetProps.Dec.F.remove_2. 
        intros Heq. symmetry in Heq. apply n in Heq. 
        assumption. assumption. }
      specialize (Hfree y Hin'). apply not_eq_sym in n.
      rewrite (update_neq _ _ _ _ _ n). rewrite (update_neq _ _ _ _ _ n).
      assumption.
  - (* tcinvk *)
    apply T_CInvk with C.
    rewrite <- H.
    symmetry. apply Hfree.
    apply IdLS.Props.IdSetProps.Dec.F.singleton_2. reflexivity.
    assumption.
  - (* tcinvk for M.f *)
    apply T_MInvk with C Mbody. 
    intros contra. destruct contra as [MC contra].
    rewrite <- Hfree in contra.
      apply H. exists MC. assumption.
    apply IdLS.Props.IdSetProps.Dec.F.singleton_2. reflexivity.
    assumption. assumption.
  - (* tlet *)
    apply T_Let with T1.
    + apply IHHT1. intros y Hin.
      apply Hfree.
      apply IdLS.Props.IdSetProps.Dec.F.union_2; assumption.
    + apply IHHT2. intros y Hin.
      destruct (beq_idP x y).
      * subst. rewrite update_eq. rewrite update_eq. reflexivity.
      * rewrite (update_neq _ _ _ _ _ n). 
        rewrite (update_neq _ _ _ _ _ n).
        apply Hfree.
        apply IdLS.Props.IdSetProps.Dec.F.union_3.
        apply IdLS.Props.IdSetProps.Dec.F.remove_2.
        assumption. assumption.
Qed.


(** These are auxiliary tactics to simplify proofs 
    involving model names in terms/contexts *)

Definition no_model_names_as_cvars_in_Gamma 
           (MTbl : mdlcontext) (G : context) : Prop :=
  forall M, 
    (exists C, G M = Some (cpttype C))
    /\ IdLPM.IdMap.In M MTbl ->
    False.

Definition no_model_names_as_bound_cvars_in_term
           (MTbl : mdlcontext) (t : tm) : Prop :=
  ~ (exists M, IdLS.IdSet.In M (bound_cvars t)
               /\ IdLPM.IdMap.In M MTbl).

Ltac prove_no_bound_cvar_in_subterm :=
  match goal with
    [ HMtf : ~ IdLS.IdSet.In _ ?t
      |- ~ IdLS.IdSet.In _ (bound_cvars ?st)] 
    => match t with context [ st ] 
    => let HMtf' := fresh "HMtf" in
       assert (HMtf' := HMtf);
       intros contra; apply HMtf'; simpl;
       auto using IdLS.Props.IdSetProps.Dec.F.union_2, 
                  IdLS.Props.IdSetProps.Dec.F.union_3,
                  IdLS.Props.IdSetProps.Dec.F.singleton_2,
                  IdLS.Props.IdSetProps.Dec.F.remove_2,
                  IdLS.Props.IdSetProps.Dec.F.add_2;
         clear HMtf'
    end end.

Ltac prove_no_model_names_as_bound_cvars_in_subterm :=
  match goal with
    [ HtfMT : no_model_names_as_bound_cvars_in_term ?MTbl ?t
      |- no_model_names_as_bound_cvars_in_term ?MTbl ?st] 
    => match t with context [ st ] 
    => let HtfMT' := fresh "HtfMT'" in
       assert (HtfMT' := HtfMT);
       unfold no_model_names_as_bound_cvars_in_term;
       unfold no_model_names_as_bound_cvars_in_term in HtfMT';
       intros contra;
       let cM := fresh "cM" in
       let Hintf := fresh "Hintf" in
       let HinMT := fresh "HinMT" in
       inversion contra as [cM [Hintf HinMT]];
       apply HtfMT'; 
       eexists; split;
       try solve [
             simpl;
             eauto using 
                   IdLS.Props.IdSetProps.Dec.F.union_2, 
                   IdLS.Props.IdSetProps.Dec.F.union_3,
                   IdLS.Props.IdSetProps.Dec.F.singleton_2,
                   IdLS.Props.IdSetProps.Dec.F.remove_2,
                   IdLS.Props.IdSetProps.Dec.F.add_2
           ];
       try assumption
    end end.


Lemma context_weakening : forall CTbl MTbl Gamma Gamma' t T,
    CTbl $ MTbl ; Gamma |- t \in T ->
    no_model_names_as_bound_cvars_in_term MTbl t -> 
    (forall x, Gamma x <> None -> Gamma' x = Gamma x) ->
    no_model_names_as_cvars_in_Gamma MTbl Gamma' -> 
    CTbl $ MTbl ; Gamma' |- t \in T.
Proof.
  intros CTbl MTbl Gamma Gamma' t T HT.
  generalize dependent Gamma'.
  induction HT;
    intros Gamma' Htok HGamma' Hcvars;
  (* for trivial cases *)
    try solve [constructor];
  (* for inductive cases simply apply IHs *)
    try solve [
          constructor;
          match goal with
            [ HT : has_type _ _ ?Gamma ?s ?S ,
              IH : context [ has_type _ _ _ ?s ?S ]
              |- _ $ _ ; ?Gamma' |- ?s \in ?S ]
            => apply IH; 
               (assumption 
                || prove_no_model_names_as_bound_cvars_in_subterm)
          end
        ].
  - (* tvar *)
    pose proof (eq_Some_not_None _ _ _ _ H) as Hnone.
    specialize (HGamma' _ Hnone).
    apply T_Var. rewrite HGamma'. assumption.
  - (* tapp *)
    apply T_App with T11.
    apply IHHT1; 
      (assumption 
       || prove_no_model_names_as_bound_cvars_in_subterm).
    apply IHHT2; 
      (assumption 
       || prove_no_model_names_as_bound_cvars_in_subterm).
  - (* tabs *)
    apply T_Abs.
    apply IHHT.
    prove_no_model_names_as_bound_cvars_in_subterm. 
    intros z Hznone.
    destruct (beq_idP x z) as [Hxz | Hxz].
    + (* = *)
      subst. repeat rewrite update_eq. reflexivity.
    + (* <> *)
      repeat rewrite update_neq; try assumption.
      apply HGamma'. rewrite update_neq in Hznone; try assumption.
    + (* no_model_names_as_cvars_in_Gamma *)
      unfold no_model_names_as_cvars_in_Gamma.
      intros M [[C HC] Hin].
      destruct (beq_idP x M) as [HxM | HxM].
      * (* = *)
        subst. rewrite update_eq in HC. inversion HC.
      * (* <> *)
        rewrite update_neq in HC; try assumption.
        unfold no_model_names_as_cvars_in_Gamma in Hcvars.
        apply Hcvars with M.
        split. exists C; assumption. assumption. 
  - (* tmapp *)
    apply T_MApp with C Mbody; try assumption.
    apply IHHT; (assumption 
                 || prove_no_model_names_as_bound_cvars_in_subterm).
  - (* tcabs *)
    apply T_CAbs with Cbody; try assumption.
    apply IHHT.
    prove_no_model_names_as_bound_cvars_in_subterm. 
    intros z Hznone.
    destruct (beq_idP c z) as [Hcz | Hcz].
    + (* = *)
      subst. repeat rewrite update_eq. reflexivity.
    + (* <> *)
      repeat rewrite update_neq; try assumption.
      apply HGamma'. rewrite update_neq in Hznone; try assumption.
    + (* no_model_names_as_cvars_in_Gamma *)
      unfold no_model_names_as_cvars_in_Gamma.
      intros M [[C' HC'] Hin].
      unfold no_model_names_as_bound_cvars_in_term in Htok.
      unfold no_model_names_as_cvars_in_Gamma in Hcvars.
      simpl in Htok.
      destruct (beq_idP c M) as [HcM | HcM].
      * subst.
        apply Htok. exists M.
        split; try assumption.
        apply IdLS.Props.IdSetProps.Dec.F.add_1; reflexivity.
      * rewrite update_neq in HC'. 
        apply Hcvars with M. split; try assumption.
        exists C'; assumption. assumption. 
  - (* T_CInvk *)
    apply T_CInvk with C; try assumption.
    pose proof (eq_Some_not_None _ _ _ _ H) as Hnone.
    specialize (HGamma' _ Hnone).
    rewrite HGamma'. assumption.
  - (* T_MInvk *)
    apply T_MInvk with C Mbody; try assumption.
    unfold no_model_names_as_cvars_in_Gamma in Hcvars.
    intros contra. apply Hcvars with M.
    split; try assumption. 
    apply IdMapProps.F.in_find_iff. intros contra'.
    rewrite H0 in contra'. inversion contra'. 
  - (* tlet *)
    apply T_Let with T1.
    apply IHHT1; 
      (assumption
       || prove_no_model_names_as_bound_cvars_in_subterm).
    apply IHHT2.
    prove_no_model_names_as_bound_cvars_in_subterm.
    intros z Hznone.    
    destruct (beq_idP x z) as [Hxz | Hxz].
    + (* = *)
      subst. repeat rewrite update_eq. reflexivity.
    + (* <> *)
      repeat rewrite update_neq; try assumption.
      apply HGamma'. rewrite update_neq in Hznone; try assumption.
    + (* no_model_names_as_cvars_in_Gamma *)
      unfold no_model_names_as_cvars_in_Gamma.
      intros M [[C HC] Hin].
      destruct (beq_idP x M) as [HxM | HxM].
      * (* = *)
        subst. rewrite update_eq in HC. inversion HC.
      * (* <> *)
        rewrite update_neq in HC; try assumption.
        unfold no_model_names_as_cvars_in_Gamma in Hcvars.
        apply Hcvars with M.
        split. exists C; assumption. assumption.
Qed.

Lemma cptcontext_weakening__concept_fun_member :
  forall (CTbl CTbl' : cptcontext) C f TF,
    concept_fun_member CTbl C f TF ->
    (** CTbl' possibly contains more than CTbl *)
    (forall C cpt, 
        IdLPM.IdMap.find C CTbl = Some (CTdef cpt) ->
        exists cpt',
          IdLPM.IdMap.find C CTbl' = Some (CTdef cpt')
          /\ IdLPM.IdMap.Equal cpt cpt') ->
    concept_fun_member CTbl' C f TF.
Proof.
  intros CTbl CTbl' C f TF H HCweak.
  unfold concept_fun_member in H.
  destruct (IdLPM.IdMap.find C CTbl) as [[Cbody] | ] eqn:HeqC;
    try solve [inversion H].
  specialize (HCweak C Cbody HeqC).
  destruct HCweak as [Cbody' [HC' HeqCC']].
  unfold concept_fun_member.
  rewrite HC'. unfold find_ty in *.
  apply IdMapProps.F.find_mapsto_iff.
  rewrite IdMapProps.F.Equal_mapsto_iff in HeqCC'.
  rewrite <- IdMapProps.F.find_mapsto_iff in H.
  rewrite <- (HeqCC' f TF). assumption.
Qed.  

Lemma cptcontext_weakening :
  forall CTbl MTbl Gamma (t : tm) (T : ty) CTbl',
    (** term has type under [CTbl] *)
    CTbl $ MTbl ; Gamma |- t \in T ->
    (** CTbl' possibly contains more than CTbl *)
    (forall C cpt, 
        IdLPM.IdMap.find C CTbl = Some (CTdef cpt) ->
        exists cpt',
          IdLPM.IdMap.find C CTbl' = Some (CTdef cpt')
          /\ IdLPM.IdMap.Equal cpt cpt') ->
    (** then term has the same type under CTbl' *)
    CTbl' $ MTbl ; Gamma |- t \in T.
Proof.
  intros CTbl MTbl Gamma t T CTbl'. intros HT. 
  generalize dependent CTbl'.
  induction HT;
    intros CTbl' HCweak;
  (* simple cases, such as [ttrue] of [tvar] *)
  try solve [constructor; try assumption];
  (* for regular inductive cases we just apply IHs *)
  try solve [
        constructor;
        (*apply IHHT1; assumption.*)
        match goal with
          [ IHHT : context[ _ -> (has_type _ _ _ ?s ?S) ]
            |- ?CTbl $ ?MTable; ?Gamma |- ?s \in ?S ] 
          => apply IHHT; assumption
        end].
  - (* tapp *)
    apply T_App with T11.
    apply IHHT1. assumption.
    apply IHHT2; assumption.
  - (* tmapp *)
    apply T_MApp with C Mbody.
    assumption.
    apply IHHT; assumption.
  - (* tcabs *)
    specialize (IHHT CTbl' HCweak).
    specialize (HCweak C Cbody H).
    destruct HCweak as [Cbody' [H' _]].
    apply T_CAbs with Cbody';
      assumption.
  - (* T_CInvk *)
    pose proof (cptcontext_weakening__concept_fun_member 
                  CTable CTbl' C f TF H0 HCweak)
    as Hfun.
    apply T_CInvk with C; try assumption.
  - (* T_MInvk *)
    apply T_MInvk with C Mbody; try assumption.
    apply cptcontext_weakening__concept_fun_member with CTable; assumption.
  - (* T_Let *)
    apply T_Let with T1.
    apply IHHT1; assumption.
    apply IHHT2; assumption.
Qed.

Lemma mdlcontext_weakening :
  forall CTbl MTbl Gamma (t : tm) (T : ty) MTbl',
    (** term has type under [MTbl] *)
    CTbl $ MTbl ; Gamma |- t \in T ->
    (** MTbl' possibly contains more than MTbl *)
    (forall M C mdl, 
        IdLPM.IdMap.find M MTbl = Some (MTdef C mdl) ->
        exists mdl',
          IdLPM.IdMap.find M MTbl' = Some (MTdef C mdl')
          /\ IdLPM.IdMap.Equal mdl mdl') ->
    (** then term has the same type under MTbl' *)
    CTbl $ MTbl' ; Gamma |- t \in T.
Proof.
  intros CTbl MTbl Gamma t T MTbl'. intros HT. 
  generalize dependent MTbl'.
  induction HT;
    intros MTbl' HMweak;
  (* simple cases, such as [ttrue] of [tvar] *)
  try solve [constructor; try assumption];
  (* for regular inductive cases we just apply IHs *)
  try solve [
        constructor;
        (*apply IHHT1; assumption.*)
        match goal with
          [ IHHT : context[ _ -> (has_type _ _ _ ?s ?S) ]
            |- ?CTbl $ ?MTbl; ?Gamma |- ?s \in ?S ] 
          => apply IHHT; assumption
        end].
  - (* tapp *)
    apply T_App with T11.
    apply IHHT1. assumption.
    apply IHHT2; assumption.  
  - (* tmapp *)
    assert (HMweak' := HMweak).
    specialize (HMweak M C Mbody H).
    destruct HMweak as [Mbody' [HM HeqMM']].
    apply T_MApp with C Mbody'. assumption.
    apply IHHT; assumption.
  - (* tcabs *)
    apply T_CAbs with Cbody. assumption.
    apply IHHT; assumption.
  - (* T_CInvk *)
    apply T_CInvk with C; try assumption.
  - (* T_MInvk *)
    specialize (HMweak M C Mbody H0).
    destruct HMweak as [Mbody' [HM HeqMM']].
    apply T_MInvk with C Mbody'; try assumption.
  - (* T_Let *)
    apply T_Let with T1.
    apply IHHT1; assumption.
    apply IHHT2; assumption.
Qed.


(* ----------------------------------------------------------------- *)
(** **** Aux Props about QMM (qualify_model_members) *)
(* ----------------------------------------------------------------- *)

Lemma qualify_model_members'_preserves_typing_for_good_Gamma' :
  forall (CTbl : cptcontext) (MTbl : mdlcontext)
         (Gamma : context) (tf : tm) (Tf : ty)
         mdlmems (C : id) Cbody M Mbody Gamma',
    (* [tf] has type [Tf] *)
    CTbl $ MTbl ; Gamma |- tf \in Tf ->
    (* term does not contain concept vars named as model names *)
    no_model_names_as_bound_cvars_in_term MTbl tf ->
    (* we work with a valid concept *)
    IdLPM.IdMap.find C CTbl = Some (CTdef Cbody) ->
    (* names we qualify appear in concept and consistent with Gamma *)
    (forall x, IdLS.IdSet.In x mdlmems -> 
               exists Tx, 
                 (IdLPM.IdMap.find x Cbody = Some Tx)
                 /\ (forall Tx', 
                      Gamma x = Some (tmtype Tx') ->
                      Tx = Tx')) -> 
    (* M in MTbl *)
    IdLPM.IdMap.find M MTbl = Some (MTdef C Mbody) ->
    (* Gamma' contains not-to-qualify variables from Gamma *)
    (forall x, Gamma x <> None ->
               (~ IdLS.IdSet.In x mdlmems 
                \/ exists xC, Gamma x = Some (cpttype xC)) -> 
               Gamma' x = Gamma x) ->
    (* Gamma' does not contain M as a concept parameter *)
    ~ (exists MC, Gamma' M = Some (cpttype MC)) ->
    (* Gamma' does not contain other model names from MTbl *)
    no_model_names_as_cvars_in_Gamma MTbl Gamma' ->
    let tf'   := qualify_model_members' M mdlmems tf in 
    CTbl $ MTbl ; Gamma' |- tf' \in Tf.
Proof.
  intros CTbl MTbl Gamma tf. generalize dependent Gamma.
  induction tf;
    intros Gamma Tf mdlmems C Cbody M Mbody Gamma';
    intros HT HtfMT HfindC HGamma HMMTbl 
           HGamma' HGamma'M HGamma'MTbl;
    (inversion HT; subst; simpl);
    unfold id_mem in *;
  (* trivial cases such as [ttrue] can be solved *)
  try solve [constructor];
  (* we can also solve inductive cases with IHs *)
  try solve [
        constructor;
        match goal with
          [HTst : ?CTbl $ ?MTbl ; ?Gamma |- ?st \in ?ST ,
           IHst : context [
                      has_type ?CTbl _ _
                               (qualify_model_members' _ _ ?st) 
                    ] ,
           Cbody : id_ty_map ,
           HCbody : context [ Some (CTdef Cbody) ]
           |- has_type ?CTbl ?MTbl' ?Gamma' 
                       (qualify_model_members' _ _ ?st) ?ST]
          => apply IHst with Gamma C Cbody Mbody;
             try (assumption || prove_no_model_names_as_bound_cvars_in_subterm)
        end ]. 
  - (* tvar *)
    rename i into f.
    destruct (IdLS.IdSet.mem f mdlmems) eqn:Hmemf.
    + (* f in mdlnames *)
      apply T_MInvk with C Mbody.
      assumption. assumption.
      unfold concept_fun_member. rewrite HfindC.
      apply IdLS.Props.IdSetProps.Dec.F.mem_2 in Hmemf.
      specialize (HGamma f Hmemf).
      destruct HGamma as [Tx [HCbody HGamma]].
      specialize (HGamma Tf H3). subst.
      assumption.
    + (* f not in mdlmems *)
      apply T_Var.
      rewrite HGamma'. assumption.
      intros contra. rewrite H3 in contra. inversion contra. left.
      apply IdLS.Props.IdSetProps.Dec.F.not_mem_iff. assumption.
  - (* tapp *)
    apply T_App with T11.
    apply IHtf1 with Gamma C Cbody Mbody; 
      try (assumption || prove_no_model_names_as_bound_cvars_in_subterm).
    apply IHtf2 with Gamma C Cbody Mbody; 
      try (assumption || prove_no_model_names_as_bound_cvars_in_subterm).
  - (* tabs *)
    rename i into x. rename t into T.
    apply T_Abs.
    apply IHtf
    with (update Gamma x (tmtype T)) C Cbody Mbody;
      try assumption.
    + (* Gamma *)
      intros z Hzin.
      apply IdLS.Props.IdSetProps.Dec.F.remove_iff in Hzin.
      destruct Hzin as [Hzin Hxz].
      specialize (HGamma _ Hzin).
      destruct HGamma as [Tz [HzCbody HGamma]].
      exists Tz. split. assumption.
      intros Tz' HGTz. 
      rewrite update_neq in HGTz; try assumption. 
      apply HGamma. assumption.
    + (* Gamma' *)
      intros z HGammaz.
      destruct (beq_idP x z) as [Hxz | Hxz].
      * (* x = z *)
        subst. intros _.
        repeat rewrite update_eq.
        reflexivity.
      *  (* x <> z *)
        intros Hninz.
        repeat rewrite update_neq; try assumption.
        destruct Hninz as [Hninz | Hcpt];
        apply HGamma';
        rewrite update_neq in HGammaz; try assumption. 
        left.
          intros contra. 
          pose proof (@IdLS.Props.IdSetProps.Dec.F.remove_2 mdlmems _ _ Hxz contra)
            as contra'.
          apply Hninz in contra'. assumption.
        right.
          destruct Hcpt as [xC Hcpt]. rewrite update_neq in Hcpt. 
          eexists. eassumption. assumption.
    + (* HGamma' M *)
      intros contra. destruct contra as [MC contra].
      destruct (beq_idP x M) as [HxM | HxM].
      subst. rewrite update_eq in contra. inversion contra.
      rewrite update_neq in contra. apply HGamma'M.
        eexists. eassumption. assumption.
    + (* No models in Gamma' *)
      unfold no_model_names_as_cvars_in_Gamma.
      unfold no_model_names_as_cvars_in_Gamma in HGamma'MTbl.
      intros M0 HM0. destruct HM0 as [[M0C Hupd] HM0].
      destruct (beq_idP x M0).
      subst. rewrite update_eq in Hupd. inversion Hupd.
      rewrite update_neq in Hupd; try assumption.
      apply HGamma'MTbl with M0. split; try assumption.
      eexists; eassumption.
  - (* tmapp *)
    rename i into N.
    apply T_MApp with C0 Mbody0.
    + (* find N MTbl' *)
      assumption.
    + (* typing *) 
      apply IHtf with Gamma C Cbody Mbody; assumption.
  - (* tcabs *)
    rename i into c. rename i0 into C'.
    apply T_CAbs with Cbody0. assumption.
    apply IHtf with (update Gamma c (cpttype C')) C Cbody Mbody;
      try assumption.
    + (* no model names *)
      prove_no_model_names_as_bound_cvars_in_subterm.
    + (* Gamma *)
      intros z Hzin.
      apply IdLS.Props.IdSetProps.Dec.F.remove_iff in Hzin.
      destruct Hzin as [Hzin Hcz].
      specialize (HGamma _ Hzin).
      destruct HGamma as [Tz [HzCbody HGamma]].
      exists Tz. split. assumption.
      intros Tz' HGTz. 
      rewrite update_neq in HGTz; try assumption. 
      apply HGamma. assumption.
    + (* Gamma' *)
      intros z HGammaz.
      destruct (beq_idP c z) as [Hcz | Hcz].
      * (* c = z *)
        subst. intros _.
        repeat rewrite update_eq. reflexivity.
      *  (* c <> z *)
        intros Hninz.
        repeat rewrite update_neq; try assumption.
        apply HGamma'.
        rewrite update_neq in HGammaz; try assumption.
        destruct Hninz as [Hninz | Hcpt].
        left.
          intros contra. 
          pose proof (@IdLS.Props.IdSetProps.Dec.F.remove_2 mdlmems _ _ Hcz contra)
            as contra'.
          apply Hninz in contra'. assumption.
        right.
          destruct Hcpt as [xC Hcpt]. 
          rewrite update_neq in Hcpt; try assumption.
          eexists. eassumption.
    + (* HGamma' M *)
      intros HGM'. destruct HGM' as [MC HGM'].
      destruct (beq_idP c M) as [HcM | HcM].
      * subst. 
        unfold no_model_names_as_bound_cvars_in_term in HtfMT.
        apply HtfMT. exists M. split.
        simpl. apply IdLS.Props.IdSetProps.Dec.F.add_1. reflexivity.
        unfold IdLPM.IdMap.In. eexists. 
        apply IdMapProps.F.find_mapsto_iff. eassumption.
      * rewrite update_neq in HGM'; try assumption.
        apply HGamma'M. eexists. eassumption.
    + (* No models in Gamma' *)
      unfold no_model_names_as_cvars_in_Gamma.
      unfold no_model_names_as_bound_cvars_in_term in HtfMT.
      simpl in HtfMT.
      unfold no_model_names_as_cvars_in_Gamma in HGamma'MTbl.
      intros M0 HM0. destruct HM0 as [[M0C Hupd] HM0].
      destruct (beq_idP c M0).
      subst. rewrite update_eq in Hupd. inversion Hupd.
        subst. apply HtfMT. exists M0. split.
        apply IdLS.Props.IdSetProps.Dec.F.add_1. reflexivity. assumption.
      rewrite update_neq in Hupd; try assumption.
        apply HGamma'MTbl with M0. split; try assumption.
        eexists; eassumption. 
  - (* T_CInvk *)
    rename i into c. rename i0 into f.
    apply T_CInvk with C0. rewrite <- H4. 
    apply HGamma'.
    intros contra. rewrite H4 in contra. inversion contra.
    destruct (IdLS.Props.IdSetProps.In_dec c mdlmems) as [Hmemc | Hmemc].
    + right. eexists. eassumption.
    + left. assumption.
    + assumption.
  - (* T_MInvk *)
    rename i into N. rename i0 into f.
    apply T_MInvk with C0 Mbody0; try assumption.
    + unfold no_model_names_as_cvars_in_Gamma in HGamma'MTbl.
      intros HN. apply HGamma'MTbl with N.
      split. assumption.
      apply IdMapProps.F.in_find_iff. 
      intros contra. rewrite H5 in contra. inversion contra.
  - (* tlet *)
    rename i into x. 
    apply T_Let with T1.
    apply IHtf1 with Gamma C Cbody Mbody; 
      try (assumption || prove_no_model_names_as_bound_cvars_in_subterm).    
    apply IHtf2 with (update Gamma x (tmtype T1)) C Cbody Mbody;
      try assumption.
    + prove_no_model_names_as_bound_cvars_in_subterm.
    + (* Gamma *)
      intros z Hzin.
      apply IdLS.Props.IdSetProps.Dec.F.remove_iff in Hzin.
      destruct Hzin as [Hzin Hxz].
      specialize (HGamma _ Hzin).
      destruct HGamma as [Tz [HzCbody HGamma]].
      exists Tz. split. assumption.
      intros Tz' HGTz. 
      rewrite update_neq in HGTz; try assumption. 
      apply HGamma. assumption.
(*    + prove_no_bound_cvar_in_subterm. *)
    + (* Gamma' *)
      intros z HGammaz.
      destruct (beq_idP x z) as [Hxz | Hxz].
      * (* x = z *)
        subst. intros _.
        repeat rewrite update_eq.  reflexivity.
      * (* x <> z *)
        intros Hninz.
        repeat rewrite update_neq; try assumption.
        destruct Hninz as [Hninz | Hcpt];
        apply HGamma';
        rewrite update_neq in HGammaz; try assumption. 
        left.
          intros contra. 
          pose proof (@IdLS.Props.IdSetProps.Dec.F.remove_2 mdlmems _ _ Hxz contra)
            as contra'.
          apply Hninz in contra'. assumption.
        right.
          destruct Hcpt as [xC Hcpt]. rewrite update_neq in Hcpt. 
          eexists. eassumption. assumption.
    + (* HGamma' M *)
      intros contra. destruct contra as [MC contra].
      destruct (beq_idP x M) as [HxM | HxM].
      subst. rewrite update_eq in contra. inversion contra.
      rewrite update_neq in contra. apply HGamma'M.
        eexists. eassumption. assumption.
    + (* No models in Gamma' *)
      unfold no_model_names_as_cvars_in_Gamma.
      unfold no_model_names_as_cvars_in_Gamma in HGamma'MTbl.
      intros M0 HM0. destruct HM0 as [[M0C Hupd] HM0].
      destruct (beq_idP x M0).
      subst. rewrite update_eq in Hupd. inversion Hupd.
      rewrite update_neq in Hupd; try assumption.
      apply HGamma'MTbl with M0. split; try assumption.
      eexists; eassumption.
Qed.

Lemma qualify_model_members'_preserves_typing_for_good_Gamma :
  forall (CTbl : cptcontext) (MTbl : mdlcontext)
         (Gamma : context) (tf : tm) (Tf : ty)
         mdlmems (C : id) Cbody M Mbody,
    (* [tf] has type [Tf] *)
    CTbl $ MTbl ; Gamma |- tf \in Tf ->
    (* term does not contain concept vars named as model names *)
    no_model_names_as_bound_cvars_in_term MTbl tf ->
    (* we work with a valid concept *)
    IdLPM.IdMap.find C CTbl = Some (CTdef Cbody) ->
    (* all names in Gamma are to be qualified *)
    (forall x, Gamma x <> None ->
               exists Tx, Gamma x = Some (tmtype Tx)
                          /\ IdLS.IdSet.In x mdlmems) ->
    (* names we qualify appear in concept and consistent with Gamma *)
    (forall x, 
        IdLS.IdSet.In x mdlmems -> 
        exists Tx, 
          IdLPM.IdMap.find x Cbody = Some Tx
          /\ (Gamma x <> None -> Gamma x = Some (tmtype Tx))) ->
    (* M in MTbl *)
    IdLPM.IdMap.find M MTbl = Some (MTdef C Mbody) ->
    let tf'   := qualify_model_members' M mdlmems tf in 
    CTbl $ MTbl ; ctxempty |- tf' \in Tf.
Proof.
  intros CTbl MTbl Gamma tf Tf mdlmems C Cbody M Mbody.
  intros HT HMTtf HfindC HGamma Hmems HMMtbl.
  simpl. 
  apply qualify_model_members'_preserves_typing_for_good_Gamma'
    with Gamma C Cbody Mbody; 
    try assumption.
  + (* Gamma *)
    intros z Hinz. assert (Hmems' := Hmems).
    specialize (Hmems z Hinz).
    destruct Hmems as [Tz [Hfindz Hz]].
    exists Tz. split. assumption.
    intros Tz' HTz'.
    assert (Hznone : Gamma z <> None).
    { intros contra. rewrite HTz' in contra. inversion contra. }
    specialize (Hz Hznone). rewrite Hz in HTz'. inversion HTz'.
    subst. reflexivity.
  + intros z Hz. intros contra.
    destruct contra as [contra | contra];
      exfalso. 
    apply contra. specialize (HGamma z Hz).
      destruct HGamma as [_ [_ Hzmem]]. assumption.
    destruct contra as [xC contra].
      specialize (HGamma z Hz). destruct HGamma as [Tz [Hzeq _]].
      rewrite Hzeq in contra. inversion contra.
  + intros contra. destruct contra as [MC contra].
    inversion contra.
  + unfold no_model_names_as_cvars_in_Gamma.
    intros M0 [[C0 contra] _]. inversion contra.
Qed.


Lemma qualify_model_members'_preserves_term_in_empty' :
  forall (CTbl : cptcontext) (MTbl : mdlcontext) M
         (tf : tm) (Tf : ty) Gamma mdlmems,
    (* [tf] has type [Tf] *)
    CTbl $ MTbl ; Gamma |- tf \in Tf ->
    (* Gamma does not contain names to qualify *)
    (forall x, Gamma x <> None -> ~ IdLS.IdSet.In x mdlmems) ->
    (* term does not contain concept vars named as model names *)
    no_model_names_as_bound_cvars_in_term MTbl tf ->
    (* M is not used for concept parameter names *)
    ~ IdLS.IdSet.In M (bound_cvars tf) ->
    let tf' := qualify_model_members' M mdlmems tf in 
    tf = tf'.
Proof.
  intros CTbl MTbl M tf.
  induction tf;
    intros Tf Gamma mdlmems;
    intros HT HGamma Hcvars HMtf; 
    (inversion HT; subst; simpl);
  (* trivial cases *)
    try reflexivity;
  (* inductive cases *)
    try (
      repeat match goal with
      [ HTst : ?CTbl $ ?MTbl; ?Gamma |- ?st \in ?ST ,
        IHst : context[ 
                   ?st = _  
                 ]
        |- context[ qualify_model_members' ?M ?mdlmems ?st ] ] 
      => rewrite <- IHst with ST Gamma mdlmems; 
           try (assumption 
                || prove_no_model_names_as_bound_cvars_in_subterm
                || prove_no_bound_cvar_in_subterm)

      end;
      reflexivity).
  - (* tvar *) 
    rename i into x.
    pose proof (eq_Some_not_None _ _ _ _ H3) as Hnone.
    specialize (HGamma x Hnone). 
    apply IdLS.Props.IdSetProps.Dec.F.not_mem_iff in HGamma.
    unfold id_mem. rewrite HGamma. reflexivity.
  - (* tabs *)
    rename i into x. rename t into T.
    rewrite <- IHtf with T12 (update Gamma x (tmtype T)) 
                             (IdLS.IdSet.remove x mdlmems);
      try assumption.
    reflexivity.
    intros z Hz.
    destruct (beq_idP x z) as [Hxz | Hxz].
    + (* x = z *)
      subst. apply IdLS.Props.IdSetProps.Dec.F.remove_1. 
      reflexivity.
    + (* x <> z *)
      rewrite update_neq in Hz; try assumption.
      intros contra.
      apply IdLS.Props.IdSetProps.Dec.F.remove_3 in contra.
      specialize (HGamma _ Hz). tauto.
  - (* tcabs *)
    rename i into c. rename i0 into C.
    rewrite <- IHtf with T1 (update Gamma c (cpttype C)) 
                            (IdLS.IdSet.remove c mdlmems);
      try assumption.
    reflexivity.
    intros z Hz.
    destruct (beq_idP c z) as [Hcz | Hcz].
    + (* c = z *)
      subst. apply IdLS.Props.IdSetProps.Dec.F.remove_1. 
      reflexivity.
    + (* c <> z *)
      rewrite update_neq in Hz; try assumption.
      intros contra.
      apply IdLS.Props.IdSetProps.Dec.F.remove_3 in contra.
      specialize (HGamma _ Hz). tauto.
    + prove_no_model_names_as_bound_cvars_in_subterm.
    + prove_no_bound_cvar_in_subterm.
  - (* tlet *)
    rename i into x. 
    rewrite <- IHtf1 with T1 Gamma mdlmems;
      try (assumption 
           || prove_no_model_names_as_bound_cvars_in_subterm
           || prove_no_bound_cvar_in_subterm).
    rewrite <- IHtf2 
    with Tf (update Gamma x (tmtype T1)) (IdLS.IdSet.remove x mdlmems);
      try (assumption 
           || prove_no_model_names_as_bound_cvars_in_subterm
           || prove_no_bound_cvar_in_subterm).
    reflexivity.
    intros z Hz.
    destruct (beq_idP x z) as [Hxz | Hxz].
    + (* x = z *)
      subst. apply IdLS.Props.IdSetProps.Dec.F.remove_1. 
      reflexivity.
    + (* x <> z *)
      rewrite update_neq in Hz; try assumption.
      intros contra.
      apply IdLS.Props.IdSetProps.Dec.F.remove_3 in contra.
      specialize (HGamma _ Hz). tauto.
Qed.

Lemma qualify_model_members'_preserves_term_in_empty :
  forall (CTbl : cptcontext) (MTbl : mdlcontext) M
         (tf : tm) (Tf : ty) mdlmems,
    (* [tf] has type [Tf] *)
    CTbl $ MTbl ; ctxempty |- tf \in Tf ->
    (* term does not contain concept vars named as model names *)
    no_model_names_as_bound_cvars_in_term MTbl tf ->
    (* M in MTbl *)
    (exists MT, IdLPM.IdMap.find M MTbl = Some MT) ->
    let tf' := qualify_model_members' M mdlmems tf in 
    tf = tf'.
Proof.
  intros CTbl MTbl M tf Tf mdlmems HT Hcvars (*HninM HtfM*) HfindM.
  apply qualify_model_members'_preserves_term_in_empty'
  with CTbl MTbl Tf ctxempty;
    try assumption.
  intros x contra. 
  unfold ctxempty in contra. rewrite apply_empty in contra.
  exfalso. apply contra. reflexivity.
  destruct HfindM as [MT HfindM].
  intros contra. 
  unfold no_model_names_as_bound_cvars_in_term in Hcvars.
  apply Hcvars. exists M. split.
  assumption. unfold IdLPM.IdMap.In.
  eexists. rewrite IdMapProps.F.find_mapsto_iff. eassumption.
Qed.


Lemma in_keys_of_elements :
  forall (V : Type) (k : id) (m : id_map V),
    In k (map fst (IdLPM.IdMap.elements m)) ->
    exists v, In (k, v) (IdLPM.IdMap.elements m).
Proof.
  intros V k m. 
  induction (IdLPM.IdMap.elements m) as [| km elems' IHelems'].
  simpl; intros contra. contradiction.
  (* km :: elems' *)
  intros Hin. simpl in *.
  destruct Hin as [Hin | Hin].
  - destruct km as [k' v'].
    simpl in *. subst.
    exists v'. left. reflexivity.
  - apply IHelems' in Hin. destruct Hin as [v Hin].
    exists v. right. assumption.
Qed.

Lemma in_set_of_keys__in_map :
  forall (V : Type) (x : id) (m : id_map V),
    IdLS.IdSet.In  x (set_of_keys m) ->
    IdLPM.IdMap.In x m.
Proof.
  unfold set_of_keys.
  intros V x m Hin.
  apply IdLS.Props.in_set_from_list__in_list in Hin.
  apply in_keys_of_elements in Hin.
  destruct Hin as [v Hin].
  apply IdMapProps.F.elements_in_iff.
  exists v. apply SetoidList.In_InA.
  apply IdMapProps.eqke_equiv. assumption.
Qed.  

Lemma pair_in_list__value_in_fst :
  forall X Y x y (ps : list (X * Y)),
    List.In (x, y) ps ->
    List.In x (map fst ps).
Proof.
  intros X Y x y ps. 
  induction ps as [| p ps' IHps'];
    intros Hin.
  inversion Hin.
  destruct p as [x' y']. simpl in Hin.
  destruct Hin as [Hin | Hin].
  - inversion Hin. subst. 
    simpl. left. reflexivity.
  - simpl. right.
    apply IHps'. assumption.
Qed.

Lemma in_map__in_set_of_keys :
  forall (V : Type) (x : id) (m : id_map V),
    IdLPM.IdMap.In x m ->
    IdLS.IdSet.In  x (set_of_keys m).
Proof.
  unfold set_of_keys.
  intros V x m Hin.
  apply IdLS.Props.in_list__in_set_from_list.
  apply IdMapProps.F.elements_in_iff in Hin.
  destruct Hin as [v Hin].
  rewrite SetoidList.InA_alt in Hin. destruct Hin as [[x' v'] [Heq Hin]].
  unfold IdLPM.IdMap.eq_key_elt in Heq. simpl in Heq.
  inversion Heq. subst.
  apply pair_in_list__value_in_fst with v'. assumption.
Qed.


(** 
We need something to prove typing of model members.
*)

Lemma fold_left_members_ok__inital_prop :
  forall CTbl MTbl mdlnames Cbody pnds P cl,
    fst
      (fold_left
         (fun (okAndCl : Prop * context) (dt : id * tm) =>
            let (ok, cl) := okAndCl in
            (let (nm, d) := dt in
             model_member_valid CTbl MTbl mdlnames Cbody cl nm d /\ ok,
             let (nm, _) := dt in
             match find_ty nm Cbody with
             | Some tp => update cl nm (tmtype tp)
             | None => cl
             end))
         pnds
         (P, cl)) ->
    P.
Proof.
  intros CTbl MTbl mdlnames Cbody pnds.
  induction pnds as [| pnd pnds' IHpnds'];
    intros P cl H.
  simpl in *. assumption.
  (* pnds = pnd :: pnds' *)
  simpl in H. destruct pnd as [nm d].
  specialize (IHpnds' 
                (model_member_valid CTbl MTbl mdlnames Cbody cl nm d /\ P)
                (match find_ty nm Cbody with
                 | Some tp => update cl nm (tmtype tp)
                 | None => cl
                 end) 
             H).
  tauto.
Qed.

Lemma fold_left_members_ok__last_cl_includes_cl :
  forall CTbl MTbl mdlnames Cbody pnds P cl okF clF,
    (okF, clF)
    = (fold_left
         (fun (okAndCl : Prop * context) (dt : id * tm) =>
            let (ok, cl) := okAndCl in
            (let (nm, d) := dt in
             model_member_valid CTbl MTbl mdlnames Cbody cl nm d /\ ok,
             let (nm, _) := dt in
             match find_ty nm Cbody with
             | Some tp => update cl nm (tmtype tp)
             | None => cl
             end))
         pnds
         (P, cl)) ->
    okF ->
    (~ exists f, cl f <> None /\ List.In f (map fst pnds)) ->
    List.NoDup (map fst pnds) ->
    forall f Tf,
      cl  f = Some Tf ->
      clF f = Some Tf.
Proof.
  intros CTbl MTbl mdlnames Cbody pnds.
  induction pnds as [| [f tf] pnds' IHpnds'];
    intros P cl okF clF Heqfold HokF Hpndsok Hnodup.
  (* nil *)
  simpl in *. intros. inversion Heqfold. assumption.
  (* pnds = [f tf] :: pnds' *)
  simpl in *. 
  intros f' tf' Hmapsf'.
  specialize (IHpnds' 
                (model_member_valid CTbl MTbl mdlnames Cbody cl f tf /\ P)
                (match find_ty f Cbody with
                 | Some tp => update cl f (tmtype tp)
                 | None => cl
                 end)).
  specialize (IHpnds' okF clF Heqfold).
  apply IHpnds'; try assumption.
  - (* no bad name *)
    intros Hexcontra.
    destruct Hexcontra as [f0 [Hf0incl Hf0inpnds']].
    destruct (find_ty f Cbody) eqn:Heqfind.
    + destruct (beq_idP f f0) as [Hff0 | Hff0].
      * subst. inversion Hnodup. subst.
        apply H1 in Hf0inpnds'. contradiction.
      * apply Hpndsok. exists f0.
        split. rewrite update_neq in Hf0incl. 
        assumption. assumption. right. assumption.
    + apply Hpndsok. exists f0. 
      split. assumption. right. assumption.
  - (* no dup *)
    inversion Hnodup. subst. assumption.
  - (* mapsto *)
    destruct (find_ty f Cbody) eqn:Hfind.
    + destruct (beq_idP f f') as [Hff' | Hff'].
      * subst. exfalso. apply Hpndsok.
        exists f'. split. 
        intros contra. rewrite Hmapsf' in contra. inversion contra.
        left; reflexivity.
      * rewrite update_neq; assumption. 
    + assumption.
Qed.

Lemma fold_left_members_ok__no_model_names_in_last_cl :
  forall CTbl MTbl mdlnames Cbody pnds P cl okF clF,
    IdLS.IdSet.Subset (set_of_keys MTbl) mdlnames ->
    (okF, clF) 
    = (fold_left
         (fun (okAndCl : Prop * context) (dt : id * tm) =>
            let (ok, cl) := okAndCl in
            (let (nm, d) := dt in
             model_member_valid CTbl MTbl mdlnames Cbody cl nm d /\ ok,
             let (nm, _) := dt in
             match find_ty nm Cbody with
             | Some tp => update cl nm (tmtype tp)
             | None => cl
             end))
         pnds
         (P, cl)) ->
    okF ->
    no_model_names_as_cvars_in_Gamma MTbl cl ->
    no_model_names_as_cvars_in_Gamma MTbl clF.
Proof.
  intros CTbl MTbl mdlnames Cbody pnds.
  induction pnds as [| [f' tf'] pnds' IHpnds'];
    intros P cl okF clF Hsubset Heqfold HokF Hcl; simpl.
  (* pnds = nil *)
  simpl in *. inversion Heqfold. assumption.
  (* pnds = [f' tf'] :: pnds' *)
  simpl in Heqfold.
  specialize (IHpnds' 
                (model_member_valid CTbl MTbl mdlnames Cbody cl f' tf' /\ P)
                (match find_ty f' Cbody with
                 | Some tp => update cl f' (tmtype tp)
                 | None => cl
                 end)
                okF clF Hsubset Heqfold HokF).
  apply IHpnds'.
 - (* no model names *)
   destruct (find_ty f' Cbody) eqn:Heqfind; try assumption.
   unfold no_model_names_as_cvars_in_Gamma.
   intros M [HMfind HMin].
   destruct HMfind as [C HMfind].
   destruct (beq_idP f' M) as [Hf'M | Hf'M].
   + subst. rewrite update_eq in HMfind.
     inversion HMfind.
   + rewrite update_neq in HMfind; try assumption.
     unfold no_model_names_as_cvars_in_Gamma in Hcl.
     specialize (Hcl M).
     apply Hcl. split.
     exists C; assumption. assumption.
Qed.

Lemma fold_left_members_ok__ok_in_last_cl' :
  forall CTbl MTbl mdlnames Cbody pnds P cl okF clF,
    IdLS.IdSet.Subset (set_of_keys MTbl) mdlnames ->
    (okF, clF) 
    = (fold_left
         (fun (okAndCl : Prop * context) (dt : id * tm) =>
            let (ok, cl) := okAndCl in
            (let (nm, d) := dt in
             model_member_valid CTbl MTbl mdlnames Cbody cl nm d /\ ok,
             let (nm, _) := dt in
             match find_ty nm Cbody with
             | Some tp => update cl nm (tmtype tp)
             | None => cl
             end))
         pnds
         (P, cl)) ->
    okF ->
    no_model_names_as_cvars_in_Gamma MTbl cl ->
    (~ exists f, cl f <> None /\ List.In f (map fst pnds)) ->
    List.NoDup (map fst pnds) ->
    forall f tf,
      List.In (f, tf) pnds ->
      model_member_valid CTbl MTbl mdlnames Cbody clF f tf.
Proof.
  intros CTbl MTbl mdlnames Cbody pnds.
  induction pnds as [| [f' tf'] pnds' IHpnds'];
    intros P cl okF clF Hsubset Heqfold HokF Hmdlsincl
           Hpnds Hnodup; simpl.
  (* pnds = nil *)
  intros. contradiction.
  (* pnds = [f' tf'] :: pnds' *)
  intros f tf Hin.
  destruct Hin as [Hin | Hin].
  - (* f=tf in head *)
    inversion Hin. subst. clear Hin.
    simpl in Heqfold.
    assert (HeqOk : okF = fst (
          fold_left
              (fun (okAndCl : Prop * context) (dt : id * tm) =>
               let (ok, cl) := okAndCl in
               (let (nm, d) := dt in
                model_member_valid CTbl MTbl mdlnames Cbody cl nm d /\ ok,
               let (nm, _) := dt in
               match find_ty nm Cbody with
               | Some tp => update cl nm (tmtype tp)
               | None => cl
               end)) pnds'
              (model_member_valid CTbl MTbl mdlnames Cbody cl f tf /\ P,
              match find_ty f Cbody with
              | Some tp => update cl f (tmtype tp)
              | None => cl
              end))).
    { rewrite surjective_pairing in Heqfold.
      inversion Heqfold. reflexivity. }
    assert (Hok : fst
            (fold_left
               (fun (okAndCl : Prop * context) (dt : id * tm) =>
                let (ok, cl) := okAndCl in
                (let (nm, d) := dt in
                 model_member_valid CTbl MTbl mdlnames Cbody cl nm d /\ ok,
                let (nm, _) := dt in
                match find_ty nm Cbody with
                | Some tp => update cl nm (tmtype tp)
                | None => cl
                end)) pnds'
               (model_member_valid CTbl MTbl mdlnames Cbody cl f tf /\ P,
               match find_ty f Cbody with
               | Some tp => update cl f (tmtype tp)
               | None => cl
               end))).
    { subst. assumption. }
    pose proof (fold_left_members_ok__inital_prop 
                  _ _ _ _ _ _ _ Hok) as HfOk'. 
    clear Hok. clear HeqOk.
    destruct HfOk' as [HfOk' _].
    (* model_member_valid *)
    unfold model_member_valid.
    unfold model_member_valid in HfOk'.
    destruct HfOk' as [Tf [Hfindf [Hcvarstf Hhas_type]]].
    exists Tf. repeat (split; try assumption).
    (* try to prove that for bigger context it's still Ok *)
    apply context_weakening with (Gamma := cl).
    + assumption.
    + (* no model names as bound cvars *)
      unfold no_bound_cvar_names_in_term in Hcvarstf.
      unfold no_model_names_as_bound_cvars_in_term.
      intros contra.
      destruct contra as [z [Hzintf HzinMT]].
      specialize (Hcvarstf z).
      apply Hcvarstf.
      unfold IdLS.IdSet.Subset in Hsubset.
      apply Hsubset.
      apply in_map__in_set_of_keys.
      assumption. assumption.
    + (* clF preserves cl *)
      intros x Hxin.
      pose proof (fold_left_members_ok__last_cl_includes_cl 
                    CTbl MTbl mdlnames Cbody)
        as Htyping.
      specialize (Htyping pnds' _ _ _ _ Heqfold HokF).
      (* cl good *)
      assert (Hcl : ~
                      (exists f0 : id,
                          match find_ty f Cbody with
                          | Some tp => update cl f (tmtype tp)
                          | None => cl
                          end f0 <> None /\ In f0 (map fst pnds'))).
      { intros [f0 [Hf0 Hf0in]].
        destruct (find_ty f Cbody) eqn:Heqfind.
        * (* upd cl *)
          destruct (beq_idP f f0) as [Hff0 | Hff0].
          ** subst. inversion Hnodup.
             subst. apply H1 in Hf0in. contradiction.
          ** apply Hpnds.
             rewrite update_neq in Hf0; try assumption.
             exists f0. split. assumption.
             simpl. right. assumption.
        * apply Hpnds.
          exists f0. split. assumption.
          simpl. right. assumption. }
      specialize (Htyping Hcl). clear Hcl.
      inversion Hnodup; subst.
      specialize (Htyping H2).
      destruct (cl x) eqn:Heqclx.
      * apply Htyping.
        destruct (find_ty f Cbody) eqn:Heqfind.
        ** destruct (beq_idP f x) as [Hfx | Hfx].
           ++ subst.
              exfalso. apply Hpnds.
              exists x. split. rewrite Heqclx. assumption.
              simpl. left. reflexivity.
           ++ rewrite update_neq; assumption.
        ** assumption.
      * assert (Hrefl : @None ctxvarty = None) by reflexivity.
        apply Hxin in Hrefl. contradiction.
    + (* no model names as cvars clF *)
      apply fold_left_members_ok__no_model_names_in_last_cl
      with CTbl mdlnames Cbody ((f, tf) :: pnds')
           P cl okF;
        try assumption.
  - (* f=tf in pnds' *)
    simpl in Heqfold.
    apply IHpnds' 
    with (model_member_valid CTbl MTbl mdlnames Cbody cl f' tf' /\ P)
         (match find_ty f' Cbody with
          | Some tp => update cl f' (tmtype tp)
          | None => cl
          end)
         okF; try assumption.
    + (* no model names *)
      destruct (find_ty f' Cbody) eqn:Heqfind.
      * unfold no_model_names_as_cvars_in_Gamma.
        intros M [[C HfindM] HinMT].
        destruct (beq_idP f' M) as [Hf'M | Hf'M].
        ** subst. rewrite update_eq in HfindM.
           inversion HfindM.
        ** rewrite update_neq in HfindM.
           unfold no_model_names_as_cvars_in_Gamma in Hmdlsincl.
           specialize (Hmdlsincl M). apply Hmdlsincl.
           split. eexists; eassumption. assumption. assumption.
      * assumption.
    + (* f0 ok *)
      intros [f0 [Hf0cl Hf0pnds]].
      destruct (find_ty f') eqn:Heqfind.
      * destruct (beq_idP f' f0) as [Hf'f0 | Hf'f0].
        ** subst.
           inversion Hnodup; subst. 
           apply H1 in Hf0pnds. contradiction.
        ** rewrite update_neq in Hf0cl; try assumption.
           apply Hpnds. exists f0. split.
           assumption. simpl. right. assumption.
      * apply Hpnds. exists f0. split.
        assumption. simpl. right. assumption.
    + inversion Hnodup; subst. assumption.
Qed.

Lemma fold_left_members_ok__ok_in_last_cl :
  forall CTbl MTbl mdlnames Cbody pnds okF clF,
    IdLS.IdSet.Subset (set_of_keys MTbl) mdlnames ->
    (okF, clF) 
    = (fold_left
         (fun (okAndCl : Prop * context) (dt : id * tm) =>
            let (ok, cl) := okAndCl in
            (let (nm, d) := dt in
             model_member_valid CTbl MTbl mdlnames Cbody cl nm d /\ ok,
             let (nm, _) := dt in
             match find_ty nm Cbody with
             | Some tp => update cl nm (tmtype tp)
             | None => cl
             end))
         pnds
         (True, ctxempty)) ->
    okF ->
    List.NoDup (map fst pnds) ->
    forall f tf,
      List.In (f, tf) pnds ->
      model_member_valid CTbl MTbl mdlnames Cbody clF f tf.
Proof.
  intros CTbl MTbl mdlnames Cbody pnds okF clF.
  intros Hsubset Heqfold HokF Hnodup.
  intros f tf Hin.
  apply fold_left_members_ok__ok_in_last_cl' 
  with pnds True ctxempty okF; try assumption.
  (* ctxempty is good *)
  - unfold no_model_names_as_cvars_in_Gamma.
    intros M [[C contra] _]. 
    unfold ctxempty in contra. rewrite apply_empty in contra.
    inversion contra.
  (* ctxempty ok *)
  - intros [f0 [contra _]]. unfold ctxempty in contra.
    rewrite apply_empty in contra. tauto.
Qed.

Lemma fold_left_members_ok__last_Gamma_only_from_tmtypes' :
  forall CTbl MTbl mdlnames Cbody pnds P cl okF clF names,
    (okF, clF) 
    = (fold_left
         (fun (okAndCl : Prop * context) (dt : id * tm) =>
            let (ok, cl) := okAndCl in
            (let (nm, d) := dt in
             model_member_valid CTbl MTbl mdlnames Cbody cl nm d /\ ok,
             let (nm, _) := dt in
             match find_ty nm Cbody with
             | Some tp => update cl nm (tmtype tp)
             | None => cl
             end))
         pnds
         (P, cl)) ->
    okF ->
    (forall x, List.In x (map fst pnds) -> List.In x names) ->
    (forall x, 
      cl x <> None ->
      exists Tx, cl x = Some (tmtype Tx)
                 /\ List.In x names
                 /\ find_ty x Cbody = Some Tx) ->
    forall x, 
      clF x <> None ->
      exists Tx, clF x = Some (tmtype Tx)
                 /\ List.In x names
                 /\ find_ty x Cbody = Some Tx.
Proof.
  intros CTbl MTbl mdlnames Cbody pnds.
  induction pnds as [| [f' tf'] pnds' IHpnds'];
    intros P cl okF clF names Heqfold HokF Hnames HclOk; simpl.
  (* pnds = nil *)
  simpl in Heqfold. inversion Heqfold. subst.
  assumption.
  (* pnds = [f' tf'] pnds' *)
  simpl in Heqfold.
  specialize 
    (IHpnds' 
       (model_member_valid CTbl MTbl mdlnames Cbody cl f' tf' /\ P)
       (match find_ty f' Cbody with
        | Some tp => update cl f' (tmtype tp)
        | None => cl
        end)
       okF clF names Heqfold HokF).
  simpl in HclOk. 
  assert (Hnames' : forall x : id, In x (map fst pnds') -> In x names).
  { intros x Hxin. apply Hnames.
    simpl. right. assumption. }
  specialize (IHpnds' Hnames').
  apply IHpnds'.
  intros z Hnone.
  destruct (find_ty f' Cbody) eqn:Heqfind.
  + destruct (beq_idP f' z) as [Hf'z | Hf'z].
    * subst. exists t. split.
      rewrite update_eq. reflexivity.
      specialize (Hnames z). split; try assumption. 
      apply Hnames. simpl. left. reflexivity.
    * rewrite update_neq.
      rewrite update_neq in Hnone; try assumption.
      specialize (HclOk z Hnone). assumption. assumption.
  + specialize (HclOk z Hnone). assumption. 
Qed.

Lemma fold_left_members_ok__last_Gamma_only_from_tmtypes :
  forall CTbl MTbl mdlnames Cbody pnds okF clF,
    (okF, clF) 
    = (fold_left
         (fun (okAndCl : Prop * context) (dt : id * tm) =>
            let (ok, cl) := okAndCl in
            (let (nm, d) := dt in
             model_member_valid CTbl MTbl mdlnames Cbody cl nm d /\ ok,
             let (nm, _) := dt in
             match find_ty nm Cbody with
             | Some tp => update cl nm (tmtype tp)
             | None => cl
             end))
         pnds
         (True, ctxempty)) ->
    okF ->
    forall x, 
      clF x <> None ->
      exists Tx, clF x = Some (tmtype Tx)
                 /\ List.In x (map fst pnds)
                 /\ find_ty x Cbody = Some Tx.
Proof.
  intros. 
  apply fold_left_members_ok__last_Gamma_only_from_tmtypes'
  with CTbl MTbl mdlnames pnds True ctxempty okF;
    try assumption.
  - intros z Hz. assumption.
  - intros z contra. unfold ctxempty in contra.
    rewrite apply_empty in contra. tauto.
Qed.


(* %%% *)
Lemma qualify_model_members_preserves_typing_for_good_Gamma :
  forall (CTbl : cptcontext) (MTbl : mdlcontext)
         (Gamma : context) (tf : tm) (Tf : ty)
         (C : id) Cbody M Mbody,
    (* [tf] has type [Tf] *)
    CTbl $ MTbl ; Gamma |- tf \in Tf ->
    (* term does not contain concept vars named as model names *)
    no_model_names_as_bound_cvars_in_term MTbl tf ->
    (* we work with a valid concept *)
    IdLPM.IdMap.find C CTbl = Some (CTdef Cbody) ->
    (* all names in Gamma are to be qualified *)
    (forall x, Gamma x <> None ->
               exists Tx, Gamma x = Some (tmtype Tx)
                          /\ IdLPM.IdMap.In x Mbody) ->
    (* names we qualify appear in concept and consistent with Gamma *)
    (forall x, 
        IdLPM.IdMap.In x Mbody -> 
        exists Tx, 
          IdLPM.IdMap.find x Cbody = Some Tx
          /\ (Gamma x <> None -> Gamma x = Some (tmtype Tx))) ->
    IdLPM.IdMap.find M MTbl = Some (MTdef C Mbody) ->
    let tf'   := qualify_model_members M Mbody tf in 
    CTbl $ MTbl ; ctxempty |- tf' \in Tf.
Proof.
  intros CTbl MTbl Gamma tf Tf C Cbody M Mbody.
  intros HT HMTtf HfindC HGamma Hmems (*Hnin HMnin*) HMfind.
  unfold qualify_model_members.
  apply qualify_model_members'_preserves_typing_for_good_Gamma
  with Gamma C Cbody Mbody; try assumption.
  - (* Gamma is good *)
    intros x Hnone.
    specialize (HGamma x Hnone).
    destruct HGamma as [Tx [HeqGamma Hxin]].
    exists Tx. split; try assumption.
    apply in_map__in_set_of_keys; assumption.
  - (* Cbody *)
    intros x HinMbody. 
    apply in_set_of_keys__in_map in HinMbody.
    specialize (Hmems x HinMbody). assumption.
Qed.


Lemma value_in_fst__pair_in_list:
  forall (X Y : Type) (x : X) (ps : list (X * Y)),
    In x (map fst ps) -> 
    exists (y : Y), In (x, y) ps.
Proof.
  intros X Y x ps. induction ps as [| [x' y'] ps' IHps'].
  - intros. inversion H.
  - intros H. simpl in H. destruct H as [H | H].
    + subst. simpl.
      exists y'. left. reflexivity.
    + apply IHps' in H. destruct H as [y H].
      exists y. simpl. right. assumption.
Qed.

Lemma in_list__in_map_namedef_to_pair :
  forall nds f tf,
    List.In (nm_def f tf) nds ->
    In (f, tf) (map namedef_to_pair nds).
Proof.
  intros nds. induction nds as [| [n d] nds' IHnds'].
  - intros. inversion H.
  - intros f tf Hin. simpl in *.
    destruct Hin as [Hin | Hin].
    + inversion Hin. subst.
      left. reflexivity.
    + right. apply IHnds'. assumption.
Qed.


Lemma qualify_model_members_preserves_typing_in_empty_context:
  forall CTbl MTbl mdlnames Cbody pnds okF clF C Mbody M,
    IdLS.IdSet.Subset (set_of_keys MTbl) mdlnames ->
    (okF, clF) 
    = (fold_left
         (fun (okAndCl : Prop * context) (dt : id * tm) =>
            let (ok, cl) := okAndCl in
            (let (nm, d) := dt in
             model_member_valid CTbl MTbl mdlnames Cbody cl nm d /\ ok,
             let (nm, _) := dt in
             match find_ty nm Cbody with
             | Some tp => update cl nm (tmtype tp)
             | None => cl
             end))
         pnds
         (True, ctxempty)) ->
    okF ->
    List.NoDup (map fst pnds) ->
    IdLPM.IdMap.find C CTbl = Some (CTdef Cbody) ->
    IdLPM.eq_list_map pnds Mbody ->
    IdLPM.IdMap.find M MTbl = Some (MTdef C Mbody) ->
    forall f tf,
      List.In (f, tf) pnds ->
      exists Tf,
        find_ty f Cbody = Some Tf
        /\
        CTbl $ MTbl ; ctxempty |- (qualify_model_members M Mbody tf) \in Tf.
Proof.
  intros CTbl MTbl mdlnames Cbody pnds okF clF C Mbody M.
  intros Hsubset Heqfold HokF Hnodup HfindC HMbody (*HMinMdls HMinMT*) HfindM.
  pose proof (fold_left_members_ok__ok_in_last_cl) as HtfOkinclF.
  specialize (HtfOkinclF CTbl MTbl mdlnames Cbody pnds okF clF).
  specialize (HtfOkinclF Hsubset Heqfold HokF Hnodup).
  (* go to concrete member of pnds *)
  intros f tf Htfin.
  pose proof (HtfOkinclF f tf Htfin) as Hfvalid.
  unfold model_member_valid in Hfvalid.
  destruct Hfvalid as [Tf [Hffind [Htfvars HTtf]]].
  exists Tf. split. assumption. 
  (* qualify_model_members typing *)
  pose proof (qualify_model_members_preserves_typing_for_good_Gamma)
       as HTQMMtf.
  specialize (HTQMMtf CTbl MTbl clF tf Tf).
  specialize (HTQMMtf C Cbody M Mbody).
  specialize (HTQMMtf HTtf).
  apply HTQMMtf; try assumption;
    pose proof (fold_left_members_ok__last_Gamma_only_from_tmtypes)
    as HclFOk;
    specialize (HclFOk CTbl MTbl mdlnames Cbody pnds okF clF);
    specialize (HclFOk Heqfold HokF).
  - (* no_model_names_as_bound_cvars_in_term MTbl tf *)
    unfold no_model_names_as_bound_cvars_in_term.
    intros [M0 [HM0tf HM0MT]].
    unfold no_bound_cvar_names_in_term in Htfvars.
    specialize (Htfvars M0). unfold IdLS.IdSet.Subset in Hsubset.
    apply in_map__in_set_of_keys in HM0MT. specialize (Hsubset M0 HM0MT).
    specialize (Htfvars Hsubset). apply Htfvars.
    assumption.
  - (* all x in clF are good *)
    intros z Hnone. specialize (HclFOk z Hnone).
    destruct HclFOk as [Tz [HclFz [Hinz Hfind]]].
    exists Tz. split. assumption.
    unfold IdLPM.eq_list_map in HMbody.
    destruct HMbody as [_ [_ HMbodyforall]].
    rewrite Forall_forall in HMbodyforall.
    apply value_in_fst__pair_in_list in Hinz.
    destruct Hinz as [tz Hinz].
    specialize (HMbodyforall (z, tz) Hinz).
    simpl in HMbodyforall. unfold IdLPM.IdMap.In.
    exists tz. apply IdMapProps.F.find_mapsto_iff; assumption.
  - (* type in concept and clF consistent *)
    intros x Hxin. unfold IdLPM.IdMap.In in Hxin.
    destruct Hxin as [tx Htx].
    pose proof (IdLPM.Props.eq_list_map__iff _ _ _  HMbody x tx) as Htx'.
    rewrite <- Htx' in Htx.
    specialize (HtfOkinclF x tx Htx).
    unfold model_member_valid in HtfOkinclF.
    destruct HtfOkinclF as [Tx [Hfindx [HtxOk HTtx]]].
    exists Tx. split. assumption.
    intros HclF. specialize (HclFOk x HclF).
    destruct HclFOk as [Tx' [HTx' [Hin Hfind']]].
    rewrite Hfindx in Hfind'. inversion Hfind'. subst. clear Hfind'.
    assumption.
Qed.


Theorem model_welldefined__QMMs_have_types:
  forall CTbl MTbl mdlnames M C Mbody' Mbody,
    model_welldefined CTbl MTbl mdlnames (mdl_def M C Mbody') ->
    IdLPM.eq_list_map (map namedef_to_pair Mbody') Mbody ->
    IdLS.IdSet.Subset (set_of_keys MTbl) mdlnames ->
    IdLPM.IdMap.find M MTbl = Some (MTdef C Mbody) ->
    forall f tf, 
      List.In (nm_def f tf) Mbody' ->
      exists Cbody Tf,
        IdLPM.IdMap.find C CTbl = Some (CTdef Cbody)
        /\ IdLPM.IdMap.find f Cbody = Some Tf
        /\ (*let MTbl' := IdLPM.IdMap.add M (MTdef C Mbody) MTbl in*)
           CTbl $ MTbl ; ctxempty |- (qualify_model_members M Mbody tf) \in Tf.
Proof.
  intros CTbl MTbl mdlnames M C Mbody'.
  unfold model_welldefined.
    unfold MMdlMem_SinglePassImplMDefs.module_ok,
    MMdlMem_SinglePassImplMDefs.HelperD.MGM.module_ok,
    MMdlMem_SinglePassImplMDefs.HelperD.members_ok,
    MMdlMem_SinglePassImplMDefs.HelperD.MSP.members_ok,
    MMdlMem_SinglePassImplMDefs.HelperD.MSP.members_ok',
    MMdlMem_SinglePassImplMDefs.HelperD.MSP.process_dep_member,
    MMdlMem_SinglePassImplMBase.MD.ctxloc,
    MMdlMem_SinglePassImplMDefs.HelperD.update_prop,
    MMdlMem_DataLCIOkDef.is_ok,
    MMdlMem_SinglePassImplMDefs.HelperD.update_ctxloc,
    MMdlMem_SinglePassImplMBase.upd_ctxloc,
    MMdlMem_SinglePassImplMBase.ctxl_init,
    MMdlMem_SinglePassImplMDefs.HelperD.req_members_defined,
    MMdlMem_SinglePassImplMBase.members_to_define,
    MMdlMem_SinglePassImplMBase.id, MMdlMem_SinglePassImplMBase.MId.id,
    MMdlMem_SinglePassImplMDefs.HelperD.dt, MMdlMem_SinglePassImplMBase.MD.t.
    intros Mbody [Cbody HCbody] HeqMbody 
           Hsubset HfindM (*HMinMT HM*) f tf Hnmdef.
    destruct HCbody as [HfindC Hmdl].
    destruct Hmdl as [[Hnodup HmdlOk] HCforall].
  remember (fold_left
                (fun (okAndCl : Prop * context) (dt : id * tm) =>
                 let (ok, cl) := okAndCl in
                 (let (nm, d) := dt in
                  model_member_valid CTbl MTbl mdlnames Cbody cl nm d /\ ok,
                 let (nm, _) := dt in
                 match find_ty nm Cbody with
                 | Some tp => update cl nm (tmtype tp)
                 | None => cl
                 end)) (map namedef_to_pair Mbody') (True, ctxempty))
      as memsok.
  destruct memsok as [okF clF].
  remember (fst
             (fold_left
                (fun (okAndCl : Prop * context) (dt : id * tm) =>
                 let (ok, cl) := okAndCl in
                 (let (nm, d) := dt in
                  model_member_valid CTbl MTbl mdlnames Cbody cl nm d /\ ok,
                 let (nm, _) := dt in
                 match find_ty nm Cbody with
                 | Some tp => update cl nm (tmtype tp)
                 | None => cl
                 end)) (map namedef_to_pair Mbody') (True, ctxempty)))
    as okF'.
  assert (okF' = okF) as HeqokF.
  { rewrite surjective_pairing in Heqmemsok.
    inversion Heqmemsok. subst. reflexivity. }
  assert (HokF : okF').
  { subst. assumption. }
  rewrite -> HeqokF in HokF.
  pose proof (qualify_model_members_preserves_typing_in_empty_context)
      as HQMMtf.
  specialize (HQMMtf CTbl MTbl mdlnames Cbody 
                     (map namedef_to_pair Mbody') okF clF 
                     C Mbody M).
  specialize (HQMMtf Hsubset Heqmemsok HokF Hnodup).
  specialize (HQMMtf HfindC HeqMbody (*HMinMT*) HfindM).
  apply in_list__in_map_namedef_to_pair in Hnmdef.
  specialize (HQMMtf f tf Hnmdef).
  destruct HQMMtf as [Tf [Hfindf HTtf]].
  simpl in HTtf.
  exists Cbody Tf. repeat (split; try assumption).
Qed.


Lemma model_members_ok__mdlcontext_weakening' :
  forall CTbl MTbl MTbl' mdlnames Cbody pnds (P P' : Prop) cl,
    fst
      (fold_left
         (fun (okAndCl : Prop * context) (dt : id * tm) =>
            let (ok, cl) := okAndCl in
            (let (nm, d) := dt in
             model_member_valid CTbl MTbl mdlnames Cbody cl nm d /\ ok,
             let (nm, _) := dt in
             match find_ty nm Cbody with
             | Some tp => update cl nm (tmtype tp)
             | None => cl
             end)) 
         pnds (P, cl)) ->
    IdLS.IdSet.Subset (set_of_keys MTbl) mdlnames ->
    IdLS.IdSet.Subset (set_of_keys MTbl') mdlnames ->
    (forall (M' : IdLPM.IdMap.key) (C' : id) (mdl : id_tm_map),
        IdLPM.IdMap.find M' MTbl = Some (MTdef C' mdl) ->
        exists mdl' : id_tm_map,
          IdLPM.IdMap.find M' MTbl' = Some (MTdef C' mdl') /\
          IdLPM.IdMap.Equal mdl mdl') ->
    (P -> P') ->
    fst
      (fold_left
         (fun (okAndCl : Prop * context) (dt : id * tm) =>
            let (ok, cl) := okAndCl in
            (let (nm, d) := dt in
             model_member_valid CTbl MTbl' mdlnames Cbody cl nm d /\ ok,
             let (nm, _) := dt in
             match find_ty nm Cbody with
             | Some tp => update cl nm (tmtype tp)
             | None => cl
             end)) 
         pnds (P', cl)).
Proof.
  intros CTbl MTbl MTbl' mdlnames Cbody pnds.
  induction pnds as [| [f tf] pnds' IHpnds'].
  (* pnds = nil *)
  intros. simpl in *. apply H3. assumption.
  (* pnds = (f, tf) :: pnds' *)
  intros P P' cl Hfold Hsubset Hsubset' HMTbl' HPP'.
  simpl. simpl in Hfold.
  specialize (IHpnds' 
                (model_member_valid CTbl MTbl mdlnames Cbody cl f tf /\ P)
                (model_member_valid CTbl MTbl' mdlnames Cbody cl f tf /\ P')
                (match find_ty f Cbody with
                 | Some tp => update cl f (tmtype tp)
                 | None => cl
                 end)).
  apply IHpnds'; try assumption.
  unfold model_member_valid.
  intros [[T [Hfind [Hcvars HT]]] HP].
  split.
  - exists T. repeat (split; try assumption).
    apply mdlcontext_weakening with MTbl; assumption.
  - apply HPP'; assumption.
Qed.

Lemma model_members_ok__mdlcontext_weakening :
  forall CTbl MTbl MTbl' mdlnames Cbody pnds,
    fst
      (fold_left
         (fun (okAndCl : Prop * context) (dt : id * tm) =>
            let (ok, cl) := okAndCl in
            (let (nm, d) := dt in
             model_member_valid CTbl MTbl mdlnames Cbody cl nm d /\ ok,
             let (nm, _) := dt in
             match find_ty nm Cbody with
             | Some tp => update cl nm (tmtype tp)
             | None => cl
             end)) 
         pnds (True, ctxempty)) ->
    IdLS.IdSet.Subset (set_of_keys MTbl) mdlnames ->
    IdLS.IdSet.Subset (set_of_keys MTbl') mdlnames ->
    (forall (M' : IdLPM.IdMap.key) (C' : id) (mdl : id_tm_map),
        IdLPM.IdMap.find M' MTbl = Some (MTdef C' mdl) ->
        exists mdl' : id_tm_map,
          IdLPM.IdMap.find M' MTbl' = Some (MTdef C' mdl') /\
          IdLPM.IdMap.Equal mdl mdl') ->
    fst
      (fold_left
         (fun (okAndCl : Prop * context) (dt : id * tm) =>
            let (ok, cl) := okAndCl in
            (let (nm, d) := dt in
             model_member_valid CTbl MTbl' mdlnames Cbody cl nm d /\ ok,
             let (nm, _) := dt in
             match find_ty nm Cbody with
             | Some tp => update cl nm (tmtype tp)
             | None => cl
             end)) 
         pnds (True, ctxempty)).
Proof.
  intros CTbl MTbl MTbl' mdlnames Cbody pnds.
  intros Hfold Hsubset Hsubset' HMTbl'.
  apply model_members_ok__mdlcontext_weakening' with MTbl True;
    try assumption. tauto.
Qed.

Lemma model_welldefined__mdlcontext_weakening :
  forall CTbl MTbl MTbl' mdlnames M C Mbody' Mbody,
    model_welldefined CTbl MTbl mdlnames (mdl_def M C Mbody') ->
    IdLPM.eq_list_map (map namedef_to_pair Mbody') Mbody ->
    IdLS.IdSet.Subset (set_of_keys MTbl) mdlnames ->
    IdLS.IdSet.Subset (set_of_keys MTbl') mdlnames ->
    (forall (M' : IdLPM.IdMap.key) (C' : id) (mdl : id_tm_map),
        IdLPM.IdMap.find M' MTbl = Some (MTdef C' mdl) ->
        exists mdl' : id_tm_map,
          IdLPM.IdMap.find M' MTbl' = Some (MTdef C' mdl') /\
          IdLPM.IdMap.Equal mdl mdl') ->
    model_welldefined CTbl MTbl' mdlnames (mdl_def M C Mbody').
Proof.
  intros CTbl MTbl MTbl' mdlnames M C Mbody'.
  unfold model_welldefined.
    unfold MMdlMem_SinglePassImplMDefs.module_ok,
    MMdlMem_SinglePassImplMDefs.HelperD.MGM.module_ok,
    MMdlMem_SinglePassImplMDefs.HelperD.members_ok,
    MMdlMem_SinglePassImplMDefs.HelperD.MSP.members_ok,
    MMdlMem_SinglePassImplMDefs.HelperD.MSP.members_ok',
    MMdlMem_SinglePassImplMDefs.HelperD.MSP.process_dep_member,
    MMdlMem_SinglePassImplMBase.MD.ctxloc,
    MMdlMem_SinglePassImplMDefs.HelperD.update_prop,
    MMdlMem_DataLCIOkDef.is_ok,
    MMdlMem_SinglePassImplMDefs.HelperD.update_ctxloc,
    MMdlMem_SinglePassImplMBase.upd_ctxloc,
    MMdlMem_SinglePassImplMBase.ctxl_init,
    MMdlMem_SinglePassImplMDefs.HelperD.req_members_defined,
    MMdlMem_SinglePassImplMBase.members_to_define,
    MMdlMem_SinglePassImplMBase.id, MMdlMem_SinglePassImplMBase.MId.id,
    MMdlMem_SinglePassImplMDefs.HelperD.dt, MMdlMem_SinglePassImplMBase.MD.t.
    intros Mbody [Cbody HCbody] HeqMbody 
           Hsubset Hsubset' HMTbl'.
    destruct HCbody as [HfindC Hmdl].
    destruct Hmdl as [[Hnodup HmdlOk] HCforall].
    exists Cbody; repeat split; try assumption.
    apply model_members_ok__mdlcontext_weakening with MTbl;
      try assumption.
Qed.

Lemma modelsec_members_ok__inital_prop :
  forall CTbl mdlnames mds P cl,
    fst
      (fold_left
          (fun (okAndCl : Prop * mdlcontext) (dt : id * modeldef) =>
             let (ok, cl) := okAndCl in
             (model_welldefined CTbl cl mdlnames (snd dt) /\ ok,
              let (_, d) := dt in
              match d with
              | mdl_def Mname C Mbody =>
                IdLPM.IdMap.add 
                  Mname
                  (MTdef C (IdLPM.map_from_list (map namedef_to_pair Mbody)))
                  cl
              end)) 
          mds 
          (P, cl)) ->
    P.
Proof.
  intros CTbl mdlnames mds.
  induction mds as [| [M Mdef] mds' IHmds'];
    intros P cl H.
  simpl in *. assumption.
  (* mds = (M, Mdef) :: mds' *)
  simpl in H.
  specialize (IHmds' 
                (model_welldefined CTbl cl mdlnames Mdef /\ P)
                match Mdef with
                | mdl_def Mname C Mbody =>
                  IdLPM.IdMap.add 
                    Mname
                    (MTdef C (IdLPM.map_from_list (map namedef_to_pair Mbody))) 
                    cl
                end 
             H).
  tauto.
Qed.

Lemma model_welldefined__NoDup :
  forall CTbl MTbl mdlnames M C Mbody,
    model_welldefined CTbl MTbl mdlnames (mdl_def M C Mbody) ->
    NoDup (map fst (map namedef_to_pair Mbody)).
Proof.
  intros CTbl MTbl mdlnames M C Mbody H.
  unfold model_welldefined in H.
  destruct H as [Cbody [HfindC Hmodule_ok]].
  unfold MMdlMem_SinglePassImplMDefs.module_ok in Hmodule_ok.
  unfold MMdlMem_SinglePassImplMDefs.HelperD.MGM.module_ok in Hmodule_ok.
  destruct Hmodule_ok as [[Hnodup _] _].
  assumption.
Qed.

Lemma modelsec_members_ok_last_cl_in_mdlnames :
  forall CTbl mdlnames mds P cl okF clF,
    (okF, clF) 
    = fold_left
        (fun (okAndCl : Prop * mdlcontext) (dt : id * modeldef) =>
           let (ok, cl) := okAndCl in
           (model_welldefined CTbl cl mdlnames (snd dt) /\ ok,
            let (_, d) := dt in
            match d with
            | mdl_def Mname C Mbody =>
              IdLPM.IdMap.add 
                Mname
                (MTdef C (IdLPM.map_from_list (map namedef_to_pair Mbody)))
                cl
            end)) mds
        (P, cl) ->
    okF ->
    IdLS.IdSet.Subset (set_of_keys cl) mdlnames ->
    (forall x : id,
         In x (map modeldef__get_name (map snd mds)) ->
         IdLS.IdSet.In x mdlnames) ->
    IdLS.IdSet.Subset (set_of_keys clF) mdlnames.
Proof.
  intros CTbl mdlnames mds.
  induction mds as [| [Mid Mdef] mds' IHmds'].
  (* mds = nil *)
  intros. simpl in *. inversion H. subst. assumption.
  (* mds = Mdef :: mds' *)
  intros P cl okF clF Heqfold.
  intros HokF Hsubset Hmds.
  simpl in Heqfold.
  specialize (IHmds' 
                (model_welldefined CTbl cl mdlnames Mdef /\ P)
                (match Mdef with
                 | mdl_def Mname C Mbody =>
                   IdLPM.IdMap.add Mname
                    (MTdef C (IdLPM.map_from_list (map namedef_to_pair Mbody)))
                    cl
                 end)
                okF clF Heqfold HokF).
  apply IHmds'. 
  destruct Mdef as [Mname C Mbody].
  unfold IdLS.IdSet.Subset.
  intros M' HM'in. apply in_set_of_keys__in_map in HM'in.
  rewrite IdMapProps.F.add_in_iff in HM'in. 
  destruct HM'in as [HM'in | HM'in].
  - unfold IdUOTOrig.eq in *. subst.
    apply Hmds. simpl. left. reflexivity.
  - unfold IdLS.IdSet.Subset in Hsubset.
    apply Hsubset. 
    apply in_map__in_set_of_keys. assumption.
  - intros M Hin. apply Hmds.
    simpl. right. assumption.
Qed.

Lemma modelsec_members_ok__cl_in_last_cl :
  forall CTbl mdlnames mds P cl okF clF,
    (okF, clF) 
    =  (fold_left
          (fun (okAndCl : Prop * mdlcontext) (dt : id * modeldef) =>
             let (ok, cl) := okAndCl in
             (model_welldefined CTbl cl mdlnames (snd dt) /\ ok,
              let (_, d) := dt in
              match d with
              | mdl_def Mname C Mbody =>
                IdLPM.IdMap.add 
                  Mname
                  (MTdef C (IdLPM.map_from_list (map namedef_to_pair Mbody)))
                  cl
              end)) 
          mds 
          (P, cl)) ->
    okF ->
    (forall M, IdLPM.IdMap.In M cl ->
               ~ List.In M (map modeldef__get_name (map snd mds))) ->
    NoDup (map modeldef__get_name (map snd mds)) ->
    forall M Mdef, 
      IdLPM.IdMap.find M cl = Some Mdef ->
      IdLPM.IdMap.find M clF = Some Mdef.
Proof.
  intros CTbl mdlnames mds.
  induction mds as [| [M' M'def] mds' IHmds'].
  intros. simpl in *. inversion H. subst. assumption.
  (* mds = (M', M'def) :: mds' *)
  intros P cl okF clF Heqfold HokF Hmds Hnodup.
  simpl in Heqfold.
  specialize (IHmds'  
                (model_welldefined CTbl cl mdlnames M'def /\ P)
                (match M'def with
                 | mdl_def Mname C Mbody =>
                   IdLPM.IdMap.add
                     Mname
                     (MTdef C (IdLPM.map_from_list (map namedef_to_pair Mbody)))
                     cl
                 end)).
  specialize (IHmds' okF clF Heqfold HokF).
  clear Heqfold.
  destruct M'def as [M'name C M'body].
  intros M Mdef Hfind.
  destruct (beq_idP M M'name) as [HMM | HMM].
  - subst. exfalso.
    unfold not in Hmds. apply Hmds with M'name.
    + unfold IdLPM.IdMap.In. eexists. 
      apply IdMapProps.F.find_mapsto_iff. eassumption.
    + simpl. left. reflexivity.
  - apply IHmds'.
    + simpl in Hmds.
      intros M0 HM0in.
      rewrite IdMapProps.F.add_in_iff in HM0in.
      destruct HM0in as [HM0in | HM0in].
      * unfold IdUOTOrig.eq in *. subst.
        intros HM0mds'. simpl in Hnodup.
        inversion Hnodup; subst.    
        apply H1; assumption.
      * intros contra.
        specialize (Hmds _ HM0in). apply Hmds.
        right; assumption.
    + inversion Hnodup; assumption.
    + rewrite IdMapProps.F.add_neq_o; try assumption.
      intuition.
Qed.

Lemma modelsec_members_ok__model_welldefined_in_last_cl' :
  forall CTbl mdlnames mds P cl okF clF,
    (okF, clF) 
    =  (fold_left
          (fun (okAndCl : Prop * mdlcontext) (dt : id * modeldef) =>
             let (ok, cl) := okAndCl in
             (model_welldefined CTbl cl mdlnames (snd dt) /\ ok,
              let (_, d) := dt in
              match d with
              | mdl_def Mname C Mbody =>
                IdLPM.IdMap.add 
                  Mname
                  (MTdef C (IdLPM.map_from_list (map namedef_to_pair Mbody)))
                  cl
              end)) 
          mds 
          (P, cl)) ->
    okF ->
    IdLS.IdSet.Subset (set_of_keys cl) mdlnames ->
    (forall x, 
        List.In x (map modeldef__get_name (map snd mds)) -> 
        IdLS.IdSet.In x mdlnames) ->
    (forall M : IdLPM.IdMap.key,
        IdLPM.IdMap.In M cl ->
        ~ In M (map modeldef__get_name (map snd mds))) ->    
    NoDup (map modeldef__get_name (map snd mds)) ->
    forall M Mdef,
      List.In (M, Mdef) mds ->
      model_welldefined CTbl clF mdlnames Mdef.
Proof.
  intros CTbl mdlnames mds.
  induction mds as [| [M' M'def] mds' IHmds'].
  intros. simpl in *. contradiction.
  (* mds = (M', M'def) :: mds' *)
  intros P cl okF clF Heqfold HokF Hsubset Hmds Hclmds Hnodup.
  intros M Mdef Hin.
  pose proof (modelsec_members_ok_last_cl_in_mdlnames)
    as HclFmdlnames.
  specialize (HclFmdlnames CTbl mdlnames
                           ((M', M'def) :: mds') P cl okF clF
                           Heqfold HokF).
  specialize (HclFmdlnames Hsubset Hmds).
  pose proof (modelsec_members_ok__cl_in_last_cl)
    as HclFcl.
  specialize (HclFcl CTbl mdlnames
                     ((M', M'def) :: mds') P cl okF clF
                     Heqfold HokF).
  specialize (HclFcl Hclmds Hnodup).
  simpl in Heqfold.
  specialize (IHmds'  
                (model_welldefined CTbl cl mdlnames M'def /\ P)
                (match M'def with
                 | mdl_def Mname C Mbody =>
                   IdLPM.IdMap.add
                     Mname
                     (MTdef C (IdLPM.map_from_list (map namedef_to_pair Mbody)))
                     cl
                 end)).
  specialize (IHmds' okF clF Heqfold HokF).
  simpl in Hin.
  destruct Hin as [Hin | Hin].
  - (* (M, Mdef) is a head *)
    inversion Hin. subst. clear Hin.
    pose proof (modelsec_members_ok__inital_prop) as HMdefOk.
    specialize (HMdefOk CTbl mdlnames mds').
    specialize 
      (HMdefOk 
         (model_welldefined CTbl cl mdlnames Mdef /\ P)
         (match Mdef with
          | mdl_def Mname C Mbody =>
            IdLPM.IdMap.add 
              Mname
              (MTdef C (IdLPM.map_from_list (map namedef_to_pair Mbody)))
              cl
          end)).
    assert (Hbase : model_welldefined CTbl cl mdlnames Mdef).
    { apply HMdefOk. rewrite surjective_pairing in Heqfold.
      inversion Heqfold. subst. assumption. }
    destruct Mdef as [M' C Mbody'].
    apply model_welldefined__mdlcontext_weakening 
    with cl (IdLPM.map_from_list (map namedef_to_pair Mbody'));
      try assumption.
    + (* Mbody list_map eq *)
      apply IdLPMProps.eq_list_map_from_list.
      apply model_welldefined__NoDup with CTbl cl mdlnames M' C.
      assumption.
    + (* find mdl preserved *)
      intros M0 C0 mdl0. exists mdl0.
      split. apply HclFcl. assumption.
      apply IdMapProps.F.Equal_refl.
  - (* (M, Mdef) in mds' *)
    apply IHmds' with M; try assumption; clear Heqfold.
    + (* subset *)
      destruct M'def as [M'name C M'body].
      unfold IdLS.IdSet.Subset. intros M0 HinM0.
      apply in_set_of_keys__in_map in HinM0.
      rewrite IdMapProps.F.add_in_iff in HinM0.
      destruct HinM0 as [HinM0 | HinM0].
      * unfold IdUOTOrig.eq in *. subst.
        apply Hmds. simpl. left. reflexivity.
      * unfold IdLS.IdSet.Subset in Hsubset.
        apply Hsubset. 
        apply in_map__in_set_of_keys. assumption.
    + (* in mdlnames *)
      intros M0 HinM0. apply Hmds.
      simpl. right. assumption.
    + (* no intersection *)
      destruct M'def as [M'name C M'body].
      intros M0 HinM0.
      rewrite IdMapProps.F.add_in_iff in HinM0.
      destruct HinM0 as [HinM0 | HinM0].
      * unfold IdUOTOrig.eq in *. subst.
        intros contra. inversion Hnodup; subst.
        apply H1 in contra. contradiction.
      * intros Hinmds'. 
        unfold not in Hclmds; apply Hclmds with M0.
        assumption.
        simpl. right. assumption.
    + (* nodup *)
      inversion Hnodup; subst; assumption.
Qed.

Lemma modelsec_members_ok__model_welldefined_in_last_cl :
  forall CTbl mdlnames mds okF clF,
    (okF, clF) 
    =  (fold_left
          (fun (okAndCl : Prop * mdlcontext) (dt : id * modeldef) =>
             let (ok, cl) := okAndCl in
             (model_welldefined CTbl cl mdlnames (snd dt) /\ ok,
              let (_, d) := dt in
              match d with
              | mdl_def Mname C Mbody =>
                IdLPM.IdMap.add 
                  Mname
                  (MTdef C (IdLPM.map_from_list (map namedef_to_pair Mbody)))
                  cl
              end)) 
          mds 
          (True, mstempty)) ->
    okF ->
    (forall x, 
        List.In x (map modeldef__get_name (map snd mds)) -> 
        IdLS.IdSet.In x mdlnames) ->
    NoDup (map modeldef__get_name (map snd mds)) ->
    forall M Mdef,
      List.In (M, Mdef) mds ->
      model_welldefined CTbl clF mdlnames Mdef.
Proof.
  intros CTbl mdlnames mds okF clF Heqfold HokF.
  intros Hmds Hnodup.
  apply modelsec_members_ok__model_welldefined_in_last_cl'
  with True mstempty okF; try assumption.
  + unfold IdLS.IdSet.Subset; intros M contra; 
      unfold mstempty in contra;
      apply in_set_of_keys__in_map in contra;
      rewrite IdMapProps.F.empty_in_iff in contra; contradiction.
  + intros M contra; 
      unfold mstempty in contra.
    rewrite IdMapProps.F.empty_in_iff in contra; contradiction.
Qed.

Lemma modelsec_members_ok__exists_domain_of_Mbody' :
  forall CTbl mdlnames MDS mds P cl okF clF,
    (okF, clF) 
    =  (fold_left
          (fun (okAndCl : Prop * mdlcontext) (dt : id * modeldef) =>
             let (ok, cl) := okAndCl in
             (model_welldefined CTbl cl mdlnames (snd dt) /\ ok,
              let (_, d) := dt in
              match d with
              | mdl_def Mname C Mbody =>
                IdLPM.IdMap.add 
                  Mname
                  (MTdef C (IdLPM.map_from_list (map namedef_to_pair Mbody)))
                  cl
              end)) 
          mds 
          (P, cl)) ->
    okF ->
    (forall p, List.In p mds -> List.In p MDS) ->
    (forall (M C : id) Mbody, 
      IdLPM.IdMap.find M cl = Some (MTdef C Mbody) ->
      exists N (Mbody' : list namedef), 
        List.In (N, mdl_def M C Mbody') MDS) ->
    forall (M C : id) Mbody, 
      IdLPM.IdMap.find M clF = Some (MTdef C Mbody) ->
      exists N (Mbody' : list namedef), 
        List.In (N, mdl_def M C Mbody') MDS.
Proof.
  intros CTbl mdlnames MDS mds.
  induction mds as [| [M' M'def] mds' IHmds'].
  intros. simpl in *. inversion H; subst.
  apply H2 with Mbody; try assumption.
  (* mds = (M', M'def) :: mds' *)
  intros P cl okF clF Heqfold HokF. 
  intros Hmds (*Hnodup*) HMDS.
  intros M C Mbody Hfind.
  simpl in Heqfold.
  specialize 
    (IHmds' 
       (model_welldefined CTbl cl mdlnames M'def /\ P)
       (match M'def with
        | mdl_def Mname C Mbody =>
          IdLPM.IdMap.add 
            Mname
            (MTdef C (IdLPM.map_from_list (map namedef_to_pair Mbody)))
            cl
        end)
       okF clF
       Heqfold HokF).
  clear Heqfold.
  apply IHmds' with Mbody; try assumption.
  - (* in p mds' *) 
    intros p Hin. apply Hmds.
    simpl. right; assumption.
  - (* assumption on cl *)
    destruct M'def as [M1name C1 Mbody1].
    intros M0 C0 Mbody0 HM0find.
    rewrite <- IdMapProps.F.find_mapsto_iff in HM0find.
    rewrite IdMapProps.F.add_mapsto_iff in HM0find.
    destruct HM0find as [[HeqM0 Heqdef] | [HeqM0 Hcl]].
    + (* eq *)
      unfold IdUOTOrig.eq in HeqM0. subst.
      inversion Heqdef. subst. clear Heqdef.
      exists M' Mbody1. apply Hmds.
      simpl. left. reflexivity.
    + (* neq *)
      rewrite IdMapProps.F.find_mapsto_iff in Hcl.
      specialize (HMDS _ _ _ Hcl). assumption.
Qed.

Lemma modelsec_members_ok__exists_domain_of_Mbody :
  forall CTbl mdlnames mds okF clF,
    (okF, clF) 
    =  (fold_left
          (fun (okAndCl : Prop * mdlcontext) (dt : id * modeldef) =>
             let (ok, cl) := okAndCl in
             (model_welldefined CTbl cl mdlnames (snd dt) /\ ok,
              let (_, d) := dt in
              match d with
              | mdl_def Mname C Mbody =>
                IdLPM.IdMap.add 
                  Mname
                  (MTdef C (IdLPM.map_from_list (map namedef_to_pair Mbody)))
                  cl
              end)) 
          mds 
          (True, mstempty)) ->
    okF ->
    forall (M C : id) Mbody, 
      IdLPM.IdMap.find M clF = Some (MTdef C Mbody) ->
      exists N (Mbody' : list namedef), 
        List.In (N, mdl_def M C Mbody') mds.
Proof.
  intros CTbl mdlnames mds.
  intros okF clF Heqfold HokF. 
  intros M C Mbody Hfind.
  apply modelsec_members_ok__exists_domain_of_Mbody'
  with CTbl mdlnames mds True mstempty okF clF Mbody;
    try assumption.
  - intros; assumption.
  - intros M0 C0 Mbody0 HfindM0.
    unfold mstempty in HfindM0. rewrite IdMapProps.F.empty_o in HfindM0.
    inversion HfindM0.
Qed.

Remove Hints model_welldefined.

Lemma modelsec_members_ok__last_cl_equal_to' :
  forall CTbl mdlnames MSec mds P cl okF clF,
    mds = map modeldef_pair_with_id MSec ->
    (okF, clF) 
    =  (fold_left
          (fun (okAndCl : Prop * mdlcontext) (dt : id * modeldef) =>
             let (ok, cl) := okAndCl in
             (model_welldefined CTbl cl mdlnames (snd dt) /\ ok,
              let (_, d) := dt in
              match d with
              | mdl_def Mname C Mbody =>
                IdLPM.IdMap.add 
                  Mname
                  (MTdef C (IdLPM.map_from_list (map namedef_to_pair Mbody)))
                  cl
              end)) 
          mds 
          (P, cl)) ->
    okF ->
    (forall x, IdLPM.IdMap.In x cl ->
               ~ List.In x (map modeldef__get_name (map snd mds))) ->
    NoDup (map modeldef__get_name (map snd mds)) ->
    IdLPM.IdMap.Equal 
      clF 
      (IdLPM.HelperFuns.map_from_list' (map modeldef_to_pair_id_mty MSec) cl).
Proof.
  intros CTbl mdlnames MSec.
  induction MSec as [| [M C Mdef] MSec' IHMSec'].
  intros. simpl in *. subst. simpl in *. 
  inversion H0; subst. apply IdMapProps.F.Equal_refl.
  (* MSec = (M, C, Mdef) :: MSec' *)
  intros mds P cl okF clF Heqmds Heqfold HokF. 
  intros Hcl Hnodup.
  subst mds. simpl in Heqfold.
  replace (exists fnmtys : id_ty_map,
                  IdLPM.IdMap.find C CTbl = Some (CTdef fnmtys) /\
                  MMdlMem_SinglePassImplMDefs.module_ok 
                    (CTbl, cl, mdlnames) fnmtys (map namedef_to_pair Mdef))
  with (model_welldefined CTbl cl mdlnames (mdl_def M C Mdef))
    in Heqfold
    by reflexivity.
  assert (Htriv : map modeldef_pair_with_id MSec' 
                  = map modeldef_pair_with_id MSec')
    by reflexivity.
  specialize 
    (IHMSec' 
       (map modeldef_pair_with_id MSec')
       (model_welldefined CTbl cl mdlnames (mdl_def M C Mdef) /\ P)
       (IdLPM.IdMap.add 
          M (MTdef C (IdLPM.map_from_list (map namedef_to_pair Mdef))) cl)
       okF clF
       Htriv
       Heqfold HokF).
  clear Heqfold.
  simpl.
  apply IHMSec'. 
  - (* new cl ok *)
    intros x Hin. rewrite IdMapProps.F.add_in_iff in Hin.
    destruct Hin as [Hin | Hin].
    + (* x = M *)
      unfold IdUOTOrig.eq in Hin. subst.
      inversion Hnodup. subst. assumption.
    + (* x <> M *)
      intros contra. specialize (Hcl x Hin).
      apply Hcl. simpl. right. assumption.
  - (* nodup *)
    inversion Hnodup. assumption.
Qed.

Lemma modelsec_members_ok__last_cl_equal_to :
  forall CTbl mdlnames MSec mds okF clF,
    mds = map modeldef_pair_with_id MSec ->
    (okF, clF) 
    =  (fold_left
          (fun (okAndCl : Prop * mdlcontext) (dt : id * modeldef) =>
             let (ok, cl) := okAndCl in
             (model_welldefined CTbl cl mdlnames (snd dt) /\ ok,
              let (_, d) := dt in
              match d with
              | mdl_def Mname C Mbody =>
                IdLPM.IdMap.add 
                  Mname
                  (MTdef C (IdLPM.map_from_list (map namedef_to_pair Mbody)))
                  cl
              end)) 
          mds 
          (True, mstempty)) ->
    okF ->
    NoDup (map modeldef__get_name (map snd mds)) ->
    IdLPM.IdMap.Equal clF 
                      (IdLPM.map_from_list (map modeldef_to_pair_id_mty MSec)).
Proof.
  intros CTbl mdlnames MSec mds okF clF.
  intros Heqmds Heqfold HokF Hnodup.
  apply modelsec_members_ok__last_cl_equal_to'
  with CTbl mdlnames mds True okF; try assumption.
  (* empty *)
  intros x Hin. apply IdMapProps.F.empty_in_iff in Hin.
  contradiction.
Qed.

Lemma fst_map_modeldef_pair_with_id__modeldef__get_name_map_snd :
  forall MSec,
    (map fst (map modeldef_pair_with_id MSec))
    = (map modeldef__get_name (map snd (map modeldef_pair_with_id MSec))).
Proof.
  intros MSec. induction MSec as [| [M C Mbody'] MSec' IHMsec'].
  simpl. reflexivity.
  (* MSec = _ :: MSec' *)
  simpl. rewrite IHMsec'. reflexivity.
Qed.

Lemma map_fst__modeldef__get_name__nodup :
  forall MSec,
    NoDup (map fst (map modeldef_pair_with_id MSec)) ->
    NoDup (map modeldef__get_name (map snd (map modeldef_pair_with_id MSec))).
Proof.
  intros. 
  rewrite <- fst_map_modeldef_pair_with_id__modeldef__get_name_map_snd.
  assumption.
Qed.

(* %%%%% *)

Theorem qualify_model_members_preserves_typing :
  forall CTbl MTbl M C Mbody f Tf tf,
    mdlcontext_welldefined CTbl MTbl ->
    IdLPM.IdMap.find M MTbl = Some (MTdef C Mbody) ->
    CTbl $ MTbl; ctxempty |- tcinvk M f \in Tf ->
    find_tm f Mbody = Some tf ->                                       
    CTbl $ MTbl; ctxempty |- qualify_model_members M Mbody tf \in Tf.
Proof.
  intros CTbl MTbl M C Mbody f Tf tf.
  unfold mdlcontext_welldefined.
  intros [MSec [HMSecOk HMSecMTbl]].
  unfold modelsec_welldefined in HMSecOk.
  unfold MMdlDef_SinglePassMDefs.module_ok,
    MMdlDef_SinglePassMDefs.HelperD.MGM.module_ok,
    MMdlDef_SinglePassMDefs.HelperD.members_ok,
    MMdlDef_SinglePassMDefs.HelperD.MSP.members_ok,
    MMdlDef_SinglePassMDefs.HelperD.MSP.members_ok',
    MMdlDef_SinglePassMDefs.HelperD.MSP.process_dep_member,
    MMdlDef_SinglePassMDefs.HelperD.update_prop, 
    MMdlDef_SinglePassMDefs.HelperD.update_ctxloc,
    MMdlDef_SinglePassMBase.upd_ctxloc,
    MMdlDef_DataLCOkDef.is_ok,
    MMdlDef_SinglePassMBase.ctxl_init,
    MMdlDef_SinglePassMBase.MD.ctxloc,
    MMdlDef_SinglePassMBase.id,
    MMdlDef_SinglePassMBase.MId.id,
    MMdlDef_SinglePassMDefs.HelperD.dt,
    MMdlDef_SinglePassMBase.MD.t
    in HMSecOk.
  destruct HMSecOk as [HMSecnodup HMSecOk].
  intros HfindM HTMf Hfindf.
  (* typing of QMM *)
  pose proof (model_welldefined__QMMs_have_types) as HTQMMtf.
  remember (IdLPM.map_from_list (map modeldef_to_pair_id_mty MSec)) as MSecMap.
  specialize (HTQMMtf CTbl MTbl (model_names MTbl) M C).
  assert (HfindM' : IdLPM.IdMap.find M MSecMap = Some (MTdef C Mbody)).
  { unfold IdLPM.IdMap.Equal in HMSecMTbl.
    specialize (HMSecMTbl M). rewrite -> HMSecMTbl in HfindM. assumption. }
  (* we need model def that is WD *)
  pose proof (modelsec_members_ok__exists_domain_of_Mbody) as Hmdldef.
  destruct (fold_left
                 (fun (okAndCl : Prop * mdlcontext) (dt : id * modeldef) =>
                  let (ok, cl) := okAndCl in
                  (model_welldefined CTbl cl (model_names MTbl) (snd dt) /\ ok,
                  let (_, d) := dt in
                  match d with
                  | mdl_def Mname C Mbody =>
                      IdLPM.IdMap.add Mname
                        (MTdef C
                           (IdLPM.map_from_list (map namedef_to_pair Mbody)))
                        cl
                  end)) (map modeldef_pair_with_id MSec) 
                 (True, mstempty))
    as [okF clF] eqn:Heqfold. symmetry in Heqfold.
  assert (HokF : okF).
  { rewrite surjective_pairing in Heqfold. inversion Heqfold.
    assumption. }
  specialize (Hmdldef CTbl (model_names MTbl) 
                      (map modeldef_pair_with_id MSec)
                      okF clF Heqfold HokF).
  pose proof (modelsec_members_ok__last_cl_equal_to) as HEqclF.
  assert (Htriv : map modeldef_pair_with_id MSec
                  = map modeldef_pair_with_id MSec)
    by reflexivity.
  pose proof (map_fst__modeldef__get_name__nodup MSec HMSecnodup)
    as Hnodup.
  specialize (HEqclF CTbl (model_names MTbl) MSec 
                     (map modeldef_pair_with_id MSec)
                     okF clF Htriv Heqfold HokF Hnodup).
  clear Htriv.
  assert (HclFMtbl : IdLPM.IdMap.Equal clF MTbl).
  { eapply IdMapProps.F.Equal_trans. eassumption.
    subst MSecMap. apply IdMapProps.F.Equal_sym.
    assumption. }
  assert (HclFfind : IdLPM.IdMap.find M clF = Some (MTdef C Mbody)).
  { apply IdMapProps.F.find_mapsto_iff.
    apply IdMapProps.F.find_mapsto_iff in HfindM.
    rewrite IdMapProps.F.Equal_mapsto_iff in HclFMtbl.
    apply HclFMtbl. assumption. }
  specialize (Hmdldef _ _ _ HclFfind).
  destruct Hmdldef as [N [Mbody' HmdldefIn]].
  pose proof (modelsec_members_ok__model_welldefined_in_last_cl) as HmdlWD.
  specialize 
    (HmdlWD CTbl (model_names MTbl) (map modeldef_pair_with_id MSec)
            okF clF Heqfold HokF).
Admitted.  
(*
dd

(*
  specialize (HTQMMtf MSec Mbody).
*)
Abort.
*)

(* %%%%% *)

(* ================================================================= *)
(** *** CTbl and MTbl well-definedness properties *)
(* ================================================================= *)



(* ================================================================= *)
(** *** Progress *)
(* ================================================================= *)



Section HelperProgress.

  Variable CTbl : cptcontext.
  Variable MTbl : mdlcontext.

  Lemma canonical_forms_bool : forall (t : tm),
      CTbl $ MTbl ; ctxempty |- t \in TBool ->
      value t ->
      (t = ttrue) \/ (t = tfalse).
  Proof.
    intros t HT HVal.
    inversion HVal; inversion HT; subst; try solve_by_invert; try tauto.
  Qed.

  Lemma canonical_forms_nat : forall (t : tm),
      CTbl $ MTbl ; ctxempty |- t \in TNat ->
      value t ->
      exists n, t = tnat n.
  Proof.
    intros t HT HVal.
    inversion HVal; inversion HT; subst; try solve_by_invert. 
    exists n0. symmetry. assumption.
  Qed.

  Lemma canonical_forms_lambda : forall (t : tm) (T1 T2 : ty),
      CTbl $ MTbl ; ctxempty |- t \in (TArrow T1 T2) ->
      value t ->
      exists x s, t = tabs x T1 s.
  Proof.
    intros t T1 T2 HT HVal.
    inversion HVal; inversion HT; subst; try solve_by_invert. 
    exists x0 t12. symmetry. assumption.
  Qed.

  Lemma canonical_forms_cpt_lambda : forall (t : tm) (C : id) (T : ty),
      CTbl $ MTbl ; ctxempty |- t \in (TConceptPrm C T) ->
      value t ->
      exists c s, t = tcabs c C s.
  Proof.
    intros t T1 T2 HT HVal.
    inversion HVal; inversion HT; subst; try solve_by_invert. 
    exists c0 t1. symmetry. assumption.
  Qed.

End HelperProgress.


Theorem mdlcontext_WD__name_definition_exists :
  forall CTbl MTbl,
    cptcontext_welldefined CTbl ->
    mdlcontext_welldefined CTbl MTbl ->
    forall M C nmtms nmtys nm T,
      IdLPM.IdMap.find M MTbl = Some (MTdef C nmtms) ->
      IdLPM.IdMap.find C CTbl = Some (CTdef nmtys) ->
      find_ty nm nmtys = Some T ->
      exists t,
        find_tm nm nmtms = Some t.
Admitted.

Ltac make_substep :=
  match goal with
  | [Ht : exists t', ?CTbl $ ?MTbl ; ?t #==> t' 
     |- (*exists s, ?CTbl $ ?MTbl ; context[?t] #==> s*) context[ ?t ] ] 
    => inversion Ht as [subt' Hsubt']; 
       eexists; constructor; eassumption                                     
  end.

Ltac progress_bin_op_nat :=
  match goal with
  | [ IHHT1 : context[ value ?t1 
                       \/ (exists t1' : tm, ?CTbl $ ?Mtbl; ?t1 #==> t1') ] ,
      IHHT2 : context[ value ?t2 
                       \/ (exists t2' : tm, ?CTbl $ ?Mtbl; ?t2 #==> t2') ] ,
      HT1 : ?CTbl $ ?MTbl ; ctxempty |- ?t1 \in TNat ,
      HT2 : ?CTbl $ ?MTbl ; ctxempty |- ?t2 \in TNat 
      |- _ ] 
    => right;
       destruct IHHT1 as [Ht1 | Ht1]; try tauto;
         [ destruct IHHT2 as [Ht2 | Ht2]; try tauto;
           pose proof (canonical_forms_nat _ _ t1 HT1 Ht1) as Hv1;
           inversion Hv1 as [n1 Hn1]; subst t1;
           try (pose proof (canonical_forms_nat _ _ t2 HT2 Ht2) as Hv2;
                inversion Hv2 as [n2 Hn2]; subst t2; eexists; constructor);
           try make_substep
         | make_substep ]
  end.

(** This the main [progress] theorem. *)

Theorem progress : forall CTbl MTbl t T,
     CTbl $ MTbl ; ctxempty ||- t \in T ->
     value t \/ exists t', CTbl $ MTbl ; t #==> t'.
Proof.
  intros CTbl MTbl.
  intros t T HT.
  (* [remember] is a technical moment: otherwise information 
     about emptiness of Gamma is lost. *)
  remember ctxempty as Gamma.
  unfold has_type_WD in HT.
  destruct HT as [HCTOk [HMTOk HT]].
  induction HT; subst Gamma; eauto;
    (* for binary nat ops *)
    try solve [progress_bin_op_nat].
(* tvar *)
  - (* var cannot be typed in empty context*) 
    inversion H.
(* tapp *)
  - (* application always makes a step *)
    right.
    (* case analysis on [t1] progress *)
    destruct IHHT1; try tauto.
    + (* case analysis on [t2] progress *)
      destruct IHHT2; try tauto.
      * (* abs val *)
        pose proof (canonical_forms_lambda _ _ _ _ _ HT1 H) as Ht1.
        inversion Ht1 as [x Hs]. inversion Hs as [s Heq].
        exists ([x := t2] s). subst. 
        constructor. assumption.
      * (* t2 #==> t2' *)
        inversion H0 as [t2' Ht2].
        exists (tapp t1 t2'). 
        constructor; assumption.
    + (* t1 #==> t1' *)
      inversion H as [t1' Ht1].
      exists (tapp t1' t2). 
      constructor; assumption.
(* tmapp *)
  - (* model application always makes a step *)
    right.
    (* case analysis on [t1] progress *)
    destruct IHHT; try tauto.
    + (* t1 is a value -- concept abstraction *)
      pose proof (canonical_forms_cpt_lambda _ _ _ _ _ HT H0) as Ht1.
      inversion Ht1 as [c Hs]. inversion Hs as [s Heq].
      exists ([#c := M] s). subst t1. 
      apply ST_MAppCAbs with (Mbody := Mbody). assumption.
    + (* t1 #==> t1' *)
      inversion H0 as [t1' Ht1].
      exists (tmapp t1' M). 
      constructor; assumption.
(* tcinvk c f *)
  - (* concept method invocation cannot be types in empty Gamma *)
    inversion H.
(* tcinvk M f *)
  - (* method invocation makes a step to its body *)
    right.
    (* For this we actually need model table correctness *)
    pose proof 
         (mdlcontext_WD__name_definition_exists CTable MTable
            HCTOk HMTOk M C Mbody) as Hspec.   
    unfold concept_fun_member in *.
    destruct (IdLPM.IdMap.find C CTable) as [[nmtys] |] eqn:Heq.
    + specialize (Hspec nmtys f TF H0).
      assert (Htriv : Some (CTdef nmtys) = Some (CTdef nmtys)) by reflexivity.
      specialize (Hspec Htriv H1).
      clear Htriv. 
      inversion Hspec as [t' Ht'].
      exists (qualify_model_members M Mbody t').
      apply ST_CInvk with (C := C) (Mbody := Mbody).
      assumption. assumption.
    + contradiction.
(* tif t1 t2 t3 *)
  - (* if always makes a step *)
    right.
    destruct IHHT1 as [Ht1 | Ht1]; try tauto.
    + (* t1 is a bool value *)
      pose proof (canonical_forms_bool _ _ t1 HT1 Ht1).
      destruct H as [Htrue | Hfalse]; subst t1;
        econstructor; constructor.
    + (* t1 can make a step *)
      make_substep.      
(* tsucc t1 *)
  - (* tsucc can always make a step *)
    right.
    destruct IHHT as [Ht1 | Ht1]; try tauto.
    + (* t1 is a nat value *)
      pose proof (canonical_forms_nat _ _ t1 HT Ht1).
      destruct H as [n Hn]. subst t1.
      eexists. apply ST_SuccNV.
    + make_substep.
(* tpred t1 *)
  - (* tpred can always make a step *)
    right.
    destruct IHHT as [Ht1 | Ht1]; try tauto.
    + (* t1 is a nat value *)
      pose proof (canonical_forms_nat _ _ t1 HT Ht1).
      destruct H as [n Hn]. subst t1.
      destruct n as [| n']. 
      eexists. apply ST_PredZero.
      eexists. apply ST_PredSucc.
    + make_substep.
(* teqnat *)
  - (* teqnat always makes a step *)
    right.
    destruct IHHT1 as [Ht1 | Ht1]; try tauto.
    + destruct IHHT2 as [Ht2 | Ht2]; try tauto;
        pose proof (canonical_forms_nat _ _ t1 HT1 Ht1) as Hv1;
        inversion Hv1 as [n1 Hn1]; subst t1.
      pose proof (canonical_forms_nat _ _ t2 HT2 Ht2) as Hv2.
      inversion Hv2 as [n2 Hn2]. subst t2.
      destruct (Nat.eq_dec n1 n2).
      * exists ttrue. apply ST_EqnatNVTrue; tauto.
      * exists tfalse. apply ST_EqnatNVFalse; tauto.
      * make_substep. 
    + make_substep.
(* tlenat *)
  - (* tlenat always makes a step *)
    right.
    destruct IHHT1 as [Ht1 | Ht1]; try tauto.
    + destruct IHHT2 as [Ht2 | Ht2]; try tauto;
        pose proof (canonical_forms_nat _ _ t1 HT1 Ht1) as Hv1;
        inversion Hv1 as [n1 Hn1]; subst t1.
      pose proof (canonical_forms_nat _ _ t2 HT2 Ht2) as Hv2.
      inversion Hv2 as [n2 Hn2]. subst t2.
      destruct (lt_dec n1 n2).
      * exists ttrue. apply ST_LenatNVTrue; tauto.
      * exists tfalse. apply ST_LenatNVFalse. apply not_lt; assumption.
      * make_substep. 
    + make_substep.
Qed.

(* ================================================================= *)
(** *** Preservation *)
(* ================================================================= *)

(* ----------------------------------------------------------------- *)
(** **** Aux defs and proofs *)
(* ----------------------------------------------------------------- *)

Lemma free_in_context : forall CTbl MTbl x t T Gamma,
   appears_free_in CTbl MTbl x t ->
   CTbl $ MTbl ; Gamma |- t \in T ->
   (exists T', Gamma x = Some (tmtype T'))
     /\ ((exists MT, IdLPM.IdMap.find x MTbl = Some MT)
                 \/ (IdLPM.IdMap.find x MTbl = None))
   \/ (exists C, Gamma x = Some (cpttype C))
   \/ (exists MT, IdLPM.IdMap.find x MTbl = Some MT)
      /\ (Gamma x = None).
Proof.
  intros CTbl MTbl x t.
  induction t;
    intros T Gamma Hfree HT; 
    unfold appears_free_in in *; simpl in *;
    inversion HT; simpl in *; subst;
    (* we can do some automation... *)
    try 
    solve [
    (* in simple cases such as [ttrue] we have a contradiction
       in the assumption: there are no FV in the term *)
      match goal with
      |[ H : IdLS.IdSet.In x IdLS.IdSet.empty |- _ ]
       => rewrite IdLS.Props.IdSetProps.Dec.F.empty_iff in H; 
          contradiction
      end
    (* in recursive cases such as [tif] pt [tsucc]
       we can simply solve it by IH *)
    | repeat (apply IdLS.Props.IdSetProps.FM.union_1 in Hfree;
            destruct Hfree as [Hfree | Hfree]);
          match goal with
          | [IHt : forall (T : ty) (Gamma : context),
                   IdLS.IdSet.In ?x (free_vars ?CTbl ?MTbl ?t1) ->
                   ?CTbl $ ?MTbl; Gamma |- ?t1 \in T -> _,
               Hfree : IdLS.IdSet.In ?x (free_vars ?CTbl ?MTbl ?t1),
               HTt : ?CTbl $ ?MTbl; ?Gamma |- ?t1 \in ?T |- _]
            => specialize (IHt _ Gamma Hfree HTt); assumption
          end ].
  - (* tvar i *)
    apply IdLS.Props.IdSetProps.FM.singleton_1 in Hfree.
    unfold IdUOT.eq in Hfree. subst.
    left. split. 
    + (* tmtype *) 
      exists T. assumption.
    + (* find dec *)
      destruct (IdLPM.IdMap.find x MTbl) eqn:Heq.
      left. eexists. reflexivity.
      right. reflexivity.
  - (* tabs *)
    rename i into y. rename t into T11.
    rewrite IdLS.Props.IdSetProps.Dec.F.remove_iff in Hfree.
    destruct Hfree as [Hfree Heqxy]. unfold IdUOT.eq in *.
    specialize (IHt _ _ Hfree H6).
    pose proof (update_neq _ (tmtype T11) x y Gamma Heqxy) as HG.
    rewrite <- HG. assumption.
  - (* tcabs *)
    rename i into c. rename i0 into C.
    rewrite IdLS.Props.IdSetProps.Dec.F.remove_iff in Hfree.
    destruct Hfree as [Hfree Heqxy]. unfold IdUOT.eq in *.
    specialize (IHt _ _ Hfree H7).
    pose proof (update_neq _ (cpttype C) x c Gamma Heqxy) as HG.
    rewrite <- HG. assumption.
  - (* [tcinvk c f] for c#C \in Gamma *)
    rename i into c. rename i0 into f.
    apply IdLS.Props.IdSetProps.FM.singleton_1 in Hfree.
    unfold IdUOT.eq in Hfree. subst.
    right. left. exists C. assumption.
  - (* [tcinvk M f] *)
    rename i into M. rename i0 into f.
    apply IdLS.Props.IdSetProps.FM.singleton_1 in Hfree.
    unfold IdUOT.eq in Hfree. subst.
    destruct (Gamma x) eqn:Heq.
    + (* tmtype or cpttype *)
      destruct c eqn:Heq1. subst.
      * (* tmtype *)
        left. split. eexists; reflexivity.
        left. eexists. eassumption.
      * (* cpttype *)
        exfalso. apply H1. eexists. reflexivity.
    + (* None *)
      right. right. split. eexists. eassumption. reflexivity.
  - (* tlet *)
    rename i into y.
    apply IdLS.Props.IdSetProps.FM.union_1 in Hfree.
    destruct Hfree as [Hfree | Hfree].
    + specialize (IHt1 _ Gamma Hfree H6); assumption.
    + rewrite IdLS.Props.IdSetProps.Dec.F.remove_iff in Hfree.
      destruct Hfree as [Hfree Heqxy]. unfold IdUOT.eq in *.
      specialize (IHt2 _ _ Hfree H7). 
      pose proof (update_neq _ (tmtype T1) x y Gamma Heqxy) as HG.
      rewrite <- HG. assumption.
Qed.

(** Context consists of type variables only. *)
Definition Gamma_of_tmtypes (G : context) :=
  forall x, G x <> None ->
            exists T, G x = Some (tmtype T).

(** All term types from Gamma appear in concept type *)
Definition cty_consistent_with_Gamma (CT : id_ty_map) (G : context) :=
  forall f Tf, G f = Some (tmtype Tf) ->
               IdLPM.IdMap.find f CT = Some Tf.

Definition mdlnames_consistent_with_Gamma (mdlnames : id_set) (G : context) :=
  forall x, G x <> None ->
            IdLS.IdSet.In x mdlnames.

(** There is a subtelty in typing preservation for substitution.
    If [v] has type [S] in the empty context,
      it could be the case that v is equal to [M.f]
      where [M \in MTbl].
    It means that [v] could become badly-typed 
    in the context [Gamma] which contains [M].

    Here is an _example_.

    * [concept CBar { foo : Nat -> Nat },
       concept CFoo { foo : Bool },
       model MFoo of CFoo { foo = true }]
    * [Gamma = { MFoo # CBar }]
    * [t = if x then 42 else 0]
    * [v = MFoo.foo] 

    We have:
      [Gamma, x:Bool |- t : Nat]
    and
      [|- v : Bool].
   
    But the result of substitution does not have a type:
      [MFoo # CBar |- if MFoo.foo then 42 else 0 !!!]
    because [MFoo.foo] in [Gamma] has type [Nat -> Nat]. 

    Thus, we can only consider [Gamma], which
    does not contain concept variables named as models.

    As long as concept variables come into Gamma from a term,
    we also have to require that a term does not contain
    bound concept variables named as models.
 *)

(*
Fixpoint all_vars (t : tm) : IdLS.id_set := 
  match t with
  (* AV(x) = {x} *)
  | tvar x      => IdLS.IdSet.singleton x  
  (* AV(t1 t2) = AV(t1) \union AV(t2) *)
  | tapp t1 t2  => IdLS.IdSet.union (all_vars t1) (all_vars t2)
  (* AV(\x:T.t) = AV(t) \union {x} *)                               
  | tabs x T t  => IdLS.IdSet.union (IdLS.IdSet.singleton x) (all_vars t)
  (* AV(t # M) = AV(t) because M refers to MTable, not term itself *)   
  | tmapp t M   => all_vars t   
  (* AV(\c#C.t) = AV(t) \unin {c} *)
  | tcabs c C t => IdLS.IdSet.union (IdLS.IdSet.singleton c) (all_vars t)
  (* AV(c.f) = {c} *)
  | tcinvk c f  => IdLS.IdSet.singleton c
  (* AV(true) = {} *)
  | ttrue       => IdLS.IdSet.empty
  (* AV(false) = {} *)
  | tfalse      => IdLS.IdSet.empty
  (* AV(if t1 then t2 else t3) = AV(t1) \union AV(t2) \union AV(t3) *)
  | tif t1 t2 t3 => IdLS.IdSet.union 
                      (IdLS.IdSet.union (all_vars t1) (all_vars t2)) 
                      (all_vars t3)
  (* AV(n) = {} *)
  | tnat n      => IdLS.IdSet.empty
  (* AV(succ t) = AV(t) *)
  | tsucc t     => all_vars t
  (* AV(pred t) = AV(t) *)
  | tpred t     => all_vars t
  (* AV(plus t1 t2) = AV(t1) \union AV(t2) *)
  | tplus t1 t2  => IdLS.IdSet.union (all_vars t1) (all_vars t2)
  (* AV(minus t1 t2) = AV(t1) \union AV(t2) *)
  | tminus t1 t2 => IdLS.IdSet.union (all_vars t1) (all_vars t2)
  (* AV(mult t1 t2) = AV(t1) \union AV(t2) *)
  | tmult t1 t2  => IdLS.IdSet.union (all_vars t1) (all_vars t2)
  (* AV(eqnat t1 t2) = AV(t1) \union AV(t2) *)
  | teqnat t1 t2 => IdLS.IdSet.union (all_vars t1) (all_vars t2)
  (* AV(lenat t1 t2) = AV(t1) \union AV(t2) *)
  | tlenat t1 t2 => IdLS.IdSet.union (all_vars t1) (all_vars t2)
  (* AV(let x=t1 in t2) = AV(t1) \union AV(t2) \union {x} *)       
  | tlet x t1 t2 => IdLS.IdSet.union
                      (IdLS.IdSet.singleton x)
                      (IdLS.IdSet.union (all_vars t1) (all_vars t2))
  end.

Definition no_model_names_in_context (CTbl : cptcontext) 
           (MTbl : mdlcontext) (Gamma : context) : Prop :=
  forall (x : id), 
    (exists MT, IdLPM.IdMap.find x MTbl = Some MT) ->
    Gamma x = None.

(** This property means that model names do not appear in term
 ** in variable positions (neither free nor bound). *)
Definition no_model_names_in_term (CTbl : cptcontext) 
           (MTbl : mdlcontext) (t : tm) : Prop :=
  forall (x : id), 
    IdLPM.IdMap.In x MTbl ->
    IdLS.IdSet.In x (all_vars t) -> 
    False.

Definition no_bound_model_names_in_term (CTbl : cptcontext) 
           (MTbl : mdlcontext) (t : tm) : Prop :=
  forall (x : id), 
    IdLPM.IdMap.In x MTbl ->
    IdLS.IdSet.In x (bound_cvars t) -> 
    False.

Ltac prove_no_model_names_in_subterm :=
  match goal with
    [ Hvars : no_model_names_in_term ?CTbl ?MTbl ?t
      |- no_model_names_in_term ?CTbl ?MTbl ?s ]
    => let Hnew := fresh "Hvars" in 
       assert (Hnew := Hvars);
       unfold no_model_names_in_term;
       unfold no_model_names_in_term in Hnew;
       intros mx HinM HinS; 
       specialize (Hnew mx HinM);
       apply Hnew; simpl;
       auto using IdLS.Props.IdSetProps.Dec.F.union_2,
                  IdLS.Props.IdSetProps.Dec.F.union_3,
                  IdLS.Props.IdSetProps.Dec.F.remove_2
  end.

Ltac prove_no_model_names_in_upd_Gamma :=
  match goal with
    [ HGamma : no_model_names_in_context ?CTbl ?MTbl ?Gamma ,
      Hvars  : no_model_names_in_term ?CTbl ?MTbl _
      |- no_model_names_in_context ?CTbl ?MTbl (update ?Gamma ?u ?V ) ]
    => unfold no_model_names_in_context;
       intros zf HM;
       inversion HM as [MT HMT];
       assert (Hinz : IdLPM.IdMap.In zf MTbl)
         by (apply MId.IdLPM.Props.IdMapProps.F.in_find_iff;
             intros contra; rewrite HMT in contra; inversion contra);
       destruct (beq_idP u zf) as [Huzf | Huzf];
       [ subst; unfold no_model_names_in_term in Hvars;
         specialize (Hvars zf Hinz);
         exfalso; apply Hvars; simpl;
         auto using IdLS.Props.IdSetProps.Dec.F.union_2,
                    IdLS.Props.IdSetProps.Dec.F.union_3,
                    IdLS.Props.IdSetProps.FM.singleton_2 
       | unfold no_model_names_in_context in HGamma;
         specialize (HGamma zf HM);
         rewrite update_neq; assumption ]
  end.
*)

Lemma substitution_preserves_typing : 
  forall CTbl MTbl Gamma x S t v T,
    no_model_names_as_cvars_in_Gamma MTbl Gamma ->
    no_model_names_as_bound_cvars_in_term MTbl t ->
    no_model_names_as_bound_cvars_in_term MTbl v ->
    CTbl $ MTbl ; (update Gamma x (tmtype S)) |- t \in T ->
    CTbl $ MTbl ; ctxempty |- v \in S -> 
    CTbl $ MTbl ; Gamma |- [x:=v] t \in T.
Proof.
  intros CTbl MTbl Gamma x S t v T (*HCTOk HMTOk*).
  intros HGamma HtOk HvOk HTt HTv.
  generalize dependent T. generalize dependent Gamma.
  induction t;
    intros Gamma HGamma T HTt;
    inversion HTt; subst; simpl;
  (* simple cases such as [ttrue] can be solved with constructor *)
  try solve [constructor];
  (* for regular inductive cases we can use IHs *)
  try solve [ 
    constructor;
    match goal with
      [ IHt : context[ [?x:=?v] ?s ]
        |- ?CTbl $ ?MTbl; ?Gamma |- [?x := ?v] ?s \in ?T ]
      => apply IHt; try assumption; 
         prove_no_model_names_as_bound_cvars_in_subterm 
    end ].
(* tvar *)
  - rename i into y. destruct (beq_idP x y). 
    + subst. 
      rewrite update_eq in H3. inversion H3. subst. clear H3.
      apply context_weakening with (Gamma := ctxempty);
        try assumption.
      intros x Hnone. unfold ctxempty in Hnone. 
      rewrite apply_empty in Hnone. tauto.
    + constructor.
      rewrite <- H3. symmetry.
      apply update_neq. assumption.
(* tapp *)
  - apply T_App with T11.
    + apply IHt1;
        [prove_no_model_names_as_bound_cvars_in_subterm 
        | assumption | assumption].
    + apply IHt2; 
        [prove_no_model_names_as_bound_cvars_in_subterm 
        | assumption | assumption].
(* tabs *)
  - rename i into y. rename t into T.
    destruct (beq_idP x y) as [Heqxy | Heqxy]. 
    + (* x = y *) 
      subst. 
      apply context_invariance with (update Gamma y (tmtype S));
        try assumption.
      intros x Hfree.
      destruct (beq_idP y x) as [Heqxy | Heqxy].
      * subst. unfold appears_free_in in Hfree.
        simpl in Hfree.
        assert (Htriv : x = x) by reflexivity.
        apply IdLS.Props.IdSetProps.Dec.F.remove_1
        with (s := free_vars CTbl MTbl t0) (x := x) (y := x) in Htriv.
        apply Htriv in Hfree. contradiction.
      * apply update_neq. assumption.
    + (* x <> y *)
      apply T_Abs.
      apply IHt. prove_no_model_names_as_bound_cvars_in_subterm.
      * (* model names invariant *) 
        unfold no_model_names_as_cvars_in_Gamma.
        intros z [[C HupdM] HMinMT].
        destruct (beq_idP y z) as [Hyz | Hyz].
        { subst. rewrite update_eq in HupdM. inversion HupdM. }
        { unfold no_model_names_as_cvars_in_Gamma in HGamma.
          rewrite update_neq in HupdM; try assumption.
          apply HGamma with z. split.
          eexists; eassumption. assumption. }
      * apply context_invariance 
        with (update (update Gamma x (tmtype S)) y (tmtype T)); 
          try assumption.
        intros z _. 
        apply update_permute_get; assumption.
(* tmapp *)
  - rename i into M.
    apply T_MApp with C Mbody. assumption.
    apply IHt; try assumption.
(* tcabs *)
  - rename i into c. rename i0 into C.
    apply T_CAbs with Cbody. assumption.
    destruct (beq_idP c x) as [Hxc | Hxc].
    + (* x = c *) 
      subst. 
      apply context_invariance 
      with (update (update Gamma x (tmtype S)) x (cpttype C));
        try assumption.
      intros z Hfree.
      rewrite (update_shadow _ Gamma _ _ x). reflexivity.
    + (* x <> c*)
      apply IHt. prove_no_model_names_as_bound_cvars_in_subterm.
      * (* model names invariant *) 
        unfold no_model_names_as_cvars_in_Gamma.
        intros z [[C0 HupdM] HMinMT].
        unfold no_model_names_as_bound_cvars_in_term in HtOk.
        destruct (beq_idP c z) as [Hcz | Hcz].
        ** subst. apply HtOk. exists z. split; try assumption.
           simpl. apply IdLS.Props.IdSetProps.Dec.F.add_1. reflexivity.
        ** rewrite update_neq in HupdM; try assumption.
           unfold no_model_names_as_cvars_in_Gamma in HGamma.
           apply HGamma with z. split.
           eexists. eassumption. assumption.
      * (* typing *) 
        apply context_invariance 
        with (update (update Gamma x (tmtype S)) c (cpttype C));
          try assumption.
        intros z _.
        apply update_permute_get. intuition.
(* tcinvk c f *)
  - rename i into c. rename i0 into f.
    apply context_invariance with (update Gamma x (tmtype S));
      try assumption.
    intros y Hfree.
    unfold appears_free_in in Hfree. simpl in Hfree.
    apply IdLS.Props.IdSetProps.FM.singleton_1 in Hfree. 
    unfold IdUOT.eq in Hfree. subst.
    destruct (beq_idP x y) as [Hxy | Hxy].
    + subst. rewrite update_eq in H4.
      inversion H4.
    + rewrite update_neq. reflexivity. assumption.
(* tcinvk M f *)
  - rename i into M. rename i0 into f.
    apply T_MInvk with C Mbody; try assumption.
    unfold no_model_names_as_cvars_in_Gamma in HGamma.
    intros [MC contra]. apply HGamma with M. split.
    exists MC. assumption. apply IdMapProps.F.in_find_iff.
    intros contra'. rewrite H5 in contra'. inversion contra'.
(* tlet *)
  - rename i into y. 
    apply T_Let with T1.
    apply IHt1; try assumption. 
    prove_no_model_names_as_bound_cvars_in_subterm.
    destruct (beq_idP x y) as [Hxy | Hxy]. 
    + (* x = y *) 
      subst. 
      apply context_invariance 
      with (update (update Gamma y (tmtype S)) y (tmtype T1));
        try assumption.
      intros x _.
      rewrite update_shadow. reflexivity.
    + (* x <> y *)
      apply IHt2. prove_no_model_names_as_bound_cvars_in_subterm.
      * (* model names invariant *) 
        unfold no_model_names_as_cvars_in_Gamma.
        intros z [[C HupdM] HMinMT].
        destruct (beq_idP y z) as [Hyz | Hyz].
        { subst. rewrite update_eq in HupdM. inversion HupdM. }
        { unfold no_model_names_as_cvars_in_Gamma in HGamma.
          rewrite update_neq in HupdM; try assumption.
          apply HGamma with z. split.
          eexists; eassumption. assumption. }
      * apply context_invariance 
        with (update (update Gamma x (tmtype S)) y (tmtype T1)); 
          try assumption.
        intros z _. 
        apply update_permute_get; assumption.
Qed.

(** There are subtelties with concept substitution as well. 

    Consider an example.

    * [concept CBar {foo : Nat},
       concept CFoo {foo : Bool},
       model MFoo of CFoo ...]
    * [Gamma = {MFoo#CBar}]
    * [t = c.foo]
    * [M = MFoo]    

    We have
      [Gamma, c#CFoo |- c.foo : Bool]
    but 
      [[c:=MFoo]t = MFoo.foo]
    and
      [MFoo#CBar |- MFoo.foo : Nat], not [Bool]!

    So we need that model name we substitute for 
    the concept parameter does no appear in Gamma
    as a bound concept variable.
*)


Ltac prove_no_model_name_in_subterm :=
      match goal with
        [ HMt : ~ IdLS.IdSet.In ?M (bound_cvars ?t)
          |- ~ IdLS.IdSet.In ?M (bound_cvars ?s) ]
        => match t with context[ s ] 
           => let Hcontra := fresh "contra" in
              intros Hcontra;
              assert (Hcontrapremise : IdLS.IdSet.In M (bound_cvars t))
                by (simpl;
                    auto using IdLS.Props.IdSetProps.Dec.F.union_2,
                    IdLS.Props.IdSetProps.Dec.F.union_3,
                    IdLS.Props.IdSetProps.Dec.F.remove_2);
              apply HMt; assumption
           end
      end.


Lemma concept_substitution_preserves_typing : 
  forall CTbl MTbl Gamma c C t T M Mbody,
(*    cptcontext_welldefined CTbl ->
    mdlcontext_welldefined CTbl MTbl ->    *)
(*    no_model_names_in_context CTbl MTbl Gamma ->
    no_model_names_in_term CTbl MTbl t -> *)
    CTbl $ MTbl ; (update Gamma c (cpttype C)) |- t \in T ->
    IdLPM.IdMap.find M MTbl = Some (MTdef C Mbody) ->
    (~ exists C, Gamma M = Some (cpttype C)) ->
    (~ IdLS.IdSet.In M (bound_cvars t)) ->
    CTbl $ MTbl ; Gamma |- [#c:=M] t \in T.
Proof.
  intros CTbl MTbl Gamma c C t T M Mbody (*HCTOk HMTOk*).
  intros (*HGamma Hvars*) HTt HMdef HMGamma HMt.
  generalize dependent T. generalize dependent Gamma.
  induction t;
    intros Gamma HMGamma (*HGamma*) T HTt;
    inversion HTt; subst; simpl;
  (* simple cases such as [ttrue] can be solved with constructor *)
  try solve [constructor];
  (* for regular inductive cases we can use IHs *)
  try solve [ 
    constructor;
    match goal with
      [ IHt : context[ [#?c:=?M] ?s ]
        |- ?CTbl $ ?MTbl; ?Gamma |- [#?c := ?M] ?s \in ?T ]
      => apply IHt; try assumption; prove_no_model_name_in_subterm 
    end ].
(* tvar *)
  - rename i into y. destruct (beq_idP c y). 
    + (* c = y *)
      subst. 
      rewrite update_eq in H3. inversion H3.
    + (* c <> y *)
      rewrite update_neq in H3; try assumption.
      apply T_Var. assumption.
(* tapp *)
  - apply T_App with T11.
    + apply IHt1; (assumption || prove_no_model_name_in_subterm). 
    + apply IHt2; (assumption || prove_no_model_name_in_subterm).
(* tabs *)
  - rename i into x. rename t into T.
    apply T_Abs.
    destruct (beq_idP c x) as [Hcx | Hcx].
    + (* c = x *)
      subst.
      apply context_invariance 
      with (update (update Gamma x (cpttype C)) x (tmtype T));
        try assumption.
      intros z _. rewrite update_shadow. reflexivity.
    + (* c <> x *)
      apply IHt. 
      * prove_no_model_name_in_subterm.
      * (* M not in upd Gamma *)
        destruct (beq_idP x M) as [HxM | HxM].
        { subst. rewrite update_eq. 
          intros [C0 contra]. inversion contra. }
        { rewrite update_neq; try assumption. }
      * apply context_invariance 
        with (update (update Gamma c (cpttype C)) x (tmtype T));
          try assumption.
        intros z _. apply update_permute_get; assumption.
(* tmapp *)
  - rename i into M'.
    apply T_MApp with C0 Mbody0. assumption.
    apply IHt; try assumption. 
(* tcabs *)
    - rename i into c'. rename i0 into C'.
      apply T_CAbs with Cbody. assumption.
      destruct (beq_idP c c') as [Hcc' | Hcc'].
      + (* c = c' *)
        subst.
        apply context_invariance 
        with (update (update Gamma c' (cpttype C)) c' (cpttype C'));
          try assumption.
        intros z _. rewrite update_shadow. reflexivity.
      + (* c <> c' *)        
        apply IHt; try assumption.
        simpl in HMt.
        * destruct (beq_idP c' M) as [Hc'M | Hc'M].
          ** subst. exfalso.
             apply HMt. apply IdLS.Props.IdSetProps.Dec.F.add_1. reflexivity.
          ** rewrite IdLS.Props.IdSetProps.Dec.F.add_neq_iff in HMt;
               try assumption.
        * destruct (beq_idP c' M) as [Hc'M | Hc'M].
          ** subst. simpl in HMt. exfalso.
             apply HMt. apply IdLS.Props.IdSetProps.Dec.F.add_1. reflexivity.
          ** rewrite update_neq; try assumption.
        * apply context_invariance 
          with (update (update Gamma c (cpttype C)) c' (cpttype C'));
            try assumption.
          intros z _. apply update_permute_get; assumption.
(* tcinvk *)
    - rename i into c'. rename i0 into f.
      destruct (beq_idP c c') as [Hcc' | Hcc'].
      + (* c = c' *)
        subst. rewrite update_eq in H4. inversion H4; subst. clear H4.
        apply T_MInvk with C0 Mbody; try assumption.
(*        unfold no_model_names_in_context in HGamma;
          try assumption.
        assert (HMT : exists MT : mty, IdLPM.IdMap.find M MTbl = Some MT)
          by (exists (MTdef C Mbody); assumption).
        specialize (HGamma M HMT).
        destruct (Gamma M) eqn:Heq.
        * symmetry in Heq. inversion HGamma.
        * reflexivity.
        * rewrite update_eq in H4. inversion H4. subst. assumption. *)
      + (* c <> c' *)
        inversion HTt; subst.
        * apply T_CInvk with C1.
          rewrite update_neq in H5. assumption. 
          assumption. assumption.
        * rewrite update_neq in H1; try assumption.
          apply T_MInvk with C1 Mbody0; try assumption.
(* tcinvk T_MInvk *)
    - rename i into M'. rename i0 into f.
      destruct (beq_idP c M') as [HcM' | HcM'].
      + (* c = M' *)
        subst. exfalso. apply H1.
        exists C. rewrite update_eq. reflexivity.
      + (* c <> M' *)
        apply T_MInvk with C0 Mbody0; try assumption.
        rewrite update_neq in H1. assumption. assumption.
(* tlet *)
    - rename i into y.
      apply T_Let with T1.
      apply IHt1; try assumption.
      prove_no_model_name_in_subterm.
      destruct (beq_idP c y) as [Hcy | Hcy].
      + (* c = y *)
        subst.
        apply context_invariance 
        with (update (update Gamma y (cpttype C)) y (tmtype T1));
          try assumption.
        intros z _. rewrite update_shadow. reflexivity.
      + (* c <> y *)
        apply IHt2.
        * prove_no_model_name_in_subterm.
        * (* M not in upd Gamma *)
          destruct (beq_idP y M) as [HyM | HyM].
          { subst. rewrite update_eq. 
            intros [C0 contra]. inversion contra. }
          { rewrite update_neq; try assumption. }
        * apply context_invariance 
          with (update (update Gamma c (cpttype C)) y (tmtype T1));
            try assumption.
          intros z _. apply update_permute_get; assumption.
Qed.



Lemma no_model_names_in_empty_context :
  forall MTbl,
    no_model_names_as_cvars_in_Gamma MTbl ctxempty.
Proof.
  intros MTbl.
  unfold no_model_names_as_cvars_in_Gamma.
  intros M [[C contra] _]. inversion contra.
Qed.

(** The problem with preservation is when we make a step from
    [M.f] to [QMM(tf)], the definition of [f] in the model [M]
    where all names referring to the [M] members 
    are replaced with qualified names.

    We have to know that the type is preserved for the
    member definition [tf].
 *)

Lemma no_model_names_as_cvars_in_empty_context :
  forall MTbl, 
    no_model_names_as_cvars_in_Gamma MTbl ctxempty.
Proof.
  intros MTbl.
  unfold no_model_names_as_cvars_in_Gamma.
  intros z [[C contra] _].
  inversion contra.
Qed.  


(* ----------------------------------------------------------------- *)
(** **** Main Preservation Theorem *)
(* ----------------------------------------------------------------- *)

Ltac prove_preservation_with_IH :=
  match goal with
    [ Hbvars : no_model_names_as_bound_cvars_in_term ?MTbl ?t ,
      HTs    : ?CTbl $ ?MTbl ; ctxempty |- ?s \in ?S ,
      IHHE   : no_model_names_as_bound_cvars_in_term ?MTbl ?s ->
               forall T : ty, 
                 ?CTbl $ ?MTbl ; ctxempty ||- ?s \in T ->
                 ?CTbl $ ?MTbl; ctxempty ||- ?s' \in T
        |- ?CTbl $ ?MTbl; ctxempty |- ?s' \in ?S]
    => assert (Hmnames : no_model_names_as_bound_cvars_in_term MTbl s)
         by prove_no_model_names_as_bound_cvars_in_subterm ;
       assert (HTypeSub : CTbl $ MTbl; ctxempty ||- s \in S) 
         by (split; [ assumption | split; assumption ]) ;
       specialize (IHHE Hmnames S HTypeSub);
       inversion IHHE as [_ [_ HTypeSub']];
       assumption
  end.


Theorem preservation : forall CTbl MTbl t t' T,
    (* source term does not use model names as bound concept variables *)
    no_model_names_as_bound_cvars_in_term MTbl t -> 
    (* source term has a type *)
    CTbl $ MTbl ; ctxempty ||- t \in T ->
    (* term makes a step *)
    CTbl $ MTbl ; t #==> t' ->
    (* then a new term has the same type *)
    CTbl $ MTbl ; ctxempty ||- t' \in T.
Proof.
  remember ctxempty as Gamma.
  intros CTbl MTbl t t' T HtOk HT HE. 
  generalize dependent T.
  induction HE;
    intros T [HCTOk [HMTOk HT]]; subst Gamma;
    (* resolve boring WD part *)
    (split; [assumption | split; [assumption | idtac]]);
    (* get typing information for every term *)
    (inversion HT; subst; simpl);
    (* for trivial cases *)
    try assumption;
    (* for regular inductive cases we can use IHs *)
    try solve [
          constructor;
          (assumption || prove_preservation_with_IH)
        ].
(* ST_AppAbs *)
  - apply substitution_preserves_typing with T0;
      try assumption.
    apply no_model_names_as_cvars_in_empty_context.
    prove_no_model_names_as_bound_cvars_in_subterm.
    prove_no_model_names_as_bound_cvars_in_subterm.    
    inversion H5. subst. assumption.
(* ST_App1 *)
  - apply T_App with T11; try assumption.
    prove_preservation_with_IH.
(* ST_App2 *)
  - apply T_App with T11; try assumption.
    prove_preservation_with_IH.
(* ST_MAppAbs *)
  - apply concept_substitution_preserves_typing with C0 Mbody0;
      try assumption.
    + inversion H7; subst. assumption.
    + intros [C1 contra]. inversion contra.
    + unfold no_model_names_as_bound_cvars_in_term in HtOk.
      simpl in HtOk.
      intros HinM. apply HtOk. exists M.
      split. 
      apply IdLS.Props.IdSetProps.Dec.F.add_2. assumption.
      apply IdMapProps.F.in_find_iff. intros contra. 
        rewrite H5 in contra. inversion contra.
(* ST_MApp *) 
  - apply T_MApp with C Mbody; try assumption.
    prove_preservation_with_IH.
(* tf (method invocation) for concept *)
  - inversion H6.
(* M.f ==> tf for model *)
  - clear H3. rewrite H7 in H. inversion H; subst.
    pose proof qualify_model_members_preserves_typing as HTQMM.
    specialize (HTQMM CTbl MTbl M C Mbody f T tf).
    specialize (HTQMM HMTOk H7 HT H0). assumption.
(* tlet *)
  - apply T_Let with T1.
    prove_preservation_with_IH.
    assumption.
(* tlet with substitution *)
  - apply substitution_preserves_typing with T1;
      try assumption.
    apply no_model_names_in_empty_context.
    prove_no_model_names_as_bound_cvars_in_subterm.    
    prove_no_model_names_as_bound_cvars_in_subterm.    
Qed.

(* ================================================================= *)
(** *** Soundness *)
(* ================================================================= *)

(* ----------------------------------------------------------------- *)
(** **** Aux Props *)
(* ----------------------------------------------------------------- *)

Lemma substitution_preserves_no_model_names_in_term :
  forall(* CTbl *) MTbl (x : id) (t v : tm),
(*    cptcontext_welldefined CTbl ->
    mdlcontext_welldefined CTbl MTbl -> *)
    no_model_names_as_bound_cvars_in_term MTbl t ->
    no_model_names_as_bound_cvars_in_term MTbl v ->
    no_model_names_as_bound_cvars_in_term MTbl ([x:=v] t).
Proof.
  intros (* CTbl *) MTbl x t.
  induction t;
    intros v (*HCTOk HMTOk*) HtOk HvOk.
  - (* tvar *)
    rename i into y.
    simpl.
    destruct (beq_idP x y) as [Hxy | Hxy];
      assumption.
  - (* tapp *)
    simpl.
    assert (Ht1Ok : no_model_names_as_bound_cvars_in_term MTbl t1)
      by prove_no_model_names_as_bound_cvars_in_subterm.
    specialize (IHt1 v Ht1Ok HvOk).
    assert (Ht2Ok : no_model_names_as_bound_cvars_in_term MTbl t2)
    by prove_no_model_names_as_bound_cvars_in_subterm.
    specialize (IHt2 v Ht2Ok HvOk).
    unfold no_model_names_as_bound_cvars_in_term. simpl.
    intros contra.
    unfold no_model_names_as_bound_cvars_in_term in IHt1.
    unfold no_model_names_as_bound_cvars_in_term in IHt2.
    destruct contra as [M [contra H]].
    apply IdLS.Props.IdSetProps.Dec.F.union_1 in contra. 
    destruct contra as [contra | contra].
    apply IHt1. eexists; split; eassumption.
    apply IHt2. eexists; split; eassumption.
  - (* tabs *)
    rename i into y. rename t into T.
    assert (Ht0Ok : no_model_names_as_bound_cvars_in_term MTbl t0)
      by prove_no_model_names_as_bound_cvars_in_subterm.
    specialize (IHt v Ht0Ok HvOk).
    unfold no_model_names_as_bound_cvars_in_term. simpl.
    intros contra.
    unfold no_model_names_as_bound_cvars_in_term in IHt.
    destruct (beq_idP x y) as [Hxy | Hxy].
    + subst.
Admitted.

Lemma step_preserves_no_model_names_as_bound_cvars_in_term :
  forall CTbl MTbl,
    (*cptcontext_welldefined CTbl ->
    mdlcontext_welldefined CTbl MTbl -> *)
  forall (t t' : tm),
    no_model_names_as_bound_cvars_in_term MTbl t ->
    CTbl $ MTbl ; t #==> t' ->
    no_model_names_as_bound_cvars_in_term MTbl t'.
Proof.
  intros CTbl MTbl (*HCTOk HMTOk*) t.
  induction t;
    intros t' HtOk HE;
    inversion HE; subst; simpl.

  - (* ST_AppAbs *)
    apply substitution_preserves_no_model_names_in_term;
      try assumption.
    prove_no_model_names_as_bound_cvars_in_subterm.
    prove_no_model_names_as_bound_cvars_in_subterm.
  - (* ST_App1 *)
    assert (Ht1Ok : no_model_names_as_bound_cvars_in_term MTbl t1)
      by prove_no_model_names_as_bound_cvars_in_subterm. 
    assert (Ht2Ok : no_model_names_as_bound_cvars_in_term MTbl t2)
      by prove_no_model_names_as_bound_cvars_in_subterm. 
    specialize (IHt1 t1' Ht1Ok H2).
    unfold no_model_names_as_bound_cvars_in_term. simpl.
    intros contra.
    unfold no_model_names_as_bound_cvars_in_term in IHt1.
    unfold no_model_names_as_bound_cvars_in_term in Ht2Ok.
    destruct contra as [M [contra H]].
    apply IdLS.Props.IdSetProps.Dec.F.union_1 in contra. 
    destruct contra as [contra | contra].
    apply IHt1. eexists; split; eassumption.
    apply Ht2Ok. eexists; split; eassumption.
Admitted.


(* ----------------------------------------------------------------- *)
(** **** Main Soundness Theorem *)
(* ----------------------------------------------------------------- *)

Definition normal_form CTbl MTbl (t : tm) : Prop :=
  ~ (exists t', CTbl $ MTbl ; t #==> t').

Definition stuck CTbl MTbl (t : tm) : Prop :=
  (normal_form CTbl MTbl t) /\ ~ value t.


Corollary soundness : 
  forall CTbl MTbl t t' T,
    no_model_names_as_bound_cvars_in_term MTbl t ->
    (* term has a type *)
    CTbl $ MTbl ; ctxempty ||- t \in T ->
    (* term makes a step *)
    CTbl $$ MTbl ;; t #==>* t' ->
    (* then a new term is not stuck *)
    ~ (stuck CTbl MTbl t').
Proof.
  intros CTbl MTbl t t' T HtOk Hhas_type Hmulti. 
  unfold stuck.
  intros [Hnf Hnot_val]. unfold normal_form in Hnf.
  induction Hmulti.
  - (* no step from t *)
    apply progress in Hhas_type.
    inversion Hhas_type as [Hval | Hstep].
    + (* t is value *)
      apply Hnot_val in Hval. contradiction.
    + (* t ==> t' *)
      apply Hnf in Hstep. contradiction.
  - (* t ==> t' *)
    remember (preservation _ _ _ _ _ HtOk Hhas_type H) as Ht'. clear HeqHt'.
    apply IHHmulti in Ht'; auto.
    apply step_preserves_no_model_names_as_bound_cvars_in_term
    with CTbl t1; try assumption.
Qed.
