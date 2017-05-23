(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(* Simply Typed Lambda Calculus with simple Concept Parameters
   :: version a
   Properties

   Properties of STLC are based on
   Sofware Foundations, v.4 
  
   Last Update: Mon, 22 May 2017
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
Require Import ConceptParams.GenericModuleLib.MIntrfs1.

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

Module ty_DataOkProp <: DataOkProp ty_Data ty_DataOkDef ty_DataOkInterp.
  Definition is_ok_b__sound := type_valid_b__sound.
  Definition is_ok_b__complete := type_valid_b__complete.
End ty_DataOkProp.

Module conceptProps := MIntrfs1Props 
                         ty_Intrfs1Base 
                         ty_DataOkDef ty_DataOkInterp ty_DataOkProp.

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
  unfold concept_welldefined, conceptDefs.intrfs_ok.
  destruct (split (map namedecl_to_pair nmtps)) as [nms tps] eqn:Heq.
  (* For some reason, just [rewrite] cannot handle [split (map ...)] *)
  intros CT CT'.
  rewrite Heq at 1. rewrite Heq at 1.
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
  unfold conceptInterp.intrfs_ok_b in *.
  destruct (split (map namedecl_to_pair nds)) as [nms tps] eqn:Heq.
  rewrite Heq in HCdef at 1. 
  rewrite andb_true_iff in HCdef. inversion HCdef as [Hun Hok].
  apply IdLS.Props.ids_are_unique__sound in Hun.
  apply split_fst__map_fst in Heq. subst. assumption.
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



(* ################################################################# *)
(** ** Soundness *)
(* ################################################################# *)

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


Theorem progress : forall CTbl MTbl t T,
     CTbl $ MTbl ; ctxempty |- t \in T ->
     value t \/ exists t', CTbl $ MTbl ; t #==> t'.
Proof.
  intros CTbl MTbl.
  intros t T HT.
  (* [remember] is a technical moment: otherwise information 
     about emptiness of Gamma is lost. *)
  remember ctxempty as Gamma.
  induction HT; subst Gamma; eauto.
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



Abort.


