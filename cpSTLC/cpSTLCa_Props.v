(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(* Simply Typed Lambda Calculus with simple Concept Parameters
   :: version a
   Properties

   Properties of STLC are based on
   Sofware Foundations, v.4 
  
   Last Update: Mon, 12 Jun 2017
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

Lemma free_in_context : forall CTbl MTbl x t T Gamma,
   appears_free_in CTbl MTbl x t ->
   CTbl $ MTbl ; Gamma |- t \in T ->
   (exists T', Gamma x = Some (tmtype T'))
   \/ (exists C, Gamma x = Some (cpttype C))
   \/ (exists MT, IdLPM.IdMap.find x MTbl = Some MT).
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
    left. exists T. assumption.
  - (* tabs *)
    rename i into y. rename t into T11.
    rewrite IdLS.Props.IdSetProps.Dec.F.remove_iff in Hfree.
    destruct Hfree as [Hfree Heqxy]. unfold IdUOT.eq in *.
    specialize (IHt _ _ Hfree H6).
    destruct IHt as [IHt | IHt];
      [ idtac | destruct IHt as [IHt | IHt] ];
      destruct IHt as [V HV];
      [ left | right; left | right; right ]; exists V;
        pose proof (update_neq _ (tmtype T11) x y Gamma Heqxy) as HG;
        [ rewrite <- HG | rewrite <- HG | idtac ]; assumption.
  - (* tcabs *)
    rename i into c. rename i0 into C.
    rewrite IdLS.Props.IdSetProps.Dec.F.remove_iff in Hfree.
    destruct Hfree as [Hfree Heqxy]. unfold IdUOT.eq in *.
    specialize (IHt _ _ Hfree H7).
    destruct IHt as [IHt | IHt];
      [ idtac | destruct IHt as [IHt | IHt] ];
      destruct IHt as [V HV];
      [ left | right; left | right; right ]; exists V;
      pose proof (update_neq _ (cpttype C) x c Gamma Heqxy) as HG;
      [ rewrite <- HG | rewrite <- HG | idtac ]; assumption.
  - (* [tcinvk c f] for c#C \in Gamma *)
    rename i into c. rename i0 into f.
    apply IdLS.Props.IdSetProps.FM.singleton_1 in Hfree.
    unfold IdUOT.eq in Hfree. subst.
    right. left. exists C. assumption.
  - (* [tcinvk M f] *)
    rename i into M. rename i0 into f.
    apply IdLS.Props.IdSetProps.FM.singleton_1 in Hfree.
    unfold IdUOT.eq in Hfree. subst.
    right. right. eexists. eassumption.
  - (* tlet *)
    rename i into y.
    apply IdLS.Props.IdSetProps.FM.union_1 in Hfree.
    destruct Hfree as [Hfree | Hfree].
    + specialize (IHt1 _ Gamma Hfree H6); assumption.
    + rewrite IdLS.Props.IdSetProps.Dec.F.remove_iff in Hfree.
      destruct Hfree as [Hfree Heqxy]. unfold IdUOT.eq in *.
      specialize (IHt2 _ _ Hfree H7). 
      destruct IHt2 as [IHt2 | IHt2];
        [ idtac | destruct IHt2 as [IHt2 | IHt2] ];
      destruct IHt2 as [V HV];
      [ left | right; left | right; right ]; exists V;
      pose proof (update_neq _ (tmtype T1) x y Gamma Heqxy) as HG;
      [ rewrite <- HG | rewrite <- HG | idtac ]; assumption.
Qed.

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



Lemma has_type_in_empty_context__only_model_free_vars :
  forall CTbl MTbl t T,
    CTbl $ MTbl ; ctxempty |- t \in T ->
    forall x, 
      appears_free_in CTbl MTbl x t ->
      exists C Mbody Cbody,
        IdLPM.IdMap.find x MTbl = Some (MTdef C Mbody)
        /\ IdLPM.IdMap.find C CTbl = Some (CTdef Cbody).
Proof.
  intros CTbl MTbl t.
  induction t;
    intros T HT x Hapfree;
    (inversion HT; subst; simpl).
  - (* tvar *)
    inversion H3.
  - (* tapp *)
    unfold appears_free_in in Hapfree. simpl in Hapfree.
    apply IdLS.Props.IdSetProps.Dec.F.union_1 in Hapfree.
    destruct Hapfree as [Hapfree | Hapfree].
    
(*
 T HT. (* free_in_context *)
  induction HT
*)
Abort.


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
    (* M is not in MTbl *)                 
    ~ IdLPM.IdMap.In M MTbl ->
    (* M is not used for concept parameter names *)
    ~ IdLS.IdSet.In M (bound_cvars tf) ->
    (* Gamma' contains not-to-qualify variables from Gamma *)
    (forall x, Gamma x <> None ->
               (~ IdLS.IdSet.In x mdlmems 
                \/ exists xC, Gamma x = Some (cpttype xC)) -> 
               Gamma' x = Gamma x) ->
    (* Gamma' does not contain M as a concept parameter *)
    ~ (exists MC, Gamma' M = Some (cpttype MC)) ->
    (* Gamma' does not contain other model names from MTbl *)
    no_model_names_as_cvars_in_Gamma MTbl Gamma' ->
    let MTbl' := IdLPM.IdMap.add M (MTdef C Mbody) MTbl in
    let tf'   := qualify_model_members' M mdlmems tf in 
    CTbl $ MTbl' ; Gamma' |- tf' \in Tf.
Proof.
  intros CTbl MTbl Gamma tf. generalize dependent Gamma.
  induction tf;
    intros Gamma Tf mdlmems C Cbody M Mbody Gamma';
    intros HT HtfMT HfindC HGamma HMnin HMtf HGamma' HGamma'M HGamma'MTbl;
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
          => apply IHst with Gamma Cbody;
             try (assumption || prove_no_bound_cvar_in_subterm
                  || prove_no_model_names_as_bound_cvars_in_subterm)
        end ].
  - (* tvar *)
    rename i into f.
    destruct (IdLS.IdSet.mem f mdlmems) eqn:Hmemf.
    + (* f in mdlnames *)
      apply T_MInvk with C Mbody.
      assumption.
      apply IdMapProps.F.add_eq_o. reflexivity.
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
    apply IHtf1 with Gamma Cbody; 
      try (assumption || prove_no_bound_cvar_in_subterm
          || prove_no_model_names_as_bound_cvars_in_subterm).
    apply IHtf2 with Gamma Cbody; 
      try (assumption || prove_no_bound_cvar_in_subterm
          || prove_no_model_names_as_bound_cvars_in_subterm).
  - (* tabs *)
    rename i into x. rename t into T.
    apply T_Abs.
    apply IHtf with (Gamma := update Gamma x (tmtype T)) (Cbody := Cbody);
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
      assert (HN : IdLPM.IdMap.find N MTbl <> None).
      { intros contra. rewrite H4 in contra. inversion contra. }
      apply IdMapProps.F.in_find_iff in HN.
      rewrite IdMapProps.F.add_neq_o. assumption.
      intros contra. unfold IdUOTOrig.eq in contra. subst.
      apply HMnin in HN. contradiction.
    + (* typing *) 
      apply IHtf with Gamma Cbody; assumption.
  - (* tcabs *)
    rename i into c. rename i0 into C'.
    apply T_CAbs with Cbody0. assumption.
    apply IHtf with (Gamma := update Gamma c (cpttype C')) (Cbody := Cbody);
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
    + (* no_bound_cvars *)
      simpl in HMtf. 
      destruct (beq_idP M c) as [HcM | HcM].
      * (* c = M *)
        subst. 
        assert (contra : IdLS.IdSet.In c (IdLS.IdSet.add c (bound_cvars tf))).
        { apply IdLS.Props.IdSetProps.Dec.F.add_1. reflexivity. }
        apply HMtf in contra. contradiction.
      * (* c <> M *)
        intros contra. apply HMtf.
        apply IdLS.Props.IdSetProps.Dec.F.add_2. assumption.
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
      simpl in HMtf.
      intros HGM'. destruct HGM' as [MC HGM'].
      destruct (beq_idP c M) as [HcM | HcM].
      * subst. 
        assert (contra : IdLS.IdSet.In M (IdLS.IdSet.add M (bound_cvars tf))).
        { apply IdLS.Props.IdSetProps.Dec.F.add_1. reflexivity. }
        apply HMtf in contra. contradiction.
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
    + (* find N *)
      rewrite IdMapProps.F.add_neq_o. assumption.
      intros contra. unfold IdUOTOrig.eq in contra. subst.
      apply HMnin. apply IdMapProps.F.in_find_iff.
      intros contra. rewrite H5 in contra. inversion contra.
  - (* tlet *)
    rename i into x. 
    apply T_Let with T1.
    apply IHtf1 with Gamma Cbody; 
      try (assumption || prove_no_bound_cvar_in_subterm
          || prove_no_model_names_as_bound_cvars_in_subterm).    
    apply IHtf2 with (Gamma := update Gamma x (tmtype T1)) (Cbody := Cbody);
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
    + prove_no_bound_cvar_in_subterm.
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
    (* M is not in MTbl *)                 
    ~ IdLPM.IdMap.In M MTbl ->
    (* M is not used for concept parameter names *)
    ~ IdLS.IdSet.In M (bound_cvars tf) ->
    let MTbl' := IdLPM.IdMap.add M (MTdef C Mbody) MTbl in
    let tf'   := qualify_model_members' M mdlmems tf in 
    CTbl $ MTbl' ; ctxempty |- tf' \in Tf.
Proof.
  intros CTbl MTbl Gamma tf Tf mdlmems C Cbody M Mbody.
  intros HT HMTtf HfindC HGamma Hmems Hnin HMnin.
  simpl. 
  apply qualify_model_members'_preserves_typing_for_good_Gamma'
    with Gamma Cbody; 
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
         (tf : tm) (Tf : ty)
         Gamma mdlmems,
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
         (tf : tm) (Tf : ty)
         mdlmems,
    (* [tf] has type [Tf] *)
    CTbl $ MTbl ; ctxempty |- tf \in Tf ->
    (* term does not contain concept vars named as model names *)
    no_model_names_as_bound_cvars_in_term MTbl tf ->
    (* M is not in MTbl *)                 
    ~ IdLPM.IdMap.In M MTbl ->
    (* M is not used for concept parameter names *)
    ~ IdLS.IdSet.In M (bound_cvars tf) ->
    let tf' := qualify_model_members' M mdlmems tf in 
    tf = tf'.
Proof.
  intros CTbl MTbl M tf Tf mdlmems HT Hcvars HninM HtfM.
  apply qualify_model_members'_preserves_term_in_empty'
  with CTbl MTbl Tf ctxempty;
    try assumption.
  intros x contra. 
  unfold ctxempty in contra. rewrite apply_empty in contra.
  exfalso. apply contra. reflexivity.
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
         (fun (okAndCl : Prop * id_ty_map) (dt : id * tm) =>
            let (ok, cl) := okAndCl in
            (let (nm, d) := dt in
             model_member_valid CTbl MTbl mdlnames Cbody cl nm d /\ ok,
             let (nm, _) := dt in
             match find_ty nm Cbody with
             | Some tp => IdLPM.IdMap.add nm tp cl
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
                 | Some tp => IdLPM.IdMap.add nm tp cl
                 | None => cl
                 end) 
             H).
  tauto.
Qed.


Lemma fold_left_members_ok__last_cl_includes_cl :
  forall CTbl MTbl mdlnames Cbody pnds P cl okF clF,
    (okF, clF)
    = (fold_left
         (fun (okAndCl : Prop * id_ty_map) (dt : id * tm) =>
            let (ok, cl) := okAndCl in
            (let (nm, d) := dt in
             model_member_valid CTbl MTbl mdlnames Cbody cl nm d /\ ok,
             let (nm, _) := dt in
             match find_ty nm Cbody with
             | Some tp => IdLPM.IdMap.add nm tp cl
             | None => cl
             end))
         pnds
         (P, cl)) ->
    okF ->
    (~ exists f, IdLPM.IdMap.In f cl /\ List.In f (map fst pnds)) ->
    List.NoDup (map fst pnds) ->
    forall f Tf,
      IdLPM.IdMap.MapsTo f Tf cl ->
      IdLPM.IdMap.MapsTo f Tf clF.
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
                 | Some tp => IdLPM.IdMap.add f tp cl
                 | None => cl
                 end)).
  specialize (IHpnds' okF clF Heqfold).
  apply IHpnds'; try assumption.
  - (* no bad name *)
    intros Hexcontra.
    destruct Hexcontra as [f0 [Hf0incl Hf0inpnds']].
    destruct (find_ty f Cbody) eqn:Heqfind.
    + rewrite IdMapProps.F.add_in_iff in Hf0incl.
      destruct Hf0incl as [Hf0 | Hf0].
      * unfold IdUOTOrig.eq in Hf0. subst.
        inversion Hnodup. subst.
        apply H1 in Hf0inpnds'. contradiction.
      * apply Hpndsok. exists f0.
        split. assumption. right. assumption.
    + apply Hpndsok. exists f0. 
      split. assumption. right. assumption.
  - (* no dup *)
    inversion Hnodup. subst. assumption.
  - (* mapsto *)
    destruct (find_ty f Cbody) eqn:Hfind.
    + destruct (beq_idP f f') as [Hff' | Hff'].
      * subst. exfalso. apply Hpndsok.
        exists f'. split. 
        unfold IdLPM.IdMap.In. 
        exists tf'. assumption.
        left; reflexivity.
      * apply IdMapProps.F.add_neq_mapsto_iff; assumption.
    + assumption.
Qed.
  
Lemma elem_in_cl__elem_in_derived_Gamma :
  forall cl cl' Gamma Gamma',
    (forall f Tf,
      IdLPM.IdMap.MapsTo f Tf cl ->
      IdLPM.IdMap.MapsTo f Tf cl') ->
    Gamma 
    = IdLPM.IdMap.fold
        (fun (nm : IdLPM.IdMap.key) (tp : ty) (G : partial_map ctxvarty) =>
           update G nm (tmtype tp)) 
        cl ctxempty ->
    Gamma'
    = IdLPM.IdMap.fold
        (fun (nm : IdLPM.IdMap.key) (tp : ty) (G : partial_map ctxvarty) =>
           update G nm (tmtype tp)) 
        cl' ctxempty ->
    forall x,
      Gamma x <> None ->
      Gamma' x = Gamma x.
Proof.
  pose proof (@IdLPM.Props.IdMapProps.fold_rec ty context) as Hind.
  remember 
    (fun cl Gamma =>
       forall (cl' : IdLPM.IdMap.t ty) (Gamma' : partial_map ctxvarty),
         (forall (f : IdLPM.IdMap.key) (Tf : ty),
             IdLPM.IdMap.MapsTo f Tf cl -> IdLPM.IdMap.MapsTo f Tf cl') ->
         Gamma =
         IdLPM.IdMap.fold
           (fun (nm : IdLPM.IdMap.key) (tp : ty) (G : partial_map ctxvarty) =>
              update G nm (tmtype tp)) cl ctxempty ->
         Gamma' =
         IdLPM.IdMap.fold
           (fun (nm : IdLPM.IdMap.key) (tp : ty) (G : partial_map ctxvarty) =>
              update G nm (tmtype tp)) cl' ctxempty ->
         forall x : id, Gamma x <> None -> Gamma' x = Gamma x)
    as P.
  remember (fun (nm : IdLPM.IdMap.key) (tp : ty) (G : partial_map ctxvarty) =>
              update G nm (tmtype tp))
    as f.
(*
  specialize (Hind P f).
  intros cl. specialize (Hind ctxempty cl).
  intros cl' Gamma. generalize dependent cl'. 
  assert (Hind_empty : 
            forall m : IdLPM.IdMap.t ty, IdLPM.IdMap.Empty m -> P m ctxempty).
  { intros m Hempty.
    subst P. intros.
    unfold ctxempty in *. 
    rewrite apply_empty in H2. tauto. }
  specialize (Hind Hind_empty). clear Hind_empty.
  
  assert (Hind_step :
            (forall (k : IdLPM.IdMap.key) (e : ty) (a : context)
                    (m' m'' : IdLPM.IdMap.t ty),
                IdLPM.IdMap.MapsTo k e cl ->
                ~ IdLPM.IdMap.In k m' ->
                IdLPM.Props.IdMapProps.Add k e m' m'' -> 
                P m' a -> P m'' (f k e a))).
  { intros nm tp Gamma0 m' m''.
    intros Hmapscl Hnotinnm Haddnm.
    intros Hm'. subst P. 
    intros cl' Gamma' Hcl' HGamma0 HGamma' z Hnone.
    destruct (beq_idP z nm


(*  generalize dependent Gamma. generalize dependent cl. *)
  specialize (Hind ctxempty).
  

  rewrite <- HeqP.
  


  pose proof (@IdLPM.Props.IdMapProps.map_induction ty) as Hind.
  remember (fun cl =>
              forall (cl' : IdLPM.IdMap.t ty) (Gamma Gamma' : partial_map ctxvarty),
                (forall (f : IdLPM.IdMap.key) (Tf : ty),
                    IdLPM.IdMap.MapsTo f Tf cl -> IdLPM.IdMap.MapsTo f Tf cl') ->
                Gamma =
                IdLPM.IdMap.fold
                  (fun (nm : IdLPM.IdMap.key) (tp : ty) (G : partial_map ctxvarty) =>
                     update G nm (tmtype tp)) cl ctxempty ->
                Gamma' =
                IdLPM.IdMap.fold
                  (fun (nm : IdLPM.IdMap.key) (tp : ty) (G : partial_map ctxvarty) =>
                     update G nm (tmtype tp)) cl' ctxempty ->
                forall x : id, Gamma x <> None -> Gamma' x = Gamma x)
           as P.
  specialize (Hind P). 
  intros cl. rewrite <- (HeqP cl).

apply Hind.

  apply Hind with (m := cl).
  - (* empty case *)
    intros.


  apply IdLPM.Props.IdMapProps.fold_rec.
  - (* empty case *)
    intros m Hempty cl' Gamma Gamma' Hcl'.
    intros HeqGamma HwqGamma' z contra.
    subst. unfold ctxempty in *. 
    rewrite apply_empty in contra. tauto.
  - (* inductive case *)
    intros nm tp Gamma0 m' m''.
    intros Hclmaps. intros Hnmm'.
    intros Hm'm''nm. 
    intros IH.
    intros cl' Gamma Gamma'.
    intros Hcl'. intros HeqGamma HeqGamma'.
    intros z HzGamma.
  
IdLPM.Props.IdMapProps .IdMap
*)
Abort.


Lemma fold_left_members_ok__ok_in_last_cl' :
  forall CTbl MTbl mdlnames Cbody pnds P cl,
    IdLS.IdSet.Subset (set_of_keys MTbl) mdlnames ->
    let (okF, clF) :=
      (fold_left
         (fun (okAndCl : Prop * id_ty_map) (dt : id * tm) =>
            let (ok, cl) := okAndCl in
            (let (nm, d) := dt in
             model_member_valid CTbl MTbl mdlnames Cbody cl nm d /\ ok,
             let (nm, _) := dt in
             match find_ty nm Cbody with
             | Some tp => IdLPM.IdMap.add nm tp cl
             | None => cl
             end))
         pnds
         (P, cl)) in
    okF ->
    forall f tf,
      List.In (f, tf) pnds ->
      model_member_valid CTbl MTbl mdlnames Cbody clF f tf.
Proof.
  intros CTbl MTbl mdlnames Cbody pnds.
  induction pnds as [| pnd pnds' IHpnds'];
    intros P cl Hsubset. 
  simpl. intros. contradiction.
  simpl. destruct pnd as [f' tf'].
  destruct (fold_left
                (fun (okAndCl : Prop * id_ty_map) (dt : id * tm) =>
                 let (ok, cl) := okAndCl in
                 (let (nm, d) := dt in
                  model_member_valid CTbl MTbl mdlnames Cbody cl nm d /\ ok,
                 let (nm, _) := dt in
                 match find_ty nm Cbody with
                 | Some tp => IdLPM.IdMap.add nm tp cl
                 | None => cl
                 end)) pnds'
                (model_member_valid CTbl MTbl mdlnames Cbody cl f' tf' /\ P,
                match find_ty f' Cbody with
                | Some tp => IdLPM.IdMap.add f' tp cl
                | None => cl
                end)) as [okF clF] eqn:Heq.
  intros HokF f tf Hin.
  destruct Hin as [Hin | Hin].
  - (* head *)
    inversion Hin. subst. clear Hin.
    assert (HokFeq : fst (
         fold_left
          (fun (okAndCl : Prop * id_ty_map) (dt : id * tm) =>
           let (ok, cl) := okAndCl in
           (let (nm, d) := dt in
            model_member_valid CTbl MTbl mdlnames Cbody cl nm d /\ ok,
           let (nm, _) := dt in
           match find_ty nm Cbody with
           | Some tp => IdLPM.IdMap.add nm tp cl
           | None => cl
           end)) pnds'
          (model_member_valid CTbl MTbl mdlnames Cbody cl f tf /\ P,
          match find_ty f Cbody with
          | Some tp => IdLPM.IdMap.add f tp cl
          | None => cl
          end)) = okF).
    { assert (Htriv : fst (okF, clF) = okF) by reflexivity.
      rewrite -> Heq. assumption. }
    assert (Hok : fst (
         fold_left
          (fun (okAndCl : Prop * id_ty_map) (dt : id * tm) =>
           let (ok, cl) := okAndCl in
           (let (nm, d) := dt in
            model_member_valid CTbl MTbl mdlnames Cbody cl nm d /\ ok,
           let (nm, _) := dt in
           match find_ty nm Cbody with
           | Some tp => IdLPM.IdMap.add nm tp cl
           | None => cl
           end)) pnds'
          (model_member_valid CTbl MTbl mdlnames Cbody cl f tf /\ P,
          match find_ty f Cbody with
          | Some tp => IdLPM.IdMap.add f tp cl
          | None => cl
          end))).
    { rewrite -> HokFeq. assumption. }
    pose proof (fold_left_members_ok__inital_prop _ _ _ _ _ _ _ 
                                                  Hok) as HfOk'.
    destruct HfOk' as [HfOk' _].

    unfold model_member_valid.
    unfold model_member_valid in HfOk'.
    destruct HfOk' as [Tf [Hfindf [Hcvarstf Hhas_type]]].
    exists Tf. repeat (split; try assumption).
    (* try to prove that for bigger context it's still Ok *)
    apply context_weakening 
    with (Gamma := 
            IdLPM.IdMap.fold
              (fun (nm : IdLPM.IdMap.key) (tp : ty)
                   (G : partial_map ctxvarty) => update G nm (tmtype tp)) 
              cl ctxempty).
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
      
(*

  specialize (IHpnds'
                (model_member_valid CTbl MTbl mdlnames Cbody cl f' tf' /\ P)
                (match find_ty f' Cbody with
                 | Some tp => IdLPM.IdMap.add f' tp cl
                 | None => cl
                 end)
             Hsubset).
  
  rewrite Heq in IHpnds'.
  intros okF.

HokF. f tf Hin.
*)
Abort.


Lemma abc :
  forall CTbl MTbl mdlnames M C Mbody' Mbody,
    model_has_type CTbl MTbl mdlnames (mdl_def M C Mbody') (MTdef C Mbody) ->
    IdLS.IdSet.Subset (set_of_keys MTbl) mdlnames ->
    IdLS.IdSet.In M mdlnames ->
    forall f tf, List.In (nm_def f tf) Mbody' ->
    ~ IdLPM.IdMap.In M MTbl ->
    exists Cbody Tf,
      IdLPM.IdMap.find C CTbl = Some (CTdef Cbody)
      /\ IdLPM.IdMap.find f Cbody = Some Tf
      /\ let MTbl' := IdLPM.IdMap.add M (MTdef C Mbody) MTbl in
         CTbl $ MTbl' ; ctxempty |- (qualify_model_members M Mbody tf) \in Tf.
Proof.
  intros CTbl MTbl mdlnames M C Mbody'.
  unfold model_has_type.
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
  induction Mbody' as [| nmdef nmdefs' IHnmdefs'].
  - (* Mbody' = nil *)
    simpl. intros. contradiction.
  - (* Mbody' = nmdef :: nmdefs' *)
    simpl. 
    intros Mbody [[Cbody HCbody] HeqMbody] Hsubset HM f tf Hnmdef.
    intros HMinMT.
    destruct HCbody as [HfindC Hmdl].
    destruct Hmdl as [[Hnodup HmdlOk] HCforall].
    destruct nmdef as [f' tf']. simpl in *.
    pose proof (fold_left_members_ok__inital_prop _ _ _ _ _ _ _ 
                                                  HmdlOk) as Hf'Ok.
    destruct Hf'Ok as [Hf'Ok _].
    destruct Hnmdef as [Hnmdef | Hnmdef].
    + (* head nmdef *)
      exists Cbody.
      inversion Hnmdef. subst. clear Hnmdef.
      unfold model_member_valid in Hf'Ok.
      destruct Hf'Ok as [Tf [Hfindf [Hnocvars HTtf]]].
      unfold ctxempty in HTtf. 
      compute in HTtf. 
      replace (fun _ : id => None) with ctxempty in HTtf.
      exists Tf. split.
      assumption. split. assumption.
      assert (Heqtf : tf = qualify_model_members M Mbody tf).
      { unfold qualify_model_members.
        apply qualify_model_members'_preserves_term_in_empty
          with CTbl MTbl Tf; try assumption;
          unfold no_bound_cvar_names_in_term in Hnocvars.
        (* part 1 *)
        unfold no_model_names_as_bound_cvars_in_term.
        intros contra. destruct contra as [M' [HM'tf HM']].
        unfold IdLS.IdSet.Subset in Hsubset.
        pose proof (in_map__in_set_of_keys _ _ _ HM') as HM'in.
        specialize (Hsubset M' HM'in).
        specialize (Hnocvars M' Hsubset).
        apply Hnocvars. assumption.
        (* part 2 *)
        intros contra.
        specialize (Hnocvars M HM).
        apply Hnocvars. assumption. }
      rewrite <- Heqtf; try reflexivity.
      apply mdlcontext_weakening with MTbl;
        try (assumption || reflexivity).
      intros M' C' M'body HfindM'.
      exists M'body. split.
      rewrite IdMapProps.F.add_neq_o; try assumption.
      (* M <> M' *)
      intros contra. unfold IdUOTOrig.eq in contra. subst M.
      apply IdMapProps.F.not_find_in_iff in HMinMT.
      rewrite HfindM' in HMinMT. inversion HMinMT. reflexivity.
      reflexivity.
    + (* inductive case *)
      apply IHnmdefs'; try assumption.
      split.
      exists Cbody. repeat (split; try assumption).
      inversion Hnodup; subst. assumption.

      remember (IdLPM.map_from_list (map namedef_to_pair nmdefs'))
        as Mbody'.
      specialize (IHnmdefs' Mbody').
      assert (Hprem : 
                exists fnmtys : id_ty_map,
                 IdLPM.IdMap.find C CTbl = Some (CTdef fnmtys) /\
                 (NoDup (map fst (map namedef_to_pair nmdefs')) /\
                  fst
                    (fold_left
                       (fun (okAndCl : Prop * id_ty_map) (dt : id * tm) =>
                        let (ok, cl) := okAndCl in
                        (let (nm, d) := dt in
                         model_member_valid CTbl MTbl mdlnames fnmtys cl nm d /\ ok,
                        let (nm, _) := dt in
                        match find_ty nm fnmtys with
                        | Some tp => IdLPM.IdMap.add nm tp cl
                        | None => cl
                        end)) (map namedef_to_pair nmdefs')
                       (True, IdLPM.IdMap.empty ty))) /\
                 Forall
                   (fun nm : id => In nm (map fst (map namedef_to_pair nmdefs')))
                   (map fst (IdLPM.IdMap.elements fnmtys))).
      { exists Cbody.
        repeat (split; try assumption).
        inversion Hnodup; subst. assumption.
(*    
    apply IHnmdefs'; try assumption.

      simpl in HeqMbody.
      unfold IdLPM.eq_list_map in HeqMbody.
      destruct HeqMbody as [_ [_ Hforall]].
      rewrite Forall_forall in Hforall.
      specialize (Hforall (f, tf)). simpl in Hforall.
      assert (Hfin : (f, tf) = (f, tf) 
                     \/ In (f, tf) (map namedef_to_pair nmdefs'))
        by (left; reflexivity).
      specialize (Hforall Hfin).
      IdLPM.Props .Helper
*)
Abort.


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


(*
Lemma abc' :
  forall CTbl MTbl M C,
    model_welldefined CTbl MTbl M ->
    forall (nm : id),
      IdLPM.IdMap.find nm CTbl = Some

Lemma abc :
  forall CTbl MTbl,
    cptcontext_welldefined CTbl ->
    mdlcontext_welldefined CTbl MTbl ->
    forall (nm : id),
      IdLPM.IdMap.find nm CTbl = Some
*)


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




(* 

  forall (CTbl : cptcontext) (MTbl : mdlcontext)
         (Gamma : context) (tf : tm) (Tf : ty),
    (* [tf] has type [Tf] *)
    CTbl $ MTbl ; Gamma |- tf \in Tf ->
    (* Gamma only contains term variables *)
    Gamma_of_tmtypes Gamma ->             
    forall C Cbody,
    (* we consider a concept consistent with Gamma *)
      IdLPM.IdMap.find C CTbl = Some (CTdef Cbody) ->
      cty_consistent_with_Gamma Cbody Gamma ->
    (* MTbl' is MTbl plus an appropriate model *)                 
      forall (MTbl' : mdlcontext) M Mbody,
        ~ IdLPM.IdMap.In M MTbl ->
        MTbl' = IdLPM.IdMap.add M (MTdef C Mbody) MTbl ->
    (* we qualify all the members from Gamma *)
        forall mdlnames, mdlnames_consistent_with_Gamma mdlnames Gamma ->
    (* then we can typecheck QMM'(M, mdlnames, tf) *)
        CTbl $ MTbl' ; ctxempty |- (qualify_model_members' M mdlnames tf) \in Tf.

*)

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

(*
Definition no_cvars_from_mdlnames_in_Gamma (mdlnames : id_set) (G : context) :=
  forall c C, G c = Some (cpttype C) ->
              ~ IdLS.IdSet.In c mdlnames.
*)









(*
Lemma qualify_model_members_empty_context : 
  forall CTbl MTbl t T,
    CTbl $ MTbl ; ctxempty |- t \in T ->
    forall M Mbody,
      qualify_model_members M Mbody t = t.
Proof.
  intros CTbl MTbl t.
  induction t;
    intros T HT M Mbody;
    inversion HT; subst; simpl;
    unfold qualify_model_members in *; simpl.
  - (* tvar *)
    inversion H3.
  - (* tapp *)
    erewrite IHt1.
    erewrite IHt2.
    reflexivity.
    eassumption. eassumption.
  - (* tabs *)
    rename i into x. rename t into T.
    

Abort.

Lemma qualify_model_members_empty_context : 
  forall CTbl MTbl t T,
    CTbl $ MTbl ; ctxempty |- t \in T ->
    forall M Mbody,
      qualify_model_members M Mbody t = t.
Proof.
  intros CTbl MTbl t.
  induction t;
    intros T HT M Mbody;
    inversion HT; subst; simpl;
    unfold qualify_model_members in *; simpl.
  - (* tvar *)
    inversion H3.
  - (* tapp *)
    erewrite IHt1.
    erewrite IHt2.
    reflexivity.
    eassumption. eassumption.
  - (* tabs *)
    rename i into x. rename t into T.
    

Abort.
*)


(** There is a subtelty in typing preservation for substitution.
    If [v] has type [S] in the empty context,
      it could be the case that v is equal to [M.f]
      where [M \in MTbl].
    It means that [v] could become badly-typed 
    in the context [Gamma] which contains [M].

    Thus, we can only consider [Gamma], which
    does not contain model-named variables.
 *)

(** We need even stronger requirement.

    Suppose we have
    * [v = M.f : Nat] (Note that FV(M.f) = M)
    * [t = \M:Nat.M + x]
    * [x : Nat]
    
    Then [x:=v]t = \M:Nat.M + M.f does not have a type.

    The problem is that model name [M] became bound
    in the term t.

    So we need that terms do not have shared 
    variables with MTable.
*)

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

Lemma substitution_preserves_typing : 
  forall CTbl MTbl Gamma x S t v T,
    cptcontext_welldefined CTbl ->
    mdlcontext_welldefined CTbl MTbl ->
    no_model_names_in_context CTbl MTbl Gamma ->
    no_model_names_in_term CTbl MTbl t ->
    CTbl $ MTbl ; (update Gamma x (tmtype S)) |- t \in T ->
    CTbl $ MTbl ; ctxempty |- v \in S -> 
    CTbl $ MTbl ; Gamma |- [x:=v] t \in T.
Proof.
  intros CTbl MTbl Gamma x S t v T HCTOk HMTOk.
  intros HGamma Hvars HTt HTv.
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
      => apply IHt; try assumption; prove_no_model_names_in_subterm 
    end ].
(* tvar *)
  - rename i into y. destruct (beq_idP x y). 
    + subst. 
      rewrite update_eq in H3. inversion H3. subst. clear H3.
      apply context_invariance with (Gamma := ctxempty);
        try assumption.
      intros x Hfree. 
      pose proof (free_in_context _ _ x v _ _ Hfree HTv) as Hv'.
      destruct Hv' as [HG | [HG | HG]]; unfold ctxempty in *.
      * inversion HG as [V HV]. 
        rewrite apply_empty in HV. inversion HV.
      * inversion HG as [V HV]. 
        rewrite apply_empty in HV. inversion HV.
      * unfold no_model_names_in_context in HGamma.
        specialize (HGamma x HG).
        rewrite apply_empty.
        destruct (Gamma x) eqn:Heq.
        { inversion HGamma. }
        { reflexivity. }
    + constructor.
      rewrite <- H3. symmetry.
      apply update_neq. assumption.
(* tapp *)
  - apply T_App with T11.
    + apply IHt1;
        [prove_no_model_names_in_subterm | assumption | assumption].
    + apply IHt2; 
        [prove_no_model_names_in_subterm | assumption | assumption].
(* tabs *)
  - rename i into y. rename t into T.
    destruct (beq_idP x y) as [Heqxy | Heqxy]. 
    + (* x = y *) 
      subst. 
      apply context_invariance with (update Gamma y (tmtype S));
        try assumption.
      intros x Hfree.
      destruct (beq_idP x y) as [Heqxy | Heqxy].
      * subst. unfold appears_free_in in Hfree.
        simpl in Hfree.
        assert (Htriv : y = y) by reflexivity.
        apply IdLS.Props.IdSetProps.Dec.F.remove_1
        with (s := free_vars CTbl MTbl t0) (x := y) (y := y) in Htriv.
        apply Htriv in Hfree. contradiction.
      * apply update_neq. intuition.
    + (* x <> y *)
      apply T_Abs.
      apply IHt. prove_no_model_names_in_subterm.
      * (* model names invariant *) 
        unfold no_model_names_in_context.
        intros z HM.
        inversion HM as [MT HMT]. 
        assert (Hin : IdLPM.IdMap.In z MTbl)
          by (apply MId.IdLPM.Props.IdMapProps.F.in_find_iff;
              intros contra; rewrite HMT in contra; inversion contra).        
        destruct (beq_idP y z) as [Hyz | Hyz].
        { subst. unfold no_model_names_in_term in Hvars.
          specialize (Hvars z Hin).
          exfalso. apply Hvars. simpl.
          auto using IdLS.Props.IdSetProps.Dec.F.union_2,
                     IdLS.Props.IdSetProps.FM.singleton_2. }
        { unfold no_model_names_in_context in HGamma.
          specialize (HGamma z HM).
          rewrite update_neq.  
          assumption. assumption. }
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
      apply IHt. prove_no_model_names_in_subterm.
      prove_no_model_names_in_upd_Gamma.
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
(*
  - rename i into M. rename i0 into f.
    apply T_MInvk with C Mbody; try assumption.
    apply update_none in H1. assumption.
(* tlet *)
  - rename i into y. 
    apply T_Let with T1.
    apply IHt1; try assumption. prove_no_model_names_in_subterm.
    destruct (beq_idP x y) as [Hxy | Hxy]. 
    + (* x = y *) 
      subst. 
      apply context_invariance 
      with (update (update Gamma y (tmtype S)) y (tmtype T1));
        try assumption.
      intros x _.
      rewrite update_shadow. reflexivity.
    + (* x <> y *)
      apply IHt2. prove_no_model_names_in_subterm.
      prove_no_model_names_in_upd_Gamma.
      apply context_invariance 
      with (update (update Gamma x (tmtype S)) y (tmtype T1)); 
        try assumption.
      intros z _. 
      apply update_permute_get; assumption. *)
Abort.
(*Qed.*)


(** There are subtelties with concept substitution as well. 
    
    Consider an example:
    * [Gamma = {c # MonoidNat, MMonoidSum : bool}]
    * [t = c.ident : MonoidNat # Nat]
    * [M = MMonoidSum]

    Then [#c := M] t = MMonoidSum.ident 
    cannot be typed in [Gamma]!

    And model names can only appear in a context
    if they are bound variables.
*)

(*
Lemma concept_substitution_preserves_typing : 
  forall CTbl MTbl Gamma c C t T M Mbody,
    cptcontext_welldefined CTbl ->
    mdlcontext_welldefined CTbl MTbl ->    
    no_model_names_in_context CTbl MTbl Gamma ->
    no_model_names_in_term CTbl MTbl t ->
    CTbl $ MTbl ; (update Gamma c (cpttype C)) |- t \in T ->
    IdLPM.IdMap.find M MTbl = Some (MTdef C Mbody) ->
    CTbl $ MTbl ; Gamma |- [#c:=M] t \in T.
Proof.
  intros CTbl MTbl Gamma c C t T M Mbody HCTOk HMTOk.
  intros HGamma Hvars HTt HMdef.
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
      [ IHt : context[ [#?c:=?M] ?s ]
        |- ?CTbl $ ?MTbl; ?Gamma |- [#?c := ?M] ?s \in ?T ]
      => apply IHt; try assumption; prove_no_model_names_in_subterm 
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
    + apply IHt1; try assumption. 
      prove_no_model_names_in_subterm.
    + apply IHt2; try assumption.
      prove_no_model_names_in_subterm.
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
      apply IHt. prove_no_model_names_in_subterm.
      prove_no_model_names_in_upd_Gamma.
      apply context_invariance 
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
        prove_no_model_names_in_subterm. 
        prove_no_model_names_in_upd_Gamma.
        apply context_invariance 
        with (update (update Gamma c (cpttype C)) c' (cpttype C'));
          try assumption.
        intros z _. apply update_permute_get; assumption.
(* tcinvk *)
    - rename i into c'. rename i0 into f.
      destruct (beq_idP c c') as [Hcc' | Hcc'].
      + (* c = c' *)
        subst.
        apply T_MInvk with C Mbody; try assumption.
        unfold no_model_names_in_context in HGamma;
          try assumption.
        assert (HMT : exists MT : mty, IdLPM.IdMap.find M MTbl = Some MT)
          by (exists (MTdef C Mbody); assumption).
        specialize (HGamma M HMT).
        destruct (Gamma M) eqn:Heq.
        * symmetry in Heq. inversion HGamma.
        * reflexivity.
        * rewrite update_eq in H4. inversion H4. subst. assumption.
      + (* c <> c' *)
        inversion HTt; subst.
        apply T_CInvk with C1.
        rewrite update_neq in H5. assumption. 
        assumption. assumption.
        rewrite H4 in H1. inversion H1.
(* tcinvk *)
    - rename i into M'. rename i0 into f.
      destruct (beq_idP c M') as [HcM' | HcM'].
      + (* c = M' *)
        subst.
        rewrite update_eq in H1. inversion H1.
      + (* c <> M' *)
        apply T_MInvk with C0 Mbody0; try assumption.
        apply update_none in H1. assumption.
(* tlet *)
    - rename i into y.
      apply T_Let with T1.
      apply IHt1; try assumption.
      prove_no_model_names_in_subterm.
      destruct (beq_idP c y) as [Hcy | Hcy].
      + (* c = y *)
        subst.
        apply context_invariance 
        with (update (update Gamma y (cpttype C)) y (tmtype T1));
          try assumption.
        intros z _. rewrite update_shadow. reflexivity.
      + (* c <> y *)
        apply IHt2; try assumption.
        prove_no_model_names_in_subterm.
        prove_no_model_names_in_upd_Gamma.
        apply context_invariance 
        with (update (update Gamma c (cpttype C)) y (tmtype T1));
          try assumption.
        intros z _. apply update_permute_get; assumption.
Qed.


Lemma no_model_names_in_empty_context :
  forall CTbl MTbl,
    no_model_names_in_context CTbl MTbl ctxempty.
Proof.
  intros CTbl MTbl.
  unfold no_model_names_in_context.
  intros x H.
  reflexivity.
Qed.


Fixpoint concept_names_ty (T : ty) : id_set :=
  match T with
  | TBool => IdLS.IdSet.empty
  | TNat  => IdLS.IdSet.empty
  | TArrow T1 T2     => IdLS.IdSet.union (concept_names_ty T1) (concept_names_ty T2)
  | TConceptPrm C T1 => IdLS.IdSet.add C (concept_names_ty T1)
  end.

Fixpoint concept_names_tm (t : tm) : id_set := 
  match t with
  | tvar x      => IdLS.IdSet.empty  
  | tapp t1 t2  => IdLS.IdSet.union (concept_names_tm t1) (concept_names_tm t2)
  | tabs x T t  => IdLS.IdSet.union (concept_names_ty T) (concept_names_tm t)
  | tmapp t M   => concept_names_tm t   
  | tcabs c C t => IdLS.IdSet.add C (concept_names_tm t)
  | tcinvk c f  => IdLS.IdSet.empty
  | ttrue       => IdLS.IdSet.empty
  | tfalse      => IdLS.IdSet.empty
  | tif t1 t2 t3 => IdLS.IdSet.union 
                      (IdLS.IdSet.union (concept_names_tm t1) (concept_names_tm t2)) 
                      (concept_names_tm t3)
  | tnat n      => IdLS.IdSet.empty
  | tsucc t     => concept_names_tm t
  | tpred t     => concept_names_tm t
  | tplus t1 t2  => IdLS.IdSet.union (concept_names_tm t1) (concept_names_tm t2)
  | tminus t1 t2 => IdLS.IdSet.union (concept_names_tm t1) (concept_names_tm t2)
  | tmult t1 t2  => IdLS.IdSet.union (concept_names_tm t1) (concept_names_tm t2)
  | teqnat t1 t2 => IdLS.IdSet.union (concept_names_tm t1) (concept_names_tm t2)
  | tlenat t1 t2 => IdLS.IdSet.union (concept_names_tm t1) (concept_names_tm t2)
  | tlet x t1 t2 => IdLS.IdSet.union (concept_names_tm t1) (concept_names_tm t2)
  end.




(** The problem with preservation is when we make a step from
    [M.f] to [QMM(tf)], the definition of [f] in the model [M]
    where all names referring to the [M] members 
    are replaced with qualified names.

    We have to know that the type is preserved for the
    member definition [tf].
 *)

Ltac prove_appears_free_in_superterm :=
  match goal with
    [ HGFree : forall x : id,
               appears_free_in ?CTbl ?MTbl x ?t ->
               ~ IdLS.IdSet.In x ?mdlmems -> 
               ?Gamma x = ?Gamma' x
      |- forall x : id,
         appears_free_in ?CTbl ?MTbl x ?s ->
         ~ IdLS.IdSet.In x ?mdlmems -> 
         ?Gamma x = ?Gamma' x ]
    => intros x_f Hfree_x (*Hnotin_x*);
       apply HGFree; unfold appears_free_in; simpl;
       unfold appears_free_in in Hfree_x;
       auto using IdLS.Props.IdSetProps.Dec.F.union_2,
                  IdLS.Props.IdSetProps.Dec.F.union_3,
                  IdLS.Props.IdSetProps.Dec.F.singleton_2;
       assumption
    end.


Lemma qualify_model_members_preserves_typing' :
  forall (CTbl : cptcontext) (MTbl : mdlcontext)
         C Mbody
         Gamma (t : tm) (T : ty) M mdlmems Gamma',
    (* term [t] has type [T] under Gamma *)
    CTbl $ MTbl ; Gamma |- t \in T ->
    (* [M] is a valid model name *)
    IdLPM.IdMap.find M MTbl = Some (MTdef C Mbody) ->
    (* mdlmems is a subset of names from Mbody *)
    IdLS.IdSet.Subset mdlmems (set_of_keys Mbody) ->
    (* all variables in Gamma from mdlmems can be type-preservingly
       qualified with [M] *)
    (forall (x : id), 
        Gamma x <> None ->
        IdLS.IdSet.In x mdlmems ->
        (exists GT,
            Gamma x = Some (tmtype GT) 
            /\ CTbl $ MTbl ; ctxempty |- tcinvk M x \in GT )) ->
    (* all other important variables from Gamma appear in Gamma' *)
    (forall x, 
        appears_free_in CTbl MTbl x t -> 
        ~ IdLS.IdSet.In x mdlmems ->
        Gamma x = Gamma' x) ->
    (* Gamma' does not contain model names' variables *)
    no_model_names_in_context CTbl MTbl Gamma' ->
    (* No bad names in term *)
    no_model_names_in_term CTbl MTbl t ->
    (* then the qualified term has type [T] under the empty context *)
    CTbl $ MTbl ; Gamma' |- (qualify_model_members' M mdlmems t) \in T.
Proof.
  intros CTbl MTbl C Mbody Gamma t. generalize dependent Gamma.
  induction t;
    intros Gamma T M mdlmems Gamma' 
           HT HMfind Hmems HGamma Hapfree HGamma' HtOk;
    inversion HT; subst; simpl;
      unfold qualify_model_members in *; simpl;
      unfold id_mem in *;
    (* in simple cases such as [ttrue] we can apply constructor *)
    try solve [constructor; assumption];
    (* for regular inductive cases we can apply IHs *)
    try solve [
          constructor;
          match goal with
            [ IHt : context[ (*_ -> (has_type _ _ _ _ _)*)
                        no_model_names_in_term ?CTbl ?MTbl ?s 
                      ]
              |- context[ ?s ] (*?CTbl $ ?MTbl; ?Gamma |- ?s \in ?S*) ] 
            => apply IHt with Gamma; 
               (assumption || prove_appears_free_in_superterm ||
                prove_no_model_names_in_subterm)
          end ].
 - (* tvar *)
    rename i into x.
    destruct (IdLS.IdSet.mem x mdlmems) eqn:Heq;
      unfold id_mem in *.
    + (* x to qualify *) 
      apply IdLS.Props.IdSetProps.Dec.F.mem_2 in Heq.
      assert (Hnone : Gamma x <> None).
      { intros contra. rewrite H3 in contra. inversion contra. }
      specialize (HGamma x Hnone Heq). 
      destruct HGamma as [GT [Heqx HGamma]].
      inversion HGamma; subst. inversion H5.
      apply T_MInvk with C0 Mbody0; try assumption.
      unfold no_model_names_in_context in HGamma'.
      apply HGamma'; try assumption. 
      eexists; eassumption. 
      rewrite H3 in Heqx. inversion Heqx. subst. assumption.
    + (* x not touched *)
      apply T_Var.
      rewrite <- H3. symmetry.
      apply Hapfree.
      unfold appears_free_in in *. simpl in *.
      apply IdLS.Props.IdSetProps.Dec.F.singleton_2; reflexivity.
      apply IdLS.Props.IdSetProps.Dec.F.not_mem_iff. assumption.
  - (* tapp *)
    apply T_App with T11.
    apply IHt1 with Gamma; (assumption || prove_appears_free_in_superterm ||
                            prove_no_model_names_in_subterm).
    apply IHt2 with Gamma; (assumption || prove_appears_free_in_superterm ||
                           prove_no_model_names_in_subterm).
  - (* tabs *)
    rename i into x. rename t into T.
    apply T_Abs.
    apply IHt with (update Gamma x (tmtype T));
      try (assumption || prove_no_model_names_in_upd_Gamma || 
           prove_no_model_names_in_subterm).      
    + (* trans *)
      destruct (IdLS.IdSet.mem x mdlmems) eqn:Hxmem.
      * pose proof IdLS.Props.IdSetProps.Dec.F.Subset_trans as Htrans.
        unfold RelationClasses.Transitive in Htrans.
        apply Htrans with mdlmems.
        unfold IdLS.IdSet.Subset. 
        intros z Hinz.
        apply IdLS.Props.IdSetProps.Dec.F.remove_3 in Hinz. 
        assumption. assumption.
      * assumption.
    + intros z Hnone Hin.
      destruct (IdLS.IdSet.mem x mdlmems) eqn:Hxmem;
        destruct (beq_idP x z) as [Hxz | Hxz].
      * subst.
        assert (Htriv : z = z) by reflexivity. 
        apply IdLS.Props.IdSetProps.Dec.F.remove_1 
        with (s := mdlmems) in Htriv.
        apply Htriv in Hin. contradiction.
      * rewrite update_neq; try assumption. 
        rewrite update_neq in Hnone; try assumption.
        apply IdLS.Props.IdSetProps.Dec.F.remove_3 in Hin.
        specialize (HGamma z Hnone Hin). 
        assumption.
      * subst.
        rewrite <- IdLS.Props.IdSetProps.Dec.F.not_mem_iff in Hxmem.
        apply Hxmem in Hin. contradiction.
      * rewrite update_neq. rewrite update_neq in Hnone; try assumption.
        apply HGamma; try assumption. assumption.
    + (* appears_free *)
      intros z Hfree Hin.
      destruct (beq_idP x z) as [Hxz | Hxz].
      ** subst.
         repeat rewrite update_eq.
         reflexivity.
      ** repeat rewrite update_neq; try assumption.
         apply Hapfree.
         unfold appears_free_in in *.
         simpl.
         apply IdLS.Props.IdSetProps.Dec.F.remove_neq_iff;
           assumption.
         destruct (IdLS.IdSet.mem x mdlmems) eqn:Hxmem.
         { rewrite IdLS.Props.IdSetProps.Dec.F.remove_neq_iff in Hin;
             assumption. }
         { assumption. }
  - (* tmapp *)
    rename i into M'.
    apply T_MApp with C0 Mbody0; try assumption.
    apply IHt with Gamma; try assumption.
  - (* tcabs *)
    rename i into c. rename i0 into C'.
    apply T_CAbs with Cbody; try assumption.
    apply IHt with (update Gamma c (cpttype C'));
      try (assumption || prove_no_model_names_in_upd_Gamma || 
           prove_no_model_names_in_subterm).      
    + (* trans *)
      destruct (IdLS.IdSet.mem c mdlmems) eqn:Hxmem.
      * pose proof IdLS.Props.IdSetProps.Dec.F.Subset_trans as Htrans.
        unfold RelationClasses.Transitive in Htrans.
        apply Htrans with mdlmems.
        unfold IdLS.IdSet.Subset. 
        intros z Hinz.
        apply IdLS.Props.IdSetProps.Dec.F.remove_3 in Hinz. 
        assumption. assumption.
      * assumption.
    + intros z Hnone Hin.
      destruct (IdLS.IdSet.mem c mdlmems) eqn:Hxmem;
        destruct (beq_idP c z) as [Hxz | Hxz].
      * subst.
        assert (Htriv : z = z) by reflexivity. 
        apply IdLS.Props.IdSetProps.Dec.F.remove_1 
        with (s := mdlmems) in Htriv.
        apply Htriv in Hin. contradiction.
      * rewrite update_neq; try assumption. 
        rewrite update_neq in Hnone; try assumption.
        apply IdLS.Props.IdSetProps.Dec.F.remove_3 in Hin.
        specialize (HGamma z Hnone Hin). 
        assumption.
      * subst.
        rewrite <- IdLS.Props.IdSetProps.Dec.F.not_mem_iff in Hxmem.
        apply Hxmem in Hin. contradiction.
      * rewrite update_neq. rewrite update_neq in Hnone; try assumption.
        apply HGamma; try assumption. assumption.
    + (* appears_free *)
      intros z Hfree Hin.
      destruct (beq_idP c z) as [Hcz | Hcz].
      ** subst.
         repeat rewrite update_eq.
         reflexivity.
      ** repeat rewrite update_neq; try assumption.
         apply Hapfree.
         unfold appears_free_in in *.
         simpl.
         apply IdLS.Props.IdSetProps.Dec.F.remove_neq_iff;
           assumption.
         destruct (IdLS.IdSet.mem c mdlmems) eqn:Hxmem.
         { rewrite IdLS.Props.IdSetProps.Dec.F.remove_neq_iff in Hin;
             assumption. }
         { assumption. }
  - (* tcinvk, T_CInvk *)
    rename i into c. rename i0 into f.
    apply T_CInvk with C0; try assumption.
    rewrite <- H4. symmetry.
    apply Hapfree.
    unfold appears_free_in. simpl.
    apply IdLS.Props.IdSetProps.Dec.F.singleton_2. reflexivity.
    intros Hcontra.
    assert (Htriv : Gamma c <> None).
    { intros contra. rewrite H4 in contra. inversion contra. }
    specialize (HGamma c Htriv Hcontra).
    destruct HGamma as [GT [HGamma _]].
    rewrite HGamma in H4. inversion H4.
  - (* tcinvk, T_MInvk *)
    rename i into M'. rename i0 into f.
    unfold no_model_names_in_term in HtOk.
    assert (Hin : IdLPM.IdMap.In M' MTbl).
    { apply IdMapProps.F.in_find_iff.
      intros contra. rewrite H5 in contra. inversion contra. }
    specialize (HtOk M' Hin). simpl in HtOk.
    exfalso. apply HtOk. 
    apply IdLS.Props.IdSetProps.Dec.F.singleton_2. reflexivity.
  - (* tlet *)
    rename i into x.
    apply T_Let with T1; try assumption.
    apply IHt1 with Gamma; 
      (assumption || prove_appears_free_in_superterm ||
       prove_no_model_names_in_subterm).
    apply IHt2 with (update Gamma x (tmtype T1));
      try (assumption || prove_no_model_names_in_upd_Gamma || 
           prove_no_model_names_in_subterm).   
    + (* trans *)
      destruct (IdLS.IdSet.mem x mdlmems) eqn:Hxmem.
      * pose proof IdLS.Props.IdSetProps.Dec.F.Subset_trans as Htrans.
        unfold RelationClasses.Transitive in Htrans.
        apply Htrans with mdlmems.
        unfold IdLS.IdSet.Subset. 
        intros z Hinz.
        apply IdLS.Props.IdSetProps.Dec.F.remove_3 in Hinz. 
        assumption. assumption.
      * assumption.
    + intros z Hnone Hin.
      destruct (IdLS.IdSet.mem x mdlmems) eqn:Hxmem;
        destruct (beq_idP x z) as [Hxz | Hxz].
      * subst.
        assert (Htriv : z = z) by reflexivity. 
        apply IdLS.Props.IdSetProps.Dec.F.remove_1 
        with (s := mdlmems) in Htriv.
        apply Htriv in Hin. contradiction.
      * rewrite update_neq; try assumption. 
        rewrite update_neq in Hnone; try assumption.
        apply IdLS.Props.IdSetProps.Dec.F.remove_3 in Hin.
        specialize (HGamma z Hnone Hin). 
        assumption.
      * subst.
        rewrite <- IdLS.Props.IdSetProps.Dec.F.not_mem_iff in Hxmem.
        apply Hxmem in Hin. contradiction.
      * rewrite update_neq. rewrite update_neq in Hnone; try assumption.
        apply HGamma; try assumption. assumption.
    + (* appears_free *)
      intros z Hfree Hin.
      destruct (beq_idP x z) as [Hxz | Hxz].
      ** subst.
         repeat rewrite update_eq.
         reflexivity.
      ** repeat rewrite update_neq; try assumption.
         apply Hapfree.
         unfold appears_free_in in *.
         simpl.
         apply IdLS.Props.IdSetProps.Dec.F.union_3.
         apply IdLS.Props.IdSetProps.Dec.F.remove_neq_iff;
           assumption.
         destruct (IdLS.IdSet.mem x mdlmems) eqn:Hxmem.
         { rewrite IdLS.Props.IdSetProps.Dec.F.remove_neq_iff in Hin;
             assumption. }
         { assumption. }
Qed.


Lemma qualify_model_members_preserves_typing :
  forall (CTbl : cptcontext) (MTbl : mdlcontext) M
         C Mbody Gamma (t : tm) (T : ty),
    (* term [t] has type [T] under Gamma *)
    CTbl $ MTbl ; Gamma |- t \in T ->
    (* [M] is a valid model name *)
    IdLPM.IdMap.find M MTbl = Some (MTdef C Mbody) ->
    (* all variables in Gamma can be type-preservingly qualified with [M] *)
    (forall (x : id), 
        Gamma x <> None ->
        IdLS.IdSet.In x (set_of_keys Mbody)
        /\ (exists GT,
               Gamma x = Some (tmtype GT)
               /\ CTbl $ MTbl ; ctxempty |- tcinvk M x \in GT )) ->
    (* No bad names in term *)
    no_model_names_in_term CTbl MTbl t ->
    (* then the qualified term has type [T] under the empty context *)
    CTbl $ MTbl ; ctxempty |- (qualify_model_members M Mbody t) \in T.
Proof.
  intros CTbl MTbl M C Mbody Gamma t T.
  intros HT Hfind HGamma HtOk.
  unfold qualify_model_members.
  apply qualify_model_members_preserves_typing'
    with C Mbody Gamma; try assumption.
  - (* subset *)
    pose proof IdLS.Props.IdSetProps.Dec.F.Subset_refl as Hrefl.
    unfold RelationClasses.Reflexive in Hrefl.
    apply Hrefl.
  - (* typing *)
    intros x Hnone Hin.
    specialize (HGamma x Hnone). tauto.
  - (* appears_free_in *)
    intros x Hfree Hin.
    destruct (Gamma x) eqn:Heq.
    + assert (Htriv : Gamma x <> None).
      { intros contra. rewrite Heq in contra. inversion contra. }
      specialize (HGamma x Htriv).
      destruct HGamma as [Hin' [GT [Hcontra _]]].
      apply Hin in Hin'. contradiction.
    + reflexivity.
  - apply no_model_names_in_empty_context.
Qed.


Theorem mdlcontext_WD_minimal_Gamma_for_member :
  forall CTbl MTbl M C Mbody f tf,
    cptcontext_welldefined CTbl ->
    mdlcontext_welldefined CTbl MTbl ->
    IdLPM.IdMap.find M MTbl = Some (MTdef C Mbody) ->
    find_tm f Mbody = Some tf ->
    exists Cbody T Gamma,
      IdLPM.IdMap.find C CTbl = Some (CTdef Cbody)
      /\ find_ty f Cbody = Some T
      /\ no_model_names_in_term CTbl MTbl tf
      /\ (CTbl $ MTbl ; Gamma |- tf \in T)
      /\ (forall (x : id), 
             Gamma x <> None ->
             IdLS.IdSet.In x (set_of_keys Mbody)
             /\ (exists GT,
                    Gamma x = Some (tmtype GT)
                    /\ CTbl $ MTbl ; ctxempty |- tcinvk M x \in GT )).
Admitted.




(* ----------------------------------------------------------------- *)
(** **** Main Preservation Theorem *)
(* ----------------------------------------------------------------- *)

Ltac prove_preservation_with_IH :=
  match goal with
    [ Hbvars : no_model_names_in_term ?CTbl ?MTbl ?t ,
      HTs    : ?CTbl $ ?MTbl ; ctxempty |- ?s \in ?S ,
      IHHE   : no_model_names_in_term ?CTbl ?MTbl ?s ->
               forall T : ty, 
                 ?CTbl $ ?MTbl ; ctxempty ||- ?s \in T ->
                 ?CTbl $ ?MTbl; ctxempty ||- ?s' \in T
        |- ?CTbl $ ?MTbl; ctxempty |- ?s' \in ?S]
    => assert (Hmnames : no_model_names_in_term CTbl MTbl s)
         by prove_no_model_names_in_subterm ;
       assert (HTypeSub : CTbl $ MTbl; ctxempty ||- s \in S) 
         by (split; [ assumption | split; assumption ]) ;
       specialize (IHHE Hmnames S HTypeSub);
       inversion IHHE as [_ [_ HTypeSub']];
       assumption
  end.

Theorem preservation : forall CTbl MTbl t t' T,
    (* source term does not use model names as bound variables *)
    no_model_names_in_term CTbl MTbl t ->
    (* source term has a type *)
    CTbl $ MTbl ; ctxempty ||- t \in T ->
    (* term makes a step *)
    CTbl $ MTbl ; t #==> t' ->
    (* then a new term has the same type *)
    CTbl $ MTbl ; ctxempty ||- t' \in T.
Proof.
  remember ctxempty as Gamma.
  intros CTbl MTbl t t' T Hbvars HT HE. 
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
    apply no_model_names_in_empty_context.
    prove_no_model_names_in_subterm.
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
    apply no_model_names_in_empty_context.
    prove_no_model_names_in_subterm.
    inversion H7; subst. assumption.
(* ST_MApp *) 
  - apply T_MApp with C Mbody; try assumption.
    prove_preservation_with_IH.
(* tf (method invocation) for concept *)
  - unfold ctxempty in H6. rewrite apply_empty in H6.
    inversion H6.
(* M.f ==> tf for model *)
  - clear H3.
    pose proof (mdlcontext_WD_minimal_Gamma_for_member
                CTbl MTbl M C Mbody f tf 
                HCTOk HMTOk H H0) as HtfOk.
    destruct HtfOk as [Cbody [TF [Gamma [HfindC [ Hfindf 
                      [Hmnames [HTtf HGamma]]]]]]].
    apply qualify_model_members_preserves_typing
    with C Gamma; try assumption.
    (* need to unify all assumptions *)
    rewrite H in H7. inversion H7. subst. clear H7.
    unfold concept_fun_member in H9.
    destruct (IdLPM.IdMap.find C0 CTbl); try solve [inversion H9].
    destruct c as [fnmtys]. inversion HfindC. subst. clear HfindC.
    rewrite H9 in Hfindf. inversion Hfindf. subst.
    + (* typing *)
      assumption.
(* tlet *)
  - apply T_Let with T1.
    prove_preservation_with_IH.
    assumption.
(* tlet with substitution *)
  - apply substitution_preserves_typing with T1;
      try assumption.
    apply no_model_names_in_empty_context.
    prove_no_model_names_in_subterm.
Qed.


(* ================================================================= *)
(** *** Soundness *)
(* ================================================================= *)

(* ----------------------------------------------------------------- *)
(** **** Aux Props *)
(* ----------------------------------------------------------------- *)

(*
Lemma substitution_preserves_no_model_names_in_term :
  forall CTbl MTbl (x : id) (t v : tm),
    cptcontext_welldefined CTbl ->
    mdlcontext_welldefined CTbl MTbl ->
    no_model_names_in_term CTbl MTbl t ->
    no_model_names_in_term CTbl MTbl v ->
    no_model_names_in_term CTbl MTbl ([x:=v] t).
Proof.
  intros CTbl MTbl x t.
  induction t;
    intros v HCTOk HMTOk HtOk HvOk.
  - (* tvar *)
    rename i into y.
    simpl.
    destruct (beq_idP x y) as [Hxy | Hxy];
      assumption.
  - (* tapp *)
    simpl.
    assert (Ht1Ok : no_model_names_in_term CTbl MTbl t1).
    
    (*constructor.*)
      match goal with
    [ IHsubs : context [ no_model_names_in_term ?CTbl ?MTbl (subst _ _ ?s) ] ,
      HtOk   : context sC [ ?s ]
      |- no_model_names_in_term ?CTbl ?MTbl ?s ]
    => let Hnew := fresh "HtOk" in 
       assert (Hnew := HtOk);
       unfold no_model_names_in_term; idtac 1 ;
       idtac HtOk; (*let z := (context sC [0] ) in *) idtac 5
(*       unfold no_model_names_in_term in Hnew;
       intros mx HinM HinS; 
       specialize (Hnew mx HinM);
       apply Hnew; simpl;
       auto using IdLS.Props.IdSetProps.Dec.F.union_2,
                  IdLS.Props.IdSetProps.Dec.F.union_3,
                  IdLS.Props.IdSetProps.Dec.F.remove_2 *)
      end.

 prove_no_model_names_in_subterm.
      unfold no_model_names_in_term in HvOk.

    unfold no_model_names_in_term in HtOk.
    simpl in HtOk.

    { unfold no_model_names_in_term.
      intros z HinM Hin.
      apply HtOk with z; try assumption.
      

    prove_no_model_names_in_superterm.
    

Abort.
 
Ltac prove_no_model_names_in_subterm_precise :=
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

*)

(*
Lemma step_preserves_no_model_names_in_term :
  forall CTbl MTbl (t t' : tm),
    cptcontext_welldefined CTbl ->
    mdlcontext_welldefined CTbl MTbl ->
    no_model_names_in_term CTbl MTbl t ->
    CTbl $ MTbl ; t #==> t' ->
    no_model_names_in_term CTbl MTbl t'.
Proof.
  intros CTbl MTbl t.
  induction t;
    intros t' HCTOk HMTOk HtOk HE;
    inversion HE; subst; simpl.

  - (* ST_AppAbs *)
    unfold  simpl.


Abort.


no_model_names_in_term CTbl MTbl t1
  Hhas_type : CTbl $ MTbl; ctxempty ||- t1 \in T
  t2, t3 : tm
  H : CTbl $ MTbl; t1 #==> t2
*)

(* ----------------------------------------------------------------- *)
(** **** Main Soundness Theorem *)
(* ----------------------------------------------------------------- *)

Definition normal_form CTbl MTbl (t : tm) : Prop :=
  ~ (exists t', CTbl $ MTbl ; t #==> t').

Definition stuck CTbl MTbl (t : tm) : Prop :=
  (normal_form CTbl MTbl t) /\ ~ value t.


Corollary soundness : 
  forall CTbl MTbl t t' T,
    no_model_names_in_term CTbl MTbl t ->
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
    remember (preservation _ _ _ Hhas_type H) as Ht'. clear HeqHt'.
    apply IHHmulti in Ht'; auto.
Qed.
*)

