(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(* Simply Typed Lambda Calculus with simple Concept Parameters
   :: version a
   Properties

   Properties of STLC are based on
   Sofware Foundations, v.4 
  
   Last Update: Mon, 29 May 2017
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


Axiom mdlcontext_WD__name_definition_exists :
  forall CTbl MTbl,
    cptcontext_welldefined CTbl ->
    mdlcontext_welldefined CTbl MTbl ->
    forall M C nmtms nmtys nm T,
      IdLPM.IdMap.find M MTbl = Some (MTdef C nmtms) ->
      IdLPM.IdMap.find C CTbl = Some (CTdef nmtys) ->
      find_ty nm nmtys = Some T ->
      exists t,
        find_tm nm nmtms = Some t.

(*Close Scope stlca_scope.*)

(*
Definition test CTbl MTbl t T :=
  CTbl $ MTbl ; ctxempty |- t \in T.
*)

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
      exists t'.
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

(*
(* CInvk *)

    unfold mdlcontext_welldefined in HMTOk.
    destruct HMTOk as [mdls [HmdlsOk HmdlsMty]].
    unfold modelsec_welldefined in HmdlsOk.
    
(*    MMdlDef_SinglePassMDefs.unfold_def HmdlsOk. *)

    unfold MMdlDef_SinglePassMDefs.module_ok in HmdlsOk.
    unfold MMdlDef_SinglePassMDefs.HelperD.MGM.module_ok in HmdlsOk.
    destruct HmdlsOk as [Hdup Hmems].
    unfold MMdlDef_SinglePassMDefs.HelperD.members_ok in Hmems.
    unfold MMdlDef_SinglePassMDefs.HelperD.MSP.members_ok in Hmems.
    unfold MMdlDef_SinglePassMDefs.HelperD.MSP.members_ok' in Hmems.
    remember (IdLPM.IdMap.find f Mbody) as ftm'.
    unfold MMdlDef_SinglePassMDefs.HelperD.MSP.process_dep_member in Hmems.
    unfold MMdlDef_SinglePassMDefs.HelperD.update_prop in Hmems.
    unfold MMdlDef_DataLCOkDef.is_ok in Hmems.
    unfold model_welldefined in Hmems.
    unfold MMdlMem_SinglePassImplMDefs.module_ok in Hmems.
    unfold MMdlMem_SinglePassImplMDefs.module_ok in Hmems.
    unfold MMdlMem_SinglePassImplMDefs.HelperD.MGM.module_ok in Hmems.
    unfold MMdlMem_SinglePassImplMDefs.HelperD.members_ok in Hmems.
    unfold MMdlMem_SinglePassImplMDefs.HelperD.MSP.members_ok in Hmems.
    unfold MMdlMem_SinglePassImplMDefs.HelperD.MSP.members_ok' in Hmems.
    unfold MMdlMem_SinglePassImplMDefs.HelperD.MSP.process_dep_member in Hmems.
    unfold MMdlMem_SinglePassImplMDefs.HelperD.update_prop in Hmems.
    unfold MMdlMem_DataLCIOkDef.is_ok in Hmems.
    unfold model_member_valid in Hmems.
*)

Definition appears_free_in (CTbl : cptcontext) (MTbl : mdlcontext)
           (x : id) (t : tm) : Prop :=
  IdLS.IdSet.In x (free_vars CTbl MTbl t).

Hint Unfold appears_free_in.

Lemma free_in_context : forall CTbl MTbl x t T Gamma,
   appears_free_in CTbl MTbl x t ->
   CTbl $ MTbl ; Gamma |- t \in T ->
   (exists T', Gamma x = Some (tmtype T'))
   \/ (exists C, Gamma x = Some (cpttype C)).
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
      destruct IHt as [V HV]; 
      [ left | right ]; exists V;
      pose proof (update_neq _ (tmtype T11) x y Gamma Heqxy) as HG;
      rewrite <- HG; assumption.
  - (* tcabs *)
    rename i into c. rename i0 into C.
    rewrite IdLS.Props.IdSetProps.Dec.F.remove_iff in Hfree.
    destruct Hfree as [Hfree Heqxy]. unfold IdUOT.eq in *.
    specialize (IHt _ _ Hfree H7).
    destruct IHt as [IHt | IHt];
      destruct IHt as [V HV];
      [ left | right ]; exists V;
      pose proof (update_neq _ (cpttype C) x c Gamma Heqxy) as HG;
      rewrite <- HG; assumption.
  - (* tcinvk *)
    rename i into c. rename i0 into f.
    destruct (IdLPM.IdMap.find c MTbl).
    + rewrite IdLS.Props.IdSetProps.Dec.F.empty_iff in Hfree.
      contradiction.
    + apply IdLS.Props.IdSetProps.FM.singleton_1 in Hfree.
      unfold IdUOT.eq in Hfree. subst.
      right. exists C. assumption.
  - (* tcinvk *)
    rename i into M. rename i0 into f.
    destruct (IdLPM.IdMap.find M MTbl).
    + rewrite IdLS.Props.IdSetProps.Dec.F.empty_iff in Hfree.
      contradiction.
    + apply IdLS.Props.IdSetProps.FM.singleton_1 in Hfree.
      unfold IdUOT.eq in Hfree. subst.
      inversion H5.
  - (* tlet *)
    rename i into y.
    apply IdLS.Props.IdSetProps.FM.union_1 in Hfree.
    destruct Hfree as [Hfree | Hfree].
    + specialize (IHt1 _ Gamma Hfree H6); assumption.
    + rewrite IdLS.Props.IdSetProps.Dec.F.remove_iff in Hfree.
      destruct Hfree as [Hfree Heqxy]. unfold IdUOT.eq in *.
      specialize (IHt2 _ _ Hfree H7). 
      destruct IHt2 as [IHt2 | IHt2];
      destruct IHt2 as [V HV];
      [ left | right ]; exists V;
      pose proof (update_neq _ (tmtype T1) x y Gamma Heqxy) as HG;
      rewrite <- HG; assumption.
Qed.

Lemma context_invariance : forall CTbl MTbl Gamma Gamma' t T,
    cptcontext_welldefined CTbl ->
    mdlcontext_welldefined CTbl MTbl ->
    CTbl $ MTbl ; Gamma |- t \in T  ->
    (forall x, appears_free_in CTbl MTbl x t -> Gamma x = Gamma' x) ->
    CTbl $ MTbl ; Gamma' |- t \in T.
Proof.
  intros CTbl MTbl Gamma Gamma' t T HCTOk HMTOk HT.
  generalize dependent Gamma'.
  induction HT; intros Gamma' Hfree; 
    unfold appears_free_in in *; simpl; auto;
    repeat match goal with
             [HCTOk : cptcontext_welldefined ?CTable ,
              HMTOk : mdlcontext_welldefined ?CTable ?MTable ,      
              IHHT : cptcontext_welldefined ?CTable ->
              mdlcontext_welldefined ?CTable ?MTable ->
              forall Gamma' : id -> option ctxvarty, _ |- _ ]
             => specialize (IHHT HCTOk HMTOk)
    end;
    simpl in *.
(*    unfold free_vars in Hfree; simpl in Hfree. *)
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
    


Abort.


Lemma substitution_preserves_typing : 
  forall CTbl MTbl Gamma x S t v T,
    cptcontext_welldefined CTbl ->
    mdlcontext_welldefined CTbl MTbl ->
    CTbl $ MTbl ; (update Gamma x (tmtype S)) |- t \in T ->
    CTbl $ MTbl ; ctxempty |- v \in S -> 
    CTbl $ MTbl ; Gamma |- [x:=v] t \in T.
Proof.
  intros CTbl MTbl Gamma x S t v T HCTOk HMTOk.
  intros Ht Hv.
  generalize dependent T. generalize dependent Gamma.
  induction t;
    intros Gamma T Ht;
    inversion Ht; subst; simpl. 
(* tvar *)
  - rename i into y. destruct (beq_idP x y). 
    + subst. 
      rewrite update_eq in H3. inversion H3. subst. clear H3.
      
      
    
  

Abort.



Theorem preservation : forall CTbl MTbl t t' T,
    (* source term has a type *)
    CTbl $ MTbl ; ctxempty ||- t \in T ->
    (* term makes a step *)
    CTbl $ MTbl ; t #==> t' ->
    (* then a new term has the same type *)
    CTbl $ MTbl ; ctxempty ||- t' \in T.
Proof.
  remember ctxempty as Gamma.
  intros CTbl MTbl t t' T HT. generalize dependent t'.
  destruct HT as [HCTOk [HMTOk HT]].
  induction HT;
    intros t' HE; subst Gamma;
    try solve [inversion HE; subst; auto];
  repeat match goal with
  |[ HCTOk : cptcontext_welldefined ?CTbl ,
     HMTOk : mdlcontext_welldefined ?CTbl ?MTbl,
     H : ctxempty = ctxempty ->
         cptcontext_welldefined ?CTbl ->
         mdlcontext_welldefined ?CTbl ?MTbl -> _
     |- _ ] 
    => assert (Htriv : ctxempty = ctxempty) by reflexivity; 
         specialize (H Htriv HCTOk HMTOk); clear Htriv
  end.
(* tapp t1 t2 *)
  - inversion HE; subst.
    inversion HT1; subst.
     
Abort.
     