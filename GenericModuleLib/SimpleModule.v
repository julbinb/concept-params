(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(* Module with Certified Checking 
   of Simple Module.
  
   Last Update: Tue, 23 May 2017
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 

Add LoadPath "../..".

Require Import ConceptParams.AuxTactics.LibTactics.
Require Import ConceptParams.AuxTactics.BasicTactics.

Require Import ConceptParams.SetMapLib.List2Set.
Require Import ConceptParams.SetMapLib.ListPair2FMap.

Require Import ConceptParams.GenericModuleLib.SharedDataDefs.

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Bool.Bool.

Require Import Coq.Structures.Orders.
Require Import Coq.Structures.Equalities.

(* ***************************************************************** *)
(** * Simple Module *)

(** Simple Module is well-defined if
    all names are different 
    and all members are well-defined (independtly of each other). *)
(* ***************************************************************** *)
(* ***************************************************************** *)

(* ################################################################# *)
(** ** Shared Parameters of all building blocks *)
(* ################################################################# *)

Module Type SimpleModuleBase.
  Include ModuleBase.

  Declare Module MD : DataC.
  Definition dt := MD.t.
  Definition ctx := MD.ctx.
End SimpleModuleBase.

Module SimpleModule_Data (MMB : SimpleModuleBase) 
<: GenericModule_Data. 

  Definition dt := MMB.dt.
  Definition ctx := MMB.ctx.
End SimpleModule_Data.

(* ################################################################# *)
(** ** Propositional Part *)
(* ################################################################# *)

Module SimpleModuleDefs (Import MMB : SimpleModuleBase) 
       (Import TOkD : DataCOkDef MMB.MD).

  Module HelperD.
    (** Aux definition "all members in a list are ok" *)
    Definition members_ok (c : ctx) (dts : list dt) : Prop :=
      List.Forall (fun elem => is_ok c elem) dts.

    Module MData := SimpleModule_Data MMB.
    Module MDataM <: GenericModule_DataDefs MId MData. 
      Definition members_ok (c : ctx) (decls : list (id * dt)) :=
        members_ok c (map snd decls).
    End MDataM.
    Module M := GenericModule_Defs MId MData MDataM.

  End HelperD.

  (** Simple Module given as the AST [ds]  
   ** is well-defined in the context [c] *)
  Definition module_ok (c : ctx) (decls : list (id * dt)) : Prop :=
    HelperD.M.module_ok c decls.
  (*  let (nms, dts) := split decls in
    (** all names are distinct *)
    List.NoDup nms
    (** and all types are valid *)
    /\ HelperD.members_ok c dts. *)

(*
  (** The finite map [imap] corresponds to the given well-defined
   ** AST [iast] of an interface *)
  Definition intrfs_ast_has_eq_map (c : ctx) 
             (iast : intrfs_ast) (imap : intrfs_map) : Prop :=
    (* interface is well-defined *)
    intrfs_ok c iast
    (* map is equal to ast *)
    /\ IdLPM.eq_list_map iast imap.
*)
End SimpleModuleDefs.

(* ################################################################# *)
(** ** Computable Part (static checker of the interpreter) *)
(* ################################################################# *)

Module SimpleModuleInterp (Import MMB : SimpleModuleBase) 
       (Import TOkI : DataCOkInterp MMB.MD).

  Module HelperI.
    Definition members_ok_b (c : ctx) (dts : list dt) : bool :=
      List.forallb (fun elem => is_ok_b c elem) dts.

    Module MData := SimpleModule_Data MMB.
    Module MDataM <: GenericModule_DataInterp MId MData. 
      Definition members_ok_b (c : ctx) (decls : list (id * dt)) := 
        members_ok_b c (map snd decls).
    End MDataM.
    Module M := GenericModule_Interp MId MData MDataM.
  End HelperI.

  (** Checks that an interface given as an AST [ds]  
   ** is well-defined in the context [c] *)
  Definition module_ok_b (c : ctx) (decls : list (id * dt)) : bool :=
    HelperI.M.module_ok_b c decls.
  (* let (nms, dts) := split decls in
    andb
      (** all names are distinct *)
      (MId.IdLS.ids_are_unique nms)
      (** and all types are valid *)
      (HelperI.members_ok_b c dts). *)

(*
  (** If an interface with the AST [iast] is well-defined,  
   ** converts it to the equal finite map *)
  Definition intrfs_ast_to_eq_map (c : ctx) 
             (iast : intrfs_ast) : option intrfs_map :=
    (* if interface is well-defined *)
    if intrfs_ok_b c iast then
      (* generate map from ast *)
      Some (IdLPM.map_from_list iast)
    else None.
*) 
End SimpleModuleInterp.

(* ################################################################# *)
(** ** Proofs of Correctness *)
(* ################################################################# *)

Module SimpleModuleProps 
       (Import MMB : SimpleModuleBase)
       (Import TOkD : DataCOkDef MMB.MD)
       (Import TOkI : DataCOkInterp MMB.MD)
       (Import TOkP : DataCOkProp MMB.MD TOkD TOkI)
.
  Module Import MMD := SimpleModuleDefs   MMB TOkD.
  Module Import MMI := SimpleModuleInterp MMB TOkI.
  Import MMD.HelperD. Import MMI.HelperI.

  Module Helper.

    Lemma members_ok_b__sound : forall (c : ctx) (dts : list dt),
      members_ok_b c dts = true ->
      members_ok c dts.
    Proof.
      intros c dts. unfold members_ok_b.
      induction dts as [| tp dts'];
        intros H.
      - (* ts = nil *)
        apply Forall_nil.
      - (* ts = tp :: ts' *)
        simpl in H. rewrite -> andb_true_iff in H.
        inversion H as [Htp Hdts']; clear H.
        apply IHdts' in Hdts'. 
        apply TOkP.is_ok_b__sound in Htp.
        apply Forall_cons; auto.
    Qed.

    Lemma members_ok_b__complete : forall (c : ctx) (ts : list dt),
        members_ok c ts ->
        members_ok_b c ts = true.
    Proof.
      intros c ts. unfold members_ok_b.
      induction ts as [| tp ts' IHts'];
        intros H.
      - (* ts = nil *)
        reflexivity.
      - (* ts = tp :: ts' *)
        inversion H; subst.
        simpl. rewrite -> andb_true_iff. split.
        + apply TOkP.is_ok_b__complete. assumption.
        + apply IHts'. assumption.
    Qed.

(* ----------------------------------------------------------------- *) 

    Module MData := MMD.HelperD.MData.
    Module MDataM <: GenericModule_DataProps 
                       MId MData MMD.HelperD.MDataM MMI.HelperI.MDataM.
      Theorem members_ok_b__sound : 
        forall (c : ctx) (decls : list (id * dt)),
          MMI.HelperI.MDataM.members_ok_b c decls = true -> 
          MMD.HelperD.MDataM.members_ok c decls.
      Proof.
        intros c decls H.
        unfold MDataM.members_ok_b in H.
        unfold MDataM.members_ok.
        apply members_ok_b__sound. assumption.
      Qed.

      Theorem members_ok_b__complete : 
        forall (c : ctx) (decls : list (id * dt)),
          MMD.HelperD.MDataM.members_ok c decls ->
          MMI.HelperI.MDataM.members_ok_b c decls = true.
      Proof.
        intros c decls H.
        unfold MDataM.members_ok_b. 
        unfold MDataM.members_ok in H.
        apply members_ok_b__complete. assumption.
      Qed.
    End MDataM.
    Module M := GenericModule_Props 
                  MId MMD.HelperD.MData
                  MMD.HelperD.MDataM MMI.HelperI.MDataM
                  MDataM.

  End Helper.

  Theorem module_ok_b__sound : forall (c : ctx) (decls : list (id * dt)),
      module_ok_b c decls = true ->
      module_ok c decls.
  Proof.
    apply Helper.M.module_ok_b__sound. 
(*    intros c ds. intros H.
    unfold module_ok_b in H. 
    unfold module_ok.
    destruct (split ds).
    rewrite -> andb_true_iff in H. inversion H as [Hid Helem].
    apply MId.IdLS.Props.ids_are_unique__sound in Hid.
    apply members_ok_b__sound in Helem.
    split; tauto. *)
  Qed.

  Theorem module_ok_b__complete : forall (c : ctx) (decls : list (id * dt)),
      module_ok c decls ->
      module_ok_b c decls = true.
  Proof.
    apply Helper.M.module_ok_b__complete.
(*    intros c ds. intros H.
    unfold module_ok_b.
    unfold module_ok in H.
    destruct (split ds).
    inversion H as [Hdup Hmems].
    rewrite -> andb_true_iff. split.
    apply MId.IdLS.Props.ids_are_unique__complete in Hdup. assumption.
    apply members_ok_b__complete. assumption. *)
  Qed.

(*
  Theorem module_ok__cons : forall (c : ctx) (ds : list (id * ty))
                                   (nm : id) (tp : ty),
      intrfs_ok c ((nm, tp) :: ds) ->
      intrfs_ok c ds.
  Proof.
    intros c ds nm tp H.
    unfold intrfs_ok in *. simpl in *.
    destruct (split ds) as [nms tps] eqn:Heq.
    propositional.
    inversion H0. assumption.
    inversion H1. assumption.
  Qed.

  Theorem intrfs_ok_b__cons : forall (c : ctx) (ds : list (id * ty))
                                   (nm : id) (tp : ty),
      intrfs_ok_b c ((nm, tp) :: ds) = true ->
      intrfs_ok_b c ds = true.
  Proof.
    intros c ds nm tp H.
    unfold intrfs_ok_b in *. simpl in *.
    destruct (split ds) as [nms tps] eqn:Heq.
    apply andb_true_iff. apply andb_true_iff in H.
    propositional.
    apply IdLS.Props.ids_are_unique__cons with (x := nm); assumption.
    apply types_ok_b__complete.
    apply types_ok_b__sound in H1. inversion H1. assumption.
  Qed.
*)

(*
(* ----------------------------------------------------------------- *)
(** *** Helper Props  *)
(* ----------------------------------------------------------------- *)

  Module Helper.

    Lemma intrfs_ast_has_eq_map__iso :
      forall (c : ctx) (Iast : intrfs_ast) (Imap1 Imap2 : intrfs_map),
        intrfs_ast_has_eq_map c Iast Imap1 ->
        intrfs_ast_has_eq_map c Iast Imap2 ->
        IdLPM.IdMap.Equal Imap1 Imap2.
    Proof.
      intros c Iast Imap1 Imap2.
      unfold intrfs_ast_has_eq_map.
      intros [Hok Heq1] [Hok2 Heq2]. clear Hok2.
      apply IdLPM.Props.eq_list_map__same_list__eq_maps with (ps := Iast);
        assumption.
    Qed.

  End Helper.

  Theorem eq__split_fst__map_fst : 
    forall {A B : Type} (l : list (prod A B)) (xs : list A) (ys : list B),
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

  Theorem intrfs_ast_to_eq_map__sound :
    forall (c : ctx) (iast : intrfs_ast) (imap : intrfs_map),  
    intrfs_ast_to_eq_map c iast = Some imap ->
    intrfs_ast_has_eq_map c iast imap.
  Proof.
    intros c ast mp H.
    unfold intrfs_ast_to_eq_map, intrfs_ast_has_eq_map in *.
    destruct (intrfs_ok_b c ast) eqn:Hok;
    [ apply intrfs_ok_b__sound in Hok | idtac ];
    split ; try inversion H.
    - assumption.
    - inversion H. subst. 
      apply IdLPM.Props.eq_list_map_from_list. 
      unfold intrfs_ok in *.
      destruct (split ast) as [nms tps] eqn:Heq; subst.
      inversion Hok as [Hdup Htypes].
      apply eq__split_fst__map_fst in Heq. subst.
      assumption.
  Qed.

  Theorem intrfs_ast_to_eq_map__complete :
    forall (c : ctx) (iast : intrfs_ast) (imap imap' : intrfs_map),  
      intrfs_ast_has_eq_map c iast imap ->
      intrfs_ast_to_eq_map c iast = Some imap' ->
      IdLPM.IdMap.Equal imap imap'.
  Proof.
    intros c ast mp mp' Htype Hcheck.
    apply intrfs_ast_to_eq_map__sound in Hcheck.
    apply Helper.intrfs_ast_has_eq_map__iso with (c := c) (Iast := ast); 
      assumption.
  Qed.
*)
End SimpleModuleProps.



