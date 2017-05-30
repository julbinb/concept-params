(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(* Module with Certified Checking 
   of Single-Pass Implementation Module.
  
   Last Update: Fri, 26 May 2017
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

Require Import Coq.omega.Omega.

(* ***************************************************************** *)
(** * Single-Pass Implementation Module *)

(** Single-Pass Module is well-defined if
    all names are different 
    and all members are well-defined with respect to some interface
      with following elements
      refering to the previously defined ones via local context. *)
(* ***************************************************************** *)
(* ***************************************************************** *)

(* ################################################################# *)
(** ** Shared Parameters of all building blocks *)
(* ################################################################# *)

Module Type SinglePassImplModuleBase.
  Include ModuleBase.

  Declare Module MD : DataLCI.
  Import MD.

  (** Initial local context *)
  Parameter ctxl_init : ctxloc.
  (** Update local context *)
  Parameter upd_ctxloc : ctxloc -> ctx -> intrfs -> id -> t -> ctxloc.

  (** Members which have to be defined by an interface *)
  Parameter members_to_define : intrfs -> list id.
End SinglePassImplModuleBase.

(* ----------------------------------------------------------------- *)
(** *** Aux Definitions (for implementation purposes only) *)
(* ----------------------------------------------------------------- *)

Module SinglePassImplModule_Data (Import MMB : SinglePassImplModuleBase) 
<: GenericModule_Data. 

  Definition dt := MD.t.
  Definition ctx := (MD.ctx * MD.intrfs)%type.
End SinglePassImplModule_Data.

(* ################################################################# *)
(** ** Propositional Part *)
(* ################################################################# *)

Module SinglePassImplModuleDefs (Import MMB : SinglePassImplModuleBase) 
       (Import TOkD : DataLCIOkDef MMB.MId MMB.MD).

  Module HelperD.
    Export MMB.MD.
    Definition dt := t.

    (** We can use generic implementation of single-pass module
        checking from the SharedDataDefs.
        For this we need several aux functions. *)

    Definition update_prop (ok : Prop) (ci : ctx * intrfs) 
               (cl : ctxloc) (decl : id * dt) : Prop
      := let (c, i) := ci in
         let (nm, d) := decl in 
         (* check curr member in the local context *)
         TOkD.is_ok c i cl nm d  
         (* and preserve previous members' part *)
         /\ ok.

    Definition update_ctxloc (cl : ctxloc) (ci : ctx * intrfs) 
               (decl : id * dt) : ctxloc
      := let (c, i) := ci in 
         let (nm, d) := decl in 
         upd_ctxloc cl c i nm d.

    (** We can use generic implementation of module-welldefinedness *)
    Module MData := SinglePassImplModule_Data MMB.
    Module MSP := SinglePassModule_ProcessMembers.
    Module MGM := GenericModule_ModuleOk MId.

    (** Aux function checking that all members are ok. *)
    Definition members_ok (ci : ctx * intrfs) 
               (decls : list (id * dt)) : Prop 
      := MSP.members_ok (ctx * intrfs) ctxloc (id * dt) 
                        update_prop update_ctxloc ci ctxl_init decls.

    Definition req_members_defined (i : intrfs) (decls : list (id * dt)) : Prop
      := List.Forall 
           (fun nm => List.In nm (map fst decls)) 
           (members_to_define i).
 
  End HelperD.
  Import HelperD.

  (** Single-Pass Module given as the AST [decls]  
   ** is well-defined in the context [c]. *)
  Definition module_ok (c : ctx) (i : intrfs) (decls : list (id * dt)) : Prop :=
    MGM.module_ok MData.dt MData.ctx members_ok (c, i) decls
    /\ (HelperD.req_members_defined i decls).

  Ltac unfold_def :=
    unfold module_ok, MGM.module_ok.

End SinglePassImplModuleDefs.

(* ################################################################# *)
(** ** Computable Part (static checker of the interpreter) *)
(* ################################################################# *)

Module SinglePassImplModuleInterp (Import MMB : SinglePassImplModuleBase) 
       (Import TOkI : DataLCIOkInterp MMB.MId MMB.MD).

  Module HelperI.
    Export MMB.MD.
    Definition dt := t.

    Definition check_member (ci : ctx * intrfs) 
               (cl : ctxloc) (decl : id * dt) : bool
      := let (c, i) := ci in 
         let (nm, d) := decl in 
         TOkI.is_ok_b c i cl nm d.

    Definition update_ctxloc (cl : ctxloc) (ci : ctx * intrfs) 
               (decl : id * dt) : ctxloc
      := let (c, i) := ci in 
         let (nm, d) := decl in 
         upd_ctxloc cl c i nm d.

    (** We can use generic implementation of module-welldefinedness *)
    Module MData := SinglePassImplModule_Data MMB.
    Module MSP := SinglePassModule_ProcessMembers.
    Module MGM := GenericModule_ModuleOk MId.

    (** Aux function checking that all members are ok. *)
    Definition members_ok_b (ci : ctx * intrfs) 
               (decls : list (id * dt)) : bool 
      := MSP.members_ok_b (ctx * intrfs) ctxloc (id * dt)
                          check_member update_ctxloc ci ctxl_init decls.

    Definition req_members_defined_b (i : intrfs) (decls : list (id * dt)) : bool
      := List.forallb 
           (fun nm => Nat.leb 1 (List.count_occ MId.IdDT.eq_dec (map fst decls) nm)) 
           (members_to_define i).

  End HelperI.
  Import HelperI.

  (** Checks that a module given as the AST [decls]  
   ** is well-defined in the context [c]. *)
  Definition module_ok_b (c : ctx) (i : intrfs) 
             (decls : list (id * dt)) : bool :=
    andb 
      (MGM.module_ok_b MData.dt MData.ctx members_ok_b (c, i) decls)
      (req_members_defined_b i decls).

End SinglePassImplModuleInterp.

(* ################################################################# *)
(** ** Proofs of Correctness *)
(* ################################################################# *)

Module SinglePassImplModuleProps 
       (Import MMB : SinglePassImplModuleBase)
       (Import TOkD : DataLCIOkDef MMB.MId MMB.MD)
       (Import TOkI : DataLCIOkInterp MMB.MId MMB.MD)
       (Import TOkP : DataLCIOkProp MMB.MId MMB.MD TOkD TOkI)
.
  Module Import MMD := SinglePassImplModuleDefs   MMB TOkD.
  Module Import MMI := SinglePassImplModuleInterp MMB TOkI.
  Import MMD.HelperD. Import MMI.HelperI.

(* ----------------------------------------------------------------- *)
(** *** Helper Props  *)
(* ----------------------------------------------------------------- *)

  Module Helper.
    Import MMD.HelperD.
 
    Lemma check_member__sound : 
      forall (ci : ctx * intrfs) (cl : ctxloc) (decl : id * dt) (P : Prop),
        P -> 
        check_member ci cl decl = true ->
        update_prop P ci cl decl.
    Proof.
      intros [c i] cl [nm d] P HP H.
      unfold check_member in H. unfold update_prop.
      apply TOkP.is_ok_b__sound in H. tauto.
    Qed.

    Lemma check_member__complete : 
      forall (ci : ctx * intrfs) (cl : ctxloc) (decl : id * dt) (P : Prop),
        P -> 
        update_prop P ci cl decl ->
        check_member ci cl decl = true.
    Proof.
      intros [c i] cl [nm d] P HP H.
      unfold check_member. unfold update_prop in H.
      apply TOkP.is_ok_b__complete. tauto.
    Qed.

    Lemma update_prop__spec :
      forall (ci : ctx * intrfs) (cl : ctxloc) (decl : id * dt) (P : Prop),
        update_prop P ci cl decl -> P.
    Proof.
      intros [c i] cl [nm d] P H.
      unfold update_prop in H. tauto.
    Qed.

(* ----------------------------------------------------------------- *)
    
    (** We can use generic implementation of module-welldefinedness *)
    Module MData := SinglePassImplModule_Data MMB.
    Module MSP := SinglePassModule_ProcessMembers.
    Module MGM := GenericModule_ModuleOk MId.

    Lemma members_ok_b__sound :
      forall (ci : ctx * intrfs) (decls : list (id * dt)),
      members_ok_b ci decls = true ->
      members_ok ci decls.
    Proof.
      intros ci ds H.
      unfold members_ok_b in H.
      unfold members_ok.
      apply MSP.members_ok_b__sound with (update_prop := update_prop) in H.
      assumption. 
      exact check_member__sound.
    Qed.

    Lemma members_ok_b__complete :
      forall (ci : ctx * intrfs) (decls : list (id * dt)),
        members_ok ci decls -> 
        members_ok_b ci decls = true.
    Proof.
      intros ci ds H.
      unfold members_ok in H.
      unfold members_ok_b.
      apply MSP.members_ok_b__complete with (check_member := check_member) in H.
      assumption. 
      exact check_member__complete.
      exact update_prop__spec.
    Qed.

(* ----------------------------------------------------------------- *) 

    Lemma req_members_defined_b__sound :
      forall (i : intrfs) (decls : list (id * dt)),
        req_members_defined_b i decls = true ->
        req_members_defined i decls.
    Proof.
      intros i.
      unfold req_members_defined_b, req_members_defined.
      induction (members_to_define i) as [| m ms IHms].
      - (* no members to define *)
        intros ds H. constructor.
      - (* members_to_define = m :: ms *)
        intros ds H.
        simpl in *.
        rewrite andb_true_iff in H. destruct H as [Hm Hms].
        destruct (count_occ MId.IdDT.eq_dec (map fst ds) m) eqn:Heq.
        rewrite Heq in Hm at 1.
        inversion Hm. clear Hm.
        constructor.
        rewrite -> (count_occ_In MId.IdDT.eq_dec). omega.
        apply IHms. assumption.
    Qed.

    Lemma req_members_defined_b__complete :
      forall (i : intrfs) (decls : list (id * dt)),
        req_members_defined i decls ->
        req_members_defined_b i decls = true.
    Proof.
      intros i.
      unfold req_members_defined_b, req_members_defined.
      induction (members_to_define i) as [| m ms IHms].
      - (* no members to define *)
        intros ds H. simpl. reflexivity.
      - (* members_to_define = m :: ms *)
        intros ds H.
        simpl in *.
        rewrite andb_true_iff. 
        inversion H as [Hm | Hms]; subst.
        split.
        + rewrite -> (count_occ_In MId.IdDT.eq_dec) in H0.
          inversion H0. rewrite <- H3 at 1. reflexivity.
          rewrite <- H2 at 1. reflexivity.
        + specialize (IHms ds H1). assumption.
    Qed.

  End Helper.

(* ================================================================= *)
(** *** Properties *)
(* ================================================================= *)

  Theorem module_ok_b__sound : 
    forall (c : ctx) (i : intrfs) (decls : list (id * dt)),
      module_ok_b c i decls = true ->
      module_ok c i decls.
  Proof.
    intros c i decls H.
    unfold module_ok_b in H. unfold module_ok.
    rewrite andb_true_iff in H. inversion H as [Hm Hids].
    split.
    - apply MGM.module_ok_b__sound 
      with (members_ok := HelperD.members_ok) in Hm. assumption.
      apply Helper.members_ok_b__sound.
    - clear Hm.
      apply Helper.req_members_defined_b__sound. assumption.
  Qed.

  Theorem module_ok_b__complete : 
    forall (c : ctx) (i : intrfs) (decls : list (id * dt)),
      module_ok c i decls ->
      module_ok_b c i decls = true.
  Proof.
    intros c i decls H.
    unfold module_ok in H. unfold module_ok_b.
    rewrite andb_true_iff. inversion H as [Hm Hids].
    split.
    - apply MGM.module_ok_b__complete
      with (members_ok := HelperD.members_ok); try assumption.
      apply Helper.members_ok_b__complete.
    - apply Helper.req_members_defined_b__complete; assumption.
  Qed.

End SinglePassImplModuleProps.



