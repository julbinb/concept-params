(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(* Module with Certified Checking 
   of Single-Pass Module.
  
   Last Update: Wed, 24 May 2017
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
(** * Single-Pass Module *)

(** Single-Pass Module is well-defined if
    all names are different 
    and all members are well-defined with following elements
      refering to the previously defined ones via local context. *)
(* ***************************************************************** *)
(* ***************************************************************** *)

(* ################################################################# *)
(** ** Shared Parameters of all building blocks *)
(* ################################################################# *)

Module Type SinglePassModuleBase.
  Include ModuleBase.

  Declare Module MD : DataLC.
  Import MD.

  (** Initial local context *)
  Parameter ctxl_init : ctxloc.
  (** Update local context *)
  Parameter upd_ctxloc : ctxloc -> ctx -> id -> t -> ctxloc.
End SinglePassModuleBase.


(* ################################################################# *)
(** ** Propositional Part *)
(* ################################################################# *)

Module SinglePassModuleDefs (Import MMB : SinglePassModuleBase) 
       (Import TOkD : DataLCOkDef MMB.MD).

  Module HelperD.
    Export MD.
    Definition dt := t.

    (** We can use generic implementation of single-pass module
        checking from the SharedDataDefs.
        For this we need several aux functions. *)

    Definition update_prop (ok : Prop) (c : ctx) 
               (cl : ctxloc) (decl : id * dt) : Prop
      := (* check curr member in the local context *)
          TOkD.is_ok c cl (snd decl)  
          (* and preserve previous members' part *)
          /\ ok.

    Definition update_ctxloc (cl : ctxloc) (c : ctx) 
               (decl : id * dt) : ctxloc
      := match decl with (nm, d) => upd_ctxloc cl c nm d end.

    (** We can use generic implementation of module-welldefinedness *)
    Module MSP := SinglePassModule_ProcessMembers.
    Module MGM := GenericModule_ModuleOk MId.

    (** Aux function checking that all members are ok. *)
    Definition members_ok (c : ctx) (decls : list (id * dt)) : Prop :=
      MSP.members_ok ctx ctxloc (id * dt) 
                     update_prop update_ctxloc c ctxl_init decls.

  End HelperD.
  Import HelperD.

  (** Single-Pass Module given as the AST [decls]  
   ** is well-defined in the context [c]. *)
  Definition module_ok (c : ctx) (decls : list (id * dt)) : Prop :=
    MGM.module_ok dt ctx members_ok c decls.

  Ltac unfold_def G :=
    unfold module_ok, MGM.module_ok in G.

End SinglePassModuleDefs.

(* ################################################################# *)
(** ** Computable Part (static checker of the interpreter) *)
(* ################################################################# *)

Module SinglePassModuleInterp (Import MMB : SinglePassModuleBase) 
       (Import TOkI : DataLCOkInterp MMB.MD).

  Module HelperI.
    Export MD.
    Definition dt := t.

    Definition check_member  (c : ctx) (cl : ctxloc) (decl : id * dt) : bool
      := TOkI.is_ok_b c cl (snd decl).

    Definition update_ctxloc (cl : ctxloc) (c : ctx) 
               (decl : id * dt) : ctxloc
      := match decl with (nm, d) => upd_ctxloc cl c nm d end.

    Module MSP := SinglePassModule_ProcessMembers.
    Module MGM := GenericModule_ModuleOk MId.

    (** Aux function checking that all members are ok. *)
    Definition members_ok_b (c : ctx) (decls : list (id * dt)) : bool :=
      MSP.members_ok_b ctx ctxloc (id * dt)
                       check_member update_ctxloc c ctxl_init decls.

  End HelperI.
  Import HelperI.

  (** Checks that a module given as the AST [decls]  
   ** is well-defined in the context [c]. *)
  Definition module_ok_b (c : ctx) (decls : list (id * dt)) : bool :=
    MGM.module_ok_b dt ctx members_ok_b c decls.

End SinglePassModuleInterp.

(* ################################################################# *)
(** ** Proofs of Correctness *)
(* ################################################################# *)

Module SinglePassModuleProps 
       (Import MMB : SinglePassModuleBase)
       (Import TOkD : DataLCOkDef MMB.MD)
       (Import TOkI : DataLCOkInterp MMB.MD)
       (Import TOkP : DataLCOkProp MMB.MD TOkD TOkI)
.
  Module Import MMD := SinglePassModuleDefs   MMB TOkD.
  Module Import MMI := SinglePassModuleInterp MMB TOkI.
  Import MMD.HelperD. Import MMI.HelperI.

(* ----------------------------------------------------------------- *)
(** *** Helper Props  *)
(* ----------------------------------------------------------------- *)

  Module Helper.
    Import MMD.HelperD.

    Lemma check_member__sound : 
      forall (c : ctx) (cl : ctxloc) (decl : id * dt) (P : Prop),
        P -> 
        check_member c cl decl = true ->
        update_prop P c cl decl.
    Proof.
      intros c cl decl P HP H.
      unfold check_member in H. unfold update_prop.
      apply TOkP.is_ok_b__sound in H. tauto.
    Qed.

    Lemma check_member__complete : 
      forall (c : ctx) (cl : ctxloc) (decl : id * dt) (P : Prop),
        P -> 
        update_prop P c cl decl ->
        check_member c cl decl = true.
    Proof.
      intros c cl decl P HP H.
      unfold check_member. unfold update_prop in H.
      apply TOkP.is_ok_b__complete. tauto.
    Qed.

    Lemma update_prop__spec :
      forall (c : ctx) (cl : ctxloc) (decl : id * dt) (P : Prop),
        update_prop P c cl decl -> P.
    Proof.
      intros c cl decl P H.
      unfold update_prop in H. tauto.
    Qed.

(* ----------------------------------------------------------------- *)

    Module MSP := SinglePassModule_ProcessMembers.
    Module MGM := GenericModule_ModuleOk MId.

    Lemma members_ok_b__sound :
      forall (c : ctx) (decls : list (id * dt)),
      members_ok_b c decls = true ->
      members_ok c decls.
    Proof.
      intros c ds H.
      unfold members_ok_b in H.
      unfold members_ok.
      apply MSP.members_ok_b__sound with (update_prop := update_prop) in H.
      assumption. 
      exact check_member__sound.
    Qed.

    Lemma members_ok_b__complete :
      forall (c : ctx) (decls : list (id * dt)),
        members_ok c decls -> 
        members_ok_b c decls = true.
    Proof.
      intros c ds H.
      unfold members_ok in H.
      unfold members_ok_b.
      apply MSP.members_ok_b__complete with (check_member := check_member) in H.
      assumption. 
      exact check_member__complete.
      exact update_prop__spec.
    Qed.

  End Helper.

(* ================================================================= *)
(** *** Properties *)
(* ================================================================= *)

  Theorem module_ok_b__sound : forall (c : ctx) (decls : list (id * dt)),
      module_ok_b c decls = true ->
      module_ok c decls.
  Proof.
    apply Helper.MGM.module_ok_b__sound.
    apply Helper.members_ok_b__sound.
  Qed.

  Theorem module_ok_b__complete : forall (c : ctx) (decls : list (id * dt)),
      module_ok c decls ->
      module_ok_b c decls = true.
  Proof.
    apply Helper.MGM.module_ok_b__complete.
    apply Helper.members_ok_b__complete.
  Qed.

End SinglePassModuleProps.



