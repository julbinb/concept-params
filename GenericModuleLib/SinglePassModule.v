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
  Definition dt := MD.t.
  Definition ctx := MD.ctx.
  Definition ctxloc := MD.ctxloc.

  (** Initial local context *)
  Parameter ctxl_init : ctxloc.
  (** Update local context *)
  Parameter upd_ctxloc : ctxloc -> ctx -> id -> dt -> ctxloc.
End SinglePassModuleBase.

Module SinglePassModule_Data (MMB : SinglePassModuleBase) 
<: GenericModule_Data. 

  Definition dt := MMB.dt.
  Definition ctx := MMB.ctx.
End SinglePassModule_Data.

(* ################################################################# *)
(** ** Propositional Part *)
(* ################################################################# *)

Module SinglePassModuleDefs (Import MMB : SinglePassModuleBase) 
       (Import TOkD : DataLCOkDef MMB.MD).

  Module HelperD.

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

    (** Aux function checking that all members are ok. *)
    Definition members_ok (c : ctx) (decls : list (id * dt)) : Prop :=
      members_ok ctx ctxloc (id * dt) 
                 update_prop update_ctxloc c ctxl_init decls.

    Module MData := SinglePassModule_Data MMB.
    Module MDataM <: GenericModule_DataDefs MId MData. 
      Definition members_ok := members_ok.
    End MDataM.
    Module M := GenericModule_Defs MId MData MDataM.
 
  End HelperD.

  (** Single-Pass Module given as the AST [decls]  
   ** is well-defined in the context [c]. *)
  Definition module_ok (c : ctx) (decls : list (id * dt)) : Prop :=
    HelperD.M.module_ok c decls.
  (*  let nms := map fst decls in
    (** all names are distinct *)
    List.NoDup nms
    (** and all members are valid *)
    /\ HelperD.members_ok c decls. *)
    

End SinglePassModuleDefs.

(* ################################################################# *)
(** ** Computable Part (static checker of the interpreter) *)
(* ################################################################# *)

Module SinglePassModuleInterp (Import MMB : SinglePassModuleBase) 
       (Import TOkI : DataLCOkInterp MMB.MD).

  Module HelperI.

    Definition check_member  (c : ctx) (cl : ctxloc) (decl : id * dt) : bool
      := TOkI.is_ok_b c cl (snd decl).

    Definition update_ctxloc (cl : ctxloc) (c : ctx) 
               (decl : id * dt) : ctxloc
      := match decl with (nm, d) => upd_ctxloc cl c nm d end.

(*
    (** Aux function checking one member (to be used in [fold_left]).
     ** The [okAndCl] param is an accumulator. *)
    Definition process_dep_member_b (c : ctx) 
               (okAndCl : bool * ctxloc) (decl : id * dt) 
               : bool * ctxloc := 
      match okAndCl with 
      | (true, cl) =>
        match decl with (nm, d) =>
          let ok := TOkI.is_ok_b c cl d in
          let cl' := MMB.upd_ctxloc cl c nm d in
          (ok, cl')
        end 
      | (false, cl) => (false, cl)
      end.

    (** Aux function checking that all members are ok 
     ** in the given initial conditions. *)
    Definition members_ok'_b (c : ctx) (cl : ctxloc) 
               (decls : list (id * dt)) : bool * ctxloc :=
      List.fold_left (process_dep_member_b c) decls (true, cl).
*)

    (** Aux function checking that all members are ok. *)
    Definition members_ok_b (c : ctx) (decls : list (id * dt)) : bool :=
      members_ok_b ctx ctxloc (id * dt)
                   check_member update_ctxloc c ctxl_init decls.

    Module MData := SinglePassModule_Data MMB.
    Module MDataM <: GenericModule_DataInterp MId MData. 
      Definition members_ok_b := members_ok_b.
    End MDataM.
    Module M := GenericModule_Interp MId MData MDataM.

  End HelperI.

  (** Checks that a module given as the AST [decls]  
   ** is well-defined in the context [c]. *)
  Definition module_ok_b (c : ctx) (decls : list (id * dt)) : bool :=
    HelperI.M.module_ok_b c decls.
  (*  let nms := map fst decls in
    andb
      (** all names are distinct *)
      (MId.IdLS.ids_are_unique nms)
      (** and all types are valid *)
      (HelperI.members_ok_b c decls). *)

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

    Lemma members_ok_b__sound :
      forall (c : ctx) (decls : list (id * dt)),
      members_ok_b c decls = true ->
      members_ok c decls.
    Proof.
      intros c ds H.
      unfold members_ok_b in H.
      unfold members_ok.
      apply members_ok_b__sound with (update_prop := update_prop) in H.
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
      apply members_ok_b__complete with (check_member := check_member) in H.
      assumption. 
      exact check_member__complete.
      exact update_prop__spec.
    Qed.

(* ----------------------------------------------------------------- *) 

    Module MData := MMD.HelperD.MData.
    Module MDataM <: GenericModule_DataProps 
                       MId MData MMD.HelperD.MDataM MMI.HelperI.MDataM.
      Definition members_ok_b__sound := members_ok_b__sound.
      Definition members_ok_b__complete := members_ok_b__complete.
    End MDataM.
    Module M := GenericModule_Props 
                  MId MMD.HelperD.MData
                  MMD.HelperD.MDataM MMI.HelperI.MDataM
                  MDataM.

  End Helper.

(* ================================================================= *)
(** *** Properties *)
(* ================================================================= *)

  Theorem module_ok_b__sound : forall (c : ctx) (decls : list (id * dt)),
      module_ok_b c decls = true ->
      module_ok c decls.
  Proof.
    apply Helper.M.module_ok_b__sound.
(*    intros c ds. intros H.
    unfold module_ok_b in H. 
    unfold module_ok.
    rewrite -> andb_true_iff in H. inversion H as [Hid Hds].
    apply MId.IdLS.Props.ids_are_unique__sound in Hid.
    apply Helper.members_ok_b__sound in Hds.
    split; assumption. *)
  Qed.

  Theorem module_ok_b__complete : forall (c : ctx) (decls : list (id * dt)),
      module_ok c decls ->
      module_ok_b c decls = true.
  Proof.
    apply Helper.M.module_ok_b__complete.
(*    intros c ds. intros H.
    unfold module_ok_b.
    unfold module_ok in H.
    inversion H as [Hdup Hmems].
    rewrite -> andb_true_iff. split.
    apply MId.IdLS.Props.ids_are_unique__complete in Hdup. assumption.
    apply Helper.members_ok_b__complete. assumption. *)
  Qed.

End SinglePassModuleProps.



