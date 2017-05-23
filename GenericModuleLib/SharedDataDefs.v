(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(* Module with shared definitions used by 
   "interfaces" and "implementations".
  
   Last Update: Mon, 22 May 2017
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 

Add LoadPath "../..".

Require Import ConceptParams.AuxTactics.LibTactics.
Require Import ConceptParams.AuxTactics.BasicTactics.

Require Import ConceptParams.SetMapLib.List2Set.
Require Import ConceptParams.SetMapLib.ListPair2FMap.

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Bool.Bool.

Require Import Coq.Structures.Orders.
Require Import Coq.Structures.Equalities.

(* ***************************************************************** *)
(** * Shared Data Definitions *)

(** Data definition shared by various kinds of modules *)
(* ***************************************************************** *)
(* ***************************************************************** *)

(* ################################################################# *)
(** ** Data Module Types  *)
(* ################################################################# *)

(** Wrapper module for a single type *)
Module Type Data.
  (** Type of Data *)
  Parameter t : Type.
End Data.

(** Module consisting of types of _Data_ and _Context_ *)
Module Type DataC.
  (** Type of Data *)
  Parameter t : Type.
  (** Type of Context (might be needed for checking WD of [t]) *)
  Parameter ctx : Type.
End DataC.

(** Module consisting of types of 
 ** _Data_, _global context_, and _Local Context_ *)
Module Type DataLC.  
  (** Type of Data *)
  Parameter t : Type.
  (** Type of Context (might be needed for checking WD of [t]) *)
  Parameter ctx : Type.
  (** Type of Local Context which might also be needed
   ** for checking WD of [t] *)
  Parameter ctxloc : Type.
End DataLC.


(* ################################################################# *)
(** ** Module Types for Well-definedness of Modules *)
(* ################################################################# *)

(* ================================================================= *)
(** ** Module Types for Well-definedness of Simple Modules *)

(** In a _Simple Module_ all elements are checked independently 
 ** of each other: only global context matters. *)
(* ================================================================= *)

Module Type DataCOkDef (Import D : DataC).
  Parameter is_ok : ctx -> t -> Prop.
End DataCOkDef.

Module Type DataCOkInterp (Import D : DataC).
  Parameter is_ok_b : ctx -> t -> bool.
End DataCOkInterp.

Module Type DataCOkProp (Import D : DataC) 
       (Import DDef : DataCOkDef D) (Import DInt : DataCOkInterp D).

  Axiom is_ok_b__sound : forall (c : ctx) (x : t),
      is_ok_b c x = true -> is_ok c x.
  Axiom is_ok_b__complete : forall (c : ctx) (x : t),
      is_ok c x -> is_ok_b c x = true.
End DataCOkProp.

(* ================================================================= *)
(** ** Module Types with Well-definedness of Single-Pass Modules *)

(** In a _Single-Pass Module_ following elements can refer to
 ** the previously defined ones by means of the local context. *)
(* ================================================================= *)

Module Type DataLCOkDef (Import D : DataLC). 
  (* Element [t] must be ok with respect 
     to global [ctx] and local [ctxloc] contexts. *) 
  Parameter is_ok : ctx -> ctxloc -> t -> Prop.
End DataLCOkDef.

Module Type DataLCOkInterp (Import D : DataLC).
  Parameter is_ok_b : ctx -> ctxloc -> t -> bool.
End DataLCOkInterp.

Module Type DataLCOkProp (Import D : DataLC) 
       (Import DDef : DataLCOkDef D) (Import DInt : DataLCOkInterp D).

  Axiom is_ok_b__sound : forall (c : ctx) (cl : ctxloc) (x : t),
    is_ok_b c cl x = true -> is_ok c cl x.
  
  Axiom is_ok_b__complete : forall (c : ctx) (cl : ctxloc) (x : t),
    is_ok c cl x -> is_ok_b c cl x = true.
End DataLCOkProp.


(* ################################################################# *)
(** ** Shared Parameters of all building blocks *)
(* ################################################################# *)

Module Type IdentifiersBase.
  (* Id Set *)
  Declare Module IdDT  : UsualDecidableType.
  Declare Module IdSET : MSetInterface.WSets
           with Definition E.t := IdDT.t
           with Definition E.eq := IdDT.eq.
  Declare Module IdLS  : List2MSet IdDT IdSET.
  
  (* Id Map *)
  Declare Module IdDT' : ListPair2FMap.UsualDecidableTypeOrig
      with Definition t  := IdDT.t
      with Definition eq := IdDT.eq.
  Declare Module IdMAP : FMapInterface.WS 
           with Definition E.t := IdDT.t
           with Definition E.eq := IdDT.eq.
  Declare Module IdLPM : ListPair2FMapW IdDT' IdMAP.

  (* Id *)
  Definition id := IdDT.t.
(*Definition id_set := IdLS.id_set.
  Definition id_map := IdLPM.id_map.*)
End IdentifiersBase.


(* ################################################################# *)
(** ** Module Types for Modules *)
(* ################################################################# *)

Module Type ModuleBase.
  Declare Module MId : IdentifiersBase.
  Definition id := MId.id.
  Definition id_set := MId.IdLS.id_set.
  Definition id_map := MId.IdLPM.id_map.
End ModuleBase.


(* ################################################################# *)
(** ** Generic Well-definedness of Modules *)
(* ################################################################# *)

Module Type GenericModule_Data.
  (** Type of members *)
  Parameter dt : Type.
  (** Type of context *)
  Parameter ctx : Type.
End GenericModule_Data.


Module Type GenericModule_DataDefs (Import MId : IdentifiersBase) 
       (Import MD : GenericModule_Data).
  Parameter members_ok : ctx -> list (id * dt) -> Prop.
End GenericModule_DataDefs.

Module Type GenericModule_DataInterp (Import MId : IdentifiersBase) 
       (Import MD : GenericModule_Data).
  Parameter members_ok_b : ctx -> list (id * dt) -> bool.
End GenericModule_DataInterp.

Module Type GenericModule_DataProps (Import MId : IdentifiersBase) 
       (Import MD  : GenericModule_Data)
       (Import MDD : GenericModule_DataDefs MId MD)
       (Import MDI : GenericModule_DataInterp MId MD)
.
  Axiom members_ok_b__sound : forall (c : ctx) (decls : list (id * dt)),
    members_ok_b c decls = true -> members_ok c decls.
  
  Axiom members_ok_b__complete : forall (c : ctx) (decls : list (id * dt)),
    members_ok c decls -> members_ok_b c decls = true.
End GenericModule_DataProps.


Module GenericModule_Defs (Import MId : IdentifiersBase) 
       (Import MD  : GenericModule_Data)
       (Import MDD : GenericModule_DataDefs MId MD).

  Definition module_ok (c : ctx) (decls : list (id * dt)) : Prop :=
    let nms := map fst decls in
    (** all names are distinct *)
    List.NoDup nms
    (** and all members are valid *)
    /\ members_ok c decls. 

End GenericModule_Defs.

Module GenericModule_Interp (Import MId : IdentifiersBase) 
       (Import MD : GenericModule_Data)
       (Import MDI : GenericModule_DataInterp MId MD).

  Definition module_ok_b (c : ctx) (decls : list (id * dt)) : bool :=
    let nms := map fst decls in
    andb
      (** all names are distinct *)
      (MId.IdLS.ids_are_unique nms)
      (** and all types are valid *)
      (members_ok_b c decls).

End GenericModule_Interp.

Module GenericModule_Props (Import MId : IdentifiersBase) 
       (Import MD : GenericModule_Data)
       (Import MDD : GenericModule_DataDefs MId MD)
       (Import MDI : GenericModule_DataInterp MId MD)
       (Import MDP : GenericModule_DataProps MId MD MDD MDI).

  Module MDef := GenericModule_Defs   MId MD MDD.
  Module MInt := GenericModule_Interp MId MD MDI.
  Import MDef. Import MInt.

  Theorem module_ok_b__sound : forall (c : ctx) (decls : list (id * dt)),
      module_ok_b c decls = true ->
      module_ok c decls.
  Proof.
    intros c ds. intros H.
    unfold module_ok_b in H. 
    unfold module_ok.
    rewrite -> andb_true_iff in H. inversion H as [Hid Hds].
    apply MId.IdLS.Props.ids_are_unique__sound in Hid.
    apply members_ok_b__sound in Hds.
    split; assumption.
  Qed.

  Theorem module_ok_b__complete : forall (c : ctx) (decls : list (id * dt)),
      module_ok c decls ->
      module_ok_b c decls = true.
  Proof.
    intros c ds. intros H.
    unfold module_ok_b.
    unfold module_ok in H.
    inversion H as [Hdup Hmems].
    rewrite -> andb_true_iff. split.
    apply MId.IdLS.Props.ids_are_unique__complete in Hdup. assumption.
    apply members_ok_b__complete. assumption.
  Qed.  

End GenericModule_Props.






Module GenericModuleData (Import MId : IdentifiersBase).
  
  (** Type of members *)
  Parameter dt : Type.
  (** Type of context *)
  Parameter ctx : Type.

  Parameter members_ok   : ctx -> list (id * dt) -> Prop.

  Definition module_ok (c : ctx) (decls : list (id * dt)) : Prop :=
    let nms := map fst decls in
    (** all names are distinct *)
    List.NoDup nms
    (** and all members are valid *)
    /\ members_ok c decls. 

  Parameter members_ok_b : ctx -> list (id * dt) -> bool.

  Definition module_ok_b (c : ctx) (decls : list (id * dt)) : bool :=
    let nms := map fst decls in
    andb
      (** all names are distinct *)
      (MId.IdLS.ids_are_unique nms)
      (** and all types are valid *)
      (members_ok_b c decls).

  Axiom members_ok_b__sound : forall (c : ctx) (decls : list (id * dt)),
    members_ok_b c decls = true -> members_ok c decls.
  
  Axiom members_ok_b__complete : forall (c : ctx) (decls : list (id * dt)),
    members_ok c decls -> members_ok_b c decls = true.

  Theorem module_ok_b__sound : forall (c : ctx) (decls : list (id * dt)),
      module_ok_b c decls = true ->
      module_ok c decls.
  Proof.
    intros c ds. intros H.
    unfold module_ok_b in H. 
    unfold module_ok.
    rewrite -> andb_true_iff in H. inversion H as [Hid Hds].
    apply MId.IdLS.Props.ids_are_unique__sound in Hid.
    apply members_ok_b__sound in Hds.
    split; assumption.
  Qed.

  Theorem module_ok_b__complete : forall (c : ctx) (decls : list (id * dt)),
      module_ok c decls ->
      module_ok_b c decls = true.
  Proof.
    intros c ds. intros H.
    unfold module_ok_b.
    unfold module_ok in H.
    inversion H as [Hdup Hmems].
    rewrite -> andb_true_iff. split.
    apply MId.IdLS.Props.ids_are_unique__complete in Hdup. assumption.
    apply members_ok_b__complete. assumption.
  Qed.  

End GenericModuleData.





(* ################################################################# *)
(** ** Old *)
(* ################################################################# *)

Module Type DataOkDef (D : DataC) := DataCOkDef D.
Module Type DataOkInterp (D : DataC) := DataCOkInterp D.
Module Type DataOkProp (D : DataC) 
       (DDef : DataCOkDef D) (DInt : DataCOkInterp D) :=
  DataCOkProp D DDef DInt.


Module Type IntrfsBase.
  Include IdentifiersBase.

  (* Types Data *)
  Declare Module TyDT : DataC.
  Definition ty := TyDT.t.

  Definition intrfs_ast := list (id * ty).
  Definition intrfs_map := IdLPM.id_map ty.

  Parameter members_to_define : intrfs_map -> list id.
End IntrfsBase.

Module Type IntrfsLCBase.
  Include IdentifiersBase.

  (* Types Data *)
  Declare Module TyDT : DataLC.
  Definition ty := TyDT.t.

  Definition intrfs_ast := list (id * ty).
  Definition intrfs_map := IdLPM.id_map ty.
End IntrfsLCBase.




(* ################################################################# *)
(** ** Module Types  *)
(* ################################################################# *)

(** Data which might depend on some local context. *)
Module Type DepData.  
  (** Contains types [t] and [ctx] *)
  Include DataC. 

  (** Type of local context which might be
      required for checking a  *)
  Parameter ctxloc : Type.
End DepData.

Module Type DepDataOkDef (Import D : DepData) 
       (Import MI : IntrfsBase).
  (* Element [id] = [t] must be ok with respect 
     to global [ctx] and local [ctxloc] contexts, and it also should 
     correspond to the interface represented by [intrfs_map] *) 
  Parameter is_ok : ctx -> intrfs_map -> ctxloc -> 
                    id -> t -> Prop.
End DepDataOkDef.

Module Type DepDataOkInterp (Import D : DepData)
       (Import MI : IntrfsBase).
  Parameter is_ok_b : ctx -> intrfs_map -> ctxloc -> 
                      id -> t -> bool.
End DepDataOkInterp.

Module Type DepDataOkProp (Import D : DepData) 
       (Import MI : IntrfsBase)
       (Import DDef : DepDataOkDef D MI) (Import DInt : DepDataOkInterp D MI).

  Axiom is_ok_b__sound : 
    forall (c : ctx) (imap : MI.intrfs_map) (cl : ctxloc)
           (nm : id) (x : t),
      is_ok_b c imap cl nm x = true -> is_ok c imap cl nm x.

  Axiom is_ok_b__complete : 
    forall (c : ctx) (imap : MI.intrfs_map) (cl : ctxloc) 
           (nm : id) (x : t),
      is_ok c imap cl nm x -> is_ok_b c imap cl nm x = true.
End DepDataOkProp.



(* ################################################################# *)
(** ** Shared Parameters of all building blocks *)
(* ################################################################# *)


Module Type ImplmnBase (Import MI : IntrfsBase).
  (** Module of a corresponding interface (the data depends on) *)
(*  Declare Module MI : IntrfsBase. *)

  (* Terms Data *) 
  Declare Module TmDT : DepData.
  Definition tm := TmDT.t.

  Definition implmn_ast := list (id * tm).
  Definition implmn_map := IdLPM.id_map tm.
End ImplmnBase.