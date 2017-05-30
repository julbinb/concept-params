(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(* Module with shared definitions used by 
   "interfaces" and "implementations".
  
   Last Update: Wed, 24 May 2017
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
(** ** Module Types for various kinds of data modules work with *)
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

(** Module consisting of types of 
 ** _Data_, _global context_, and _Local Context_,
 ** and also _Interface_. *)
Module Type DataLCI.  
  (** Type of Data *)
  Parameter t : Type.
  (** Type of Context (might be needed for checking WD of [t]) *)
  Parameter ctx : Type.
  (** Type of Local Context which might also be needed
   ** for checking WD of [t] *)
  Parameter ctxloc : Type.
  (** Type of Interface [t] could depend on. *)
  Parameter intrfs : Type.
End DataLCI.


(* ################################################################# *)
(** ** Shared Parameters and Code of all building blocks *)
(* ################################################################# *)

(* ================================================================= *)
(** *** Identifiers *)
(* ================================================================= *)

(** All we need to work with identifiers *)
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
(** ** Module Types - Parameters for Well-definedness of Modules *)
(* ################################################################# *)

(* ================================================================= *)
(** ** Parameters of Well-definedness of Simple Modules *)

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
(** ** Parameters of Well-definedness of Single-Pass Modules *)

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

(* ================================================================= *)
(** ** Module Types with Well-definedness 
 ** of Single-Pass Implementation Modules *)
(* ================================================================= *)

Module Type DataLCIOkDef (Import MId : IdentifiersBase) (Import D : DataLCI). 
  (* Element [t] must be ok with respect 
     to global [ctx] and local [ctxloc] contexts. *) 
  Parameter is_ok : ctx -> intrfs -> ctxloc -> id -> t -> Prop.
End DataLCIOkDef.

Module Type DataLCIOkInterp (Import MId : IdentifiersBase) (Import D : DataLCI).
  Parameter is_ok_b : ctx -> intrfs -> ctxloc -> id -> t -> bool.
End DataLCIOkInterp.

Module Type DataLCIOkProp (Import MId : IdentifiersBase) (Import D : DataLCI) 
       (Import DDef : DataLCIOkDef MId D) (Import DInt : DataLCIOkInterp MId D).

  Axiom is_ok_b__sound : 
    forall (c : ctx) (i : intrfs) (cl : ctxloc) (nm : id) (x : t),
      is_ok_b c i cl nm x = true -> is_ok c i cl nm x.
  
  Axiom is_ok_b__complete : 
    forall (c : ctx) (i : intrfs) (cl : ctxloc) (nm : id) (x : t),
      is_ok c i cl nm x -> is_ok_b c i cl nm x = true.
End DataLCIOkProp.


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
(** ** Shared Functionality of Module Checkers *)
(* ################################################################# *)

(* ================================================================= *)
(** ** Generic Well-definedness of all Modules *)
(* ================================================================= *)

Module GenericModule_ModuleOk (Import MId : IdentifiersBase).
Section GenericDefinitions.
  
  (** Type of members *)
  Variable dt : Type.
  (** Type of context *)
  Variable ctx : Type.
  
  Variable members_ok : ctx -> list (id * dt) -> Prop.
  Variable members_ok_b : ctx -> list (id * dt) -> bool.

  Variable members_ok_b__sound : forall (c : ctx) (decls : list (id * dt)),
    members_ok_b c decls = true -> members_ok c decls.
  Variable members_ok_b__complete : forall (c : ctx) (decls : list (id * dt)),
    members_ok c decls -> members_ok_b c decls = true.

  Definition module_ok (c : ctx) (decls : list (id * dt)) : Prop :=
    let nms := map fst decls in
    (** all names are distinct *)
    List.NoDup nms
    (** and all members are valid *)
    /\ members_ok c decls. 

  Definition module_ok_b (c : ctx) (decls : list (id * dt)) : bool :=
    let nms := map fst decls in
    andb
      (** all names are distinct *)
      (MId.IdLS.ids_are_unique nms)
      (** and all types are valid *)
      (members_ok_b c decls).
  
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

End GenericDefinitions.
End GenericModule_ModuleOk.


Module Type GenericModule_Data.
  (** Type of members *)
  Parameter dt : Type.
  (** Type of context *)
  Parameter ctx : Type.
End GenericModule_Data.


(* ================================================================= *)
(** *** Single-Pass Modules *)
(* ================================================================= *)

Module SinglePassModule_ProcessMembers.
Section GenericDefinitions.

(* ----------------------------------------------------------------- *)
(** **** Definitions and Functions *)
(* ----------------------------------------------------------------- *)

  Variable ctx : Type.
  Variable ctxloc : Type.
  Variable data : Type.

  Variable update_prop : Prop -> ctx -> ctxloc -> data -> Prop.
  Variable check_member : ctx -> ctxloc -> data -> bool.
  Variable update_ctxloc : ctxloc -> ctx -> data -> ctxloc.

  (** Aux function checking one member (to be used in [fold_left]).
   ** The [okAndCl] param is an accumulator. *)
  Definition process_dep_member 
             (c : ctx) (okAndCl : Prop * ctxloc) (dt : data) 
    : Prop * ctxloc 
    := match okAndCl with 
         (ok, cl) =>
         let ok' := update_prop ok c cl dt in
         let cl' := update_ctxloc cl c dt in
         (ok', cl')
       end.

  (** Boolean version of the previous function *)
  Definition process_dep_member_b 
             (c : ctx) (okAndCl : bool * ctxloc) (dt : data) 
    : bool * ctxloc 
    := match okAndCl with 
       | (true, cl) =>
         let ok' := check_member c cl dt in
         let cl' := update_ctxloc cl c dt in
         (ok', cl')
       | (false, cl) =>
         (false, cl)
       end.

  (** Aux function checking that all members are ok 
   ** in the given initial conditions.
   ** The [initP] parameter can be any provable proposition.
      This is more convenient for doing proofs than 
      using [True] as initial proposition, for example. *)
  Definition members_ok' (c : ctx) (cl : ctxloc) (initP : Prop)
             (dts : list data) : Prop * ctxloc 
    := List.fold_left (process_dep_member c) dts (initP, cl).

  (** Aux function checking that all members are ok 
   ** in the given initial conditions. *)
  Definition members_ok'_b (c : ctx) (cl : ctxloc)
             (dts : list data) : bool * ctxloc 
    := List.fold_left (process_dep_member_b c) dts (true, cl).

(* ----------------------------------------------------------------- *)

  (** Function checking that all members are ok. *)
  Definition members_ok 
             (c : ctx) (cl_init : ctxloc) (dts : list data) : Prop 
    := fst (members_ok' c cl_init True dts).

  (** Boolean version of the previous function. *)
  Definition members_ok_b 
             (c : ctx) (cl_init : ctxloc) (dts : list data) : bool 
    := fst (members_ok'_b c cl_init dts).

(*
  Lemma abc :
    forall P P' c cl dt, update_prop P c cl dt -> P'),
    forall (c : ctx) (cl_init : ctxloc) (dts : list data),
      members_ok c cl_init dts ->
      forall (cl : ctxloc) (P P' : Prop) 
             (HSpec : update_prop P c cl dt -> P'),
      forall dt : data, 
        List.In dt dts ->
*)        
            

(* ----------------------------------------------------------------- *)
(** **** Proofs *)
(* ----------------------------------------------------------------- *)

  Variable check_member__sound : 
    forall (c : ctx) (cl : ctxloc) (dt : data) (P : Prop),
      P -> 
      check_member c cl dt = true ->
      update_prop P c cl dt.

  Variable check_member__complete : 
    forall (c : ctx) (cl : ctxloc) (dt : data) (P : Prop),
      P -> 
      update_prop P c cl dt ->
      check_member c cl dt = true.

  Variable update_prop__spec :
    forall (c : ctx) (cl : ctxloc) (dt : data) (P : Prop),
      update_prop P c cl dt -> P.

(* ----------------------------------------------------------------- *)

  (** Soundness *)   

  Lemma process_dep_member_b_preserves_false : 
    forall (c : ctx) (dts : list data) (cl : ctxloc),
      fold_left (process_dep_member_b c) dts (false, cl) 
      = (false, cl).
  Proof.
    intros c ds.
    induction ds as [| d ds' IHds'];
      intros cl.
    - (* ds = nil *)
      simpl. reflexivity.
    - (* ds = d :: ds' *)
      simpl. apply IHds'.
  Qed.

  Lemma members_ok'_b_cons_true :
      forall (c : ctx) (dts : list data) (cl : ctxloc) (dt : data),
        fst (members_ok'_b c cl (dt :: dts)) = true ->
        fst (members_ok'_b c (update_ctxloc cl c dt) dts) = true.
    Proof.
      intros c ds.
      unfold members_ok'_b. simpl.
      intros cl dt H.
      assert (Hok : check_member c cl dt = true).
      { destruct (check_member c cl dt) eqn:Heq.
        reflexivity.
        destruct ds as [| dt' ds'].
        + simpl in H. assumption.
        + rewrite (process_dep_member_b_preserves_false c _ _) in H.
          simpl in H. inversion H. }
      rewrite Hok in H. assumption.
    Qed.

    Lemma members_ok'_b_true__head_ok :
      forall (c : ctx) (dts : list data) (cl : ctxloc) (dt : data),
        fst (members_ok'_b c cl (dt :: dts)) = true ->
        check_member c cl dt = true.
    Proof.
      intros c ds cl d H.
      unfold members_ok'_b in H. simpl in H.
      destruct (check_member c cl d) eqn:Heq.
      reflexivity.
      rewrite (process_dep_member_b_preserves_false c _ _) in H.
      simpl in H. assumption.
    Qed. 

    Lemma members_ok'_b__sound :
      forall (c : ctx) (dts : list data) (cl : ctxloc) (initP : Prop),
        initP ->
        fst (members_ok'_b c cl dts) = true ->
        fst (members_ok' c cl initP dts).
    Proof.
      intros c ds.
      induction ds as [| dt ds' IHds'];
        intros cl P HP H.
      - simpl. assumption.
      - (* ds = dt :: ds' *)
        assert (H' := H).
        apply members_ok'_b_true__head_ok in H'.
        unfold members_ok'. simpl.
        apply IHds'.
        assert (H'' := H').
        apply check_member__sound with (P := P) in H''. 
        tauto. assumption.
        unfold members_ok'_b in H. simpl in H.
        unfold members_ok'_b. rewrite H' in H. 
        assumption.
    Qed.

(* ----------------------------------------------------------------- *)

    (** Completeness *)

    Lemma members_ok'__fst_prop :
      forall (c : ctx) (dts : list data) (cl : ctxloc) 
             (initP : Prop) (dt : data),
      exists Ps : Prop,
        (fst (members_ok' c cl initP (dt :: dts)) = Ps)
        /\ (Ps -> update_prop initP c cl dt).
    Proof.
      intros c ds.
      induction ds as [| dt' ds' IHds'];
        intros cl P dt.
      - (* ds = nil *)
        unfold members_ok'. simpl. 
        exists (update_prop P c cl dt). tauto.
      - (* ds = dt' :: ds' *)
        replace (fst (members_ok' c cl P (dt :: dt' :: ds')))
        with (fst (members_ok' c (update_ctxloc cl c dt) 
                               (update_prop P c cl dt) (dt' :: ds')))
          by (unfold members_ok'; reflexivity).
        remember (update_ctxloc cl c dt) as cl'.      
        specialize (IHds' cl' (update_prop P c cl dt) dt').
        inversion IHds' as [Ps HPs].
        inversion HPs as [Heq Himp].
        exists Ps. split.
        assumption. 
        intros HPs'. apply Himp in HPs'.
        apply update_prop__spec in HPs'. tauto.
    Qed.

    Lemma members_ok'__head_ok :
      forall (c : ctx) (dts : list data) (cl : ctxloc) 
             (initP : Prop) (dt : data),
        initP ->
        fst (members_ok' c cl initP (dt :: dts)) ->
        update_prop initP c cl dt.
    Proof.
      intros c ds cl P dt HP H.
      pose proof (members_ok'__fst_prop c ds cl P dt) as Hex.
      inversion Hex as [Ps [Heq Himp]].
      rewrite Heq in H. apply Himp in H.
      assumption.
    Qed. 

    Lemma members_ok'_b__complete :
      forall (c : ctx) (dts : list data) (cl : ctxloc) (initP : Prop),
        initP ->
        fst (members_ok' c cl initP dts) ->
        fst (members_ok'_b c cl dts) = true.
    Proof.
      intros c ds.
      induction ds as [| dt ds' IHds'];
        intros cl P HP H.
      - simpl. reflexivity.
      - (* ds = dt :: ds' *)
        assert (H' := H).
        apply members_ok'__head_ok in H'; try assumption.
        assert (Hok := H'). 
        apply check_member__complete in Hok; try assumption.
        remember (update_ctxloc cl c dt) as cl'.
        replace (members_ok'_b c cl (dt :: ds'))
        with (members_ok'_b c cl' ds')
          by (unfold members_ok'_b; simpl; subst cl'; rewrite Hok; reflexivity).
        apply IHds' with (initP := update_prop P c cl dt).
        assumption.
        unfold members_ok' in *. simpl in *.
        subst cl'. assumption.
    Qed.

(* ----------------------------------------------------------------- *)

    Theorem members_ok_b__sound :
      forall (c : ctx) (cl_init : ctxloc) (dts : list data),
      members_ok_b c cl_init dts = true ->
      members_ok c cl_init dts.
    Proof.
      intros c cl_init ds H.
      unfold members_ok_b in H.
      unfold members_ok.
      apply members_ok'_b__sound with (initP := True) in H.
      assumption. constructor.
    Qed.

    Theorem members_ok_b__complete :
      forall (c : ctx) (cl_init : ctxloc) (dts : list data),
        members_ok c cl_init dts -> 
        members_ok_b c cl_init dts = true.
    Proof.
      intros c cl_init ds H.
      unfold members_ok in H.
      unfold members_ok_b.
      apply members_ok'_b__complete with (initP := True) in H.
      assumption. constructor.
    Qed.

End GenericDefinitions.
End SinglePassModule_ProcessMembers.



