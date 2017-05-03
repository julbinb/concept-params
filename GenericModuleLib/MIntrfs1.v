(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(* Module with Certified Checking 
   of the simplest module-interface.
  
   Last Update: Wed, 3 May 2017
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 

Add LoadPath "../..".

Require Import ConceptParams.AuxTactics.LibTactics.
Require Import ConceptParams.AuxTactics.BasicTactics.

Require Import ConceptParams.SetMapLib.List2Set.

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Bool.Bool.

Require Import Coq.Structures.Orders.

(* ***************************************************************** *)
(** * Module-Interface 1 

      The Simplest Semantics of Modules *)

(** Module-Interfase is well-defined if
    all names are different 
    and all types are well-defined. *)
(* ***************************************************************** *)
(* ***************************************************************** *)

(* ################################################################# *)
(** ** Module Types defining Parameters *)
(* ################################################################# *)

Module Type Data.
  (** Type of Data *)
  Parameter t : Type.
  (** Type of Context *)
  Parameter ctx : Type.
End Data.

Module Type DataOkDef (Import D : Data).
  Parameter is_ok : ctx -> t -> Prop.
End DataOkDef.

Module Type DataOkInterp (Import D : Data).
  Parameter is_ok_b : ctx -> t -> bool.
End DataOkInterp.

Module Type DataOkProp (Import D : Data) 
       (Import DDef : DataOkDef D) (Import DInt : DataOkInterp D).

  Axiom is_ok_b__sound : forall (c : ctx) (x : t),
      is_ok_b c x = true -> is_ok c x.
  Axiom is_ok_b__complete : forall (c : ctx) (x : t),
      is_ok c x -> is_ok_b c x = true.
End DataOkProp.

(* ################################################################# *)
(** ** Shared Parameters of all building blocks *)
(* ################################################################# *)

Module Type Intrfs1Base.
  Declare Module IdOT : UsualOrderedType.
  Declare Module TyDT : Data.
  Declare Module IdLS : List2Set IdOT.

  Definition id := IdOT.t.
  Definition ty := TyDT.t.
  Definition ctx := TyDT.ctx.
End Intrfs1Base.

(* ################################################################# *)
(** ** Propositional Part *)
(* ################################################################# *)

Module MIntrfs1Defs (Import MIB : Intrfs1Base) 
       (Import TOkD : DataOkDef MIB.TyDT).

  Definition types_ok (c : ctx) (tps : list ty) : Prop :=
    List.Forall (fun tp => is_ok c tp) tps.

  Definition intrfs_ok (c : ctx) (ds : list (id * ty)) : Prop :=
    let (nms, tps) := split ds in
    (** all names are distinct *)
    List.NoDup nms
    (** and all types are valid *)
    /\ types_ok c tps. 

End MIntrfs1Defs.

(* ################################################################# *)
(** ** Computable Part (static checker of the interpreter) *)
(* ################################################################# *)

Module MIntrfs1Interp (Import MIB : Intrfs1Base) 
       (Import TOkI : DataOkInterp MIB.TyDT).

  Definition types_ok_b (c : ctx) (tps : list ty) : bool :=
    List.forallb (fun tp => is_ok_b c tp) tps.

  Definition intrfs_ok_b (c : ctx) (ds : list (id * ty)) : bool :=
    let (nms, tps) := split ds in
    andb
      (** all names are distinct *)
      (IdLS.ids_are_unique nms)
      (** and all types are valid *)
      (types_ok_b c tps).
 
End MIntrfs1Interp.

(* ################################################################# *)
(** ** Proofs of Correctness *)
(* ################################################################# *)

Module MIntrfs1Props 
       (Import MIB : Intrfs1Base)
       (Import TOkD : DataOkDef MIB.TyDT)
       (Import TOkI : DataOkInterp MIB.TyDT)
       (Import TOkP : DataOkProp MIB.TyDT TOkD TOkI)
.
  Module Import MID := MIntrfs1Defs   MIB TOkD.
  Module Import MII := MIntrfs1Interp MIB TOkI.

  Lemma types_ok_b__sound : forall (c : ctx) (ts : list ty),
      types_ok_b c ts = true ->
      types_ok c ts.
  Proof.
    intros c ts. unfold types_ok_b.
    induction ts as [| tp ts'];
      intros H.
    - (* ts = nil *)
      apply Forall_nil.
    - (* ts = tp :: ts' *)
      simpl in H. rewrite -> andb_true_iff in H.
      inversion H as [Htp Hts']; clear H.
      apply IHts' in Hts'. 
      apply TOkP.is_ok_b__sound in Htp.
      apply Forall_cons; auto.
  Qed.

  Lemma types_ok_b__complete : forall (c : ctx) (ts : list ty),
      types_ok c ts ->
      types_ok_b c ts = true.
  Proof.
    intros c ts. unfold types_ok_b.
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

  Theorem intrfs_ok_b__sound : forall (c : ctx) (ds : list (id * ty)),
      intrfs_ok_b c ds = true ->
      intrfs_ok c ds.
  Proof.
    intros c ds. intros H.
    unfold intrfs_ok_b in H. 
    unfold intrfs_ok.
    destruct (split ds).
    rewrite -> andb_true_iff in H. inversion H as [Hid Hty].
    apply IdLS.Props.ids_are_unique__sound in Hid.
    apply types_ok_b__sound in Hty.
    split; tauto.
  Qed.

  Theorem intrfs_ok_b__complete : forall (c : ctx) (ds : list (id * ty)),
      intrfs_ok c ds ->
      intrfs_ok_b c ds = true.
  Proof.
    intros c ds. intros H.
    unfold intrfs_ok_b.
    unfold intrfs_ok in H.
    destruct (split ds).
    inversion H as [Hdup Htys].
    rewrite -> andb_true_iff. split.
    apply IdLS.Props.ids_are_unique__complete in Hdup. assumption.
    apply types_ok_b__complete. assumption.
  Qed.

  Theorem intrfs_ok__cons : forall (c : ctx) (ds : list (id * ty))
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

End MIntrfs1Props.
















(*
Module Type HasWellDef <: Typ.

  Include Typ.

  Parameter is_welldef   : t -> Prop.
  Parameter is_welldef_b : t -> bool.

End HasWellDef.


Module Type Concept1Base.

  Declare Module IdOT : UsualOrderedType.
  Declare Module TyWD : HasWellDef.
  Declare Module IdLS : List2Set IdOT.

  Definition id := IdOT.t.
  Definition ty := TyWD.t.

End Concept1Base.

Module Type Concept1Defs (Import MCB : Concept1Base).

  Parameter types_ok : list ty -> Prop.
  Parameter concept_ok : list (id * ty) -> Prop.

End Concept1Defs.

Module Type Concept1Interp (Import MCB : Concept1Base).

  Parameter types_ok_b : list ty -> bool.
  Parameter concept_ok_b : list (id * ty) -> bool.

End Concept1Interp.


Module MConcept1Base
       (id_UOT : UsualOrderedType)
       (ty_WD  : HasWellDef)
       (id_LS  : List2Set id_UOT)
<: Concept1Base.

  Module IdOT := id_UOT.
  Module TyWD := ty_WD.
  Module IdLS := id_LS.

  Definition id := IdOT.t.
  Definition ty := TyWD.t.

End MConcept1Base.


Module MConcept1Defs (Import MCB : Concept1Base).

  Definition types_ok (tps : list ty) : Prop :=
    List.Forall (fun tp => TyWD.is_welldef tp) tps.

  Definition concept_ok (ds : list (id * ty)) : Prop :=
    let (nms, tps) := split ds in
    (** all names are distinct *)
    List.NoDup nms
    (** and all types are valid *)
    /\ types_ok tps. 

End MConcept1Defs.


Module MConcept1Interp (Import MCB : Concept1Base).

  Definition types_ok_b (tps : list ty) : bool :=
    List.forallb (fun tp => TyWD.is_welldef_b tp) tps.

  Definition concept_ok_b (ds : list (id * ty)) : bool :=
    let (nms, tps) := split ds in
    andb
      (** all names are distinct *)
      (IdLS.ids_are_unique nms)
      (** and all types are valid *)
      (types_ok_b tps).
 
End MConcept1Interp.


Module MConcept1Props 
       (Import MCB : Concept1Base)
.
  Module Import MCD := MConcept1Defs   MCB.
  Module Import MCI := MConcept1Interp MCB.

  Lemma types_ok_b__sound : forall (ts : list ty),
        types_ok_b ts = true ->
        types_ok ts.
    Proof.
      intros ts. unfold types_ok_b.
      induction ts as [| tp ts'];
        intros H.
      - (* ts = nil *)
        apply Forall_nil.
      - (* ts = tp :: ts' *)
        simpl in H. rewrite -> andb_true_iff in H.
        inversion H as [Htp Hts']; clear H.
        apply IHts' in Hts'. 
        apply TyWD.is_welldef_b__sound in Htp.
        apply Forall_cons; auto.
    Qed.

    Lemma types_ok_b__complete : forall (ts : list ty),
        types_ok ts ->
        types_ok_b ts = true.
    Proof.
      intros ts. unfold types_ok_b.
      induction ts as [| tp ts' IHts'];
        intros H.
      - (* ts = nil *)
        reflexivity.
      - (* ts = tp :: ts' *)
        inversion H; subst.
        simpl. rewrite -> andb_true_iff. split.
        + apply TyWD.is_welldef_b__complete. assumption.
        + apply IHts'. assumption.
    Qed.

End MConcept1Props.

(*
Module MConcept1 
       (id_UOT : UsualOrderedType)
       (ty_WD  : HasWellDef)
       (id_LS  : List2Set id_UOT)
.

  Module IdOT := id_UOT.
  Module TyWD := ty_WD.
  Module IdLS := id_LS.

  Definition id := IdOT.t.
  Definition ty := TyWD.t.

  (*
  Definition get_ids (xs : list (id * ty)) : list id 
      := List.map fst xs.
  *)

(*  Module PropDefs. *)
  
    Definition types_ok (tps : list ty) : Prop :=
      List.Forall (fun tp => TyWD.is_welldef tp) tps.

    Definition concept_ok (ds : list (id * ty)) : Prop :=
      let (nms, tps) := split ds in
      (** all names are distinct *)
      List.NoDup nms
      (** and all types are valid *)
      /\ types_ok tps.    

(*  End PropDefs. *)


(*  Module FunDefs. *)

    Definition types_ok_b (tps : list ty) : bool :=
      List.forallb (fun tp => TyWD.is_welldef_b tp) tps.

    Definition concept_ok_b (ds : list (id * ty)) : bool :=
      let (nms, tps) := split ds in
      andb
        (** all names are distinct *)
        (IdLS.ids_are_unique nms)
        (** and all types are valid *)
        (types_ok_b tps).    

(*  End FunDefs. *)


(*  Module Props.
    Import PropDefs.
    Import FunDefs. *)
    
    Lemma types_ok_b__sound : forall (ts : list ty),
        types_ok_b ts = true ->
        types_ok ts.
    Proof.
      intros ts. unfold types_ok_b.
      induction ts as [| tp ts'];
        intros H.
      - (* ts = nil *)
        apply Forall_nil.
      - (* ts = tp :: ts' *)
        simpl in H. rewrite -> andb_true_iff in H.
        inversion H as [Htp Hts']; clear H.
        apply IHts' in Hts'. 
        apply TyWD.is_welldef_b__sound in Htp.
        apply Forall_cons; auto.
    Qed.

    Lemma types_ok_b__complete : forall (ts : list ty),
        types_ok ts ->
        types_ok_b ts = true.
    Proof.
      intros ts. unfold types_ok_b.
      induction ts as [| tp ts' IHts'];
        intros H.
      - (* ts = nil *)
        reflexivity.
      - (* ts = tp :: ts' *)
        inversion H; subst.
        simpl. rewrite -> andb_true_iff. split.
        + apply TyWD.is_welldef_b__complete. assumption.
        + apply IHts'. assumption.
    Qed.

(*  End Props. *)

  
End MConcept1.
*)
*)