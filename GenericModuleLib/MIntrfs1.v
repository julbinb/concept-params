(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(* Module with Certified Checking 
   of the simplest module-interface.
  
   Last Update: Wed, 3 May 2017
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
  (*Definition id_set := IdLS.id_set.*)
End IdentifiersBase.

Module Type IntrfsBase.
  Include IdentifiersBase.

  (* Types Data *)
  Declare Module TyDT : Data.
  Definition ty := TyDT.t.

  Definition intrfs_ast := list (id * ty).
  Definition intrfs_map := IdLPM.id_map ty.

  Parameter members_to_define : intrfs_map -> list id.
End IntrfsBase.

Module Type Intrfs1Base.
  Include IntrfsBase.
  Definition ctx := TyDT.ctx.
End Intrfs1Base.

(* ################################################################# *)
(** ** Propositional Part *)
(* ################################################################# *)

Module MIntrfs1Defs (Import MIB : Intrfs1Base) 
       (Import TOkD : DataOkDef MIB.TyDT).

  Module HelperD.

    (** Aux definition "all types in a list are ok" *)
    Definition types_ok (c : ctx) (tps : list ty) : Prop :=
      List.Forall (fun tp => is_ok c tp) tps.

  End HelperD.

  (** Interface given as an AST [ds] is well-defined 
   ** in the context [c] *)
  Definition intrfs_ok (c : ctx) (ds : list (id * ty)) : Prop :=
    let (nms, tps) := split ds in
    (** all names are distinct *)
    List.NoDup nms
    (** and all types are valid *)
    /\ HelperD.types_ok c tps. 

  (** The finite map [imap] corresponds to the given well-defined
   ** AST [iast] of an interface *)
  Definition intrfs_ast_has_eq_map (c : ctx) 
             (iast : intrfs_ast) (imap : intrfs_map) : Prop :=
    (* interface is well-defined *)
    intrfs_ok c iast
    (* map is equal to ast *)
    /\ IdLPM.eq_list_map iast imap.

End MIntrfs1Defs.

(* ################################################################# *)
(** ** Computable Part (static checker of the interpreter) *)
(* ################################################################# *)

Module MIntrfs1Interp (Import MIB : Intrfs1Base) 
       (Import TOkI : DataOkInterp MIB.TyDT).

  Module HelperI.

    Definition types_ok_b (c : ctx) (tps : list ty) : bool :=
      List.forallb (fun tp => is_ok_b c tp) tps.

  End HelperI.

  (** Checks that an interface given as an AST [ds]  
   ** is well-defined in the context [c] *)
  Definition intrfs_ok_b (c : ctx) (ds : list (id * ty)) : bool :=
    let (nms, tps) := split ds in
    andb
      (** all names are distinct *)
      (IdLS.ids_are_unique nms)
      (** and all types are valid *)
      (HelperI.types_ok_b c tps).

  (** If an interface with the AST [iast] is well-defined,  
   ** converts it to the equal finite map *)
  Definition intrfs_ast_to_eq_map (c : ctx) 
             (iast : intrfs_ast) : option intrfs_map :=
    (* if interface is well-defined *)
    if intrfs_ok_b c iast then
      (* generate map from ast *)
      Some (IdLPM.map_from_list iast)
    else None.
 
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
  Import MID.HelperD. Import MII.HelperI.

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

End MIntrfs1Props.



