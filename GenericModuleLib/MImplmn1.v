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

Require Import ConceptParams.GenericModuleLib.MIntrfs1.

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Bool.Bool.

Require Import Coq.Structures.Orders.
Require Import Coq.Structures.Equalities.

(* ***************************************************************** *)
(** * Module-Implementation 1 

      The Simplest Semantics of Modules *)

(** Module-Implementation is well-defined with respect to
    if
    all names are different 
    and all types are well-defined. *)
(* ***************************************************************** *)
(* ***************************************************************** *)

(* ################################################################# *)
(** ** Module Types defining Parameters *)
(* ################################################################# *)

Module Type DepData.  
  (* contains types [t] and [ctx] *)
  Include Data. 

  (** Type of Local Context *)
  Parameter ctx_local : Type.
End DepData.

Module Type DepDataOkDef (Import D : DepData) 
       (Import MI : IntrfsBase).
  (* element is ok on its own, 
   * and it also corresponds to the interface *)
  Parameter is_ok : ctx -> intrfs_map -> ctx_local -> 
                    id -> t -> Prop.
End DepDataOkDef.

Module Type DepDataOkInterp (Import D : DepData)
       (Import MI : IntrfsBase).
  Parameter is_ok_b : ctx -> intrfs_map -> ctx_local -> 
                      id -> t -> bool.
End DepDataOkInterp.

Module Type DepDataOkProp (Import D : DepData) 
       (Import MI : IntrfsBase)
       (Import DDef : DepDataOkDef D MI) (Import DInt : DepDataOkInterp D MI).

  Axiom is_ok_b__sound : 
    forall (c : ctx) (imap : MI.intrfs_map) (cl : ctx_local)
           (nm : id) (x : t),
      is_ok_b c imap cl nm x = true -> is_ok c imap cl nm x.

  Axiom is_ok_b__complete : 
    forall (c : ctx) (imap : MI.intrfs_map) (cl : ctx_local) 
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

Module Type Implmn1Base (Import MI : IntrfsBase).
  Include (ImplmnBase MI).

  Definition ctx := TmDT.ctx.

  Definition ctx_local := TmDT.ctx_local.
  (** Initial local context *)
  Parameter ctxl_init : ctx_local.
  (** Update local context *)
  Parameter upd_ctx_local : ctx_local -> ctx -> intrfs_map -> 
                            id -> tm -> ctx_local.
End Implmn1Base.

(* ################################################################# *)
(** ** Propositional Part *)
(* ################################################################# *)

Module MImplmn1Defs 
       (Import MI : IntrfsBase)
       (Import MIB : Implmn1Base MI) 
       (Import TOkD : DepDataOkDef MIB.TmDT MI).

  Definition process_dep_member
             (c : ctx) (imap : intrfs_map)
             (okAndCl : Prop * ctx_local) (def : id * tm) 
  : Prop * ctx_local :=
    match okAndCl with (ok_prop, cl) =>
    match def with (nm, t) =>
      let ok_prop' := 
          (* check curr member in the local context *)
          TOkD.is_ok c imap cl nm t  
          (* and preserve previous members' part *)
          /\ ok_prop in
      (* update local context *)
      let cl' := MIB.upd_ctx_local cl c imap nm t in
      (ok_prop', cl')
    end end.

  (** [initP] could be any provable proposition.
      This is more convenient for doing proofs than 
        using [True] as initial proposition, for example. *)
  Definition terms_ok' 
             (c : ctx) (imap : intrfs_map) (cl : ctx_local) (initP : Prop)
             (defs : list (id * tm)) : Prop * ctx_local :=
    List.fold_left
      (process_dep_member c imap)
      defs
      (initP, cl).

  Definition terms_ok 
             (c : ctx) (imap : intrfs_map) 
             (defs : list (id * tm)) : Prop :=
    fst (terms_ok' c imap ctxl_init True defs).


  Definition implmn_ok 
             (c : ctx) (imap : intrfs_map) 
             (defs : list (id * tm)) : Prop :=
    let nms := IdLPM.get_ids defs in
    (** all names are distinct *)
    List.NoDup nms
    (** and all members are valid *)
    /\ terms_ok c imap defs. 

End MImplmn1Defs.

(* ################################################################# *)
(** ** Computable Part (static checker of the interpreter) *)
(* ################################################################# *)

Module MImplmn1Interp 
       (Import MI : IntrfsBase)
       (Import MIB : Implmn1Base MI) 
       (Import TOkI : DepDataOkInterp MIB.TmDT MI).

  
  Definition process_dep_member_b 
             (c : ctx) (imap : intrfs_map)
             (okAndCl : bool * ctx_local) (def : id * tm) 
  : bool * ctx_local :=
    match okAndCl with 
    | (true, cl) =>
      match def with (nm, t) =>
        let ok := TOkI.is_ok_b c imap cl nm t in
        let cl' := MIB.upd_ctx_local cl c imap nm t in
        (ok, cl')
      end 
    | (false, cl) => (false, cl)
    end.

  Definition terms_ok'_b 
             (c : ctx) (imap : intrfs_map) (cl : ctx_local)
             (defs : list (id * tm)) : bool * ctx_local :=
    List.fold_left
      (process_dep_member_b c imap)
      defs
      (true, cl).

  Definition terms_ok_b 
             (c : ctx) (imap : intrfs_map) 
             (defs : list (id * tm)) : bool :=
    fst (terms_ok'_b c imap ctxl_init defs).

  Definition implmn_ok_b 
             (c : ctx) (imap : intrfs_map) 
             (defs : list (id * tm)) : bool :=
    let nms := IdLPM.get_ids defs in
    andb
      (** all names are distinct *)
      (IdLS.ids_are_unique nms)
      (** and all types are valid *)
      (terms_ok_b c imap defs).
 
End MImplmn1Interp.

(* ################################################################# *)
(** ** Proofs of Correctness *)
(* ################################################################# *)

Module MImplmn1Props 
       (Import MI : IntrfsBase)
       (Import MIB : Implmn1Base MI) 
       (Import TOkD : DepDataOkDef MIB.TmDT MI)
       (Import TOkI : DepDataOkInterp MIB.TmDT MI)
       (Import TOkP : DepDataOkProp MIB.TmDT MI TOkD TOkI)
.
  Module Import MID := MImplmn1Defs   MI MIB TOkD.
  Module Import MII := MImplmn1Interp MI MIB TOkI.


(* ----------------------------------------------------------------- *)
(** *** Helper Props  *)
(* ----------------------------------------------------------------- *)

  Module Helper.

    (** Soundness *)   

    Lemma process_dep_member_b_preserves_false :
      forall (c : ctx) (imap : intrfs_map)
             (ds : list (id * tm)) (cl : ctx_local),
        fold_left (process_dep_member_b c imap) ds (false, cl) = (false, cl).
    Proof.
      intros c imap ds.
      induction ds as [| [nm t] ds' IHds'];
        intros cl.
      - (* ds = nil *)
        simpl. reflexivity.
      - (* ds = (nm, t) :: ds' *)
        simpl. apply IHds'.
    Qed.

    Lemma terms_ok'_b_cons_true :
      forall (c : ctx) (imap : intrfs_map)
             (ds : list (id * tm)) (cl : ctx_local)
             (nm : id) (t : tm),
        fst (terms_ok'_b c imap cl ((nm, t) :: ds)) = true ->
        fst (terms_ok'_b c imap (upd_ctx_local cl c imap nm t) ds) = true.
    Proof.
      intros c imap ds.
      unfold terms_ok'_b. simpl.
      intros cl nm t H.
      assert (Hok : is_ok_b c imap cl nm t = true).
      { destruct (is_ok_b c imap cl nm t) eqn:Heq.
        reflexivity.
        destruct ds as [| d ds'].
        + simpl in H. assumption.
        + rewrite (process_dep_member_b_preserves_false c imap _ _) in H.
          simpl in H. inversion H. }
      rewrite Hok in H. assumption.
    Qed.

    Lemma terms_ok'_b_true__head_ok :
      forall (c : ctx) (imap : intrfs_map)
             (ds : list (id * tm)) (cl : ctx_local)
             (nm : id) (t : tm),
        fst (terms_ok'_b c imap cl ((nm, t) :: ds)) = true ->
        is_ok_b c imap cl nm t = true.
    Proof.
      intros c imap ds cl nm t H.
      unfold terms_ok'_b in H. simpl in H.
      destruct (is_ok_b c imap cl nm t) eqn:Heq.
      reflexivity.
      rewrite (process_dep_member_b_preserves_false c imap _ _) in H.
      simpl in H. assumption.
    Qed. 

    Lemma terms_ok'_b__sound :
      forall (c : ctx) (imap : intrfs_map)
             (defs : list (id * tm)) (cl : ctx_local) (initP : Prop),
        initP ->
        fst (terms_ok'_b c imap cl defs) = true ->
        fst (terms_ok' c imap cl initP defs).
    Proof.
      intros c imap ds.
      induction ds as [| [nm t] ds' IHds'];
        intros cl P HP H.
      - simpl. assumption.
      - (* ds = (nm, t) :: ds' *)
        assert (H' := H).
        apply terms_ok'_b_true__head_ok in H'.
        assert (H'' := H').
        apply TOkP.is_ok_b__sound in H''.
        unfold terms_ok'. simpl.
        apply IHds'.
        tauto.
        unfold terms_ok'_b in H. simpl in H.
        unfold terms_ok'_b. rewrite H' in H. 
        assumption.
    Qed.

(* ----------------------------------------------------------------- *) 

    (** Completeness *)

    Lemma terms_ok'__fst_prop :
      forall (c : ctx) (imap : intrfs_map)
             (ds : list (id * tm)) (cl : ctx_local) (initP : Prop)
             (nm : id) (t : tm),
      exists Ps : Prop,
        (fst (terms_ok' c imap cl initP ((nm, t) :: ds)) = Ps)
        /\ (Ps -> (is_ok c imap cl nm t) /\ initP).
    Proof.
      intros c imap ds.
      induction ds as [| [dnm dt] ds' IHds'];
        intros cl P nm t.
      - (* ds = nil *)
        unfold terms_ok'. simpl. 
        exists (is_ok c imap cl nm t /\ P).
        tauto.
      - (* ds = (dnm, dt) :: ds' *)
        replace (fst (terms_ok' c imap cl P ((nm, t) :: (dnm, dt) :: ds')))
        with (fst (terms_ok' c imap (upd_ctx_local cl c imap nm t) 
                             (is_ok c imap cl nm t /\ P) ((dnm, dt) :: ds')))
          by (unfold terms_ok'; reflexivity).
        remember (upd_ctx_local cl c imap nm t) as cl'.      
        specialize (IHds' cl' (is_ok c imap cl nm t /\ P) dnm dt).
        inversion IHds' as [Ps HPs].
        inversion HPs as [Heq Himp].
        exists Ps. split.
        assumption. tauto.
    Qed.

    Lemma terms_ok'__head_ok :
      forall (c : ctx) (imap : intrfs_map)
             (ds : list (id * tm)) (cl : ctx_local) (initP : Prop)
             (nm : id) (t : tm),
        initP ->
        fst (terms_ok' c imap cl initP ((nm, t) :: ds)) ->
        (is_ok c imap cl nm t) /\ initP.
    Proof.
      intros c imap ds cl P nm t HP H.
      pose proof (terms_ok'__fst_prop c imap ds cl P nm t) as Hex.
      inversion Hex as [Ps [Heq Himp]].
      rewrite Heq in H. apply Himp in H.
      assumption.
    Qed. 

    Lemma terms_ok'_b__complete :
      forall (c : ctx) (imap : intrfs_map)
             (defs : list (id * tm)) (cl : ctx_local) (initP : Prop),
        initP ->
        fst (terms_ok' c imap cl initP defs) ->
        fst (terms_ok'_b c imap cl defs) = true.
    Proof.
      intros c imap ds.
      induction ds as [| [nm t] ds' IHds'];
        intros cl P HP H.
      - simpl. reflexivity.
      - (* ds = (nm, t) :: ds' *)
        assert (H' := H).
        apply terms_ok'__head_ok in H'.
        inversion H' as [Hok _].
        assert (Hok' := Hok). apply TOkP.is_ok_b__complete in Hok'.
        remember (upd_ctx_local cl c imap nm t) as cl'.
        replace (terms_ok'_b c imap cl ((nm, t) :: ds'))
        with (terms_ok'_b c imap cl' ds')
          by (unfold terms_ok'_b; simpl; subst cl'; rewrite Hok'; reflexivity).
        apply IHds' with (initP := is_ok c imap cl nm t /\ P).
        assumption.
        unfold terms_ok' in *. simpl in *.
        subst cl'. assumption. assumption.
    Qed.    

  End Helper.

(* ================================================================= *)
(** *** Properties *)
(* ================================================================= *)

  Lemma terms_ok_b__sound :
    forall (c : ctx) (imap : intrfs_map) (defs : list (id * tm)),
      terms_ok_b c imap defs = true ->
      terms_ok c imap defs.
  Proof.
    intros c imap ds H.
    unfold terms_ok_b in H.
    unfold terms_ok.
    apply Helper.terms_ok'_b__sound with (initP := True) in H.
    assumption. constructor.
  Qed.

  Lemma terms_ok_b__complete :
    forall (c : ctx) (imap : intrfs_map) (defs : list (id * tm)),
      terms_ok c imap defs -> 
      terms_ok_b c imap defs = true.
  Proof.
    intros c imap ds H.
    unfold terms_ok in H.
    unfold terms_ok_b.
    apply Helper.terms_ok'_b__complete with (initP := True) in H.
    assumption. constructor.
  Qed.

End MImplmn1Props.



