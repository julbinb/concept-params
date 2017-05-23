(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(* Module with Certified Checking 
   of Single-Pass Module.
  
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

    (** Aux function checking one member (to be used in [fold_left]).
     ** The [okAndCl] param is an accumulator. *)
    Definition process_dep_member (c : ctx) 
               (okAndCl : Prop * ctxloc) (decl : id * dt) 
               : Prop * ctxloc := 
      match okAndCl with (ok_prop, cl) =>
      match decl with (nm, d) =>
        let ok_prop' := 
            (* check curr member in the local context *)
            TOkD.is_ok c cl d  
            (* and preserve previous members' part *)
            /\ ok_prop in
        (* update local context *)
        let cl' := MMB.upd_ctxloc cl c nm d in
        (ok_prop', cl')
      end end.

    (** Aux function checking that all members are ok 
     ** in the given initial conditions.
     ** The [initP] parameter can be any provable proposition.
          This is more convenient for doing proofs than 
          using [True] as initial proposition, for example. *)
    Definition members_ok' (c : ctx) (cl : ctxloc) (initP : Prop)
               (decls : list (id * dt)) : Prop * ctxloc :=
      List.fold_left (process_dep_member c) decls (initP, cl).

    (** Aux function checking that all members are ok. *)
    Definition members_ok (c : ctx) (decls : list (id * dt)) : Prop :=
      fst (members_ok' c ctxl_init True decls).

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

    (** Aux function checking that all members are ok. *)
    Definition members_ok_b (c : ctx) (decls : list (id * dt)) : bool :=
      fst (members_ok'_b c ctxl_init decls).

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
    
    (** Soundness *)   

    Lemma process_dep_member_b_preserves_false :
      forall (c : ctx) (decls : list (id * dt)) (cl : ctxloc),
        fold_left (process_dep_member_b c) decls (false, cl) = (false, cl).
    Proof.
      intros c ds.
      induction ds as [| [nm d] ds' IHds'];
        intros cl.
      - (* ds = nil *)
        simpl. reflexivity.
      - (* ds = (nm, d) :: ds' *)
        simpl. apply IHds'.
    Qed.

    Lemma members_ok'_b_cons_true :
      forall (c : ctx) (decls : list (id * dt)) (cl : ctxloc)
             (nm : id) (d : dt),
        fst (members_ok'_b c cl ((nm, d) :: decls)) = true ->
        fst (members_ok'_b c (upd_ctxloc cl c nm d) decls) = true.
    Proof.
      intros c ds.
      unfold members_ok'_b. simpl.
      intros cl nm d H.
      assert (Hok : is_ok_b c cl d = true).
      { destruct (is_ok_b c cl d) eqn:Heq.
        reflexivity.
        destruct ds as [| elem ds'].
        + simpl in H. assumption.
        + rewrite (process_dep_member_b_preserves_false c _ _) in H.
          simpl in H. inversion H. }
      rewrite Hok in H. assumption.
    Qed.

    Lemma members_ok'_b_true__head_ok :
      forall (c : ctx) (decls : list (id * dt)) (cl : ctxloc)
             (nm : id) (d : dt),
        fst (members_ok'_b c cl ((nm, d) :: decls)) = true ->
        is_ok_b c cl d = true.
    Proof.
      intros c ds cl nm d H.
      unfold members_ok'_b in H. simpl in H.
      destruct (is_ok_b c cl d) eqn:Heq.
      reflexivity.
      rewrite (process_dep_member_b_preserves_false c _ _) in H.
      simpl in H. assumption.
    Qed. 

    Lemma members_ok'_b__sound :
      forall (c : ctx) (decls : list (id * dt)) (cl : ctxloc) (initP : Prop),
        initP ->
        fst (members_ok'_b c cl decls) = true ->
        fst (members_ok' c cl initP decls).
    Proof.
      intros c ds.
      induction ds as [| [nm t] ds' IHds'];
        intros cl P HP H.
      - simpl. assumption.
      - (* ds = (nm, t) :: ds' *)
        assert (H' := H).
        apply members_ok'_b_true__head_ok in H'.
        assert (H'' := H').
        apply TOkP.is_ok_b__sound in H''.
        unfold members_ok'. simpl.
        apply IHds'.
        tauto.
        unfold members_ok'_b in H. simpl in H.
        unfold members_ok'_b. rewrite H' in H. 
        assumption.
    Qed.

(* ----------------------------------------------------------------- *) 

    (** Completeness *)

    Lemma members_ok'__fst_prop :
      forall (c : ctx) (decls : list (id * dt)) (cl : ctxloc) (initP : Prop)
             (nm : id) (d : dt),
      exists Ps : Prop,
        (fst (members_ok' c cl initP ((nm, d) :: decls)) = Ps)
        /\ (Ps -> (is_ok c cl d) /\ initP).
    Proof.
      intros c ds.
      induction ds as [| [dnm dt] ds' IHds'];
        intros cl P nm t.
      - (* ds = nil *)
        unfold members_ok'. simpl. 
        exists (is_ok c cl t /\ P).
        tauto.
      - (* ds = (dnm, dt) :: ds' *)
        replace (fst (members_ok' c cl P ((nm, t) :: (dnm, dt) :: ds')))
        with (fst (members_ok' c (upd_ctxloc cl c nm t) 
                             (is_ok c cl t /\ P) ((dnm, dt) :: ds')))
          by (unfold members_ok'; reflexivity).
        remember (upd_ctxloc cl c nm t) as cl'.      
        specialize (IHds' cl' (is_ok c cl t /\ P) dnm dt).
        inversion IHds' as [Ps HPs].
        inversion HPs as [Heq Himp].
        exists Ps. split.
        assumption. tauto.
    Qed.

    Lemma members_ok'__head_ok :
      forall (c : ctx) (decls : list (id * dt)) (cl : ctxloc) (initP : Prop)
             (nm : id) (d : dt),
        initP ->
        fst (members_ok' c cl initP ((nm, d) :: decls)) ->
        (is_ok c cl d) /\ initP.
    Proof.
      intros c ds cl P nm t HP H.
      pose proof (members_ok'__fst_prop c ds cl P nm t) as Hex.
      inversion Hex as [Ps [Heq Himp]].
      rewrite Heq in H. apply Himp in H.
      assumption.
    Qed. 

    Lemma members_ok'_b__complete :
      forall (c : ctx) (decls : list (id * dt)) (cl : ctxloc) (initP : Prop),
        initP ->
        fst (members_ok' c cl initP decls) ->
        fst (members_ok'_b c cl decls) = true.
    Proof.
      intros c ds.
      induction ds as [| [nm t] ds' IHds'];
        intros cl P HP H.
      - simpl. reflexivity.
      - (* ds = (nm, t) :: ds' *)
        assert (H' := H).
        apply members_ok'__head_ok in H'.
        inversion H' as [Hok _].
        assert (Hok' := Hok). apply TOkP.is_ok_b__complete in Hok'.
        remember (upd_ctxloc cl c nm t) as cl'.
        replace (members_ok'_b c cl ((nm, t) :: ds'))
        with (members_ok'_b c cl' ds')
          by (unfold members_ok'_b; simpl; subst cl'; rewrite Hok'; reflexivity).
        apply IHds' with (initP := is_ok c cl t /\ P).
        assumption.
        unfold members_ok' in *. simpl in *.
        subst cl'. assumption. assumption.
    Qed.  

    Lemma members_ok_b__sound :
      forall (c : ctx) (decls : list (id * dt)),
      members_ok_b c decls = true ->
      members_ok c decls.
    Proof.
      intros c ds H.
      unfold members_ok_b in H.
      unfold members_ok.
      apply members_ok'_b__sound with (initP := True) in H.
      assumption. constructor.
    Qed.

    Lemma members_ok_b__complete :
      forall (c : ctx) (decls : list (id * dt)),
        members_ok c decls -> 
        members_ok_b c decls = true.
    Proof.
      intros c ds H.
      unfold members_ok in H.
      unfold members_ok_b.
      apply members_ok'_b__complete with (initP := True) in H.
      assumption. constructor.
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



