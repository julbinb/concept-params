(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(* Transformation of
     List of Pairs (id, T) 
   into
     Maps from id to T (FMap interface)   
  
   Last Update: Wed, 14 June 2017
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 

Add LoadPath "../..".

Require Import ConceptParams.AuxTactics.LibTactics.
Require Import ConceptParams.AuxTactics.BasicTactics.

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Bool.Bool.

Require Import Coq.Structures.Equalities.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.FSets.FMapInterface.
Require Import Coq.FSets.FMapAVL.


(* ***************************************************************** *)
(** * List-of-Pairs-to-Map 

      ([FMap] based transformations of [List of Pair]) *)

(** Module with definitions and properties of functions
    that transform lists of pairs into maps.  
 *)
(* ***************************************************************** *)
(* ***************************************************************** *)

(* ################################################################# *)
(** ** Auxiliary Module Types for Ordering *)
(* ################################################################# *)

(** Original [DecidableType] Module (used in weak FMaps) 
 ** together with usual equality. *)

Module Type UsualDecidableTypeOrig <: UsualDecidableType.
  Include UsualDecidableType. 
  Parameter eq_refl : forall x : t, eq x x.
  Parameter eq_sym : forall x y : t, eq x y -> eq y x.
  Parameter eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
End UsualDecidableTypeOrig.

(** Original [OrderedType] Module (used in FMaps)
 ** together with decidable usual equality. *)

Module Type UsualOrderedTypeOrig 
<: OrderedType <: UsualDecidableType <: UsualDecidableTypeOrig.
  (*Include UsualDecidableType. *)
  Include UsualDecidableTypeOrig.
  Parameter lt : t -> t -> Prop.
  Parameter lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Parameter lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Parameter compare : forall x y : t, Compare lt eq x y.
End UsualOrderedTypeOrig.

(* ################################################################# *)
(** ** Module Type [ListPair2FMapW] *)
(* ################################################################# *)

(** [ListPair2FMapW] functor takes [id_UOT : UsualOrderedType] module, 
    a compatible [id_Map : FMapInterface.WS] module,
    which provides a finite map for type [id_UOT.t] of "identifiers". *)

Module Type ListPair2FMapW
       (id_UDTOrig : UsualDecidableTypeOrig)
       (id_Map : FMapInterface.WS 
           with Definition E.t := id_UDTOrig.t
           with Definition E.eq := id_UDTOrig.eq)
(* See some comments in [MListPair2FMapW]. *)
.

  (** Ordering of ids *)
  Module IdDT := id_UDTOrig.
  
  (** FMap of ids *)
  Module IdMap := id_Map.

  (** Type of Identificators *)
  Definition id : Type := IdMap.key. 

  (** Type of Map-of-Identifiers *)
  Definition id_map := IdMap.t.

(* ================================================================= *)
(** *** Main Functions *)
(* ================================================================= *)

  (** [map_from_list] builds a map [id -> A] from 
   ** the list of pairs [id * A]. *)
  Parameter map_from_list : forall {A : Type}, list (id * A) -> id_map A.
  
  Definition get_ids {A : Type} (xs : list (id * A)) : list id :=
    map fst xs.

(* ================================================================= *)
(** *** Main Definitions *)
(* ================================================================= *)

  Parameter eq_list_map : forall {A : Type}, 
      list (id * A) -> id_map A -> Prop.

(* ================================================================= *)
(** *** Properties *)
(* ================================================================= *)

  Module Props.

(* ----------------------------------------------------------------- *)
(** *** Props about List.In and IdMap.In  *)
(* ----------------------------------------------------------------- *)

    Axiom in_map_from_list__id_in_list :
      forall (val : Type) (pnds : list (id * val)) 
             (nm : id) (tp : val),
        IdMap.MapsTo nm tp (map_from_list pnds) ->
        List.In nm (get_ids pnds).

    Axiom in_map_from_list__in_list :
      forall (val : Type) (pnds : list (id * val)) 
             (nm : id) (tp : val),
        IdMap.MapsTo nm tp (map_from_list pnds) ->
        List.In (nm, tp) pnds.

    Axiom in_list_no_id_dup__in_map_from_list :
      forall (val : Type) (pnds : list (id * val)) 
             (nm : id) (tp : val),
        List.In (nm, tp) pnds ->
        NoDup (get_ids pnds) ->
        IdMap.MapsTo nm tp (map_from_list pnds).

    Axiom in_ids__in_map_from_list :
      forall (val : Type) (pnds : list (id * val)) (nm : id),
        List.In  nm (get_ids pnds) ->
        IdMap.In nm (map_from_list pnds).

    Axiom map_from_list__find_cons___true : 
      forall (val : Type) (nm : id) (tp : val)                                  
             (pnds : list (id * val)),
        ~ List.In nm (get_ids pnds) ->
        IdMap.find nm (map_from_list ((nm, tp) :: pnds)) = Some tp.

    Axiom map_from_list_cons__preserves_mapping : 
      forall (val : Type) (pnds : list (id * val))
             (nm nm': id) (tp tp': val),
      IdMap.MapsTo nm tp (map_from_list pnds) ->
      IdMap.MapsTo nm tp (map_from_list ((nm', tp') :: pnds)).

(* ----------------------------------------------------------------- *)
(** *** Props about Length and Cardinal  *)
(* ----------------------------------------------------------------- *)

    Axiom map_from_list__length_cardinal_eq :
      forall (val : Type) (pnds : list (id * val)),
        NoDup (get_ids pnds) ->
        length pnds 
        = IdMap.cardinal (elt:=val) (map_from_list pnds).

(* ----------------------------------------------------------------- *)
(** *** Equality of List and Map  *)
(* ----------------------------------------------------------------- *)

    Axiom elem_in_map_eq_length__elem_in_list :
      forall (val : Type) (pnds : list (id * val))
             (nm : id) (tp : val) (CT : id_map val),
        Forall
          (fun pnd : id * val =>
             match pnd with
             | (f, T) => IdMap.find f CT = Some T
             end) 
          pnds ->
        NoDup (get_ids pnds) ->
        length pnds = IdMap.cardinal (elt:=val) CT ->
        IdMap.MapsTo nm tp CT ->
        List.In (nm, tp) pnds.    

    Axiom eq_list_map__same_list__eq_maps :
      forall (val : Type) (ps : list (id * val)) (mp1 mp2 : id_map val),
        eq_list_map ps mp1 ->
        eq_list_map ps mp2 ->
        IdMap.Equal mp1 mp2.

    Axiom eq_list_map_from_list : 
      forall (val : Type) (ps : list (id * val)),
        List.NoDup (get_ids ps) ->
        eq_list_map ps (map_from_list ps).

    Axiom eq_list_map__iff :
      forall (val : Type) (ps : list (id * val)) (mp : id_map val),
        eq_list_map ps mp ->
        forall x v,
          List.In (x, v) ps <-> IdMap.MapsTo x v mp.

  End Props.

End ListPair2FMapW.

(* ################################################################# *)
(** ** Module [MListPair2FMapW] (weak interface of [FMap]) *)
(** Transformation of list of pairs into 
 ** a weak FMap and its properties. *)
(* ################################################################# *)

Module MListPair2FMapW
       (id_UDTOrig : UsualDecidableTypeOrig)
       (id_Map : FMapInterface.WS 
           with Definition E.t := id_UDTOrig.t
           with Definition E.eq := id_UDTOrig.eq)
<: ListPair2FMapW id_UDTOrig id_Map

(* More concrete version below does not work, as, for example, 
 * FMapAVL.Make removes information about [eq_equiv] 
 * due to opaque typing. *)

(*       (id_Map : FMapInterface.WS with Module E := id_UDTOrig) *)
.

  (** Ordering of ids *)
  Module IdDT := id_UDTOrig.
  
  (** FMap of ids *)
  Module IdMap := id_Map.

  (** Type of Identificators *)
  Definition id : Type := IdMap.key. (*IdDT.t.*)

  (** Type of Map-of-Identifiers *)
  Definition id_map := IdMap.t.

(* ----------------------------------------------------------------- *)
(** *** Helper Functions *)
(* ----------------------------------------------------------------- *)

  Import IdMap.
  Module HelperFuns.

    Definition map_from_list' {A : Type} (xs : list (id * A)) 
               (m : id_map A) : id_map A
      := fold_left
           (fun m xv => match xv with (x, v) => add x v m end)
           xs m.
    Hint Unfold map_from_list'.

  End HelperFuns.

(* ================================================================= *)
(** *** Main Functions *)
(* ================================================================= *)

  (** [map_from_list] builds a map [id -> A] from 
   ** the list of pairs [id * A]. *)
  Definition map_from_list {A : Type} (xs : list (id * A)) : id_map A
    := HelperFuns.map_from_list' xs (empty A).
  Hint Unfold map_from_list.

  Definition get_ids {A : Type} (ps : list (id * A)) : list id 
      := List.map fst ps.

(* ================================================================= *)
(** *** Main Definitions *)
(* ================================================================= *)

  Definition eq_list_map {A : Type} (xs : list (id * A)) 
             (mp : id_map A) : Prop :=
    (* All ids are unique *)
    List.NoDup (get_ids xs)
    (* Length is the same *)
    /\ List.length xs = IdMap.cardinal mp
    (* Elements are the same *)
    /\ List.Forall 
         (fun p => match p with (nm, v) =>
                     IdMap.find nm mp = Some v
                   end) 
         xs.
  Hint Unfold eq_list_map.

(* ================================================================= *)
(** *** Properties *)
(* ================================================================= *)

  Module Props.

    Import HelperFuns.

    Module IdMapFacts := FMapFacts.WFacts IdMap.
    Module IdMapProps := FMapFacts.WProperties IdMap.

    Import IdMapFacts.
    Import IdMapProps.
    
(* ----------------------------------------------------------------- *)
(** *** Helper Properties *)
(* ----------------------------------------------------------------- *)

    Module Helper.

      Lemma map_from_list'_not_in__preserves_mapping : 
        forall (val : Type) (pnds : list (id * val)) 
               (nm : id) (tp : val) (m : id_map val),  
          IdMap.MapsTo nm tp m ->
          ~ List.In nm (get_ids pnds) ->
          IdMap.MapsTo nm tp (map_from_list' pnds m).
      Proof.
        intros val pnds. induction pnds as [| pnd pnds' IHpnds'].
        - (* pnds = nil *)
          intros nm tp m Hmaps Hnin. simpl. assumption. 
        - (* pnds = pnd :: pnds' *)
          intros nm tp m Hmaps Hin.
          unfold map_from_list' in *. simpl. simpl in IHpnds'.
          apply IHpnds'.
          + (* IdMap.MapsTo nm tp (m += pnd) *)    
            destruct pnd as [x v]. destruct (IdDT.eq_dec nm x). subst.
            assert (contra: List.In x (List.map fst ((x, v) :: pnds'))) 
              by (simpl; left; reflexivity).
            apply Hin in contra. contradiction.
            apply IdMap.add_2. intros H. symmetry in H. apply n in H. 
            contradiction.
            assumption.
          + (* ~ List.In nm (map fst pnds') *)
            intros H. 
            assert (contra: List.In nm (List.map fst (pnd :: pnds')))
              by (simpl; right; assumption).
            apply Hin in contra. contradiction.
      Qed.

      Lemma map_from_list'__cons_new : 
        forall (val : Type) (pnds : list (id * val)) 
               (nm : id) (tp : val) (m : id_map val),  
          ~ List.In nm (get_ids pnds) ->
          IdMap.MapsTo nm tp (map_from_list' ((nm, tp) :: pnds) m).
      Proof. 
        intros pnds nm tp m. intros Hin.
        simpl. apply map_from_list'_not_in__preserves_mapping.
        apply IdMap.add_1. reflexivity.
      Qed.

      Lemma map_from_list'__ignore_list :
        forall (val : Type) (pnds : list (id * val)) 
               (nm : id) (tp : val) (m : id_map val),  
          ~ List.In nm (get_ids pnds) ->
          IdMap.MapsTo nm tp (map_from_list' pnds m) ->
          IdMap.MapsTo nm tp m.
      Proof.
        intros val pnds. induction pnds as [|pnd pnds' IHpnds'].
        - intros. simpl in *. assumption.
        - intros nm tp m Hin Hmaps.
          destruct pnd as [x v]. simpl in *. 
          assert (Hin' : ~ List.In nm (List.map fst pnds')).
          { unfold not in *. intros contra.
            apply Hin. tauto. }  
          specialize (IHpnds' nm tp (add x v m) Hin' Hmaps).
          apply add_mapsto_iff in IHpnds'.
          inversion IHpnds'.
          tauto.
          tauto.
      Qed.

      Lemma map_from_list'__eq_maps : 
        forall (val : Type) (pnds : list (id * val)) 
               (nm : id) (tp : val) (m m': id_map val), 
          IdMap.Equal m' m ->
          IdMap.MapsTo nm tp (map_from_list' pnds m)
          -> 
          IdMap.MapsTo nm tp (map_from_list' pnds m').
      Proof.
        intros val pnds. induction pnds as [|pnd pnds' IHpnds'].
        - (* pnds = nil *)
          intros nm tp m m' Heq Hmaps. 
          simpl in *. 
          eapply Equal_mapsto_iff; eauto.
        - (* pnds = pnd :: pnds' *)
          intros nm tp m m' Heq Hmaps.
          destruct pnd as [x v]; simpl in *.
          eapply IHpnds'.
          assert (H : IdMap.Equal (add x v m') (add x v m)).
          { apply add_m. apply id_UDTOrig.eq_refl. 
            reflexivity. assumption. }
          eassumption.
          assumption.
      Qed.
      
      Lemma permute_add__eq_maps :
        forall (val : Type)
               (nm x : id) (tp v : val) (m : id_map val), 
          x <> nm ->
          IdMap.Equal (add x v (add nm tp m))
                      (add nm tp (add x v m)).
      Proof.
        intros val nm x tp v m Hneq.
        apply Equal_mapsto_iff.
        intros k e. split.
        + intros H1.
          apply add_mapsto_iff in H1; propositional.
          unfold id_UDTOrig.eq in *; subst.
          subst. apply add_mapsto_iff.
          right.
          pose proof (IdDT.eq_dec nm k) as Hid.
          inversion Hid. subst. simpl in *.
          assert (contra : k = k) by reflexivity.
          apply Hneq in contra.
          contradiction.
          split; auto.
          apply add_mapsto_iff.
          left. split; auto.
          unfold id_UDTOrig.eq in *; subst. reflexivity.
          apply add_mapsto_iff in H1; propositional.
          subst. apply add_mapsto_iff.
          left. unfold id_UDTOrig.eq in *; subst.
          split; reflexivity.
          apply add_mapsto_iff.
          right. split; auto.
          apply add_mapsto_iff.
          right. split; auto.
        + intros H1.
          apply add_mapsto_iff in H1; propositional;
            unfold id_UDTOrig.eq in *; subst.
          apply add_mapsto_iff.
          right.
          pose proof (IdDT.eq_dec x k) as Hid.
          inversion Hid; unfold id_UDTOrig.eq in *; subst.
          simpl in *.
          assert (contra : k = k) by reflexivity.
          apply Hneq in contra.
          contradiction.
          split; auto.
          apply add_mapsto_iff.
          left. split; auto.
          unfold id_UDTOrig.eq in *; subst. reflexivity.
          apply add_mapsto_iff in H1; propositional.
          subst. apply add_mapsto_iff.
          left. unfold id_UDTOrig.eq in *; subst.
          split; reflexivity.
          apply add_mapsto_iff.
          right. split; auto.
          apply add_mapsto_iff.
          right. split; auto.
      Qed.

      Lemma map_from_list'__ignore_list_add :
        forall (val : Type) (pnds : list (id * val)) 
               (nm : id) (tp : val) (m : id_map val),  
          ~ List.In nm (get_ids pnds) ->
          IdMap.MapsTo nm tp (map_from_list' pnds (add nm tp m)).
      Proof.
        intros val pnds. induction pnds as [|pnd pnds' IHpnds'].
        - intros. simpl.
          apply IdMap.add_1. reflexivity.
        - intros nm tp m H.
          destruct pnd as [x v]. simpl. 
          apply map_from_list'__eq_maps with
          (m := (add nm tp (add x v m))).
          apply permute_add__eq_maps.
          simpl in H. unfold not. intros contra.
          eapply or_introl in contra.
          apply H in contra. contradiction.
          apply IHpnds'.
          unfold not in *. intros contra.
          assert (H1 : List.In nm (List.map fst ((x, v) :: pnds')))
            by (simpl; right;  assumption).
          tauto.
      Qed.

      Lemma map_from_list'__any_map : 
        forall (val : Type) (pnds : list (id * val)) 
               (nm : id) (tp : val) (m m' : id_map val),  
          List.In nm (get_ids pnds) ->
          IdMap.MapsTo nm tp (map_from_list' pnds m) ->
          IdMap.MapsTo nm tp (map_from_list' pnds m').
      Proof.
        intros val pnds. induction pnds as [|pnd pnds' IHpnds'].
        - (* pnds = nil *)
          intros nm tp m m' Hin (* Hdup *) Hmaps. 
          simpl in Hin. contradiction.
        - (* pnds = pnd :: pnds' *)
          intros nm tp m m' Hin (* Hdup *) Hmaps.
          simpl. simpl in Hmaps.
          destruct pnd as [x v].       
          pose proof (in_dec IdDT.eq_dec nm (List.map fst pnds')) as Hindec.
          inversion Hindec as [Hinnm | Hinnm].
          + eapply IHpnds'.
            assumption.
            eassumption.
          + simpl in Hin. inversion Hin.
            { subst.
              pose proof (map_from_list'__ignore_list val
                          pnds' nm tp (add nm v m) Hinnm Hmaps) as Hnm.
              apply add_mapsto_iff in Hnm; propositional.
              subst.
              apply map_from_list'__ignore_list_add.
              assumption. } 
            tauto.
      Qed.      

      Lemma pair_in_map_from_list'__id_in_list' :
        forall (val : Type) (pnds : list (id * val)) 
               (nm : id) (tp : val) (m : id_map val),
          IdMap.MapsTo nm tp (map_from_list' pnds m) ->
          ~ (IdMap.In nm m) ->
          List.In nm (get_ids pnds).
      Proof.
        intros val pnds. 
        induction pnds as [| pnd pnds' IHpnds'].
        - intros. simpl in H. 
          apply IdMap.find_1 in H.
          assert (Hfind : IdMap.find (elt:=val) nm m <> None).
          equality.    
          rewrite <- in_find_iff in Hfind.
          apply H0 in Hfind. contradiction.
        - intros. destruct pnd as [x v].
          simpl in *.
          destruct (IdDT.eq_dec nm x).
          + equality.
          + right.
            apply IHpnds' with (tp := tp) (m := (add x v m)).
            assumption.
            unfold "~". intro Hin.     
            rewrite add_in_iff in Hin.
            inversion Hin. equality.
            apply H0 in H1.
            assumption.
      Qed.

      Lemma pair_in_map_from_list'__in_list_or_map :
        forall (val : Type) (pnds : list (id * val)) 
               (nm : id) (tp : val) (m : id_map val),
          IdMap.MapsTo nm tp (map_from_list' pnds m) ->
          IdMap.MapsTo nm tp m \/ List.In (nm, tp) pnds.
      Proof.
        intros val pnds.
        induction pnds as [| pnd pnds' IHpnds'].
        - (* pnds = nil *)
          intros. simpl in *. tauto.
        - (* pnds = pnd :: pnds' *)
          intros. simpl in *.
          destruct pnd as [x v].
          apply IHpnds' in H.
          destruct H as [Hmap | Hlist].
          + rewrite add_mapsto_iff in Hmap. 
            propositional.
            unfold id_UDTOrig.eq in *; subst. tauto.
          + tauto.
      Qed.

      Lemma pair_in_map_from_list'__pair_in_list :
        forall (val : Type) (pnds : list (id * val)) 
               (nm : id) (tp : val) (m : id_map val),
          IdMap.MapsTo nm tp (map_from_list' pnds m) ->
          ~ (IdMap.In nm m) ->
          List.In (nm, tp) pnds.
      Proof.
        intros val pnds nm tp m Hmaps Hin.
        apply pair_in_map_from_list'__in_list_or_map in Hmaps.
        destruct Hmaps as [Hmap | Hlist].
        - apply find_1 in Hmap.
          rewrite not_find_in_iff in Hin. 
          rewrite Hmap in Hin; inversion Hin.
        - assumption.
      Qed.

      Lemma pair_in_map_from_list'__id_in_list :
        forall (val : Type) (pnds : list (id * val)) 
               (nm : id) (tp : val),
          IdMap.MapsTo nm tp (map_from_list' pnds (empty val)) ->
          List.In nm (get_ids pnds).
      Proof.
        intros val pnds nm tp Hmaps.
        apply pair_in_map_from_list'__id_in_list' with (tp := tp) (m := empty val).
        assumption.
        unfold not. 
        intros contra. rewrite empty_in_iff in contra.
        assumption.
      Qed.

      Lemma in_list_no_id_dup__in_map_from_list' :
        forall (val : Type) (pnds : list (id * val)) 
               (nm : id) (tp : val) (m : id_map val),
          List.In (nm, tp) pnds ->
          NoDup (get_ids pnds) ->
          IdMap.MapsTo nm tp (map_from_list' pnds m).
      Proof.
        intros val pnds. 
        induction pnds as [|pnd pnds' IHpnds']; 
          intros; simpl in *.
        - (* pnds = nil *) contradiction.
        - (* pnds = pnd :: pnds' *)
          destruct pnd as [x v].
          destruct H as [Heq | Hin].
          + inversion Heq; subst.
            inversion H0; subst.
            apply map_from_list'__ignore_list_add. assumption.
          + apply IHpnds'. assumption.
            inversion H0. assumption.
      Qed.
  
      Lemma map_from_list'_preserves_eq :
        forall (val : Type) (pnds : list (id * val)) 
               (m m' : id_map val),
          IdMap.Equal m m' ->
          IdMap.Equal (map_from_list' pnds m) (map_from_list' pnds m').
      Proof.
        intros val pnds. induction pnds as [|pnd pnds' IHpnds'].
        - (* pnds = nil *)
          intros m m' Heq. simpl.
          assumption.
        - (* pnds = pnd :: pnds' *)
          intros m m' Heq. destruct pnd as [x v].
          simpl.
          apply IHpnds'.
          apply F.add_m; unfold id_UDTOrig.eq in *; subst; tauto.
      Qed.
    
      Lemma map_from_list_cons_cardinal' :
        forall (val : Type) (pnds : list (id * val)) 
               (nm : id) (tp : val) (m : id_map val),
          ~ List.In nm (get_ids pnds) ->
          ~ IdMap.In nm m ->
          IdMap.cardinal (elt:=val) (map_from_list' ((nm, tp) :: pnds) m)
          = S (IdMap.cardinal (elt:=val) (map_from_list' pnds m)).
      Proof.
        intros val pnds. induction pnds as [|pnd pnds' IHpnds'].
        - (* pnds = nil *)
          intros nm tp m Hin Hmap. simpl.
          rewrite <- cardinal_2 with (m' := (add nm tp m))
                                       (x := nm) (e := tp).
          reflexivity.
          assumption.
          unfold Add. intros y.
          reflexivity.
        - (* pnds = pnd :: pnds' *)
          intros nm tp m Hin Hmap. destruct pnd as [x v].
          simpl in *.
          assert (Heq : IdMap.Equal 
                          (map_from_list' pnds' (add x v (add nm tp m)))
                          (map_from_list' pnds' (add nm tp (add x v m)))).
          { apply map_from_list'_preserves_eq.
            apply permute_add__eq_maps.
            tauto. }
          rewrite Heq.
          apply IHpnds'.
          tauto. 
          unfold not. intros contra.
          rewrite F.add_in_iff in contra.
          inversion contra; tauto.
      Qed.

      Lemma map_from_list_cons_cardinal :
        forall (val : Type) (pnds : list (id * val)) 
               (nm : id) (tp : val),
          ~ List.In nm (get_ids pnds) ->
          IdMap.cardinal (elt:=val) (map_from_list ((nm, tp) :: pnds))
          = S (IdMap.cardinal (elt:=val) (map_from_list pnds)).
      Proof.
        intros val pnds. induction pnds as [|pnd pnds' IHpnds'].
        - (* pnds = nil *)
          intros nm tp Hin. unfold map_from_list. simpl.
          pose proof (@empty_1 val) as Hem.
          apply cardinal_Empty in Hem. 
          assert (Hadd : cardinal (add nm tp (empty val)) 
                         = S (cardinal (empty val))).
          { apply cardinal_2 with (x := nm) (e := tp).
            intros contra. rewrite F.empty_in_iff in contra.
            contradiction.
            unfold Add. intros y. reflexivity. }
          rewrite Hadd. rewrite Hem. reflexivity.
        - (* pnds = pnd :: pnds' *)
          intros nm tp Hin. destruct pnd as [x v].
          assert 
            (Heq : IdMap.cardinal (elt:=val) 
                   (map_from_list ((nm, tp) :: (x, v) :: pnds'))
                   = S (IdMap.cardinal (elt:=val) (map_from_list ((x, v) :: pnds')))).
          { change (IdMap.cardinal (elt:=val) 
                    (map_from_list' ((nm, tp) :: (x, v) :: pnds') (empty val)) 
                    =
                    S (IdMap.cardinal (elt:=val) 
                       (map_from_list' ((x, v) :: pnds') (empty val)))).
            apply map_from_list_cons_cardinal'.
            assumption.
            unfold not. intros contra.
            rewrite F.empty_in_iff in contra. 
            tauto. }
          rewrite Heq.
          unfold map_from_list in *. reflexivity.
      Qed.

      Lemma list_elems_in_map__remove_unused :
        forall (val : Type) (pnds : list (id * val))
               (f : id) (CT CT' : id_map val),
          Forall
            (fun pnd : id * val =>
               match pnd with
               | (f, T) => find f CT = Some T
               end) pnds ->
          ~ List.In f (get_ids pnds) ->
          CT' = IdMap.remove (elt:=val) f CT ->
          Forall
            (fun pnd : id * val =>
               match pnd with
               | (f0, T0) => find f0 CT' = Some T0
               end) pnds.
      Proof.
        intros val pnds. induction pnds as [| pnd pnds' IHpnds' ].
        - (* pnds = nil *)
          intros f CT CT' Htypes Hin Heq.
          constructor.
        - (* pnds = pnd :: pnds' *)
          intros f CT CT' Htypes Hin Heq.
          destruct pnd as [nm tp]. simpl in *.
          inversion Htypes; clear Htypes; subst.
          apply Forall_cons.
          + pose proof (IdDT.eq_dec nm f).
            inversion H.
            { eapply or_introl in H0.
              eapply Hin in H0. contradiction. }
            clear H.
            apply F.find_mapsto_iff.
            apply F.remove_mapsto_iff.
            split. equality.
            apply F.find_mapsto_iff. assumption.
          + apply IHpnds' with (f := f) (CT := CT).
            assumption.
            unfold not. intros contra.
            eapply or_intror in contra.
            apply Hin in contra. contradiction.
            reflexivity.
      Qed.

    End Helper.

(* ================================================================= *)
(** *** Main Properties *)
(* ================================================================= *)

    Theorem map_from_list_nil__cardinal :
      forall (val : Type),
      IdMap.cardinal (@map_from_list val []) = 0.
    Proof.
      intros. unfold map_from_list; simpl.
      apply cardinal_1. apply empty_1.
    Qed.

(* ----------------------------------------------------------------- *)
(** *** Props about List.In and IdMap.In  *)
(* ----------------------------------------------------------------- *)

    Theorem in_map_from_list__id_in_list :
      forall (val : Type) (pnds : list (id * val)) 
             (nm : id) (tp : val),
        IdMap.MapsTo nm tp (map_from_list pnds) ->
        List.In nm (get_ids pnds).
    Proof.
      intros val pnds nm tp H.
      change (MapsTo nm tp (map_from_list' pnds (empty val))) in H.
      apply Helper.pair_in_map_from_list'__id_in_list with (tp := tp). 
      assumption.
    Qed.    

    Theorem in_map_from_list__in_list :
      forall (val : Type) (pnds : list (id * val)) 
             (nm : id) (tp : val),
        IdMap.MapsTo nm tp (map_from_list pnds) ->
        List.In (nm, tp) pnds.
    Proof.
      intros val pnds nm tp H.
      change (MapsTo nm tp (map_from_list' pnds (empty val))) in H.
      apply Helper.pair_in_map_from_list'__pair_in_list 
        with (m := empty val). assumption.
      intros contra. rewrite empty_in_iff in contra. 
      contradiction.
    Qed. 

    Theorem in_list_no_id_dup__in_map_from_list :
      forall (val : Type) (pnds : list (id * val)) 
             (nm : id) (tp : val),
        List.In (nm, tp) pnds ->
        NoDup (get_ids pnds) ->
        IdMap.MapsTo nm tp (map_from_list pnds).
    Proof.
      intros. 
      apply Helper.in_list_no_id_dup__in_map_from_list'; assumption.
    Qed.


    Theorem in_ids__in_map_from_list :
      forall (val : Type) (pnds : list (id * val)) (nm : id),
        List.In  nm (get_ids pnds) ->
        IdMap.In nm (map_from_list pnds).
    Proof.
      intros val pnds.
      induction pnds as [| [n' d'] pnds' IHpnds'].
      - intros. inversion H.
      - intros nm Hnmin.
        simpl in Hnmin. destruct Hnmin as [Hnmin | Hnmin].
        + subst. remember (get_ids pnds') as ids.
          assert (Hdec : {List.In nm ids} + {~ List.In nm ids}).
          { apply List.in_dec. apply IdDT.eq_dec. }
          destruct Hdec as [Hdec | Hdec].
          * specialize (IHpnds' nm Hdec).
            unfold map_from_list. simpl.
            unfold map_from_list in IHpnds'.
            unfold In in *.
            destruct IHpnds' as [v Hmaps].
            exists v.
            apply Helper.map_from_list'__any_map with (empty val).
            subst ids. assumption. assumption.
          * unfold map_from_list.
            unfold In. exists d'.
            apply Helper.map_from_list'__cons_new. subst ids. assumption.
        + specialize (IHpnds' nm Hnmin).
          unfold map_from_list. simpl.
          unfold map_from_list in IHpnds'.
          unfold In in *.
          destruct IHpnds' as [v Hmaps].
          exists v.
          apply Helper.map_from_list'__any_map with (empty val).
          assumption. assumption.
    Qed.


    Theorem map_from_list__find_cons___true : 
      forall (val : Type) (nm : id) (tp : val)                                  
             (pnds : list (id * val)),
        ~ List.In nm (get_ids pnds) ->
        find nm (map_from_list ((nm, tp) :: pnds)) = Some tp.
    Proof.
      intros val nm tp pnds. intros Hin.
      apply IdMap.find_1.
      apply Helper.map_from_list'__cons_new. auto.
    Qed.

    Theorem map_from_list_cons__preserves_mapping : 
      forall (val : Type) (pnds : list (id * val))
             (nm nm': id) (tp tp': val),
      IdMap.MapsTo nm tp (map_from_list pnds) ->
      IdMap.MapsTo nm tp (map_from_list ((nm', tp') :: pnds)).
    Proof.
      intros val pnds nm nm' tp tp' H.
      change (IdMap.MapsTo nm tp 
             (map_from_list' ((nm', tp') :: pnds) (IdMap.empty val))).
      change (IdMap.MapsTo nm tp 
             (map_from_list' pnds (IdMap.empty val))) in H.
      simpl.
      apply Helper.map_from_list'__any_map with (m := IdMap.empty val). 
      apply Helper.pair_in_map_from_list'__id_in_list with (tp := tp).
      assumption. assumption.
    Qed.

(* ----------------------------------------------------------------- *)
(** *** Props about Length and Cardinal  *)
(* ----------------------------------------------------------------- *)

    Theorem map_from_list__length_cardinal_eq :
      forall (val : Type) (pnds : list (id * val)),
        NoDup (get_ids pnds) ->
        length pnds 
        = IdMap.cardinal (elt:=val) (map_from_list pnds).
    Proof.
      intros val pnds Hdup.
      induction pnds as [| pnd pnds' IHpnds']. 
      - (* nil *) 
        unfold map_from_list; simpl.
        symmetry. apply cardinal_1. apply empty_1.
      - (* pnds = pnd :: pnds' *)
        destruct pnd as [nm tp]. simpl.
        rewrite Helper.map_from_list_cons_cardinal.
        apply f_equal.
        apply IHpnds'.
        inversion Hdup; tauto.
        inversion Hdup; tauto.
    Qed.

(* ----------------------------------------------------------------- *)
(** *** Equality of List and Map  *)
(* ----------------------------------------------------------------- *)

    Theorem elem_in_map_eq_length__elem_in_list :
      forall (val : Type) (pnds : list (id * val))
             (nm : id) (tp : val) (CT : id_map val),
        Forall
          (fun pnd : id * val =>
             match pnd with
             | (f, T) => find f CT = Some T
             end) 
          pnds ->
        NoDup (get_ids pnds) ->
        length pnds = IdMap.cardinal (elt:=val) CT ->
        IdMap.MapsTo nm tp CT ->
        List.In (nm, tp) pnds.    
    Proof.
      intros val pnds. induction pnds as [| pnd pnds' IHpnds' ].
      - (* npds = nil *)
        intros nm tp CT Htypes Hdup Hcard Hmaps. simpl in *.
        symmetry in Hcard. apply cardinal_Empty in Hcard. 
        unfold IdMap.Empty in *.
        apply Hcard in Hmaps; contradiction.
      - (* pnds = pnd :: pnds' *)
        intros nm tp CT Htypes Hdup Hcard Hmaps.
        inversion Htypes; subst; simpl in *. clear Htypes.
        destruct pnd as [f T].
        simpl in Hdup. inversion Hdup. subst.
        assert (Hfind := Hmaps).
        rewrite (F.find_mapsto_iff CT nm tp) in Hfind.
        pose proof (IdDT.eq_dec f nm).
        inversion H; clear H.
        + subst.
          rewrite -> H1 in Hfind. inversion Hfind.
          left; trivial.
        + right.
          (* To apply IH, we need smaller map *)
          remember (IdMap.remove f CT) as CT'.
          apply IHpnds' with (CT := CT').
          subst CT'.
          apply Helper.list_elems_in_map__remove_unused 
          with (f := f) (CT := CT); trivial.
          assumption.
          assert (Hnotin : ~ IdMap.In f CT').
          { subst. intros contra.
            apply F.remove_in_iff in contra.
            inversion contra; unfold id_UDTOrig.eq in *; subst; tauto. }
          assert (Hcard' : IdMap.cardinal (elt:=val) CT 
                           = S (IdMap.cardinal (elt:=val) CT')).
          { apply cardinal_2 with (x := f) (e := T).
            assumption. unfold Add. subst.
            intros y. 
            pose proof (IdDT.eq_dec f y) as Hyf. inversion Hyf.
            subst.
            rewrite H1. 
            rewrite (F.add_eq_o _ _ (eq_refl y)). reflexivity.
            rewrite (F.add_neq_o _ _ H).
            symmetry. apply F.remove_neq_o. assumption. }
          rewrite <- Hcard in Hcard'.
          inversion Hcard'. reflexivity.
          subst. apply F.remove_neq_mapsto_iff. assumption. assumption.
    Qed. 

    Theorem eq_list_map__same_list__eq_maps :
      forall (val : Type) (ps : list (id * val)) (mp1 mp2 : id_map val),
        eq_list_map ps mp1 ->
        eq_list_map ps mp2 ->
        IdMap.Equal mp1 mp2.
    Proof.
      intros val ps mp1 mp2. 
      unfold eq_list_map.
      intros [Hdup [Hlen1 Hfind1]] [_ [Hlen2 Hfind2]].
      apply Equal_mapsto_iff.
      intros k v. split; intros Hmaps.
      - (* 1 -> 2 *)
        pose proof (elem_in_map_eq_length__elem_in_list
                      val ps k v mp1 Hfind1 Hdup Hlen1 Hmaps) as Hin.
        assert (Hmp2 := Hfind2).
        rewrite Forall_forall in Hmp2.
        specialize (Hmp2 (k, v) Hin). simpl in Hmp2.
        apply IdMapProps.F.find_mapsto_iff.
        assumption.
      - (* 2 -> 1 *)
        pose proof (elem_in_map_eq_length__elem_in_list
                      val ps k v mp2 Hfind2 Hdup Hlen2 Hmaps) as Hin.
        assert (Hmp1 := Hfind1).
        rewrite Forall_forall in Hmp1.
        specialize (Hmp1 (k, v) Hin). simpl in Hmp1.
        apply IdMapProps.F.find_mapsto_iff.
        assumption.
    Qed.

    Theorem eq_list_map_from_list : 
      forall (val : Type) (ps : list (id * val)),
        List.NoDup (get_ids ps) ->
        eq_list_map ps (map_from_list ps).
    Proof.
      intros val ps.
      induction ps as [| p ps' IHps']; 
        unfold eq_list_map;
        intros Hdup.
      - (* ps = nil *)
        propositional; simplify.
        symmetry. apply map_from_list_nil__cardinal.
        constructor.
      - (* ps = p :: ps' *)
        propositional; destruct p as [nm v];
        inversion Hdup; subst;
        specialize (IHps' H2); unfold eq_list_map in IHps'.
        + simpl in *.
          pose proof (Helper.map_from_list_cons_cardinal val ps' nm v H1) 
            as Hcard.
          rewrite Hcard. apply f_equal.
          propositional.
        + inversion Hdup; subst. 
          constructor.  
          * apply map_from_list__find_cons___true.
            assumption.
          * propositional.
            apply Forall_impl with
            (P := fun p : key * val =>
                  let (nm, v) := p in find nm (map_from_list ps') = Some v).
            (* cons *)
            intros [nm' v'] Hfind.
            apply IdMap.find_2 in Hfind.
            apply IdMap.find_1. 
            apply map_from_list_cons__preserves_mapping. assumption.
            (* rec case *)
            assumption.
    Qed.

    Theorem eq_list_map__iff :
      forall (val : Type) (ps : list (id * val)) (mp : id_map val),
        eq_list_map ps mp ->
        forall x v,
          List.In (x, v) ps <-> IdMap.MapsTo x v mp.
      Proof.
        intros val ps mp Heq.
        unfold eq_list_map in Heq.
        destruct Heq as [Hnodup [Hlen Hforall]].
        intros x v. 
        split.
        - (* List.In -> MapsTo *) 
          rewrite Forall_forall in Hforall.
          specialize (Hforall (x, v)).
          intros Hin. specialize (Hforall Hin).
          simpl in Hforall. apply F.find_mapsto_iff. assumption.
        - (* MapsTo *)
          intros Hmaps.
          apply elem_in_map_eq_length__elem_in_list with mp;
            try assumption.
      Qed.

  End Props.

End MListPair2FMapW.

(* ################################################################# *)
(** ** Module for [MListPair2MapAVL] *)
(* ################################################################# *)

Module MListPair2FMapAVL (id_UOTOrig : UsualOrderedTypeOrig).
  Module IdMapAVL := FMapAVL.Make id_UOTOrig.
  Module M := MListPair2FMapW id_UOTOrig IdMapAVL.
End MListPair2FMapAVL.
