(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(* Transformation of
     List of Pairs (id, T) 
   into
     Maps from id to T (AVL-based)   
  
   Last Update: Fri, 28 Apr 2017
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 

Add LoadPath "../..".

Require Import ConceptParams.AuxTactics.LibTactics.
Require Import ConceptParams.AuxTactics.BasicTactics.

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Bool.Bool.

Require Import Coq.Structures.Equalities.
Require Import Coq.FSets.FMapAVL.
Require Import Coq.FSets.FMapFacts.


(* ***************************************************************** *)
(** * List-of-Pairs-to-Map 

      ([AVL-Map] based transformations of [List of Pair]) *)

(** Module with definitions and properties of functions
 ** that transform lists of pairs into maps.  
 ** *)
(* ***************************************************************** *)
(* ***************************************************************** *)

(* ################################################################# *)
(** ** Auxiliary Module Types for Ordering *)
(* ################################################################# *)

(** Original [OrderedType] Module (used in FSets)
 ** together with decidable usual equality. *)

Module Type UsualOrderedTypeOrig <: OrderedType <: UsualDecidableType.
  Include UsualDecidableType. 
  Parameter lt : t -> t -> Prop.
  Parameter eq_refl : forall x : t, eq x x.
  Parameter eq_sym : forall x y : t, eq x y -> eq y x.
  Parameter eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Parameter lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Parameter lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Parameter compare : forall x y : t, Compare lt eq x y.
End UsualOrderedTypeOrig.

(* ################################################################# *)
(** ** Module Type [ListPair2Map] *)
(* ################################################################# *)


(* ################################################################# *)
(** ** Module for [MListPair2MapAVL] *)
(* ################################################################# *)

Module MListPair2MapAVL
       (id_UOTOrig : UsualOrderedTypeOrig)
.

  (** Ordering of ids *)
  Module IdOT := id_UOTOrig.
  (** AVL Map of ids *)
  Module IdMap := FMapAVL.Make IdOT.

  (** Type of Identificators *)
  Definition id : Type := IdMap.key. (*IdOT.t.*)

  (** Type of Map-of-Identifiers *)
  Definition id_map := IdMap.t.

(* ================================================================= *)
(** *** Helper Functions *)
(* ================================================================= *)

  Import IdMap.
  Module HelperFuns.

    Definition map_from_list' {A : Type} (xs : list (id * A)) 
               (m : id_map A) : id_map A
      := fold_left
           (fun m xv => match xv with (x, v) => add x v m end)
           xs m.

  End HelperFuns.

(* ================================================================= *)
(** *** Main Functions *)
(* ================================================================= *)

  (** [map_from_list] builds a map [id -> A] from 
   ** the list of pairs [id * A]. *)
  Definition map_from_list {A : Type} (xs : list (id * A)) : id_map A
    := fold_left
         (fun m xv => match xv with (x, v) => add x v m end)
         xs (empty A).

  Definition get_ids {A : Type} (ps : list (id * A)) : list id 
      := List.map fst ps.

(* ================================================================= *)
(** *** Properties *)
(* ================================================================= *)

  Module Props.

    Import HelperFuns.

    Module IdMapFacts := FMapFacts.WFacts IdMap.
    Module IdMapProps := FMapFacts.WProperties IdMap.

    Import IdMapFacts.
    Import IdMapProps.
    

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
            destruct pnd as [x v]. destruct (IdOT.eq_dec nm x). subst.
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

      Lemma map_from_list__cons_new : 
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
          { apply add_m; tauto. }
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
          subst. apply add_mapsto_iff.
          right.
          pose proof (IdOT.eq_dec nm k) as Hid.
          inversion Hid. subst. simpl in *.
          assert (contra : k = k) by reflexivity.
          apply Hneq in contra.
          contradiction.
          split; auto.
          apply add_mapsto_iff.
          left. split; auto.
          apply add_mapsto_iff in H1; propositional.
          subst. apply add_mapsto_iff.
          left. split; reflexivity.
          apply add_mapsto_iff.
          right. split; auto.
          apply add_mapsto_iff.
          right. split; auto.
        + intros H1.
          apply add_mapsto_iff in H1; propositional.
          subst. apply add_mapsto_iff.
          right.
          pose proof (IdOT.eq_dec x k) as Hid.
          inversion Hid. subst. simpl in *.
          assert (contra : k = k) by reflexivity.
          apply Hneq in contra.
          contradiction.
          split; auto.
          apply add_mapsto_iff.
          left. split; auto.
          apply add_mapsto_iff in H1; propositional.
          subst. apply add_mapsto_iff.
          left. split; reflexivity.
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
          pose proof (in_dec IdOT.eq_dec nm (List.map fst pnds')) as Hindec.
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

      Lemma elem_in_map'__elem_in_list' :
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
          destruct (IdOT.eq_dec nm x).
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

      Lemma elem_in_map'__elem_in_list :
        forall (val : Type) (pnds : list (id * val)) 
               (nm : id) (tp : val),
          IdMap.MapsTo nm tp (map_from_list' pnds (empty val)) ->
          List.In nm (get_ids pnds).
      Proof.
        intros val pnds nm tp Hmaps.
        apply elem_in_map'__elem_in_list' with (tp := tp) (m := empty val).
        assumption.
        unfold not. 
        intros contra. rewrite empty_in_iff in contra.
        assumption.
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
          apply F.add_m; tauto.
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
          intros nm tp Hin. 
          reflexivity.
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
          + pose proof (IdOT.eq_dec nm f).
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

    Theorem map_from_list__find_cons___true : 
      forall (val : Type) (nm : id) (tp : val)                                  
             (pnds : list (id * val)),
        ~ List.In nm (get_ids pnds) ->
        find nm (map_from_list ((nm, tp) :: pnds)) = Some tp.
    Proof.
      intros val nm tp pnds. intros Hin.
      apply IdMap.find_1.
      apply Helper.map_from_list__cons_new. auto.
    Qed.

    Theorem elem_in_map__elem_in_list :
      forall (val : Type) (pnds : list (id * val)) 
             (nm : id) (tp : val),
        IdMap.MapsTo nm tp (map_from_list pnds) ->
        List.In nm (get_ids pnds).
    Proof.
      intros val pnds nm tp H.
      change (MapsTo nm tp (map_from_list' pnds (empty val))) in H.
      apply Helper.elem_in_map'__elem_in_list with (tp := tp). assumption.
    Qed.    

    Theorem map_from_list__length_cardinal_eq :
      forall (val : Type) (pnds : list (id * val)),
        NoDup (get_ids pnds) ->
        length pnds 
        = IdMap.cardinal (elt:=val) (map_from_list pnds).
    Proof.
      intros val pnds Hdup.
      induction pnds as [| pnd pnds' IHpnds']. 
      - (* nil *) reflexivity.
      - (* pnds = pnd :: pnds' *)
        destruct pnd as [nm tp]. simpl.
        rewrite Helper.map_from_list_cons_cardinal.
        apply f_equal.
        apply IHpnds'.
        inversion Hdup; tauto.
        inversion Hdup; tauto.
    Qed.

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
        unfold IdMap.Raw.Proofs.Empty in *.
        apply Hcard in Hmaps; contradiction.
      - (* pnds = pnd :: pnds' *)
        intros nm tp CT Htypes Hdup Hcard Hmaps.
        inversion Htypes; subst; simpl in *. clear Htypes.
        destruct pnd as [f T].
        simpl in Hdup. inversion Hdup. subst.
        assert (Hfind := Hmaps).
        rewrite (F.find_mapsto_iff CT nm tp) in Hfind.
        pose proof (IdOT.eq_dec f nm).
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
            inversion contra; tauto. }
          assert (Hcard' : IdMap.cardinal (elt:=val) CT 
                           = S (IdMap.cardinal (elt:=val) CT')).
          { apply cardinal_2 with (x := f) (e := T).
            assumption. unfold Add. subst.
            intros y. 
            pose proof (IdOT.eq_dec f y) as Hyf. inversion Hyf.
            subst.
            rewrite H1. 
            rewrite (F.add_eq_o _ _ (eq_refl y)). reflexivity.
            rewrite (F.add_neq_o _ _ H).
            symmetry. apply F.remove_neq_o. assumption. }
          rewrite <- Hcard in Hcard'.
          inversion Hcard'. reflexivity.
          subst. apply F.remove_neq_mapsto_iff. assumption. assumption.
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
      apply Helper.elem_in_map'__elem_in_list with (tp := tp).
      assumption. assumption.
    Qed.

  End Props.

End MListPair2MapAVL.

