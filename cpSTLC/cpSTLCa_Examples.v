(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(* Simply Typed Lambda Calculus with simple Concept Parameters
   :: version a
  
   Last Update: Wed, 18 Jan 2017
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 


(* ***************************************************************** *)
(** * cpSTLCa Tests and Examples

    (Simply Typed Lambda Calculus with simple Concept Parameters  
     :: version a) *)
(* ***************************************************************** *)
(* ***************************************************************** *)

Add LoadPath "../..".

Require Import ConceptParams.BasicPLDefs.Maps.
Require Import ConceptParams.BasicPLDefs.Relations.

Require Import ConceptParams.AuxTactics.LibTactics.
Require Import ConceptParams.AuxTactics.BasicTactics.

Require Import ConceptParams.cpSTLC.cpSTLCa_Defs.

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Bool.Bool.

Require Import Coq.omega.Omega.


(* ################################################################# *)
(** ** Syntax *)

(* ================================================================= *)
(** *** Examples *)

(** Let's define some examples so that we can check them later *)

Module Examples.

  (** Concept names *)
  
  Definition CNnrevmap := Id 1.
  Definition CNnmonoid := Id 2.
  Definition CNnfoo := Id 3.
  Definition CNbbar := Id 4.
  Definition CNempty := Id 5.

  (** Model names *)

  Definition MNnrm_plus1 := Id 11.
  Definition MNnrm_ident := Id 12.
  Definition MNnmnd_plus := Id 13.
  Definition MNnmnd_mult := Id 14.
  Definition MNnfoo := Id 15.
  Definition MNbbar1 := Id 16.
  Definition MNbbar2 := Id 17.
  Definition MNnbar := Id 18.

  (** Var names *)

  Definition vx := Id 30.
  Definition vy := Id 31.
  Definition vz := Id 32.

  (** Function names *)

  Definition FNmap := Id 40.
  Definition FNpam := Id 41.
  Definition FNident := Id 42.
  Definition FNop := Id 43.

  (** Concept definitions *)

  Definition Cnrevmap : conceptdef :=
    cpt_def
      (* name *) CNnrevmap
      (* body *) [
                   nm_decl FNmap (TArrow TNat TNat); (* map : Nat -> Nat  *)                    
                   nm_decl FNpam (TArrow TNat TNat)  (* pam : Nat -> Nat  *)
                 ].
  
  Definition Cnmonoid : conceptdef :=
    cpt_def
      (* name *) CNnmonoid
      (* body *) [
                   nm_decl FNident TNat;             (* ident : Nat   *)                    
                   nm_decl FNop (TArrow TNat TNat)   (* op : Nat -> Nat -> Nat *)
                 ].

  Definition Cempty : conceptdef :=
    cpt_def
      (* name *) CNempty
      (* body *) [].

  Definition Cbad1 : conceptdef :=
    cpt_def
      (* name *) CNnfoo
      (* body *) [
                   nm_decl FNmap (TArrow TNat TNat); (* map : Nat -> Nat  *)                    
                   nm_decl FNmap (TArrow TNat TNat)  (* map : Nat -> Nat  *)
                 ].
  
  (** Model definitions *)

  Definition Mnrm_plus1 : modeldef :=
    mdl_def
      (* name *)    MNnrm_plus1
      (* concept *) CNnrevmap
      (* body *)    [
                      (* map = \x:Nat.succ x *)
                      nm_def FNmap (tabs vx TNat (tsucc (tvar vx)));
                      (* pam = \x:Nat.pred x *)
                      nm_def FNpam (tabs vx TNat (tpred (tvar vx)))
                    ].

  Definition Mnrm_ident : modeldef :=
    mdl_def
      (* name *)    MNnrm_ident
      (* concept *) CNnrevmap
      (* body *)    [
                      (* map = \x:Nat.x *)
                      nm_def FNmap (tabs vx TNat (tvar vx));
                      (* pam = \x:Nat.x *)
                      nm_def FNpam (tabs vx TNat (tvar vx))
                    ].

  Definition Mnmnd_plus : modeldef :=
    mdl_def
      (* name *)    MNnmnd_plus
      (* concept *) CNnmonoid
      (* body *)    [
                      (* ident = 0 *)
                      nm_def FNident (tnat 0);
                      (* op = \x:Nat.\y:Nat. x + y *)
                      nm_def FNop (tabs vx TNat (tabs vy TNat
                                    (tplus (tvar vx) (tvar vy))))
                    ].

  Definition Mnmnd_mult : modeldef :=
    mdl_def
      (* name *)    MNnmnd_mult
      (* concept *) CNnmonoid
      (* body *)    [
                      (* ident = 1 *)
                      nm_def FNident (tnat 1);
                      (* op = \x:Nat.\y:Nat. x * y *)
                      nm_def FNop (tabs vx TNat (tabs vy TNat
                                    (tmult (tvar vx) (tvar vy))))
                    ].

  (* not all members are defined *)
  Definition Mnmnd_bad1 : modeldef :=
    mdl_def
      (* name *)    MNnfoo
      (* concept *) CNnmonoid
      (* body *)    [
                      (* ident = 1 *)
                      nm_def FNident (tnat 1)
                    ].

(* types of members are not correct *)
  Definition Mnmnd_bad2 : modeldef :=
    mdl_def
      (* name *)    MNnbar
      (* concept *) CNnmonoid
      (* body *)    [
                      (* ident = 0 *)
                      nm_def FNident (tnat 0);
                      (* op = \x:Nat.x *)
                      nm_def FNop (tabs vx TNat (tvar vx))
                    ].
  
End Examples.


(* ################################################################# *)
(** ** Typing *)

(* ----------------------------------------------------------------- *)
(** **** Checking Concept Definitions *)

(* Examples / ---------------------------- *)
Module Examples_ConceptTypes.
  Export Examples.
  
  Definition CTnrevmap := CT_def (map_from_list [
    (FNmap, TArrow TNat TNat);                          
    (FNpam, TArrow TNat TNat)
  ]).
  
  Definition CTnmonoid := CT_def (map_from_list [
    (FNident, TNat);                          
    (FNop,    TArrow TNat TNat)
  ]).

  Definition CTempty : cty := CT_def (map_from_list []).

  Definition CTbad1 := CT_def (map_from_list [
    (FNmap, TArrow TNat TNat);                          
    (FNmap, TArrow TNat TNat)
  ]).

End Examples_ConceptTypes.
(* / Examples ---------------------------- *)

(** Let's check [concept_welldefined] on some examples *)

(* Tests / ------------------------------- *)
Module TestConcepts1. 
  Import Examples.
  
  Example test_concept_1 : concept_welldefined cstempty Cnrevmap.
  Proof.
    unfold concept_welldefined, Cnrevmap.
    simpl.
    split.
    - (* NoDup *)
      apply NoDup_cons. intros H.
      inversion H. inversion H0. inversion H0.
      apply NoDup_cons. intros H. inversion H.
      apply NoDup_nil.
      (*apply NoDup_cons;
        [intros H; try (solve_by_inverts 2) | ].
      apply NoDup_cons;
        [intros H; try (solve_by_inverts 1) | ].
      apply NoDup_nil.*)
      
    - (* All types valid *)
      apply Forall_cons. apply type_valid_arrow; repeat constructor.
      apply Forall_cons. apply type_valid_arrow; repeat constructor.
      apply Forall_nil.
      (* auto.*)
  Qed.

  Example test_concept_2 : concept_welldefined cstempty Cempty.
  Proof.
    unfold concept_welldefined, Cnrevmap.
    simpl.
    split.
    - (* NoDup *)
      apply NoDup_nil.
    - (* All types valid *)
      apply Forall_nil.
  Qed.

  Example test_concept_3 : ~ (concept_welldefined cstempty Cbad1). 
  Proof.
    unfold concept_welldefined, Cnrevmap.
    simpl. intros [HDup HTy].
    inversion HDup; subst.
    assert (Contra: In FNmap [FNmap]) by (simpl; left; reflexivity).
    apply H1 in Contra. contradiction.
  Qed.

  Example test_concept_4 : concept_welldefined cstempty Cnmonoid. 
  Proof.
    unfold concept_welldefined, Cnmonoid.
    simpl. split.
    - (* NoDup *)
      solve_NoDup_true 3.
    - (* All types valid *)
      auto.
  Qed.
End TestConcepts1.
(* / Tests ------------------------------- *)

(** Let's check [ids_are_unique] on examples. *)

(* Tests / ------------------------------- *)
Module TestIdsUniqueness1.
  Import Examples.
  
  Example test_ids_1 : ids_are_unique [vx; vy; vz] = true.
  Proof.
    reflexivity.
  Qed.

  Example test_ids_2 : ids_are_unique [] = true.
  Proof.
    reflexivity.
  Qed.

  Example test_ids_3 : ids_are_unique [vx; vy; vx] = false.
  Proof.
    reflexivity.
  Qed.
End TestIdsUniqueness1.
(* / Tests ------------------------------- *)

(* ================================================================= *)
(** *** Checking Types Validity *)

(** Let's check our concepts. *)

(* Tests / ------------------------------- *)
Module TestConcepts1_b. 
  Import Examples.
  
  Example test_concept_1 : (concept_welldefined_b cstempty Cnrevmap) = true.
  Proof. reflexivity. Qed.

  Example test_concept_2 : (concept_welldefined_b cstempty Cempty) = true.
  Proof. reflexivity. Qed.

  Example test_concept_3 : (concept_welldefined_b cstempty Cbad1) = false. 
  Proof. reflexivity. Qed.

  Example test_concept_4 :  (concept_welldefined_b cstempty Cnmonoid) = true.
  Proof. reflexivity. Qed.
                           
End TestConcepts1_b.
(* / Tests ------------------------------- *)

(** And we also have to test the typechecking routines. *)

(* Tests / ------------------------------- *)
Module TestTypes1. 
  Import Examples_ConceptTypes.
  
  Example test_type_1 : type_valid cstempty TNat.
  Proof.
    apply type_valid_nat.
  Qed.

  Definition tyNatBoolNat : ty := TArrow TNat (TArrow TBool TNat).
  
  Example test_type_2_1 : ~ (type_valid cstempty (TConceptPrm CNnmonoid tyNatBoolNat)).
  Proof.
    intros H. inversion H; subst.
    unfold concept_defined in H2.
    assert (Hcontra : cstempty CNnmonoid = None) by reflexivity.
    tryfalse.
  Qed.
  
  Example test_type_2_2 :
    type_valid (update cstempty CNnmonoid CTnmonoid) (TConceptPrm CNnmonoid tyNatBoolNat).
  Proof.
    apply type_valid_cpt.
    + unfold concept_defined. intros Hnm. tryfalse.
    + apply type_valid_arrow; auto.
  Qed.
End TestTypes1.

Module TestTypes1_b. 
  Import Examples_ConceptTypes.
  
  Example test_type_1 : (type_valid_b cstempty TNat) = true.
  Proof. reflexivity. Qed.

  Definition tyNatBoolNat := TestTypes1.tyNatBoolNat.
  
  Example test_type_2_1 :
    type_valid_b cstempty (TConceptPrm CNnmonoid tyNatBoolNat) = false.
  Proof. reflexivity. Qed.

  Example test_type_2_2 :
    type_valid_b (update cstempty CNnmonoid CTnmonoid) (TConceptPrm CNnmonoid tyNatBoolNat)
    = true.
  Proof. reflexivity. Qed.
End TestTypes1_b.
(* / Tests ------------------------------- *)

(* ================================================================= *)
(** *** Typing of Terms *)

(* ----------------------------------------------------------------- *)
(** **** Checking Model Definitions *)

(* Examples / ---------------------------- *)
Module Examples_ModelTypes.
  Export Examples.
  
  Definition MTnrm_plus1 := MTdef CNnrevmap (map_from_list [
    (FNmap, tabs vx TNat (tsucc (tvar vx)));
    (FNpam, tabs vx TNat (tpred (tvar vx)))
  ]).
 
  Definition MTnrm_ident := MTdef CNnrevmap (map_from_list [
    (FNmap, tabs vx TNat (tvar vx));
    (FNpam, tabs vx TNat (tvar vx))
  ]).

  Definition MTnmnd_plus := MTdef CNnmonoid (map_from_list [
    (FNident, tnat 0);
    (FNop, tabs vx TNat (tabs vy TNat (tplus (tvar vx) (tvar vy))))
  ]).

  Definition MTnmnd_mult := MTdef CNnmonoid (map_from_list [
    (FNident, tnat 1);
    (FNop, tabs vx TNat (tabs vy TNat (tmult (tvar vx) (tvar vy))))
  ]).

  Definition MTbad1 := MTdef CNnfoo (map_from_list [
    (FNident, tnat 1)
  ]).

End Examples_ModelTypes.
(* / Examples ---------------------------- *)

(* ----------------------------------------------------------------- *)
(** **** Checking Programs *)


(* ################################################################# *)
(** ** Operational Semantics *)


(* ================================================================= *)
(** *** Substitution *)

