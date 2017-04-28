(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(* Mainly borrowed from Sofware Foundations, v.4 
   $Date: 2015-12-11 17:17:29 -0500 (Fri, 11 Dec 2015) $

   Last Update: Thu, 27 Apr 2017
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 


(* ***************************************************************** *)
(** * Identifiers as wrappers of nats *)
(* ***************************************************************** *)
(* ***************************************************************** *)

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.

Require Import Coq.Structures.Orders.
Require Import Coq.Structures.OrdersAlt.
Require Import Coq.Structures.Equalities.
Require Import Coq.ZArith.ZArith.

Require Import Coq.MSets.MSets.

(* ################################################################# *)
(** ** Identifier Definitions  *)
(* ################################################################# *)

Inductive id : Type :=
  | Id : nat -> id.

Definition beq_id id1 id2 :=
  match id1,id2 with
    | Id n1, Id n2 => beq_nat n1 n2
  end.

(* ================================================================= *)
(** *** Properties of Identifiers *)
(* ================================================================= *)

Theorem beq_id_refl : forall id, true = beq_id id id.
Proof.
  intros [n]. simpl. rewrite <- beq_nat_refl.
  reflexivity.
Qed.

Theorem beq_id_true_iff : forall id1 id2 : id,
  beq_id id1 id2 = true <-> id1 = id2.
Proof.
   intros [n1] [n2].
   unfold beq_id. 
   rewrite beq_nat_true_iff.
   split.
   - (* -> *) intros H. rewrite H. reflexivity.
   - (* <- *) intros H. inversion H. reflexivity.
Qed.

Theorem beq_id_false_iff : forall x y : id,
  beq_id x y = false
  <-> x <> y.
Proof.
  intros x y. rewrite <- beq_id_true_iff.
  rewrite not_true_iff_false. reflexivity.
Qed.

Theorem false_beq_id : forall x y : id,
   x <> y
   -> beq_id x y = false.
Proof.
  intros x y. rewrite beq_id_false_iff.
  intros H. apply H.
Qed.

(* ----------------------------------------------------------------- *)
(** **** Reflecting Equality of Identifiers *)
(* ----------------------------------------------------------------- *)

(** It's convenient to use the reflection idioms.  
    We begin by proving a fundamental _reflection lemma_ relating 
    the equality proposition on [id]s 
    with the boolean function [beq_id]. *)

(** Use the proof of [beq_natP] in chapter [IndProp] as a template to
    prove the following: *)

Lemma beq_idP : forall x y, reflect (x = y) (beq_id x y).
Proof.
  intros x y. 
  apply iff_reflect. symmetry. apply beq_id_true_iff.
Qed.

(* ----------------------------------------------------------------- *)
(** **** Propositional Equality of Identifiers *)
(* ----------------------------------------------------------------- *)

Definition eq_id x y : Prop :=
  match x, y with
    Id n, Id m => eq_nat n m
  end.

Lemma eq_id_iff_eq_nat : forall n m,
    eq_id (Id n) (Id m) <-> eq_nat n m.
Proof.
  tauto.
Qed. 

Theorem eq_id_decide : forall x y, {eq_id x y} + {~ eq_id x y}.
Proof.
  intros [n] [m]. simpl.
  apply eq_nat_decide.
Qed.

Theorem eq_id_dec : forall (x y : id), {x = y} + {x <> y}.
Proof.
  intros [x] [y]. destruct (eq_nat_dec x y) as [H|H].
  - subst. left. reflexivity.
  - right. intros contra. inversion contra as [contra'].
    apply H in contra'. assumption.
Qed.


(* ################################################################# *)
(** ** Identifier Utils  *)
(* ################################################################# *)

(* ----------------------------------------------------------------- *)
(** **** Ordering of Identifiers *)
(* ----------------------------------------------------------------- *)

Definition lt_id id1 id2 :=
  match id1,id2 with
    | Id n1, Id n2 => lt n1 n2
  end.

Lemma lt_id_iff_lt_nat : forall n m,
    lt_id (Id n) (Id m) <-> lt n m.
Proof.
  tauto.
Qed.  

(* ================================================================= *)
(** *** Identifiers as Ordered type *)
(* ================================================================= *)

(** This is the initially used implementation *)

Module Id_as_OT'_old <: OrderedType.OrderedType. 
(* From Coq.Structures.OrderedType *)

  Definition t := id.

  Definition eq := @eq id.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  Definition lt := lt_id.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    intros [x] [y] [z]. unfold lt, lt_id.
    apply Nat.lt_trans.
  Qed.  

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    intros [x] [y]. unfold lt, lt_id. unfold eq.
    intros Hlt Contra. inversion Contra as [Contra'].
    apply Nat.lt_neq in Hlt. apply Hlt in Contra'.
    apply Contra'.
  Qed.
  
  Definition compare : forall x y : t, OrderedType.Compare lt eq x y.
  Proof.
    intros [x] [y]. destruct (nat_compare x y) as [ | | ] eqn:H.
    - (* EQ *) apply OrderedType.EQ. apply nat_compare_eq in H; subst. 
               reflexivity.
    - (* LT *) apply OrderedType.LT. apply nat_compare_Lt_lt in H.
               rewrite <- lt_id_iff_lt_nat in H. assumption.
    - (* GT *) apply OrderedType.GT. apply nat_compare_Gt_gt in H.
               unfold gt in H.
               rewrite <- lt_id_iff_lt_nat in H. assumption.
  Defined. 

  Definition eq_dec := eq_id_dec.

End Id_as_OT'_old.

Module Id_as_OT_old <: OrderedType := 
  Coq.Structures.OrdersAlt.Update_OT Id_as_OT'_old.

(** But we need [UsualOrderedType] to use ids in the framework ListasAVL. *)

Module IdMDT <: MiniDecidableType.
  Definition t := id.
  Definition eq_dec := eq_id_dec.
End IdMDT.

(** [IdUDT] provides decidable equality *)
Module IdUDT <: UsualDecidableType := Make_UDT IdMDT.

(** This part is needed for both original and new versions of ordered type *)
Module IdPreUOT.
  Include IdUDT.

  Definition lt := lt_id.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    intros [x] [y] [z]. unfold lt, lt_id.
    apply Nat.lt_trans.
  Qed.  
  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    intros [x] [y]. unfold lt, lt_id. unfold eq.
    intros Hlt Contra. inversion Contra as [Contra'].
    apply Nat.lt_neq in Hlt. apply Hlt in Contra'.
    apply Contra'.
  Qed.
End IdPreUOT.

(** Original ordered type (used in FSets) with usual decidable equality *)
Module IdUOTOrig <: OrderedType.OrderedType.
  Include IdPreUOT.
  Definition compare : forall x y : t, OrderedType.Compare lt eq x y.
  Proof.
    intros [x] [y]. destruct (nat_compare x y) as [ | | ] eqn:H.
    - (* EQ *) apply OrderedType.EQ. apply nat_compare_eq in H; subst. 
               reflexivity.
    - (* LT *) apply OrderedType.LT. apply nat_compare_Lt_lt in H.
               rewrite <- lt_id_iff_lt_nat in H. assumption.
    - (* GT *) apply OrderedType.GT. apply nat_compare_Gt_gt in H.
               unfold gt in H.
               rewrite <- lt_id_iff_lt_nat in H. assumption.
  Defined. 
End IdUOTOrig.

(** And this is a new representation: usual ordered type,
 ** which is used for MSets.
 ** (Implementation is copied from the standard lib.) *)

Module IdUOT <: UsualOrderedType.
  Include IdPreUOT.
  Instance lt_strorder : StrictOrder lt.
  Proof.
    split.
    intros x Hx. apply (lt_not_eq _ _ Hx); auto with *.
    exact lt_trans.
  Qed.
  Instance lt_compat : Proper (eq==>eq==>iff) lt.
  Proof.
    apply proper_sym_impl_iff_2; auto with *.
  Qed.

  Definition compare x y :=
    match IdUOTOrig.compare x y with
    | OrderedType.EQ _ => Eq
    | OrderedType.LT _ => Lt
    | OrderedType.GT _ => Gt
    end.

  Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
  Proof.
    intros; unfold compare; destruct IdUOTOrig.compare; auto.
  Qed.
End IdUOT.
