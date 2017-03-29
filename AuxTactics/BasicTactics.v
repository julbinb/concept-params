(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(* Last Update: Mon, 27 Mar 2017
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 


(* ***************************************************************** *)
(** * Basic Tactics *)
(* ***************************************************************** *)
(* ***************************************************************** *)

Add LoadPath "../..".

Require Import ConceptParams.AuxTactics.LibTactics.

Require Import Coq.Lists.List.
Import ListNotations.

(* ################################################################# *)
(** ** Some FRAP Tactics (Adam Chlipala) *)

Ltac equality := intuition congruence.

Ltac propositional := intuition idtac.

(* ----------------------------------------------------------------- *)
(** **** Simplify *)

Ltac simplify := 
  repeat match goal with
         | [ H : True |- _ ] => clear H
         end;
  repeat progress (simpl in *; intros; try autorewrite with core in *).

(* ----------------------------------------------------------------- *)
(** **** cases *)

Ltac cases E :=
  ((is_var E; destruct E)
   || match type of E with
      | {_} + {_} => destruct E
      | _ => let Heq := fresh "Heq" in destruct E eqn:Heq
      end);
  repeat match goal with
         | [ H : _ = left _ |- _ ] => clear H
         | [ H : _ = right _ |- _ ] => clear H
         end.

(* ----------------------------------------------------------------- *)
(** **** invert *)

Ltac invert' H := inversion H; clear H; subst.

Ltac invertN n :=
  match goal with
    | [ |- forall x : ?E, _ ] =>
      match type of E with
        | Prop =>
          let H := fresh in intro H;
            match n with
              | 1 => invert' H
              | S ?n' => invertN n'
            end
        | _ => intro; invertN n
      end
  end.

Ltac invert e := invertN e || invert' e.

Ltac invert0 e := invert e; fail.
Ltac invert1 e := invert0 e || (invert e; []).
Ltac invert2 e := invert1 e || (invert e; [|]).


(* ################################################################# *)
(** ** Contradiction in Assumption *)

(** JB | [solve_by_inverts] tactic is borrowed from 
    Sofware Foundations, v.4 :: [Smallstep.v]
    $Date: 2016-07-13 12:41:41 -0400 (Wed, 13 Jul 2016) $

    The following custom tactic, called [solve_by_inverts], can be
    helpful in such cases.  It will solve the goal if it can be solved
    by inverting some hypothesis; otherwise, it fails. *)

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ => 
  match type of T with Prop =>
    solve [ 
      inversion H; 
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

(** It looks
    through the current proof state for a hypothesis [H] (the first
    [match]) of type [Prop] (the second [match]) such that performing
    inversion on [H] (followed by a recursive invocation of the same
    tactic, if its argument [n] is greater than one) completely solves
    the current goal.  If no such hypothesis exists, it fails.

    We will usually want to call [solve_by_inverts] with argument
    [1] (especially as larger arguments can lead to very slow proof
    checking), so we define [solve_by_invert] as a shorthand for this
    case. *)

Ltac solve_by_invert :=
  solve_by_inverts 1.


(* ################################################################# *)
(** ** Lists Analysis *)

(** [solve_NoDup_true] resolves the goal if it is true [NoDup l] prop.
    [n] must be equal to at least [length l] + 1. *)

Ltac solve_NoDup_true n :=
  match goal with [ |- NoDup ?l ] => 
  match l with
  | [] => apply NoDup_nil
  | _  => apply NoDup_cons;
          [ intros H; try (solve_by_inverts n) |
            match n with S (S (?n')) => solve_NoDup_true (S n') end
          ]
  end end.

