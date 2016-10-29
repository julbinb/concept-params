(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(* Last Update: Sat, 29 Oct 2016
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

