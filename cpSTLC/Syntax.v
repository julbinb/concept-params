(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(* Simply Typed Lambda Calculus with simple Concept Parameters
   :: Syntax

   Definitions of STLC are based on
   Sofware Foundations, v.4 
  
   Last Update: Mon, 17 Oct 2016
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 


(* ***************************************************************** *)
(** * cpSTLC Syntax (Simply Typed Lambda Calculus 
      with simple Concept Parameters)  *)
(* ***************************************************************** *)
(* ***************************************************************** *)

Add LoadPath "../..".

Require Import ConceptParams.BasicPLDefs.Maps.


Inductive ty : Type :=
  | TBool : ty 
  | TNat  : ty
  | TArrow : ty -> ty -> ty.