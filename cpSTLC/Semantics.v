(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(* Simply Typed Lambda Calculus with simple Concept Parameters
   :: Semantics

   Definitions of STLC are based on
   Sofware Foundations, v.4 
  
   Last Update: Mon, 17 Oct 2016
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 


(* ***************************************************************** *)
(** * cpSTLC Semantics (Simply Typed Lambda Calculus 
      with simple Concept Parameters)  *)
(* ***************************************************************** *)
(* ***************************************************************** *)

Add LoadPath "../..".

Require Import ConceptParams.BasicPLDefs.Maps.
Require Export ConceptParams.cpSTLC.Syntax.

Inductive tm : Type :=
  | tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : id -> ty -> tm -> tm
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm.