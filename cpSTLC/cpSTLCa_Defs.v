(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(* Simply Typed Lambda Calculus with simple Concept Parameters
   :: version a

   Definitions of STLC are based on
   Sofware Foundations, v.4 
  
   Last Update: Mon, 18 Oct 2016
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 


(* ***************************************************************** *)
(** * cpSTLCa Syntax and Semantics Definition 
      (Simply Typed Lambda Calculus with simple Concept Parameters  
       :: version a) *)
(* ***************************************************************** *)
(* ***************************************************************** *)

Add LoadPath "../..".

Require Import ConceptParams.BasicPLDefs.Maps.
Require Import ConceptParams.BasicPLDefs.Relations.


(* ################################################################# *)
(** ** Syntax *)

(** cpSTLCa -- Symply Typed Lambda Calculus 
    with simple concept parameters.
   
    _Types_ are STLC types plus [C # T], 
    where C is a concept name, T is a type.
    
    _Terms_ are STLC terms plus [\c#C. t], 
    where c is a concept parameter.

      CSec ::=           Concept declarations
             | <empty>              
             | CDef CSec           

      CDef ::=           Concept definition
             | concept Id NameDecls endc

      MSec ::=           Model declarations 
             | <empty>
             | MDef MSec
    
      MDef ::=
             | model Id of Id NameDefs endm
      
      NameDecls ::=      List of name declarations
             | <empty>
             | NameDecl ; NameDecls

      NameDefs ::=       List of name definitions
             | <empty>
             | NameDef ; NameDefs

      NameDecl ::=       Name declaration
             | Id : T

      NameDef ::=        Name definition
             | Id = t


      C metavariable means concept name (Id)       

      T ::=              Types
          | Nat
          | Bool
          | T -> T           function
          | C # T            concept dependency


      x metavariable means variable name (Id)
      n metavariable means nat constant
      c metavariable means concept parameter name (Id)
      M metavariable means model name (Id)

      t ::=              Terms
          | x                variable
          | \x:T.t           function
          | t t              function application
          | \c#C.t           concept parameter
          | t # M            model application
          | true
          | false
          | if t then t else t
          | n
          | succ t
          | pred t
          | mult t t   
          | let x = t in t   let binding

    _Program_ consists of concept and model declarations, 
    and a term.
          
*)

(* ----------------------------------------------------------------- *)
(** *** Types *)

Inductive ty : Type :=
  | TBool : ty 
  | TNat  : ty
  | TArrow   : ty -> ty -> ty
  | TConcept : id -> ty -> ty
.

(* ----------------------------------------------------------------- *)
(** *** Terms *)

Inductive tm : Type :=
  | tvar  : id -> tm               (* x *)
  | tapp  : tm -> tm -> tm         (* t1 t2 *)
  | tabs  : id -> ty -> tm -> tm   (* \x:T.t *)
  | tmapp : tm -> id -> tm         (* t # M *)
  | ttrue  : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm     (* if t1 then t2 else t3 *)
  | tnat   : nat -> tm             (* n *)
  | tsucc  : tm -> tm              (* succ t1 *) 
  | tpred  : tm -> tm              (* pred t1 *)
  | tmult  : tm -> tm -> tm        (* mult t1 t2 *)
  | tlet   : id -> tm -> tm -> tm  (* let x = t1 in t2 *)                           
.

(* ----------------------------------------------------------------- *)
(** *** Concepts *)

(** Name declaration *)

Inductive namedecl : Type :=
  | nm_decl : id -> ty -> namedecl   (* f : T *)
.

(** List of name declarations *)

Definition namedecl_list : Type := list namedecl.

(** Concept definition *)

Inductive conceptdef : Type :=
  | cpt_def : id -> namedecl_list -> conceptdef   (* concept Id NameDefs endc *)
.

(** Concept declarations Section *)

Definition conceptsec : Type := list conceptdef.

(* ----------------------------------------------------------------- *)
(** *** Models *)

(** Name definition *)

Inductive namedef : Type :=
  | nm_def : id -> tm -> namedef   (* f = T *)
.

(** List of name definitions *)

Definition namedef_list : Type := list namedef.

(** Model definition *)

Inductive modeldef : Type :=
  | mdl_def : id -> id -> namedef_list -> modeldef   (* model Id of Id NameDefs endm *)
.

(** Model declarations Section *)

Definition modelsec : Type := list modeldef.

(* ----------------------------------------------------------------- *)
(** *** Program *)

Inductive program : Type :=
  | tprog : conceptsec -> modelsec -> tm -> program
.