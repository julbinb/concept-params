(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(* Simply Typed Lambda Calculus with simple Concept Parameters
   :: version a

   Definitions of STLC are based on
   Sofware Foundations, v.4 
  
   Last Update: Fri, 29 Oct 2016
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

Require Import ConceptParams.AuxTactics.LibTactics.
Require Import ConceptParams.AuxTactics.BasicTactics.

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Bool.Bool.

Require Import Coq.omega.Omega.


(* ################################################################# *)
(** ** Syntax *)

(** cpSTLCa — Symply Typed Lambda Calculus 
    with simple _concept parameters_.


    Types are STLC types with a type [C # T], 
    where [C] is a concept name, [T] is a type.

    Terms are STLC terms with a term [\c#C. t], 
    where [c] is a concept parameter.

<<
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
          | c.f              concept element invocation
          | true
          | false
          | if t then t else t
          | n
          | succ t
          | pred t
          | plus t t 
          | minus t t 
          | mult t t   
          | eqnat t t        nat equality
          | le t t           nat less-than         
          | let x = t in t   let binding

>>

    _Program_ consists of concept and model declarations, 
    and a term.

<<
      p ::=
          | CSec MSec t
>>
          
*)

(* ----------------------------------------------------------------- *)
(** **** Types *)

Inductive ty : Type :=
  | TBool : ty 
  | TNat  : ty
  | TArrow : ty -> ty -> ty        (* T1 -> T2 *)
  | TConceptPrm : id -> ty -> ty   (* C # T *)
.

(* ----------------------------------------------------------------- *)
(** **** Terms *)

Inductive tm : Type :=
  | tvar  : id -> tm               (* x *)
  | tapp  : tm -> tm -> tm         (* t1 t2 *)
  | tabs  : id -> ty -> tm -> tm   (* \x:T.t *)
  | tmapp : tm -> id -> tm         (* t # M *)
  | tcabs  : id -> id -> tm -> tm  (* \c#C.t *)
  | tcinvk : id -> id -> tm        (* c.f *)                                 
  | ttrue  : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm     (* if t1 then t2 else t3 *)
  | tnat   : nat -> tm             (* n *)
  | tsucc  : tm -> tm              (* succ t1 *) 
  | tpred  : tm -> tm              (* pred t1 *)
  | tplus  : tm -> tm -> tm        (* plus t1 t2 *)
  | tminus : tm -> tm -> tm        (* minus t1 t2 *)
  | tmult  : tm -> tm -> tm        (* mult t1 t2 *)
  | teqnat : tm -> tm -> tm        (* eqnat t1 t2 *)
  | tle    : tm -> tm -> tm        (* le t1 t2 *)
  | tlet   : id -> tm -> tm -> tm  (* let x = t1 in t2 *)                           
.

(* ----------------------------------------------------------------- *)
(** **** Concepts *)

(** Name declaration *)

Inductive namedecl : Type :=
  | nm_decl : id -> ty -> namedecl   (* f : T *)
.

(** Auxiliary function to transform name declaration into pair *)
Definition namedecl_to_pair (nmdecl : namedecl) : (id * ty) :=
  match nmdecl with
    nm_decl fname ftype => (fname, ftype)
  end.


(** List of name declarations *)

Definition namedecl_list : Type := list namedecl.

(** Concept definition *)

Inductive conceptdef : Type :=
  | cpt_def : id -> namedecl_list -> conceptdef   (* concept Id NameDefs endc *)
.

(** Concept declarations Section *)

Definition conceptsec : Type := list conceptdef.

(* ----------------------------------------------------------------- *)
(** **** Models *)

(** Name definition *)

Inductive namedef : Type :=
  | nm_def : id -> tm -> namedef   (* f = T *)
.

(** Auxiliary function to transform name defintion into pair *)
Definition namedef_to_pair (nmdef : namedef) : (id * tm) :=
  match nmdef with
    nm_def fname fdef => (fname, fdef)
  end.

(** List of name definitions *)

Definition namedef_list : Type := list namedef.

(** Model definition *)

Inductive modeldef : Type :=
  | mdl_def : id -> id -> namedef_list -> modeldef   (* model Id of Id NameDefs endm *)
.

(** Model declarations Section *)

Definition modelsec : Type := list modeldef.

(* ----------------------------------------------------------------- *)
(** **** Program *)

Inductive program : Type :=
  | tprog : conceptsec -> modelsec -> tm -> program
.

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
                   nm_decl FNident TNat;               (* ident : Nat   *)                    
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

End Examples.


(* ################################################################# *)
(** ** Typing *)

(** To typecheck terms with concept parameters, we need an additional 
    context with information about concepts: concept context,
    just st typing context.
    
    There must be a global _symbol table_ with information about
    concepts and models.
 *)

(* ----------------------------------------------------------------- *)
(** **** Checking Concept Definitions *)

(** Concept information: list of pairs (element name, element type) 
    [(fi, Ti)].
 *)

Definition cty : Type := list (id * ty).

(* Examples / ---------------------------- *)
Module ExamplesTypes.
  Export Examples.
  
  Definition CTnrevmap := [
    (FNmap, TArrow TNat TNat);                          
    (FNpam, TArrow TNat TNat)
  ].
  
  Definition CTnmonoid := [
    (FNident, TNat);                          
    (FNop,    TArrow TNat TNat)
  ].

  Definition CTempty : cty := [].

  Definition CTbad1 := [
    (FNmap, TArrow TNat TNat);                          
    (FNmap, TArrow TNat TNat)
  ].

End ExamplesTypes.
(* / Examples ---------------------------- *)

(** Concept definition is Ok if names of concept elements are
    distinct, and types of elements are valid.

    The only problem in types is with concept dependency [C # T]:
    if C is undefined concept name, type is not valid.
    So to check types validity, we need symbol table already.
*)

(** Symbol table is a map from concept names to concept types
    [Ci -> CTi]. *)

Definition symbtable : Type := partial_map cty.

(** Now let's define a property "type is valid".
    This property must be checked againts concrete symbol table.
 *)

Definition name_defined (st :  symbtable) (nm : id) : Prop := 
  st nm <> None.

Definition name_defined_b (st : symbtable) (nm : id) : bool :=
  match st nm with
  | None   => false
  | Some _ => true
  end.
  
Inductive type_valid (st : symbtable) : ty -> Prop :=
  | type_valid_nat   : type_valid st TNat
  | type_valid_bool  : type_valid st TBool
  | type_valid_arrow : forall T1 T2,
      type_valid st T1 ->
      type_valid st T2 ->
      type_valid st (TArrow T1 T2)
  | type_valid_cpt   : forall C T,
      name_defined st C ->
      type_valid st T ->
      type_valid st (TConceptPrm C T)
.

Hint Constructors type_valid. 

(** Now we are ready to define a property "concept is well defined" *)

Definition concept_welldefined (st : symbtable) (C : conceptdef) : Prop :=
  match C with
    cpt_def cname cbody =>
    let (fnames, ftypes) := split (map namedecl_to_pair cbody) in
    (** all names are distinct *)
    List.NoDup fnames
    (** and all types are valid *)
    /\ List.Forall (fun ftype => type_valid st ftype) ftypes            
  end.

Hint Unfold concept_welldefined.
  
Definition stempty := @empty cty.

(** Let's check some examples *)

(* Tests / ------------------------------- *)
Module TestConcepts1. 
  Import Examples.
  
  Example test_concept_1 : concept_welldefined stempty Cnrevmap.
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

  Example test_concept_2 : concept_welldefined stempty Cempty.
  Proof.
    unfold concept_welldefined, Cnrevmap.
    simpl.
    split.
    - (* NoDup *)
      apply NoDup_nil.
    - (* All types valid *)
      apply Forall_nil.
  Qed.

  Example test_concept_3 : ~ (concept_welldefined stempty Cbad1). 
  Proof.
    unfold concept_welldefined, Cnrevmap.
    simpl. intros [HDup HTy].
    inversion HDup; subst.
    assert (Contra: In FNmap [FNmap]) by (simpl; left; reflexivity).
    apply H1 in Contra. contradiction.
  Qed.

  Example test_concept_4 : concept_welldefined stempty Cnmonoid. 
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

(** There is a problem: it's quite cumbersome to check 
    well-definedness of concept definitions in propositional style.
    We could implement auxuliary tactics to make proofs easier,
    but it's not very practical. 

    It would be convenient to have an algorithm for 
    checking name repetitions in a concept definition.
    To check this, we need an effective set of ids. 
    The one based on AVL trees is defined in [Maps.v].
*)

(** Let's write a function [ids_are_unique] to check name repetitions. *)

Fixpoint ids_are_unique_recur (nmlist : list id) (nmset : id_set) : bool :=
  match nmlist with
  | [] => true
  | nm :: nms => if ids_mem nm nmset 
                 then false
                 else  ids_are_unique_recur nms (ids_add nm nmset)
  end.

Definition ids_are_unique (names : list id) : bool :=
  ids_are_unique_recur names ids_empty.

(** Check it on some examples. *)

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

(** We can also write a function [types_are_valid] to check that 
    all types in a list are valid.
*)

Fixpoint type_valid_b (st : symbtable) (t : ty) : bool :=
  match t with
  | TNat  => true
  | TBool => true
  | TArrow t1 t2     => andb (type_valid_b st t1)  (type_valid_b st t2)
  | TConceptPrm c t1 => andb (name_defined_b st c) (type_valid_b st t1)
  end.

Definition types_valid_b (st : symbtable) (ts : list ty) : bool :=
  List.forallb (fun t => type_valid_b st t) ts.

(** And define a function to check that "concept is well defined" *)

Definition concept_welldefined_b (st : symbtable) (C : conceptdef) : bool :=
  match C with
    cpt_def cname cbody =>
    let (fnames, ftypes) := split (map namedecl_to_pair cbody) in
    andb
      (** all names are distinct *)
      (ids_are_unique fnames)
      (** and all types are valid *)
      (types_valid_b st ftypes)           
  end.

(** Let's check our concepts. *)

(* Tests / ------------------------------- *)
Module TestConcepts1_b. 
  Import Examples.
  
  Example test_concept_1 : (concept_welldefined_b stempty Cnrevmap) = true.
  Proof. reflexivity. Qed.

  Example test_concept_2 : (concept_welldefined_b stempty Cempty) = true.
  Proof. reflexivity. Qed.

  Example test_concept_3 : (concept_welldefined_b stempty Cbad1) = false. 
  Proof. reflexivity. Qed.

  Example test_concept_4 :  (concept_welldefined_b stempty Cnmonoid) = true.
  Proof. reflexivity. Qed.
                           
End TestConcepts1_b.
(* / Tests ------------------------------- *)

(** And we also have to test the typechecking routines. *)

(* Tests / ------------------------------- *)
Module TestTypes1. 
  Import ExamplesTypes.
  
  Example test_type_1 : type_valid stempty TNat.
  Proof.
    apply type_valid_nat.
  Qed.

  Definition tyNatBoolNat : ty := TArrow TNat (TArrow TBool TNat).
  
  Example test_type_2_1 : ~ (type_valid stempty (TConceptPrm CNnmonoid tyNatBoolNat)).
  Proof.
    intros H. inversion H; subst.
    unfold name_defined in H2.
    assert (Hcontra : stempty CNnmonoid = None) by reflexivity.
    tryfalse.
  Qed.
  
  Example test_type_2_2 :
    type_valid (update stempty CNnmonoid CTnmonoid) (TConceptPrm CNnmonoid tyNatBoolNat).
  Proof.
    apply type_valid_cpt.
    + unfold name_defined. intros Hnm. tryfalse.
    + apply type_valid_arrow; auto.
  Qed.
End TestTypes1.

Module TestTypes1_b. 
  Import ExamplesTypes.
  
  Example test_type_1 : (type_valid_b stempty TNat) = true.
  Proof. reflexivity. Qed.

  Definition tyNatBoolNat := TestTypes1.tyNatBoolNat.
  
  Example test_type_2_1 :
    type_valid_b stempty (TConceptPrm CNnmonoid tyNatBoolNat) = false.
  Proof. reflexivity. Qed.

  Example test_type_2_2 :
    type_valid_b (update stempty CNnmonoid CTnmonoid) (TConceptPrm CNnmonoid tyNatBoolNat)
    = true.
  Proof. reflexivity. Qed.
End TestTypes1_b.
(* / Tests ------------------------------- *)

(** At this point we cannot do more on contexts. To check models
    we have to be able to check terms (function definitions). 
    But terms may conist of model applications.

    Therefore, typing of terms and models are mutually recursive.
*)

(* ================================================================= *)
(** *** Typing of terms *)

(*
Inductive tm : Type :=
  | tvar  : id -> tm               (* x *)
  | tapp  : tm -> tm -> tm         (* t1 t2 *)
  | tabs  : id -> ty -> tm -> tm   (* \x:T.t *)
  | tmapp : tm -> id -> tm         (* t # M *)
  | tcabs  : id -> id -> tm -> tm  (* \c#C.t *)
  | tcinvk : id -> id -> tm        (* c.f *)                                 
  | ttrue  : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm     (* if t1 then t2 else t3 *)
  | tnat   : nat -> tm             (* n *)
  | tsucc  : tm -> tm              (* succ t1 *) 
  | tpred  : tm -> tm              (* pred t1 *)
  | tplus  : tm -> tm -> tm        (* plus t1 t2 *)
  | tminus : tm -> tm -> tm        (* minus t1 t2 *)
  | tmult  : tm -> tm -> tm        (* mult t1 t2 *)
  | teqnat : tm -> tm -> tm        (* eqnat t1 t2 *)
  | tle    : tm -> tm -> tm        (* le t1 t2 *)
  | tlet   : id -> tm -> tm -> tm  (* let x = t1 in t2 *) 
.
*)


(* ################################################################# *)
(** ** Operational Semantics *)


(* ================================================================= *)
(** *** Substitution *)




(*

Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | tvar y =>
      if beq_id x y then s else t
  | tabs y T t1 =>
      tabs y T (if beq_id x y then t1 else (subst x s t1))
  | tapp t1 t2 =>
      tapp (subst x s t1) (subst x s t2)
  | tnat n =>
      tnat n
  | tsucc t1 =>
      tsucc (subst x s t1)
  | tpred t1 =>
      tpred (subst x s t1)
  | tmult t1 t2 =>
      tmult (subst x s t1) (subst x s t2)
  | tif0 t1 t2 t3 =>
      tif0 (subst x s t1) (subst x s t2) (subst x s t3)
  | tpair t1 t2 =>
      tpair (subst x s t1) (subst x s t2)
  | tfst t1 =>
      tfst (subst x s t1)
  | tsnd t1 =>
      tsnd (subst x s t1)
  | tunit => tunit
    (* [x := s] (let y = t1 in t2) *)           
  | tlet y t1 t2 =>
      tlet y (subst x s t1) (if beq_id x y then t2 else (subst x s t2))
  | tinl T t1 =>
      tinl T (subst x s t1)
  | tinr T t1 =>
      tinr T (subst x s t1)
  | tcase t0 y1 t1 y2 t2 =>
      tcase (subst x s t0)
         y1 (if beq_id x y1 then t1 else (subst x s t1))
         y2 (if beq_id x y2 then t2 else (subst x s t2))
  | tnil T =>
      tnil T
  | tcons t1 t2 =>
      tcons (subst x s t1) (subst x s t2)
  | tlcase t1 t2 y1 y2 t3 =>
      tlcase (subst x s t1) (subst x s t2) y1 y2
        (if beq_id x y1 then
           t3
         else if beq_id x y2 then t3
              else (subst x s t3))
  | tfix t1 =>
      tfix (subst x s t1)
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

 *)
