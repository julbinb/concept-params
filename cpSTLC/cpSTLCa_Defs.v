(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(* Simply Typed Lambda Calculus with simple Concept Parameters
   :: version a

   Definitions of STLC are based on
   Sofware Foundations, v.4 
  
   Last Update: Thu, 20 Oct 2016
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

Require Import Coq.Lists.List.
Import ListNotations.

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

Definition concept_defined (st :  symbtable) (C : id) : Prop := 
  st C <> None.
  
Inductive ty_valid (st : symbtable) : ty -> Prop :=
  | ty_valid_nat   : ty_valid st TNat
  | ty_valid_bool  : ty_valid st TBool
  | ty_valid_arrow : forall T1 T2,
      ty_valid st T1 ->
      ty_valid st T2 ->
      ty_valid st (TArrow T1 T2)
  | ty_valid_cpt   : forall C T,
      concept_defined st C ->
      ty_valid st T ->
      ty_valid st (TConceptPrm C T)
.

(** Now we are ready to define a property "concept is well defined" *)

(*
Print List.NoDup.
Inductive NoDup (A : Type) : list A -> Prop :=
    NoDup_nil : List.NoDup nil
  | NoDup_cons : forall (x : A) (l : list A), ~ List.In x l -> List.NoDup l -> List.NoDup (x :: l)

Print List.In.
List.In = 
fun A : Type =>
fix In (a : A) (l : list A) {struct l} : Prop :=
  match l with
  | nil => False
  | (b :: m)%list => b = a \/ In a m
  end
     : forall A : Type, A -> list A -> Prop

Print List.Forall.
Inductive Forall (A : Type) (P : A -> Prop) : list A -> Prop :=
    Forall_nil : List.Forall P nil
  | Forall_cons : forall (x : A) (l : list A), P x -> List.Forall P l -> List.Forall P (x :: l)
*)

Definition concept_welldefined (st : symbtable) (C : conceptdef) : Prop :=
  match C with
    cpt_def cname cbody =>
    let (fnames, ftypes) := split (map namedecl_to_pair cbody) in
    (** all names are distinct *)
    List.NoDup fnames
    (** and all types are valid *)
    /\ List.Forall (fun ftype => ty_valid st ftype) ftypes            
  end.
  
Definition stempty := @empty cty.

(** Let's check some examples *)

Module TestConcepts.
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
  - (* All types valid *)
    apply Forall_cons. apply ty_valid_arrow; repeat constructor.
    apply Forall_cons. apply ty_valid_arrow; repeat constructor.
    apply Forall_nil.
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

End TestConcepts.

(** There is a problem here: it's quite cumbersome to check 
    well-definedness of concept definitions in proposition style.
    We could implement auxuliary tactics to make proofs easier,
    but it's not very practical. 

    It would be convenient to at least have an algorithm for 
    checking name repetitions in a concept definition.
    To check this, we need an effective set. E.g. MSetAVL.
*)




(*
Definition map_nat_nat: Type := M.t nat.

Definition find k (m: map_nat_nat) := M.find k m.

Definition update (p: nat * nat) (m: map_nat_nat) :=
  M.add (fst p) (snd p) m.

Notation "k |-> v" := (pair k v) (at level 60).
Notation "[ ]" := (M.empty nat).
Notation "[ p1 , .. , pn ]" := (update p1 .. (update pn (M.empty nat)) .. ).

Example ex1: find 3 [1 |-> 2, 3 |-> 4] = Some 4.
Proof. reflexivity. Qed.

Example ex2: find 5 [1 |-> 2, 3 |-> 4] = None.
Proof. reflexivity. Qed.
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