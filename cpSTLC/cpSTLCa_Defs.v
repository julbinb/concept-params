(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(* Simply Typed Lambda Calculus with simple Concept Parameters
   :: version a

   Definitions of STLC are based on
   Sofware Foundations, v.4 
  
   Last Update: Mon, 31 Oct 2016
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
  | tabs  : id -> ty -> tm -> tm   (* \x:T11.t12 *)
  | tmapp : tm -> id -> tm         (* t1 # M *)
  | tcabs  : id -> id -> tm -> tm  (* \c#C.t1 *)
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
  | tlenat : tm -> tm -> tm        (* lenat t1 t2 *)
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
Hint Unfold namedecl_list.

(** Concept definition *)

Inductive conceptdef : Type :=
  | cpt_def : id -> namedecl_list -> conceptdef   (* concept Id NameDefs endc *)
.

(** Concept declarations Section *)

Definition conceptsec : Type := list conceptdef.
Hint Unfold conceptsec.

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
Hint Unfold namedef_list.

(** Model definition *)

Inductive modeldef : Type :=
  | mdl_def : id -> id -> namedef_list -> modeldef   (* model Id of Id NameDefs endm *)
.

(** Model declarations Section *)

Definition modelsec : Type := list modeldef.
Hint Unfold modelsec.

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

(** To typecheck terms with concept parameters, we need 
    information about concepts and models.
    So we need a kind of a _symbol table_. It is defined later.
    We start with defining types of concepts and models.
 *)

(** [tycontext] is a typing context: a map from ids to types. *)

Definition tycontext := partial_map ty.
Hint Unfold tycontext. 

(** Concept type [cty] contains information about members' types.

    To check welldefinedness of a concept, it is enough to use
    [tycontext] (functional map from ids to types) to store 
    information about names and types of concept members.

    But we also need to check welldefinedness of models. To do so,
    we have to check that a model defines all concept members.
    Thus, there must be a way to extract information about all 
    concept members from [cty].
 
    Therefore, we will use AVL Map from ids to types to express
    information about concept members.
 *)

(** AVL map from [id] to [ty]. *)
Definition id_ty_map := id_map ty.
Hint Unfold id_ty_map.

Inductive cty : Type := CTdef : id_ty_map -> cty.

Definition find_ty := mids_find ty.
Hint Unfold find_ty.

(** Models are always defined for some concepts. Therefore, 
    a list of members and their types must be the same as in
    the corresponding concept. 
    The only thing we need to know about a model to typecheck
    its application is its concept.
    But to implement terms reduction, we have to provide 
    information about members' implementation.

    Thus, model type [mty] will contain both concept name
    and a map from ids to terms. *)

(** AVL map from [id] to [tm]. *)
Definition id_tm_map := id_map tm.
Hint Unfold id_tm_map.

Inductive mty : Type := MTdef : id -> id_tm_map -> mty.

Definition find_tm := mids_find tm.
Hint Unfold find_tm.

(** For further checks we need a _symbol table_ to store 
    information about concepts and models. We can either 
    store both in one table, or have separate tables 
    for concepts and models.

    For simplicity, we choose the second option. *)

(** Concept symbol table is a map from concept names
    to concept types [Ci -> CTi]. *)

Definition cptcontext : Type := partial_map cty.

(** Model symbol table is a map from model names
    to model types [Mi -> MTi]. *)

Definition mdlcontext : Type := partial_map mty.

(* ----------------------------------------------------------------- *)
(** **** Checking Concept Definitions *)

(* Examples / ---------------------------- *)
Module Examples_ConceptTypes.
  Export Examples.
  
  Definition CTnrevmap := CTdef (map_from_list [
    (FNmap, TArrow TNat TNat);                          
    (FNpam, TArrow TNat TNat)
  ]).
  
  Definition CTnmonoid := CTdef (map_from_list [
    (FNident, TNat);                          
    (FNop,    TArrow TNat TNat)
  ]).

  Definition CTempty : cty := CTdef (map_from_list []).

  Definition CTbad1 := CTdef (map_from_list [
    (FNmap, TArrow TNat TNat);                          
    (FNmap, TArrow TNat TNat)
  ]).

End Examples_ConceptTypes.
(* / Examples ---------------------------- *)

(** Concept definition is Ok if names of concept elements are
    distinct, and types of elements are valid.

    The only problem in types is with concept dependency [C # T]:
    if C is undefined concept name, type is not valid.
    So to check types validity, we need symbol table already.
*)

(** Now let's define a property "type is valid".
    This property must be checked againts concrete symbol table.
 *)

Definition concept_defined (st : cptcontext) (nm : id) : Prop := 
  st nm <> None.

Definition concept_defined_b (st : cptcontext) (nm : id) : bool :=
  match st nm with
  | None   => false
  | Some _ => true
  end.
  
Inductive type_valid (st : cptcontext) : ty -> Prop :=
  | type_valid_nat   : type_valid st TNat
  | type_valid_bool  : type_valid st TBool
  | type_valid_arrow : forall T1 T2,
      type_valid st T1 ->
      type_valid st T2 ->
      type_valid st (TArrow T1 T2)
  | type_valid_cpt   : forall C T,
      concept_defined st C ->
      type_valid st T ->
      type_valid st (TConceptPrm C T)
.

Hint Constructors type_valid. 

(** Now we are ready to define a property "concept is well defined" *)

Definition concept_welldefined (st : cptcontext) (C : conceptdef) : Prop :=
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

Fixpoint type_valid_b (st : cptcontext) (t : ty) : bool :=
  match t with
  | TNat  => true
  | TBool => true
  | TArrow t1 t2     => andb (type_valid_b st t1)  (type_valid_b st t2)
  | TConceptPrm c t1 => andb (concept_defined_b st c) (type_valid_b st t1)
  end.

Definition types_valid_b (st : cptcontext) (ts : list ty) : bool :=
  List.forallb (fun t => type_valid_b st t) ts.

(** And define a function to check that "concept is well defined" *)

Definition concept_welldefined_b (st : cptcontext) (C : conceptdef) : bool :=
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
  Import Examples_ConceptTypes.
  
  Example test_type_1 : type_valid stempty TNat.
  Proof.
    apply type_valid_nat.
  Qed.

  Definition tyNatBoolNat : ty := TArrow TNat (TArrow TBool TNat).
  
  Example test_type_2_1 : ~ (type_valid stempty (TConceptPrm CNnmonoid tyNatBoolNat)).
  Proof.
    intros H. inversion H; subst.
    unfold concept_defined in H2.
    assert (Hcontra : stempty CNnmonoid = None) by reflexivity.
    tryfalse.
  Qed.
  
  Example test_type_2_2 :
    type_valid (update stempty CNnmonoid CTnmonoid) (TConceptPrm CNnmonoid tyNatBoolNat).
  Proof.
    apply type_valid_cpt.
    + unfold concept_defined. intros Hnm. tryfalse.
    + apply type_valid_arrow; auto.
  Qed.
End TestTypes1.

Module TestTypes1_b. 
  Import Examples_ConceptTypes.
  
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

(** At this point we cannot do more on contexts. To check models,
    we have to be able to typecheck terms (function definitions). 
    But terms may conist of model applications.
 *)

(* ================================================================= *)
(** *** Typing of Terms *)

(** To typecheck terms we need:
    - context [Gamma], which (in contrast to STLC) contains not only
      variables, but also concept variables;      
    - concept symbol table [CTable];
    - model symbol table [MTable].
*)

(** Informal typing rules are listed below.
    
    We can read the five-place relation 
      [CTable * MTable ; Gamma |- t \in T] as:
    "to the term [t] we can assign the type [T],
     if types of free variables of [t] are specified in [Gamma],
     free concept variables of [t] are specified in [Gamma], 
     context types are specified in [CTable],
     model types are specified in [MTable]."

    [dom( * )]   is a domain of a map (map keys -- ids),
    [range( * )] is a range of a map (map values -- types).


                             Gamma \has x:T
                    --------------------------------                    (T_Var)
                    CTable * MTable ; Gamma |- x : T


                 CTable * MTable ; Gamma |- t1 : T11->T12
                  CTable * MTable ; Gamma |- t2 : T11
                 ----------------------------------------               (T_App)
                  CTable * MTable ; Gamma |- t1 t2 : T12


              CTable * MTable ; (Gamma , x:T11) |- t12 : T12
             ------------------------------------------------           (T_Abs)
             CTable * MTable ; Gamma |- \x:T11.t12 : T11->T12


- MTable contains info about model M
- Model M implements concept C
  (MTable(M) = ... of C ...)

                              M \in dom(MTable)
                         MTable(M) = ... of C ...
                 CTable * MTable ; Gamma |- t1 : (C # T1)
                 ----------------------------------------              (T_MApp)
                 CTable * MTable ; Gamma |- (t1 # M) : T1   


              CTable * MTable ; (Gamma , c#C) |- t1 : T1
             --------------------------------------------------        (T_CAbs)
             CTable * MTable ; Gamma |- \c#C.t1 : (C # T1)


- CTable contains info about concept C;
- C contains member f and its type is TF 
  (CTable(C) = ... f : TF ... )

                              Gamma \has c#C
                             C \in dom(CTable)
                        CTable(C) = ... f : TF ...
                   -----------------------------------                (T_CInvk)
                   CTable * MTable ; Gamma |- c.f : TF


                  ------------------------------------                 (T_True)
                 CTable * MTable ; Gamma |- true : Bool

                  ------------------------------------                (T_False)
                 CTable * MTable ; Gamma |- false : Bool


                  CTable * MTable ; Gamma |- t1 : Bool    
                   CTable * MTable ; Gamma |- t2 : T    
                   CTable * MTable ; Gamma |- t3 : T
            ---------------------------------------------------          (T_If)
           CTable * MTable ; Gamma |- if t1 then t2 else t3 : T


                  -------------------------------------                 (T_Nat)
                 CTable * MTable ; Gamma |- tnat n : Nat


                   CTable * MTable ; Gamma |- t1 : Nat
                ------------------------------------------             (T_Succ)
                CTable * MTable ; Gamma |- succ t1 : Nat

                   CTable * MTable ; Gamma |- t1 : Nat
                ------------------------------------------             (T_Pred)
                CTable * MTable ; Gamma |- pred t1 : Nat


                   CTable * MTable ; Gamma |- t1 : Nat
                   CTable * MTable ; Gamma |- t2 : Nat
                ----------------------------------------               (T_Plus)
                CTable * MTable ; Gamma |- t1 + t2 : Nat

                   CTable * MTable ; Gamma |- t1 : Nat
                   CTable * MTable ; Gamma |- t2 : Nat
                ----------------------------------------              (T_Minus)
                CTable * MTable ; Gamma |- t1 - t2 : Nat

                   CTable * MTable ; Gamma |- t1 : Nat
                   CTable * MTable ; Gamma |- t2 : Nat
                ---------------------------------------                (T_Mult)
                CTable * MTable ; Gamma |- t1 * t2 : Nat


                    CTable * MTable ; Gamma |- t1 : Nat
                    CTable * MTable ; Gamma |- t2 : Nat
                ------------------------------------------            (T_EqNat)
                 CTable * MTable ; Gamma |- t1 = t2 : Bool

                   CTable * MTable ; Gamma |- t1 : Nat
                   CTable * MTable ; Gamma |- t2 : Nat
                ------------------------------------------            (T_LeNat)
                CTable * MTable ; Gamma |- t1 <= t2 : Bool


                    CTable * MTable ; Gamma |- t1 : T1 
               CTable * MTable ; (Gamma , x:T1) |- t2 : T2
               ----------------------------------------------           (T_Let)
               CTable * MTable ; Gamma |- let x=t1 in t2 : T2
*)

(** In SLTC Gamma consists of only variable types, 
    but now it can also information about concept parameters.
*)

Inductive ctxvarty : Type :=
  (* type of term variable [x : T] -- normal type *)
| tmtype  : ty -> ctxvarty
  (* type of concept parameter [c # C] -- concept name *)
| cpttype : id -> ctxvarty
.

Definition context : Type := partial_map ctxvarty.

Reserved Notation "CTable '*' MTable ';' Gamma '|-' t '\in' T" (at level 40).

Definition concept_fun_member (CTable : cptcontext) (C : id) (f : id) (TF : ty) : Prop :=
  match CTable C with
  | None => False
  | Some (CTdef fundefs) => find_ty f fundefs = Some TF
  end.

(* 
Inductive mty : Type :=
  MTdef : id -> id_tm_map -> mty 

mdlcontext = partial_map mty
     : Type

*)
Inductive has_type : cptcontext -> mdlcontext -> context -> tm -> ty -> Prop :=
  | T_Var   : forall CTable MTable Gamma x T,
      Gamma x = Some (tmtype T) ->
      CTable * MTable ; Gamma |- tvar x \in T
  | T_App   : forall CTable MTable Gamma t1 t2 T11 T12,
      CTable * MTable ; Gamma |- t1 \in T11 ->
      CTable * MTable ; Gamma |- t2 \in T12 ->                 
      CTable * MTable ; Gamma |- tapp t1 t2 \in T12
  | T_Abs   : forall CTable MTable Gamma x t12 T11 T12,
      CTable * MTable ; (update Gamma x (tmtype T11)) |- t12 \in T12 ->                 
      CTable * MTable ; Gamma |- tabs x T11 t12 \in T12
  | T_MApp  : forall CTable MTable Gamma t1 M C Mbody T1,
      MTable M = Some (MTdef C Mbody) ->
      CTable * MTable ; Gamma |- t1 \in TConceptPrm C T1 ->
      CTable * MTable ; Gamma |- tmapp t1 M \in T1
  | T_CAbs  : forall CTable MTable Gamma c t1 C T1,
      CTable * MTable ; (update Gamma c (cpttype C)) |- t1 \in T1 ->
      CTable * MTable ; Gamma |- tcabs c C t1 \in TConceptPrm C T1
  | T_CInvk : forall CTable MTable Gamma c f C TF,
      Gamma c = Some (cpttype C) ->
      concept_fun_member CTable C f TF ->
      CTable * MTable ; Gamma |- tcinvk c f \in TF
  | T_True  : forall CTable MTable Gamma,
      CTable * MTable ; Gamma |- ttrue \in TBool
  | T_False : forall CTable MTable Gamma,
      CTable * MTable ; Gamma |- tfalse \in TBool
  | T_If    : forall CTable MTable Gamma t1 t2 t3 T,
      CTable * MTable ; Gamma |- t1 \in TBool ->
      CTable * MTable ; Gamma |- t2 \in T ->
      CTable * MTable ; Gamma |- t3 \in T ->
      CTable * MTable ; Gamma |- tif t1 t2 t3 \in T
  | T_Nat   : forall CTable MTable Gamma n,
      CTable * MTable ; Gamma |- tnat n \in TNat
  | T_Succ   : forall CTable MTable Gamma t1,
      CTable * MTable ; Gamma |- t1 \in TNat ->
      CTable * MTable ; Gamma |- tsucc t1 \in TNat                                                    | T_Pred   : forall CTable MTable Gamma t1,
      CTable * MTable ; Gamma |- t1 \in TNat ->
      CTable * MTable ; Gamma |- tpred t1 \in TNat                                                    | T_Plus   : forall CTable MTable Gamma t1 t2,
      CTable * MTable ; Gamma |- t1 \in TNat ->
      CTable * MTable ; Gamma |- t2 \in TNat ->
      CTable * MTable ; Gamma |- tplus t1 t2 \in TNat                                                 | T_Minus  : forall CTable MTable Gamma t1 t2,
      CTable * MTable ; Gamma |- t1 \in TNat ->
      CTable * MTable ; Gamma |- t2 \in TNat ->
      CTable * MTable ; Gamma |- tminus t1 t2 \in TNat                                                | T_Mult   : forall CTable MTable Gamma t1 t2,
      CTable * MTable ; Gamma |- t1 \in TNat ->
      CTable * MTable ; Gamma |- t2 \in TNat ->
      CTable * MTable ; Gamma |- tmult t1 t2 \in TNat                                                 | T_EqNat  : forall CTable MTable Gamma t1 t2,
      CTable * MTable ; Gamma |- t1 \in TNat ->
      CTable * MTable ; Gamma |- t2 \in TNat ->
      CTable * MTable ; Gamma |- teqnat t1 t2 \in TBool                                               | T_LeNat  : forall CTable MTable Gamma t1 t2,
      CTable * MTable ; Gamma |- t1 \in TNat ->
      CTable * MTable ; Gamma |- t2 \in TNat ->
      CTable * MTable ; Gamma |- tlenat t1 t2 \in TBool                                               | T_Let    : forall CTable MTable Gamma x t1 t2 T1 T2,
      CTable * MTable ; Gamma |- t1 \in T1 ->
      CTable * MTable ; (update Gamma x (tmtype T1)) |- t2 \in T2 ->
      CTable * MTable ; Gamma |- tlet x t1 t2 \in T2                          

where "CTable '*' MTable ';' Gamma '|-' t '\in' T"
      := (has_type CTable MTable Gamma t T).

Hint Constructors has_type.

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

(** Model definition is Ok if:
    - concept name is defined;
    - all concept members are defined in a model;
    - model member types coincide with concept member types.
*)

(** Now let's define a property "type is valid".
    This property must be checked againts concrete symbol table.
 *)

Definition model_defined (st : mdlcontext) (nm : id) : Prop := 
  st nm <> None.

Definition model_defined_b (st : mdlcontext) (nm : id) : bool :=
  match st nm with
  | None   => false
  | Some _ => true
  end.

(*
Inductive type_valid (st : cptcontext) : ty -> Prop :=
  | type_valid_nat   : type_valid st TNat
  | type_valid_bool  : type_valid st TBool
  | type_valid_arrow : forall T1 T2,
      type_valid st T1 ->
      type_valid st T2 ->
      type_valid st (TArrow T1 T2)
  | type_valid_cpt   : forall C T,
      concept_defined st C ->
      type_valid st T ->
      type_valid st (TConceptPrm C T)
.

Hint Constructors type_valid. 

(** Now we are ready to define a property "concept is well defined" *)

Definition concept_welldefined (st : cptcontext) (C : conceptdef) : Prop :=
  match C with
    cpt_def cname cbody =>
    let (fnames, ftypes) := split (map namedecl_to_pair cbody) in
    (** all names are distinct *)
    List.NoDup fnames
    (** and all types are valid *)
    /\ List.Forall (fun ftype => type_valid st ftype) ftypes            
  end.

Hint Unfold concept_welldefined.
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
