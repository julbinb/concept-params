(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(* Simply Typed Lambda Calculus with simple Concept Parameters
   :: version a

   Definitions of STLC are based on
   Sofware Foundations, v.4 
  
   Last Update: Wed, 18 Jan 2017
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

Require Import ConceptParams.BasicPLDefs.Utils.

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


    Types are STLC types with the type [C # T], 
    where [C] is a concept name, [T] is a type.

    Terms are STLC terms with the terms:
    - [\c#C. t] (concept parametrization) where [c] is a concept parameter;
    - [t # M] (model application) where [M] is a model.

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

Fixpoint beq_ty (T1 T2 : ty) : bool :=
  match T1, T2 with
  | TBool, TBool => true
  | TNat,  TNat  => true 
  | TArrow T11 T12, TArrow T21 T22 =>
      andb (beq_ty T11 T21) (beq_ty T12 T22)
  | TConceptPrm C1 T1, TConceptPrm C2 T2 =>
      andb (beq_id C1 C2) (beq_ty T1 T2)
  | _, _ => false
  end.

Lemma beq_ty_refl : forall T1, beq_ty T1 T1 = true.
Proof.
  intros T1. induction T1; (simpl; auto).
  - (* T1 -> T2 *)
    rewrite -> IHT1_1. rewrite -> IHT1_2. reflexivity.
  - (* C # T *)
    rewrite -> IHT1. rewrite <- beq_id_refl. reflexivity.
Qed.

Lemma beq_ty__eq : forall T1 T2,
    beq_ty T1 T2 = true -> T1 = T2.
Proof.
  intros T1. induction T1;
  (intros T2; induction T2; intros H);
    (* in some cases it's just reflexivity *)
    try reflexivity;
    (* in other cases we have impossible equalities as assumptions 
       (such as TNat = TBool) *)
    try solve_by_invert.
  - (* T1_1 -> T1_2 = T2_1 -> T2_2 *)
    simpl in H. apply andb_true_iff in H.
    inversion H as [H1 H2].
    apply IHT1_1 in H1. apply IHT1_2 in H2.
    subst. reflexivity.
  - (* C1 # T1 = C2 # T2 *)
    simpl in H. apply andb_true_iff in H.
    inversion H as [HC HT].
    rewrite -> beq_id_true_iff in HC. subst.
    apply IHT1 in HT. subst.
    reflexivity.
Qed.  

Lemma beq_tyP : forall T1 T2, reflect (T1 = T2) (beq_ty T1 T2).
Proof.
  intros T1 T2. 
  apply iff_reflect. split.
  - (* T1 = T2 -> beq_ty T1 T2 = true *)
    intros H. 
    destruct T1; destruct T2;
      (* in simple cases reflexivity *)
      try reflexivity;
      (* some cases give contra in assumption *)
      try (inversion H).
    + (* T2_1 -> T2_2 = T2_1 -> T2_2 *)
      simpl. apply andb_true_iff. split.
      apply beq_ty_refl. apply beq_ty_refl.
    + (* C # T2 = C # T2 *)
      rename i0 into C. simpl. apply andb_true_iff. split.
      symmetry. apply beq_id_refl. apply beq_ty_refl. 
  - (* beq_ty T1 T2 = true -> T1 = T2 *)
    apply beq_ty__eq.
Qed.

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

Definition conceptdef__get_name (C : conceptdef) : id :=
  match C with cpt_def nm nmdecls => nm end.

(** Concept declarations Section *)

Definition conceptsec : Type := list conceptdef.
Hint Unfold conceptsec.

(* ----------------------------------------------------------------- *)
(** **** Models *)

(** Name definition *)

Inductive namedef : Type :=
  | nm_def : id -> tm -> namedef   (* f = t *)
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

(** There are examples of concepts and programs in [cpSTLCa_Examples.v]. *)

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

(** Concept type *)
Inductive cty : Type := CTdef : id_ty_map -> cty.

Definition find_ty := mids_find ty.
Hint Unfold find_ty.

Definition beq_cty (CT1 CT2 : cty) : bool :=
  match CT1, CT2 with
    CTdef c1, CTdef c2 => IdMap.equal beq_ty c1 c2            
  end.

(*Lemma beq_cty_refl : forall CT1, beq_cty CT1 CT1 = true.
Proof.
  intros CT1. induction CT1; simpl.
  apply IdMap.equal_1.
  unfold IdMap.Equivb. unfold IdMap.Equiv.
Qed.*)

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

(** Model type *)
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
Definition cstempty : cptcontext := @empty cty.

(** Model symbol table is a map from model names
    to model types [Mi -> MTi]. *)

Definition mdlcontext : Type := partial_map mty.
Definition mstempty : mdlcontext := @empty mty.

(* ================================================================= *)
(** *** Checking Types Validity *)

(* ----------------------------------------------------------------- *)
(** **** Checking Concept Definitions *)

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

(** We have a symbol table for concepts, concept types, but
    we have not defined yet a relation on concept definitions and
    concept types. *)

Definition concept_has_type (cst : cptcontext) (C : conceptdef) (CT : cty) : Prop :=
  (** concept def must be well-defined *)
  concept_welldefined cst C
  /\  match C  with cpt_def cname cbody =>
      match CT with CTdef  cnmtys =>   
  (** all concept members are reflected in a concept type *)      
        List.Forall (fun nmdecl => match nmdecl with nm_decl f T =>
                         find_ty f cnmtys = Some T end) cbody
  (** amount of concept members is the same as in the concept type *)
        /\ List.length cbody = IdMap.cardinal cnmtys
      end end.

(** And we now need an algorithmical way to find type of a concept. *)

Definition concept_type_check (cst : cptcontext) (C : conceptdef) : option cty :=
  if concept_welldefined_b cst C 
  then match C with cpt_def cname cbody =>
      let cbody' := map namedecl_to_pair cbody in
      Some (CTdef (map_from_list cbody'))
  end
  else 
    None.

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


                              C \in dom(CTable)
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
    but now it can also have information about concept parameters.
*)

Inductive ctxvarty : Type :=
  (* type of term variable [x : T] -- normal type *)
| tmtype  : ty -> ctxvarty
  (* type of concept parameter [c # C] -- concept name *)
| cpttype : id -> ctxvarty
.

Definition context : Type := partial_map ctxvarty.
Definition ctxempty : context := @empty ctxvarty.

(** Aux function for typing relation *)
Definition concept_fun_member (CTable : cptcontext) (C : id) (f : id) (TF : ty) : Prop :=
  match CTable C with
  | None => False
  | Some (CTdef fundefs) => find_ty f fundefs = Some TF
  end.

Reserved Notation "CTable '$' MTable ';' Gamma '|-' t '\in' T" (at level 50).

(** Here is our typing relation for cpSTLCa terms. *)

Inductive has_type : cptcontext -> mdlcontext -> context -> tm -> ty -> Prop :=
  | T_Var   : forall CTable MTable Gamma x T,
      Gamma x = Some (tmtype T) ->
      CTable $ MTable ; Gamma |- tvar x \in T
  | T_App   : forall CTable MTable Gamma t1 t2 T11 T12,
      CTable $ MTable ; Gamma |- t1 \in T11 ->
      CTable $ MTable ; Gamma |- t2 \in T12 ->                 
      CTable $ MTable ; Gamma |- tapp t1 t2 \in T12
  | T_Abs   : forall CTable MTable Gamma x t12 T11 T12,
      CTable $ MTable ; (update Gamma x (tmtype T11)) |- t12 \in T12 ->        
      CTable $ MTable ; Gamma |- tabs x T11 t12 \in T12
  | T_MApp  : forall CTable MTable Gamma t1 M C Mbody T1,
      MTable M = Some (MTdef C Mbody) ->
      CTable $ MTable ; Gamma |- t1 \in TConceptPrm C T1 ->
      CTable $ MTable ; Gamma |- tmapp t1 M \in T1
  | T_CAbs  : forall CTable MTable Gamma c t1 C Cbody T1,
      CTable C = Some (CTdef Cbody) ->
      CTable $ MTable ; (update Gamma c (cpttype C)) |- t1 \in T1 ->
      CTable $ MTable ; Gamma |- tcabs c C t1 \in TConceptPrm C T1
  | T_CInvk : forall CTable MTable Gamma c f C TF,
      Gamma c = Some (cpttype C) ->
      concept_fun_member CTable C f TF ->
      CTable $ MTable ; Gamma |- tcinvk c f \in TF
  | T_True  : forall CTable MTable Gamma,
      CTable $ MTable ; Gamma |- ttrue \in TBool
  | T_False : forall CTable MTable Gamma,
      CTable $ MTable ; Gamma |- tfalse \in TBool
  | T_If    : forall CTable MTable Gamma t1 t2 t3 T,
      CTable $ MTable ; Gamma |- t1 \in TBool ->
      CTable $ MTable ; Gamma |- t2 \in T ->
      CTable $ MTable ; Gamma |- t3 \in T ->
      CTable $ MTable ; Gamma |- tif t1 t2 t3 \in T
  | T_Nat   : forall CTable MTable Gamma n,
      CTable $ MTable ; Gamma |- tnat n \in TNat
  | T_Succ   : forall CTable MTable Gamma t1,
      CTable $ MTable ; Gamma |- t1 \in TNat ->
      CTable $ MTable ; Gamma |- tsucc t1 \in TNat
  | T_Pred   : forall CTable MTable Gamma t1,
      CTable $ MTable ; Gamma |- t1 \in TNat ->
      CTable $ MTable ; Gamma |- tpred t1 \in TNat 
  | T_Plus   : forall CTable MTable Gamma t1 t2,
      CTable $ MTable ; Gamma |- t1 \in TNat ->
      CTable $ MTable ; Gamma |- t2 \in TNat ->
      CTable $ MTable ; Gamma |- tplus t1 t2 \in TNat 
  | T_Minus  : forall CTable MTable Gamma t1 t2,
      CTable $ MTable ; Gamma |- t1 \in TNat ->
      CTable $ MTable ; Gamma |- t2 \in TNat ->
      CTable $ MTable ; Gamma |- tminus t1 t2 \in TNat      
  | T_Mult   : forall CTable MTable Gamma t1 t2,
      CTable $ MTable ; Gamma |- t1 \in TNat ->
      CTable $ MTable ; Gamma |- t2 \in TNat ->
      CTable $ MTable ; Gamma |- tmult t1 t2 \in TNat        
  | T_EqNat  : forall CTable MTable Gamma t1 t2,
      CTable $ MTable ; Gamma |- t1 \in TNat ->
      CTable $ MTable ; Gamma |- t2 \in TNat ->
      CTable $ MTable ; Gamma |- teqnat t1 t2 \in TBool    
  | T_LeNat  : forall CTable MTable Gamma t1 t2,
      CTable $ MTable ; Gamma |- t1 \in TNat ->
      CTable $ MTable ; Gamma |- t2 \in TNat ->
      CTable $ MTable ; Gamma |- tlenat t1 t2 \in TBool 
  | T_Let    : forall CTable MTable Gamma x t1 t2 T1 T2,
      CTable $ MTable ; Gamma |- t1 \in T1 ->
      CTable $ MTable ; (update Gamma x (tmtype T1)) |- t2 \in T2 ->
      CTable $ MTable ; Gamma |- tlet x t1 t2 \in T2                          

where "CTable '$' MTable ';' Gamma '|-' t '\in' T"
      := (has_type CTable MTable Gamma t T) : stlca_scope.

Hint Constructors has_type.

(** And the corresponding typechecker. *)

(** Looks for _term_ type of [x] in context [Gamma]. *)
Definition context_get_type (Gamma : context) (x : id) : option ty :=
  option_handle (Gamma x)
                (fun (ctx_ty : ctxvarty) 
                 => match ctx_ty with | tmtype T => Some T | _ => None end)
                None.

(** Looks for _concept_ type of [C] in context [Gamma]. *)
Definition context_get_concept (CTable : cptcontext) 
                               (Gamma : context) (c : id) : option cty :=
  option_handle (Gamma c)
                (fun (ctx_ty : ctxvarty) 
                 => match ctx_ty with | cpttype C => CTable C | _ => None end)
                None.

(** The type checking function. *)
Fixpoint type_check (CTable : cptcontext) (MTable : mdlcontext)
         (Gamma : context) (t : tm) : option ty :=
  let tycheck := type_check CTable MTable in
  let process_nat_un := fun (t1 : tm) =>
                          match tycheck Gamma t1 with
                          | Some TNat => Some TNat
                          | _ => None
                          end in
  let process_nat_bin := fun (t1 t2 : tm) =>
                           match tycheck Gamma t1, tycheck Gamma t2 with
                           | Some TNat, Some TNat => Some TNat
                           | _, _ => None
                           end in
  let process_nat_bin_bool := fun (t1 t2 : tm) =>
                           match tycheck Gamma t1, tycheck Gamma t2 with
                           | Some TNat, Some TNat => Some TBool
                           | _, _ => None
                           end in
  match t with
  | tvar x => 
      (* there must be x : T \in Gamma *)
      context_get_type Gamma x
  | tapp t1 t2 => 
      (* if t1 : T11 -> T12, t2 : T11, then (t1 t2) : T12 *)
      match tycheck Gamma t1, tycheck Gamma t2 with
        | Some (TArrow T11 T12), Some T2 => 
          if beq_ty T11 T2 then Some T12 else None
        | _ , _=> None
      end
  | tabs x T11 t12 =>
      (* if t12 : T12 in (Gamma, x:T11), then \x:T11.t12 : T11 -> T12  *)
      match tycheck (update Gamma x (tmtype T11)) t12 with
      | Some T12 => Some (TArrow T11 T12)
      | _ => None
      end
  | tmapp t1 M =>
      (* if t1 : C # T1 and M defines concept C, then (t1 # M) : T1 *)
      match tycheck Gamma t1, MTable M with
        | Some (TConceptPrm C T1), Some (MTdef C' Mbody) => 
          if beq_id C C' then Some T1 else None
        | _, _ => None
      end
  | tcabs c C t1 =>
      (* if C is known concept, and t1 : T1 in (Gamma, c:C), then
         \c#C.t1 : C # T1 *)
      match CTable C, tycheck (update Gamma c (cpttype C)) t1 with
        | Some CT, Some T1 => Some (TConceptPrm C T1)
        | _, _ => None
      end
  | tcinvk c f =>
      (* if c:C \in Gamma, C:CT \in CTable, and f:TF \in CT,
         then c.f : TF *)
      match context_get_concept CTable Gamma c with
      | Some (CTdef Cbody) => find_ty f Cbody 
      | None => None
      end
  | ttrue  => Some TBool
  | tfalse => Some TBool
  | tif t1 t2 t3 =>
      let tycheck' := tycheck Gamma in
      match tycheck' t1, tycheck' t2, tycheck' t3 with
      | Some TBool, Some T, Some T' => if beq_ty T T' then Some T else None
      | _, _, _ => None
      end
  | tnat n   => Some TNat
  | tsucc t1 => process_nat_un t1
  | tpred t1 => process_nat_un t1
  | tplus  t1 t2 => process_nat_bin t1 t2
  | tminus t1 t2 => process_nat_bin t1 t2
  | tmult  t1 t2 => process_nat_bin t1 t2
  | teqnat t1 t2 => process_nat_bin_bool t1 t2
  | tlenat t1 t2 => process_nat_bin_bool t1 t2
  | tlet x t1 t2 =>
      (* if t1 : T1 and t2 : T2 \in (Gamma, x:T1), 
         then (let x=t1 in t2) : T2 *)
      match tycheck Gamma t1 with
      | Some T1 => match tycheck (update Gamma x (tmtype T1)) t2 with
                     | Some T2 => Some T2 | _ => None 
                   end
      | _ => None
      end
  end. 

(* ----------------------------------------------------------------- *)
(** **** Checking Model Definitions *)

(** Model definition is Ok if:
    - concept name is defined;
    - all concept members are defined in a model;
    - model member types coincide with concept member types.
*)

Definition model_defined (st : mdlcontext) (nm : id) : Prop := 
  st nm <> None.

Definition model_defined_b (st : mdlcontext) (nm : id) : bool :=
  match st nm with
  | None   => false
  | Some _ => true
  end.

(** [model_member_valid] is a proposition stating that the given
    model member [nd] (name definition, [f := t]) is valid against
    a concept with members [fntys] (name declarations, [f : T]).
*)

Definition model_member_valid (cst : cptcontext) (mst : mdlcontext)
                              (fnmtys : id_ty_map) (nd : namedef) : Prop :=
  match nd with nm_def nm t =>
    exists (T : ty),
    (** there is [nm : T] in a concept *)
    find_ty nm fnmtys = Some T
    (** and [T] is a type of [t], that is [cst * mst ; empty |- t : T] *)
    /\ has_type cst mst ctxempty t T
  end.

(** And [model_member_valid_b] is a corresponding function to
    check member's validity. *)

Definition model_member_valid_b (cst : cptcontext) (mst : mdlcontext)
                                (fnmtys : id_ty_map) (nd : namedef) : bool :=
  match nd with nm_def nm t =>
    (** there is [nm : T] in a concept *)
    match find_ty nm fnmtys with
    (** and [T] is a type of [t], that is [cst * mst ; empty |- t : T] *)
    | Some T => match type_check cst mst ctxempty t with
                  | Some T' => if beq_ty T T' then true else false
                  | _ => false  end
    | _ => false
  end end.

(** Now we are ready to formally define what it means for a model
    to be well-defined. *)

Definition model_welldefined (cst : cptcontext) (mst : mdlcontext) (M : modeldef) : Prop :=
  match M with 
    mdl_def mname C mbody =>
    let (fnames, fterms) := split (map namedef_to_pair mbody) in
    (** concept is defined in symbol table *)
    concept_defined cst C
    (** fnmtys is a map from C ids to their types *)
    /\ (exists fnmtys : id_ty_map, cst C = Some (CTdef fnmtys)
    (** model members are the same as concept members *)
       /\ let fnmtys_list := mids_elements ty fnmtys in
          let Cfnames := List.map fst fnmtys_list in
          IdSet.Equal (set_from_list fnames) (set_from_list Cfnames)
    (** types of model member terms conincide with 
        concept member types *)
       /\ List.Forall (model_member_valid cst mst fnmtys) mbody
    (** amount of concept members is the same as model members
        (together with previous condition it means that 
        all concept members are defined correctly in a model) *)     
       /\ IdMap.cardinal fnmtys = List.length mbody)
  end.

Hint Unfold model_welldefined.

(** And we define a function to check that "model is well defined" *)

Definition model_welldefined_b (cst : cptcontext) (mst : mdlcontext) 
           (M : modeldef) : bool :=
  match M with 
    mdl_def mname C mbody =>
    match (cst C) with
    (** concept is defined in symbol table *)
    | Some (CTdef fnmtys) =>
      let (fnames, fterms) := split (map namedef_to_pair mbody) in
    (** model members are the same as concept members *)
      let fnmtys_list := mids_elements ty fnmtys in
      let Cfnames := List.map fst fnmtys_list in
      andb
        (IdSet.equal (set_from_list fnames) (set_from_list Cfnames))
      (andb
    (** types of model member terms conincide with 
        concept member types *)
        (forallb (model_member_valid_b cst mst fnmtys) mbody)
    (** amount of concept members is the same as model members
        (together with previous condition it means that 
        all concept members are defined correctly in a model) *)  
        (beq_nat (IdMap.cardinal fnmtys) (List.length mbody)))
    | _ => false     
  end end.

(** And we also need typing relation for models. *)

Definition model_has_type (cst : cptcontext) (mst : mdlcontext) 
           (M : modeldef) (MT : mty) : Prop :=
  (** model def must be well-defined *)
  model_welldefined cst mst M
  /\  match M  with mdl_def mname C mbody =>
      match MT with MTdef C' mnmtms =>   
  (** a concept defined by model coincides with the concept in type *)
        C = C'
  (** all model members are reflected in the model type *)      
        /\ List.Forall (fun nmdef => match nmdef with nm_def f t =>
                        find_tm f mnmtms = Some t end) mbody
  (** amount of model members is the same as in the model type *)
        /\ List.length mbody = IdMap.cardinal mnmtms
      end end.

(** And we now need an algorithmical way to find type of a model. *)

Definition model_type_check (cst : cptcontext) (mst : mdlcontext) 
           (M : modeldef) : option mty :=
  if model_welldefined_b cst mst M
  then match M with mdl_def mname C mbody =>
       let mbody' := map namedef_to_pair mbody in
       Some (MTdef C (map_from_list mbody'))
  end
  else 
    None.

(* ----------------------------------------------------------------- *)
(** **** Checking Programs *)

(** Now we can write down what it means for the whole program 
    to be well-defined. *)

(* Inductive program : Type :=  tprog : conceptsec -> modelsec -> tm -> program *)

(** First, concept section (list of concept definitions) is to be 
    well-formed. 
    That is there is a symbol table of concepts such that
    - all concepts in the section are well-defined against it;
    - symbol table contains appropriate concept types. *)

Definition conceptsec_welldefined (cptsec : conceptsec) (cst : cptcontext) : Prop :=
  (*Forall (fun (C : conceptdef) => concept_welldefined cst C) cptsec
  /\ Forall (fun (C : conceptdef) => cst (conceptdef__get_name C) <> None) cptsec*)
  Forall (fun (C : conceptdef) => 
            (concept_welldefined cst C)
            /\ (exists (CT : cty),
                   (* concept symb. table contains info about the type of C *)
                   cst (conceptdef__get_name C) = Some CT 
                   (* and C indeed has this type *)
                   /\ concept_has_type cst C CT)
         ) cptsec. 

Definition conceptsec_welldefined_b (cptsec : conceptsec) : cptcontext * bool :=
(* use fold_left to pass the right context along the check *)
  fold_left 
    (fun (acc : cptcontext * bool) (C : conceptdef) =>
       let (cst, correct) := acc
       in if correct then 
            let ctp := concept_type_check cst C
            in match ctp with
                 | Some CT => (update cst (conceptdef__get_name C) CT, true)
                 | None    => (cstempty, false)
               end 
          else (cstempty, false)
    )
    cptsec (cstempty, true).

(** First, model section (list of model definitions) is also 
    to be well-formed. 
    That is there is a symbol table of models such that
    - all models in the section are well-defined against it;
    - symbol table contains appropriate concept types. *)

Definition modelsec_welldefined 
           (mdlsec : modelsec) (cst : cptcontext) (mst : mdlcontext) : Prop :=
(* TODO *)
  Forall (fun (M : modeldef) =>
            (model_welldefined cst mst M)
            /\ (exists (MT : mty),
                   True)
         ) mdlsec.

(** And, finally, we can define program correctness *)

Definition program_correct (prg : program) 
           (cst : cptcontext) (mst : mdlcontext) (T : ty) : Prop :=
  match prg with tprog cptsec mdlsec t =>
    (** All concepts are well_defined *)
    conceptsec_welldefined cptsec cst 
    (** All models are well defined *)
    /\ modelsec_welldefined mdlsec cst mst
    (** Term is well typed *)
    /\ has_type cst mst ctxempty t T
  end.



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
