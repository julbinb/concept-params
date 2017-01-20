(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(* Simply Typed Lambda Calculus with simple Concept Parameters
   :: version a
   Definitions

   Definitions of STLC are based on
   Sofware Foundations, v.4 
  
   Last Update: Thu, 19 Jan 2017
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

Definition modeldef__get_name (M : modeldef) : id :=
  match M with mdl_def nm C nmdefs => nm end.

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

(* ----------------------------------------------------------------- *)
(** **** Checking Model Definitions *)

(** Model definition is Ok if:
    - concept name is defined;
    - all concept members are defined in a model;
    - model member types coincide with concept member types.
*)

Definition model_defined (st : mdlcontext) (nm : id) : Prop := 
  st nm <> None.

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

(** And we also need typing relation for models. *)

Definition model_has_type (cst : cptcontext) (mst : mdlcontext) 
           (M : modeldef) (MT : mty) : Prop :=
  (** model def must be well-defined *)
  model_welldefined cst mst M
  /\  match M  with mdl_def mname C mbody =>
      match MT with MTdef C' mnmtms =>   
  (** a concept defined by model coincides with the concept in the type *)
        C = C'
  (** all model members are reflected in the model type *)      
        /\ List.Forall (fun nmdef => match nmdef with nm_def f t =>
                        find_tm f mnmtms = Some t end) mbody
  (** amount of model members is the same as in the model type *)
        /\ List.length mbody = IdMap.cardinal mnmtms
      end end.

(** _Note!_ No any evaluation is applied to model members (terms). 
    So model members have to be exactly reflected in the model type,
    that is have exactly the same syntactic structure.  *)

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
                   (* concept symb. table contains info about type of C *)
                   cst (conceptdef__get_name C) = Some CT 
                   (* and C indeed has this type *)
                   /\ concept_has_type cst C CT)
         ) cptsec. 

(** First, model section (list of model definitions) is also 
    to be well-formed. 
    That is there is a symbol table of models such that
    - all models in the section are well-defined against it;
    - symbol table contains appropriate concept types. *)

Definition modelsec_welldefined 
           (mdlsec : modelsec) (cst : cptcontext) (mst : mdlcontext) : Prop :=
  Forall (fun (M : modeldef) =>
            (* model is welldefined *)
            (model_welldefined cst mst M)
            /\ (exists (MT : mty),
                   (* model symb. table contains info about type of M *)
                   mst (modeldef__get_name M) = Some MT
                   (* and M indeed has this type *)
                   /\ model_has_type cst mst M MT)
         ) mdlsec.

(** And, finally, we can define what it means for the whole _program_
    to be well-typed (correct). *)

Definition program_has_type (cst : cptcontext) (mst : mdlcontext)
           (prg : program) (T : ty) : Prop :=
  match prg with tprog cptsec mdlsec t =>
    (** All concepts are well defined *)
    conceptsec_welldefined cptsec cst 
    (** All models are well defined *)
    /\ modelsec_welldefined mdlsec cst mst
    (** Term is well typed *)
    /\ has_type cst mst ctxempty t T
  end.


(* ################################################################# *)
(** ** Operational Semantics *)

(* ================================================================= *)
(** *** Values *)

(** We start with defining the values of our language. *)

(** There are several "standard" categories of values:

    - boolean constants [true] and [false];
    - numbers [nat n];
    - abstractions (functions) [\x:T.t].

    But in cpSTLCa there is one more kind of abstraction:
    concept parameters. We consider it as a value too.
*)

Inductive value : tm -> Prop :=
  | v_abs  : forall x T t,
      value (tabs x T t)
  | v_cabs : forall c C t,
      value (tcabs c C t)
  | v_true :
      value ttrue
  | v_false :
      value tfalse
  | v_nat : forall n,
      value (tnat n).

Hint Constructors value.

(* ================================================================= *)
(** *** Substitution *)

(** Apparently, to evaluate terms of cpSTLCa we need not only usual
    terms substitution, but also models subsitution. *)

(* ----------------------------------------------------------------- *)
(** **** Free Variables *)

(** To define substitution, we will need free variables and free. *)


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


(* ================================================================= *)
(** *** Reduction (Small-step operational semantics) *)

(** What is the form of reduction relation in cpSTLCa? 

    We will definitely need to keep track the information from 
    symbol tables of concept and models.
    
    So, instead of usual [t ==> t']
    we have
                    [CTable * MTable ; t ==> t']


    In the inference rules we use two kinds of substitution:

    [x:=s] t -- substitution, variable substitution 
                (variable [x] is substituted with term [s] in term [t])

    [#c:=M] t -- concept substitution
                 (concept parameter [c] is substituted with 
                  model [M] in term [t])


    Here are the rules:

    tvar x
      no rules

    tapp t1 t2

                               value v2
             -------------------------------------------            (ST_AppAbs)
             CTbl * MTbl ; (\x:T.t12) v2 ==> [x:=v2] t12

                        CTble * MTbl ; t1 ==> t1'
                     ------------------------------                   (ST_App1)
                     CTbl * MTbl ; t1 t2 ==> t1' t2

                              value v1
                        CTbl * MTbl ; t2 ==> t2'
                     ------------------------------                   (ST_App2)
                     CTbl * MTbl ; v1 t2 ==> v1 t2'


    tabs x T11 t12  (\x:T11.t12)
      no rules

    tmapp t1 M      (t1 # M)

                           M \in dom(MTbl)
                        MTble(M) implements C
              ------------------------------------------          (ST_MAppCAbs)
                CTbl * MTbl ; (\c#C.t) M ==> [#c:=M] t

                       CTble * MTbl ; t1 ==> t1'
                    --------------------------------                 (ST_MApp1)
                    CTbl * MTbl ; t1 # M ==> t1' # M
    

    tcabs c C t1    (\c#C.t1)
      no rules
 
    tcinvk M f      (M.f)

      member invocation can be evaluated only if a model name 
      is used as a receiver, so we write M.f instead of c.f

                           M \in dom(MTbl)
                        f \in names(MTbl(M))
                          MTble(M)(f) = tf
                     ---------------------------                     (ST_CInvk)
                      CTbl * MTbl ; M.f ==> tf

    ttrue
      no rules

    tfalse
      no rules

    tif t1 t2 t3    (if t1 then t2 else t3)
    
             ----------------------------------------------         (ST_IfTrue)
              CTbl * MTbl ; if true then t1 else t2 ==> t1

            -----------------------------------------------        (ST_IfFalse)
             CTbl * MTbl ; if false then t1 else t2 ==> t2

                      CTbl * MTbl ; t1 ==> t1'
   ------------------------------------------------------------------   (ST_If)
   CTbl * MTbl ; (if t1 then t2 else t3) ==> (if t1' then t2 else t3)


    tnat n
      no rules

    tsucc t1        (succ t1)
    
              ------------------------------------------            (ST_SuccNV)
              CTbl * MTbl ; succ (tnat n) ==> tnat (S n)

                      CTbl * MTbl ; t1 ==> t1'
                ------------------------------------                  (ST_Succ)
                 CTbl * MTbl ; succ t1 ==> succ t1'    


    tpred t1        (pred t1)

              --------------------------------------              (ST_PredZero)
              CTbl * MTbl ; pred (tnat 0) ==> tnat 0

             ------------------------------------------           (ST_PredSucc)
             CTbl * MTbl ; pred (tnat (S n)) ==> tnat n

                      CTbl * MTbl ; t1 ==> t1'
                ------------------------------------                  (ST_Pred)
                 CTbl * MTbl ; pred t1 ==> pred t1' 


    tplus t1 t2     (plus t1 t2)

       ---------------------------------------------------------    (ST_PlusNV)
       CTbl * MTbl ; plus (tnat n1) (tnat n2) ==> tnat (n1 + n2)

                      CTbl * MTbl ; t1 ==> t1'
               ----------------------------------------              (ST_Plus1)
               CTbl * MTbl ; plus t1 t2 ==> plus t1' t2 

                              value v1
                      CTbl * MTbl ; t2 ==> t2'
               ----------------------------------------              (ST_Plus2)
               CTbl * MTbl ; plus v1 t2 ==> plus v1 t2' 


    tminus t1 t2    (minus t1 t2)

      ----------------------------------------------------------   (ST_MinusNV)
      CTbl * MTbl ; minus (tnat n1) (tnat n2) ==> tnat (n1 - n2)

                      CTbl * MTbl ; t1 ==> t1'
              ------------------------------------------            (ST_Minus1)
              CTbl * MTbl ; minus t1 t2 ==> minus t1' t2 

                              value v1
                      CTbl * MTbl ; t2 ==> t2'
              ------------------------------------------            (ST_Minus2)
              CTbl * MTbl ; minus v1 t2 ==> minus v1 t2' 


    tmult t1 t2     (mult t1 t2)

       ---------------------------------------------------------    (ST_MultNV)
       CTbl * MTbl ; mult (tnat n1) (tnat n2) ==> tnat (n1 * n2)

                      CTbl * MTbl ; t1 ==> t1'
               ----------------------------------------              (ST_Mult1)
               CTbl * MTbl ; mult t1 t2 ==> mult t1' t2 

                              value v1
                      CTbl * MTbl ; t2 ==> t2'
               ----------------------------------------              (ST_Mult2)
               CTbl * MTbl ; mult v1 t2 ==> mult v1 t2' 


    teqnat t1 t2    (eqnat t1 t2)

      ----------------------------------------------------------   (ST_EqnatNV)
      CTbl * MTbl ; eqnat (tnat n1) (tnat n2) ==> tnat (n1 = n2)

                      CTbl * MTbl ; t1 ==> t1'
              ------------------------------------------            (ST_Eqnat1)
              CTbl * MTbl ; eqnat t1 t2 ==> eqnat t1' t2 

                              value v1
                      CTbl * MTbl ; t2 ==> t2'
              ------------------------------------------            (ST_Eqnat2)
              CTbl * MTbl ; eqnat v1 t2 ==> eqnat v1 t2'


    tlenat t1 t2    (lenat t1 t2)

      ----------------------------------------------------------   (ST_LenatNV)
      CTbl * MTbl ; lenat (tnat n1) (tnat n2) ==> tnat (n1 < n2)

                      CTbl * MTbl ; t1 ==> t1'
              ------------------------------------------            (ST_Lenat1)
              CTbl * MTbl ; lenat t1 t2 ==> lenat t1' t2 

                              value v1
                      CTbl * MTbl ; t2 ==> t2'
              ------------------------------------------            (ST_Lenat2)
              CTbl * MTbl ; lenat v1 t2 ==> lenat v1 t2'


    tlet x t1 t2    (let x = t1 in t2)

                           CTbl * MTbl ; t1 ==> t1'
           ------------------------------------------------            (ST_Let)
           CTbl * MTbl ; let x=t1 in t2 ==> let x=t1' in t2

                              value v1
              -------------------------------------------         (ST_LetValue)
              CTbl * MTbl ; let x=v1 in t2 ==> [x:=v1] t2
*)

