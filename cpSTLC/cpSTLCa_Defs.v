(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(* Simply Typed Lambda Calculus with simple Concept Parameters
   :: version a
   Definitions

   Definitions of STLC are based on
   Sofware Foundations, v.4 
  
   Last Update: Mon, 27 Mar 2017
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 


(* ***************************************************************** *)
(** * cpSTLCa Syntax and Semantics Definition 

    (Simply Typed Lambda Calculus with simple Concept Parameters  
     :: version a) *)
(* ***************************************************************** *)
(* ***************************************************************** *)

Add LoadPath "../..".

Require Import ConceptParams.BasicPLDefs.Identifier.
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
(* ################################################################# *)

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
(* ----------------------------------------------------------------- *)

Inductive ty : Type :=
  | TBool : ty 
  | TNat  : ty
  | TArrow : ty -> ty -> ty        (* T1 -> T2 *)
  | TConceptPrm : id -> ty -> ty   (* C # T *)
.

(* ----------------------------------------------------------------- *)
(** **** Terms *)
(* ----------------------------------------------------------------- *)

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
(* ----------------------------------------------------------------- *)

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
(* ----------------------------------------------------------------- *)

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
(* ----------------------------------------------------------------- *)

Inductive program : Type :=
  | tprog : conceptsec -> modelsec -> tm -> program
.

(** There are examples of concepts and programs in [cpSTLCa_Examples.v]. *)


(* ################################################################# *)
(** ** Typing *)
(* ################################################################# *)

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
(* ================================================================= *)

(* ----------------------------------------------------------------- *)
(** **** Checking Concept Definitions *)
(* ----------------------------------------------------------------- *)

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
(* ================================================================= *)

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

                            M \notin dom(Gamma)
                             M \in dom(MTable)
                          MTable(M) = ... of C ...
                             C \in dom(CTable)
                        CTable(C) = ... f : TF ...
                   -----------------------------------                (T_MInvk)
                   CTable * MTable ; Gamma |- M.f : TF


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
      CTable $ MTable ; Gamma |- t1 \in (TArrow T11 T12) ->
      CTable $ MTable ; Gamma |- t2 \in T11 ->                 
      CTable $ MTable ; Gamma |- tapp t1 t2 \in T12
  | T_Abs   : forall CTable MTable Gamma x t12 T11 T12,
      CTable $ MTable ; (update Gamma x (tmtype T11)) |- t12 \in T12 ->        
      CTable $ MTable ; Gamma |- tabs x T11 t12 \in (TArrow T11 T12)
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
  | T_MInvk : forall CTable MTable Gamma M C Mbody f TF,
      Gamma M = None ->
      MTable M = Some (MTdef C Mbody) ->
      concept_fun_member CTable C f TF ->
      CTable $ MTable ; Gamma |- tcinvk M f \in TF
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
(* ----------------------------------------------------------------- *)

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
(* ----------------------------------------------------------------- *)

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
(* ################################################################# *)

(* ================================================================= *)
(** *** Values *)
(* ================================================================= *)

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
(* ================================================================= *)

(** Apparently, to evaluate terms of cpSTLCa we need not only usual
    terms substitution, but also models subsitution. *)

(* ----------------------------------------------------------------- *)
(** **** Free Variables *)
(* ----------------------------------------------------------------- *)

(** To correctly apply substitution(s), we will need free variables. 
    Both normal and concept-parameters. *)

(** The only source of free vars is [tvar] constructor.
    Lambda binds its variable.
    
    The only source of free concept vars is [tcinvk] constructor.
    Concept abstraction binds its parameter.  
    Oooops, t # M also gives us free model variable M. 

    All other forms of term needs recursive search of free vars. *)

Fixpoint free_vars (t : tm) : id_set := 
  match t with
  (* FV(x) = {x} *)
  | tvar x      => ids_singleton x  
  (* FV(t1 t2) = FV(t1) \union FV(t2) *)
  | tapp t1 t2  => ids_union (free_vars t1) (free_vars t2)
  (* FV(\x:T.t) = FV(t) \ {x} *)                               
  | tabs x T t  => let t_fv := free_vars t in
      IdSet.remove x t_fv
(*
  (* FV(t # M) = FV(t) because M refers to MTable, not term itself *)   
  | tmapp t M   => free_vars t   
*)
  (* FV(t # M) = FV(t) \union {M} *)   
  | tmapp t M   => ids_union (free_vars t) (ids_singleton M)   
  (* FV(\c#C.t) = FV(t) because C is not subject for substitution *)
  | tcabs c C t => let t_fv := free_vars t in
      IdSet.remove c t_fv
  (* FV(c.f) = {c} *)
  | tcinvk c f  => ids_singleton c
  (* FV(true) = {} *)
  | ttrue       => ids_empty
  (* FV(false) = {} *)
  | tfalse      => ids_empty
  (* FV(if t1 then t2 else t3) = FV(t1) \union FV(t2) \union FV(t3) *)
  | tif t1 t2 t3 => ids_union (ids_union 
      (free_vars t1) (free_vars t2)) (free_vars t3)
  (* FV(n) = {} *)
  | tnat n      => ids_empty
  (* FV(succ t) = FV(t) *)
  | tsucc t     => free_vars t
  (* FV(pred t) = FV(t) *)
  | tpred t     => free_vars t
  (* FV(plus t1 t2) = FV(t1) \union FV(t2) *)
  | tplus t1 t2  => ids_union (free_vars t1) (free_vars t2)
  (* FV(minus t1 t2) = FV(t1) \union FV(t2) *)
  | tminus t1 t2 => ids_union (free_vars t1) (free_vars t2)
  (* FV(mult t1 t2) = FV(t1) \union FV(t2) *)
  | tmult t1 t2  => ids_union (free_vars t1) (free_vars t2)
  (* FV(eqnat t1 t2) = FV(t1) \union FV(t2) *)
  | teqnat t1 t2 => ids_union (free_vars t1) (free_vars t2)
  (* FV(lenat t1 t2) = FV(t1) \union FV(t2) *)
  | tlenat t1 t2 => ids_union (free_vars t1) (free_vars t2) 
  (* FV(let x=t1 in t2) = FV(t1) \union (FV(t2) \ {x}) *)       
  | tlet x t1 t2 => let t2_fv := free_vars t2 in
      ids_union (free_vars t1) (IdSet.remove x t2_fv) 
  end.

(* ----------------------------------------------------------------- *)
(** **** Alpha Conversion ??? *)
(* ----------------------------------------------------------------- *)

(** We will only work with nicely defined terms, which satisfy
    Barendregt variable convention:
    all bindings introduce different variables *)

(** We'll come back to this later... *)

(* ----------------------------------------------------------------- *)
(** **** Substitution Function *)
(* ----------------------------------------------------------------- *)

(** Note!
    As normal parameters and concept-parameters lie in the same Gamma,
    later binding hides the earlier one even if they are of different kinds.
    Thus, in the example below
   
        [\c:Nat.\c#MonoidNat. if c = c.ident ...] 

    we cannot type this term, because [c] becomes concept.
*)

(** Question:
    
    Is it true that if we start with closed term,
    nothing bad can happen?

    Answer:

    Probably. Consider

        (\c#MonoidNat.(\x:Nat.\c:Nat. if x = c ...) c.ident) # Plus
        -->
        (\x:Nat.\c:Nat. if x = c ...) Plus.ident
        -->
        \c:Nat. if Plus.ident = c ...

    But
       
        (\c#MonoidNat.(\Plus#MonoidNat. if c.ident = ...)) Plus
        -->
        \Plus.MonoidNat. if Plus.ident...

   (captured)
*)

(** Let us first define a substitution informally.

    For simplicity, we assume that all variables binded in different
    lambdas (and let-bindings)
    are distinct (and we calculate closed terms only,
      or free vars do not appear in bindings), 
    so we don't need renaming.
    
    The same should also be applied to concept parameters, 
    and, probably, concept names and model names: 
    no repetitions and no intersections with variables.
*)

(** Note that since M and C are not first-class, they have
    syntax-directed positions and do not interfere with Gamma.

       [x:=s] x               = s
       [x:=s] y               = y                        if x <> y

       [x:=s] (t1 t2)         = ([x:=s] t1) ([x:=s] t2)

       [x:=s] (\x:T11. t12)   = \x:T11. t12
       [x:=s] (\y:T11. t12)   = \y:T11. [x:=s]t12        if x <> y
                                                         Check: y \notin FV(s)

       Note! The situation when y \in FV(s) must be impossible
       under our assumptions.

       [x:=s] (t1 # M)        = ([x:=s] t1) # M          

       Note! The situation M = x must be impossible
       under our assumptions. Or we do not care about this...

       [x:=s] (\x#C.t1)       = \x#C.t1   
       [x:=s] (\c#C.t1)       = \c#C.([x:=s] t1)         if x <> c
                
       [x:=s] (c.f)           = c.f         (independently of x <> c)

       [x:=s] true            = true
       [x:=s] false           = false

       [x:=s] (if t1 then t2 else t3) 
                              =
                       if [x:=s]t1 then [x:=s]t2 else [x:=s]t3
                       
       [x:=s] n               = n
       
       [x:=s] (succ t)        = succ ([x:=s] t)
       [x:=s] (pred t)        = pred ([x:=s] t)

       [x:=s] (plus t1 t2)    = plus ([x:=s] t1) ([x:=s] t2)
       [x:=s] (minus t1 t2)   = minus ([x:=s] t1) ([x:=s] t2)
       [x:=s] (mult t1 t2)    = mult ([x:=s] t1) ([x:=s] t2)
       [x:=s] (eqnat t1 t2)   = eqnat ([x:=s] t1) ([x:=s] t2)
       [x:=s] (lenat t1 t2)   = lenat ([x:=s] t1) ([x:=s] t2)
       
       [x:=s] (let x = t1 in t2)
                              =
                       let x = ([x:=s] t1) t2

       [x:=s] (let y = t1 in t2)                         if y <> x
                              =                          (and y \notin FV(s))
                       let y = ([x:=s] t1) ([x:=s] t2)  
*)

(** Function [subst] takes var [x], terms [s] and [t].
    It replaces all free occurences of [x] in term [t] with term [s]. *)
Fixpoint subst (x : id) (s : tm) (t : tm) : tm :=
  match t with
    | tvar y =>
        if beq_id x y then s else t
    | tapp t1 t2  =>
        tapp (subst x s t1) (subst x s t2)
    (* We assume that y \notin FV(s) *)
    | tabs y T t1 =>
        tabs y T (if beq_id x y then t1 else (subst x s t1))
    | tmapp t1 M  =>
        tmapp (subst x s t1) M
    | tcabs c C t1 =>
        tcabs c C (if beq_id c x then t1 else (subst x s t1))
    | tcinvk c f =>
        tcinvk c f
    | ttrue  => ttrue
    | tfalse => tfalse
    | tif t1 t2 t3 =>
        tif (subst x s t1) (subst x s t2) (subst x s t3)
    | tnat n =>
        tnat n
    | tsucc t1 =>
        tsucc (subst x s t1)
    | tpred t1 =>
        tpred (subst x s t1)
    | tplus t1 t2  =>
        tplus (subst x s t1) (subst x s t2)
    | tminus t1 t2 =>
        tminus (subst x s t1) (subst x s t2)
    | tmult t1 t2  =>
        tmult (subst x s t1) (subst x s t2)
    | teqnat t1 t2 =>
        teqnat (subst x s t1) (subst x s t2)
    | tlenat t1 t2 =>
        tlenat (subst x s t1) (subst x s t2)
    | tlet y t1 t2 => 
        tlet y (subst x s t1) (if beq_id x y then t2 else (subst x s t2))
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20) : stlca_scope. 

(** We will also need concept parameters substitution. 
    Let us first define it informally.

    For simplicity, we assume that all concept-parameters 
    binded in different concept abstractions
    are distinct.

       [#c:=M] x               = x      (we do not touch variables)

       [#c:=M] (t1 t2)         = ([#c:=M] t1) ([#c:=M] t2)

       [#c:=M] (\c:T11. t12)   = \c:T11. t12
       [#c:=M] (\x:T11. t12)   = \x:T11. ([#c:=M] t12)     if c <> x

       [#c:=M] (t1 # N)        = ([#c:=M] t1) # N

       [x:=s] (\c#C.t1)        = \c#C.([#c:=M] t1)         

       [#c:=M] (\c#C.t1)       = \c#C.t1
       [#c:=M] (\d#C.t1)       = \d#C.([#c:=M] t1)         if c <> d
                                                         Check: M <> d

       Note! The situation when M = d must be impossible
       under our assumptions.

       [#c:=M] (c.f)           = M.f                      
       [#c:=M] (d.f)           = d.f                      if c <> d  

       [#c:=M] true            = true
       [#c:=M] false           = false

       [#c:=M] (if t1 then t2 else t3) 
                              =
                       if [#c:=M]t1 then [#c:=M]t2 else [#c:=M]t3
                       
       [#c:=M] n               = n
       
       [#c:=M] (succ t)        = succ ([#c:=M] t)
       [#c:=M] (pred t)        = pred ([#c:=M] t)

       [#c:=M] (plus t1 t2)    = plus  ([#c:=M] t1) ([#c:=M] t2)
       [#c:=M] (minus t1 t2)   = minus ([#c:=M] t1) ([#c:=M] t2)
       [#c:=M] (mult t1 t2)    = mult  ([#c:=M] t1) ([#c:=M] t2)
       [#c:=M] (eqnat t1 t2)   = eqnat ([#c:=M] t1) ([#c:=M] t2)
       [#c:=M] (lenat t1 t2)   = lenat ([#c:=M] t1) ([#c:=M] t2)
       
       [#c:=M] (let c = t1 in t2)
                              =
                       let c = ([#c:=M] t1) in t2

       [#c:=M] (let x = t1 in t2)                         if c <> x
                              =                          Check: M <> x
                       let x = ([#c:=M] t1) in ([#c:=M] t2)  
*)


(** Function [substc] takes concept parameter name [c], 
      model name [M], and terms [t].
    It replaces all free occurences of [c] in term [t] with term [s]. *)
Fixpoint substc (c : id) (M : id) (t : tm) : tm :=
  match t with
    | tvar x => tvar x
    | tapp t1 t2  =>
        tapp (substc c M t1) (substc c M t2)
    | tabs x T t1 =>
        tabs x T (if beq_id c x then t1 else (substc c M t1))
    | tmapp t1 N  =>
        tmapp (substc c M t1) N
(* We assume that M <> d *)
    | tcabs d C t1 =>
        tcabs d C (if beq_id c d then t1 else (substc c M t1))
    | tcinvk d f =>
        tcinvk (if beq_id c d then M else d) f
    | ttrue  => ttrue
    | tfalse => tfalse
    | tif t1 t2 t3 =>
        tif (substc c M t1) (substc c M t2) (substc c M t3)
    | tnat n =>
        tnat n
    | tsucc t1 =>
        tsucc (substc c M t1)
    | tpred t1 =>
        tpred (substc c M t1)
    | tplus t1 t2  =>
        tplus (substc c M t1) (substc c M t2)
    | tminus t1 t2 =>
        tminus (substc c M t1) (substc c M t2)
    | tmult t1 t2  =>
        tmult (substc c M t1) (substc c M t2)
    | teqnat t1 t2 =>
        teqnat (substc c M t1) (substc c M t2)
    | tlenat t1 t2 =>
        tlenat (substc c M t1) (substc c M t2)
(* We assume that M <> x *)
    | tlet x t1 t2 => 
        tlet x (substc x M t1) (if beq_id c x then t2 else (substc c M t2))
  end.

Notation "'[#' c ':=' M ']' t" := (substc c M t) (at level 20) : stlca_scope.

(* ================================================================= *)
(** *** Reduction (Small-step operational semantics) *)
(* ================================================================= *)

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


(** Here is a formal definition [step] of the 
  * small-step reduction relation. *)

Reserved Notation "CTbl '$' MTbl ';' t1 '#==>' t2" (at level 50).

Inductive step (CTbl : cptcontext) (MTbl : mdlcontext) : tm -> tm -> Prop :=
(* app *)
  | ST_AppAbs : forall x T11 t12 v2,
         value v2 ->
         CTbl $ MTbl ; (tapp (tabs x T11 t12) v2) #==> ([x:=v2] t12)
  | ST_App1 : forall t1 t1' t2,
         CTbl $ MTbl ; t1 #==> t1' ->
         CTbl $ MTbl ; (tapp t1 t2) #==> (tapp t1' t2)
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         CTbl $ MTbl ; t2 #==> t2' ->
         CTbl $ MTbl ; (tapp v1 t2) #==> (tapp v1 t2')
(* mapp *)
  | ST_MAppCAbs : forall c C t M Mbody,
         MTbl M = Some (MTdef C Mbody) ->
         CTbl $ MTbl ; (tmapp (tcabs c C t) M) #==> ([#c:=M] t)
  | ST_MApp1 : forall t1 t1' M,
         CTbl $ MTbl ; t1 #==> t1' ->
         CTbl $ MTbl ; (tmapp t1 M) #==> (tmapp t1' M)
(* cinvk *)
  | ST_CInvk : forall M f C Mbody tf,
         MTbl M = Some (MTdef C Mbody) ->
         find_tm f Mbody = Some tf -> 
         CTbl $ MTbl ; (tcinvk M f) #==> tf
(* if *)
  | ST_IfTrue : forall t2 t3,
         CTbl $ MTbl ; (tif ttrue t2 t3) #==> t2
  | ST_IfFalse : forall t2 t3,
         CTbl $ MTbl ; (tif tfalse t2 t3) #==> t3
  | ST_If : forall t1 t1' t2 t3,
         CTbl $ MTbl ; t1 #==> t1' ->
         CTbl $ MTbl ; (tif t1 t2 t3) #==> (tif t1' t2 t3)
(* succ *)
  | ST_SuccNV : forall n,
         CTbl $ MTbl ; (tsucc (tnat n)) #==> tnat (S n)
  | ST_Succ : forall t1 t1',
         CTbl $ MTbl ; t1 #==> t1' ->
         CTbl $ MTbl ; (tsucc t1) #==> (tsucc t1')
(* pred *)
  | ST_PredZero :
         CTbl $ MTbl ; (tpred (tnat 0)) #==> tnat 0
  | ST_PredSucc : forall n,
         CTbl $ MTbl ; (tpred (tnat (S n))) #==> tnat n
  | ST_Pred : forall t1 t1',
         CTbl $ MTbl ; t1 #==> t1' ->
         CTbl $ MTbl ; (tpred t1) #==> (tpred t1')
(* plus *)
  | ST_PlusNV : forall n1 n2,
         CTbl $ MTbl ; (tplus (tnat n1) (tnat n2)) #==> tnat (n1 + n2) 
  | ST_Plus1 : forall t1 t1' t2,
         CTbl $ MTbl ; t1 #==> t1' ->
         CTbl $ MTbl ; (tplus t1 t2) #==> (tplus t1' t2)
  | ST_Plus2 : forall v1 t2 t2',
         value v1 ->
         CTbl $ MTbl ; t2 #==> t2' ->
         CTbl $ MTbl ; (tplus v1 t2) #==> (tplus v1 t2')
(* minus *)
  | ST_MinusNV : forall n1 n2,
         CTbl $ MTbl ; (tminus (tnat n1) (tnat n2)) #==> tnat (n1 - n2) 
  | ST_Minus1 : forall t1 t1' t2,
         CTbl $ MTbl ; t1 #==> t1' ->
         CTbl $ MTbl ; (tminus t1 t2) #==> (tminus t1' t2)
  | ST_Minus2 : forall v1 t2 t2',
         value v1 ->
         CTbl $ MTbl ; t2 #==> t2' ->
         CTbl $ MTbl ; (tminus v1 t2) #==> (tminus v1 t2')
(* mult *)
  | ST_MultNV : forall n1 n2,
         CTbl $ MTbl ; (tmult (tnat n1) (tnat n2)) #==> tnat (n1 * n2) 
  | ST_Mult1 : forall t1 t1' t2,
         CTbl $ MTbl ; t1 #==> t1' ->
         CTbl $ MTbl ; (tmult t1 t2) #==> (tmult t1' t2)
  | ST_Mult2 : forall v1 t2 t2',
         value v1 ->
         CTbl $ MTbl ; t2 #==> t2' ->
         CTbl $ MTbl ; (tmult v1 t2) #==> (tmult v1 t2')
(* eqnat *)
  | ST_EqnatNVTrue : forall n1 n2,
         n1 = n2 ->
         CTbl $ MTbl ; (teqnat (tnat n1) (tnat n2)) #==> ttrue
  | ST_EqnatNVFalse : forall n1 n2,
         n1 <> n2 ->
         CTbl $ MTbl ; (teqnat (tnat n1) (tnat n2)) #==> tfalse
  | ST_Eqnat1 : forall t1 t1' t2,
         CTbl $ MTbl ; t1 #==> t1' ->
         CTbl $ MTbl ; (teqnat t1 t2) #==> (teqnat t1' t2)
  | ST_Eqnat2 : forall v1 t2 t2',
         value v1 ->
         CTbl $ MTbl ; t2 #==> t2' ->
         CTbl $ MTbl ; (teqnat v1 t2) #==> (teqnat v1 t2')
(* lenat *)
  | ST_LenatNVTrue : forall n1 n2,
         n1 < n2 ->
         CTbl $ MTbl ; (tlenat (tnat n1) (tnat n2)) #==> ttrue
  | ST_LenatNVFalse : forall n1 n2,
         n2 <= n1 ->
         CTbl $ MTbl ; (tlenat (tnat n1) (tnat n2)) #==> tfalse
  | ST_Lenat1 : forall t1 t1' t2,
         CTbl $ MTbl ; t1 #==> t1' ->
         CTbl $ MTbl ; (tlenat t1 t2) #==> (tlenat t1' t2)
  | ST_Lenat2 : forall v1 t2 t2',
         value v1 ->
         CTbl $ MTbl ; t2 #==> t2' ->
         CTbl $ MTbl ; (tlenat v1 t2) #==> (tlenat v1 t2')
(* let *)
  | ST_Let : forall x t1 t1' t2,
         CTbl $ MTbl ; t1 #==> t1' ->
         CTbl $ MTbl ; (tlet x t1 t2) #==> (tlet x t1' t2)
  | ST_LetValue : forall x v1 t2,
         CTbl $ MTbl ; (tlet x v1 t2) #==> ([x:=v1] t2)

where "CTbl '$' MTbl ';' t1 '#==>' t2" := (step CTbl MTbl t1 t2) : stlca_scope.

Hint Constructors step.


Section MultiStep.

Parameter CTable : cptcontext.
Parameter MTable : mdlcontext.

Definition step_fixed : tm -> tm -> Prop := step CTable MTable.

Notation multistep := (multi step_fixed).
Notation "t1 '#==>*' t2" := (multistep t1 t2) (at level 40) : cpstlca_scope.

Open Scope cpstlca_scope. 

Lemma test' : forall (t t' : tm),
    t #==>* t'.
Proof.
Abort.

End MultiStep.


(*
Open Scope cpstlca_scope. 


Lemma test' : forall (t t' : tm),
    t #==>* t'.

*)