## Simply Typed Lambda Calculus with Concept Parameters: version a

### cpSTLCa Description

STLC with `Nat` and `Bool` with simple **concept parameters**:

*   **Concepts** contains only names with types
    
    ```
    C := <empty>
       | CDef C
       
    CDef ::= concept Id 
               f1 : T1
               f2 : T2
               ...
               fn : Tn
             endc  
    ```
    
*   **Models** consist of concept-names definitions:

    ```
    M := <empty>
       | MDef M
       
    MDef ::= model Id of Id
               f1 = t1
               f2 = t2
               ...
               fn = tn
             endm
    ```
    
*   **Types** are STLC types with _concept parameters_:
    
    ```
    T ::= Nat
        | Bool
        | T -> T    (function)
        | C # T     (concept parameter, C is a concept)
    ```
    
*   **Terms** are STLC terms with _model applications_:

    ```
    t ::= true
        | false
        | n          (natural constant)
        | pred t
        | succ t
        | mult t t
        | if t then t else t
        | t t
        | \x:T.t
        | t # m      (model application)
        | \c#C.t     (c is a concept parameter of concept C)
    ```

### cpSTLCa Coq Definitions

#### Syntax

```coq
Inductive ty : Type :=
  | TBool : ty 
  | TNat  : ty
  | TArrow : ty -> ty -> ty        (* T1 -> T2 *)
  | TConceptPrm : id -> ty -> ty   (* C # T *)
.

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
```

#### Typing

```coq
Inductive namedecl : Type :=
  | nm_decl : id -> ty -> namedecl   (* f : T *)
.
Definition namedecl_list : Type := list namedecl.

Inductive conceptdef : Type :=
  | cpt_def : id -> namedecl_list -> conceptdef   (* concept Id NameDefs endc *)
.
Definition conceptsec : Type := list conceptdef.

Inductive namedef : Type :=
  | nm_def : id -> tm -> namedef   (* f = T *)
.
Definition namedef_list : Type := list namedef.

Inductive modeldef : Type :=
  | mdl_def : id -> id -> namedef_list -> modeldef (* model Id of Id NameDefs endm *)
.
Definition modelsec : Type := list modeldef.


Inductive program : Type :=
  | tprog : conceptsec -> modelsec -> tm -> program
.


(** [tycontext] is a typing context: a map from ids to types. *)
Definition tycontext := partial_map ty.

(** AVL map from [id] to [ty]. *)
Definition id_ty_map := id_map ty.

(** Concept type *)
Inductive cty : Type := CTdef : id_ty_map -> cty.

Definition find_ty := mids_find ty.


(** AVL map from [id] to [tm]. *)
Definition id_tm_map := id_map tm.

(** Model type *)
Inductive mty : Type := MTdef : id -> id_tm_map -> mty.

Definition find_tm := mids_find tm.


(** Concept symbol table is a map from concept names
    to concept types [Ci -> CTi]. *)

Definition cptcontext : Type := partial_map cty.
Definition cstempty : cptcontext := @empty cty.

(** Model symbol table is a map from model names
    to model types [Mi -> MTi]. *)

Definition mdlcontext : Type := partial_map mty.
Definition mstempty : mdlcontext := @empty mty.

```

#### Checking Concepts, Models, and Programs

```coq
(** Concepts *)

Definition concept_defined (st : cptcontext) (nm : id) : Prop.
Definition concept_defined_b (st : cptcontext) (nm : id) : bool.

Inductive type_valid (st : cptcontext) : ty -> Prop.
Fixpoint type_valid_b (st : cptcontext) (t : ty) : bool.

Definition concept_welldefined (st : cptcontext) (C : conceptdef) : Prop.
Definition concept_welldefined_b (st : cptcontext) (C : conceptdef) : bool.

Definition concept_has_type (cst : cptcontext) (C : conceptdef) (CT : cty) : Prop.
Definition concept_type_check (cst : cptcontext) (C : conceptdef) : option cty.

(** Terms *)

Inductive ctxvarty : Type :=
  (* type of term variable [x : T] -- normal type *)
| tmtype  : ty -> ctxvarty
  (* type of concept parameter [c # C] -- concept name *)
| cpttype : id -> ctxvarty
.

Definition context : Type := partial_map ctxvarty.
Definition ctxempty : context := @empty ctxvarty.

(** Typing rule *)
Inductive has_type : cptcontext -> mdlcontext -> context -> tm -> ty -> Prop.


(** Models *)

```


