(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(* Simply Typed Lambda Calculus with simple Concept Parameters
   :: version a
   Interpreter

   Definitions of STLC are based on
   Sofware Foundations, v.4 
  
   Last Update: Thu, 19 Jan 2017
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 


(* ***************************************************************** *)
(** * cpSTLCa Static Analysis and Interpretation

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

Require Import ConceptParams.cpSTLC.cpSTLCa_Defs.

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Bool.Bool.

Require Import Coq.omega.Omega.


(* ################################################################# *)
(** ** Syntax *)

(* ----------------------------------------------------------------- *)
(** **** Types *)

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


(* ################################################################# *)
(** ** Typing *)

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

(* ================================================================= *)
(** *** Checking Types Validity *)

(* ----------------------------------------------------------------- *)
(** **** Checking Concept Definitions *)

Definition concept_defined_b (st : cptcontext) (nm : id) : bool :=
  match st nm with
  | None   => false
  | Some _ => true
  end.

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

(** Let's define a typechecker, which corresponds to 
    [has_type] relation. *)

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

Definition model_defined_b (st : mdlcontext) (nm : id) : bool :=
  match st nm with
  | None   => false
  | Some _ => true
  end.

(** Function [model_member_valid_b] corresponds to the [model_member_valid]
    relation of member's validity. *)

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

(** And we define a function to check that "model is well defined". *)

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

Definition modelsec_welldefined_b (mdlsec : modelsec) (cst : cptcontext)
           : mdlcontext * bool :=
  fold_left 
    (fun (acc : mdlcontext * bool) (M : modeldef) =>
       let (mst, correct) := acc
       in if correct then 
            let mtp := model_type_check cst mst M
            in match mtp with
                 | Some MT => (update mst (modeldef__get_name M) MT, true)
                 | None    => (mstempty, false)
               end 
          else (mstempty, false)
    )
    mdlsec (mstempty, true).

Definition program_type_check (cst : cptcontext) (mst : mdlcontext)
           (prg : program) : option ty :=
  match prg with tprog cptsec mdlsec t =>
    let (cst, cpt_good) := conceptsec_welldefined_b cptsec in
    (** All concepts are well defined *)
    if cpt_good then
      let (mst, mdl_good) := modelsec_welldefined_b mdlsec cst in
      (** All models are well defined *)
      if mdl_good then
        (** Term is well typed *)
        type_check cst mst ctxempty t
      else None
    else None
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
