(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(* General Aux Datatypes and Functions

   Last Update: Wed, 18 Jan 2017
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 


(* ***************************************************************** *)
(** * Options *)
(* ***************************************************************** *)
(* ***************************************************************** *)

(** Processes [option A] value [x] and returns the value of type [B]:
    [fsome x'] if [x = Some x'] or [vnone] otherwise. *)

Definition option_handle {A B : Type} (x : option A) 
                         (fsome : A -> B) (vnone : B) : B :=
  match x with
    | Some x' => fsome x'
    | None    => vnone
  end.
  