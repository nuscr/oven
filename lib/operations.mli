
open Syntax
open Syntax.Int


val get_transitions : compilation_unit -> (string * transition_label) list

val do_transition : role list -> global -> transition_label -> global option


(* traces *)

type 'lbl trace
   = Done
   | OutOfFuel
   | Split of ('lbl * 'lbl trace Lazy.t) list


val string_of_trace : 'lbl trace -> ('lbl -> string) -> string
val global_trace : int -> role list -> global -> transition_label trace
