
open Syntax
open Syntax.Int


val get_transitions : compilation_unit -> (string * transition_label) list

val do_transition : role list -> global -> transition_label -> global option
