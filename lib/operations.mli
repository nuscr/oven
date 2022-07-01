open Syntax
open Syntax.Int

module Trace : sig

  type 'lbl t
    = Done
    | Split of ('lbl * 'lbl t Lazy.t) list


  val string_of_trace : int -> 'lbl t -> ('lbl -> string) -> string
end

module Global : sig
  val get_transitions : compilation_unit -> (string * transition_label) list

  val do_transition : role list -> global -> transition_label -> global option

  val get_trace : role list -> global -> transition_label Trace.t
end
