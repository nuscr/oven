open Syntax


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

module Local : sig

  val project : global -> role -> local

  val project_transition : role -> transition_label -> Syntax.Local.local_transition_label option

  val get_enabled_transitions : role list -> local -> Syntax.Local.local_transition_label list

  val do_transition : role list -> local -> Syntax.Local.local_transition_label -> local option

end
