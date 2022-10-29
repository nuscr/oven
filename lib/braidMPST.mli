val parse_string : string -> Syntax.compilation_unit
val quick_parse_string : string -> (string list, string) result
val translate_and_validate : Syntax.compilation_unit -> Syntax.compilation_unit

val find_protocol : string option -> Syntax.compilation_unit -> Syntax.global Syntax.protocol option

val get_transitions : Syntax.compilation_unit -> (string * Syntax.transition_label) list

val string_of_transition_label : Syntax.transition_label -> string

val get_traces_as_string : Syntax.compilation_unit -> string

val generate_global_state_machine : Syntax.global -> GlobalLocal.State.t * GlobalLocal.Global.FSM.t
val project_state_machine : Syntax.role -> GlobalLocal.Global.FSM.t -> GlobalLocal.Local.FSM.t


val dot_of_global_machine : GlobalLocal.Global.FSM.t -> string

val dot_of_local_machine : GlobalLocal.Local.FSM.t -> string

val minimal_dot_of_local_machine : GlobalLocal.Local.FSM.t -> string

val get_log : unit -> string

val generate_local_machines_for_roles : Syntax.role list -> GlobalLocal.Global.FSM.t -> (Syntax.role * GlobalLocal.Local.FSM.t) list

val well_behaved_local_machines : string -> (Syntax.role * GlobalLocal.Local.FSM.t) list -> unit

val local_dots_of_scribble_file : string -> string
