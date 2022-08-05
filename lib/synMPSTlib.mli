

val say_hello : unit -> string


val parse_string : string -> Syntax.compilation_unit
val translate_and_validate : Syntax.compilation_unit -> Syntax.compilation_unit

val get_transitions : Syntax.compilation_unit -> (string * Syntax.transition_label) list

val string_of_transition_label : Syntax.transition_label -> string

val get_traces_as_string : Syntax.compilation_unit -> string

val generate_global_state_machine : Syntax.global -> Machine.State.t * Machine.Global.FSM.t
val project_state_machine : Syntax.role -> Machine.Global.FSM.t -> Machine.Local.FSM.t


val dot_of_global_machine : Machine.Global.FSM.t -> string

val dot_of_local_machine : Machine.Local.FSM.t -> string

val minimal_dot_of_local_machine : Machine.Local.FSM.t -> string

val get_log : unit -> string

val generate_all_local_machines : Syntax.global Syntax.protocol -> Machine.Local.FSM.t

val well_behaved_protocol : Syntax.global Syntax.protocol -> unit

val local_dots_of_scribble_file : string -> string
