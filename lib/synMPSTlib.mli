

val say_hello : unit -> string


val parse_string : string -> Syntax.Ext.compilation_unit
val translate_and_validate : Syntax.Ext.compilation_unit -> Syntax.Int.compilation_unit option

val get_transitions : Syntax.Int.compilation_unit -> (string * Syntax.transition_label) list

val string_of_transition_label : Syntax.transition_label -> string

val get_traces_as_string : Syntax.Int.compilation_unit -> string

val generate_global_state_machine : Syntax.Int.global -> Machine.State.t * Machine.Global.FSM.t
val project_state_machine : Syntax.role -> Machine.Global.FSM.t -> Machine.Local.FSM.t
