

val say_hello : unit -> string


val parse_string : string -> Syntax.Ext.compilation_unit
val translate_and_validate : Syntax.Ext.compilation_unit -> Syntax.Int.compilation_unit option
