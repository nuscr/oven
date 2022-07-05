
module Toplevel = struct
  let say_hello () = "hello!"

  let _inactive = Syntax.Int.End

  let set_filename (fname : string) (lexbuf : Lexing.lexbuf) =
    lexbuf.Lexing.lex_curr_p <-
      {lexbuf.Lexing.lex_curr_p with Lexing.pos_fname= fname} ;
    lexbuf

  let parse_from_lexbuf lexbuf  : Syntax.Ext.compilation_unit =
    try Parser.cu Lexer.token lexbuf with
    | Lexer.LexError msg -> raise (Error.UserError ("Lexing error: " ^ msg))
    | Parser.Error ->
      let pos = Lexing.((lexeme_start_p lexbuf).pos_fname) in
      raise (Error.UserError ("Parseing error: " ^ pos))
    | e -> raise (Error.Violation ("Found a problem:" ^  Printexc.to_string e))



  let _parse fname (ch : In_channel.t) : Syntax.Ext.compilation_unit  =
    let lexbuf = set_filename fname (Lexing.from_channel ch) in
    parse_from_lexbuf lexbuf

  let parse_string string : Syntax.Ext.compilation_unit = parse_from_lexbuf @@ Lexing.from_string string

  let translate_and_validate (cu : Syntax.Ext.compilation_unit) : Syntax.Int.compilation_unit option =
    try
      let cu' = Syntax.translate_compilation_unit cu in
      if Syntax.Int.validate_compilation_unit cu' then
        Some cu'
      else
        None
    with
      _ -> None

  let get_transitions = Operations.Global.get_transitions

  let get_traces_as_string (cu : Syntax.Int.compilation_unit) : string =
    Syntax.(
    List.map (fun p ->
          let tr = Operations.Global.get_trace p.roles p.interactions in
        p.protocol_name
        ^ "\n"
        ^ Operations.Trace.string_of_trace 20 tr string_of_transition_label) cu |> String.concat "\n"
)

  let string_of_transition_label = Syntax.string_of_transition_label

  let generate_global_state_machine = Machine.Global.generate_state_machine
  let project_state_machine = Machine.Local.project
end

include Toplevel
