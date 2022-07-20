module Toplevel = struct
  let say_hello () = "hello!"

  let _inactive = Syntax.Seq []

  let set_filename (fname : string) (lexbuf : Lexing.lexbuf) =
    lexbuf.Lexing.lex_curr_p <-
      {lexbuf.Lexing.lex_curr_p with Lexing.pos_fname= fname} ;
    lexbuf

  let parse_from_lexbuf lexbuf  : Syntax.compilation_unit =
    try Parser.cu Lexer.token lexbuf with
    | Lexer.LexError msg -> raise (Error.UserError ("Lexing error: " ^ msg))
    | Parser.Error ->
      let pos = Lexing.lexeme_start_p lexbuf in
      let pos_str = Lexing.(pos.pos_fname ^ " line: " ^  (Int.to_string pos.pos_lnum)) in
      raise (Error.UserError ("Parsing error: " ^ pos_str))
    | e -> raise (Error.Violation ("Found a problem:" ^  Printexc.to_string e))



  let _parse fname ch : Syntax.compilation_unit  =
    let lexbuf = set_filename fname (Lexing.from_channel ch) in
    parse_from_lexbuf lexbuf

  let parse_string string : Syntax.compilation_unit = parse_from_lexbuf @@ Lexing.from_string string

  let translate_and_validate (cu : Syntax.compilation_unit) : Syntax.compilation_unit =
    if Syntax.validate_compilation_unit cu then
      cu
    else
      Error.UserError "Validation failed!" |> raise

  let get_transitions = Operations.Global.get_transitions

  let get_traces_as_string (cu : Syntax.compilation_unit) : string =
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

  let dot_of_global_machine = Machine.Global.generate_dot

  let  generate_all_local_machines : Syntax.global Syntax.protocol -> Machine.Local.FSM.t =
    Machine.Local.generate_all_local

  let dot_of_local_machine = Machine.Local.generate_dot

end

include Toplevel

let get_log = Utils.get_log
