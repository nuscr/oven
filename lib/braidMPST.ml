module Toplevel = struct
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

  let quick_parse_string s : (string list, string) result =
    try
      parse_string s |> List.map (fun cu -> cu.Syntax.protocol_name) |> Result.ok
    with
      Error.UserError s -> Result.error s

  let translate_and_validate (cu : Syntax.compilation_unit) : Syntax.compilation_unit =
    if Syntax.validate_compilation_unit cu then
      cu
    else
      Error.UserError "Validation failed!" |> raise

  let rec find_protocol n (cu : Syntax.compilation_unit) =
    match n, cu with
    | _, [] -> None
    | None, prot::_ -> Some prot
    | Some n, prot::_ when n = prot.Syntax.protocol_name -> Some prot
    | _, _::prots -> find_protocol n prots

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

  let generate_global_state_machine = GlobalLocal.Global.generate_state_machine
  let project_state_machine = GlobalLocal.Local.project

  let dot_of_global_machine = GlobalLocal.Global.generate_dot

  let minimal_dot_of_local_machine = GlobalLocal.Local.generate_minimal_dot

  let generate_local_machines_for_roles =
    GlobalLocal.Local.generate_local_for_roles

  let dot_of_local_machine = GlobalLocal.Local.generate_dot

  let well_behaved_local_machines protocol_name rs_and_ls : unit =
    match GlobalLocal.Local.well_behaved_local_machines rs_and_ls with
    | Result.Ok () -> ()
    | Result.Error errMsg ->
      protocol_name ^ ": failed with : " ^ errMsg |> Utils.log ;
      Error.UserError ("Protocol: " ^ protocol_name ^ " failed with:\n" ^ errMsg) |> raise

end

module CommandLineInterface = struct
  open Syntax

  let process_role (r, lfsm) =
    let dot = Toplevel.minimal_dot_of_local_machine lfsm in
    "// Role: " ^ r ^ "\n" ^ dot

  let process_protocol (proto : global protocol) : string =
    let _, gfsm = Toplevel.generate_global_state_machine proto.interactions in
    let rs_lfsms = Toplevel.generate_local_machines_for_roles proto.roles gfsm in

    Toplevel.well_behaved_local_machines proto.protocol_name rs_lfsms ;

    let out = List.map process_role rs_lfsms |> String.concat "\n" in


    "// Protocol: " ^ proto.protocol_name ^ "\n"
    ^ out

  let process_file_contents scribble =
    let cu = Toplevel.parse_string scribble in
    List.map process_protocol cu |> String.concat "\n"

end

include Toplevel

let local_dots_of_scribble_file = CommandLineInterface.process_file_contents

let get_log = Utils.get_log
