open Js_of_ocaml
(* open Nuscrlib *)

module Code = struct
  let id = "protocol-textarea"

  let _get () = Js.(to_string (Webutils.get_textarea id)##.value)

  let get () =
    let res = Js.Unsafe.eval_string ("iblize.getValue();") in
    Js.to_string res

  let _set s = (Webutils.get_textarea id)##.value := Js.string s

  let set s =
    let s = String.escaped s in
    let _ = Js.Unsafe.eval_string ("iblize.setValue(\"" ^ s ^ "\");") in
    ()

  let get_name () =
    let get_protocol = "getProtocolName();" in
    let res = Js.Unsafe.eval_string get_protocol in
    Js.to_string res

  let get_format () =
    let get_format = "getOutputFormat();" in
    let res = Js.Unsafe.eval_string get_format in
    Js.to_string res

end

module Error = struct
  let errorbox = "errorbox"

  let display fmt =
    let display string =
      let string = Str.global_substitute (Str.regexp "<") (fun _ -> "&lt") string in
      let string = Str.global_substitute (Str.regexp ">") (fun _ -> "&gt") string in
      let string = Str.global_substitute (Str.regexp "$") (fun _ -> "</br>") string in
      let e = Webutils.get errorbox in
      Webutils.(
        set_inner_html e "%s" string ;
        set_display e "block")
    in
    Printf.ksprintf display fmt

  (* let display_exn = function *)
  (*   | Err.UserError e -> *)
  (*       display "<b>User error</b>: %s" (Err.show_user_error e) *)
  (*   | Err.UnImplemented (s, _) -> *)
  (*       display "<b>Feature not implemented</b>: %s" s *)
  (*   | Err.Violation (s, _) -> display "<b>Violation</b>: %s" s *)
  (*   | e -> display "<b>Unknown error</b>: %s" (Printexc.to_string e) *)

  let display_exn s = display "%s" s (* "Something sad happened" *)

  let reset () = Webutils.(set_display (get "errorbox") "none")
end

module GraphEFSM = struct
  let id = "efsm"

  let clear () = Webutils.set_children (Webutils.get id) []

  let set (svg : Dom.node Js.t) =
    Webutils.set_children (Webutils.get id) [svg]

  let set_dot_text (dot :string) =
    Webutils.set_dot_text id dot

  let set_dot_graph (dot : string) =
    let _ = set_dot_text "" in
    let dot = Js.string dot in
    let viz = Js.Unsafe.global##._Viz in
    let viz = Js.Unsafe.new_obj viz [||] in
    let promise =
      Js.Unsafe.meth_call viz "renderSVGElement" [|Js.Unsafe.inject dot|]
    in
    let _promise =
      Js.Unsafe.meth_call promise "then" [|Js.Unsafe.inject set|]
    in
    ()




  let set_dot (dot : string) =
    (match Code.get_format () with
    | "graph" -> set_dot_graph
    | "dot" -> set_dot_text
    | _ -> set_dot_graph) dot


end

module GraphLocal = struct
  let clear id = Webutils.set_children (Webutils.get id) []

  let set id (svg : Dom.node Js.t) =
    Webutils.set_children (Webutils.get id) [svg]

  let set_div id string =
      let e = Webutils.get id in
      Webutils.(
        set_inner_html e "%s" string ;
        set_display e "block")

  let set_dot_text id (dot :string) =
    Webutils.set_dot_text id dot


  let set_dot_graph id (dot : string) =
    let dot = Js.string dot in
    let viz = Js.Unsafe.global##._Viz in
    let viz = Js.Unsafe.new_obj viz [||] in
    let promise =
      Js.Unsafe.meth_call viz "renderSVGElement" [|Js.Unsafe.inject dot|]
    in
    let _promise =
      Js.Unsafe.meth_call promise "then" [|Js.Unsafe.inject (set id) |]
    in
    ()

  let set_dot id (dot : string) =
    (match Code.get_format () with
    | "graph" -> set_dot_graph
    | "dot" -> set_dot_text
    | _ -> set_dot_graph) id dot
end
