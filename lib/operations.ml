open Syntax
open Syntax.Int


let rec get_enabled_transitions (roles : role list ) (blocked : role list) : global -> transition_label list =
  let is_done () =
    (* this assumes we have the right roles, maybe a stronger function can be implemented *)
    List.length blocked = List.length roles
  in
  (* let is_label_enabled {sender ; receiver ; label } = *)
  let is_not_blocked = function {sender ; receiver ; _} ->
    (not (List.mem sender blocked)) && (not (List.mem receiver blocked))
  in
  function
  | End -> []
  | Rec (_, g) -> get_enabled_transitions roles blocked g
  | RecVar _ when is_done () -> [] (* we need a notion of being done *)
  | RecVar {name = _ ; global} -> get_enabled_transitions roles blocked !(get_global_ref global)
  | Choice branches ->
    (* labels in this choice *)
    let labels =
      List.map (function  Message {tr_label ; _} -> tr_label) branches |>
      List.filter is_not_blocked
    in
    let blocked' =
      (blocked  @ List.concat_map (function {sender ; receiver ; _} -> [sender ; receiver]) labels)
      |> Utils.uniq
    in

    (* labels in the continuations of this choice *)
    let f = function Message {tr_label = _ ; continuation} ->
      get_enabled_transitions roles blocked' continuation
    in

    labels @ List.concat_map f branches

let get_transitions (cu : compilation_unit) : (string * transition_label) list =
  List.concat_map (fun p ->
      get_enabled_transitions p.roles [] p.interactions |> List.map (fun lbls -> (p.protocol_name, lbls))) cu
