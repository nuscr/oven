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

let do_transition (roles : role list) (g : global) (lbl : transition_label) : global option =
  let et = get_enabled_transitions roles [] g in
  if not (List.mem lbl et) then
    None
  else
    let rec f = function
    | End -> None
    | RecVar {name = _ ; global} -> f !(get_global_ref global) (* for the variables we just follow the reference *)
    | Rec (_, global) -> f global (* since the variables are unfolded by reference we don't need to unfold *)
    | Choice branches -> fb branches
    and fb branches =
      (* find lbl in the choice ->G-Com1 *)
      let rec find_continuation = function
        | [] -> None
        | Message {tr_label ; continuation} :: _ when tr_label = lbl -> Some continuation
        | Message {tr_label=_ ; continuation=_} :: brs -> find_continuation brs
      in
      (* find the lbl in the continuation ->G-Com2 *)
      let rec find_in_continuation = function
        | [] -> None
        | Message {tr_label=_ ; continuation} :: brs ->
          begin match f continuation with
              | Some g -> Some g
              | None -> find_in_continuation brs
          end
      in
      let parts = get_branches_participants branches in
      if (List.mem lbl.sender parts || List.mem lbl.receiver parts) then
        (* has to be in the prefix *)
        find_continuation branches
      else
        (* has to be in the continuations *)
        find_in_continuation branches
    in
    f g
