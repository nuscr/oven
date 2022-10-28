module StateEquivalenceClasses (FSM: Machine.FSM) =
struct

  (* a list whre each element is a list of the equivalent states *)
  type state_equivalence_class = FSM.vertex list list

  let _string_of_state_equivalence_class sec =
    List.map (fun l -> List.map FSM.State.as_string l |> String.concat "; ") sec |> String.concat " || "

  let canonicalise_start_end eq_sts =
    let make_head_start l =
      try
        let _ = List.hd l |> FSM.State.mark_as_start in ()
      with
      | Failure _ -> Error.Violation "The equivalence class needs a canonical element." |> raise
    in
    let make_head_end l =
      try
        let _ = List.hd l |> FSM.State.mark_as_end in ()
      with
      | Failure _ -> Error.Violation "The equivalence class needs a canonical element." |> raise
    in
    let canonicalise eq_st =
      if List.exists FSM.State.is_start eq_st then make_head_start eq_st ;
      if List.exists FSM.State.is_end eq_st then make_head_end eq_st ;
      eq_st
    in
    List.map canonicalise eq_sts

  let compute_from_pair_list (vss : (FSM.vertex * FSM.vertex) list) : state_equivalence_class =
    let find_list_and_rest v eq_sts =
      let have, rest = List.partition (List.mem v) eq_sts in
      match have with
      | [] -> [], rest
      | [have] -> have, rest
      | _::_ -> Error.Violation "Invariant: each vertex appears only once." |> raise
    in

    let merge (eq_sts : state_equivalence_class)
        ((v1, v2) : FSM.vertex * FSM.vertex) : state_equivalence_class =

      let add_if_not_there v l = if List.mem v l then l else v::l in

      let has_v1, rest =  find_list_and_rest v1 eq_sts in
      if List.mem v2 has_v1 then eq_sts (* we are done *)

      else if Utils.is_empty has_v1
      then
        let has_v2, rest = find_list_and_rest v2 eq_sts in
        (add_if_not_there v2 (add_if_not_there v1 has_v2))::rest
      else
        (* has_v1 is not empty and it does not contain v2 *)
        (* rest may contain v2 *)
        let has_v2, rest = find_list_and_rest v2 rest in

        (has_v1 @ (add_if_not_there v2 has_v2))::rest
    in
    List.fold_left merge [] vss

  let translate (eqsts : state_equivalence_class) (fsm : FSM.t) : FSM.t =
    let eqsts = canonicalise_start_end eqsts in
    (* get the canonical representative for each vertex *)
    let translate_st st =
      try
        List.find (fun sts -> List.mem st sts) eqsts |> List.hd
      with
      | Failure _ -> Error.Violation "Equivalence class cannot be empty." |> raise
      | Not_found -> st (* if it is not in an equivalence class it's on its own one *)

    in
    let translate_edge e =
      if FSM.E.label e |> FSM.Label.is_default
      then None
      else Some (FSM.E.create
                   (FSM.E.src e |> translate_st)
                   (FSM.E.label e)
                   (FSM.E.dst e |> translate_st))
    in
    FSM.fold_edges_e
      (fun e fsm ->
         match translate_edge e with
         | None -> fsm
         | Some e' -> FSM.add_edge_e fsm e')
      fsm FSM.empty
end

module type STRENGTH = sig
  type strength = Strong | Weak

  val strength : strength
end

module Strong =
struct
  type strength = Strong | Weak

  let strength = Strong
end

module Weak =
struct
  type strength = Strong | Weak

  let strength = Weak
end


module Bisimulation (FSM : Machine.FSM) (Str : STRENGTH)  = struct
  (* Compute the bisimulation quotient using the algorithm by Kanellakis and Smolka *)

  let get_strength () = Str.strength
  let is_strong = Str.strength = Str.Strong

  module EC = StateEquivalenceClasses (FSM)

  type block = FSM.vertex list
