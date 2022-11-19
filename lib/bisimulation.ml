module StateEquivalenceClasses (FSM: Machine.FSM) =
struct

  (* a list whre each element is a list of the equivalent states *)
  type state_equivalence_class = FSM.vertex list list

  let _string_of_state_equivalence_class sec =
    List.map (fun l -> List.map FSM.State.as_string l |> String.concat "; ") sec |> String.concat " || "

  (* mark the state as a start or an end if one of the states in the ec is *)
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
    List.fold_left merge [] vss |> canonicalise_start_end

    (* get the canonical representative for each vertex *)
    let translate_with_ec eqsts  st =
      try
        List.find (fun sts -> List.mem st sts) eqsts |> List.hd
      with
      | Failure _ -> Error.Violation "Equivalence class cannot be empty." |> raise
      | Not_found -> st (* if it is not in an equivalence class it's on its own one *)

  let get_dict_from_ec fsm eqsts =
    let vs = FSM.get_vertices fsm in
    let vs' = List.map (translate_with_ec eqsts) vs in
    List.combine vs vs'

  let translate (eqsts : state_equivalence_class) (fsm : FSM.t) : FSM.t =
    let translate_edge e =
      if FSM.E.label e |> FSM.Label.is_default
      then None
      else Some (FSM.E.create
                   (FSM.E.src e |> translate_with_ec eqsts)
                   (FSM.E.label e)
                   (FSM.E.dst e |> translate_with_ec eqsts))
    in
    FSM.fold_edges_e
      (fun e fsm ->
         match translate_edge e with
         | None -> fsm
         | Some e' -> FSM.add_edge_e fsm e')
      fsm FSM.empty

  let make_tau_ends_equivalent_with_dict fsm =
    let tau_pairs =
      FSM.fold_edges_e
        (fun e l ->
             if FSM.E.label e |> FSM.Label.is_default
             then  (FSM.E.src e, FSM.E. dst e)::l
             else l)
        fsm []
    in
    (* lists of equivalent states *)
    let eqsts = compute_from_pair_list tau_pairs in
    translate eqsts fsm, get_dict_from_ec fsm eqsts

  let make_tau_ends_equivalent fsm =
    if Debug.post_process_taus_off None then fsm
    else
      make_tau_ends_equivalent_with_dict fsm |> fst

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

  let compute_bisimulation_quotient (fsm : FSM.t) : EC.state_equivalence_class =
    let initial () : EC.state_equivalence_class * FSM.edge list =
      (* a singleton block with all the states to be refined *)
      let bs : EC.state_equivalence_class = [FSM.fold_vertex (fun st l -> st :: l) fsm []] in
      let edges = FSM.get_edges fsm in
      bs, edges
    in

    let bs, edges = initial() in
    (* Performance: this is quite naive, as we compare lots of blocks for identity, so many
       very slow comparisons of lists. If we run into performance probles,
       this is a thing to improve. It should not be hard once the system is working. *)

    let find_state_in_blocks st bs =
      List.filter (List.mem st) bs
    in

    (* given a vertex and a label check all the block lists that can be reached *)
    let can_reach_block
        (st : FSM.vertex)
        (a : FSM.Label.t)
        (bs : EC.state_equivalence_class)
      : EC.state_equivalence_class list =
      let sts = if is_strong then
          (* this makes it a strong bisimulation *)
          FSM.can_reach_with_anything edges st a
        else
          (* this makes it a weak bisimulation *)
          FSM.can_reach_with_weak_step fsm st a
      in
      List.map (fun st -> find_state_in_blocks st bs) sts |> Utils.uniq
    in

    let split (b : block) (a : FSM.Label.t) (bs : EC.state_equivalence_class) : block * block =
      match b with
      | [] -> [], []
      | st::_ -> (* choose some state in the block *)
        let b1, b2 =
          List.fold_left
            (fun (b1, b2) st' ->
               if can_reach_block st a bs = can_reach_block st' a bs
               then (st'::b1, b2)
               else (b1, st'::b2))
            ([], []) b
        in
        b1, b2 (* TODO remove the let *)
    in

    let compute (bs : block list) : bool * EC.state_equivalence_class =
      let rec for_each_edge (b : block) : FSM.edge list -> bool * block list = function
        | [] -> false, [b]
        | e::es ->
          let b1, b2 = split b (FSM.E.label e) bs in
          if Utils.is_empty b2 then
            for_each_edge b es
          else
            true, [b1; b2]
      in

      let rec for_each_block acc_bs changed = function
        | [] -> changed, acc_bs
        | b::bs ->
          (* sort? *)
          let changed', split_b = for_each_edge b edges  in
          for_each_block (acc_bs @ split_b) (changed || changed') bs
      in

      for_each_block [] false bs
    in

    let rec compute_while_changes bs =
      let changed, bs' = compute bs in
      if changed then
        compute_while_changes bs'
      else
        bs'

    in
    compute_while_changes bs |> EC.canonicalise_start_end

  let are_states_bisimilar (blocks : EC.state_equivalence_class) st1 st2 : bool =
    let find_block (st : FSM.vertex) =
      let find_in_block bl =
        List.mem st bl
      in
      List.find find_in_block blocks
    in
    find_block st1 = find_block st2

  let minimise (fsm : FSM.t) : FSM.t =
    if Debug.minimise_off None then fsm
    else
      let eqsts = compute_bisimulation_quotient fsm in
      EC.translate eqsts fsm

  let minimise_and_translate (fsm : FSM.t) (vs : FSM.vertex list) : FSM.t * FSM.vertex list =
    if Debug.minimise_off None then fsm, vs
    else
      let eqsts = compute_bisimulation_quotient fsm in
      let vs' = List.map (EC.translate_with_ec eqsts) vs in
      EC.translate eqsts fsm, vs'

  let minimise_and_return_dict (fsm : FSM.t)
    : FSM.t * (FSM.vertex * FSM.vertex) list =
    if Debug.minimise_off None then
      let vs = FSM.get_vertices fsm in
      fsm, List.combine vs vs
    else
      let eqsts = compute_bisimulation_quotient fsm in
      EC.translate eqsts fsm, EC.get_dict_from_ec fsm eqsts


  let generate_minimal_dot fsm =
    fsm |> minimise |> FSM.remove_reflexive_taus |> FSM.Dot.generate_dot
end
