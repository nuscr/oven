open StateMachine

module type STRENGTH = sig
  val is_strong : bool
end

module Bisimulation (State : STATE) (Label : LABEL) (Str : STRENGTH)  = struct
  (* Compute the bisimulation quotient using the algorithm by Kanellakis and Smolka *)

  module FSM = FSM (State) (Label)
  include FSM

  open StateEquivalenceClasess

  type block = vertex list

  let compute_bisimulation_quotient (fsm : FSM.t) : state_equivalence_class =
    let initial () : state_equivalence_class * FSM.edge list =
      (* a singleton block with all the states to be refined *)
      let bs : state_equivalence_class = [FSM.fold_vertex (fun st l -> st :: l) fsm []] in
      let edges = get_edges fsm in
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
    let can_reach_block (st:vertex) (a:Label.t) (bs:state_equivalence_class) : state_equivalence_class list =
      let sts = if Str.is_strong then
          (* this makes it a strong bisimulation *)
          can_reach_with_anything edges st a
        else
          (* this makes it a weak bisimulation *)
          can_reach_with_weak_step fsm st a
      in
      List.map (fun st -> find_state_in_blocks st bs) sts |> Utils.uniq
    in

    let split (b : block) (a : Label.t) (bs : state_equivalence_class) : block * block =
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

    let compute (bs : block list) : bool * state_equivalence_class =
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
    compute_while_changes bs

  let are_states_bisimilar (blocks : block list) st1 st2 : bool =
    let find_block (st : vertex) =
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
      StateEquivalenceClasess.translate eqsts fsm

  let generate_minimal_dot _fsm =
    (* fsm |> minimise |> FSM.remove_reflexive_taus |> FSM.Dot.generate_dot *)
    assert false

end
