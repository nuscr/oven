open Graph

module type STATE = sig
  type t
  val equal : t -> t -> bool
  val hash : t -> int
  val compare : t -> t -> int

  val get_id : t -> int

  val fresh : unit -> t
  val freshen : t -> t
  val renumber_state : int -> t -> t

  val as_string : t -> string
  val list_as_string : t list -> string

  val mark_as_start : t -> t
  val mark_as_end : t -> t

  (* val fresh_start : unit -> t *)
  (* val fresh_end : unit -> t *)

  val is_start : t -> bool
  val is_end : t -> bool
end

module type LABEL = sig
  type t

  val default : t

  val compare : t -> t -> int

  val as_string : t -> string
  val list_as_string : t list -> string

  val is_default : t -> bool
end

module FSM (State : STATE) (Label : LABEL) = struct
  module G = Persistent.Digraph.ConcreteLabeled (State) (Label)
  include G

  let _string_of_edge e =
    (E.src e |> State.as_string)
    ^ "--" ^ (E.label e |> Label.as_string) ^ "->"
    ^ (E.dst e |> State.as_string)

  let get_edges fsm =
    fold_edges_e (fun e l -> e::l) fsm []

  let get_vertices (fsm : t) : V.t list =
    let l = fold_vertex (fun st l -> st::l) fsm [] in
    assert (List.length l = nb_vertex fsm) ;
    l

  let get_start_state fsm =
    try
      List.find State.is_start @@ get_vertices fsm
    with
    |_ -> Error.Violation "FSM must have a start state." |> raise

  (* states that can be reached in one step with label that is not tau a from st *)
  let _can_reach_with_labels edges st a =
    List.filter_map (fun e -> if E.src e = st && E.label e = a && not (E.label e = Label.default) then Some (E.dst e) else None) edges

  let walk_collect_edges_with_predicate (fsm : t) (st : vertex) (step : vertex -> edge list) (p : edge -> bool) : edge list =
    (* states from edges *)
    let sfe es =
      List.concat_map (fun e -> E.src e:: E.dst e::[]) es
    in

    let rec f visited acc to_visit =
      match to_visit with
      | [] -> acc
      | curr_st::sts when List.mem curr_st visited  ->
        f visited acc sts
      | curr_st::sts ->
        let acc' = (List.filter p (succ_e fsm curr_st)) @ acc in
        let visited' = curr_st::visited in
        let to_visit' = to_visit @ (sfe @@ step curr_st)  in
        f  visited' acc' (sts@to_visit')
    in
    f [] [] [st]

  let walk_collect_vertices_with_predicate (fsm : t) (st : vertex) (step : vertex -> edge list) (p : edge -> bool) : vertex list =
    (* states from edges *)
    let sfe es =
      List.concat_map (fun e -> E.src e:: E.dst e::[]) es
    in

    let rec f visited acc to_visit =
      match to_visit with
      | [] -> acc
      | curr_st::sts when List.mem curr_st visited  ->
        f visited acc sts
      | curr_st::sts ->
        let acc' = (List.filter p (succ_e fsm curr_st) |> List.map E.dst) @ acc in
        let visited' = curr_st::visited in
        let to_visit' = to_visit @ (sfe @@ step curr_st)  in
        f  visited' acc' (sts@to_visit')
    in
    f [] [] [st]

  let walk_with_function (st : vertex) (step : vertex -> edge list) (p : edge -> 'a) : 'a list =
    let visited : vertex list ref = ref [] in
    let add v = visited := v :: !visited in
    let was_visited v = List.mem v !visited in
    let rec f st res (k : 'a list -> 'b) =
      (* if it can step then done *)
      if was_visited st then k res
      else
        let sts, res' = step st |> List.map (fun e -> E.dst e, p e) |> List.split in
        add st ;
        fs sts (res' @ res) k

    and fs sts res (k : 'a list -> 'b) =
      match sts with
      | [] -> k res
      | st::sts ->
        f st res (fun res -> fs sts res k)
    in
    f st [] (fun x -> x)

  let walk_with_any_predicate (st : vertex) (step : vertex -> edge list) (p : edge -> bool) : bool =
    walk_with_function st step p |> List.exists ((=) true)

  let only_with_tau (fsm : t) (st : vertex) : edge list =
    succ_e fsm st |> List.filter (fun e -> E.label e = Label.default)

  let with_any_transition (fsm : t) (st : vertex) : edge list =
    succ_e fsm st

  (* if state can step with ANY transition, including tau *)
  let state_can_step (fsm : t) (st : vertex) : bool =
    succ fsm st |> Utils.is_empty|> not

  let get_reachable_labels (fsm : t) (st : vertex) : Label.t list  =
    walk_with_function st (with_any_transition fsm) (fun e -> E.label e)

  (* if the state can step with a non tau transition explore transitively *)
  let _state_can_step_recursive (fsm : t) (st : vertex) : bool =
    walk_with_any_predicate st (with_any_transition fsm) (fun e -> E.label e |> Label.is_default |> not)

  let has_strong_outgoing_transitions fsm st =
    succ_e fsm st |> List.filter (fun e -> E.label e = Label.default |> not) |> Utils.is_empty |> not

  let get_final_states (fsm : t) : vertex list =
    let has_no_successor st =
      succ fsm st |> Utils.is_empty
    in
    let has_predecessor st =
      pred fsm st |> Utils.is_empty |> not
    in
    let final_sts =
      get_vertices fsm |> List.filter (fun st -> has_no_successor st && has_predecessor st)
    in
    (* if there are not continuations, continue from a detached state *)
    if Utils.is_empty final_sts then [State.fresh()] else final_sts

  (* return all the tau reachable states *)
  let tau_reachable fsm st =
    walk_collect_vertices_with_predicate fsm st (only_with_tau fsm) (fun e -> E.label e = Label.default)

  let tau_reachable_labelled_edges fsm st =
    walk_collect_edges_with_predicate fsm st (only_with_tau fsm) (fun e -> E.label e = Label.default |> not)

  (* states that can be reached in one step with label a from st *)
  let can_reach_with_anything edges st a =
    List.filter_map (fun e -> if E.src e = st && E.label e = a then Some (E.dst e) else None) edges

  let can_reach_with_weak_step fsm st a =
    (* labels that are tau reachable from this state *)
    let weak_edges = tau_reachable_labelled_edges fsm st in
    (* add the set of tau reacheable states from the destination of the edge *)
    List.concat_map (fun e -> let dst = E.dst e in if E.label e = a then dst::(tau_reachable fsm dst) else []) weak_edges

  let minimise_state_numbers fsm =
    if Debug.minimise_state_numbers_off None then fsm
    else
      let vertices = get_vertices fsm |> List.mapi (fun n st -> (st, State.renumber_state n st)) in

      let fsm' = List.fold_left (fun fsm (_, st) -> add_vertex fsm st ) empty vertices in
      let update e =
        let tr st = List.assoc st vertices in
        E.create (E.src e |> tr) (E.label e) (E.dst e |> tr)
      in
      fold_edges_e (fun e fsm -> add_edge_e fsm (update e)) fsm fsm'

  (* simple merge two state machines *)
  let merge (fsm : t) (fsm' : t) : t =
    (* extend with vertices *)
    let with_vertices = fold_vertex (fun v g -> add_vertex g v) fsm' fsm in
    (* extend with edges *)
    let with_edges = fold_edges_e (fun e g -> add_edge_e g e) fsm' with_vertices in
    with_edges

  (* simple merge two state machines *)
  let merge_all (fsms : t list) : t =
    List.fold_left merge empty fsms

  let remove_reflexive_taus (fsm : t) : t =
    let e_fsm = fold_vertex (fun st fsm -> add_vertex fsm st) fsm empty in
    let is_reflexive_tau e =
      if (E.src e = E.dst e && E.label e |> Label.is_default)
      then true
      else
        false
    in
    fold_edges_e (fun e fsm -> if is_reflexive_tau e then fsm else add_edge_e fsm e) fsm e_fsm

  module StateEquivalenceClasess =
  struct

    (* a list whre each element is a list of the equivalent states *)
    type state_equivalence_class = vertex list list

    let _string_of_state_equivalence_class sec =
      List.map (fun l -> List.map State.as_string l |> String.concat "; ") sec |> String.concat " || "

    let canonicalise_start_end eq_sts =
      let make_head_start l =
        try
          let _ = List.hd l |> State.mark_as_start in ()
        with
        | Failure _ -> Error.Violation "The equivalence class needs a canonical element." |> raise
      in
      let make_head_end l =
        try
          let _ = List.hd l |> State.mark_as_end in ()
        with
        | Failure _ -> Error.Violation "The equivalence class needs a canonical element." |> raise
      in
      let canonicalise eq_st =
        if List.exists State.is_start eq_st then make_head_start eq_st ;
        if List.exists State.is_end eq_st then make_head_end eq_st ;
        eq_st
      in
      List.map canonicalise eq_sts

    let compute_from_pair_list (vss : (vertex * vertex) list) : state_equivalence_class =
      let find_list_and_rest v eq_sts =
        let have, rest = List.partition (List.mem v) eq_sts in
        match have with
        | [] -> [], rest
        | [have] -> have, rest
        | _::_ -> Error.Violation "Invariant: each vertex appears only once." |> raise
      in

      let merge (eq_sts : state_equivalence_class)
          ((v1, v2) : vertex * vertex) : state_equivalence_class =

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

    let translate (eqsts : state_equivalence_class) (fsm : t) : t =
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
        if E.label e |> Label.is_default
        then None
        else Some (E.create
                     (E.src e |> translate_st)
                     (E.label e)
                     (E.dst e |> translate_st))
      in
      fold_edges_e
        (fun e fsm ->
           match translate_edge e with
           | None -> fsm
           | Some e' -> add_edge_e fsm e')
        fsm empty
  end


  module Dot = struct
    module Display = struct
      include G

      let vertex_name v =
        string_of_int @@ State.get_id v

      let graph_attributes _ = [`Rankdir `LeftToRight]

      let default_vertex_attributes _ = []

      let vertex_attributes = function
        | v when State.is_start v && State.is_end v -> [`Shape `Doublecircle ; `Style `Filled ; `Fillcolor 0x7777FF ; `Label (State.as_string v)]
        | v when State.is_start v -> [`Shape `Circle ; `Style `Filled ; `Fillcolor 0x77FF77 ; `Label (State.as_string v)]
        | v when State.is_end v -> [`Shape `Doublecircle ; `Style `Filled ; `Fillcolor 0xFF7777 ; `Label (State.as_string v)]
        | v -> [`Shape `Circle ; `Label (State.as_string v) ]

      let default_edge_attributes _ = []

      let edge_attributes (e : edge) = [ `Label (Label.as_string @@ E.label e) ]

      let get_subgraph _ = None
    end

    module Output = Graphviz.Dot(Display)

    let generate_dot fsm =
      let buffer_size = 65536 in
      let buffer = Buffer.create buffer_size in
      let formatter = Format.formatter_of_buffer buffer in
      Output.fprint_graph formatter fsm ;
      Format.pp_print_flush formatter () ;
      Buffer.contents buffer
  end

end
