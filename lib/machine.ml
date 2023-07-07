open Graph

open Utils.List

module type STATE =
sig
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

module type LABEL =
sig
  type t

  val default : t

  val compare : t -> t -> int

  val as_string : t -> string
  val list_as_string : t list -> string

  val is_default : t -> bool
end

module type FSM =
sig
  type t

  module State : STATE
  module Label : LABEL

  type vertex = State.t

  module E :
  sig
    type t
    val compare : t -> t -> int
    val src : t -> vertex
    val dst : t -> vertex
    type label = Label.t
    val create : vertex -> label -> vertex -> t
    val label : t -> label
  end

  val get_vertices : t -> vertex list
  val get_start_state : t -> vertex
  val add_vertex : t -> vertex -> t
  val empty : t

  val has_start : t -> bool

  type edge = E.t
  val get_edges : t -> edge list
  val add_edge : t -> vertex -> vertex -> t
  val add_edge_e : t -> edge -> t
  val succ : t -> vertex -> vertex list
  val succ_e : t -> vertex -> edge list
  val fold_edges :
    (vertex -> vertex -> 'a -> 'a) -> t -> 'a -> 'a
  val iter_edges_e : (edge -> unit) -> t -> unit
  val fold_edges_e : (edge -> 'a -> 'a) -> t -> 'a -> 'a
  val iter_vertex : (vertex -> unit) -> t -> unit
  val fold_vertex : (vertex -> 'a -> 'a) -> t -> 'a -> 'a

  val walk_collect_edges_with_predicate :
    t -> vertex-> (vertex -> edge list) -> (edge -> bool) -> edge list
  val walk_collect_vertices_with_predicate :
    t -> vertex -> (vertex -> edge list) -> (edge -> bool) -> vertex list
  val walk_with_function :
    vertex -> (vertex -> edge list) -> (edge -> 'a) -> 'a list
  val walk_with_any_predicate :
    vertex -> (vertex -> edge list) -> (edge -> bool) -> bool
  val only_with_tau : t -> vertex -> edge list
  val with_any_transition : t -> vertex -> edge list
  val state_can_step : t -> vertex -> bool
  val get_reachable_labels : t -> vertex -> E.label list
  val state_can_step_recursive : t -> vertex -> bool
  val has_strong_outgoing_transitions : t -> vertex -> bool
  val get_final_states : t -> vertex list
  val tau_reachable : t -> vertex -> vertex list
  val tau_reachable_labelled_edges : t -> vertex -> edge list
  val can_reach_with_anything :
    E.t list -> vertex -> E.label -> vertex list
  val can_reach_with_weak_step : t -> vertex -> E.label -> vertex list
  val minimise_state_numbers : t -> t
  val merge : t -> t -> t
  val merge_all : t list -> t
  val freshen_with_dict : t -> t * (vertex * vertex) list
  val remove_reflexive_taus : t -> t
  module Dot :
  sig
    val generate_dot : t -> string
  end
end

module StateMachine (State : STATE) (Label : LABEL) = struct
  module G = Persistent.Digraph.ConcreteLabeled (State) (Label)
  include G

  type t = G.t

  module State = State
  module Label = Label

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

  let has_start fsm =
    List.find_opt State.is_start @@ get_vertices fsm |> Option.is_some


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
  let state_can_step_recursive (fsm : t) (st : vertex) : bool =
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

  let freshen_with_dict (fsm : t) : t * (vertex * vertex) list =
    let dict =
      let vs = get_vertices fsm in
      List.map (fun v -> v, State.freshen v) vs
    in
    let trs v = List.assoc v dict in
    let tre e = E.create (E.src e |> trs) (E.label e) (E.dst e |> trs) in

    fold_edges_e (fun e fsm -> add_edge_e fsm (tre e)) fsm empty, dict

  let remove_reflexive_taus (fsm : t) : t =
    let e_fsm = fold_vertex (fun st fsm -> add_vertex fsm st) fsm empty in
    let is_reflexive_tau e =
      if (E.src e = E.dst e && E.label e |> Label.is_default)
      then true
      else
        false
    in
    fold_edges_e (fun e fsm -> if is_reflexive_tau e then fsm else add_edge_e fsm e) fsm e_fsm

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
