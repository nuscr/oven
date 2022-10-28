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

  module MachineComposition =
  struct
    (* Monadic interface commented out for now *)
    (* (\* monad for the edge selection *\) *)
    (* type ('a , 's) m = 's -> 's * 'a *)
    (* let sbind (m1 : ('a, 's) m) (m2: 'a -> ('a, 's) m) : ('a, 's) m = *)
    (*   fun s -> let a, s' = m1 s in m2 a s' *)

    (* let run (initial_state : 's) (v : ('a, 's) m) : 'a = *)
    (*   v initial_state |> snd *)

    (* let (let*\) = sbind *)

    (* relation between the combined and resulting fsms *)
    type dict = ((vertex * vertex) * vertex) list (* ((s1, s2), s3) state s1 and s2 became s3 *)

    (* generate product state space *)
    let generate_state_space fsm fsm' =
      let sts_fsm = get_vertices fsm in
      let sts_fsm' = get_vertices fsm' in
      (* new combined_state *)
      let ncs st st' =
        let new_st () =
          let new_st = State.fresh() in
          let new_st' = if State.is_start st && State.is_start st' then State.mark_as_start new_st else new_st in
          if State.is_end st && State.is_end st' then State.mark_as_end new_st' else new_st'
        in
        if  st = st' then st else
          new_st ()
      in
      let state_space = List.fold_left (fun b a  -> List.fold_left (fun b' a' -> ((a, a'), ncs a a')::b') b sts_fsm') [] sts_fsm in
      (* generate state_machine for the combined state *)
      let machine = List.fold_left (fun fsm (_, st) -> add_vertex fsm st) empty state_space
      in
      state_space, machine

    let find_state_in_dest (st, st') (dict : dict) =
      try
        List.find_map
          (fun ((st1, st1'), rst) -> if st = st1 && st' = st1' then Some rst else None)
          dict |> Option.get
      with
      | _ -> Error.Violation "Joint FSM must contain this state." |> raise

    type side = L | R

    let build_joint_state (st, st') side st_tr =
      match side with
      | L -> (st_tr, st')
      | R -> (st, st_tr)

    let _get_states_with side dict st =
      List.find_all
        (fun (sts, _) -> match side with
           | L -> st = fst sts | R -> st = snd sts)
        dict |> List.map fst

    let translate_state_to_joint_fsm sts side dict st_tr =
      List.assoc (build_joint_state sts side st_tr) dict

    let translate_edge_to_joint_fsm sts side dict e =
      let coord = translate_state_to_joint_fsm sts side dict in
      E.create (E.src e |> coord) (E.label e) (E.dst e |> coord)

    let walker (fsm : t) (fsm' : t) (initial_st : vertex * vertex)
        (walk_fun : dict -> vertex * vertex -> ((edge * (vertex * vertex))) list)
      : dict * (vertex list * t) =
      let dict, jfsm = generate_state_space fsm fsm' in
      let rec walk
          (sts : vertex * vertex)
          (visited : vertex list)
          (jfsm : t)
          (k : vertex list -> t -> 'a) : 'a  =
        let curr_st = find_state_in_dest sts dict in
        if List.mem curr_st visited
        then k visited jfsm
        else
          let jes = walk_fun dict sts in
          add_edges jes (curr_st::visited) jfsm k

      and add_edges
          (pending : (edge * (vertex * vertex)) list)
          (visited : vertex list)
          (jfsm : t)
          (k : vertex list -> t -> 'a) : ' a =
        match pending with
        | (je, next_sts)::jes ->
          let jfsm = add_edge_e jfsm je in
          walk next_sts visited jfsm
            (fun visited jfsm -> add_edges jes visited jfsm k)

        | [] -> k visited jfsm

      in
      walk initial_st [] jfsm (fun _visited fsm -> dict, (get_final_states fsm, fsm))
  end

  (* compose two machines with a function *)
  let compose_with
      (sts : vertex * vertex)
      (fsm : t)
      (fsm' : t)
      (* from the dict and the current state, produce a list of edges and the one next state per edge *)
      (f : MachineComposition.dict -> vertex * vertex -> (edge * (vertex * vertex)) list)
    :  vertex * (vertex list * t) =

    let dict, next_jfsm = MachineComposition.walker fsm fsm' sts f in
    MachineComposition.find_state_in_dest sts dict, next_jfsm

  (* compose two machines allowing all their interleavings *)
  let parallel_compose
      (sts : vertex * vertex)
      (fsm : t)
      (fsm' : t) :  vertex * (vertex list * t) =
    let open MachineComposition in
    compose_with sts fsm fsm'
      (fun dict (st, st' as sts) ->
         let l_es = succ_e fsm st in
         let r_es = succ_e fsm' st' in

         let f side es =
           List.map
             (fun e ->
                translate_edge_to_joint_fsm sts side dict e,
                build_joint_state sts side (E.dst e))
             es
         in
         f L l_es @ f R r_es)

  (* compose two machines allowing only their common labels *)
  let intersection_compose
      (sts : vertex * vertex)
      (fsm : t)
      (fsm' : t) :  vertex * (vertex list * t) =
    let open MachineComposition in
    compose_with sts fsm fsm'
      (fun dict (st, st') ->
         let l_es = succ_e fsm st in
         let r_es = succ_e fsm' st' in

         let l_es' = List.filter (fun e -> List.mem (E.label e) (List.map E.label r_es)) l_es in

         let f side es =
           List.map
             (fun e ->
                translate_edge_to_joint_fsm sts side dict e,
                build_joint_state sts side (E.dst e))
             es
         in
         f L l_es')

  (* compose two machines joining their common labels, and allowing free interleavings of the rest *)
  let join_compose
      (sts : vertex * vertex)
      (fsm : t)
      (fsm' : t) :  vertex * (vertex list * t) =
    let get_size_as_str fsm = get_vertices fsm |> List.length |> string_of_int in
    "FSM size = " ^ get_size_as_str fsm |> Utils.log ;
    "FSM' size = " ^ get_size_as_str fsm' |> Utils.log ;
    let open MachineComposition in
    compose_with sts fsm fsm'
      (fun dict (st, st' as sts) ->
         let l_es = succ_e fsm st in
         let r_es = succ_e fsm' st' in

         (* if the transition is enabled in both, then it's ok *)
         let l_both = List.filter (fun e -> List.mem (E.label e) (List.map E.label r_es)) l_es in

         let left_labels = get_reachable_labels fsm st in
         let right_labels = get_reachable_labels fsm' st' in

         (* edges on the left, that are never on the right *)
         let l_es' = List.filter (fun e -> List.mem (E.label e) right_labels |> not)  l_es in
         (* edges on the right, that are never on the left *)
         let r_es' = List.filter (fun e -> List.mem (E.label e) left_labels |> not)  r_es in

         let get_edge_with_label es l =
           List.find (fun e -> E.label e = l) es
         in

         let f_both es =
           let lbls = List.map E.label es in

           List.map (fun l ->
               let jsrc = List.assoc (st, st') dict in

               let dst = get_edge_with_label l_es l |> E.dst in
               let dst' = get_edge_with_label r_es l |> E.dst in

               let jdst = List.assoc (dst, dst') dict in

               E.create jsrc l jdst, (dst, dst')
             )
             lbls
         in
         let f_sided side es =
           List.map
             (fun e ->
                translate_edge_to_joint_fsm sts side dict e,
                build_joint_state sts side (E.dst e))
             es
         in

         f_both l_both @ f_sided L l_es' @ f_sided R r_es'
      )


  type priority_source
    = FirstMachine
    | SecondMachine
    | NoMachine

  let rec prioritise
      (initial_fsm : t)
      (fsm : t) (s_st : vertex)
      (fsm1 : t) (s1_st : vertex)
      (fsm2 : t) (s2_st : vertex)
    : vertex list * t =
    let edges_with_labels_in es lbls =
      List.filter (fun e -> List.mem (E.label e) lbls) es
    in
    let rec pr i s s1 s2 visited =
      if List.mem s visited then i
      else
        (* all the edges to rank *)
        let es =
          try succ_e fsm s with
            e -> raise (Error.Violation ("Unexpected, succ_e failed with: " ^ Printexc.to_string e))
        in
        (* labels available in f1 and f2 *)
        let f1_lbls = succ_e fsm1 s1 |> List.map E.label in
        let f2_lbls = succ_e fsm2 s2 |> List.map E.label in
        (* edges that are in f1 or f2 respectively *)
        let es_in_f1 = edges_with_labels_in es f1_lbls in
        let es_in_f2 = edges_with_labels_in es f2_lbls in
        let m, next_es =
          if Utils.is_non_empty es_in_f1
          then FirstMachine, es_in_f1
          else if Utils.is_non_empty es_in_f2
          then SecondMachine, es_in_f2
          else NoMachine, es
        in
        (* add the edges and continue *)
        prs i m next_es s1 s2 (s::visited)

    and prs i m es s1 s2 visited =
      let find_edge_with_label m st lbl =
        try
          succ_e m st |> List.find (fun e -> E.label e = lbl)
        with
          Not_found -> Error.Violation "Unexpected: the label must be in the list." |> raise
      in
      match es, m with
      | [], _ -> i

      | e::es, FirstMachine ->
        let s1' = find_edge_with_label fsm1 s1 (E.label e) |> E.dst in
        let i = pr (add_edge_e i e) (E.dst e) s1' s2 visited in
        prs i m es s1' s2 visited

      | e::es, SecondMachine ->
        let s2' = find_edge_with_label fsm2 s2 (E.label e) |> E.dst in
        let i = pr (add_edge_e i e) (E.dst e) s1 s2' visited in
        prs i m es s1 s2' visited

      | e::es, NoMachine ->
        let i = pr (add_edge_e i e) (E.dst e) s1 s2 visited in
        prs i m es s1 s2 visited
    in
    let res = pr initial_fsm s_st s1_st s2_st [] in
    get_final_states res, res

  let only_reachable_from st fsm =
    let add_state_and_successors n_fsm st =
      let next_sts = succ fsm st in
      let next_edges = succ_e fsm st in

      let n_fsm' = List.fold_left (fun fsm st -> add_vertex fsm st ) (add_vertex n_fsm st) next_sts in
      List.fold_left (fun fsm e -> add_edge_e fsm e) n_fsm' next_edges
    in

    let rec f n_fsm visited to_visit =
      match to_visit with
      | [] -> n_fsm
      |  st::remaining ->
        (* states reachable from st *)
        let reachable = succ fsm st in
        let n_fsm' = add_state_and_successors n_fsm st in

        let visited' = st::visited in
        let to_visit' = Utils.minus (reachable @ remaining) visited' in
        f n_fsm' visited' to_visit'
    in

    if Debug.keep_only_reacheable_off None
    then fsm
    else f empty [] [st]

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

  let generate_minimal_dot fsm =
    fsm |> minimise |> FSM.remove_reflexive_taus |> FSM.Dot.generate_dot
end
