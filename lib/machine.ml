open Syntax
open Graph

module State = struct
  type t = { id : int
           ; is_start : bool ref
           ; is_end : bool ref
           }

  let equal s1 s2 = (s1.id = s2.id)

  let hash = Hashtbl.hash

  let compare s1 s2 = compare s1.id s2.id

  let mark_as_start s =
    s.is_start := true ; s

  let mark_as_end s =
    s.is_end := true ; s

  let as_string {id ; is_start ; is_end} =
    let s_str = if !is_start then "S" else "" in
    let e_str = if !is_end then "E" else "" in
    let extra = if !is_start || !is_end then s_str ^ e_str ^ "-" else "" in
    extra ^ (string_of_int id)

  let rec list_as_string = function
    | [] -> "[]"
    | s::ss -> as_string s ^ "::" ^ list_as_string ss

  (* let mark_as_not_end s = *)
  (*   s.is_end := false ; s *)

  let is_start s = !(s.is_start)
  let is_end s = !(s.is_end)

  let fresh, fresh_start, fresh_end, freshen =
    let n = ref 0 in
    ((fun () -> incr n ; {id = !n ; is_start = ref false ; is_end = ref false}),
     (fun () -> incr n ; {id = !n ; is_start = ref true ; is_end = ref false}),
     (fun () -> incr n ; {id = !n ; is_start = ref false ; is_end = ref true}),
     (fun st -> incr n ; {id = !n ; is_start = ref (is_start st) ; is_end = ref (is_end st)}))

  let renumber_state n {id = _ ; is_start ; is_end} = {id = n ; is_start ; is_end}

  let get_id {id ; _ } = id

end

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
end

module FSM (State : STATE) (Label : LABEL) = struct
  module G = Persistent.Digraph.ConcreteLabeled (State) (Label)
  include G

  let get_edges fsm =
    fold_edges_e (fun e l -> e::l) fsm []

  let string_of_edge e =
    "[" ^ (E.src e |> State.as_string) ^ "-|-"
    ^ (E.label e |> Label.as_string) ^ "-|-" ^ (E.dst e |> State.as_string) ^ "]"

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

  let walk_with_predicate (st : vertex) (step : vertex -> edge list) (p : edge -> bool) : bool =
    let rec f st visited =
      let edges_from_st = step st in
      (* if it can step then done *)
      if List.exists p edges_from_st then true
      else
        let rec check = function
          | [] -> false
          | e::es ->
            let dst = E.dst e in
            if List.mem dst visited then
              check es
            else
              f dst (st::visited) || check es
        in
        check edges_from_st
    in
    f st []

  let only_with_tau (fsm : t) (st : vertex) : edge list =
    succ_e fsm st |> List.filter (fun e -> E.label e = Label.default)

  let with_any_transition (fsm : t) (st : vertex) : edge list =
    succ_e fsm st

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

  let minimise_state_numbers fsm = fsm
  (* let minimise_state_numbers fsm = *)
  (*   let vertices = get_vertices fsm |> List.mapi (fun n st -> (st, State.renumber_state n st)) in *)

  (*   let fsm' = List.fold_left (fun fsm (_, st) -> add_vertex fsm st ) empty vertices in *)
  (*   let update e = *)
  (*     let tr st = *)
  (*       List.assoc st vertices *)
  (*     in *)
  (*     E.create (E.src e |> tr) (E.label e) (E.dst e |> tr) *)
  (*   in *)
  (*   fold_edges_e (fun e fsm -> add_edge_e fsm (update e)) fsm fsm' *)

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

  (* this function appears twice, move them to a generic module *)
  let disjoint_merge fsm fsm' =
    let copy src dst  =
      let vertices = get_vertices src |> List.map (fun st -> (st, State.freshen st)) in

      let dst' = List.fold_left (fun fsm (_, st) -> add_vertex fsm st ) dst vertices in
      let update e =
        let tr st =
          List.assoc st vertices
        in
        E.create (E.src e |> tr) (E.label e) (E.dst e |> tr)
      in
      fold_edges_e (fun e fsm -> add_edge_e fsm (update e)) src dst'
    in
    copy fsm @@ copy fsm' empty

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
    let generate_state_space fsm fsm' : 'a =
      let sts_fsm = get_vertices fsm in
      let sts_fsm' = get_vertices fsm' in
      "Size of sts_fsm: " ^ string_of_int (List.length sts_fsm) ^ " -- "  ^ (State.list_as_string sts_fsm) |> Utils.log;
      "Size of sts_fsm': " ^ string_of_int (List.length sts_fsm') ^ " -- "  ^ (State.list_as_string sts_fsm') |> Utils.log;
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
        (f : dict -> 's -> vertex * vertex -> ((edge * (vertex * vertex) * 's)) list)
        (init : 's)
      : dict * t =
      let dict, jfsm = generate_state_space fsm fsm' in
      let rec walk
          (sts : vertex * vertex)
          (curr : 's)
          (visited : vertex list)
          (jfsm : t)
          (k : vertex list -> t -> 'a) : 'a  =
        let curr_st = find_state_in_dest sts dict in
        if List.mem curr_st visited
        then k visited jfsm
        else
          (let jes = f dict curr sts in

           "START WALK" |> Utils.log;
           "Left: " ^ State.as_string (fst sts) |> Utils.log;
           "Right: " ^ State.as_string (snd sts) |> Utils.log;
           "Joint: " ^ State.as_string curr_st |> Utils.log;
           let ts el = List.map (fun (e,_,_)->e) el |> List.map string_of_edge |> String.concat ", " in
           "Edges: " ^ ts jes |> Utils.log;
           "END WALK" |> Utils.log;

           add_edges jes (curr_st::visited) jfsm k)

      and add_edges
          (pending : (edge * (vertex * vertex) * 's) list)
          (visited : vertex list)
          (jfsm : t)
          (k : vertex list -> t -> 'a) : ' a =
        match pending with
        | (je, next_sts, curr)::jes ->
          let jfsm = add_edge_e jfsm je in
          "ADDING: " ^ (string_of_edge je) |> Utils.log ;

          walk next_sts curr visited jfsm
            (fun visited jfsm -> add_edges jes visited jfsm k)

        | [] -> k visited jfsm

      in
      dict, walk initial_st init [] jfsm (fun _ x -> x)
  end

  (* compose two machines with a function *)
  let compose_with
      (sts : vertex * vertex)
      (assoc, fsm : vertex list * t)
      (assoc', fsm' : vertex list * t)
      f init :  vertex * (vertex list * t) =

    let dict, jfsm =
      MachineComposition.walker fsm fsm' sts f init in

    let assoc_space = List.fold_left (fun b a -> List.fold_left (fun b' a' -> (a, a')::b') b assoc') [] assoc in
    let res_assoc = List.map (fun stst' -> List.assoc stst' dict) assoc_space in

    let rec dict_to_string = function
      | [] -> "[]"
      | ((s1, s2), s3)::dict ->
        "(" ^ State.as_string s1 ^ ", " ^  State.as_string s2 ^ "), " ^  State.as_string s3 ^ ")::" ^ dict_to_string dict
    in

    Utils.log @@ dict_to_string dict ;
    "Size of fsm: " ^ string_of_int (nb_vertex fsm) |> Utils.log;
    "Size of fsm': " ^ string_of_int (nb_vertex fsm') |> Utils.log;
    "Size of space: " ^ string_of_int (List.length dict) |> Utils.log;
    MachineComposition.find_state_in_dest sts dict, (res_assoc, jfsm)

  (* compose two machines allowing all their interleavings *)
  let parallel_compose
      (sts : vertex * vertex)
      (assoc, fsm : vertex list * t)
      (assoc', fsm' : vertex list * t) :  vertex * (vertex list * t) =
    let open MachineComposition in
    compose_with sts (assoc, fsm) (assoc', fsm')
      (fun dict _ (st, st' as sts) ->
         let l_es = succ_e fsm st in
         let r_es = succ_e fsm' st' in

         let f side es =
           List.map
             (fun e ->
                translate_edge_to_joint_fsm sts side dict e,
                build_joint_state sts side (E.dst e),
                ())
             es
         in
         f L l_es @ f R r_es) ()

  (* compose two machines allowing only their common labels *)
  let tight_intersection_compose
      (sts : vertex * vertex)
      (assoc, fsm : vertex list * t)
      (assoc', fsm' : vertex list * t) :  vertex * (vertex list * t) =
    let open MachineComposition in
    compose_with sts (assoc, fsm) (assoc', fsm')
      (fun dict _ (st, st') ->
         let l_es = succ_e fsm st in
         let r_es = succ_e fsm' st' in

         let l_es' = List.filter (fun e -> List.mem (E.label e) (List.map E.label r_es)) l_es in

         let f side es =
           List.map
             (fun e ->
                translate_edge_to_joint_fsm sts side dict e,
                build_joint_state sts side (E.dst e),
                ())
             es
         in
         f L l_es') ()

  (* let _restricted : (vertex * Label.t * MachineComposition.side) list ref = ref [] *)

  (* compose two machines allowing only their common labels *)
  let loose_intersection_compose _ _ _ =
    (* (sts : vertex * vertex) *)
    (* (assoc, fsm : vertex list * t) *)
    (* (assoc', fsm' : vertex list * t) :  vertex * (vertex list * t) = *)
    (* let pair_with_unit = List.map (fun x -> x, ()) in *)
    (* compose_with sts (assoc, fsm) (assoc', fsm') *)
    (*   (fun _ (st, st') -> *)
    (*      let l_es = succ_e fsm st in *)
    (*      let r_es = succ_e fsm' st' in *)

    (*      let get_restricted l1 l2 side = List.filter_map *)
    (*          (fun e -> *)
    (*             if List.mem (E.label e) (List.map E.label l2) *)
    (*             then Some (E.src e, E.label e, side) *)
    (*             else None) *)
    (*          l1 *)
    (*      in *)
    (*      let is_restricted e side = *)
    (*        List.exists (fun (st, l, side') -> E.src e = st && E.label e = l && side = side') !restricted *)
    (*      in *)
    (*      let l_es' = *)
    (*        List.filter (fun e -> is_restricted e L |> not) l_es in *)

    (*      let r_es' = *)
    (*        List.filter (fun e -> is_restricted e R |> not) r_es in *)

    (*      restricted := get_restricted l_es r_es L @ get_restricted r_es l_es R @ !restricted ; *)

    (*      (\* only if they not appear in the other list, this is broken *\) *)
    (*      let l_es' = List.filter (fun e -> not(List.mem (E.label e) (List.map E.label r_es))) l_es' in *)
    (*      let ts el = List.map E.label el |> List.map Label.as_string |> String.concat ", " in *)
    (*      "Loose intersection" |> Utils.log ; *)
    (*      "Left: " ^ ts l_es' |> Utils.log ; *)
    (*      "Right: " ^ ts r_es |> Utils.log ; *)
    (*      l_es' |> pair_with_unit, r_es' |> pair_with_unit) () *)
    assert false

  let only_reachable_from _ fsm = fsm
  (* let only_reachable_from st fsm =  *)
  (* let add_state_and_successors n_fsm st = *)
  (*   let next_sts = succ fsm st in *)
  (*   let next_edges = succ_e fsm st in *)

  (*   let n_fsm' = List.fold_left (fun fsm st -> add_vertex fsm st ) (add_vertex n_fsm st) next_sts in *)
  (*   List.fold_left (fun fsm e -> add_edge_e fsm e) n_fsm' next_edges *)
  (* in *)

  (* let rec f n_fsm visited to_visit = *)
  (*   match to_visit with *)
  (*   | [] -> n_fsm *)
  (*   |  st::remaining -> *)
  (*     (\* states reachable from st *\) *)
  (*     let reachable = succ fsm st in *)
  (*     let n_fsm' = add_state_and_successors n_fsm st in *)

  (*     let visited' = st::visited in *)
  (*     let to_visit' = Utils.minus (reachable @ remaining) visited' in *)
  (*     f n_fsm' visited' to_visit' *)
  (* in *)
  (* f empty [] [st] *)

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

  type block = vertex list

  let blocks_as_string (bs : block list) : string =
    List.map
      (fun b ->
         "["
         ^ (List.map State.as_string b |> String.concat "; ")
         ^ "]")  bs |> String.concat "\n"

  let compute_bisimulation_quotient (fsm : FSM.t) : block list =
    "Start computing bisimul quot." |> Utils.log;
    let initial () : block list * FSM.edge list =
      (* a singleton block with all the states to be refined *)
      let bs : block list = [FSM.fold_vertex (fun st l -> st :: l) fsm []] in
      let edges = get_edges fsm in
      bs, edges
    in

    let bs, edges = initial() in
    "States: " ^ State.list_as_string (List.hd bs) |> Utils.log ;
    (* Performance: this is quite naive, as we compare lots of blocks for identity, so many
       very slow comparisons of lists. If we run into performance probles,
       this is a thing to improve. It should not be hard once the system is working. *)

    let find_state_in_blocks st bs =
      List.filter (List.mem st) bs
    in

    let can_reach_block st a bs =
      let sts = if Str.is_strong then
          (* this makes it a strong bisimulation *)
          can_reach_with_anything edges st a
        else
          (* this makes it a weak bisimulation *)
          can_reach_with_weak_step fsm st a
      in
      List.map (fun st -> find_state_in_blocks st bs) sts |> Utils.uniq
    in

    let split (b : block) (a : Label.t) (bs : block list) : block * block =
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

    let compute (bs : block list) : 'a =
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
    let bs' = compute_while_changes bs in
    "Blocks are:\n" ^ blocks_as_string bs' |> Utils.log ;
    bs'

  let dict_as_string dict =
    List.map (fun (a, b) -> "(" ^ State.list_as_string a ^ " |-> " ^ State.as_string b ^ ")") dict |> String.concat "\n\t"

  let _extract_minimal (bs : block list) (es : FSM.edge list) : FSM.t =
    let new_state_from_block b =
      let st = State.fresh() in
      let st = if List.exists State.is_start b then State.mark_as_start st else st in
      let st = if List.exists State.is_end b then State.mark_as_end st else st in
      st
    in
    let st_dict = List.map (fun b -> b, new_state_from_block b) bs in
    "Translation dictionary is :" ^ dict_as_string st_dict |> Utils.log ;
    let lookup st =
      let rec l = function
        | [] -> Error.Violation "State not found, this is a bug!" |> raise
        | (b, st')::_ when List.mem st b -> st'
        | _::dict -> l dict
      in
      l st_dict
    in

    (* add states *)
    let fsm = List.fold_left (fun fsm (_, st) -> FSM.add_vertex fsm st) FSM.empty st_dict in
    (* add edges *)
    List.fold_left (fun fsm e -> FSM.add_edge_e fsm (FSM.E.create (FSM.E.src e |> lookup) (FSM.E.label e) (FSM.E.dst e |> lookup)) ) fsm es

  let are_states_bisimilar (blocks : block list) st1 st2 : bool =
    let find_block (st : vertex) =
      let find_in_block bl =
        List.mem st bl
      in
      List.find find_in_block blocks
    in
    find_block st1 = find_block st2

  (* let minimise (fsm : FSM.t) : FSM.t = *)
  (*   extract_minimal (compute_bisimulation_quotient fsm) (get_edges fsm) *)
  let minimise (fsm : FSM.t) : FSM.t = fsm

  let remove_reflexive_taus (fsm : FSM.t) : FSM.t =
    let e_fsm = fold_vertex (fun st fsm -> add_vertex fsm st) empty fsm in
    let is_reflexive_tau e = E.src e = E.dst e && E.label e = Label.default in
    fold_edges_e (fun e fsm -> if is_reflexive_tau e then fsm else add_edge_e fsm e) e_fsm fsm

  let generate_minimal_dot fsm =
    fsm |> minimise |> remove_reflexive_taus |> FSM.Dot.generate_dot
end

module Global = struct
  module Label = struct
    type t = transition_label option

    let default : t = None

    let compare = Stdlib.compare (* consider a more specific one *)

    let project r lbl =
      Option.bind lbl
        (fun l-> Operations.Local.project_transition r l)

    let as_string = function
      | None -> "τ"
      | Some l -> string_of_transition_label l
  end

  module FSM = FSM (State) (Label)
  include FSM

  let filter_degenerate_branches branches =
    List.filter (function Seq [] -> false | _ -> true) branches

  let generate_state_machine' (g : global) : vertex * FSM.t =
    let start = State.fresh_start () in

    (* tr does the recursive translation.
       s_st and e_st are the states that will bound the translated type
       next is a list of states that lead to the machine we are currently translating
       and the first element of the returned value is the places where the execution will continue
    *)
    let rec tr
        (fsm : t)
        (g : global)
        (s_st, e_st : vertex * vertex)
        (next : vertex list) : vertex list *t =
      "s_st = " ^ State.as_string s_st |> Utils.log ;
      "e_st = " ^ State.as_string e_st |> Utils.log ;
      match g with
      | MessageTransfer lbl ->
        let e x y = FSM.E.create x (Some lbl) y in
        let fsm' = List.fold_left (fun fsm st -> FSM.add_edge_e fsm (e st e_st)) fsm next in
        [e_st], fsm'

      | Seq gis ->
        let rec connect fsm gis (s_st, e_st) next =
          match gis with
          | [g'] ->
            tr fsm g' (s_st, e_st) next

          | g'::gs ->
            let fresh_st = State.fresh() in
            let next', fsm' = tr fsm g' (s_st, fresh_st) next in
            connect fsm' gs (fresh_st, e_st) next'

          | [] ->
            let st = State.fresh_start () |> State.mark_as_end in
            "Empty sequence state:" ^ State.as_string st |> Utils.log;
            st::next, FSM.add_vertex FSM.empty st

        in
        connect fsm gis (s_st, e_st) next

      | Choice branches ->
        if List.length branches = 0 then next, fsm else
          let nexts, fsms = List.map (fun g -> tr fsm g (s_st, State.fresh()) next) branches |> List.split in
          let fsm' = merge_all fsms in
          List.concat nexts |> Utils.uniq, fsm'

      | Fin g' ->
        let next', fsm' = tr fsm g' (s_st, e_st) next in
        let next'', fsm'' = tr fsm' g' (e_st, e_st) next' in
        next @ next' @ next'' @ [e_st] |> Utils.uniq, fsm''

      | Inf g' ->
        let fresh_st = State.fresh() in
        let next', fsm' = tr fsm g' (s_st, fresh_st) next in
        let _, fsm'' = tr fsm' g' (fresh_st, fresh_st) next' in
        [e_st] |> Utils.uniq, fsm''

      | Par [] ->
        "EMPTY PAR" |> Utils.log ;
        next, fsm

      | Par branches ->
        let branches = filter_degenerate_branches branches in
        if List.length branches = 0 then next, fsm else
          combine_branches fsm (s_st, e_st) branches parallel_compose next

      | LInt branches ->
        let branches = filter_degenerate_branches branches in
        if List.length branches = 0 then next, fsm else
          combine_branches fsm (s_st, e_st) branches loose_intersection_compose next

      | TInt branches ->
        let branches = filter_degenerate_branches branches in
        if List.length branches = 0 then next, fsm else
          combine_branches fsm (s_st, e_st) branches tight_intersection_compose next

      | Prioritise _ -> Error.Violation "Prioritise not yet implemented." |> raise


    and combine_branches fsm (s_st, e_st) branches f next =
      let m () =
        FSM.add_vertex (FSM.add_vertex FSM.empty s_st) e_st
      in
      let next_fsms = List.map (fun g -> s_st, tr (m ()) g (s_st, e_st) next) branches in
      List.iter
        (fun (_, stfsm) ->
           "branch number of vertices: " ^
           (FSM.nb_vertex (snd stfsm) |> string_of_int) |> Utils.log) next_fsms;
      let nexts, fsm' =
        match next_fsms with
        | [] -> [], m ()
        | [_, next_fsm] -> next_fsm
        | s_st_next_fsm::next_fsms' ->
          (List.fold_left
             (fun (s_st, fsm) (s_st', fsm') ->
                f (s_st, s_st') fsm fsm') s_st_next_fsm next_fsms') |> snd
      in
      let resfsm = merge fsm fsm' in
      let size = resfsm |> FSM.get_vertices |> List.length |> Int.to_string in
      "COMBINE size result: " ^ size |> Utils.log ;
      nexts, resfsm
    in
    let end_st = State.fresh_end() in
    let next, fsm_final = tr FSM.empty g (start, end_st) [start] in
    List.iter (fun st -> let _ = State.mark_as_end st in ()) next ;
    (start, fsm_final |> only_reachable_from start)

  module B = Bisimulation (State) (Label) (struct let is_strong = true end)
  let minimise fsm = B.minimise fsm

  let generate_state_machine (g : global) : vertex * FSM.t =
    let st, fsm = generate_state_machine' g in
    st, minimise fsm |> minimise_state_numbers

  let generate_dot fsm = fsm |> Dot.generate_dot

  let generate_minimal_dot fsm =
    let module WB = Bisimulation (State) (Label) (struct let is_strong = false end) in
    WB.generate_minimal_dot fsm
end

module Local = struct
  module Label = struct
    type t = Syntax.Local.local_transition_label option

    let default : t = None

    let compare = Stdlib.compare (* consider a more specific one *)

    let as_string = function
      | None -> "τ"
      | Some l -> Syntax.Local.string_of_local_transition_label l
  end

  module FSM = FSM (State) ( Label)
  include FSM

  (* if state can step with ANY transition, including tau *)
  let state_can_step (fsm : FSM.t) (st : vertex) : bool =
    FSM.succ fsm st |> Utils.is_empty|> not

  (* if the state can step with a non tau transition explore transitively *)
  let _state_can_step_recursive (fsm : FSM.t) (st : vertex) : bool =
    walk_with_predicate st (with_any_transition fsm) (fun e -> FSM.E.label e |> Option.is_some)

  let _has_outgoing_transitions fsm st =
    succ_e fsm st |> Utils.is_empty |> not

  let _has_strong_outgoing_transitions fsm st =
    succ_e fsm st |> List.filter (fun e -> E.label e = Label.default |> not) |> Utils.is_empty |> not


  let project (r : Syntax.role) (fsm : Global.FSM.t) : FSM.t =
    "Projecting role: " ^  r |> Utils.log ;
    (* add the \tau transitions induced by L-Rev *)
    let complete fsm : FSM.t =
      let tau_edges = FSM.fold_edges_e (fun e l -> if FSM.E.label e |> Option.is_none then e::l else l) fsm []  in

      let reverse_edge e =
        FSM.E.create (FSM.E.dst e) (FSM.E.label e) (FSM.E.src e)
      in

      let new_tau_edges = List.filter_map (fun e -> if state_can_step fsm (FSM.E.dst e) then Some (reverse_edge e) else None) tau_edges in

      List.fold_left FSM.add_edge_e fsm new_tau_edges
    in

    let project_edge e =
      FSM.E.create
        (Global.FSM.E.src e)
        (Global.Label.project r (Global.FSM.E.label e))
        (Global.FSM.E.dst e)
    in
    let with_vertices = Global.FSM.fold_vertex (fun s f -> FSM.add_vertex f s) fsm FSM.empty in
    let with_edges =
      Global.FSM.fold_edges_e
        (fun e f -> FSM.add_edge_e f (project_edge e))
        fsm
        with_vertices
    in
    with_edges |> complete


  type wb_res = (unit, string) Result.t

  module WB = Bisimulation (State) (Label) (struct let is_strong = false end)

  (* this is more applicative than monadic, as previous results don't change the future results *)
  let special_bind (v : wb_res) (f : unit -> wb_res) : wb_res =
    match v with
    | Result.Ok _ -> f ()
    | Result.Error msg ->
      begin match f() with
        | Result.Ok _ -> Result.Error msg
        | Result.Error msg' -> msg ^ "\n" ^ msg' |> Result.error
      end

  let rec pipe_fold (f: 'a -> wb_res)  (res : wb_res) : 'a list -> wb_res =
    let (let*) = special_bind in
    function
    | [] -> res
    | x::xs ->
      pipe_fold f (let* _ = res in f x) xs

  let rec wb r (st, fsm : vertex * t) : wb_res =
    let (let*) = special_bind in
    let _blocks = WB.compute_bisimulation_quotient fsm in
    let* _res = _c1 r (st, fsm) in
    let* _res = _c2 r _blocks (st, fsm) in
    let* _res = _c3 r _blocks (st, fsm) in
    let* _res = _c4 r _blocks (st, fsm) in
    _res |> Result.ok

  and _c1_alt r (st, fsm) : wb_res =
    (* if _state_can_step_recursive fsm st then *)
    (* if _has_outgoing_transitions fsm st then *)
    if _has_strong_outgoing_transitions fsm st then
      let weak_sts = st::tau_reachable fsm st in
      if List.exists State.is_end weak_sts then
        "For role: " ^ r ^ " state: " ^ State.as_string st ^ " may terminate or continue (C1 violation)." |> Result.error
      else
        Result.ok ()
    else Result.ok ()

  and _c1 r (st, fsm) : wb_res =
    if _has_strong_outgoing_transitions fsm st then
      if State.is_end st then
        "For role: " ^ r ^ " state: " ^ State.as_string st ^ " may terminate or continue (C1 violation)." |> Result.error
      else
        Result.ok ()
    else Result.ok ()


  and _c2 r blocks (st, fsm) : wb_res =
    let by_tau = tau_reachable fsm st in
    if List.for_all (fun st' -> WB.are_states_bisimilar blocks st st') by_tau
    then Result.ok ()
    else
      try
        let st' = List.find (fun st' -> WB.are_states_bisimilar blocks st st' |> not) by_tau in
        "For role: " ^ r ^ " states: " ^ State.as_string st ^ " and " ^ State.as_string st' ^ " are not bisimilar (C2 violation)." |> Result.error
      with
        _ -> Error.Violation "This is a bug. There must be a non bisimilar state."  |> raise

  (* type local_transition_label = {sender: role ; receiver: role ; direction : direction ; label: message_label} *)
  and _c3 r blocks (st, fsm) : wb_res =
    let is_send = function
      | Some l -> l.Syntax.Local.direction = Syntax.Local.Sending
      | None -> false
    in
    let by_tau = tau_reachable fsm st in

    (* send labels and their states *)
    let _sends =
      List.concat_map
        (fun st' -> List.filter_map (fun e -> if E.label e |> is_send then Some (E.label e, E.dst e) else None) (succ_e fsm st'))
        by_tau
    in

    (* makes the original state step with the labelled transition *)
    let one_step (l : Label.t) st_error =
      try
        List.find (fun e -> l = E.label e) (succ_e fsm st) |> E.dst |> Result.ok
      with
      | Not_found ->
        "For role: " ^ r ^
        " state: " ^ State.as_string st
        ^ " cannot take label: " ^ Label.as_string l
        ^ " that reaches with tau state: " ^ State.as_string st_error
        ^ " (C3 Violation)."
        |> Result.error
    in

    (* checks if the states are bisimilar after taking the step *)
    let check st l st' =
      let (let*) = Result.bind in
      let* st_succ = one_step l st' in
      if WB.are_states_bisimilar blocks st_succ st' then
        Result.ok ()
      else
        "States: " ^ State.as_string st
        ^ " is not bisimilar to state: " ^ State.as_string st'
        ^ " after taking label: " ^ Label.as_string l
        ^ " (C3 violation)."
        |> Result.error
    in

    List.fold_left (fun r (l, st') -> Result.bind r (fun _ -> check st l st')) (Result.ok ()) _sends

  and _c4 r blocks (st, fsm) : wb_res =
    let is_receive = function
      | Some l -> l.Syntax.Local.direction = Syntax.Local.Receiving
      | None -> false
    in
    let by_tau = st::tau_reachable fsm st in
    let weak_reductions =
      List.concat_map
        (fun st' -> succ_e fsm st' |> List.filter (fun e -> E.label e |> Option.is_some))
        by_tau
    in
    let rec f = function
      | [] -> Result.ok ()
      | e::es ->
        (* split in the edges with a different label, and the states that the same label transitions to *)
        let es_diff, st_same =
          List.fold_left
            (fun (d, s) e' ->
               if E.label e = E.label e'
               then
                 let t_r = tau_reachable fsm (E.dst e) in
                 let t_r' = tau_reachable fsm (E.dst e') in
                 (d, (E.dst e)::(E.dst e')::t_r @ t_r' @ s)
               else (if E.label e' |> is_receive then  e'::d,s else d, s))
            ([], [])
            es
        in
        let are_bisim = match st_same with
          | [] -> Result.ok ()
          | [_] -> Result.ok ()
          | s::ss ->
            let check s s' =
              if WB.are_states_bisimilar blocks s s' then
                Result.ok ()
              else
                "For role: " ^ r
                ^ " states: " ^ State.as_string s
                ^ " is not bisimilar to state: " ^ State.as_string s'
                ^ " after taking label: " ^ Label.as_string (E.label e)
                ^ " (C4 violation)."
                |> Result.error
            in
            List.fold_left (fun r s' -> Result.bind r (fun _ -> check s s')) (Result.ok ()) ss
        in
        Result.bind are_bisim (fun _ -> f es_diff)
    in
    f (weak_reductions |> List.filter (fun e -> E.label e |> is_receive))

  and c5 r fsm visited to_visit : wb_res =
    match to_visit with
    | [] -> Result.ok ()
    | st::_ when List.mem st visited -> Result.ok ()
    | st::sts ->
      begin match wb r (st, fsm) with
        | Result.Ok () ->
          let to_visit' = Utils.minus ((succ fsm st) @ sts) visited in
          c5 r fsm (st::visited) to_visit'
        | Result.Error err -> Result.error err
      end

  let well_behaved_role (r, st, fsm : role  * vertex * t) : wb_res =
    c5 r fsm [] [st]

  let well_behaved_protocol (proto : global protocol) : wb_res =
    let roles = proto.roles in
    let g = proto.interactions in
    let _start, gfsm = Global.generate_state_machine g in

    let lfsms = List.map (fun r -> let l = project r gfsm in r, get_start_state l, l) roles in

    pipe_fold well_behaved_role (Result.ok ()) lfsms

  let generate_dot fsm = fsm |> Dot.generate_dot

  let generate_minimal_dot fsm =
    let module WB = Bisimulation (State) (Label) (struct let is_strong = false end) in
    WB.generate_minimal_dot fsm

  let generate_all_local protocol =
    let roles = protocol.roles in

    let local_machine (g : global) (r : role) =
      let _, gfsm = Global.generate_state_machine g in
      project r gfsm
    in

    List.fold_left (fun fsm r -> let lfsm = local_machine protocol.interactions r in disjoint_merge lfsm fsm) FSM.empty roles
end
