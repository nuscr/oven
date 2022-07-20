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

  (* let mark_as_not_end s = *)
  (*   s.is_end := false ; s *)

  let is_start s = !(s.is_start)
  let is_end s = !(s.is_end)

  let fresh, fresh_start, fresh_end =
    let n = ref 0 in
    ((fun () -> incr n ; {id = !n ; is_start = ref false ; is_end = ref false}),
     (fun () -> incr n ; {id = !n ; is_start = ref true ; is_end = ref false}),
     (fun () -> incr n ; {id = !n ; is_start = ref false ; is_end = ref true}))

  let renumber_state n {id = _ ; is_start ; is_end} = {id = n ; is_start ; is_end}
end

module Global = struct
  module Label = struct
    type t = transition_label option

    let default : t = None

    let compare = Stdlib.compare (* consider a more specific one *)

    let project r lbl =
      Option.bind lbl
        (fun l-> Operations.Local.project_transition r l)
  end

  module FSM = Persistent.Digraph.ConcreteLabeled (State) (Label)

  let get_vertices (fsm : FSM.t) : FSM.V.t list =
    let l = FSM.fold_vertex (fun st l -> st::l) fsm [] in
    assert (List.length l = FSM.nb_vertex fsm) ;
    l

  (* simple merge two state machines *)
  let merge (fsm : FSM.t) (fsm' : FSM.t) : FSM.t =
    (* extend with vertices *)
    let with_vertices = FSM.fold_vertex (fun v g -> FSM.add_vertex g v) fsm' fsm in
    (* extend with edges *)
    let with_edges = FSM.fold_edges_e (fun e g -> FSM.add_edge_e g e) fsm' with_vertices in
    with_edges


  (* let get_transitions_from_state (fsm :FSM.t) (st : State.t) : FSM.E.t list = *)
  (*   FSM.fold_edges_e (fun e l -> if FSM.E.src e = st then e::l else l) fsm [] *)

  let rec print_vertices = function
    | [] -> "[]"
    | s::ss -> State.as_string s ^ "::" ^ print_vertices ss

  (* compose two machines allowing all their interleavings *)
  let parallel_compose (s_st, e_st) (fsm : FSM.t) (fsm' : FSM.t) : FSM.t =
    let generate_state_space (s_st, e_st) fsm fsm' : 'a =
      let sts_fsm = get_vertices fsm in
      let sts_fsm' = get_vertices fsm' in
      "Size of sts_fsm: " ^ string_of_int (List.length sts_fsm) ^ " -- "  ^ (print_vertices sts_fsm) |> Utils.log;
      "Size of sts_fsm': " ^ string_of_int (List.length sts_fsm') ^ " -- "  ^ (print_vertices sts_fsm') |> Utils.log;
      (* new combined_state *)
      let ncs st st' =
        let new_st () =
          let new_st = State.fresh() in
          let new_st' = if State.is_start st && State.is_start st' then State.mark_as_start new_st else new_st in
          if State.is_end st && State.is_end st' then State.mark_as_end new_st' else new_st'
        in
        if st = s_st && st = st'
        then s_st
        else if st = e_st && st = st'
        then e_st else new_st ()
      in
      let state_space = List.fold_left (fun b a  -> List.fold_left (fun b' a' -> ((a, a'), ncs a a')::b') b sts_fsm') [] sts_fsm in
      (* generate state_machine for the combined state *)
      let machine = List.fold_left (fun fsm (_, st) -> FSM.add_vertex fsm st) FSM.empty state_space
      in
      state_space, machine
    in

    let dict, jfsm = generate_state_space (s_st, e_st) fsm fsm' in

    let rec dict_to_string = function
      | [] -> "[]"
      | ((s1, s2), s3)::dict ->
        "(" ^ State.as_string s1 ^ ", " ^  State.as_string s2 ^ "), " ^  State.as_string s3 ^ ")::" ^ dict_to_string dict
    in

    Utils.log @@ dict_to_string dict ;
    "Size of fsm: " ^ string_of_int (FSM.nb_vertex fsm) |> Utils.log;
    "Size of fsm': " ^ string_of_int (FSM.nb_vertex fsm') |> Utils.log;
    "Size of space: " ^ string_of_int (List.length dict) |> Utils.log;

    (* adds an edge many times to the product space *)
    let add_edges from_first e fsm =
      let src_sts = List.filter (fun ((st, st'), _) -> if from_first then st = FSM.E.src e else st' = FSM.E.src e) dict in

      let find_end_state ( (s1, s2), _) e =
        let s = FSM.E.src e in
        let d = FSM.E.dst e in

        if from_first && (s = s1) then
          try
            let _, d_res = List.find (fun ((x0, x1), _) -> x0 = d && x1 = s2) dict in
            d_res
          with
          | _ -> failwith ("this: " ^ dict_to_string dict)

        else if (not from_first) && s = s2 then
          try
            let _, d_res = List.find (fun ((x0, x1), _) -> x1 = d && x0 = s1) dict in
            d_res
          with
          | _ -> failwith ("that: " ^ dict_to_string dict)

        else
          failwith "Violation: e is not related to s1, s2."

      in

      let coords = List.map
          (fun ((_c_s_st, c_e_st), src_st) -> src_st, find_end_state ((_c_s_st, c_e_st), src_st) e)
          src_sts
      in
      List.fold_left (fun fsm' (src, dst) -> FSM.add_edge_e fsm' (FSM.E.create src (FSM.E.label e) dst) ) fsm coords
    in
    let jfsm' = FSM.fold_edges_e (add_edges true) fsm jfsm in
    FSM.fold_edges_e (add_edges false) fsm' jfsm'

  let filter_degenerate_branches branches =
    List.filter (function Seq [] -> false | _ -> true) branches

  let generate_state_machine (g : global) : State.t * FSM.t =
    let start = State.fresh_start () in
    (* tr does the recursive translation.
       s_st and e_st are the states that will bound the translated type
       next is a list of states that lead to the machine we are currently translating
       and the first element of the returned value is the places where the execution will continue
    *)
    let rec tr fsm g (s_st, e_st) next =
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
            [st], FSM.add_vertex FSM.empty st

        in
        connect fsm gis (s_st, e_st) next

      | Choice branches ->
        let branches = filter_degenerate_branches branches in
        if List.length branches = 0 then next, fsm else
          let nexts, fsms = List.map (fun g -> tr fsm g (s_st, e_st) next) branches |> List.split in
          let fsm' = List.fold_left merge fsm fsms in
          List.concat nexts, fsm'

      | Fin g' ->
        let next', fsm' = tr fsm g' (s_st, e_st) next in
        let next'', fsm'' = tr fsm' g' (e_st, e_st) next' in
        next @ next' @ next'' @ [s_st ; e_st], fsm''

      | Inf g' ->
        let _, fsm' = tr fsm g' (s_st, s_st) next in
        [e_st], fsm'

      | Par [] ->
        "EMPTY PAR" |> Utils.log ;
        next, fsm

      | Par branches ->
        let branches = filter_degenerate_branches branches in
        if List.length branches = 0 then next, fsm else
          let m = FSM.add_vertex (FSM.add_vertex FSM.empty s_st) e_st in
          let nexts, fsms = List.map (fun g -> tr m g (s_st, e_st) next) branches |> List.split in
          List.iter (fun fsm -> "branch number of vertices: " ^ (FSM.nb_vertex fsm |> string_of_int) |> Utils.log) fsms;
          let fsm' =
            match fsms with
            | [] -> m
            | [fsm] -> fsm
            | fsm::fsms' ->
              List.fold_left (parallel_compose (s_st, e_st)) fsm fsms'
          in
          List.concat nexts, (merge fsm fsm')
    in
    let end_st = State.fresh_end() in
    let next, fsm_final = tr FSM.empty g (start, end_st) [start] in
    List.iter (fun st -> let _ = State.mark_as_end st in ()) next ;
    (start, fsm_final)

  let _minimise_state_numbers fsm =
    let vertices = get_vertices fsm |> List.mapi (fun n st -> (st, State.renumber_state n st)) in

    let fsm' = List.fold_left (fun fsm (_, st) -> FSM.add_vertex fsm st ) FSM.empty vertices in
    let update e =
      let tr st =
        List.assoc st vertices
      in
      FSM.E.create (FSM.E.src e |> tr) (FSM.E.label e) (FSM.E.dst e |> tr)
    in
    FSM.fold_edges_e (fun e fsm -> FSM.add_edge_e fsm (update e)) fsm fsm'

  module Dot = struct
    module Display = struct
      include FSM

      let vertex_name v =
        string_of_int v.State.id


      let graph_attributes _ = [`Rankdir `LeftToRight]

      let default_vertex_attributes _ = []

      let vertex_attributes = function
        | v when State.is_start v && State.is_end v -> [`Shape `Doublecircle ; `Style `Filled ; `Fillcolor 0x7777FF ; `Label (State.as_string v)]
        | v when State.is_start v -> [`Shape `Circle ; `Style `Filled ; `Fillcolor 0x77FF77 ; `Label (State.as_string v)]
        | v when State.is_end v -> [`Shape `Doublecircle ; `Style `Filled ; `Fillcolor 0xFF7777 ; `Label (State.as_string v)]
        | v -> [`Shape `Circle ; `Label (State.as_string v) ]

      let default_edge_attributes _ = []

      let edge_attributes (e : edge) =
        match FSM.E.label e with
        | None -> [`Label "tau"]
        | Some l -> [`Label (Syntax.string_of_transition_label l)]

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

  let generate_dot fsm = fsm |> _minimise_state_numbers |> Dot.generate_dot

end


module Local = struct

  module Label = struct
    type t = Syntax.Local.local_transition_label option

    let default : t = None

    let compare = Stdlib.compare (* consider a more specific one *)
  end

  module FSM = Persistent.Digraph.ConcreteLabeled (State) ( Label)
  let project (r : Syntax.role) (fsm : Global.FSM.t) : FSM.t =
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
    with_edges

  (* TODO make this modular and not copy pasted *)
  module Dot = struct
    module Display = struct
      include FSM

      let vertex_name v =
        string_of_int v.State.id


      let graph_attributes _ = [`Rankdir `LeftToRight]

      let default_vertex_attributes _ = []

      let vertex_attributes = function
        | v when State.is_start v && State.is_end v -> [`Shape `Doublecircle ; `Style `Filled ; `Fillcolor 0x7777FF ; `Label (State.as_string v)]
        | v when State.is_start v -> [`Shape `Circle ; `Style `Filled ; `Fillcolor 0x77FF77 ; `Label (State.as_string v)]
        | v when State.is_end v -> [`Shape `Doublecircle ; `Style `Filled ; `Fillcolor 0xFF7777 ; `Label (State.as_string v)]
        | v -> [`Shape `Circle ; `Label (State.as_string v) ]

      let default_edge_attributes _ = []

      let edge_attributes (e : edge) =
        match FSM.E.label e with
        | None -> [`Label "tau"]
        | Some l -> [`Label (Syntax.Local.string_of_local_transition_label l)]

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

  let generate_dot fsm = fsm (* |> _minimise_state_numbers *) |> Dot.generate_dot
end
