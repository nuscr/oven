module Composition (FSM : Machine.FSM) =
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
  type dict = ((FSM.vertex * FSM.vertex) * FSM.vertex) list (* ((s1, s2), s3) state s1 and s2 became s3 *)

  (* generate product state space *)
  let generate_state_space fsm fsm' =
    let sts_fsm = FSM.get_vertices fsm in
    let sts_fsm' = FSM.get_vertices fsm' in
    (* new combined_state *)
    let ncs st st' =
      let new_st () =
        let new_st = FSM.State.fresh() in
        let new_st' = if FSM.State.is_start st && FSM.State.is_start st' then FSM.State.mark_as_start new_st else new_st in
        if FSM.State.is_end st && FSM.State.is_end st' then FSM.State.mark_as_end new_st' else new_st'
      in
      if  st = st' then st else
        new_st ()
    in
    let state_space = List.fold_left (fun b a  -> List.fold_left (fun b' a' -> ((a, a'), ncs a a')::b') b sts_fsm') [] sts_fsm in
    (* generate state_machine for the combined state *)
    let machine = List.fold_left (fun fsm (_, st) -> FSM.add_vertex fsm st) FSM.empty state_space
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
    FSM.E.create (FSM.E.src e |> coord) (FSM.E.label e) (FSM.E.dst e |> coord)

  let walker (fsm : FSM.t) (fsm' : FSM.t) (initial_st : FSM.vertex * FSM.vertex)
      (walk_fun : dict -> FSM.vertex * FSM.vertex -> ((FSM.edge * (FSM.vertex * FSM.vertex))) list)
    : dict * (FSM.vertex list * FSM.t) =
    let dict, jfsm = generate_state_space fsm fsm' in
    let rec walk
        (sts : FSM.vertex * FSM.vertex)
        (visited : FSM.vertex list)
        (jfsm : FSM.t)
        (k : FSM.vertex list -> FSM.t -> 'a) : 'a  =
      let curr_st = find_state_in_dest sts dict in
      if List.mem curr_st visited
      then k visited jfsm
      else
        let jes = walk_fun dict sts in
        add_edges jes (curr_st::visited) jfsm k

    and add_edges
        (pending : (FSM.edge * (FSM.vertex * FSM.vertex)) list)
        (visited : FSM.vertex list)
        (jfsm : FSM.t)
        (k : FSM.vertex list -> FSM.t -> 'a) : ' a =
      match pending with
      | (je, next_sts)::jes ->
        let jfsm = FSM.add_edge_e jfsm je in
        walk next_sts visited jfsm
          (fun visited jfsm -> add_edges jes visited jfsm k)

      | [] -> k visited jfsm

    in
    walk initial_st [] jfsm (fun _visited fsm -> dict, (FSM.get_final_states fsm, fsm))


  (* compose two machines with a function *)
  let compose_with
      (sts : FSM.vertex * FSM.vertex)
      (fsm : FSM.t)
      (fsm' : FSM.t)
      (* from the dict and the current state, produce a list of edges and the one next state per edge *)
      (f : dict -> FSM.vertex * FSM.vertex -> (FSM.edge * (FSM.vertex * FSM.vertex)) list)
    :  FSM.vertex * (FSM.vertex list * FSM.t) =

    let dict, next_jfsm = walker fsm fsm' sts f in
    find_state_in_dest sts dict, next_jfsm

  (* compose two machines allowing all their interleavings *)
  let parallel_compose
      (sts : FSM.vertex * FSM.vertex)
      (fsm : FSM.t)
      (fsm' : FSM.t) :  FSM.vertex * (FSM.vertex list * FSM.t) =
    compose_with sts fsm fsm'
      (fun dict (st, st' as sts) ->
         let l_es = FSM.succ_e fsm st in
         let r_es = FSM.succ_e fsm' st' in

         let f side es =
           List.map
             (fun e ->
                translate_edge_to_joint_fsm sts side dict e,
                build_joint_state sts side (FSM.E.dst e))
             es
         in
         f L l_es @ f R r_es)

  (* compose two machines allowing only their common labels *)
  let intersection_compose
      (sts : FSM.vertex * FSM.vertex)
      (fsm : FSM.t)
      (fsm' : FSM.t) :  FSM.vertex * (FSM.vertex list * FSM.t) =
    compose_with sts fsm fsm'
      (fun dict (st, st') ->
         let l_es = FSM.succ_e fsm st in
         let r_es = FSM.succ_e fsm' st' in

         let l_es' = List.filter (fun e -> List.mem (FSM.E.label e) (List.map FSM.E.label r_es)) l_es in

         let f side es =
           List.map
             (fun e ->
                translate_edge_to_joint_fsm sts side dict e,
                build_joint_state sts side (FSM.E.dst e))
             es
         in
         f L l_es')

  (* compose two machines joining their common labels, and allowing free interleavings of the rest *)
  let join_compose
      (sts : FSM.vertex * FSM.vertex)
      (fsm : FSM.t)
      (fsm' : FSM.t) :  FSM.vertex * (FSM.vertex list * FSM.t) =
    let get_size_as_str fsm = FSM.get_vertices fsm |> List.length |> string_of_int in
    "FSM size = " ^ get_size_as_str fsm |> Utils.log ;
    "FSM' size = " ^ get_size_as_str fsm' |> Utils.log ;
    compose_with sts fsm fsm'
      (fun dict (st, st' as sts) ->
         let l_es = FSM.succ_e fsm st in
         let r_es = FSM.succ_e fsm' st' in

         (* if the transition is enabled in both, then it's ok *)
         let l_both = List.filter (fun e -> List.mem (FSM.E.label e) (List.map FSM.E.label r_es)) l_es in

         let left_labels = FSM.get_reachable_labels fsm st in
         let right_labels = FSM.get_reachable_labels fsm' st' in

         (* edges on the left, that are never on the right *)
         let l_es' = List.filter (fun e -> List.mem (FSM.E.label e) right_labels |> not)  l_es in
         (* edges on the right, that are never on the left *)
         let r_es' = List.filter (fun e -> List.mem (FSM.E.label e) left_labels |> not)  r_es in

         let get_edge_with_label es l =
           List.find (fun e -> FSM.E.label e = l) es
         in

         let f_both es =
           let lbls = List.map FSM.E.label es in

           List.map (fun l ->
               let jsrc = List.assoc (st, st') dict in

               let dst = get_edge_with_label l_es l |> FSM.E.dst in
               let dst' = get_edge_with_label r_es l |> FSM.E.dst in

               let jdst = List.assoc (dst, dst') dict in

               FSM.E.create jsrc l jdst, (dst, dst')
             )
             lbls
         in
         let f_sided side es =
           List.map
             (fun e ->
                translate_edge_to_joint_fsm sts side dict e,
                build_joint_state sts side (FSM.E.dst e))
             es
         in

         f_both l_both @ f_sided L l_es' @ f_sided R r_es'
      )


  type priority_source
    = FirstMachine
    | SecondMachine
    | NoMachine

  let rec prioritise
      (initial_fsm : FSM.t)
      (fsm : FSM.t) (s_st : FSM.vertex)
      (fsm1 : FSM.t) (s1_st : FSM.vertex)
      (fsm2 : FSM.t) (s2_st : FSM.vertex)
    : FSM.vertex list * FSM.t =
    let edges_with_labels_in es lbls =
      List.filter (fun e -> List.mem (FSM.E.label e) lbls) es
    in
    let rec pr i s s1 s2 visited =
      if List.mem s visited then i
      else
        (* all the edges to rank *)
        let es =
          try FSM.succ_e fsm s with
            e -> raise (Error.Violation ("Unexpected, succ_e failed with: " ^ Printexc.to_string e))
        in
        (* labels available in f1 and f2 *)
        let f1_lbls = FSM.succ_e fsm1 s1 |> List.map FSM.E.label in
        let f2_lbls = FSM.succ_e fsm2 s2 |> List.map FSM.E.label in
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
          FSM.succ_e m st |> List.find (fun e -> FSM.E.label e = lbl)
        with
          Not_found -> Error.Violation "Unexpected: the label must be in the list." |> raise
      in
      match es, m with
      | [], _ -> i

      | e::es, FirstMachine ->
        let s1' = find_edge_with_label fsm1 s1 (FSM.E.label e) |> FSM.E.dst in
        let i = pr (FSM.add_edge_e i e) (FSM.E.dst e) s1' s2 visited in
        prs i m es s1' s2 visited

      | e::es, SecondMachine ->
        let s2' = find_edge_with_label fsm2 s2 (FSM.E.label e) |> FSM.E.dst in
        let i = pr (FSM.add_edge_e i e) (FSM.E.dst e) s1 s2' visited in
        prs i m es s1 s2' visited

      | e::es, NoMachine ->
        let i = pr (FSM.add_edge_e i e) (FSM.E.dst e) s1 s2 visited in
        prs i m es s1 s2 visited
    in
    let res = pr initial_fsm s_st s1_st s2_st [] in
    FSM.get_final_states res, res

  let only_reachable_from st fsm =
    let add_state_and_successors n_fsm st =
      let next_sts = FSM.succ fsm st in
      let next_edges = FSM.succ_e fsm st in

      let n_fsm' = List.fold_left (fun fsm st -> FSM.add_vertex fsm st ) (FSM.add_vertex n_fsm st) next_sts in
      List.fold_left (fun fsm e -> FSM.add_edge_e fsm e) n_fsm' next_edges
    in

    let rec f n_fsm visited to_visit =
      match to_visit with
      | [] -> n_fsm
      |  st::remaining ->
        (* states reachable from st *)
        let reachable = FSM.succ fsm st in
        let n_fsm' = add_state_and_successors n_fsm st in

        let visited' = st::visited in
        let to_visit' = Utils.minus (reachable @ remaining) visited' in
        f n_fsm' visited' to_visit'
    in

    if Debug.keep_only_reacheable_off None
    then fsm
    else f FSM.empty [] [st]
end
