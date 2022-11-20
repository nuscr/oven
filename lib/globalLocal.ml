open Syntax

open Machine

let _debug =
  (* let _ = Debug.set_all_debug_flags() in *)
  (* let _ = Debug.keep_only_reacheable_off (Some true) in *)
  (* let _ = Debug.project_to_empty (Some true) in *)
  (* let _ = Debug.post_process_taus_off (Some false) in *)
  (* let _ = Debug.minimise_off (Some true) in *)
  (* let _ = Debug.minimise_state_numbers_off (Some true) in *)
  ()

module State = struct
  type t = { id : int
           ; mutable is_start : bool
           ; mutable is_end : bool
           }

  let equal s1 s2 = (s1.id = s2.id)

  let hash = Hashtbl.hash

  let compare s1 s2 = compare s1.id s2.id

  let mark_as_start s =
    s.is_start <- true ; s

  let mark_as_end s =
    s.is_end <- true ; s

  let as_string {id ; is_start ; is_end} =
    let s_str = if is_start then "S" else "" in
    let e_str = if is_end then "E" else "" in
    let extra = if is_start || is_end then s_str ^ e_str ^ "-" else "" in
    extra ^ (string_of_int id)

  let rec list_as_string = function
    | [] -> "[]"
    | s::ss -> as_string s ^ "::" ^ list_as_string ss

  (* let mark_as_not_end s = *)
  (*   s.is_end := false ; s *)

  let is_start s = s.is_start
  let is_end s = s.is_end

  let fresh, fresh_start, fresh_end, freshen =
    let n = ref 0 in
    ((fun () -> incr n ; {id = !n ; is_start = false ; is_end = false}),
     (fun () -> incr n ; {id = !n ; is_start = true ; is_end = false}),
     (fun () -> incr n ; {id = !n ; is_start = false ; is_end = true}),
     (fun st -> incr n ; {id = !n ; is_start = (is_start st) ; is_end = (is_end st)}))

  let renumber_state n {id = _ ; is_start ; is_end} = {id = n ; is_start ; is_end}

  let get_id {id ; _ } = id

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

    let list_as_string l =
      List.map as_string l |> String.concat ", "

    let is_default = function
      | None -> true
      | Some _ -> false
  end

  module FSM = StateMachine (State) (Label)

  module FSMComp = Composition.Composition (FSM)

  let _filter_degenerate_branches branches =
    List.filter (function Seq [] -> false | _ -> true) branches

  let split_prev fsm prev : FSM.vertex * FSM.t =
    let st = State.fresh() in
    st, List.fold_left (fun fsm st' -> FSM.add_edge fsm st st') fsm prev

  (* let join_next fsm next : FSM.vertex * FSM.t = *)
  (*   let st = State.fresh() in *)
  (*   st, List.fold_left (fun fsm st' -> FSM.add_edge fsm st' st) fsm next *)

  let generate_state_machine' (g : global) : FSM.vertex * FSM.t =
    let connect (s_st, e_sts, fsm) afsm'
      : FSM.vertex * FSM.vertex list * FSM.t=
      let freshen (s_st, e_sts, f) =
        let f', dict = FSM.freshen_with_dict f in
        List.assoc s_st dict, List.map (fun st -> List.assoc st dict) e_sts, f'
      in

      (* freshen afsm' and add to fsm connecting e_st to the start of afsm *)
      let plug e_st fsm =
        let s_st', e_sts', fsm' = freshen afsm' in
        let fsm = FSM.merge fsm fsm' in
        e_sts', FSM.add_edge fsm e_st s_st'
      in

      let e_sts, fsm =
        List.fold_left
          (fun (e_sts, fsm) e_st -> let e_sts', fsm = plug e_st fsm in e_sts @ e_sts', fsm)
          ([], fsm) e_sts
      in

      s_st, e_sts, fsm
    in

    (* tr does the recursive translation.
       s_st and e_st are the states that will bound the translated type
       next is a list of states that lead to the machine we are currently translating
       and the first element of the returned value is the places where the execution will continue
    *)
    let rec tr
        (g : global)
        (* return the first vertex, the vertices to connect at the
           end, and the state machine *)
      : FSM.vertex * FSM.vertex list * FSM.t =
      let start_to_end_fsm () =
        let s_st = State.fresh() in
        let e_st = State.fresh() in
        s_st, [e_st], FSM.add_edge FSM.empty s_st e_st
      in
      (* this one should not return *)
      (* let module SEC = Bisimulation.StateEquivalenceClasses (FSM) in *)
      match g with
      | MessageTransfer lbl ->
        let s_st = State.fresh() in
        let e_st = State.fresh() in
        let fsm = FSM.add_vertex (FSM.add_vertex FSM.empty e_st) s_st in
        s_st, [e_st], FSM.add_edge_e fsm (FSM.E.create s_st (Some lbl) e_st)

      | Seq gis ->
        let afsms = List.map tr gis in
        List.fold_left (fun afsm afsm' -> connect afsm afsm') (start_to_end_fsm ())  afsms

      | Choice branches ->
        if Utils.is_empty branches then start_to_end_fsm () else
          let s_sts, e_sts, fsms = List.map tr branches |> Utils.split_3 in
          let fsm = FSM.merge_all fsms in

          let s_st, fsm = split_prev fsm s_sts in
          s_st, List.concat e_sts, fsm

      | Fin _g' -> assert false
        (* let s_st, loop_st, fsm = tr fsm g' in *)
        (* let loop_st', end_loop_st, fsm = tr fsm g' in *)
        (* (\* close the loops with loop_st -> loop_st' and end_loop_st -> loop_st *\) *)
        (* let fsm = FSM.add_edge (FSM.add_edge fsm loop_st loop_st') end_loop_st loop_st' in *)
        (* (\* add the links to end s_st -> e_st and loop_st' -> e_st *\) *)
        (* let e_st = State.fresh () in *)
        (* let fsm = FSM.add_edge (FSM.add_edge fsm s_st e_st) loop_st' e_st in *)
        (* s_st, e_st, fsm *)

      | Inf _g' -> assert false
        (* let s_st, loop_st, fsm = tr fsm g' in *)

        (* let start_loop_st, end_loop_st, fsm = tr fsm g' in *)

        (* let fsm = FSM.add_edge (FSM.add_edge fsm loop_st start_loop_st) end_loop_st loop_st in *)
        (* (\* the end state is fresh and unconnected because it's an infinite loop *\) *)
        (* s_st, State.fresh(), fsm *)

      | Par [] ->
        "EMPTY PAR" |> Utils.log ;
        start_to_end_fsm ()

      (* | Par branches -> *)
      (*   let branches = filter_degenerate_branches branches in *)
      (*   if List.length branches = 0 then start_to_end_fsm () else *)
      (*     let st, fsm = gather_next fsm next in *)
      (*     combine_branches fsm next st branches FSMComp.parallel_compose *)

      (* | Join branches -> *)
      (*   let branches = filter_degenerate_branches branches in *)
      (*   if List.length branches = 0 then start_to_end_fsm () else *)
      (*     let st, fsm = gather_next fsm next in *)
      (*     combine_branches fsm next st branches FSMComp.join_compose *)

      (* | Intersection branches -> *)
      (*   let branches = filter_degenerate_branches branches in *)
      (*   if List.length branches = 0 then start_to_end_fsm () else *)
      (*     let st, fsm = gather_next fsm next in *)
      (*     combine_branches fsm next st branches FSMComp.intersection_compose *)

      (* | Prioritise (g, g1, g2) -> *)
      (*   let s_st, initial_fsm = gather_next fsm next in *)
      (*   let _, fsm = tr initial_fsm g [s_st] in *)

      (*   let s1_st = State.fresh () in *)
      (*   let _, fsm1 = tr FSM.empty g1 [s1_st] in *)
      (*   let fsm1 = SEC.make_tau_ends_equivalent fsm1 in *)

      (*   let s2_st = State.fresh () in *)
      (*   let _, fsm2 = tr FSM.empty g2 [s2_st] in *)
      (*   let fsm2 = SEC.make_tau_ends_equivalent fsm2 in *)

      (*   FSMComp.prioritise initial_fsm (FSM.add_vertex fsm s_st) s_st fsm1 s1_st fsm2 s2_st *)

      | _ -> assert false

    (* and combine_branches fsm next s_st branches *)
    (*     (combine_fun : *)
    (*        FSM.vertex * FSM.vertex -> *)
    (*      FSM.t -> FSM.t -> *)
    (*      FSM.vertex * (FSM.vertex list * FSM.t)) = *)
    (*   let m () = *)
    (*     FSM.add_vertex FSM.empty s_st *)
    (*   in *)
    (*   let st_next_fsms = List.map (fun g -> s_st, tr (m ()) g [s_st]) branches in *)
    (*   let (merged_next : FSM.vertex list), (fsm' : FSM.t) = *)
    (*     match st_next_fsms with *)
    (*     | [] -> ([s_st], m ()) *)
    (*     | [next_fsm] -> next_fsm |> snd *)
    (*     | s_st_next_fsm::next_fsms' -> *)
    (*       (List.fold_left *)
    (*          (fun (s_st, (_, fsm)) (s_st', (_, fsm')) -> *)
    (*             combine_fun (s_st, s_st') fsm fsm') *)
    (*          s_st_next_fsm *)
    (*          next_fsms') |> snd *)
    (*   in *)
    (*   let resfsm = FSM.merge fsm fsm' in *)
    (*   let next = if Utils.is_empty merged_next then next else merged_next in *)
    (*   next, resfsm *)
    in
    let s_st, e_sts, fsm_final = tr g in
    let s_st = State.mark_as_start s_st in
    let _ = List.map State.mark_as_end e_sts  in
    s_st, fsm_final |> FSMComp.only_reachable_from s_st

  module B = Bisimulation.Bisimulation (FSM) (Bisimulation.Weak)
  let minimise fsm = B.minimise fsm

  let generate_state_machine (g : global) : FSM.vertex * FSM.t =

    let st, fsm = generate_state_machine' g in
    let st, fsm = if Debug.simplify_machine_off None
      then st, fsm
      else (* st, fsm |> minimise *) (* TODO: WEIRD!!!! if we do only minimise it breaks machies appart *)
        let module SEC = Bisimulation.StateEquivalenceClasses (FSM) in
        let fsm, dict = SEC.make_tau_ends_equivalent_with_dict fsm in
        List.assoc st dict, fsm |> minimise |> FSM.remove_reflexive_taus |> FSM.minimise_state_numbers
    in
    st, fsm

  (* TODO do we need this?, maybe just not reexport it *)
  let generate_dot fsm = fsm |> FSM.Dot.generate_dot

  let generate_minimal_dot fsm =
    let module WB =  Bisimulation.Bisimulation (FSM) (Bisimulation.Weak) in
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


    let list_as_string l =
      List.map as_string l |> String.concat ", "

    let is_default = function
      | None -> true
      | Some _ -> false
  end

  module FSM = StateMachine (State) (Label)

  let project (r : Syntax.role) (fsm : Global.FSM.t) : FSM.t =
    if Debug.project_to_empty None then FSM.empty
    else begin
      (* add the \tau transitions induced by L-Rev *)
      let complete fsm : FSM.t =
        let tau_edges = FSM.fold_edges_e (fun e l -> if FSM.E.label e |> Option.is_none then e::l else l) fsm []  in

        let reverse_edge e =
          FSM.E.create (FSM.E.dst e) (FSM.E.label e) (FSM.E.src e)
        in

        let new_tau_edges = List.filter_map (fun e -> if FSM.state_can_step fsm (FSM.E.dst e) then Some (reverse_edge e) else None) tau_edges in

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
    end

  type wb_res = (unit, string) Result.t

  module WB =  Bisimulation.Bisimulation (FSM) (Bisimulation.Weak)

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

  let rec wb r (st, fsm : FSM.vertex * FSM.t) : wb_res =
    let (let*) = special_bind in
    let _blocks = WB.compute_bisimulation_quotient fsm in
    let* _res = _c1 r (st, fsm) in
    let* _res = _c2 r _blocks (st, fsm) in
    let* _res = _c3 r _blocks (st, fsm) in
    let* _res = _c4 r _blocks (st, fsm) in
    _res |> Result.ok

  and _c1 r (st, fsm) : wb_res =
    if FSM.has_strong_outgoing_transitions fsm st then
      if State.is_end st then
        "For role: " ^ r ^ " state: " ^ State.as_string st ^ " may terminate or continue (C1 violation)." |> Result.error
      else
        Result.ok ()
    else Result.ok ()

  and _c2 r blocks (st, fsm) : wb_res =
    let by_tau = FSM.tau_reachable fsm st in
    if List.for_all (fun st' -> WB.are_states_bisimilar blocks st st') by_tau
    then Result.ok ()
    else
      try
        let st' = List.find (fun st' -> WB.are_states_bisimilar blocks st st' |> not) by_tau in
        "For role: " ^ r ^ " states: " ^ State.as_string st ^ " and " ^ State.as_string st' ^ " are not bisimilar (C2 violation)." |> Result.error
      with
        _ -> Error.Violation "This is a bug. There must be a non bisimilar state."  |> raise

  and _c3 r blocks (st, fsm) : wb_res =
    let is_send = function
      | Some l -> l.Syntax.Local.direction = Syntax.Local.Sending
      | None -> false
    in
    let by_tau = FSM.tau_reachable fsm st in

    (* send labels and their states *)
    let _sends =
      List.concat_map
        (fun st' -> List.filter_map
            (fun e -> if FSM.E.label e |> is_send then Some (FSM.E.label e, FSM.E.dst e) else None)
            (FSM.succ_e fsm st'))
        by_tau
    in

    (* makes the original state step with the labelled transition *)
    let one_step (l : Label.t) st_error =
      try
        List.find (fun e -> l = FSM.E.label e) (FSM.succ_e fsm st) |> FSM.E.dst |> Result.ok
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
    let by_tau = st::FSM.tau_reachable fsm st in
    let weak_reductions =
      List.concat_map
        (fun st' -> FSM.succ_e fsm st' |> List.filter (fun e -> FSM.E.label e |> Option.is_some))
        by_tau
    in
    let rec f = function
      | [] -> Result.ok ()
      | e::es ->
        (* split in the edges with a different label, and the states that the same label transitions to *)
        let es_diff, st_same =
          List.fold_left
            (fun (d, s) e' ->
               if FSM.E.label e = FSM.E.label e'
               then
                 let t_r = FSM.tau_reachable fsm (FSM.E.dst e) in
                 let t_r' = FSM.tau_reachable fsm (FSM.E.dst e') in
                 (d, (FSM.E.dst e)::(FSM.E.dst e')::t_r @ t_r' @ s)
               else (if FSM.E.label e' |> is_receive then  e'::d,s else d, s))
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
                ^ " after taking label: " ^ Label.as_string (FSM.E.label e)
                ^ " (C4 violation)."
                |> Result.error
            in
            List.fold_left (fun r s' -> Result.bind r (fun _ -> check s s')) (Result.ok ()) ss
        in
        Result.bind are_bisim (fun _ -> f es_diff)
    in
    f (weak_reductions |> List.filter (fun e -> FSM.E.label e |> is_receive))

  and c5 r fsm visited to_visit : wb_res =
    match to_visit with
    | [] -> Result.ok ()
    | st::_ when List.mem st visited -> Result.ok ()
    | st::sts ->
      begin match wb r (st, fsm) with
        | Result.Ok () ->
          let to_visit' = Utils.minus ((FSM.succ fsm st) @ sts) visited in
          c5 r fsm (st::visited) to_visit'
        | Result.Error err -> Result.error err
      end

  let well_behaved_role (r, st, fsm : role  * FSM.vertex * FSM.t) : wb_res =
    c5 r fsm [] [st]

  let well_behaved_local_machines roles_and_lfsms : wb_res =
    let lfsms = List.map (fun (r, l) -> r, FSM.get_start_state l, l) roles_and_lfsms in
    pipe_fold well_behaved_role (Result.ok ()) lfsms

  (* TODO: do we need to reexport this? *)
  let generate_dot fsm = fsm |> FSM.Dot.generate_dot

  let generate_minimal_dot fsm =
    let module WB = Bisimulation.Bisimulation (FSM) (Bisimulation.Weak) in
    WB.generate_minimal_dot fsm

  let generate_local_for_roles roles gfsm =
    let local_machine r =
      r, project r gfsm |> FSM.minimise_state_numbers
    in

    List.map local_machine roles
end
