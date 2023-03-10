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

  type lts = (global * transition_label * global) list

  let _filter_degenerate_branches branches =
    List.filter (function Seq [] -> false | _ -> true) branches

  let generate_state_machine' (g : global) :  FSM.t =
    let rec may_terminate = function
      | MessageTransfer _ -> false
      | Par gs
      | Seq gs -> List.for_all may_terminate gs (* done is Sec [], for which it's trivially true *)
      | OutOfOrder (g1, g2) -> may_terminate g1 && may_terminate g2
      | Choice gs -> List.exists may_terminate gs
      | Fin _ -> true
      | Inf _ -> false
      | Intersection (g1, g2) ->
        get_lts_head (Intersection (g1, g2)) |> Utils.is_empty

      | Join (g1, g2) ->
        get_lts_head (Join (g1, g2)) |> Utils.is_empty


      | Prioritise (g, lbl1, lbl2) ->
        get_lts_head (Prioritise (g, lbl1, lbl2)) |> Utils.is_empty

      | Rec (x, g) ->
        may_terminate (unfold (Rec (x, g)) x g)

      | Var _ -> false

    and get_lts_head
        (g : global)
      : (transition_label * global) list =
      let done_g = Seq [] in (* a terminated global type *)

      let intersection_like f g1 g2 =
        let ltshd1 = get_lts_head g1 in
        let ltshd2 = get_lts_head g2 in

        Utils.cartesian ltshd1 ltshd2
        |> List.filter (fun ((l, _), (l', _)) -> l = l')
        |> List.map (fun ((l, g1'), (_, g2')) ->  (l, f g1' g2'))

      in
      match g with
      | MessageTransfer lbl -> [(lbl, done_g)]

      | Seq [] -> []
      | Seq [g] -> get_lts_head g
      | Seq (g::gs) ->
        let head = List.map (fun (l, g') -> l, Seq (g':: gs)) (get_lts_head g) in
        let tail =  if may_terminate g then
            get_lts_head (Seq gs)
          else
            [] in
        head @ tail

      | OutOfOrder (g1, g2) ->
        let g1_roles = get_lts g1 [] |> List.map (fun (_, lbl, _) -> [lbl.sender ; lbl.receiver]) |> List.concat |> Utils.uniq in

        let l1 = get_lts_head g1 |> List.map (fun (l, g') -> (l, OutOfOrder(g', g2))) in
        let l2 = get_lts_head g2
                 |> List.filter (fun (l, _) -> (List.mem l.sender g1_roles |> not) && (List.mem l.receiver g1_roles |> not))
                 |> List.map (fun (l, g') -> (l, OutOfOrder(g1, g'))) in

        l1 @ l2

      | Choice gs ->
        List.map get_lts_head gs |> List.concat

      | Fin g' ->
        List.map (fun (l, g'') -> l, Seq [g'' ; Fin g']) (get_lts_head g')


      | Inf g' ->
        List.map (fun (l, g'') -> l, Seq [g'' ; Inf g']) (get_lts_head g')

      | Par gs ->
        let rec build_par gs gs' =
          match gs' with
          | [] -> []
          | g'::gs' ->
            let head = List.map (fun (l, g') -> l, Par (gs @ g':: gs')) (get_lts_head g') in
            let tail =  build_par (gs @ [g']) gs'  in
            head @ tail
        in
        build_par [] gs

      | Intersection (g1, g2) ->
        intersection_like (fun x y -> Intersection (x, y)) g1 g2

      | Join (g1, g2) ->

        let lbls_in_g1 = get_lts g1 [] |> List.map (fun (_, l, _) -> l) |> Utils.uniq in
        let lbls_in_g2 = get_lts g2 [] |> List.map (fun (_, l, _) -> l) |> Utils.uniq in


        let l1 = get_lts_head g1 |> List.filter (fun (l, _) -> List.mem l lbls_in_g2 |> not)
                 |>List.map (fun (l', g1') -> (l', Join (g1', g2)))
        in

        let l2 = get_lts_head g2 |> List.filter (fun (l, _) -> List.mem l lbls_in_g1 |> not)
                 |>List.map (fun (l', g2') -> (l', Join (g1, g2')))
        in
        let l3 = intersection_like (fun x y -> Join (x,y)) g1 g2 in

        l1 @ l2 @ l3

      | Prioritise (g, lbl1, lbl2) ->
        let ltshd = get_lts_head g in

        let ltshd_filtered =
          if List.mem lbl1 (List.map fst ltshd)
          then List.filter (fun (l, _) -> l = lbl2 |> not) ltshd
          else ltshd
        in

        ltshd_filtered |> List.map (fun (l, g') -> (l, Prioritise (g', lbl1, lbl2)))

      | Rec (x, g') ->
        get_lts_head (unfold (Rec (x, g')) x  g')

      | Var _
        -> failwith "unexpected!!! VIOLATION"

    and get_lts (g : global) (visited : global list) : lts =
      if List.mem g visited then []
      else
        let lts_hd = get_lts_head g in
        List.map (fun (l, g') -> (g, l, g')::get_lts g' (g::visited)) lts_hd |> List.concat
    in


    let fsm_of_lts (lts : lts) : FSM.t =
      let rec collect_gs lts acc =
        let add g acc = if List.mem g acc then acc else g::acc in
        match lts with
        | [] -> acc
        | (g, _, g')::lts' ->
          collect_gs lts' (add g (add g' acc))
      in

      let dict = collect_gs lts [] |> List.map (fun g -> g, State.fresh ()) in
      let lu g = List.assoc g dict in
      let fsm = List.fold_left (fun fsm (_, st) -> FSM.add_vertex fsm st) FSM.empty dict in

      match lts with
      | [] ->
        let st = FSM.State.fresh () |> FSM.State.mark_as_start |> FSM.State.mark_as_end in
        FSM.add_vertex FSM.empty st
      | (g0, _label, _g1)::_ ->
        let _start = lu g0 |> FSM.State.mark_as_start in

        let add_transition fsm (g, lbl, g') =
          let s_st, e_st = lu g, lu g' in
          let _ = if may_terminate g' then let _ = FSM.State.mark_as_end e_st in () in
          FSM.add_edge_e fsm (FSM.E.create s_st (Some lbl) e_st)
        in
        List.fold_left add_transition  fsm lts
    in

    let tr (g : global) : FSM.t =
      get_lts g [] |> fsm_of_lts
    in

    let final_fsm = tr g in
    final_fsm |> FSMComp.only_reachable_from (FSM.get_start_state final_fsm)

  module B = Bisimulation.Bisimulation (FSM) (Bisimulation.Strong)
  let minimise fsm = B.minimise fsm

  let generate_state_machine (g : global) : State.t * FSM.t =
    "generate_state_machine enter" |> Utils.log ;
    let fsm = generate_state_machine' g in
    let fsm = if Debug.simplify_machine_off None
      then fsm
      else
        let module SEC = Bisimulation.StateEquivalenceClasses (FSM) in
        let fsm, _ = SEC.make_tau_ends_equivalent_with_dict fsm in
        B.minimise fsm |> FSM.remove_reflexive_taus |> FSM.minimise_state_numbers
    in
    "generate_state_machine exit" |> Utils.log ;
    FSM.get_start_state fsm, fsm

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


  let c1 r blocks (st, fsm) : wb_res =
    let by_tau = FSM.tau_reachable fsm st in
    if List.for_all (fun st' -> WB.are_states_bisimilar blocks st st') by_tau
    then Result.ok ()
    else
      try
        let st' = List.find (fun st' -> WB.are_states_bisimilar blocks st st' |> not) by_tau in
        "For role: " ^ r ^ " states: " ^ State.as_string st ^ " and " ^ State.as_string st' ^ " are not bisimilar (C1 violation)." |> Result.error
      with
        _ -> Error.Violation "This is a bug. There must be a non bisimilar state."  |> raise

  and c2 r blocks (st, fsm) : wb_res =
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
        ^ " (C2 Violation)."
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
        ^ " (C2 violation)."
        |> Result.error
    in

    List.fold_left (fun r (l, st') -> Result.bind r (fun _ -> check st l st')) (Result.ok ()) _sends

  let c3 r blocks (st, fsm) : wb_res =
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
                ^ " (C3 violation)."
                |> Result.error
            in
            List.fold_left (fun r s' -> Result.bind r (fun _ -> check s s')) (Result.ok ()) ss
        in
        Result.bind are_bisim (fun _ -> f es_diff)
    in
    f (weak_reductions |> List.filter (fun e -> FSM.E.label e |> is_receive))

  let c4 r (st, fsm) : wb_res =
    if FSM.has_strong_outgoing_transitions fsm st then
      if State.is_end st then
        "For role: " ^ r ^ " state: " ^ State.as_string st ^ " may terminate or continue (C4 violation)." |> Result.error
      else
        Result.ok ()
    else Result.ok ()

  let wb r (st, fsm : FSM.vertex * FSM.t) : wb_res =
    let (let*) = special_bind in
    let blocks = WB.compute_bisimulation_quotient fsm in
    let* _ = c1 r blocks (st, fsm) in
    let* _ = c2 r blocks (st, fsm) in
    let* _ = c3 r blocks (st, fsm) in
    let* res = c4 r (st, fsm) in
    res |> Result.ok


  let rec c5 r fsm visited to_visit : wb_res =
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
    Utils.log "well_behaved_local_machines start" ;
    let lfsms = List.map (fun (r, l) -> r, FSM.get_start_state l, l) roles_and_lfsms in
    let res = pipe_fold well_behaved_role (Result.ok ()) lfsms in
    Utils.log "well_behaved_local_machines end" ;
    res

  let generate_minimal_dot fsm =
    let module WB = Bisimulation.Bisimulation (FSM) (Bisimulation.Weak) in
    WB.generate_minimal_dot fsm

  (* if an two state have only outgoing taus to eachother, merge them!
     faster for mostly inactive roles *)
  let remove_mutally_taud_states (fsm : FSM.t) : FSM.t =
    "remove_mutally_taud_states start" |> Utils.log ;

    let vs = FSM.get_vertices fsm in
    let only_outgoing_taus st =
      FSM.succ_e fsm st |> List.for_all (fun e -> FSM.Label.is_default (FSM.E.label e))
      && (FSM.State.is_end st |> not)
    in
    let vs_out_taus_only = List.filter only_outgoing_taus vs in

    let rec points_to_merge visited st =
      if List.mem st visited then []
      else
        let vs = FSM.succ_e fsm st
                 |> List.map FSM.E.dst
                 |> List.filter (fun st -> List.mem st vs_out_taus_only)
        in
        st::(List.map (fun st' -> points_to_merge (st::visited) st') vs |> List.concat)
    in

    let rec build_ec vs acc =
      match vs with
      | [] -> acc

      | v'::vs' ->
        let eql = points_to_merge [] v' in
        let vs' = List.filter (fun v -> List.mem v eql |> not) vs' in
        build_ec vs' (eql::acc)
    in

    (* TODO make this a partial equivalence class (EC). It is partial
       because states that are not there should be considered
       singletons *)
    let ec = build_ec vs_out_taus_only [] in

    let get_canonical v = (* TODO: from this is just EC translate but better. *)
      match List.find_opt (fun l -> List.mem v l) ec with
      | None -> v
      | Some [] -> failwith "This cannot happen"
      | Some (v'::vs') ->
        if List.exists FSM.State.is_start vs' then FSM.State.mark_as_start v' else v'
    in
    let get_canonical_edge e =
      FSM.E.create (FSM.E.src e |> get_canonical) (FSM.E.label e) (FSM.E.dst e |> get_canonical)
    in
    let res = FSM.fold_edges_e (fun e fsm -> FSM.add_edge_e fsm (get_canonical_edge e)) fsm FSM.empty in
    "remove_mutally_taud_states start" |> Utils.log ;
    res

  let generate_local_for_roles roles gfsm =
    let local_machine r =
      r, project r gfsm |> remove_mutally_taud_states |> FSM.minimise_state_numbers
    in

    List.map local_machine roles
end
