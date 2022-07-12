open Syntax
open Graph

module State = struct
  type t = { id : int
           ; is_start : bool
           ; is_end : bool ref
           }

  let equal s1 s2 = (s1.id = s2.id)

  let hash = Hashtbl.hash

  let compare s1 s2 = compare s1.id s2.id

  let mark_as_end s =
    s.is_end := true ; s

  let mark_as_not_end s =
    s.is_end := false ; s

  let fresh, fresh_start, fresh_end =
    let n = ref 0 in
    ((fun () -> incr n ; {id = !n ; is_start = false ; is_end = ref false}),
     (fun () -> incr n ; {id = !n ; is_start = true ; is_end = ref false}),
     (fun () -> incr n ; {id = !n ; is_start = false ; is_end = ref true}))
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

  let merge (fsm : FSM.t) (fsm' : FSM.t) : FSM.t =
    (* extend with vertices *)
    let with_vertices = FSM.fold_vertex (fun v g -> FSM.add_vertex g v) fsm' fsm in
    (* extend with edges *)
    let with_edges = FSM.fold_edges_e (fun e g -> FSM.add_edge_e g e) with_vertices with_vertices in
    with_edges

  let generate_state_machine (_g : global) : State.t * FSM.t =
    let start = State.fresh_start () in
    let start_fsm =  FSM.add_vertex FSM.empty start in
    let rec f st fsm =
      function
      | MessageTransfer lbl ->
        let st' = State.fresh() in
        let fsm' = FSM.add_vertex fsm st' in
        st', FSM.add_edge_e fsm' (FSM.E.create st (Some lbl) st')

      | Seq [] ->
        let _ = State.mark_as_end st in
        st, fsm

      | Seq gis ->
        let end_st, end_fsm =
          List.fold_left
            (fun (st', fsm) g -> f st' fsm g)
            (st, fsm)
            gis
        in
        let _ = State.mark_as_end end_st in
        end_st, end_fsm

      | Choice branches ->
        let end_sts, fsms = List.map (f st fsm) branches |> List.split in
        let fsm' = List.fold_left (fun fsm fsm' -> merge fsm fsm') fsm fsms in
        (* TODO the end state is boolshit (maybe this should split the thing) *)
        List.hd end_sts, fsm'

      | Fin g' ->
        let end_st, fsm' = f st fsm g' in
        let st' = State.mark_as_not_end end_st in
        st, FSM.add_edge fsm' st st'


      | Inf g' ->
        let end_st, fsm' = f st fsm g' in
        let st' = State.mark_as_not_end end_st in
        (* Inf can never sequence, so we get a fresh start for the continuation *)
        State.fresh (), FSM.add_edge fsm' st st'

      | Par _ ->
        assert false

    in

    let end_st, fsm_final = f start start_fsm _g in
    let _ = State.mark_as_end end_st in
    (start, fsm_final)
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
end
