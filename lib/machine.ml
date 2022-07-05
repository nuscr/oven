open Syntax
open Graph

module State = struct
  type t = { id : int
           ; is_start : bool
           ; is_end : bool
           }

  let equal s1 s2 = (s1.id = s2.id)

  let hash = Hashtbl.hash

  let compare s1 s2 = compare s1.id s2.id

  let fresh, fresh_start, fresh_end =
    let n = ref 0 in
    ((fun () -> incr n ; {id = !n ; is_start = false ; is_end = false}),
     (fun () -> incr n ; {id = !n ; is_start = true ; is_end = false}),
     (fun () -> incr n ; {id = !n ; is_start = false ; is_end = true}))
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

  (* type t = FSM.t *)

  let merge (fsm : FSM.t) (fsm' : FSM.t) : FSM.t =
    (* extend with vertices *)
    let with_vertices = FSM.fold_vertex (fun v g -> FSM.add_vertex g v) fsm' fsm in
    (* extend with edges *)
    let with_edges = FSM.fold_edges_e (fun e g -> FSM.add_edge_e g e) with_vertices with_vertices in
    with_edges

  let generate_state_machine (_g : global) : State.t * FSM.t =
    let start = State.fresh_start () in
    let start_fsm =  FSM.add_vertex FSM.empty start in
    let rec f _st _fsm _gvs _g =
      (* function *)
    (*   | End -> *)
    (*     let end_st = State.fresh_end () in *)
    (*     let fsm' = FSM.add_vertex fsm end_st in *)
    (*     FSM.add_edge fsm' st end_st *)

    (*   | Rec (name, g) -> *)
    (*     f st fsm ((name, st)::gvs) g *)

    (*   | RecVar {name ; global = _} -> *)
    (*     let jump_to = List.assoc name gvs in *)
    (*     FSM.add_edge fsm st jump_to *)

    (*   | Choice branches -> *)
    (*     let fsms = List.map (br st fsm gvs) branches in *)
    (*     List.fold_left (fun fsm fsm' -> merge fsm fsm') fsm fsms *)
    assert false
    (* and br st fsm gvs = function Message {tr_label ; continuation} -> *)
    (*   let new_st = State.fresh() in *)
    (*   let e = FSM.E.create st (Some tr_label) new_st in *)
    (*   let fsm' = f new_st (FSM.add_vertex fsm new_st) gvs continuation in *)
    (*   FSM.add_edge_e fsm' e *)
    in
    (start, f start start_fsm [] _g)
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
