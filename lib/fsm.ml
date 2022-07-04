open Syntax.Int
open Graph

module State = struct
  type t = int

  let equal = ( = )

  let hash = Hashtbl.hash

  let compare = compare

  let fresh =
    let n = ref 0 in
    fun () ->
      incr n ; !n
end

module GlobalLabel = struct
  type t = Syntax.transition_label option

  let default : t = None

  let compare = Stdlib.compare (* consider a more specific one *)

  let project r lbl =
    Option.bind lbl
      (fun l-> Operations.Local.project_transition r l)
end


module GlobalFSM = Persistent.Digraph.ConcreteLabeled (State) (GlobalLabel)

type t = GlobalFSM.t

let merge (fsm : GlobalFSM.t) (fsm' : GlobalFSM.t) : GlobalFSM.t =
  (* extend with vertices *)
  let with_vertices = GlobalFSM.fold_vertex (fun v g -> GlobalFSM.add_vertex g v) fsm' fsm in
  (* extend with edges *)
  let with_edges = GlobalFSM.fold_edges_e (fun e g -> GlobalFSM.add_edge_e g e) with_vertices with_vertices in
  with_edges

let generate_state_machine (g : global) : State.t * GlobalFSM.t =
  let start = State.fresh () in
  let start_fsm =  GlobalFSM.add_vertex GlobalFSM.empty start in
  let rec f st fsm gvs = function
    | End ->
      let end_st = State.fresh () in
      let fsm' = GlobalFSM.add_vertex fsm end_st in
      GlobalFSM.add_edge fsm' st end_st

    | Rec (name, g) ->
      f st fsm ((name, st)::gvs) g

    | RecVar {name ; global = _} ->
      let jump_to = List.assoc name gvs in
      GlobalFSM.add_edge fsm st jump_to

    | Choice branches ->
      let fsms = List.map (br st fsm gvs) branches in
      List.fold_left (fun fsm fsm' -> merge fsm fsm') fsm fsms
  and br st fsm gvs = function Message {tr_label ; continuation} ->
    let new_st = State.fresh() in
    let e = GlobalFSM.E.create st (Some tr_label) new_st in
    let fsm' = f new_st (GlobalFSM.add_vertex fsm new_st) gvs continuation in
    GlobalFSM.add_edge_e fsm' e
  in
  (start, f start start_fsm [] g)

module Local = struct

  module LocalLabel = struct
    type t = Syntax.Local.local_transition_label option

    let default : t = None

    let compare = Stdlib.compare (* consider a more specific one *)
  end

  module LocalFSM = Persistent.Digraph.ConcreteLabeled (State) (LocalLabel)
  let project (r : Syntax.role) (fsm : GlobalFSM.t) : LocalFSM.t =
    let project_edge e =
      LocalFSM.E.create
        (GlobalFSM.E.src e)
        (GlobalLabel.project r (GlobalFSM.E.label e))
        (GlobalFSM.E.dst e)
    in
    let with_vertices = GlobalFSM.fold_vertex (fun s f -> LocalFSM.add_vertex f s) fsm LocalFSM.empty in
    let with_edges =
      GlobalFSM.fold_edges_e
        (fun e f -> LocalFSM.add_edge_e f (project_edge e))
        fsm
        with_vertices
    in
    with_edges
end
