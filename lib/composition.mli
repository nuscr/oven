module Composition :
  functor (FSM : Machine.FSMT) ->

  sig
    val parallel_compose : FSM.vertex * FSM.vertex -> FSM.t -> FSM.t -> FSM.vertex * (FSM.vertex list * FSM.t)

    val intersection_compose :
      FSM.vertex * FSM.vertex -> FSM.t -> FSM.t -> FSM.vertex * ( FSM.vertex list * FSM.t)

    val join_compose :
      FSM.vertex * FSM.vertex -> FSM.t -> FSM.t -> FSM.vertex * ( FSM.vertex list * FSM.t)
    val prioritise:
      FSM.t -> FSM.t -> FSM.vertex-> FSM.t -> FSM.vertex-> FSM.t -> FSM.vertex -> (FSM.vertex list * FSM.t)
    val only_reachable_from : FSM.vertex -> FSM.t -> FSM.t

  end
