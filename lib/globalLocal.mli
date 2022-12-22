module State :
sig
  type t
  val equal : t -> t -> bool
  val hash : t -> int
  val compare : t -> t -> int
  val fresh : unit -> t
  val fresh_start : unit -> t
  val fresh_end : unit -> t

  val is_start : t -> bool
  val is_end : t -> bool

end

module Global :
sig
  module Label : sig
    type t = Syntax.transition_label option

    val default : t

    val compare : t -> t -> int
  end

  module FSM : Machine.FSM

  val generate_state_machine : Syntax.global -> State.t * FSM.t

  val minimise : FSM.t -> FSM.t

  val generate_minimal_dot : FSM.t -> string
end

module Local :
sig

  module Label : sig
    type t = Syntax.Local.local_transition_label option


    val default : t

    val compare : t -> t -> int
  end

  module FSM : Machine.FSM

  val project : Syntax.role -> Global.FSM.t -> FSM.t

  val generate_minimal_dot : FSM.t -> string

  val generate_local_for_roles : Syntax.role list -> Global.FSM.t -> (Syntax.role * FSM.t) list

  type wb_res = (unit, string) Result.t

  val well_behaved_local_machines : (Syntax.role * FSM.t) list -> wb_res
end
