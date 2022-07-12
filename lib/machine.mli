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

module Global : sig
  module Label : sig
    type t = Syntax.transition_label option

    val default : t

    val compare : t -> t -> int
  end

  module FSM : sig
    type t
  end

  val merge : FSM.t -> FSM.t -> FSM.t
  val generate_state_machine : Syntax.global -> State.t * FSM.t
end

module Local :
  sig

    module Label : sig
      type t = Syntax.Local.local_transition_label option


      val default : t

      val compare : t -> t -> int
    end

  module FSM : sig
    type t
  end

  val project : Syntax.role -> Global.FSM.t -> FSM.t
  end
