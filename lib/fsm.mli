module State :
  sig
    type t = int
    val equal : 'a -> 'a -> bool
    val hash : 'a -> int
    val compare : 'a -> 'a -> int
    val fresh : unit -> int
  end

module GlobalLabel : sig
  type t = Syntax.transition_label option

  val default : t

  val compare : t -> t -> int
end

type t

val merge : t -> t -> t
val generate_state_machine : Syntax.Int.global -> State.t * t


module Local :
  sig

    module LocalLabel : sig
      type t = Syntax.Local.local_transition_label option


      val default : t

      val compare : t -> t -> int
    end

  module LocalFSM : sig
    type t
  end

  val project : Syntax.role -> t -> LocalFSM.t
  end
