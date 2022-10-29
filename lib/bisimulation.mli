module StateEquivalenceClasses :
  functor (FSM : StateMachine.FSMT) ->
  sig
    type state_equivalence_class
    val _string_of_state_equivalence_class :
      FSM.State.t list list -> string
    val canonicalise_start_end : FSM.State.t list list -> FSM.State.t list list
    val translate : state_equivalence_class -> FSM.t -> FSM.t
    val compute_from_pair_list :
      (FSM.vertex * FSM.vertex) list -> state_equivalence_class
  end

module type STRENGTH = sig
  type strength = Strong | Weak

  val strength : strength
end

module Strong : STRENGTH
module Weak : STRENGTH

module Bisimulation :
  functor (FSM : StateMachine.FSMT) (Str : STRENGTH) ->
  sig
    type block

    val get_strength : unit -> Str.strength

    val compute_bisimulation_quotient : FSM.t -> StateEquivalenceClasses(FSM).state_equivalence_class

    val are_states_bisimilar : StateEquivalenceClasses(FSM).state_equivalence_class -> FSM.vertex -> FSM.vertex -> bool

    val minimise : FSM.t -> FSM.t

    val generate_minimal_dot : FSM.t -> string

  end
