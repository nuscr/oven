type role = string
type value_type = string
type message_label = { name : string; payloads : value_type list; }
type rec_var = string
type 'a protocol =
  { protocol_name : string; roles : string list; interactions : 'a; }


type transition_label = {
  sender : role;
  receiver : role;
  label : message_label;
}
val string_of_transition_label : transition_label -> string

module Local :
sig

  type direction = Sending | Receiving

  type local_transition_label =
    { sender: role
    ; receiver: role
    ; direction : direction
    ; label: message_label}

  val string_of_local_transition_label : local_transition_label -> string
end

type global
  = MessageTransfer of transition_label
  | Choice of global list
  | Fin of global
  | Inf of global
  | Par of global list
  | Seq of global list
  | OutOfOrder of global * global
  | Join of global * global
  | Intersection of global * global
  | Prioritise of global * transition_label * transition_label
  | Rec of rec_var * global
  | Var of rec_var


val unfold : global -> rec_var -> global -> global

type compilation_unit = global protocol list

val validate_roles_in_compilation_unit : compilation_unit -> bool

val string_of_global : global -> string

(* local "types" *)

type local = global * role
