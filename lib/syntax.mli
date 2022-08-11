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

type global  (* consider renaming just global *)
  = MessageTransfer of transition_label
  | Choice of global list
  | Fin of global
  | Inf of global
  | Par of global list
  | Seq of global list
  | LInt of global list
  | TInt of global list

type compilation_unit = global protocol list

(* val get_transitions : compilation_unit -> (string * transition_label) list *)
val validate_global_protocol : global protocol -> bool
val validate_compilation_unit : compilation_unit -> bool

(* local "types" *)

type local = global * role
