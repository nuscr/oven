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

module Ext :
  sig
    type global_interaction =
        MessageTransfer of transition_label
      | Recursion of rec_var * global_interaction list
      | Continue of rec_var
      | Choice of global_interaction list list
    type compilation_unit = global_interaction list protocol list
  end
module Int :
  sig
    type global =
        End
      | RecVar of { name : rec_var; global : global ref option ref; }
      | Rec of rec_var * global
      | Choice of global_branch list
    and global_branch =
        Message of { tr_label : transition_label; continuation : global; }

    type compilation_unit = global protocol list

    val get_global_ref : global ref option ref -> global ref
    val subst : global -> rec_var -> global -> global
    val unfold_top : global -> global

    val get_branches_participants : global_branch list -> role list

    val syntactic_checks : global -> bool
    val syntactic_checks_branches : global_branch list -> bool
    val well_scoped : global -> global option
    (* val get_transitions : compilation_unit -> (string * transition_label) list *)
    val validate_global_type : global -> bool
    val validate_compilation_unit : compilation_unit -> bool
  end
val translate : Ext.global_interaction list protocol -> Int.global protocol
val translate_compilation_unit : Ext.compilation_unit -> Int.compilation_unit
