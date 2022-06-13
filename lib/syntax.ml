



type role = string

type value_type = string

type message_label =
  { name : string
  ; payloads : value_type list
  }

type rec_var = string

type 'a protocol =
    Protocol of { name : string
                ; roles : string list
                ; interactions : 'a
                }


module Ext = struct

  type global_interaction  (* consider renaming just global *)
    = MessageTransfer of
      { label : message_label
      ; sender : role
      ; receiver : role
      }

    | Recursion of rec_var * global_interaction list
    | Continue of rec_var
    | Choice of global_interaction list list

  type compilation_unit = (global_interaction list) protocol list
end

module Int = struct

  type global
    = End
    | RecVar of { name : rec_var ; global : global option ref }
    | Rec of rec_var * global
    | Choice of global_branch list

  and global_branch
    = Message of role * role * message_label * global

  let rec subst g x = function
    | RecVar y when x = y.name -> g
    | (RecVar _) as g' -> g'
    | Rec (y, _) as g' when x = y -> g'
    | Rec (y, g') -> Rec (y, subst g x g')
    | End -> End
    | Choice branches ->
      Choice (List.map
                (function Message (a, b, t, g') -> Message (a, b, t, subst g x g'))
                branches)


  (* Unfold a type that begins with Rec *)
  let unfold_top = function
    | Rec (_, _) -> End
    | g -> g

end

let translate (g : (Ext.global_interaction list) protocol) : Int.global protocol =
  let open Ext in
  let module I = Int in
  let rec tr gis =
    match gis with
    | MessageTransfer _ ::_ ->
      I.Choice [tr_branch  gis]
    | [Choice giss] ->
      let branches = List.map tr_branch giss in
      I.Choice branches
    | Choice _::_ ->  assert false (* unexpected continuation after choice *)
    | [Recursion (x, gis)] -> I.Rec (x, tr gis)
    | Recursion _::_ -> assert false (* unexpected continuation after recursion *)
    | [Continue n] -> I.RecVar {name = n ; global = ref None}
    | Continue _::_ -> assert false (* unexpected continuation after continue *)
    | [] -> I.End
  and tr_branch = function
    | MessageTransfer{label ; sender ; receiver}::gis ->
      I.Message(sender, receiver, label, tr gis)
    | _ -> assert false (* not a branch *)
  in
  let Protocol {name ; roles ; interactions} = g in
  Protocol {name ; roles ; interactions = tr interactions}
