
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
    | RecVar of { name : rec_var ; global : global ref option ref } (* the two references are wonky, but we want to be sure we keep pointers to things *)
    | Rec of rec_var * global
    | Choice of global_branch list

  and global_branch
    = Message of { sender: role ; receiver: role ; label: message_label ; continuation: global}

  let rec subst g x = function
    | RecVar y when x = y.name -> g
    | (RecVar _) as g' -> g'
    | Rec (y, _) as g' when x = y -> g'
    | Rec (y, g') -> Rec (y, subst g x g')
    | End -> End
    | Choice branches ->
      Choice (List.map
                (function Message {sender ; receiver ; label ; continuation} ->
                   Message {sender ; receiver ; label ; continuation = subst g x continuation})
                branches)

  (* Unfold a type that begins with Rec *)
  let unfold_top = function
    | Rec (_, _) -> End
    | g -> g


  let well_scoped (g : global) : global option =
    let ctx : (rec_var *  global ref) list ref = ref [] in
    let rec lookup x =
      List.find (fun y -> x = fst y) !ctx
    in
    let rec f = function
    | RecVar {name ; global} ->
      let (_, g') = lookup name in
      global := Some g' ;
      RecVar {name ; global}

    | Rec (y, g') ->
      ctx := (y, ref g) :: !ctx ;
      Rec (y, f g')

    | End -> End

    | Choice _branches ->

      assert false
    in
    try
      Some (f g)
    with
      _ -> None
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
      I.Message {sender; receiver; label; continuation =  tr gis}
    | _ -> assert false (* not a branch *)
  in
  let Protocol {name ; roles ; interactions} = g in
  Protocol {name ; roles ; interactions = tr interactions}
