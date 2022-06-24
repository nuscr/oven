
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

  type transition_label = {sender: role ; receiver: role ; label: message_label}

  type global
    = End
    | RecVar of { name : rec_var ; global : global ref option ref } (* the two references are wonky, but we want to be sure we keep pointers to things *)
    | Rec of rec_var * global
    | Choice of global_branch list

  and global_branch
    = Message of { tr_label : transition_label ; continuation: global}

  let get_global_ref (g : global ref option ref) : global ref =
    match !g with
    | Some g' -> g'
    | None -> assert false (* this should never happen *)

  let rec subst g x = function
    | RecVar y when x = y.name -> g
    | (RecVar _) as g' -> g'
    | Rec (y, _) as g' when x = y -> g'
    | Rec (y, g') -> Rec (y, subst g x g')
    | End -> End
    | Choice branches ->
      Choice (List.map
                (function Message { tr_label ; continuation} ->
                   Message { tr_label ; continuation = subst g x continuation})
                branches)

  (* Unfold a type that begins with Rec *)
  let unfold_top = function
    | Rec (_, _) -> End
    | g -> g


  (* the representation is a bit more versatile than what
     our types support, we check here that it is ok.
     Checks:
     - mixed choice is always the same sender
  *)
  let rec syntactic_checks = function
    | RecVar _
    | End -> true
    | Rec (_, g) -> syntactic_checks g
    | Choice branches -> syntactic_checks_branches branches

  and syntactic_checks_branches branches =
    let senders =
      List.map
        (function Message {tr_label = {sender ; receiver = _ ; label = _ }; _ } -> sender)
        branches
    in
    match senders with
    | [] -> false (* no messages is a mistake *)
    | r::roles -> List.for_all (fun r' -> r = r') roles



  (* tests the type is well scoped and connects all the recursion variables to form a graph *)
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

    | Choice branches ->
      let f' = function Message {tr_label ; continuation} ->
        Message {tr_label ; continuation = f continuation}
      in
      Choice (List.map f' branches)
    in
    try
      Some (f g)
    with
      _ -> None


  let rec get_enabled_transitions (roles : role list ) (blocked : role list) : global -> transition_label list =
    let is_done () =
      (* this assumes we have the right roles, maybe a stronger function can be implemented *)
      List.length blocked = List.length roles
    in
    (* let is_label_enabled {sender ; receiver ; label } = *)
    let is_not_blocked = function {sender ; receiver ; _} ->
      (not (List.mem sender blocked)) && (not (List.mem receiver blocked))
    in
    function
    | End -> []
    | Rec (_, g) -> get_enabled_transitions roles blocked g
    | RecVar _ when is_done () -> [] (* we need a notion of being done *)
    | RecVar {name = _ ; global} -> get_enabled_transitions roles blocked !(get_global_ref global)
    | Choice branches ->
      (* labels in this choice *)
      let labels =
        List.map (function  Message {tr_label ; _} -> tr_label) branches |>
        List.filter is_not_blocked
      in
      let blocked' =
        (blocked  @ List.concat_map (function {sender ; receiver ; _} -> [sender ; receiver]) labels) |> Utils.uniq
      in

      (* labels in the continuations of this choice *)
      let f = function Message {tr_label = _ ; continuation} ->
        get_enabled_transitions roles blocked' continuation
      in

      labels @ List.concat_map f branches


  let validate_global_type g =
    match well_scoped g with
    | Some g' -> syntactic_checks g'
    | None -> false

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
      I.Message { tr_label = {I.sender; I.receiver; I.label} ; continuation =  tr gis}
    | _ -> assert false (* not a branch *)
  in
  let Protocol {name ; roles ; interactions} = g in
  Protocol {name ; roles ; interactions = tr interactions}
