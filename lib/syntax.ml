
type role = string

type value_type = string

type message_label =
  { name : string
  ; payloads : value_type list
  }

type rec_var = string

type 'a protocol =
    { protocol_name : string
    ; roles : string list
    ; interactions : 'a
    }

type transition_label = {sender: role ; receiver: role ; label: message_label}

let string_of_transition_label lbl =
  lbl.sender ^ "->" ^ lbl.receiver ^ "<" ^ lbl.label.name ^ ">"

module Local = struct

  type direction = Sending | Receiving

  type local_transition_label = {sender: role ; receiver: role ; direction : direction ; label: message_label}

  let string_of_local_transition_label lbl =
    let dir = match lbl.direction with Sending -> "!" | Receiving -> "?" in
    lbl.sender ^ "/" ^ lbl.receiver ^ dir ^ lbl.label.name
end

module Ext = struct

  type global_interaction  (* consider renaming just global *)
    = MessageTransfer of transition_label
    | Recursion of rec_var * global_interaction list
    | Continue of rec_var
    | Choice of global_interaction list list

  type compilation_unit = (global_interaction list) protocol list
end

module Int = struct

  type global
    = End
    (* the two references are wonky, but we want to be sure we keep pointers to things *)
    | RecVar of { name : rec_var ; global : global ref option ref }
    | Rec of rec_var * global
    | Choice of global_branch list

  and global_branch
    = Message of { tr_label : transition_label ; continuation: global}

  type compilation_unit = global protocol list

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

  let get_branches_participants branches =
    let rec f = function
      | [] -> []
      | Message {tr_label = {sender; receiver; label=_} ; continuation = _ } :: brs ->
        sender::receiver::f brs
    in
    f branches |> Utils.uniq

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
    let conts =
      List.for_all
        (function Message { tr_label = _ ; continuation } -> syntactic_checks continuation)
        branches
    in
    match senders with
    | [] -> false (* no messages is a mistake *)
    | r::roles -> conts && List.for_all (fun r' -> r = r') roles



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

  let validate_global_type g =
    match well_scoped g with
    | Some g' -> syntactic_checks g'
    | None -> false

  let validate_compilation_unit cu =
    List.for_all
      (function { protocol_name = _ ; roles = _ ; interactions} -> validate_global_type interactions)
      cu

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
    | MessageTransfer{sender ; receiver; label}::gis ->
      I.Message { tr_label = {sender; receiver; label} ; continuation =  tr gis}
    | _ -> assert false (* not a branch *)
  in
  let {protocol_name ; roles ; interactions} = g in
  {protocol_name ; roles ; interactions = tr interactions}

let translate_compilation_unit (cu : Ext.compilation_unit) : Int.compilation_unit =
  List.map translate cu
