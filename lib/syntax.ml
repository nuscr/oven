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
    lbl.sender ^ dir ^ lbl.receiver ^ "<" ^ lbl.label.name ^ ">"
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
  | Prioritise of global * global * global
  | Rec of rec_var * global
  | Var of rec_var

type compilation_unit = global protocol list

let rec string_of_global = function
  | MessageTransfer lbl -> string_of_transition_label lbl
  | Choice gs ->
    "(" ^ (List.map string_of_global gs |> String.concat " (+) ") ^ ")"
  | Seq [] -> "Done"
  | Seq gs ->
    List.map string_of_global gs |> String.concat " ; "
  | Fin g -> "(" ^ string_of_global g ^ ")*"
  | Inf g -> "(" ^ string_of_global g ^ ")w"
  | _ -> "(NOT YET)"


let rec validate_roles roles = function
  | MessageTransfer {sender ; receiver ; label = _} ->
    if List.mem sender roles && List.mem receiver roles then true
    else Error.UserError "Unknown role used in protocol." |> raise
  | Choice branches
  | Par branches
  | Seq branches ->
    List.for_all (validate_roles roles) branches
  | Rec (_, g)
  | Fin g
  | Inf g ->
    validate_roles roles g
  | Prioritise (g1, g2, g3) ->
    validate_roles roles g1 &&
    validate_roles roles g2 &&
    validate_roles roles g3
  | Join (g1, g2)
  | Intersection (g1, g2) ->
    validate_roles roles g1 &&
    validate_roles roles g2
  | OutOfOrder (g1, g2) ->
    validate_roles roles g1 &&
    validate_roles roles g2
  | Var _ -> true



(* substitute g for x in the type *)
let unfold (g: global) (x : rec_var) : global -> global =
  let rec f =
    function
    | MessageTransfer lbl -> MessageTransfer lbl
    | Par gs' -> Par (List.map f gs')
    | Seq gs' -> Seq (List.map f gs')
    | OutOfOrder (g1', g2') -> OutOfOrder (f g1', f g2')
    | Choice gs' -> Choice (List.map f gs')
    | Fin g' -> Fin (f g')
    | Inf g' ->  Fin (f g')
    | Intersection (g1', g2') -> Intersection (f g1', f g2')
    | Join (g1', g2') -> Join (f g1', f g2')
    | Prioritise (g', MessageTransfer lbl1, MessageTransfer lbl2) ->
      Prioritise (f g', MessageTransfer lbl1, MessageTransfer lbl2)
    | Prioritise _ -> failwith "unsupported"
    | Rec (y, g') when x = y -> Rec (y, g')
    | Rec (y, g') -> Rec (y, f g')
    | Var y when x = y -> g
    | Var y -> Var y
  in
  f


let well_guarded : global -> bool =
  let guard dict = List.map (fun (x, _) -> (x, true)) dict in
  let rec f dict = function
    | Rec (x, g) -> f ((x, false)::dict) g
    | MessageTransfer _ -> true
    | Choice branches
    | Par branches ->
      List.for_all (f dict) branches
    | Seq [] -> true
    | Seq (g::gs) ->
      if f dict g then
        f (guard dict) (Seq gs)
      else false
    | Fin g
    | Inf g -> f dict g
    | Prioritise (g1, g2, g3) -> f dict g1 && f dict g2 && f dict g3
    | Join (g1, g2)
    | OutOfOrder (g1, g2)
    | Intersection (g1, g2) ->
      f dict g1 && f dict g2
    | Var x -> List.assoc x dict
  in
  f []

let well_guarded_protocol prot = well_guarded prot.interactions

let well_guarded_cu cu =
  if List.for_all well_guarded_protocol cu
  then ()
  else Error.UserError "Protocol not well guarded" |> raise

let syntactic_well_formedness nm =
  let rec f = function
    | MessageTransfer _ -> ()
    | Choice branches
    | Par branches
    | Seq branches ->
      List.iter f branches
    | Rec (x, g) -> in_rec [x] g
    | Fin g
    | Inf g -> f g

    | Prioritise (g1, g2, g3) -> f g1 ; f g2 ; f g3
    | Join (g1, g2)
    | OutOfOrder (g1, g2)
    | Intersection (g1, g2) ->
      f g1 ; f g2
    | Var x -> Error.UserError ("Unknown variable: " ^ x ^ " in protocol " ^ nm ^ ".") |> raise

  and in_rec c = function
    | MessageTransfer _ -> ()
    | Choice branches ->
      List.iter (in_rec c) branches
    | Seq branches ->
      List.iter (in_rec c) branches ; var_tail branches
    | Rec (x, g) -> in_rec (x::c) g
    | Par _
    | Fin _
    | Inf _
    | OutOfOrder _
    | Prioritise _
    | Join _
    | Intersection _
      -> Error.UserError ("Only messages and choice may appear in a rec block.") |> raise
    | Var x when List.mem x c -> ()
    | Var x -> Error.UserError ("Unknown variable: " ^ x ^ " in protocol " ^ nm ^ ".") |> raise

  and var_tail = function
    | []
    | [Var _] -> () (* tail position: ok *)
    | Var x ::_ -> Error.UserError ("Variable: " ^ x ^ " appears in non-tail position in protocol " ^ nm ^ ".") |> raise
    | _::gs -> var_tail gs

  in
  f

let syntactic_well_formedness_protocol protocol =
  syntactic_well_formedness protocol.protocol_name protocol.interactions

let syntactic_well_formedness_in_compilation_unit cu =
  List.iter syntactic_well_formedness_protocol cu


let validate_roles_in_global_protocol protocol =
  validate_roles protocol.roles protocol.interactions

let validate_roles_in_compilation_unit cu =
  syntactic_well_formedness_in_compilation_unit cu ;
  well_guarded_cu cu;
  List.for_all validate_roles_in_global_protocol cu


(* local "types" *)

type local = global * role
