let rec uniq x =
  let rec helper l n =
    match l with
    | [] -> []
    | h :: t when n = h -> helper t n
    | h :: t -> h::(helper t n)
  in
  match x with
  | [] -> []
  | h::t -> h::(helper (uniq t) h)


let is_empty = function
  | [] -> true
  | _ -> false

let is_non_empty = function
  | [] -> false
  | _ -> true

let log, get_log =
  let contents = ref "" in
  (fun s ->
     contents := !contents ^ "\n" ^ s),
  (fun () -> let s = !contents in contents := "" ; s)
