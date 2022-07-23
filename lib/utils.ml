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
  let contents = Buffer.create 4096 in
  (fun s ->
     Buffer.add_string contents s; Buffer.add_char contents '\n'),
  (fun () -> let s = Buffer.contents contents in Buffer.clear contents ; s)
