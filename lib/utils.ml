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


(*
let sorted_uniq compare l =
  let rec rem_dup l acc = function
    | [] -> acc
    | x::xs when Some x = l -> rem_dup l acc xs
    | x::xs -> rem_dup (Some x) (x::acc) xs
  in
  List.sort compare l |> rem_dup None []
*)

let sorted_uniq = List.sort_uniq

let is_empty = function
  | [] -> true
  | _ -> false

let is_non_empty = function
  | [] -> false
  | _ -> true

let rem x l =
  let rec f acc = function
    | [] -> acc
    | y::ys when x = y -> f acc ys
    | y::ys -> f (y::acc) ys
  in
  f [] l

let rec minus l1 = function
  | [] -> l1
  | y::ys -> minus (rem y l1) ys

let log, get_log =
  let contents = Buffer.create 4096 in
  (fun s ->
     Buffer.add_string contents s; Buffer.add_char contents '\n'),
  (fun () -> let s = Buffer.contents contents in Buffer.clear contents ; s)
