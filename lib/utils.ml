let  split_3 l =
  let rec f (acc1, acc2, acc3) = function
    | [] -> (acc1, acc2, acc3)
    | (x1, x2, x3)::xs -> f (x1::acc1, x2::acc2, x3::acc3) xs
  in
  f ([], [], []) l

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

let rev (l : 'a list) : 'a list =
  let rec f acc = function
    | [] -> acc
    | x::xs -> f (x::acc) xs
  in
  f [] l

(* Do a proper one with CPS if this works *)
let append (l1 : 'a list) (l2 : 'a list) : 'a list =
  let rec f l acc =
    match l with
      [] -> acc
    | x::xs -> f xs (x::acc)
  in
  f (rev l1) l2


let cartesian (l1 : 'a list) (l2 : 'b list) : ('a * 'b) list =
  List.fold_left (fun acc1 ele1 ->
    List.fold_left (fun acc2 ele2 -> (ele1,ele2)::acc2) acc1 l2) [] l1

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

(* Logging functions *)

let log, get_log, set_immediate_log =
  let immediate = ref false in
  let contents = Buffer.create 4096 in
  (fun s -> if !immediate then (Stdlib.output_string Stdlib.stderr @@ "//Log: " ^ s ^ "\n" ; Stdlib.flush Stdlib.stderr) else
     Buffer.add_string contents s; Buffer.add_char contents '\n'),
  (fun () -> let s = Buffer.contents contents in Buffer.clear contents ; s),
  fun b -> immediate := b
