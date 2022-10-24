
(* functions on lists *)
val split3 : ('a * 'b * 'c) list -> 'a list * 'b list * 'c list
val uniq : 'a list -> 'a list
val sorted_uniq : ('a -> 'a -> int) -> 'a list -> 'a list
val is_empty : 'a list -> bool
val is_non_empty : 'a list -> bool
val rem : 'a -> 'a list -> 'a list
val minus : 'a list -> 'a list -> 'a list

(* debugging functions *)
val log : string -> unit
val get_log : unit -> string
