
(* functions on lists *)
val uniq : 'a list -> 'a list
val is_empty : 'a list -> bool
val is_non_empty : 'a list -> bool

(* debugging functions *)
val log : string -> unit
val get_log : unit -> string
