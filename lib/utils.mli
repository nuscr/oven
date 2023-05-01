
(* functions on lists *)
val uniq : 'a list -> 'a list
val cartesian : 'a list -> 'b list -> ('a * 'b) list
val is_empty : 'a list -> bool
val is_non_empty : 'a list -> bool
val rem : 'a -> 'a list -> 'a list
val minus : 'a list -> 'a list -> 'a list
val  split_3 : ('a * 'b * 'c) list -> 'a list * 'b list * 'c list

val append : 'a list -> 'a list -> 'a list
val rev : 'a list -> 'a list

(* debugging functions *)
val log : string -> unit
val get_log : unit -> string

(* if it is true then use std error for the log, and no buffering *)
val set_immediate_log : bool -> unit
