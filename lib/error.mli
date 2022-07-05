
(* An internal problem or some expected invariant was violated *)
exception Violation of string

(* A user error *)
exception UserError of string
