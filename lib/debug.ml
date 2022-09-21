


let simplify_machine_flag = ref false
let keep_only_reacheable_flag = ref false

let set_all_debug_flags () =
  simplify_machine_flag := true ;
  keep_only_reacheable_flag := true

let unset_all_debug_flags () =
  simplify_machine_flag := false ;
  keep_only_reacheable_flag := false

let simplify_machine_off () = !simplify_machine_flag

let keep_only_reacheable_off () = !keep_only_reacheable_flag
