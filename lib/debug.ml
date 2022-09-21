


let simplify_machine_flag = ref false
let keep_only_reacheable_flag = ref false
let project_to_empty_flag = ref false
let post_process_taus_off_flag = ref false

let set_all_debug_flags () =
  simplify_machine_flag := true ;
  keep_only_reacheable_flag := true ;
  project_to_empty_flag := true ;
post_process_taus_off_flag := true

let unset_all_debug_flags () =
  simplify_machine_flag := false ;
  keep_only_reacheable_flag := false ;
  project_to_empty_flag := false ;
  post_process_taus_off_flag := false


let get_set_flag flag = function
  | None -> !flag
  | Some v -> let old = !flag in flag := v ; old

let simplify_machine_off  = get_set_flag simplify_machine_flag

let keep_only_reacheable_off =  get_set_flag keep_only_reacheable_flag

let project_to_empty = get_set_flag project_to_empty_flag

let post_process_taus_off = get_set_flag post_process_taus_off_flag
