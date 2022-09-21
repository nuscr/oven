
type flag =
  { description : string
  ; mutable state : bool
  }

let simplify_machine_flag = { description = "simplify_machine" ; state = false }
let keep_only_reacheable_flag = { description = "keep_only_reacheable" ; state = false }
let project_to_empty_flag = { description = "project_to_empty" ; state = false }
let post_process_taus_off_flag = { description = "post_process_taus_off" ; state = false }
let minimise_off_flag = { description = "minimise_off_flag" ; state = false }
let minimise_state_numbers_off_flag = { description = "minimise_state_numbers_off_flag" ; state = false }

let set_all_debug_flags () =
  simplify_machine_flag.state <- true ;
  keep_only_reacheable_flag.state <- true ;
  project_to_empty_flag.state <- true ;
  post_process_taus_off_flag.state <- true ;
  minimise_off_flag.state <- true ;
  minimise_state_numbers_off_flag.state <- true

let unset_all_debug_flags () =
  simplify_machine_flag.state <- false ;
  keep_only_reacheable_flag.state <- false ;
  project_to_empty_flag.state <- false ;
  post_process_taus_off_flag.state <- false ;
  minimise_off_flag.state <- false ;
  minimise_state_numbers_off_flag.state <- false


let get_set_flag flag = function
  | None when flag.state = true -> "Skipping: " ^ flag.description |> Utils.log ; flag.state
  | None -> "Doing: " ^ flag.description |> Utils.log ; flag.state
  | Some v -> let old = flag.state in flag.state <- v ; old

let simplify_machine_off  = get_set_flag simplify_machine_flag

let keep_only_reacheable_off =  get_set_flag keep_only_reacheable_flag

let project_to_empty = get_set_flag project_to_empty_flag

let post_process_taus_off = get_set_flag post_process_taus_off_flag

let minimise_off = get_set_flag minimise_off_flag

let minimise_state_numbers_off = get_set_flag minimise_state_numbers_off_flag
