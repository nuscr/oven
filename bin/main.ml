let read_file fn =

  let ch = open_in fn in
  let s = really_input_string ch (in_channel_length ch) in
  close_in ch;
  s

let usage_msg = "synMPST - command line tool\n Usage: syn <file1>"

let input_file = ref ""

let anon_fun filename =
  input_file := filename

let speclist = []

let () =
  Arg.parse speclist anon_fun usage_msg;
  try
    let str = !input_file |> read_file |> SynMPSTlib.local_dots_of_scribble_file in
    "// synMPST - Local state machines" |> print_endline ;
    str |> print_endline
  with
  | exp ->  print_endline ("Unable to read the file!" ^ !input_file ^ "\n" ^ Printexc.to_string exp)
