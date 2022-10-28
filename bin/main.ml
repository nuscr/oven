open BraidMPSTlib

let read_file fn =

  let ch = open_in fn in
  let s = really_input_string ch (in_channel_length ch) in
  close_in ch;
  s

let usage_msg = "braidMPST - command line tool\n Usage: syn <file1>"

let input_files = ref []

let anon_fun filename =
  input_files := filename::!input_files

let speclist = []


let process_file input_file =
    "// braidMPST - Local state machines for: " ^ input_file |> print_endline ;
  try
    let str = input_file |> read_file |> BraidMPST.local_dots_of_scribble_file in
    str |> print_endline
  with
  | exp ->  print_endline ("Unable to read the file!" ^ input_file ^ "\n" ^ Printexc.to_string exp)

let () =
  BraidMPSTlib.Utils.set_immediate_log true ;
  Arg.parse speclist anon_fun usage_msg;
  List.iter process_file !input_files
