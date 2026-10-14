(* The indentation check of lib/indent.ml run on its own, over the files named on the command line.
   The driver warns with the same messages as it reads each file; this reports them and nothing else,
   and exits 1 when there are any, so it can gate a commit. *)
module Indent = Sleight.Indent

let issues = ref 0

let check_file path =
  let src = match Sleight.Program.read_file path with s -> s | exception Sys_error m -> prerr_endline m; exit 2 in
  let found, stopped = Indent.issues path src in
  List.iter (fun i -> incr issues; print_string (Indent.show i)) found;
  (match stopped with
   | None -> ()
   | Some (l, m) ->
       incr issues;
       Printf.printf "%s: %s -- everything above is what was read before that\n" (Sleight.Reader.where path l) m);
  if found <> [] || stopped <> None then print_endline (Sleight.Reader.shape_note path)

let () =
  let files = List.tl (Array.to_list Sys.argv) in
  if files = [] then (prerr_endline "usage: indent <file.sl> ..."; exit 2);
  List.iter check_file files;
  if !issues = 0 then (print_endline "no nesting/indentation inconsistencies found"; exit 0)
  else (Printf.printf "%d issue(s) found\n" !issues; exit 1)
