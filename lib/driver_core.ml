type world = {
  input : unit -> string;
  read_line : unit -> string option;
  out : string -> unit;
  err : string -> unit;
  args : string list;
  exit : int -> unit;
  print : string -> unit;
}

type 'v t = { of_string : string -> 'v; to_string : 'v -> string; run_io : world -> 'v -> int; run_main : world -> 'v -> unit }

let read_file path = In_channel.with_open_bin path In_channel.input_all
let write_file path s = Out_channel.with_open_bin path (fun oc -> Out_channel.output_string oc s)

let make ~build ~des ~io_name ~apply =
  let rec nat v = match des "Zero" v with _, [ p ] -> 1 + nat p | _ -> 0 in
  let u8 v = match des "MkU8" v with _, [ n ] -> nat n | _ -> assert false in
  let of_string s =
    let rec nat n = if n = 0 then build "Zero" [] else build "Succ" [ nat (n - 1) ] in
    let char b = build "MkChar" [ build "MkU8" [ nat b ] ] in
    String.fold_right (fun ch acc -> build "SCons" [ char (Char.code ch); acc ]) s (build "SNil" [])
  in
  let to_string v =
    let buf = Buffer.create 64 in
    let rec go v =
      match des "SNil" v with
      | _, [ ch; rest ] -> Buffer.add_char buf (Char.chr (u8 (List.hd (snd (des "MkChar" ch))))); go rest
      | _ -> ()
    in
    go v;
    Buffer.contents buf
  in
  let run_io w v =
    let result f = match f () with x -> build "Ok" [ x ] | exception Sys_error m -> build "Fail" [ of_string m ] in
    let rec loop v =
      let i, fields = des "Exit" v in
      match (io_name i, fields) with
      | "Exit", [ code ] -> u8 code
      | "WriteOut", [ s; next ] -> w.out (to_string s); loop next
      | "WriteErr", [ s; next ] -> w.err (to_string s); loop next
      | "ReadLine", [ k ] -> loop (apply k (match w.read_line () with Some l -> build "Some" [ of_string l ] | None -> build "None" []))
      | "ReadFile", [ path; k ] -> loop (apply k (result (fun () -> of_string (read_file (to_string path)))))
      | "WriteFile", [ path; s; k ] -> loop (apply k (result (fun () -> write_file (to_string path) (to_string s); build "MkUnit" [])))
      | "GetArgs", [ k ] -> loop (apply k (List.fold_right (fun a acc -> build "Cons" [ of_string a; acc ]) w.args (build "Nil" [])))
      | _ -> assert false
    in
    loop v
  in
  let run_main w f = w.out (to_string (apply f (of_string (w.input ())))) in
  { of_string; to_string; run_io; run_main }
