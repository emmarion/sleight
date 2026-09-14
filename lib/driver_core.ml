type world = {
  input : unit -> string;
  read_line : unit -> string option;
  out : string -> unit;
  err : string -> unit;
  args : string list;
  exit : int -> unit;
  print : string -> unit;
}

type 'v request = Exit of 'v | WriteOut of 'v * 'v | WriteErr of 'v * 'v | ReadLine of 'v | ReadFile of 'v * 'v | WriteFile of 'v * 'v * 'v | GetArgs of 'v

(* What the driver builds and reads of the prelude, each a direct operation on the program's own values. *)
type 'v ops = {
  zero : 'v;
  succ : 'v -> 'v;
  pred : 'v -> 'v option;
  u8 : 'v -> 'v;
  un_u8 : 'v -> 'v;
  char : 'v -> 'v;
  un_char : 'v -> 'v;
  snil : 'v;
  scons : 'v -> 'v -> 'v;
  un_str : 'v -> ('v * 'v) option;
  some : 'v -> 'v;
  none : 'v;
  ok : 'v -> 'v;
  fail : 'v -> 'v;
  unit : 'v;
  cons : 'v -> 'v -> 'v;
  nil : 'v;
  request : 'v -> 'v request;
  apply : 'v -> 'v -> 'v;
}

type 'v t = { of_string : string -> 'v; to_string : 'v -> string; run_io : world -> 'v -> int; run_main : world -> 'v -> unit }

let read_file path = In_channel.with_open_bin path In_channel.input_all
let write_file path s = Out_channel.with_open_bin path (fun oc -> Out_channel.output_string oc s)

let make o =
  let rec nat v = match o.pred v with Some p -> 1 + nat p | None -> 0 in
  let u8 v = nat (o.un_u8 v) in
  let of_string s =
    let rec nat n = if n = 0 then o.zero else o.succ (nat (n - 1)) in
    String.fold_right (fun ch acc -> o.scons (o.char (o.u8 (nat (Char.code ch)))) acc) s o.snil
  in
  let to_string v =
    let buf = Buffer.create 64 in
    let rec go v = match o.un_str v with Some (ch, rest) -> Buffer.add_char buf (Char.chr (u8 (o.un_char ch))); go rest | None -> () in
    go v;
    Buffer.contents buf
  in
  let run_io w v =
    let result f = match f () with x -> o.ok x | exception Sys_error m -> o.fail (of_string m) in
    let rec loop v =
      match o.request v with
      | Exit code -> u8 code
      | WriteOut (s, next) -> w.out (to_string s); loop next
      | WriteErr (s, next) -> w.err (to_string s); loop next
      | ReadLine k -> loop (o.apply k (match w.read_line () with Some l -> o.some (of_string l) | None -> o.none))
      | ReadFile (path, k) -> loop (o.apply k (result (fun () -> of_string (read_file (to_string path)))))
      | WriteFile (path, s, k) -> loop (o.apply k (result (fun () -> write_file (to_string path) (to_string s); o.unit)))
      | GetArgs k -> loop (o.apply k (List.fold_right (fun a acc -> o.cons (of_string a) acc) w.args o.nil))
    in
    loop v
  in
  let run_main w f = w.out (to_string (o.apply f (of_string (w.input ())))) in
  { of_string; to_string; run_io; run_main }
