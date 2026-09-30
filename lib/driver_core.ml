type world = {
  read_rest : unit -> string;
  read_line : unit -> string option;
  out : string -> unit;
  err : string -> unit;
  args : string list;
  env : string -> string option;
  envs : unit -> (string * string) list;
  cwd : unit -> string;
  exit : int -> unit;
  print : string -> unit;
  fence : string ref;
  limit : int ref;
  used : int ref;
}

type 'v request =
  | Exit of 'v
  | Step of 'v
  | WriteOut of 'v * 'v
  | WriteErr of 'v * 'v
  | ReadLine of 'v
  | ReadFile of 'v * 'v
  | WriteFile of 'v * 'v * 'v
  | GetArgs of 'v
  | GetEnv of 'v * 'v
  | GetEnvs of 'v
  | AppendFile of 'v * 'v * 'v
  | ReadRemaining of 'v
  | ListDir of 'v * 'v
  | GetCwd of 'v
  | Stat of 'v * 'v
  | MkDir of 'v * 'v
  | DeleteFile of 'v * 'v
  | DeleteDir of 'v * 'v
  | ConfineDir of 'v * 'v
  | ConfineOutputBytes of 'v * 'v

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
  pair : 'v -> 'v -> 'v;
  is_file : 'v;
  is_dir : 'v;
  is_other : 'v;
  missing : 'v;
  changed : 'v;
  unchanged : 'v;
  request : 'v -> 'v request;
  apply : 'v -> 'v -> 'v;
  apply0 : 'v -> 'v;
}

type 'v t = { of_string : string -> 'v; to_string : 'v -> string; run_io : world -> 'v -> int; run_main : world -> 'v -> unit }

let read_file path = In_channel.with_open_bin path In_channel.input_all
let write_file path s = Out_channel.with_open_bin path (fun oc -> Out_channel.output_string oc s)
let append_file path s = Out_channel.with_open_gen [ Open_append; Open_creat; Open_wronly ] 0o666 path (fun oc -> Out_channel.output_string oc s)
let explain = function Unix.Unix_error (e, _, a) -> (if a = "" then "" else a ^ ": ") ^ Unix.error_message e | Sys_error m -> m | e -> Printexc.to_string e
let is_dir p = match (Unix.stat p).st_kind with Unix.S_DIR -> true | _ -> false | exception _ -> false
let parts p = List.filter (fun c -> c <> "" && c <> ".") (String.split_on_char '/' p)
let path cs = "/" ^ String.concat "/" cs

let resolve ~follow p =
  let follow = follow || List.mem (Filename.basename p) [ "."; ".." ] || String.ends_with ~suffix:"/" p in
  let rec go budget up = function
    | [] -> List.rev up
    | ".." :: rest -> go budget (match up with [] -> [] | _ :: above -> above) rest
    | c :: rest -> (
        let here = path (List.rev (c :: up)) in
        match (Unix.lstat here).st_kind with
        | Unix.S_LNK when follow || rest <> [] -> (
            match Unix.readlink here with
            | _ when budget = 0 -> raise (Sys_error (p ^ ": too many levels of symbolic links"))
            | target -> go (budget - 1) (if Filename.is_relative target then up else []) (parts target @ rest)
            | exception Unix.Unix_error _ -> List.rev (c :: up))
        | _ -> go budget (c :: up) rest
        | exception Unix.Unix_error _ -> List.rev (c :: up))
  in
  go 1000 [] (parts (if Filename.is_relative p then Sys.getcwd () ^ "/" ^ p else p))

let admits fence ~follow p =
  let rec prefix = function [], _ -> true | f :: fs, c :: cs -> f = c && prefix (fs, cs) | _ :: _, [] -> false in
  match resolve ~follow p with
  | cs when prefix (parts !fence, cs) -> Ok cs
  | _ -> Error (p ^ ": outside the confined directory " ^ !fence)
  | exception (Sys_error _ as e) -> Error (explain e)

let confine fence dir =
  Result.bind (admits fence ~follow:true dir) (fun cs ->
      match (Unix.stat (path cs)).st_kind with
      | Unix.S_DIR -> fence := path cs; Ok ()
      | _ -> Error (dir ^ ": not a directory")
      | exception e -> Error (explain e))

let entry_bytes = 4096
let clamp z = if Z.fits_int z then Z.to_int z else max_int

let output_limit b =
  if b <> "" && String.for_all (fun c -> c >= '0' && c <= '9') b then Ok (clamp (Z.of_string b)) else Error (b ^ ": not a number of bytes")

let start dir bytes env w =
  let fail m = prerr_endline m; exit 1 in
  Result.iter_error fail (confine w.fence dir);
  Option.iter (fun b -> w.limit := Result.fold ~ok:Fun.id ~error:fail (output_limit b)) bytes;
  if env then w else { w with env = (fun _ -> None); envs = (fun () -> []) }

let host_envs () =
  List.filter_map
    (fun s -> Option.map (fun i -> (String.sub s 0 i, String.sub s (i + 1) (String.length s - i - 1))) (String.index_opt s '='))
    (Array.to_list (Unix.environment ()))

let spend w cost =
  cost <= !(w.limit) - !(w.used) && (w.used := !(w.used) + cost; true)
  || (w.err (Printf.sprintf "runtime error: output limit exceeded: this request would bring the program's approximate output to %d bytes, over its limit of %d\n" (!(w.used) + cost) !(w.limit)); false)

let make ?str_of_host ?str_to_host ?nat_to_z o =
  let rec count z v = match o.pred v with Some p -> count (Z.succ z) p | None -> z in
  let to_z = Option.value nat_to_z ~default:(count Z.zero) in
  let u8 v = Z.to_int (to_z (o.un_u8 v)) in
  let of_string s =
    match str_of_host with
    | Some f -> f s
    | None ->
        let rec nat n = if n = 0 then o.zero else o.succ (nat (n - 1)) in
        String.fold_right (fun ch acc -> o.scons (o.char (o.u8 (nat (Char.code ch)))) acc) s o.snil
  in
  let to_string v =
    match str_to_host with
    | Some f -> f v
    | None ->
        let buf = Buffer.create 64 in
        let rec go v = match o.un_str v with Some (ch, rest) -> Buffer.add_char buf (Char.chr (u8 (o.un_char ch))); go rest | None -> () in
        go v;
        Buffer.contents buf
  in
  let run_io w v =
    let result f = match f () with x -> o.ok x | exception ((Unix.Unix_error _ | Sys_error _) as e) -> o.fail (of_string (explain e)) in
    let list of_item xs = List.fold_right (fun x acc -> o.cons (of_item x) acc) xs o.nil in
    let change already f =
      match f () with
      | () -> o.ok o.changed
      | exception Unix.Unix_error (e, _, _) when already e -> o.ok o.unchanged
      | exception ((Unix.Unix_error _ | Sys_error _) as e) -> o.fail (of_string (explain e))
    in
    let created p = if Sys.file_exists p then 0 else entry_bytes in
    let rec loop v =
      let fenced ?(follow = true) ?(cost = fun _ -> 0) path k answer =
        let p = to_string path in
        match admits w.fence ~follow p with
        | Ok _ -> if spend w (cost p) then loop (o.apply k (answer p)) else 1
        | Error m -> loop (o.apply k (o.fail (of_string m)))
      in
      let write out s k = let s = to_string s in if spend w (String.length s) then (out s; loop (o.apply0 k)) else 1 in
      let write_to f path s k = let s = to_string s in fenced ~cost:(fun p -> String.length s + created p) path k (fun p -> result (fun () -> f p s; o.unit)) in
      match o.request v with
      | Exit code -> u8 code
      | Step k -> loop (o.apply0 k)
      | WriteOut (s, k) -> write w.out s k
      | WriteErr (s, k) -> write w.err s k
      | ReadLine k -> loop (o.apply k (match w.read_line () with Some l -> o.some (of_string l) | None -> o.none))
      | ReadFile (path, k) -> fenced path k (fun p -> result (fun () -> of_string (read_file p)))
      | WriteFile (path, s, k) -> write_to write_file path s k
      | GetArgs k -> loop (o.apply k (list of_string w.args))
      | GetEnv (name, k) -> loop (o.apply k (match w.env (to_string name) with Some v -> o.some (of_string v) | None -> o.none))
      | GetEnvs k -> loop (o.apply k (list (fun (n, v) -> o.pair (of_string n) (of_string v)) (List.sort compare (w.envs ()))))
      | AppendFile (path, s, k) -> write_to append_file path s k
      | ReadRemaining k -> loop (o.apply k (of_string (w.read_rest ())))
      | ListDir (path, k) -> fenced path k (fun p -> result (fun () -> list of_string (List.sort compare (Array.to_list (Sys.readdir p)))))
      | GetCwd k -> loop (o.apply k (of_string (w.cwd ())))
      | Stat (path, k) ->
          fenced path k (fun p ->
              match (Unix.stat p).st_kind with
              | Unix.S_REG -> o.ok o.is_file
              | Unix.S_DIR -> o.ok o.is_dir
              | _ -> o.ok o.is_other
              | exception Unix.Unix_error (Unix.ENOENT, _, _) -> o.ok o.missing
              | exception (Unix.Unix_error _ as e) -> o.fail (of_string (explain e)))
      | MkDir (path, k) -> fenced ~follow:false ~cost:created path k (fun p -> change (fun e -> e = Unix.EEXIST && is_dir p) (fun () -> Unix.mkdir p 0o777))
      | DeleteFile (path, k) -> fenced ~follow:false path k (fun p -> change (fun e -> e = Unix.ENOENT) (fun () -> Unix.unlink p))
      | DeleteDir (path, k) -> fenced ~follow:false path k (fun p -> change (fun e -> e = Unix.ENOENT) (fun () -> Unix.rmdir p))
      | ConfineDir (dir, k) -> loop (o.apply k (match confine w.fence (to_string dir) with Ok () -> o.ok o.unit | Error m -> o.fail (of_string m)))
      | ConfineOutputBytes (bytes, k) ->
          let z = to_z bytes in
          loop (o.apply k (if clamp z <= !(w.limit) then (w.limit := clamp z; o.ok o.unit)
                           else o.fail (of_string (Printf.sprintf "%s bytes: above the current output limit of %d bytes" (Z.to_string z) !(w.limit)))))
    in
    loop v
  in
  let run_main w f = let s = to_string (o.apply f (of_string (w.read_rest ()))) in if spend w (String.length s) then w.out s else w.exit 1 in
  { of_string; to_string; run_io; run_main }
