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
  | WriteOut of 'v
  | WriteErr of 'v
  | ReadLine
  | ReadFile of 'v
  | WriteFile of 'v * 'v
  | GetArgs
  | GetEnv of 'v
  | GetEnvs
  | AppendFile of 'v * 'v
  | ReadRemaining
  | ListDir of 'v
  | GetCwd
  | Stat of 'v
  | MkDir of 'v
  | DeleteFile of 'v
  | DeleteDir of 'v
  | ConfineDir of 'v
  | ConfineOutputBytes of 'v
  | Measure of 'v

type 'v step = Exit of 'v | Continue of 'v

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
  mk_usage : 'v;
  request : 'v -> 'v request;
  step : 'v -> 'v step;
  is_start : 'v -> bool;
  apply : 'v -> 'v list -> 'v;
}

type 'v t = { of_string : string -> 'v; to_string : 'v -> string; perform : world -> 'v -> 'v; run_program : world -> 'v -> int; run_main : world -> 'v -> unit }

exception Halt of int

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

let print w s = if spend w (String.length s + 1) then w.print s else w.exit 1

let make ?str_of_host ?str_to_host ?nat_to_z ?nat_of_z o =
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
  let started = lazy (Unix.gettimeofday (), Unix.times (), Gc.quick_stat (), Gc.minor_words ()) in
  let perform w req =
    let entered = Gc.minor_words () in
    let result f = match f () with x -> o.ok x | exception ((Unix.Unix_error _ | Sys_error _) as e) -> o.fail (of_string (explain e)) in
    let list of_item xs = List.fold_right (fun x acc -> o.cons (of_item x) acc) xs o.nil in
    let change already f =
      match f () with
      | () -> o.ok o.changed
      | exception Unix.Unix_error (e, _, _) when already e -> o.ok o.unchanged
      | exception ((Unix.Unix_error _ | Sys_error _) as e) -> o.fail (of_string (explain e))
    in
    let created p = if Sys.file_exists p then 0 else entry_bytes in
    let fenced ?(follow = true) ?(cost = fun _ -> 0) path answer =
      let p = to_string path in
      match admits w.fence ~follow p with
      | Ok _ -> if spend w (cost p) then answer p else raise (Halt 1)
      | Error m -> o.fail (of_string m)
    in
    let write out s = let s = to_string s in if spend w (String.length s) then (out s; o.unit) else raise (Halt 1) in
    let write_to f path s = let s = to_string s in fenced ~cost:(fun p -> String.length s + created p) path (fun p -> result (fun () -> f p s; o.unit)) in
    match o.request req with
    | WriteOut s -> write w.out s
    | WriteErr s -> write w.err s
    | ReadLine -> (match w.read_line () with Some l -> o.some (of_string l) | None -> o.none)
    | ReadFile path -> fenced path (fun p -> result (fun () -> of_string (read_file p)))
    | WriteFile (path, s) -> write_to write_file path s
    | GetArgs -> list of_string w.args
    | GetEnv name -> (match w.env (to_string name) with Some v -> o.some (of_string v) | None -> o.none)
    | GetEnvs -> list (fun (n, v) -> o.pair (of_string n) (of_string v)) (List.sort compare (w.envs ()))
    | AppendFile (path, s) -> write_to append_file path s
    | ReadRemaining -> of_string (w.read_rest ())
    | ListDir path -> fenced path (fun p -> result (fun () -> list of_string (List.sort compare (Array.to_list (Sys.readdir p)))))
    | GetCwd -> of_string (w.cwd ())
    | Stat path ->
        fenced path (fun p ->
            match (Unix.stat p).st_kind with
            | Unix.S_REG -> o.ok o.is_file
            | Unix.S_DIR -> o.ok o.is_dir
            | _ -> o.ok o.is_other
            | exception Unix.Unix_error (Unix.ENOENT, _, _) -> o.ok o.missing
            | exception (Unix.Unix_error _ as e) -> o.fail (of_string (explain e)))
    | MkDir path -> fenced ~follow:false ~cost:created path (fun p -> change (fun e -> e = Unix.EEXIST && is_dir p) (fun () -> Unix.mkdir p 0o777))
    | DeleteFile path -> fenced ~follow:false path (fun p -> change (fun e -> e = Unix.ENOENT) (fun () -> Unix.unlink p))
    | DeleteDir path -> fenced ~follow:false path (fun p -> change (fun e -> e = Unix.ENOENT) (fun () -> Unix.rmdir p))
    | ConfineDir dir -> (match confine w.fence (to_string dir) with Ok () -> o.ok o.unit | Error m -> o.fail (of_string m))
    | ConfineOutputBytes bytes ->
        let z = to_z bytes in
        if clamp z <= !(w.limit) then (w.limit := clamp z; o.ok o.unit)
        else o.fail (of_string (Printf.sprintf "%s bytes: above the current output limit of %d bytes" (Z.to_string z) !(w.limit)))
    | Measure c ->
        let reading m1 extra =
          let g1 = Gc.quick_stat () in
          let c1 = Unix.times () in
          let t1 = Unix.gettimeofday () in
          let t0, c0, g0, m0 = Lazy.force started in
          let words f = f g1 -. f g0 and count f = float_of_int (f g1 - f g0) and ns f = 1e9 *. (f c1 -. f c0) in
          let nat x = match nat_of_z with Some f -> f (Z.of_float (Float.round (Float.max 0. x))) | None -> o.zero in
          o.apply o.mk_usage
            (List.map nat
               [ 1e9 *. (t1 -. t0); ns (fun c -> c.Unix.tms_utime); ns (fun c -> c.Unix.tms_stime);
                 m1 -. m0 +. extra; words (fun g -> g.Gc.promoted_words); words (fun g -> g.Gc.major_words -. g.Gc.promoted_words);
                 count (fun g -> g.Gc.minor_collections); count (fun g -> g.Gc.major_collections) ])
        in
        let measure extra = reading (Gc.minor_words ()) extra in
        if o.is_start c then begin
          let m = Gc.minor_words () in
          ignore (Sys.opaque_identity (measure 0.));
          let extra = Gc.minor_words () -. m in
          Gc.compact ();
          measure extra
        end
        else reading entered 0.
  in
  let run_program _w v =
    ignore (Lazy.force started);
    let rec loop v = match o.step v with Exit code -> u8 code | Continue k -> loop (o.apply k [ o.unit ]) in
    try loop v with Halt code -> code
  in
  let run_main w f = let s = to_string (o.apply f [ of_string (w.read_rest ()) ]) in if spend w (String.length s) then w.out s else w.exit 1 in
  { of_string; to_string; perform; run_program; run_main }
