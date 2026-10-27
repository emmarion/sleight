type fence = { reads : string list; writes : string list }

type world = {
  read_rest : unit -> string;
  read_line : unit -> string option;
  out : string -> int -> int -> unit;
  err : string -> int -> int -> unit;
  args : string list;
  env : string -> string option;
  envs : unit -> (string * string) list;
  cwd : unit -> string;
  exit : int -> unit;
  print : string -> unit;
  exec : bool;
  fence : fence ref;
  limit : int option ref;
  used : int ref;
}

type 'v request =
  | WriteOut of 'v
  | WriteErr of 'v
  | ReadLine
  | ReadFile of 'v
  | ReadFileIn of 'v * 'v
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
  | ConfinePaths of 'v * 'v
  | ConfineOutputBytes of 'v
  | Measure of 'v
  | Exec of 'v * 'v * 'v * 'v * 'v

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
  un_list : 'v -> ('v * 'v) option;
  un_pair : 'v -> 'v * 'v;
  un_some : 'v -> 'v option;
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
  mk_exited : 'v;
  request : 'v -> 'v request;
  step : 'v -> 'v step;
  is_start : 'v -> bool;
  apply : 'v -> 'v list -> 'v;
}

type 'v t = { of_string : string -> 'v; to_string : 'v -> string; perform : world -> 'v -> 'v; run_program : world -> 'v -> int; run_main : world -> 'v -> unit }

exception Halt of int

let read_file path = In_channel.with_open_bin path In_channel.input_all
let save flags path (s, o, l) = Out_channel.with_open_gen flags 0o666 path (fun oc -> Out_channel.output_substring oc s o l)
let replacing = [ Open_wronly; Open_creat; Open_trunc; Open_binary ]
let write_file path s = save replacing path (s, 0, String.length s)
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
            | target -> go (budget - 1) (if Filename.is_relative target then up else []) (parts target @ rest))
        | _ -> go budget (c :: up) rest
        | exception Unix.Unix_error _ when rest = [] -> List.rev (c :: up))
  in
  go 1000 [] (parts (if Filename.is_relative p then Sys.getcwd () ^ "/" ^ p else p))

let rec prefix = function [], _ -> true | f :: fs, c :: cs -> f = c && prefix (fs, cs) | _ :: _, [] -> false
let covers dirs cs = List.exists (fun d -> prefix (parts d, cs)) dirs

let resolved ~follow p = match resolve ~follow p with cs -> Ok cs | exception ((Sys_error _ | Unix.Unix_error _) as e) -> Error (explain e)
let inside dir ~follow p = Result.map (fun cs -> if covers [ dir ] cs then Some cs else None) (resolved ~follow p)

type access = Read | Write

let unconfined = { reads = []; writes = [ "/" ] }
let reaches f access cs = covers (match access with Read -> f.reads @ f.writes | Write -> f.writes) cs
let outside access p = Error (p ^ ": outside the " ^ (match access with Read -> "readable" | Write -> "writable") ^ " paths")

let admits fence access ~follow p =
  Result.bind (resolved ~follow p) (fun cs -> if reaches !fence access cs then Ok cs else outside access p)

let within dir p =
  match path (resolve ~follow:true dir) with
  | exception Unix.Unix_error (Unix.ENOENT, _, _) -> Error (p ^ ": no directory " ^ dir)
  | exception ((Sys_error _ | Unix.Unix_error _) as e) -> Error (explain e)
  | d when not (is_dir d) -> Error (p ^ ": no directory " ^ dir)
  | d ->
      let full = if Filename.is_relative p then d ^ "/" ^ p else p in
      let named m = p ^ if String.starts_with ~prefix:(full ^ ":") m then String.sub m (String.length full) (String.length m - String.length full) else ": " ^ m in
      Result.bind (Result.map_error named (inside d ~follow:true full)) (function
        | None -> Error (p ^ ": outside the directory " ^ dir)
        | Some _ -> Ok (full, fun () -> match read_file full with s -> Ok s | exception Sys_error m -> Error (named m)))

let read_within dir p = Result.bind (within dir p) (fun (_, read) -> read ())

let confine fence reads writes =
  let entry access e = Result.bind (resolved ~follow:true e) (fun cs -> if reaches !fence access cs then Ok (path cs) else outside access e) in
  let rec all access = function [] -> Ok [] | e :: es -> Result.bind (entry access e) (fun p -> Result.map (List.cons p) (all access es)) in
  Result.bind (all Read reads) (fun reads -> Result.map (fun writes -> fence := { reads; writes }) (all Write writes))

let restrict fence reads writes = if reads = [] && writes = [] then Ok () else confine fence reads writes

let entry_bytes = 4096
let clamp z = if Z.fits_int z then Some (Z.to_int z) else None

let output_limit b =
  match Ffi_core.nat_of_string b with Some z -> Ok (clamp z) | None -> Error (b ^ ": not a number of bytes")

let start reads writes bytes env exec w =
  let fail m = prerr_endline m; exit 1 in
  Result.iter_error fail (restrict w.fence reads writes);
  Option.iter (fun b -> w.limit := Result.fold ~ok:Fun.id ~error:fail (output_limit b)) bytes;
  let w = { w with exec = w.exec && exec } in
  if env then w else { w with env = (fun _ -> None); envs = (fun () -> []) }

let signal_names =
  Sys.[ (sigabrt, "SIGABRT"); (sigalrm, "SIGALRM"); (sigfpe, "SIGFPE"); (sighup, "SIGHUP"); (sigill, "SIGILL"); (sigint, "SIGINT");
        (sigkill, "SIGKILL"); (sigpipe, "SIGPIPE"); (sigquit, "SIGQUIT"); (sigsegv, "SIGSEGV"); (sigterm, "SIGTERM"); (sigusr1, "SIGUSR1");
        (sigusr2, "SIGUSR2"); (sigbus, "SIGBUS"); (sigtrap, "SIGTRAP"); (sigxcpu, "SIGXCPU"); (sigxfsz, "SIGXFSZ") ]

let found prog env =
  let runnable p = Sys.file_exists p && not (is_dir p) && (try Unix.access p [ Unix.X_OK ]; true with Unix.Unix_error _ -> false) in
  let absolute p = if Filename.is_relative p then Filename.concat (Sys.getcwd ()) p else p in
  if String.contains prog '/' then Ok (absolute prog)
  else
    let dirs = Option.fold ~none:[] ~some:(String.split_on_char ':') (List.assoc_opt "PATH" env) in
    Option.to_result ~none:(prog ^ ": not found on the PATH it was given")
      (List.find_opt runnable (List.map (fun d -> absolute (Filename.concat (if d = "" then "." else d) prog)) dirs))

(* The child reports a failure to start through a close-on-exec pipe, which reads empty once the exec succeeds. *)
let exec prog args env dir input =
  Result.bind (found prog env) (fun path ->
      let in_r, in_w = Unix.pipe ~cloexec:true () and out_r, out_w = Unix.pipe ~cloexec:true () in
      let err_r, err_w = Unix.pipe ~cloexec:true () and why_r, why_w = Unix.pipe ~cloexec:true () in
      match Unix.fork () with
      | 0 ->
          (try
             Option.iter Unix.chdir dir;
             List.iter (fun (a, b) -> Unix.dup2 ~cloexec:false a b) [ (in_r, Unix.stdin); (out_w, Unix.stdout); (err_w, Unix.stderr) ];
             Unix.execve path (Array.of_list (prog :: args)) (Array.of_list (List.map (fun (n, v) -> n ^ "=" ^ v) env))
           with e -> let m = Bytes.of_string (explain e) in ignore (Unix.write why_w m 0 (Bytes.length m)));
          Unix._exit 127
      | pid ->
          List.iter Unix.close [ in_r; out_w; err_w; why_w ];
          let pipe = Sys.signal Sys.sigpipe Sys.Signal_ignore in
          let out = Buffer.create 4096 and err = Buffer.create 256 and why = Buffer.create 64 and chunk = Bytes.create 65536 in
          let len = String.length input in
          let rec loop sent readers =
            let writers = if sent < len then [ in_w ] else [] in
            if readers <> [] || writers <> [] then begin
              let ready_r, ready_w, _ = try Unix.select readers writers [] (-1.) with Unix.Unix_error (Unix.EINTR, _, _) -> ([], [], []) in
              let sent =
                if ready_w = [] then sent
                else
                  let sent = match Unix.single_write_substring in_w input sent (len - sent) with
                    | n -> sent + n
                    | exception Unix.Unix_error ((Unix.EAGAIN | Unix.EINTR), _, _) -> sent
                    | exception Unix.Unix_error (Unix.EPIPE, _, _) -> len in
                  if sent = len then Unix.close in_w;
                  sent
              in
              let still fd =
                not (List.mem fd ready_r)
                || match Unix.read fd chunk 0 (Bytes.length chunk) with
                   | 0 -> Unix.close fd; false
                   | n -> Buffer.add_subbytes (if fd = out_r then out else if fd = err_r then err else why) chunk 0 n; true
                   | exception Unix.Unix_error (Unix.EINTR, _, _) -> true
              in
              loop sent (List.filter still readers)
            end
          in
          Unix.set_nonblock in_w;
          if len = 0 then Unix.close in_w;
          Fun.protect ~finally:(fun () -> Sys.set_signal Sys.sigpipe pipe) (fun () -> loop 0 [ out_r; err_r; why_r ]);
          match snd (Unix.waitpid [] pid) with
          | _ when Buffer.length why > 0 -> Error (prog ^ ": " ^ Buffer.contents why)
          | Unix.WEXITED code -> Ok (code, Buffer.contents out, Buffer.contents err)
          | Unix.WSIGNALED s | Unix.WSTOPPED s ->
              Error (prog ^ ": killed by signal " ^ Option.value (List.assoc_opt s signal_names) ~default:(string_of_int s)))

let host_envs () =
  List.filter_map
    (fun s -> Option.map (fun i -> (String.sub s 0 i, String.sub s (i + 1) (String.length s - i - 1))) (String.index_opt s '='))
    (Array.to_list (Unix.environment ()))

let spend w cost =
  match !(w.limit) with
  | None -> true
  | Some limit ->
      cost <= limit - !(w.used) && (w.used := !(w.used) + cost; true)
      || (let m = Printf.sprintf "runtime error: output limit exceeded: this request would bring the program's approximate output to %d bytes, over its limit of %d\n" (!(w.used) + cost) limit in w.err m 0 (String.length m); false)

let print w s = if spend w (String.length s + 1) then w.print s else w.exit 1

let make ?str_of_host ?str_to_slice ?nat_to_z ?nat_of_z o =
  let rec count z v = match o.pred v with Some p -> count (Z.succ z) p | None -> z in
  let to_z = Option.value nat_to_z ~default:(count Z.zero) in
  let u8 v = Z.to_int (to_z (o.un_u8 v)) in
  let nat n = match nat_of_z with Some f -> f (Z.of_int n) | None -> let rec go n = if n = 0 then o.zero else o.succ (go (n - 1)) in go n in
  let of_string s =
    match str_of_host with
    | Some f -> f s
    | None ->
        String.fold_right (fun ch acc -> o.scons (o.char (o.u8 (nat (Char.code ch)))) acc) s o.snil
  in
  let to_slice v =
    match str_to_slice with
    | Some f -> f v
    | None ->
        let buf = Buffer.create 64 in
        let rec go v = match o.un_str v with Some (ch, rest) -> Buffer.add_char buf (Char.chr (u8 (o.un_char ch))); go rest | None -> () in
        go v;
        (Buffer.contents buf, 0, Buffer.length buf)
  in
  let to_string v = let s, i, n = to_slice v in String.sub s i n in
  let started = lazy (Unix.gettimeofday (), Unix.times (), Gc.quick_stat (), Gc.minor_words ()) in
  let perform w req =
    let entered = Gc.minor_words () in
    let result f = match f () with x -> o.ok x | exception ((Unix.Unix_error _ | Sys_error _) as e) -> o.fail (of_string (explain e)) in
    let list of_item xs = List.fold_right (fun x acc -> o.cons (of_item x) acc) xs o.nil in
    let rec items of_item v = match o.un_list v with Some (x, rest) -> of_item x :: items of_item rest | None -> [] in
    let strs = items to_string in
    let change already f =
      match f () with
      | () -> o.ok o.changed
      | exception Unix.Unix_error (e, _, _) when already e -> o.ok o.unchanged
      | exception ((Unix.Unix_error _ | Sys_error _) as e) -> o.fail (of_string (explain e))
    in
    let created p = if Sys.file_exists p then 0 else entry_bytes in
    let fenced ?(access = Read) ?(follow = true) ?(cost = fun _ -> 0) path answer =
      let p = to_string path in
      match admits w.fence access ~follow p with
      | Ok _ -> if spend w (cost p) then answer p else raise (Halt 1)
      | Error m -> o.fail (of_string m)
    in
    let read p = result (fun () -> of_string (read_file p)) in
    let write out s = let t, i, n = to_slice s in if spend w n then (out t i n; o.unit) else raise (Halt 1) in
    let write_to flags path s = let (_, _, n) as x = to_slice s in fenced ~access:Write ~cost:(fun p -> n + created p) path (fun p -> result (fun () -> save flags p x; o.unit)) in
    match o.request req with
    | WriteOut s -> write w.out s
    | WriteErr s -> write w.err s
    | ReadLine -> (match w.read_line () with Some l -> o.some (of_string l) | None -> o.none)
    | ReadFile path -> fenced path read
    | ReadFileIn (dir, path) -> (
        match within (to_string dir) (to_string path) with
        | Ok (full, read) -> fenced (of_string full) (fun _ -> match read () with Ok s -> o.ok (of_string s) | Error m -> o.fail (of_string m))
        | Error m -> o.fail (of_string m))
    | WriteFile (path, s) -> write_to replacing path s
    | GetArgs -> list of_string w.args
    | GetEnv name -> (match w.env (to_string name) with Some v -> o.some (of_string v) | None -> o.none)
    | GetEnvs -> list (fun (n, v) -> o.pair (of_string n) (of_string v)) (List.sort compare (w.envs ()))
    | AppendFile (path, s) -> write_to [ Open_append; Open_creat; Open_wronly ] path s
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
    | MkDir path -> fenced ~access:Write ~follow:false ~cost:created path (fun p -> change (fun e -> e = Unix.EEXIST && is_dir p) (fun () -> Unix.mkdir p 0o777))
    | DeleteFile path -> fenced ~access:Write ~follow:false path (fun p -> change (fun e -> e = Unix.ENOENT) (fun () -> Unix.unlink p))
    | DeleteDir path -> fenced ~access:Write ~follow:false path (fun p -> change (fun e -> e = Unix.ENOENT) (fun () -> Unix.rmdir p))
    | ConfinePaths (reads, writes) ->
        (match confine w.fence (strs reads) (strs writes) with Ok () -> o.ok o.unit | Error m -> o.fail (of_string m))
    | ConfineOutputBytes bytes -> (
        let z = to_z bytes in
        match !(w.limit) with
        | Some limit when Option.fold ~none:true ~some:(fun n -> n > limit) (clamp z) ->
            o.fail (of_string (Printf.sprintf "%s bytes: above the current output limit of %d bytes" (Z.to_string z) limit))
        | _ -> w.limit := clamp z; o.ok o.unit)
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
        (* Start counts the words its throwaway build allocates and adds them to its reading, which is right only
           if the real build allocates the same words. Hiding the closure and its argument from the optimizer keeps
           the two calls compiled alike; without it, flambda at -O3 seemed to box a float in one call only, and a
           Start then Stop read 2 minor words (ASSUMPTIONS 215b). *)
        let measure = Sys.opaque_identity (fun extra -> reading (Gc.minor_words ()) extra) in
        if o.is_start c then begin
          let m = Gc.minor_words () in
          ignore (Sys.opaque_identity (measure (Sys.opaque_identity 0.)));
          let extra = Sys.opaque_identity (Gc.minor_words () -. m) in
          Gc.compact ();
          measure extra
        end
        else reading entered 0.
    | Exec (prog, args, env, dir, input) -> (
        let prog = to_string prog in
        let refuse why = o.fail (of_string (prog ^ ": " ^ why)) in
        if not w.exec then refuse "exec is disabled (--no-exec)"
        else if not (reaches !(w.fence) Write []) then refuse "exec needs the whole filesystem writable, which the fence does not allow"
        else
          let env = items (fun v -> let n, x = o.un_pair v in (to_string n, to_string x)) env in
          match exec prog (strs args) env (Option.map to_string (o.un_some dir)) (to_string input) with
          | Ok (code, out, err) -> o.ok (o.apply o.mk_exited [ o.u8 (nat code); of_string out; of_string err ])
          | Error m -> o.fail (of_string m)
          | exception ((Unix.Unix_error _ | Sys_error _) as e) -> o.fail (of_string (explain e)))
  in
  let run_program _w v =
    ignore (Lazy.force started);
    let rec loop v = match o.step v with Exit code -> u8 code | Continue k -> loop (o.apply k []) in
    try loop v with Halt code -> code
  in
  let run_main w f = let s, i, n = to_slice (o.apply f [ of_string (w.read_rest ()) ]) in if spend w n then w.out s i n else w.exit 1 in
  { of_string; to_string; perform; run_program; run_main }
