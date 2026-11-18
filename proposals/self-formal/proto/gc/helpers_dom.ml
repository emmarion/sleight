let stop = Atomic.make false
let n = try int_of_string (Sys.getenv "NDOM") with _ -> 3
let work () =
  let r = ref [] and k = ref 0 in
  while not (Atomic.get stop) do
    incr k;
    r := Array.make (1 + !k land 63) !k :: (if !k land 1023 = 0 then [] else !r);
    if !k land 65535 = 0 then ignore (Gc.major_slice 0)
  done
let ds = List.init n (fun _ -> Domain.spawn work)
let () = at_exit (fun () -> Atomic.set stop true; List.iter Domain.join ds)
