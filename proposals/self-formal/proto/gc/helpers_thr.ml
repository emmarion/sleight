let stop = ref false
let n = try int_of_string (Sys.getenv "NTHR") with _ -> 3
let work () =
  let r = ref [] and k = ref 0 in
  while not !stop do
    incr k;
    r := Array.make (1 + !k land 63) !k :: (if !k land 1023 = 0 then [] else !r);
    if !k land 4095 = 0 then Thread.yield ()
  done
let ts = List.init n (fun _ -> Thread.create work ())
let () = at_exit (fun () -> stop := true; List.iter Thread.join ts)
