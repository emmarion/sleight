import Minimal.Run

def main (args : List String) : IO UInt32 := do
  let (flags, files) := args.partition (·.startsWith "--")
  let mode := (flags.filter fun f => f != "--no-prelude" && f != "--shared").headD ""
  let groups := if flags.contains "--shared" then [files] else files.map ([·])
  for fs in groups do
    let f := fs.getLastD ""
    let (ws, out) := Minimal.runSources (← fs.mapM fun (f : String) => IO.FS.readFile f) mode (!flags.contains "--no-prelude")
    for w in ws do IO.eprintln s!"{f}: warning: {w}"
    match out with
    | .text s => IO.println s!"{f}: {s}"
    | .io k =>
      let input ← (← IO.getStdin).readBinToEnd
      match k (input.toList.map (·.toNat)) with
      | .ok bs => (← IO.getStdout).write (ByteArray.mk (bs.map (·.toUInt8)).toArray)
      | .error e => IO.println s!"{f}: {e}"
  return 0
