import Minimal.Run

def main (args : List String) : IO UInt32 := do
  let (flags, files) := args.partition (·.startsWith "--")
  let mode := (flags.filter (· != "--no-prelude")).headD ""
  for f in files do
    let (ws, out) := Minimal.runSource (← IO.FS.readFile f) mode (!flags.contains "--no-prelude")
    for w in ws do IO.eprintln s!"{f}: warning: {w}"
    IO.println s!"{f}: {out}"
  return 0
