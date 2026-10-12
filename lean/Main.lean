import Minimal.Run

def main (args : List String) : IO UInt32 := do
  let (flags, files) := args.partition (·.startsWith "--")
  let mode := (flags.filter (· != "--no-prelude")).headD ""
  for f in files do
    IO.println s!"{f}: {Minimal.runSource (← IO.FS.readFile f) mode (!flags.contains "--no-prelude")}"
  return 0
