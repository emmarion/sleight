import Minimal.Run

def main (args : List String) : IO UInt32 := do
  let (mode, files) := match args with
    | m :: fs => if m.startsWith "--" then (m, fs) else ("", args)
    | [] => ("", [])
  for f in files do
    IO.println s!"{f}: {Minimal.runSource (← IO.FS.readFile f) mode}"
  return 0
