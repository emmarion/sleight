import Minimal.Run

def main (args : List String) : IO UInt32 := do
  let (checked, files) := match args with
    | "--unchecked" :: fs => (false, fs)
    | fs => (true, fs)
  for f in files do
    IO.println s!"{f}: {Minimal.runSource (← IO.FS.readFile f) checked}"
  return 0
