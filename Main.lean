import Lantern.Explore

open Lean Lantern

def main (args : List String) : IO UInt32 := do
  let stdout ← IO.getStdout
  match args with
  | ["--explore"] =>
    stdout.putStrLn ((explore .baseline 2 6 50000).compress)
  | ["--mutants"] =>
    -- A single identifier per domain suffices to expose all three guard failures.
    stdout.putStrLn ((toJson ([Variant.unsupported, .incomplete, .duplicate].map
      fun v => explore v 1 6 50000)).compress)
  | [] =>
    let stdin ← IO.getStdin
    let input ← stdin.readToEnd
    let result := match Json.parse input with
      | .error err => malformed err
      | .ok j => runWire j
    stdout.putStrLn result.compress
  | _ =>
    (← IO.getStderr).putStrLn "usage: oracle [--explore|--mutants]"
    return 2
  return 0
