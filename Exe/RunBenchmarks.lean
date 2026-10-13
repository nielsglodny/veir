import Veir
import Veir.Panic

def count := 50_000

def getCountFrom (c : Option String) :=
  match c with
  | none => count
  | some s =>
    match s.toNat? with
    | none => count
    | some n => n

def getPCFrom (c : Option String) :=
  match c with
  | none => 100
  | some s =>
    match s.toNat? with
    | none => 100
    | some n => n

def main (args : List String) : IO Unit := do
  Veir.enableExitOnPanic
  IO.println s!"Benchmark ({args})"
  let count := getCountFrom args[1]?
  if let some bench := args[0]? then
    Veir.Benchmarks.runBenchmark bench count (getPCFrom args[2]?)
  else
    IO.eprintln "Please provide a benchmark name"
    IO.Process.exit 2
