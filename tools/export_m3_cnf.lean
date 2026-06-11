import SunflowerLean.M3.SATEncoding
open M3 Std.Sat

def clauseToDimacs (cl : CNF.Clause Nat) : String :=
  String.intercalate " "
    (cl.map (fun (l : Nat × Bool) =>
      if l.2 then s!"{l.1 + 1}" else s!"-{l.1 + 1}")) ++ " 0"

def maxVar (cnf : CNF Nat) : Nat :=
  cnf.foldl (fun acc cl => cl.foldl (fun a l => max a l.1) acc) 0

def export1 (name : String) (cnf : CNF Nat) : IO Unit := do
  let h ← IO.FS.Handle.mk name IO.FS.Mode.write
  h.putStrLn s!"p cnf {maxVar cnf + 1} {cnf.length}"
  for cl in cnf do
    h.putStrLn (clauseToDimacs cl)
  IO.println s!"{name}: {maxVar cnf + 1} vars {cnf.length} clauses"

def main : IO Unit := do
  export1 "/tmp/m3_7_2_1_7.cnf" (m3CNF 7 2 1 7)
  export1 "/tmp/m3_7_3_2_21.cnf" (m3CNF 7 3 2 21)
  export1 "/tmp/m3_7_3_2_20.cnf" (m3CNF 7 3 2 20)
