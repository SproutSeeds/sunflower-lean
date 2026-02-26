/-
  Native LRAT verification for M(n,3) upper bounds

  Uses Std.Tactic.BVDecide.LRAT.check (verified native LRAT checker) instead of
  lrat_proof (kernel term construction). This approach:
  - Compiles the LRAT checker to native code via native_decide
  - Handles much larger certificates (31MB+ for n=6)
  - Adds Lean compiler to TCB (same trust model as native_decide)

  Authors: Cody Mitchell, Claude (Opus)
  Date: February 2026
-/

import Std.Tactic.BVDecide.LRAT

open Std.Sat
open Std.Tactic.BVDecide.LRAT

-- ============================================================================
-- DIMACS CNF Parser
-- ============================================================================

/-- Parse a DIMACS CNF string into a Std.Sat.CNF Nat (0-indexed variables).
    DIMACS literal i → (i-1, true), literal -i → (i-1, false).
    The -1 shift is required because `LRAT.check` uses `CNF.convertLRAT` which
    increments all variables by 1 (to match the 1-indexed LRAT proof actions). -/
def parseDimacsCNF (s : String) : CNF Nat := Id.run do
  let mut clauses : List (CNF.Clause Nat) := []
  let mut current : List (Literal Nat) := []
  for line in s.splitOn "\n" do
    let t := line.trim
    if t.isEmpty || t.startsWith "c" || t.startsWith "p" || t.startsWith "%" then
      continue
    for tok in t.splitOn " " do
      let tok' := tok.trim
      if tok'.isEmpty then continue
      match tok'.toInt? with
      | some 0 =>
        if !current.isEmpty then
          clauses := clauses ++ [current.reverse]
          current := []
      | some i =>
        if i > 0 then
          current := (i.toNat - 1, true) :: current
        else
          current := ((-i).toNat - 1, false) :: current
      | none => pure ()
  if !current.isEmpty then
    clauses := clauses ++ [current.reverse]
  return clauses

-- ============================================================================
-- M(5,3) ≤ 12: Native LRAT verification
-- ============================================================================

/-- The DIMACS CNF for "does a 13-element 3-SF-free family on Fin 5 exist?" -/
def m5_cnf : CNF Nat := parseDimacsCNF (include_str "sat_m5_3.cnf")

/-- The LRAT proof that the CNF is UNSAT (CaDiCaL --plain mode, 290KB) -/
def m5_lrat : Array IntAction :=
  match parseLRATProof (include_str "sat_m5_3.lrat").toUTF8 with
  | .ok proof => proof
  | .error _ => #[]

/-- Native LRAT verification for n=5 -/
def m5_verified : Bool := check m5_lrat m5_cnf

/-- The LRAT checker confirms n=5 CNF is UNSAT -/
theorem m5_verified_eq_true : m5_verified = true := by native_decide

/-- The CNF encoding "13-element 3-SF-free family on Fin 5" is unsatisfiable -/
theorem m5_cnf_unsat : m5_cnf.Unsat :=
  check_sound m5_lrat m5_cnf m5_verified_eq_true

-- ============================================================================
-- M(6,3) ≤ 19: Native LRAT verification
-- ============================================================================

/-- The DIMACS CNF for "does a 20-element 3-SF-free family on Fin 6 exist?" -/
def m6_cnf : CNF Nat := parseDimacsCNF (include_str "sat_m6_3.cnf")

/-- The LRAT proof (CaDiCaL --plain, 31MB) -/
def m6_lrat : Array IntAction :=
  match parseLRATProof (include_str "sat_m6_3.lrat").toUTF8 with
  | .ok proof => proof
  | .error _ => #[]

/-- Native LRAT verification for n=6 -/
def m6_verified : Bool := check m6_lrat m6_cnf

/-- The LRAT checker confirms n=6 CNF is UNSAT -/
theorem m6_verified_eq_true : m6_verified = true := by native_decide

/-- The CNF encoding "20-element 3-SF-free family on Fin 6" is unsatisfiable -/
theorem m6_cnf_unsat : m6_cnf.Unsat :=
  check_sound m6_lrat m6_cnf m6_verified_eq_true
