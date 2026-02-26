/-
  SAT-based Upper Bounds for M(n, 3)

  Uses LRAT certificates from CaDiCaL to verify that certain
  SAT formulas are unsatisfiable, proving upper bounds on the
  maximum size of 3-sunflower-free families.

  Two independent verification pipelines:

  Pipeline A (PySAT encoding → external LRAT):
  1. Python (analysis/sat_upper_bound.py) generates DIMACS CNF encoding
  2. CaDiCaL proves UNSAT and outputs LRAT certificate
  3. Lean verifies via lrat_proof (n=5 kernel) or LRAT.check (n=6 native)

  Pipeline B (Lean-generated encoding → self-contained, sorry-free):
  1. Lean computes sunflowerCNF n B directly (SATBridge.lean)
  2. Python (analysis/generate_lean_cnf.py) reproduces exact same CNF
  3. CaDiCaL proves UNSAT on exported DIMACS
  4. LRAT.check verifies via native_decide
  5. Bridge theorem connects UNSAT to math (sorry-free since SATBridge.lean)

  Pipeline B is sorry-free for n=5 and n=6. The bridge theorems in
  SATBridge.lean have been fully verified (0 sorry's).

  Authors: Cody Mitchell, Claude (Opus)
  Date: February 2026
-/

import SunflowerLean.SATBridge
import Mathlib.Tactic.Sat.FromLRAT

namespace SunflowerLean

-- ==========================================================================
-- LRAT Certificate Verification: M(5, 3) (PySAT pipeline)
-- ==========================================================================
-- This is Pipeline A: PySAT-generated CNF verified at the kernel level.
-- Certificate: 290KB, 3663 lines, verified in ~17s

lrat_proof sat_m5_3_unsat
  (include_str "sat_m5_3.cnf")
  (include_str "sat_m5_3.lrat")

-- ==========================================================================
-- Upper Bound Theorems
-- ==========================================================================

/-- M(5,3) ≤ 12: No 13-element 3-sunflower-free family on Fin 5 exists.
    Sorry-free: LRAT verified via native_decide, bridge fully proved. -/
theorem M_5_3_upper : ∀ F : Finset (Finset (Fin 5)),
    IsSunflowerFree F 3 → F.card ≤ 12 :=
  M_5_3_upper_bridge

/-- M(6,3) ≤ 19: No 20-element 3-sunflower-free family on Fin 6 exists.
    Sorry-free: 26MB LRAT verified via native_decide, bridge fully proved. -/
theorem M_6_3_upper : ∀ F : Finset (Finset (Fin 6)),
    IsSunflowerFree F 3 → F.card ≤ 19 :=
  M_6_3_upper_bridge

/-- M(7,3) ≤ 29: No 30-element 3-sunflower-free family on Fin 7 exists.
    CaDiCaL proves sunflowerCNF 7 30 UNSAT (139.4M conflicts, 13458s).
    drat-trim VERIFIED the 9.1GB DRAT proof (61.7M/138.2M lemmas in core).
    Trimmed LRAT: 29GB — exceeds include_str capacity (~30MB practical limit).
    The bridge theorem and encoding in SATBridge.lean are sorry-free;
    only this LRAT size constraint prevents full Lean-level verification.
    Cube-and-conquer tested (k=4..16, first-k and least-constrained variable
    selection): hardest cubes still produce 300MB-8GB LRAT each, because setting
    variables FALSE satisfies (rather than constrains) sunflower exclusion clauses.
    Future: streaming LRAT checker or compressed proof format in Lean. -/
theorem M_7_3_upper : ∀ F : Finset (Finset (Fin 7)),
    IsSunflowerFree F 3 → F.card ≤ 29 := by
  sorry -- LRAT verified externally (drat-trim: 29GB, VERIFIED) but too large for include_str

-- ==========================================================================
-- Exact Values (combining lower bounds from SmallCases with upper bounds)
-- ==========================================================================

/-- M(5,3) = 12: formally verified exact value (sorry-free).
    Lower bound: witness family (native_decide in SmallCases.lean).
    Upper bound: SAT+LRAT + bridge (fully proved in SATBridge.lean). -/
theorem M_5_3 : ∃ F : Finset (Finset (Fin 5)),
    IsSunflowerFree F 3 ∧ F.card = 12 ∧
    ∀ G : Finset (Finset (Fin 5)), IsSunflowerFree G 3 → G.card ≤ 12 :=
  ⟨witness_5_3, witness_5_3_sf_free, witness_5_3_card, M_5_3_upper⟩

/-- M(6,3) = 19: formally verified exact value (sorry-free). -/
theorem M_6_3 : ∃ F : Finset (Finset (Fin 6)),
    IsSunflowerFree F 3 ∧ F.card = 19 ∧
    ∀ G : Finset (Finset (Fin 6)), IsSunflowerFree G 3 → G.card ≤ 19 :=
  ⟨witness_6_3, witness_6_3_sf_free, witness_6_3_card, M_6_3_upper⟩

/-- M(7,3) = 29: exact value (upper bound has 1 sorry due to LRAT size). -/
theorem M_7_3 : ∃ F : Finset (Finset (Fin 7)),
    IsSunflowerFree F 3 ∧ F.card = 29 ∧
    ∀ G : Finset (Finset (Fin 7)), IsSunflowerFree G 3 → G.card ≤ 29 :=
  ⟨witness_7_3, witness_7_3_sf_free, witness_7_3_card, M_7_3_upper⟩

end SunflowerLean
