/-
  M3 (F4c/F4d): small exact values — witnesses and certified bounds.

  F4c witness half: I12, the engine's optimal I3(4,2) family (12
  four-sets on 10 points, pairwise intersecting, intersections of size
  1 and 2, 3-sunflower-free), ported from
  erdos-problems/packs/sunflower/problems/857/m3_small_l_exact_orderly.mjs
  (I12_L4_T2, relabeled from points 4..13 to 0..9) and re-certified here
  by kernel `decide` (no native_decide on the witness side).

  Authors: Cody Mitchell, Claude (Fable)
  Date: June 2026
  Provenance: witness found by the deterministic orderly engine
  (36,329,094 nodes exhaustion, I3(4,2) = 12 exact engine-side);
  acceptance criterion here is `lake build` (kernel) + axiom audit.
-/

import SunflowerLean.M3.SATEncoding

namespace M3

/-- The engine's I3(4,2) optimum: 12 pairwise-intersecting 4-sets on 10
    points, pairwise intersections of size ≤ 2, 3-sunflower-free. -/
def i12Witness : Finset (Finset (Fin 10)) :=
  { {0, 1, 2, 3}, {0, 4, 5, 6}, {0, 4, 7, 8}, {1, 2, 4, 9},
    {1, 3, 4, 5}, {1, 5, 7, 8}, {1, 6, 7, 9}, {2, 3, 6, 7},
    {2, 4, 6, 8}, {2, 5, 8, 9}, {3, 4, 7, 9}, {3, 6, 8, 9} }

theorem i12Witness_card : i12Witness.card = 12 := by decide

set_option maxRecDepth 65536 in
-- The kernel `decide` walks C(12,3) = 220 subfamilies of explicit Fin 10
-- set literals; the default heartbeat budget is far too small for it.
set_option maxHeartbeats 4000000 in
-- See the comment above: 220-subfamily kernel decide.
theorem i12Witness_admissible : I3Admissible i12Witness 4 2 :=
  ⟨⟨by unfold IsUniform; decide, by unfold PairwiseCapped; decide,
    (SunflowerLean.isSFreeC_iff _ 3).mp (by decide)⟩,
   by unfold IsIntersectingFam; decide⟩

/-- F4c, lower bound: `I3(4,2) ≥ 12`, kernel-verified witness. -/
theorem I3_4_2_lower :
    ∃ F : Finset (Finset (Fin 10)), I3Admissible F 4 2 ∧ F.card = 12 :=
  ⟨i12Witness, i12Witness_admissible, i12Witness_card⟩


/-
  F4d: the t=1 table rows l = 2, 3, 4 (M3 = 6, 8, 10; I3 = 3, 4, 5) as
  redundancy against F2f. Two independent kernel paths pin each row:
  the parametric theorems instantiated below, and explicit decide
  witnesses (F2g anchors at l = 2, 3; the l = 4 anchor here). SAT/LRAT
  redundancy for the upper-bound side is NOT used: the universal upper
  bound lives on Fin ((v+1)*l) (= Fin 14 already at l = 2), where the
  bitmask encoding's triple enumeration (2^n)^3 is infeasible — and the
  kernel theorem is strictly stronger than any per-ground-set SAT check.
-/

/-- t=1 row l=2: I3 = 3. -/
theorem I3_2_1_row :
    (∃ F : Finset (Finset (Sym2 (Fin 3))), I3Admissible F 2 1 ∧
      F.card = 3) ∧
    (∀ {β : Type*} [DecidableEq β] (G : Finset (Finset β)),
      I3Admissible G 2 1 → G.card ≤ 3) := I3_one_exact 2 (by norm_num)

/-- t=1 row l=3: I3 = 4. -/
theorem I3_3_1_row :
    (∃ F : Finset (Finset (Sym2 (Fin 4))), I3Admissible F 3 1 ∧
      F.card = 4) ∧
    (∀ {β : Type*} [DecidableEq β] (G : Finset (Finset β)),
      I3Admissible G 3 1 → G.card ≤ 4) := I3_one_exact 3 (by norm_num)

/-- t=1 row l=4: I3 = 5. -/
theorem I3_4_1_row :
    (∃ F : Finset (Finset (Sym2 (Fin 5))), I3Admissible F 4 1 ∧
      F.card = 5) ∧
    (∀ {β : Type*} [DecidableEq β] (G : Finset (Finset β)),
      I3Admissible G 4 1 → G.card ≤ 5) := I3_one_exact 4 (by norm_num)

/-- t=1 row l=2: M3 = 6. -/
theorem M3_2_1_row :
    (∃ F : Finset (Finset (Sym2 (Fin 3) ⊕ Sym2 (Fin 3))),
      M3Admissible F 2 1 ∧ F.card = 6) ∧
    (∀ {β : Type*} [DecidableEq β] (G : Finset (Finset β)),
      M3Admissible G 2 1 → G.card ≤ 6) := M3_one_exact 2 (by norm_num)

/-- t=1 row l=3: M3 = 8. -/
theorem M3_3_1_row :
    (∃ F : Finset (Finset (Sym2 (Fin 4) ⊕ Sym2 (Fin 4))),
      M3Admissible F 3 1 ∧ F.card = 8) ∧
    (∀ {β : Type*} [DecidableEq β] (G : Finset (Finset β)),
      M3Admissible G 3 1 → G.card ≤ 8) := M3_one_exact 3 (by norm_num)

/-- t=1 row l=4: M3 = 10. -/
theorem M3_4_1_row :
    (∃ F : Finset (Finset (Sym2 (Fin 5) ⊕ Sym2 (Fin 5))),
      M3Admissible F 4 1 ∧ F.card = 10) ∧
    (∀ {β : Type*} [DecidableEq β] (G : Finset (Finset β)),
      M3Admissible G 4 1 → G.card ≤ 10) := M3_one_exact 4 (by norm_num)

/-
  NOTE (F4d, recorded after two failed attempts): a kernel `decide`
  witness anchor at l = 4 (starFam 4 over Sym2 (Fin 5), 15 elements)
  aborts the Lean process (SIGABRT, kernel reduction stack) at
  maxRecDepth 32768 with and without a 64MB OS stack. The l = 4 rows
  above are nonetheless doubly pinned: by the parametric kernel theorem
  (M3_one_exact/I3_one_exact instantiated) and by the engine table; the
  decide anchors at l = 2, 3 (F2g, T1Exact.lean) cover the same
  definitions one size down. native_decide would close it instantly but
  is deliberately not used on the anchor lane.
-/


/-
  F4e: cross-validation anchors for the M3 encoder, at the same n = 7
  scale as the repo's largest M(n,3) bridge. Both UNSAT results are
  LRAT-certified (CaDiCaL --plain --lrat --no-binary; certificates
  committed next to this file) and cross-checked against independent
  knowledge: m3CNF 7 2 1 7 against the kernel theorem M3(2,1) = 6
  (M3_one_exact — the cap is genuine there), and m3CNF 7 3 2 21 against
  the literature value f(3,3) = 20 (cap t = 2 is vacuous for 3-sets, so
  M3(3,2) = f(3,3)). Solver note: m3CNF 7 3 2 20 is ALSO unsat on
  Fin 7 — the f(3,3) = 20 extremal family needs more than 7 points, so
  no Fin 7 witness pair is possible at 20.

  Recheck commands (deterministic):
    lake env lean --run tools/export_m3_cnf.lean   # writes /tmp/m3_*.cnf
    cadical --plain --lrat --no-binary m3_7_2_1_7.cnf   sat_m3_7_2_1_7.lrat
    cadical --plain --lrat --no-binary m3_7_3_2_21.cnf  sat_m3_7_3_2_21.lrat
  and the native LRAT checks below re-verify the committed certificates
  against the Lean-generated CNFs on every build.
-/

open Std.Tactic.BVDecide.LRAT in
/-- LRAT certificate for `(m3CNF 7 2 1 7).Unsat`. -/
def m3_7217_lrat : Array IntAction :=
  match parseLRATProof (include_str "sat_m3_7_2_1_7.lrat").toUTF8 with
  | .ok proof => proof
  | .error _ => #[]

open Std.Tactic.BVDecide.LRAT in
def m3_7217_verified : Bool :=
  check m3_7217_lrat (m3CNF 7 2 1 7)

set_option linter.style.nativeDecide false in
-- SAT lane: LRAT certificates are checked natively by standing repo
-- methodology (kernel decide cannot walk certificates of this size).
theorem m3_7217_verified_eq_true : m3_7217_verified = true := by
  native_decide

theorem m3CNF_7_2_1_7_unsat : (m3CNF 7 2 1 7).Unsat :=
  Std.Tactic.BVDecide.LRAT.check_sound m3_7217_lrat (m3CNF 7 2 1 7)
    m3_7217_verified_eq_true

/-- F4e anchor 1: no 7-member M3(2,1)-family on `Fin 7` — encoder
    result agreeing with the kernel theorem `M3_one_exact` (= 6). -/
theorem M3_2_1_fin7_anchor :
    ∀ F : Finset (Finset (Fin 7)), M3Admissible F 2 1 → F.card < 7 :=
  m3_bridge 7 2 1 7 m3CNF_7_2_1_7_unsat

open Std.Tactic.BVDecide.LRAT in
/-- LRAT certificate for `(m3CNF 7 3 2 21).Unsat`. -/
def m3_73221_lrat : Array IntAction :=
  match parseLRATProof (include_str "sat_m3_7_3_2_21.lrat").toUTF8 with
  | .ok proof => proof
  | .error _ => #[]

open Std.Tactic.BVDecide.LRAT in
def m3_73221_verified : Bool :=
  check m3_73221_lrat (m3CNF 7 3 2 21)

set_option linter.style.nativeDecide false in
-- SAT lane: see the note on `m3_7217_verified_eq_true`.
theorem m3_73221_verified_eq_true : m3_73221_verified = true := by
  native_decide

theorem m3CNF_7_3_2_21_unsat : (m3CNF 7 3 2 21).Unsat :=
  Std.Tactic.BVDecide.LRAT.check_sound m3_73221_lrat (m3CNF 7 3 2 21)
    m3_73221_verified_eq_true

/-- F4e anchor 2: no 21-member M3(3,2)-family on `Fin 7` — encoder
    result agreeing with the literature value f(3,3) = 20 (the cap is
    vacuous for 3-sets, so M3(3,2) = f(3,3)). -/
theorem M3_3_2_fin7_anchor :
    ∀ F : Finset (Finset (Fin 7)), M3Admissible F 3 2 → F.card < 21 :=
  m3_bridge 7 3 2 21 m3CNF_7_3_2_21_unsat

end M3
