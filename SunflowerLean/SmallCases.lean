/-
  Small Cases: Formal verification of M(n,3) exact values

  Goal: Formally prove M(n,3) for n = 1, 2, 3, ..., 7
  by exhibiting witness families (lower bounds) and proving
  upper bounds via brute-force decidability (small n) or abstract machinery (larger n).

  Convention: M(n,3) = max size of a 3-sunflower-free family of subsets of (Fin n).
  This is the WEAK/NON-UNIFORM formulation (sets may have different sizes, ∅ included).

  NOTE: Our Lean-verified values may differ from some literature conventions that
  restrict to nonempty sets or uniform families. The formalization IS the ground truth.

  Authors: Cody Mitchell, Claude (Opus)
  Date: February 2026
-/

import SunflowerLean.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

namespace SunflowerLean

-- ============================================================================
-- n = 1: M(1,3) = 2  (under our non-uniform definition including ∅)
-- Ground set: Fin 1 = {0}
-- Subsets: ∅, {0}  (only 2 subsets total)
-- Any family of ≤ 2 sets is trivially 3-SF-free (need 3 sets for a 3-sunflower)
-- So M(1,3) = 2 = total number of subsets
-- ============================================================================

/-- Witness: all subsets of Fin 1 -/
def witness_1_3 : Finset (Finset (Fin 1)) := {∅, {0}}

theorem witness_1_3_card : witness_1_3.card = 2 := by native_decide

theorem witness_1_3_sf_free : IsSunflowerFree witness_1_3 3 := by
  unfold IsSunflowerFree IsSunflower
  decide

theorem M_1_3_upper : ∀ F : Finset (Finset (Fin 1)),
    IsSunflowerFree F 3 → F.card ≤ 2 := by
  unfold IsSunflowerFree IsSunflower
  decide

/-- M(1,3) = 2: formally verified exact value -/
theorem M_1_3 : ∃ F : Finset (Finset (Fin 1)),
    IsSunflowerFree F 3 ∧ F.card = 2 ∧
    ∀ G : Finset (Finset (Fin 1)), IsSunflowerFree G 3 → G.card ≤ 2 :=
  ⟨witness_1_3, witness_1_3_sf_free, witness_1_3_card, M_1_3_upper⟩

-- ============================================================================
-- n = 2: M(2,3) = 3
-- Ground set: Fin 2 = {0, 1}
-- Subsets: ∅, {0}, {1}, {0,1}  (4 subsets, 16 possible families)
-- Full set {∅,{0},{1},{0,1}} contains sunflower {∅,{0},{1}} (core ∅)
-- Witness: {∅, {0}, {0,1}} — pairwise intersections ∅, ∅, {0} → not all equal
-- ============================================================================

/-- Witness: 3-element SF-free family on Fin 2 -/
def witness_2_3 : Finset (Finset (Fin 2)) :=
  {(∅ : Finset (Fin 2)), ({0} : Finset (Fin 2)), ({0, 1} : Finset (Fin 2))}

theorem witness_2_3_card : witness_2_3.card = 3 := by native_decide

theorem witness_2_3_sf_free : IsSunflowerFree witness_2_3 3 := by
  unfold IsSunflowerFree IsSunflower
  decide

theorem M_2_3_upper : ∀ F : Finset (Finset (Fin 2)),
    IsSunflowerFree F 3 → F.card ≤ 3 := by
  unfold IsSunflowerFree IsSunflower
  decide

/-- M(2,3) = 3: formally verified exact value -/
theorem M_2_3 : ∃ F : Finset (Finset (Fin 2)),
    IsSunflowerFree F 3 ∧ F.card = 3 ∧
    ∀ G : Finset (Finset (Fin 2)), IsSunflowerFree G 3 → G.card ≤ 3 :=
  ⟨witness_2_3, witness_2_3_sf_free, witness_2_3_card, M_2_3_upper⟩

-- ============================================================================
-- n = 3: M(3,3) = 5
-- Ground set: Fin 3 = {0, 1, 2}
-- 8 subsets, 256 possible families
-- Witness: {∅, {0,1}, {0,2}, {1,2}, {0,1,2}}
--   All triples involving ∅: ∅∩X=∅, ∅∩Y=∅, X∩Y≠∅ (2-element sets overlap) → not SF
--   Without ∅: {0,1}∩{0,2}={0}, {0,1}∩{1,2}={1}, {0,2}∩{1,2}={2} → all different
-- ============================================================================

/-- Witness: 5-element SF-free family on Fin 3 -/
def witness_3_3 : Finset (Finset (Fin 3)) :=
  {(∅ : Finset (Fin 3)),
   ({0, 1} : Finset (Fin 3)),
   ({0, 2} : Finset (Fin 3)),
   ({1, 2} : Finset (Fin 3)),
   ({0, 1, 2} : Finset (Fin 3))}

theorem witness_3_3_card : witness_3_3.card = 5 := by native_decide

theorem witness_3_3_sf_free : IsSunflowerFree witness_3_3 3 := by
  unfold IsSunflowerFree IsSunflower
  decide

-- n=3 upper bound: 256 families to check. Try native_decide for speed.
set_option maxRecDepth 1000 in
theorem M_3_3_upper : ∀ F : Finset (Finset (Fin 3)),
    IsSunflowerFree F 3 → F.card ≤ 5 := by
  unfold IsSunflowerFree IsSunflower
  native_decide

/-- M(3,3) = 5: formally verified exact value -/
theorem M_3_3 : ∃ F : Finset (Finset (Fin 3)),
    IsSunflowerFree F 3 ∧ F.card = 5 ∧
    ∀ G : Finset (Finset (Fin 3)), IsSunflowerFree G 3 → G.card ≤ 5 :=
  ⟨witness_3_3, witness_3_3_sf_free, witness_3_3_card, M_3_3_upper⟩

-- ============================================================================
-- n = 4: M(4,3) = 8
-- Ground set: Fin 4 = {0,1,2,3}
-- 16 subsets, 65536 possible families
-- Witness (from exhaustive search):
--   {∅, {1,2}, {0,1,2}, {1,3}, {0,1,3}, {2,3}, {0,2,3}, {0,1,2,3}}
-- ============================================================================

/-- Witness: 8-element SF-free family on Fin 4 -/
def witness_4_3 : Finset (Finset (Fin 4)) :=
  {(∅ : Finset (Fin 4)),
   ({1, 2} : Finset (Fin 4)),
   ({0, 1, 2} : Finset (Fin 4)),
   ({1, 3} : Finset (Fin 4)),
   ({0, 1, 3} : Finset (Fin 4)),
   ({2, 3} : Finset (Fin 4)),
   ({0, 2, 3} : Finset (Fin 4)),
   ({0, 1, 2, 3} : Finset (Fin 4))}

theorem witness_4_3_card : witness_4_3.card = 8 := by native_decide

theorem witness_4_3_sf_free : IsSunflowerFree witness_4_3 3 := by
  unfold IsSunflowerFree IsSunflower
  native_decide

-- n=4 upper bound: 65536 families. native_decide compiles to native code.
theorem M_4_3_upper : ∀ F : Finset (Finset (Fin 4)),
    IsSunflowerFree F 3 → F.card ≤ 8 := by
  unfold IsSunflowerFree IsSunflower
  native_decide

/-- M(4,3) = 8: formally verified exact value -/
theorem M_4_3 : ∃ F : Finset (Finset (Fin 4)),
    IsSunflowerFree F 3 ∧ F.card = 8 ∧
    ∀ G : Finset (Finset (Fin 4)), IsSunflowerFree G 3 → G.card ≤ 8 :=
  ⟨witness_4_3, witness_4_3_sf_free, witness_4_3_card, M_4_3_upper⟩

-- ============================================================================
-- EFFICIENT DECIDABILITY FOR n ≥ 5
-- ============================================================================
-- For n ≥ 5, the default IsSunflower check uses ∃ core : Finset α, which
-- needs Fintype (Finset α) to enumerate all 2^n possible cores.
-- For n = 7, that's 128 cores × all pairs — too slow for native_decide.
--
-- IsSunflowerC: existential-free reformulation using 4 bounded quantifiers.
-- Checks "all pairwise intersections agree" directly (no core search).
-- Decidability uses only Finset.decidableBAll — no Fintype needed.
--
-- For a 29-element family (n=7, k=3):
--   C(29,3) = 3654 subfamilies × 81 tuples per check ≈ 33K effective operations.
--   Compiles and runs in seconds.

/-- Existential-free sunflower: card = k and all pairwise intersections are equal.
    Equivalent to IsSunflower but decidable without Fintype enumeration. -/
def IsSunflowerC {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (k : ℕ) : Prop :=
  family.card = k ∧
  ∀ S ∈ family, ∀ T ∈ family, ∀ U ∈ family, ∀ V ∈ family,
    S ≠ T → U ≠ V → S ∩ T = U ∩ V

/-- Efficient SF-free check using existential-free sunflower detection. -/
def IsSFreeC {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (k : ℕ) : Prop :=
  ∀ subfamily ∈ family.powersetCard k, ¬IsSunflowerC subfamily k

-- Decidable instances: NO [Fintype α] needed!
instance instDecidableIsSunflowerC {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (k : ℕ) : Decidable (IsSunflowerC family k) := by
  unfold IsSunflowerC
  exact inferInstance

instance instDecidableIsSFreeC {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (k : ℕ) : Decidable (IsSFreeC family k) := by
  unfold IsSFreeC
  exact inferInstance

theorem isSunflowerC_iff {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (k : ℕ) :
    IsSunflowerC family k ↔ IsSunflower family k := by
  constructor
  · intro ⟨hcard, hpairs⟩
    refine ⟨hcard, ?_⟩
    by_cases h2 : k < 2
    · exact ⟨∅, fun S T hS hT hne => by
        exfalso
        have := Finset.one_lt_card.mpr ⟨S, hS, T, hT, hne⟩
        omega⟩
    · push_neg at h2
      obtain ⟨S₀, hS₀, T₀, hT₀, hne₀⟩ := Finset.one_lt_card.mp (by omega : 1 < family.card)
      exact ⟨S₀ ∩ T₀, fun S T hS hT hne =>
        hpairs S hS T hT S₀ hS₀ T₀ hT₀ hne hne₀⟩
  · intro ⟨hcard, core, hcore⟩
    exact ⟨hcard, fun S hS T hT U hU V hV hST hUV =>
      (hcore S T hS hT hST).trans (hcore U V hU hV hUV).symm⟩

theorem isSFreeC_iff {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (k : ℕ) :
    IsSFreeC family k ↔ IsSunflowerFree family k := by
  constructor
  · intro h sub hsub hsf
    have hmem := Finset.mem_powersetCard.mpr ⟨hsub, hsf.1⟩
    exact h sub hmem ((isSunflowerC_iff sub k).mpr hsf)
  · intro h sub hmem
    have ⟨hsub, _⟩ := Finset.mem_powersetCard.mp hmem
    intro hsf
    exact h sub hsub ((isSunflowerC_iff sub k).mp hsf)

-- ============================================================================
-- BITMASK DECODER
-- For n ≥ 6, Finset literals are too deep for the elaborator.
-- Encode families as lists of bitmask Nats and decode computationally.
-- ============================================================================

/-- Decode a bitmask into a Finset (Fin n): bit i set means i is in the set. -/
def decodeBitmask (n : Nat) (mask : Nat) : Finset (Fin n) :=
  (Finset.univ.filter fun i => (mask >>> i.val) &&& 1 = 1)

/-- Decode a list of bitmasks into a family (Finset of Finsets). -/
def decodeFamily (n : Nat) (masks : List Nat) : Finset (Finset (Fin n)) :=
  (masks.map (decodeBitmask n)).toFinset

-- ============================================================================
-- n = 5: M(5,3) = 12
-- Ground set: Fin 5 = {0,1,2,3,4}
-- 32 subsets, 2^32 ≈ 4 billion possible families
-- Lower bound: witness verified via IsSFreeC + native_decide
-- Upper bound: 2^32 families — infeasible for brute-force, needs abstract machinery
-- ============================================================================

/-- Witness: 12-element SF-free family on Fin 5 -/
def witness_5_3 : Finset (Finset (Fin 5)) :=
  {(∅ : Finset (Fin 5)),
   ({0, 1} : Finset (Fin 5)),
   ({0, 2, 3} : Finset (Fin 5)),
   ({1, 2, 3} : Finset (Fin 5)),
   ({0, 1, 2, 3} : Finset (Fin 5)),
   ({0, 2, 4} : Finset (Fin 5)),
   ({1, 2, 4} : Finset (Fin 5)),
   ({0, 1, 2, 4} : Finset (Fin 5)),
   ({0, 3, 4} : Finset (Fin 5)),
   ({1, 3, 4} : Finset (Fin 5)),
   ({0, 1, 3, 4} : Finset (Fin 5)),
   ({0, 1, 2, 3, 4} : Finset (Fin 5))}

theorem witness_5_3_card : witness_5_3.card = 12 := by native_decide

theorem witness_5_3_sf_free : IsSunflowerFree witness_5_3 3 :=
  (isSFreeC_iff witness_5_3 3).mp (by native_decide)

theorem M_5_3_lower : ∃ F : Finset (Finset (Fin 5)),
    IsSunflowerFree F 3 ∧ F.card = 12 :=
  ⟨witness_5_3, witness_5_3_sf_free, witness_5_3_card⟩

-- ============================================================================
-- n = 6: M(6,3) ≥ 19
-- Witness from backtracking search (analysis/gen_witness_sat.py)
-- ============================================================================

/-- Witness: 19-element SF-free family on Fin 6 -/
def witness_6_3 : Finset (Finset (Fin 6)) :=
  decodeFamily 6 [0, 3, 7, 25, 26, 29, 30, 31, 41, 42, 45, 46, 47, 49, 50, 53, 54, 55, 63]

theorem witness_6_3_card : witness_6_3.card = 19 := by native_decide

theorem witness_6_3_sf_free : IsSunflowerFree witness_6_3 3 :=
  (isSFreeC_iff witness_6_3 3).mp (by native_decide)

theorem M_6_3_lower : ∃ F : Finset (Finset (Fin 6)),
    IsSunflowerFree F 3 ∧ F.card = 19 :=
  ⟨witness_6_3, witness_6_3_sf_free, witness_6_3_card⟩

-- ============================================================================
-- n = 7: M(7,3) ≥ 29
-- Witness from SAT-certified data/result_m_7_3.json
-- ============================================================================

/-- Witness: 29-element SF-free family on Fin 7 -/
def witness_7_3 : Finset (Finset (Fin 7)) :=
  decodeFamily 7 [2, 14, 21, 25, 30, 39, 43, 55, 59, 63, 71, 75, 76, 80,
    87, 91, 92, 95, 101, 102, 105, 106, 117, 118, 121, 122, 125, 126, 127]

theorem witness_7_3_card : witness_7_3.card = 29 := by native_decide

theorem witness_7_3_sf_free : IsSunflowerFree witness_7_3 3 :=
  (isSFreeC_iff witness_7_3 3).mp (by native_decide)

theorem M_7_3_lower : ∃ F : Finset (Finset (Fin 7)),
    IsSunflowerFree F 3 ∧ F.card = 29 :=
  ⟨witness_7_3, witness_7_3_sf_free, witness_7_3_card⟩

-- ============================================================================
-- SUMMARY
-- ============================================================================
/-
  Formally verified results (Lean kernel-checked):

  EXACT VALUES (both directions):
    M(1,3) = 2    (brute-force upper bound via decide)
    M(2,3) = 3    (brute-force upper bound via decide)
    M(3,3) = 5    (brute-force upper bound via native_decide)
    M(4,3) = 8    (brute-force upper bound via native_decide)

  LOWER BOUNDS (witness verified, upper bound pending):
    M(5,3) ≥ 12   (upper bound infeasible: 2^32 families)
    M(6,3) ≥ 19   (upper bound needs abstract machinery or SAT bridge)
    M(7,3) ≥ 29   (upper bound needs abstract machinery or SAT bridge)

  Convention: non-uniform formulation, ∅ included.
  M(1,3) = 2 differs from some literature (M=1) due to ∅ convention.

  Key technical innovation: IsSunflowerC (existential-free sunflower check)
  eliminates the need for Fintype (Finset α) enumeration, enabling
  native_decide on families with ground sets up to Fin 7 in seconds.
-/

end SunflowerLean
