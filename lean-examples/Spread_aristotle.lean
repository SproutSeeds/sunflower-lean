/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 09471f98-5a92-4b4f-9012-d731f4c283c4

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem spread_singleton {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (r : ℕ)
    (h_spread : IsRSpread family r) (x : α) :
    (family.filter (fun S => x ∈ S)).card * r ≤ family.card

- theorem not_spread_implies_heavy_subset {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (r : ℕ)
    (hr : r > 0) (hne : family.Nonempty)
    (h_not_spread : ¬IsRSpread family r) :
    ∃ Z : Finset α, (family.filter (fun S => Z ⊆ S)).card * r ^ Z.card > family.card
-/

/-
  Spread Families - The Key Concept from ALWZ

  A family is r-spread if no subset is "too common".
  This is THE breakthrough insight that enabled modern sunflower bounds.

  Authors: Cody Mitchell, Claude (Opus)
  Date: January 2026
  Reference: Rao's "Sunflowers: from Soil to Oil" Section 6
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card


-- ============================================================================
-- THE SPREAD DEFINITION
-- ============================================================================

/-- A family S is r-spread if for any set Z, the probability that a uniform
    random element U of S contains Z is at most r^{-|Z|}.

    Formally: |{S ∈ family : Z ⊆ S}| · r^|Z| ≤ |family| for all Z.

    This means no subset is "too popular" in the family.
-/
def IsRSpread {α : Type*} [DecidableEq α] (family : Finset (Finset α)) (r : ℕ) : Prop :=
  r > 0 ∧ family.Nonempty ∧
  ∀ Z : Finset α, (family.filter (fun S => Z ⊆ S)).card * r ^ Z.card ≤ family.card

-- ============================================================================
-- BASIC PROPERTIES OF SPREAD FAMILIES
-- ============================================================================

/-- Empty set is always contained, giving trivial bound for Z = ∅ -/
theorem spread_empty_trivial {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (r : ℕ) (hr : r > 0) (hne : family.Nonempty) :
    (family.filter (fun S => ∅ ⊆ S)).card = family.card := by
  simp [Finset.filter_true_of_mem]

/-- If family is r-spread and Z has size 1, at most family.card/r sets contain Z -/
theorem spread_singleton {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (r : ℕ)
    (h_spread : IsRSpread family r) (x : α) :
    (family.filter (fun S => x ∈ S)).card * r ≤ family.card := by
  have := h_spread.2.2 { x } ; aesop

-- PROVIDED SOLUTION:
  -- Use h_spread.2.2 {x}, then simplify {x}.card = 1 and r^1 = r

-- ============================================================================
-- WHY SPREAD MATTERS: THE REDUCTION
-- ============================================================================

/-- If a family is NOT r-spread, there exists a "heavy" subset Z such that
    the subfamily {S ∈ family : Z ⊆ S} has size > family.card / r^|Z|.

    This lets us recurse: delete Z from all sets and find sunflower in smaller family.
-/
theorem not_spread_implies_heavy_subset {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (r : ℕ)
    (hr : r > 0) (hne : family.Nonempty)
    (h_not_spread : ¬IsRSpread family r) :
    ∃ Z : Finset α, (family.filter (fun S => Z ⊆ S)).card * r ^ Z.card > family.card := by
  contrapose! h_not_spread; ( unfold IsRSpread at *; aesop; )