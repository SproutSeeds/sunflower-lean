/-
  M3(l,t): uniform, intersection-capped 3-sunflower-free maxima — definitions.

  Companion to the paper "Three-sunflower-free set systems with bounded
  pairwise intersections" and to FORMALIZATION_PLAN_M3.md (milestone M0).
  Reuses IsSunflower / IsSunflowerFree from SunflowerLean.Basic; the empty
  core is permitted there, matching the paper's convention that three
  pairwise disjoint sets form a 3-sunflower.

  Authors: Cody Mitchell, Claude (Fable)
  Date: June 2026
  Provenance: definitions only; no proofs in this file.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import SunflowerLean.Basic

namespace M3

/-- Every member of the family has exactly `l` elements. -/
def IsUniform {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (l : ℕ) : Prop :=
  ∀ S ∈ F, S.card = l

/-- Every two distinct members meet in at most `t` elements. -/
def PairwiseCapped {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (t : ℕ) : Prop :=
  ∀ S ∈ F, ∀ T ∈ F, S ≠ T → (S ∩ T).card ≤ t

/-- Every two distinct members meet (no disjoint pair). -/
def IsIntersectingFam {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Prop :=
  ∀ S ∈ F, ∀ T ∈ F, S ≠ T → (S ∩ T).Nonempty

/-- Admissible family for `M3(l,t)`: `l`-uniform, pairwise intersections of
    size at most `t`, and no 3-sunflower (empty core included). -/
def M3Admissible {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (l t : ℕ) : Prop :=
  IsUniform F l ∧ PairwiseCapped F t ∧ IsSunflowerFree F 3

/-- Admissible family for `I3(l,t)`: additionally intersecting. -/
def I3Admissible {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (l t : ℕ) : Prop :=
  M3Admissible F l t ∧ IsIntersectingFam F

end M3
