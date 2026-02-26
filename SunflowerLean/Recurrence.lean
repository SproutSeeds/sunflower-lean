/-
  Recurrence Infrastructure (Lane B2)

  This file contains Lean-friendly lemmas about splitting a family `F ⊆ P(ground)`
  into coordinate slices and relating the resulting cardinalities.

  These are “mechanics” lemmas used to state recurrence-type bounds without committing
  to a particular obstruction taxonomy yet.

  Authors: Cody Mitchell, Claude (Opus)
  Date: January 2026
-/

import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import SunflowerLean.Basic
import SunflowerLean.LocalTuran
import SunflowerLean.Slice

namespace SunflowerLean

open scoped BigOperators

/-- The i=0 slice: sets in `family` avoiding `i`. -/
def sliceAvoid {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (i : α) : Finset (Finset α) :=
  family.filter (fun S => i ∉ S)

lemma mem_sliceAvoid_iff {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {i : α} {S : Finset α} :
    S ∈ sliceAvoid family i ↔ S ∈ family ∧ i ∉ S := by
  simp [sliceAvoid]

/-- `sliceAvoid` is a subfamily, hence sunflower-freeness is inherited. -/
theorem sunflowerFree_sliceAvoid {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (i : α) (k : ℕ)
    (hfree : IsSunflowerFree family k) :
    IsSunflowerFree (sliceAvoid family i) k := by
  intro sub hsub
  have hsub' : sub ⊆ family := by
    exact Finset.Subset.trans hsub (Finset.filter_subset _ _)
  exact hfree sub hsub'

/-- The singleton slice `slice family {i}` is exactly the membership filter `i ∈ S`. -/
lemma slice_singleton_eq_filter_mem {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (i : α) :
    slice family ({i} : Finset α) = family.filter (fun S => i ∈ S) := by
  ext S
  simp [slice, Finset.singleton_subset_iff]

/-- For a singleton index, the reduced slice has cardinality `coordDegree`. -/
theorem card_sliceReduce_singleton_eq_coordDegree {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (i : α) :
    (sliceReduce family ({i} : Finset α)).card = coordDegree family i := by
  classical
  calc
    (sliceReduce family ({i} : Finset α)).card = (slice family ({i} : Finset α)).card := by
      simpa using card_sliceReduce_eq_card_slice family ({i} : Finset α)
    _ = (family.filter (fun S => i ∈ S)).card := by
      simp [slice_singleton_eq_filter_mem]
    _ = coordDegree family i := rfl

/-- Partition a family into `i ∈ S` and `i ∉ S`. -/
theorem card_filter_mem_add_card_sliceAvoid_eq_card {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (i : α) :
    (family.filter (fun S => i ∈ S)).card + (sliceAvoid family i).card = family.card := by
  classical
  -- Use Mathlib's filter-card partition lemma.
  simpa [sliceAvoid] using
    (Finset.filter_card_add_filter_neg_card_eq_card (s := family) (p := fun S : Finset α => i ∈ S))

/-- The reduced `i`-slice plus the avoiding slice recovers the family size. -/
theorem card_sliceReduce_add_card_sliceAvoid_eq_card {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (i : α) :
    (sliceReduce family ({i} : Finset α)).card + (sliceAvoid family i).card = family.card := by
  classical
  -- Replace `sliceReduce.card` with `coordDegree`, then use the partition lemma.
  have hdeg : (sliceReduce family ({i} : Finset α)).card = coordDegree family i :=
    card_sliceReduce_singleton_eq_coordDegree family i
  -- `coordDegree` is the card of the `i ∈ S` filter.
  have hpart :=
    card_filter_mem_add_card_sliceAvoid_eq_card (family := family) (i := i)
  -- Rewrite the left summand.
  simpa [coordDegree, hdeg] using hpart

/--
One-step recurrence bound (“Type I” mechanics):

For any coordinate `i`, the `i=1` slice (after deleting `{i}`) is a 3-sunflower-free family
on `ground \ {i}`, hence has size at most `maxSunflowerFreeCard (ground \ {i}) k`.
Therefore the full family size is bounded by that maximum plus the `i=0` slice size.
-/
theorem card_le_maxSunflowerFreeCard_sdiff_add_sliceAvoid {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {k : ℕ} {i : α}
    (hground : family ⊆ ground.powerset) (hfree : IsSunflowerFree family k) :
    family.card ≤
      maxSunflowerFreeCard (ground \ ({i} : Finset α)) k + (sliceAvoid family i).card := by
  classical
  have hslice :
      (sliceReduce family ({i} : Finset α)).card ≤
        maxSunflowerFreeCard (ground \ ({i} : Finset α)) k := by
    simpa using
      (card_sliceReduce_le_maxSunflowerFreeCard_sdiff
        (family := family) (ground := ground) (I := ({i} : Finset α)) (k := k) hground hfree)
  have hpart :
      (sliceReduce family ({i} : Finset α)).card + (sliceAvoid family i).card = family.card :=
    card_sliceReduce_add_card_sliceAvoid_eq_card (family := family) (i := i)
  calc
    family.card =
        (sliceReduce family ({i} : Finset α)).card + (sliceAvoid family i).card := by
          simpa using hpart.symm
    _ ≤ maxSunflowerFreeCard (ground \ ({i} : Finset α)) k + (sliceAvoid family i).card :=
          Nat.add_le_add_right hslice _

end SunflowerLean
