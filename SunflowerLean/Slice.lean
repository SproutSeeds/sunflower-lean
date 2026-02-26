/-
  Slice (t-slice) Reduction Lemmas for 3-Sunflower-Free Families

  Key fact (size-agnostic):
    If a family F is k-sunflower-free and we restrict to the slice of sets
    containing a fixed I, then deleting I from every set preserves sunflower-freeness.

  This underlies the “t-slice hierarchy” used throughout the paper.

  Authors: Cody Mitchell, Claude (Opus)
  Date: January 2026
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.SDiff
import Mathlib.Tactic
import SunflowerLean.Basic

namespace SunflowerLean

open scoped BigOperators

/-- The I-slice of `family`, reduced by deleting `I` from each set that contains it. -/
def sliceReduce {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (I : Finset α) : Finset (Finset α) :=
  (family.filter (fun S => I ⊆ S)).image (fun S => S \ I)

/-- The (unreduced) I-slice of `family`: sets in `family` that contain `I`. -/
def slice {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (I : Finset α) : Finset (Finset α) :=
  family.filter (fun S => I ⊆ S)

lemma mem_slice_iff {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {I S : Finset α} :
    S ∈ slice family I ↔ S ∈ family ∧ I ⊆ S := by
  simp [slice]

lemma sliceReduce_eq_image_slice {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (I : Finset α) :
    sliceReduce family I = (slice family I).image (fun S => S \ I) := by
  rfl

lemma mem_sliceReduce_iff {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {I : Finset α} {T : Finset α} :
    T ∈ sliceReduce family I ↔
      ∃ S ∈ family, I ⊆ S ∧ S \ I = T := by
  constructor
  · intro hT
    rcases Finset.mem_image.mp hT with ⟨S, hS, rfl⟩
    have hSf := Finset.mem_filter.mp hS
    refine ⟨S, ?_, ?_, rfl⟩
    · exact hSf.1
    · exact hSf.2
  · rintro ⟨S, hSfam, hIS, rfl⟩
    refine Finset.mem_image.mpr ?_
    refine ⟨S, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨hSfam, hIS⟩

lemma disjoint_sliceReduce {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {I T : Finset α} :
    T ∈ sliceReduce family I → Disjoint T I := by
  intro hT
  rcases (mem_sliceReduce_iff.mp hT) with ⟨S, _hSfam, _hIS, hST⟩
  subst hST
  -- `S \ I` is disjoint from `I`.
  refine Finset.disjoint_left.2 ?_
  intro x hxSI hxI
  exact (Finset.mem_sdiff.mp hxSI).2 hxI

/--
If `family` consists of subsets of `ground`, then `sliceReduce family I`
consists of subsets of `ground \ I`.
-/
lemma sliceReduce_subset_powerset_sdiff {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground I : Finset α}
    (hground : family ⊆ ground.powerset) :
    sliceReduce family I ⊆ (ground \ I).powerset := by
  intro T hT
  rcases (mem_sliceReduce_iff (family := family) (I := I) (T := T)).1 hT with ⟨S, hSfam, _hIS, hST⟩
  subst hST
  have hSsub : S ⊆ ground := by
    exact (Finset.mem_powerset.mp (hground hSfam))
  have hTsub : S \ I ⊆ ground \ I := by
    exact Finset.sdiff_subset_sdiff hSsub (Finset.Subset.refl I)
  exact Finset.mem_powerset.mpr hTsub

lemma union_eq_of_subset {α : Type*} [DecidableEq α]
    (S I : Finset α) (hIS : I ⊆ S) :
    (S \ I) ∪ I = S := by
  ext x
  constructor
  · intro hx
    have hx' : x ∈ S \ I ∨ x ∈ I := by
      exact Finset.mem_union.mp hx
    cases hx' with
    | inl hxSI =>
        exact (Finset.mem_sdiff.mp hxSI).1
    | inr hxI =>
        exact hIS hxI
  · intro hxS
    by_cases hxI : x ∈ I
    · exact Finset.mem_union.mpr (Or.inr hxI)
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hxS, hxI⟩))

lemma union_mem_family_of_mem_sliceReduce {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {I T : Finset α} :
    T ∈ sliceReduce family I → (T ∪ I) ∈ family := by
  intro hT
  rcases (mem_sliceReduce_iff.mp hT) with ⟨S, hSfam, hIS, hST⟩
  subst hST
  -- `S \ I ∪ I = S` when `I ⊆ S`.
  simpa [union_eq_of_subset S I hIS] using hSfam

lemma union_mem_slice_of_mem_sliceReduce {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {I T : Finset α} :
    T ∈ sliceReduce family I → (T ∪ I) ∈ slice family I := by
  intro hT
  have hfam : (T ∪ I) ∈ family := union_mem_family_of_mem_sliceReduce (family := family) hT
  refine (mem_slice_iff (family := family) (I := I) (S := T ∪ I)).2 ?_
  refine ⟨hfam, ?_⟩
  intro x hxI
  exact Finset.mem_union.mpr (Or.inr hxI)

lemma mem_sliceReduce_of_mem_slice {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {I S : Finset α} :
    S ∈ slice family I → (S \ I) ∈ sliceReduce family I := by
  intro hS
  have hS' : S ∈ family ∧ I ⊆ S := (mem_slice_iff (family := family) (I := I) (S := S)).1 hS
  exact (mem_sliceReduce_iff (family := family) (I := I) (T := S \ I)).2 ⟨S, hS'.1, hS'.2, rfl⟩

lemma image_union_sliceReduce_eq_slice {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (I : Finset α) :
    (sliceReduce family I).image (fun T => T ∪ I) = slice family I := by
  ext S
  constructor
  · intro hS
    rcases Finset.mem_image.mp hS with ⟨T, hT, rfl⟩
    exact union_mem_slice_of_mem_sliceReduce (family := family) (I := I) (T := T) hT
  · intro hS
    have hT : (S \ I) ∈ sliceReduce family I :=
      mem_sliceReduce_of_mem_slice (family := family) (I := I) hS
    refine Finset.mem_image.mpr ?_
    refine ⟨S \ I, hT, ?_⟩
    have hsub : I ⊆ S := (mem_slice_iff (family := family) (I := I) (S := S)).1 hS |>.2
    exact union_eq_of_subset S I hsub

/-- Sunflower-freeness is preserved by taking a slice (filtering to sets containing `I`). -/
theorem sunflowerFree_slice {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (I : Finset α) (k : ℕ)
    (hfree : IsSunflowerFree family k) :
    IsSunflowerFree (slice family I) k := by
  intro sub hsub
  have hsub' : sub ⊆ family := by
    exact Finset.Subset.trans hsub (Finset.filter_subset _ _)
  exact hfree sub hsub'

lemma union_injective_on_sliceReduce {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (I : Finset α) :
    Set.InjOn (fun T : Finset α => T ∪ I) (sliceReduce family I) := by
  classical
  intro T1 hT1 T2 hT2 hEq
  have hdis1 : Disjoint T1 I := disjoint_sliceReduce (family := family) (I := I) (T := T1) hT1
  have hdis2 : Disjoint T2 I := disjoint_sliceReduce (family := family) (I := I) (T := T2) hT2
  -- Remove I from both sides; since T1,T2 are disjoint from I, this recovers T1=T2.
  have : (T1 ∪ I) \ I = (T2 ∪ I) \ I := by
    simp [hEq]
  -- Simplify each side using disjointness.
  have h1 : (T1 ∪ I) \ I = T1 := by
    ext x
    constructor
    · intro hx
      have hx' := Finset.mem_sdiff.mp hx
      have hxU : x ∈ T1 ∪ I := hx'.1
      have hxI : x ∉ I := hx'.2
      have : x ∈ T1 := by
        have hxU' : x ∈ T1 ∨ x ∈ I := by
          simpa [Finset.mem_union] using hxU
        cases hxU' with
        | inl hxT1 => exact hxT1
        | inr hxI' => exact False.elim (hxI hxI')
      exact this
    · intro hxT1
      have hxI : x ∉ I := by
        intro hxI
        have : x ∈ (⊥ : Finset α) := hdis1.le_bot (Finset.mem_inter.mpr ⟨hxT1, hxI⟩)
        simp at this
      refine Finset.mem_sdiff.mpr ?_
      exact ⟨by simpa [Finset.mem_union] using Or.inl hxT1, hxI⟩
  have h2 : (T2 ∪ I) \ I = T2 := by
    ext x
    constructor
    · intro hx
      have hx' := Finset.mem_sdiff.mp hx
      have hxU : x ∈ T2 ∪ I := hx'.1
      have hxI : x ∉ I := hx'.2
      have : x ∈ T2 := by
        have hxU' : x ∈ T2 ∨ x ∈ I := by
          simpa [Finset.mem_union] using hxU
        cases hxU' with
        | inl hxT2 => exact hxT2
        | inr hxI' => exact False.elim (hxI hxI')
      exact this
    · intro hxT2
      have hxI : x ∉ I := by
        intro hxI
        have : x ∈ (⊥ : Finset α) := hdis2.le_bot (Finset.mem_inter.mpr ⟨hxT2, hxI⟩)
        simp at this
      refine Finset.mem_sdiff.mpr ?_
      exact ⟨by simpa [Finset.mem_union] using Or.inl hxT2, hxI⟩
  -- Finish.
  simpa [h1, h2] using this

lemma card_sliceReduce_eq_card_slice {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (I : Finset α) :
    (sliceReduce family I).card = (slice family I).card := by
  classical
  have hinj : Set.InjOn (fun T : Finset α => T ∪ I) (sliceReduce family I) :=
    union_injective_on_sliceReduce family I
  have himg : (sliceReduce family I).image (fun T : Finset α => T ∪ I) = slice family I :=
    image_union_sliceReduce_eq_slice family I
  calc
    (sliceReduce family I).card =
        ((sliceReduce family I).image (fun T : Finset α => T ∪ I)).card := by
      simpa using
        (Finset.card_image_of_injOn (s := sliceReduce family I) (f := fun T => T ∪ I) hinj).symm
    _ = (slice family I).card := by simp [himg]

lemma inter_union_of_disjoint {α : Type*} [DecidableEq α]
    (S T I : Finset α) (_hSI : Disjoint S I) (_hTI : Disjoint T I) :
    (S ∪ I) ∩ (T ∪ I) = (S ∩ T) ∪ I := by
  ext x
  constructor
  · intro hx
    have hx' : x ∈ S ∪ I ∧ x ∈ T ∪ I := by
      simpa [Finset.mem_inter] using hx
    rcases hx' with ⟨hxSI', hxTI'⟩
    have hxSI'' : x ∈ S ∨ x ∈ I := by simpa [Finset.mem_union] using hxSI'
    have hxTI'' : x ∈ T ∨ x ∈ I := by simpa [Finset.mem_union] using hxTI'
    cases hxSI'' with
    | inl hxS =>
        cases hxTI'' with
        | inl hxT =>
            exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hxS, hxT⟩))
        | inr hxI =>
            exact Finset.mem_union.mpr (Or.inr hxI)
    | inr hxI =>
        exact Finset.mem_union.mpr (Or.inr hxI)
  · intro hx
    have hx' : x ∈ S ∩ T ∨ x ∈ I := by simpa [Finset.mem_union] using hx
    cases hx' with
    | inl hxST =>
        have hxS : x ∈ S := (Finset.mem_inter.mp hxST).1
        have hxT : x ∈ T := (Finset.mem_inter.mp hxST).2
        refine Finset.mem_inter.mpr ?_
        constructor
        · exact Finset.mem_union.mpr (Or.inl hxS)
        · exact Finset.mem_union.mpr (Or.inl hxT)
    | inr hxI =>
        refine Finset.mem_inter.mpr ?_
        constructor
        · exact Finset.mem_union.mpr (Or.inr hxI)
        · exact Finset.mem_union.mpr (Or.inr hxI)

/-- Sunflower-freeness is preserved by `sliceReduce`. -/
theorem sunflowerFree_sliceReduce {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (I : Finset α) (k : ℕ)
    (hfree : IsSunflowerFree family k) :
    IsSunflowerFree (sliceReduce family I) k := by
  classical
  intro sub hsub
  -- Consider the lifted subfamily: union I into every set.
  let lift : Finset (Finset α) := sub.image (fun T => T ∪ I)
  have hlift_sub : lift ⊆ family := by
    intro U hU
    rcases Finset.mem_image.mp hU with ⟨T, hTsub, rfl⟩
    have hT_slice : T ∈ sliceReduce family I := hsub hTsub
    exact union_mem_family_of_mem_sliceReduce (family := family) (I := I) (T := T) hT_slice
  -- If sub is a k-sunflower, then lift is a k-sunflower, contradiction.
  intro hsun
  rcases hsun with ⟨hcard, core, hcore⟩
  have hinj : Set.InjOn (fun T : Finset α => T ∪ I) sub := by
    intro T1 hT1 T2 hT2 hEq
    have hT1' : T1 ∈ sliceReduce family I := hsub hT1
    have hT2' : T2 ∈ sliceReduce family I := hsub hT2
    exact (union_injective_on_sliceReduce family I) hT1' hT2' hEq
  have hlift_card : lift.card = k := by
    -- card(image)=card for injective image
    have : lift.card = sub.card := by
      simpa [lift] using Finset.card_image_of_injOn (s := sub) (f := fun T => T ∪ I) hinj
    simpa [hcard] using this
  have hlift_sun : IsSunflower lift k := by
    refine ⟨hlift_card, ?_⟩
    refine ⟨core ∪ I, ?_⟩
    intro S T hS hT hne
    rcases Finset.mem_image.mp hS with ⟨S0, hS0, rfl⟩
    rcases Finset.mem_image.mp hT with ⟨T0, hT0, rfl⟩
    have hne0 : S0 ≠ T0 := by
      intro hEq
      exact hne (by simp [hEq])
    have hS0_slice : S0 ∈ sliceReduce family I := hsub hS0
    have hT0_slice : T0 ∈ sliceReduce family I := hsub hT0
    have hS0I : Disjoint S0 I :=
      disjoint_sliceReduce (family := family) (I := I) (T := S0) hS0_slice
    have hT0I : Disjoint T0 I :=
      disjoint_sliceReduce (family := family) (I := I) (T := T0) hT0_slice
    -- Use sunflower property in `sub` and disjointness to compute intersections in `lift`.
    have hST_core : S0 ∩ T0 = core := hcore S0 T0 hS0 hT0 hne0
    calc
      (S0 ∪ I) ∩ (T0 ∪ I) = (S0 ∩ T0) ∪ I := inter_union_of_disjoint S0 T0 I hS0I hT0I
      _ = core ∪ I := by simp [hST_core]
  exact (hfree lift hlift_sub) hlift_sun

/--
The maximum size of a k-sunflower-free family on `ground`, defined by a finite max over
`ground.powerset.powerset`.
-/
noncomputable def maxSunflowerFreeCard {α : Type*} [DecidableEq α]
    (ground : Finset α) (k : ℕ) : ℕ := by
  classical
  exact (ground.powerset.powerset.filter (fun F : Finset (Finset α) => IsSunflowerFree F k)).sup
    Finset.card

theorem card_le_maxSunflowerFreeCard {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {k : ℕ}
    (hground : family ⊆ ground.powerset) (hfree : IsSunflowerFree family k) :
    family.card ≤ maxSunflowerFreeCard ground k := by
  classical
  unfold maxSunflowerFreeCard
  have hmem_pow : family ∈ ground.powerset.powerset := by
    exact Finset.mem_powerset.mpr hground
  have hmem :
      family ∈
        ground.powerset.powerset.filter (fun F : Finset (Finset α) => IsSunflowerFree F k) := by
    exact Finset.mem_filter.mpr ⟨hmem_pow, hfree⟩
  exact
    Finset.le_sup
      (s := ground.powerset.powerset.filter (fun F : Finset (Finset α) => IsSunflowerFree F k))
      (f := Finset.card) hmem

theorem card_slice_le_maxSunflowerFreeCard_sdiff {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground I : Finset α} {k : ℕ}
    (hground : family ⊆ ground.powerset) (hfree : IsSunflowerFree family k) :
    (slice family I).card ≤ maxSunflowerFreeCard (ground \ I) k := by
  classical
  have hsub :
      sliceReduce family I ⊆ (ground \ I).powerset :=
    sliceReduce_subset_powerset_sdiff (family := family) (ground := ground) (I := I) hground
  have hfree' : IsSunflowerFree (sliceReduce family I) k :=
    sunflowerFree_sliceReduce family I k hfree
  have hcard :
      (sliceReduce family I).card ≤ maxSunflowerFreeCard (ground \ I) k :=
    card_le_maxSunflowerFreeCard (family := sliceReduce family I)
      (ground := ground \ I) (k := k) hsub hfree'
  have hEq : (slice family I).card = (sliceReduce family I).card :=
    (card_sliceReduce_eq_card_slice family I).symm
  calc
    (slice family I).card = (sliceReduce family I).card := hEq
    _ ≤ maxSunflowerFreeCard (ground \ I) k := hcard

theorem card_sliceReduce_le_maxSunflowerFreeCard_sdiff {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground I : Finset α} {k : ℕ}
    (hground : family ⊆ ground.powerset) (hfree : IsSunflowerFree family k) :
    (sliceReduce family I).card ≤ maxSunflowerFreeCard (ground \ I) k := by
  classical
  have hsub :
      sliceReduce family I ⊆ (ground \ I).powerset :=
    sliceReduce_subset_powerset_sdiff (family := family) (ground := ground) (I := I) hground
  have hfree' : IsSunflowerFree (sliceReduce family I) k :=
    sunflowerFree_sliceReduce family I k hfree
  exact card_le_maxSunflowerFreeCard (family := sliceReduce family I)
    (ground := ground \ I) (k := k) hsub hfree'

/-
Paper notation correspondence:
- Paper: `F_I = {S \\ I : S ∈ F, I ⊆ S}`. Lean: `tSlice family I` (= `sliceReduce family I`).
- Paper: `c_{ij} = |F_{ij}|`. Lean: `coDegree family i j`.
- Paper: `M(n-t,3)` is modeled as `maxSunflowerFreeCard (ground \\ I) k`.
-/

/-- The reduced t-slice used in the paper: delete `I` from all sets containing `I`. -/
abbrev tSlice {α : Type*} [DecidableEq α] (family : Finset (Finset α)) (I : Finset α) :
    Finset (Finset α) :=
  sliceReduce family I

/-- Pair-slice: the reduced slice at `{i,j}`. -/
abbrev pairSlice {α : Type*} [DecidableEq α] (family : Finset (Finset α)) (i j : α) :
    Finset (Finset α) :=
  sliceReduce family ({i, j} : Finset α)

/-- Co-degree: size of the pair-slice at `{i,j}`. -/
def coDegree {α : Type*} [DecidableEq α] (family : Finset (Finset α)) (i j : α) : ℕ :=
  (pairSlice family i j).card

theorem coDegree_comm {α : Type*} [DecidableEq α] (family : Finset (Finset α)) (i j : α) :
    coDegree family i j = coDegree family j i := by
  classical
  unfold coDegree pairSlice
  have hpair : ({i, j} : Finset α) = ({j, i} : Finset α) := by
    ext x
    simp [or_comm]
  simp [hpair]

theorem coDegree_le_maxSunflowerFreeCard_sdiff {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {k : ℕ} {i j : α}
    (hground : family ⊆ ground.powerset) (hfree : IsSunflowerFree family k) :
    coDegree family i j ≤ maxSunflowerFreeCard (ground \ ({i, j} : Finset α)) k := by
  classical
  unfold coDegree
  simpa [pairSlice] using
    (card_sliceReduce_le_maxSunflowerFreeCard_sdiff
      (family := family) (ground := ground) (I := ({i, j} : Finset α)) (k := k) hground hfree)

end SunflowerLean
