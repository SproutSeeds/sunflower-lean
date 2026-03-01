/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: e6834e36-ac9c-49ef-8cc9-241ea66eca61

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem entanglement {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (k : ℕ) (hk : k ≥ 2)
    (h_sf_free : IsSunflowerFree family k)
    (h_empty : ∅ ∈ family)
    (disjoint_sub : Finset (Finset α))
    (h_sub : disjoint_sub ⊆ family.erase ∅)
    (h_disjoint : IsPairwiseDisjoint disjoint_sub) :
    disjoint_sub.card ≤ k - 2

- theorem reduction_lemma {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (k r : ℕ) (p : α)
    (h_uniform : ∀ S ∈ family, S.card = r)
    (h_sf_free : IsSunflowerFree family k) :
    let reduced

- theorem disjoint_is_sunflower {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (k : ℕ)
    (h_card : family.card = k)
    (h_disjoint : IsPairwiseDisjoint family) :
    IsSunflower family k
-/

/-
  Sunflower Conjecture - Formal Verification
  Authors: Cody Mitchell, Claude (Opus)
  Date: January 2026

  Valid theorems from our research, formalized in Lean 4 for verification by Aristotle.
  This represents a fresh start after Thomas Bloom identified errors in our original approach.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset


-- ============================================================================
-- CORE DEFINITIONS
-- ============================================================================

/-- A k-sunflower is a collection of k sets where all pairwise intersections are equal (the core).
    This is also called a Δ-system. -/
def IsSunflower {α : Type*} [DecidableEq α] (family : Finset (Finset α)) (k : ℕ) : Prop :=
  family.card = k ∧
  ∃ core : Finset α, ∀ S T : Finset α, S ∈ family → T ∈ family → S ≠ T → S ∩ T = core

/-- A family is k-sunflower-free if it contains no k-sunflower as a subfamily -/
def IsSunflowerFree {α : Type*} [DecidableEq α] (family : Finset (Finset α)) (k : ℕ) : Prop :=
  ∀ subfamily : Finset (Finset α), subfamily ⊆ family → ¬IsSunflower subfamily k

/-- Pairwise disjoint family predicate -/
def IsPairwiseDisjoint {α : Type*} [DecidableEq α] (family : Finset (Finset α)) : Prop :=
  ∀ S T : Finset α, S ∈ family → T ∈ family → S ≠ T → S ∩ T = ∅

-- ============================================================================
-- VALID THEOREM 1: ENTANGLEMENT
-- If F is k-SF-free and ∅ ∈ F, then F \ {∅} has no k-1 pairwise disjoint sets
-- ============================================================================

/-- If ∅ is in a k-SF-free family, no k-1 other sets can be pairwise disjoint -/
theorem entanglement {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (k : ℕ) (hk : k ≥ 2)
    (h_sf_free : IsSunflowerFree family k)
    (h_empty : ∅ ∈ family)
    (disjoint_sub : Finset (Finset α))
    (h_sub : disjoint_sub ⊆ family.erase ∅)
    (h_disjoint : IsPairwiseDisjoint disjoint_sub) :
    disjoint_sub.card ≤ k - 2 := by
  -- Assume disjoint_sub has at least k-1 elements. Then, adding ∅ to disjoint_sub gives a subfamily of exactly k elements which forms a k-sunflower with ∅ as the core.
  by_contra h_contra;
  -- Since disjoint_sub has n ≥ k-1 elements, we can pick any k-1 elements from disjoint_sub.
  obtain ⟨subfamily, h_subfamily⟩ : ∃ subfamily : Finset (Finset α), subfamily ⊆ disjoint_sub ∧ subfamily.card = k - 1 := by
    exact Finset.exists_subset_card_eq ( by omega );
  refine' h_sf_free ( Insert.insert ∅ subfamily ) _ _;
  · exact Finset.insert_subset_iff.mpr ⟨ h_empty, Finset.Subset.trans h_subfamily.1 ( Finset.Subset.trans h_sub ( Finset.erase_subset _ _ ) ) ⟩;
  · refine' ⟨ _, _ ⟩;
    · rw [ Finset.card_insert_of_notMem, h_subfamily.2 ] ; omega;
      exact fun h => by have := h_subfamily.1 h; have := h_sub this; aesop;
    · use ∅; intro S T hS hT hne; aesop;

-- PROVIDED SOLUTION:
  -- Suppose for contradiction that disjoint_sub.card ≥ k - 1.
  -- Then we can take k-1 sets A₁,...,Aₖ₋₁ from disjoint_sub.
  -- Consider the subfamily {∅, A₁, ..., Aₖ₋₁}.
  -- For any i ≠ j: Aᵢ ∩ Aⱼ = ∅ (by h_disjoint)
  -- For any i: ∅ ∩ Aᵢ = ∅
  -- So all pairwise intersections equal ∅, making this a k-sunflower with core ∅.
  -- This subfamily is in family (∅ ∈ family, and each Aᵢ ∈ family.erase ∅ ⊆ family).
  -- This contradicts h_sf_free.

-- ============================================================================
-- VALID THEOREM 2: REDUCTION LEMMA
-- Removing an element preserves SF-freeness
-- ============================================================================

/-- If F is r-uniform k-SF-free, then F_p^{-p} = {S \ {p} : p ∈ S ∈ F} is (r-1)-uniform k-SF-free -/
theorem reduction_lemma {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (k r : ℕ) (p : α)
    (h_uniform : ∀ S ∈ family, S.card = r)
    (h_sf_free : IsSunflowerFree family k) :
    let reduced := (family.filter (fun S => p ∈ S)).image (fun S => S.erase p)
    IsSunflowerFree reduced k := by
  -- Assume for contradiction that there exists a k-sunflower in the reduced family.
  by_contra h_contra;
  obtain ⟨subfamily, h_subfamily⟩ : ∃ subfamily : Finset (Finset α), subfamily ⊆ Finset.image (fun S => S.erase p) (family.filter (fun S => p ∈ S)) ∧ IsSunflower subfamily k := by
    unfold IsSunflowerFree at h_contra; aesop;
  -- Let's obtain the core of the sunflower in the reduced family.
  obtain ⟨core, h_core⟩ := h_subfamily.right;
  -- Let's obtain the sets in the original family that correspond to the sets in the sunflower in the reduced family.
  obtain ⟨sets, hsets⟩ : ∃ sets : Finset (Finset α), sets.card = k ∧ subfamily = Finset.image (fun S => S.erase p) sets ∧ ∀ S ∈ sets, p ∈ S ∧ S ∈ family := by
    have h_sets : ∀ T ∈ subfamily, ∃ S ∈ family, p ∈ S ∧ S.erase p = T := by
      intro T hT; specialize h_subfamily; have := h_subfamily.1 hT; aesop;
    choose! f hf using h_sets;
    refine' ⟨ Finset.image f subfamily, _, _, _ ⟩ <;> simp_all +decide [ Finset.card_image_of_injOn ];
    · rw [ Finset.card_image_of_injOn, core ];
      intro T hT T' hT' h_eq; have := hf T hT; have := hf T' hT'; aesop;
    · grind;
  -- Let's obtain the core of the sunflower in the original family.
  obtain ⟨original_core, h_original_core⟩ : ∃ original_core : Finset α, ∀ S T : Finset α, S ∈ sets → T ∈ sets → S ≠ T → S ∩ T = original_core := by
    obtain ⟨ original_core, h_original_core ⟩ := h_core; use original_core ∪ { p } ; intro S T hS hT hne; have := h_original_core ( S.erase p ) ( T.erase p ) ; simp_all +decide ;
    specialize this _ hS rfl _ hT rfl ; simp_all +decide [ Finset.ext_iff ] ;
    grind;
  exact h_sf_free sets ( Finset.subset_iff.mpr fun S hS => hsets.2.2 S hS |>.2 ) ⟨ hsets.1, original_core, fun S T hS hT hne => h_original_core S T hS hT hne ⟩

-- PROVIDED SOLUTION:
  -- Suppose reduced contains a k-sunflower {A₁,...,Aₖ} with core K.
  -- Each Aᵢ came from some Bᵢ ∈ F with p ∈ Bᵢ and Aᵢ = Bᵢ \ {p}.
  -- Consider {B₁,...,Bₖ} ⊆ F.
  -- For i ≠ j: Bᵢ ∩ Bⱼ = (Aᵢ ∪ {p}) ∩ (Aⱼ ∪ {p}) = (Aᵢ ∩ Aⱼ) ∪ {p} = K ∪ {p}
  -- So {B₁,...,Bₖ} is a k-sunflower in F with core K ∪ {p}.
  -- This contradicts h_sf_free.

-- ============================================================================
-- BASIC SUNFLOWER LEMMA: Empty core case
-- ============================================================================

/-- A collection of k pairwise disjoint nonempty sets forms a k-sunflower with empty core -/
theorem disjoint_is_sunflower {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (k : ℕ)
    (h_card : family.card = k)
    (h_disjoint : IsPairwiseDisjoint family) :
    IsSunflower family k := by
  constructor <;> aesop