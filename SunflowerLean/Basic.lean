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
import Mathlib.Tactic

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
  by_contra h_contra
  obtain ⟨subfamily, h_subfamily⟩ :
      ∃ subfamily : Finset (Finset α), subfamily ⊆ disjoint_sub ∧ subfamily.card = k - 1 := by
    exact Finset.exists_subset_card_eq (by omega)
  refine h_sf_free (insert ∅ subfamily) ?_ ?_
  · exact Finset.insert_subset_iff.mpr ⟨h_empty,
      Finset.Subset.trans h_subfamily.1
        (Finset.Subset.trans h_sub (Finset.erase_subset _ _))⟩
  · refine ⟨?_, ?_⟩
    · rw [Finset.card_insert_of_notMem, h_subfamily.2]
      · omega
      · intro h
        have := h_subfamily.1 h
        have := h_sub this
        aesop
    · refine ⟨∅, ?_⟩
      intro S T hS hT hne
      have hS' : S = ∅ ∨ S ∈ subfamily := by
        exact (Finset.mem_insert.mp hS)
      have hT' : T = ∅ ∨ T ∈ subfamily := by
        exact (Finset.mem_insert.mp hT)
      cases hS' with
      | inl hS0 =>
          cases hT' with
          | inl hT0 =>
              exact False.elim (hne (by simp [hS0, hT0]))
          | inr hTmem =>
              simp [hS0]
      | inr hSmem =>
          cases hT' with
          | inl hT0 =>
              simp [hT0]
          | inr hTmem =>
              exact h_disjoint S T (h_subfamily.1 hSmem) (h_subfamily.1 hTmem) hne
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
    (_h_uniform : ∀ S ∈ family, S.card = r)
    (h_sf_free : IsSunflowerFree family k) :
    let reduced := (family.filter (fun S => p ∈ S)).image (fun S => S.erase p)
    IsSunflowerFree reduced k := by
  by_contra h_contra
  obtain ⟨subfamily, h_subfamily⟩ :
      ∃ subfamily : Finset (Finset α),
        subfamily ⊆ (family.filter (fun S => p ∈ S)).image (fun S => S.erase p) ∧
          IsSunflower subfamily k := by
    unfold IsSunflowerFree at h_contra
    aesop
  obtain ⟨core, h_core⟩ := h_subfamily.right
  obtain ⟨sets, hsets⟩ :
      ∃ sets : Finset (Finset α),
        sets.card = k ∧
          subfamily = Finset.image (fun S => S.erase p) sets ∧
            ∀ S ∈ sets, p ∈ S ∧ S ∈ family := by
    have h_sets :
        ∀ T ∈ subfamily, ∃ S ∈ family, p ∈ S ∧ S.erase p = T := by
      intro T hT
      have := h_subfamily.1 hT
      aesop
    choose! f hf using h_sets
    refine ⟨Finset.image f subfamily, ?_, ?_, ?_⟩
    · have h_inj : Set.InjOn f subfamily := by
        intro T hT T' hT' h_eq
        have := hf T hT
        have := hf T' hT'
        aesop
      calc
        (Finset.image f subfamily).card = subfamily.card := by
          simpa using
            (Finset.card_image_of_injOn (s := subfamily) (f := f) h_inj)
        _ = k := core
    · ext T
      constructor
      · intro hT
        refine Finset.mem_image.mpr ?_
        refine ⟨f T, ?_, ?_⟩
        · exact Finset.mem_image.mpr ⟨T, hT, rfl⟩
        · exact (hf T hT).2.2
      · intro hT
        rcases Finset.mem_image.mp hT with ⟨S, hS, hST⟩
        rcases Finset.mem_image.mp hS with ⟨T', hT', hT'S⟩
        have h_erase : (f T').erase p = T := by
          simpa [hT'S] using hST
        have h_eq : T = T' := by
          exact h_erase.symm.trans (hf T' hT').2.2
        simpa [h_eq] using hT'
    · intro S hS
      rcases Finset.mem_image.mp hS with ⟨T, hT, rfl⟩
      exact ⟨(hf T hT).2.1, (hf T hT).1⟩
  obtain ⟨original_core, h_original_core⟩ :
      ∃ original_core : Finset α,
        ∀ S T : Finset α, S ∈ sets → T ∈ sets → S ≠ T → S ∩ T = original_core := by
    obtain ⟨original_core, h_original_core⟩ := h_core
    refine ⟨original_core ∪ {p}, ?_⟩
    intro S T hS hT hne
    have := h_original_core (S.erase p) (T.erase p)
    simp_all +decide
    specialize this _ hS rfl _ hT rfl
    simp_all +decide [Finset.ext_iff]
    grind
  refine h_sf_free sets ?_ ?_
  · exact Finset.subset_iff.mpr fun S hS => (hsets.2.2 S hS).2
  · exact ⟨hsets.1, original_core, fun S T hS hT hne => h_original_core S T hS hT hne⟩
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
  refine ⟨h_card, ?_⟩
  refine ⟨∅, ?_⟩
  intro S T hS hT hne
  exact h_disjoint S T hS hT hne

-- ============================================================================
-- CRITICAL INSIGHT: WHY OUR PROOF FAILED
-- Matching number and piercing number are fundamentally different.
-- ============================================================================

/-
  THE ERROR IN LEMMA 4.2:

  We claimed: If ν(F) ≤ k-2, then τ(F) ≤ k-1.
  (Small matching number implies small piercing number)

  THIS IS FALSE.

  Matching number ν(F) = max size of pairwise disjoint subfamily
  Piercing number τ(F) = min size of transversal (hitting set)

  These are LP duals, but the relationship is:
    ν(F) ≤ τ(F)  (always)
    τ(F) ≤ r · ν(F)  (for r-uniform families, by greedy)

  But there is NO bound τ(F) ≤ f(ν(F)) independent of r.

  Thomas Bloom: "This definitely cannot work, since your upper bound is independent of r.
  It is known that it has to grow exponentially in r."
-/

-- ============================================================================
-- THE SUNFLOWER CONJECTURE (OPEN PROBLEM)
-- ============================================================================

/-
  Conjecture (Erdős-Rado, 1960):
  There exists C(k) depending only on k such that any family of more than C(k)^r
  sets of size r contains a k-sunflower.

  Current best bound: C(k) ≤ O(k log k · log(k log k)) by Alweiss-Lovett-Wu-Zhang (2021)
  Erdős offered $1000 for a proof that C(k) = O(k).

  THIS REMAINS OPEN. Our attempted proof (claiming C(k) = (k-1)²) was WRONG.

  Known computational values for k=3:
  m(1,3)=2, m(2,3)=4, m(3,3)=6, m(4,3)=9, m(5,3)=13, m(6,3)=20
  Growth rate approximately 1.55^n
-/
