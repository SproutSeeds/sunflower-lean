/-
  Local Turan Inequality for Sunflower-Free Families

  This file formalizes a key combinatorial inequality that constrains the structure
  of 3-sunflower-free families. The insight is that sunflower-freeness is a LOCAL
  constraint: three sets form a 3-sunflower iff there exists a coordinate where
  exactly 2 of them contain that coordinate.

  Authors: Cody Mitchell, Claude (Opus)
  Date: January 2026
  Reference: Original research on Erdos Problem #857
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import SunflowerLean.Basic

open scoped BigOperators

-- ============================================================================
-- COORDINATE DEGREE AND BLOCKING CAPACITY
-- ============================================================================

/-- The coordinate degree d_i is the number of sets in the family that contain element i.
    For a family F over ground set U, d_i = |{S in F : i in S}|. -/
def coordDegree {α : Type*} [DecidableEq α] (family : Finset (Finset α)) (i : α) : ℕ :=
  (family.filter (fun S => i ∈ S)).card

/-- The blocking capacity at coordinate i counts the number of (pair, singleton) combinations
    where the pair consists of sets containing i and the singleton is a set not containing i.
    This equals C(d_i, 2) * (m - d_i) where d_i is the coordinate degree and m = |F|.

    Intuition: A triple (A, B, C) is blocked from being a 3-sunflower at coordinate i if
    exactly 2 of them contain i. The number of such configurations at i is the blocking capacity. -/
def blockingCapacity {α : Type*} [DecidableEq α] (family : Finset (Finset α)) (i : α) : ℕ :=
  let d := coordDegree family i
  let m := family.card
  Nat.choose d 2 * (m - d)

/-- Total blocking capacity is the sum of blocking capacities over all coordinates.
    This represents the total "budget" for blocking potential sunflowers. -/
def totalBlockingCapacity {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) : ℕ :=
  ground.sum (fun i => blockingCapacity family i)

-- ============================================================================
-- TRIPLES AND SUNFLOWER CHARACTERIZATION
-- ============================================================================

/-- A triple of distinct sets from the family -/
def IsTripleFrom {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (A B C : Finset α) : Prop :=
  A ∈ family ∧ B ∈ family ∧ C ∈ family ∧ A ≠ B ∧ B ≠ C ∧ A ≠ C

/-- A triple is blocked at coordinate i if exactly 2 of the 3 sets contain i.
    This is equivalent to the sum v_A[i] + v_B[i] + v_C[i] = 2 where v_S[i] = 1 iff i in S. -/
def IsBlockedAt {α : Type*} [DecidableEq α] (A B C : Finset α) (i : α) : Prop :=
  let count := (if i ∈ A then 1 else 0) + (if i ∈ B then 1 else 0) + (if i ∈ C then 1 else 0)
  count = 2

/-- Key characterization: Three sets form a 3-sunflower iff they are NOT blocked at any coordinate.
    Equivalently: (A, B, C) is a 3-sunflower <=> for all i, count(i in {A,B,C}) != 2. -/
def IsThreeSunflower {α : Type*} [DecidableEq α]
    (A B C : Finset α) (ground : Finset α) : Prop :=
  ∀ i ∈ ground, ¬IsBlockedAt A B C i

-- ============================================================================
-- HELPER LEMMAS
-- ============================================================================

/-- The coordinate characterization of 3-sunflowers relates to our core definition. -/
theorem three_sunflower_iff_not_blocked {α : Type*} [DecidableEq α]
    (A B C : Finset α) (_h_ne_AB : A ≠ B) (_h_ne_BC : B ≠ C) (_h_ne_AC : A ≠ C)
    (ground : Finset α) (h_A : A ⊆ ground) (h_B : B ⊆ ground) (_h_C : C ⊆ ground) :
    (∃ core : Finset α, A ∩ B = core ∧ B ∩ C = core ∧ A ∩ C = core) ↔
    IsThreeSunflower A B C ground := by
  constructor
  · rintro ⟨core, hAB, hBC, hAC⟩ i _
    by_cases hAi : i ∈ A
    · by_cases hBi : i ∈ B
      · by_cases hCi : i ∈ C
        · simp [IsBlockedAt, hAi, hBi, hCi]
        · intro _hblocked
          have h_inAB : i ∈ A ∩ B := by
            exact Finset.mem_inter.mpr ⟨hAi, hBi⟩
          have h_in_core : i ∈ core := by
            simpa [hAB] using h_inAB
          have h_inAC : i ∈ A ∩ C := by
            rw [← hAC] at h_in_core
            exact h_in_core
          have hCi' : i ∈ C := (Finset.mem_inter.mp h_inAC).2
          exact hCi hCi'
      · by_cases hCi : i ∈ C
        · intro _hblocked
          have h_inAC : i ∈ A ∩ C := by
            exact Finset.mem_inter.mpr ⟨hAi, hCi⟩
          have h_in_core : i ∈ core := by
            simpa [hAC] using h_inAC
          have h_inAB : i ∈ A ∩ B := by
            rw [← hAB] at h_in_core
            exact h_in_core
          have hBi' : i ∈ B := (Finset.mem_inter.mp h_inAB).2
          exact hBi hBi'
        · simp [IsBlockedAt, hAi, hBi, hCi]
    · by_cases hBi : i ∈ B
      · by_cases hCi : i ∈ C
        · intro _hblocked
          have h_inBC : i ∈ B ∩ C := by
            exact Finset.mem_inter.mpr ⟨hBi, hCi⟩
          have h_in_core : i ∈ core := by
            simpa [hBC] using h_inBC
          have h_inAB : i ∈ A ∩ B := by
            rw [← hAB] at h_in_core
            exact h_in_core
          have hAi' : i ∈ A := (Finset.mem_inter.mp h_inAB).1
          exact hAi hAi'
        · simp [IsBlockedAt, hAi, hBi, hCi]
      · by_cases hCi : i ∈ C
        · simp [IsBlockedAt, hAi, hBi, hCi]
        · simp [IsBlockedAt, hAi, hBi, hCi]
  · intro h_three
    have hAB_C : A ∩ B ⊆ C := by
      intro i hi
      have hAi : i ∈ A := (Finset.mem_inter.mp hi).1
      have hBi : i ∈ B := (Finset.mem_inter.mp hi).2
      have hnb := h_three i (h_A hAi)
      by_contra hCi
      have hblocked : IsBlockedAt A B C i := by
        simp [IsBlockedAt, hAi, hBi, hCi]
      exact hnb hblocked
    have hAC_B : A ∩ C ⊆ B := by
      intro i hi
      have hAi : i ∈ A := (Finset.mem_inter.mp hi).1
      have hCi : i ∈ C := (Finset.mem_inter.mp hi).2
      have hnb := h_three i (h_A hAi)
      by_contra hBi
      have hblocked : IsBlockedAt A B C i := by
        simp [IsBlockedAt, hAi, hBi, hCi]
      exact hnb hblocked
    have hBC_A : B ∩ C ⊆ A := by
      intro i hi
      have hBi : i ∈ B := (Finset.mem_inter.mp hi).1
      have hCi : i ∈ C := (Finset.mem_inter.mp hi).2
      have hnb := h_three i (h_B hBi)
      by_contra hAi
      have hblocked : IsBlockedAt A B C i := by
        simp [IsBlockedAt, hAi, hBi, hCi]
      exact hnb hblocked
    have hAB_sub_BC : A ∩ B ⊆ B ∩ C := by
      intro i hi
      have hBi : i ∈ B := (Finset.mem_inter.mp hi).2
      have hCi : i ∈ C := hAB_C hi
      exact Finset.mem_inter.mpr ⟨hBi, hCi⟩
    have hBC_sub_AB : B ∩ C ⊆ A ∩ B := by
      intro i hi
      have hBi : i ∈ B := (Finset.mem_inter.mp hi).1
      have hAi : i ∈ A := hBC_A hi
      exact Finset.mem_inter.mpr ⟨hAi, hBi⟩
    have hAC_sub_AB : A ∩ C ⊆ A ∩ B := by
      intro i hi
      have hAi : i ∈ A := (Finset.mem_inter.mp hi).1
      have hBi : i ∈ B := hAC_B hi
      exact Finset.mem_inter.mpr ⟨hAi, hBi⟩
    have hAB_sub_AC : A ∩ B ⊆ A ∩ C := by
      intro i hi
      have hAi : i ∈ A := (Finset.mem_inter.mp hi).1
      have hCi : i ∈ C := hAB_C hi
      exact Finset.mem_inter.mpr ⟨hAi, hCi⟩
    refine ⟨A ∩ B, rfl, ?_, ?_⟩
    · exact Finset.Subset.antisymm hBC_sub_AB hAB_sub_BC
    · exact Finset.Subset.antisymm hAC_sub_AB hAB_sub_AC
  -- PROVIDED SOLUTION:
  -- Forward direction (sunflower => not blocked):
  --   If all pairwise intersections equal core K, then for any coordinate i:
  --   - If i in K: i is in all three sets (count = 3)
  --   - If i in A \ K: i not in B or C (count = 1)
  --   - If i not in A ∪ B ∪ C: count = 0
  --   So count is never 2.
  --
  -- Backward direction (not blocked => sunflower):
  --   Suppose no coordinate has count = 2. We show A ∩ B = B ∩ C = A ∩ C.
  --   For any i in A ∩ B: count >= 2, so must be 3 (since != 2), so i in C.
  --   Thus A ∩ B ⊆ C, similarly B ∩ C ⊆ A and A ∩ C ⊆ B.
  --   This gives A ∩ B ⊆ A ∩ C ⊆ B ∩ C ⊆ A ∩ B, so all equal.

/-- Counting lemma: total number of triples equals C(m, 3) -/
theorem count_triples (m : ℕ) :
    Nat.choose m 3 = m * (m - 1) * (m - 2) / 6 := by
  simpa [Nat.descFactorial_succ, Nat.descFactorial_one, Nat.descFactorial_zero, Nat.factorial,
    Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
    (Nat.choose_eq_descFactorial_div_factorial m 3)

-- ============================================================================
-- THE LOCAL TURAN INEQUALITY
-- ============================================================================

/-- The Local Turan Inequality for 3-sunflower-free families.

    If F is a 3-sunflower-free family with m = |F| sets over ground set U, then:

      sum_{i in U} C(d_i, 2) * (m - d_i) >= C(m, 3)

    where d_i = |{S in F : i in S}| is the coordinate degree.

    Intuition:
    - LHS counts (coordinate, pair at coord, singleton not at coord) configurations
    - RHS counts unordered triples from F
    - Every non-sunflower triple must be "blocked" at some coordinate
    - Being blocked means exactly 2 of 3 sets contain that coordinate
    - The inequality says: total blocking capacity >= triples to block

    This is a necessary condition for sunflower-freeness that captures the LOCAL
    nature of the constraint, unlike global conditions like arithmetic progressions. -/
theorem local_turan_inequality {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (m : ℕ)
    (h_card : family.card = m)
    (h_ground : ∀ S ∈ family, S ⊆ ground)
    (h_sf_free : IsSunflowerFree family 3) :
    totalBlockingCapacity family ground ≥ Nat.choose m 3 := by
  classical
  let triples : Finset (Finset (Finset α)) := family.powersetCard 3
  have htriples_card : triples.card = Nat.choose m 3 := by
    simp [triples, h_card, Finset.card_powersetCard]
  have htriples_sub : ∀ T ∈ triples, T ⊆ family := by
    intro T hT
    exact (Finset.mem_powersetCard.mp hT).1
  have htriples_card3 : ∀ T ∈ triples, T.card = 3 := by
    intro T hT
    exact (Finset.mem_powersetCard.mp hT).2
  have hblocked :
      ∀ T ∈ triples, ∃ i ∈ ground, (T.filter (fun S => i ∈ S)).card = 2 := by
    intro T hT
    have hTsub : T ⊆ family := htriples_sub T hT
    have hTcard : T.card = 3 := htriples_card3 T hT
    have hnot : ¬ IsSunflower T 3 := h_sf_free T hTsub
    obtain ⟨A, B, C, hAB, hAC, hBC, hTdef⟩ :=
      (Finset.card_eq_three.mp (by simpa using hTcard))
    have hA_T : A ∈ T := by
      simp [hTdef]
    have hB_T : B ∈ T := by
      simp [hTdef]
    have hC_T : C ∈ T := by
      simp [hTdef]
    have hA_ground : A ⊆ ground := h_ground A (hTsub hA_T)
    have hB_ground : B ⊆ ground := h_ground B (hTsub hB_T)
    have hC_ground : C ⊆ ground := h_ground C (hTsub hC_T)
    by_contra hnone
    push_neg at hnone
    have h_three : IsThreeSunflower A B C ground := by
      intro i hi
      have hcount : (T.filter (fun S => i ∈ S)).card =
          (if i ∈ A then (1 : ℕ) else 0) +
              (if i ∈ B then (1 : ℕ) else 0) +
              (if i ∈ C then (1 : ℕ) else 0) := by
        by_cases hAi : i ∈ A <;> by_cases hBi : i ∈ B <;> by_cases hCi : i ∈ C <;>
          simp [hTdef, hAi, hBi, hCi, hAB, hAC, hBC,
            Finset.filter_insert, Finset.filter_singleton]
      have hnotblocked : (if i ∈ A then (1 : ℕ) else 0) + (if i ∈ B then (1 : ℕ) else 0) +
          (if i ∈ C then (1 : ℕ) else 0) ≠ 2 := by
        have := hnone i hi
        simpa [hcount] using this
      exact hnotblocked
    have hcore :
        ∃ core : Finset α, A ∩ B = core ∧ B ∩ C = core ∧ A ∩ C = core :=
      (three_sunflower_iff_not_blocked A B C hAB hBC hAC ground hA_ground hB_ground hC_ground).2
        h_three
    have hsunflower : IsSunflower T 3 := by
      refine ⟨?_, ?_⟩
      · simpa [hTdef] using hTcard
      · rcases hcore with ⟨core, hABc, hBCc, hACc⟩
        refine ⟨core, ?_⟩
        intro S T' hS hT' hne
        -- reduce to the three cases via membership in {A,B,C}
        have hS' : S = A ∨ S = B ∨ S = C := by
          simpa [hTdef] using hS
        have hT'' : T' = A ∨ T' = B ∨ T' = C := by
          simpa [hTdef] using hT'
        have hABc' : B ∩ A = core := by
          simpa [Finset.inter_comm] using hABc
        have hACc' : C ∩ A = core := by
          simpa [Finset.inter_comm] using hACc
        have hBCc' : C ∩ B = core := by
          simpa [Finset.inter_comm] using hBCc
        rcases hS' with rfl | rfl | rfl <;>
          rcases hT'' with rfl | rfl | rfl <;>
          simp [hABc, hBCc, hACc, hABc', hACc', hBCc'] at hne ⊢
    exact hnot hsunflower
  let blocked : α → Finset (Finset (Finset α)) :=
    fun i => triples.filter (fun T => (T.filter (fun S => i ∈ S)).card = 2)
  have hsubset_union : triples ⊆ ground.biUnion blocked := by
    intro T hT
    obtain ⟨i, hi, hblock⟩ := hblocked T hT
    refine Finset.mem_biUnion.mpr ?_
    refine ⟨i, hi, ?_⟩
    simp [blocked, hT, hblock]
  have hcard_triples_le : triples.card ≤ (ground.biUnion blocked).card := by
    exact Finset.card_le_card hsubset_union
  have hcard_union_le : (ground.biUnion blocked).card ≤ ∑ i ∈ ground, (blocked i).card := by
    exact Finset.card_biUnion_le
  have hblocked_le :
      ∀ i ∈ ground, (blocked i).card ≤
        Nat.choose (coordDegree family i) 2 * (m - coordDegree family i) := by
    intro i hi
    let F1 := family.filter (fun S => i ∈ S)
    let F0 := family.filter (fun S => i ∉ S)
    let f : Finset (Finset α) → Finset (Finset α) × Finset (Finset α) :=
      fun T => (T.filter (fun S => i ∈ S), T.filter (fun S => i ∉ S))
    have hf_inj : Set.InjOn f (blocked i) := by
      intro T hT T' hT' hEq
      have hTunion :
          (T.filter (fun S => i ∈ S) ∪ T.filter (fun S => i ∉ S)) = T := by
        simpa using (Finset.filter_union_filter_neg_eq (s := T) (p := fun S => i ∈ S))
      have hTunion' :
          (T'.filter (fun S => i ∈ S) ∪ T'.filter (fun S => i ∉ S)) = T' := by
        simpa using (Finset.filter_union_filter_neg_eq (s := T') (p := fun S => i ∈ S))
      have hEq1 : T.filter (fun S => i ∈ S) = T'.filter (fun S => i ∈ S) := by
        exact congrArg Prod.fst hEq
      have hEq2 : T.filter (fun S => i ∉ S) = T'.filter (fun S => i ∉ S) := by
        exact congrArg Prod.snd hEq
      calc
        T = T.filter (fun S => i ∈ S) ∪ T.filter (fun S => i ∉ S) := by simpa using hTunion.symm
        _ = T'.filter (fun S => i ∈ S) ∪ T'.filter (fun S => i ∉ S) := by
              simp [hEq1, hEq2]
        _ = T' := hTunion'
    have himage_subset :
        (blocked i).image f ⊆
          (F1.powersetCard 2).product (F0.powersetCard 1) := by
      intro T hT
      rcases Finset.mem_image.mp hT with ⟨T', hT', rfl⟩
      have hT'_in : T' ∈ triples := (Finset.mem_filter.mp hT').1
      have hT'_sub : T' ⊆ family := htriples_sub T' hT'_in
      have hT'_card3 : T'.card = 3 := htriples_card3 T' hT'_in
      have hblock : (T'.filter (fun S => i ∈ S)).card = 2 := (Finset.mem_filter.mp hT').2
      have hblock0 :
          (T'.filter (fun S => i ∉ S)).card = 1 := by
        have hsum :=
          Finset.filter_card_add_filter_neg_card_eq_card (s := T') (p := fun S => i ∈ S)
        have hsum' :
            (T'.filter (fun S => i ∈ S)).card +
              (T'.filter (fun S => i ∉ S)).card = 3 := by
          simpa [hT'_card3] using hsum
        omega
      have hA_sub : T'.filter (fun S => i ∈ S) ⊆ F1 := by
        intro S hS
        have hS' : S ∈ T' := (Finset.mem_filter.mp hS).1
        have hSfam : S ∈ family := hT'_sub hS'
        have hSi : i ∈ S := (Finset.mem_filter.mp hS).2
        exact Finset.mem_filter.mpr ⟨hSfam, hSi⟩
      have hB_sub : T'.filter (fun S => i ∉ S) ⊆ F0 := by
        intro S hS
        have hS' : S ∈ T' := (Finset.mem_filter.mp hS).1
        have hSfam : S ∈ family := hT'_sub hS'
        have hSi : i ∉ S := (Finset.mem_filter.mp hS).2
        exact Finset.mem_filter.mpr ⟨hSfam, hSi⟩
      have hA_mem : T'.filter (fun S => i ∈ S) ∈ F1.powersetCard 2 :=
        (Finset.mem_powersetCard.mpr ⟨hA_sub, hblock⟩)
      have hB_mem : T'.filter (fun S => i ∉ S) ∈ F0.powersetCard 1 :=
        (Finset.mem_powersetCard.mpr ⟨hB_sub, hblock0⟩)
      exact Finset.mem_product.mpr ⟨hA_mem, hB_mem⟩
    have hcard_image :
        (blocked i).card = ((blocked i).image f).card := by
      simpa using
        (Finset.card_image_of_injOn (s := blocked i) (f := f) hf_inj).symm
    have hcard_le :
        (blocked i).card ≤ ((F1.powersetCard 2).product (F0.powersetCard 1)).card := by
      calc
        (blocked i).card = ((blocked i).image f).card := hcard_image
        _ ≤ ((F1.powersetCard 2).product (F0.powersetCard 1)).card := by
            exact Finset.card_le_card himage_subset
    have hF0_card : F0.card = m - coordDegree family i := by
      have hsum :=
        Finset.filter_card_add_filter_neg_card_eq_card (s := family) (p := fun S => i ∈ S)
      have hsum' :
          coordDegree family i + F0.card = m := by
        simpa [coordDegree, F0, h_card] using hsum
      have hle : coordDegree family i ≤ m := by
        exact Nat.le.intro (by omega)
      have hsub : F0.card = m - coordDegree family i := by
        rw [← hsum', Nat.add_sub_cancel_left]
      exact hsub
    have hprod_card :
        ((F1.powersetCard 2).product (F0.powersetCard 1)).card =
          Nat.choose (coordDegree family i) 2 * (m - coordDegree family i) := by
      have hF1_card : (F1.powersetCard 2).card = Nat.choose (coordDegree family i) 2 := by
        simp [F1, coordDegree]
      have hF0_card' : (F0.powersetCard 1).card = m - coordDegree family i := by
        simp [F0, hF0_card, Nat.choose_one_right]
      simp [Finset.card_product, hF1_card, hF0_card']
    exact hcard_le.trans_eq hprod_card
  have hsum_blocked :
      (∑ i ∈ ground, (blocked i).card) ≤
        ∑ i ∈ ground, Nat.choose (coordDegree family i) 2 * (m - coordDegree family i) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    exact hblocked_le i hi
  have hcard_triples_le' :
      Nat.choose m 3 ≤ ∑ i ∈ ground, (blocked i).card := by
    have h1 : Nat.choose m 3 = triples.card := by
      simp [htriples_card]
    have h2 : triples.card ≤ ∑ i ∈ ground, (blocked i).card := by
      exact (le_trans hcard_triples_le hcard_union_le)
    simpa [h1] using h2
  have hsum_capacity :
      Nat.choose m 3 ≤
        ∑ i ∈ ground, Nat.choose (coordDegree family i) 2 * (m - coordDegree family i) := by
    exact le_trans hcard_triples_le' hsum_blocked
  simpa [totalBlockingCapacity, blockingCapacity, h_card] using hsum_capacity
  -- PROVIDED SOLUTION SKETCH:
  --
  -- Step 1: Define the set of triples T = {(A,B,C) : A,B,C in F distinct}
  --         By h_sf_free, every triple in T is NOT a 3-sunflower
  --
  -- Step 2: By three_sunflower_iff_not_blocked, each triple is blocked at some coordinate
  --         So for each (A,B,C) in T, there exists i such that IsBlockedAt A B C i
  --
  -- Step 3: Double counting argument:
  --         - For each triple, count 1 for each coordinate that blocks it
  --         - Sum over triples >= |T| = C(m,3) (each triple blocked at least once)
  --         - Sum over coordinates of (blocking configurations at that coord)
  --           = sum_i (number of (A,B,C) blocked at i)
  --           = sum_i C(d_i, 2) * (m - d_i)  (choosing 2 sets containing i, 1 not)
  --         - Therefore LHS >= RHS

-- ============================================================================
-- COROLLARIES AND APPLICATIONS
-- ============================================================================

/-- For uniform families with all sets of size r, we get additional structure.
    If F is r-uniform over {1,...,n} with m sets, then sum of degrees = r * m. -/
theorem sum_degrees_uniform {α : Type*} [DecidableEq α] [Fintype α]
    (family : Finset (Finset α)) (r : ℕ)
    (h_uniform : ∀ S ∈ family, S.card = r)
    (ground : Finset α)
    (h_ground : ∀ S ∈ family, S ⊆ ground) :
    ground.sum (fun i => coordDegree family i) = r * family.card := by
  classical
  have hcoord :
      ∀ i, coordDegree family i =
        family.sum (fun S => if i ∈ S then (1 : ℕ) else 0) := by
    intro i
    unfold coordDegree
    calc
      (family.filter (fun S => i ∈ S)).card
          = ∑ S ∈ family.filter (fun S => i ∈ S), (1 : ℕ) := by
              exact (Finset.card_eq_sum_ones (family.filter (fun S => i ∈ S)))
      _ = family.sum (fun S => if i ∈ S then (1 : ℕ) else 0) := by
            exact (Finset.sum_filter (s := family) (f := fun _ => (1 : ℕ))
              (p := fun S => i ∈ S))
  have hswap :
      ground.sum (fun i => family.sum (fun S => if i ∈ S then (1 : ℕ) else 0)) =
        family.sum (fun S => ground.sum (fun i => if i ∈ S then (1 : ℕ) else 0)) := by
    have h1 :=
      (Finset.sum_product' (s := ground) (t := family)
        (f := fun i S => if i ∈ S then (1 : ℕ) else 0))
    have h2 :=
      (Finset.sum_product_right' (s := ground) (t := family)
        (f := fun i S => if i ∈ S then (1 : ℕ) else 0))
    exact h1.symm.trans h2
  have hsum :
      ground.sum (fun i => coordDegree family i) = family.sum (fun S => S.card) := by
    calc
      ground.sum (fun i => coordDegree family i)
          = ground.sum (fun i => family.sum (fun S => if i ∈ S then (1 : ℕ) else 0)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              exact hcoord i
      _ = family.sum (fun S => ground.sum (fun i => if i ∈ S then (1 : ℕ) else 0)) := hswap
      _ = family.sum (fun S => S.card) := by
            refine Finset.sum_congr rfl ?_
            intro S hS
            have hSground := h_ground S hS
            have hfilter : ground.filter (fun i => i ∈ S) = S := by
              apply Finset.ext
              intro i
              constructor
              · intro hi
                simpa using (Finset.mem_filter.mp hi).2
              · intro hi
                exact Finset.mem_filter.mpr ⟨hSground hi, hi⟩
            calc
      ground.sum (fun i => if i ∈ S then (1 : ℕ) else 0)
          = ∑ i ∈ ground.filter (fun i => i ∈ S), (1 : ℕ) := by
                      simpa using
                        (Finset.sum_filter (s := ground) (f := fun _ => (1 : ℕ))
                          (p := fun i => i ∈ S)).symm
      _ = S.card := by
                    have hcard :
                        ∑ i ∈ ground.filter (fun i => i ∈ S), (1 : ℕ) =
                          (ground.filter (fun i => i ∈ S)).card := by
                      exact (Finset.card_eq_sum_ones (ground.filter (fun i => i ∈ S))).symm
                    rw [hfilter]
                    exact (Finset.card_eq_sum_ones S).symm
  calc
    ground.sum (fun i => coordDegree family i) = family.sum (fun S => S.card) := hsum
    _ = family.sum (fun _ => r) := by
          refine Finset.sum_congr rfl ?_
          intro S hS
          simpa using (h_uniform S hS)
    _ = r * family.card := by
          simp [Finset.sum_const, Nat.mul_comm]

/-- The Local Turan inequality constrains the growth of m(n, 3).

    Key insight: For the maximum sunflower-free family on {1,...,n}, the degrees d_i
    cannot all be too small (or blocking capacity would be less than C(m,3)),
    but also cannot all be too large (since sum d_i depends on set sizes).

    This tension is what makes the problem hard and suggests polynomial bounds
    might be possible if we can show degrees must be "balanced". -/
theorem local_turan_growth_constraint {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (m n : ℕ)
    (h_card_family : family.card = m)
    (_h_card_ground : ground.card = n)
    (h_ground : ∀ S ∈ family, S ⊆ ground)
    (h_sf_free : IsSunflowerFree family 3)
    (_h_m_pos : m ≥ 3) :
    -- The average blocking capacity per coordinate is at least C(m,3)/n
    n * (Nat.choose m 3 / n) ≤ totalBlockingCapacity family ground := by
  have hcap : Nat.choose m 3 ≤ totalBlockingCapacity family ground := by
    exact local_turan_inequality family ground m h_card_family h_ground h_sf_free
  have hdiv : n * (Nat.choose m 3 / n) ≤ Nat.choose m 3 := by
    exact Nat.mul_div_le (Nat.choose m 3) n
  exact le_trans hdiv hcap
  -- This follows from local_turan_inequality and basic arithmetic

-- ============================================================================
-- CONNECTIONS TO OTHER APPROACHES
-- ============================================================================

/-
  The Local Turan inequality is our key novel contribution to the sunflower problem.

  Why this matters:
  1. Most existing bounds (Naslund-Sawin, ALWZ) use GLOBAL techniques (slice rank, spread)
  2. The sunflower constraint is fundamentally LOCAL (per-coordinate)
  3. This inequality EXPLOITS that locality directly

  Potential applications:
  - Combined with degree-sum constraints, may yield tighter bounds
  - The "blocking budget" perspective suggests information-theoretic approaches
  - May connect to entropy methods (each coordinate has limited capacity)

  Open questions:
  - Is this inequality tight? What families achieve equality?
  - Can we strengthen it using higher-order blocking?
  - Does it improve on known bounds when combined with other constraints?
-/
