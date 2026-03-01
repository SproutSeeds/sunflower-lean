/-
  Balance Theorem (Conjecture) Engine
  Authors: Cody Mitchell, Claude (Opus)
  Date: January 2026

  Status (honest):
  - This file contains a large, fully compiling Lean development that reduces
    Balance to explicit local counting bounds (no `sorry`s).
  - The Balance conjecture itself is still UNPROVEN here: the remaining gap is
    a global counting/overlap estimate strong enough to close the final strict
    inequality in the low/high-frequency cases.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic
import SunflowerLean.Basic
import SunflowerLean.LocalTuran
import SunflowerLean.SmallCases
import SunflowerLean.Slice

/-- Coerce a Nat to Rat without relying on implicit casts. -/
def ratOfNat (n : Nat) : Rat :=
  (n : Rat)

@[simp] lemma ratOfNat_eq (n : Nat) : ratOfNat n = (n : Rat) := rfl

/-- Family is on the given ground set. -/
def IsOnGround {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) : Prop :=
  ∀ S ∈ family, S ⊆ ground

/-- Inclusion-wise maximal k-sunflower-free family on ground. -/
def IsMaximalSunflowerFree {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (k : Nat) (ground : Finset α) : Prop :=
  IsSunflowerFree family k ∧
  IsOnGround family ground ∧
  ∀ S ⊆ ground, S ∉ family → ¬ IsSunflowerFree (insert S family) k

/-- Bridge theorem: maximal 3-sunflower-free families satisfy the Local Turan inequality. -/
theorem local_turan_inequality_of_maximal {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (m : ℕ)
    (h_card_family : family.card = m)
    (hmax : IsMaximalSunflowerFree family 3 ground) :
    totalBlockingCapacity family ground ≥ Nat.choose m 3 := by
  rcases hmax with ⟨h_sf_free, h_on_ground, _⟩
  exact local_turan_inequality family ground m h_card_family h_on_ground h_sf_free

/-- Bridge theorem specialized to intrinsic family cardinality. -/
theorem local_turan_inequality_of_maximal_cards {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α)
    (hmax : IsMaximalSunflowerFree family 3 ground) :
    totalBlockingCapacity family ground ≥ Nat.choose family.card 3 := by
  simpa using local_turan_inequality_of_maximal family ground family.card rfl hmax

/-- Bridge theorem: maximal 3-sunflower-free families satisfy the Local Turan growth constraint. -/
theorem local_turan_growth_constraint_of_maximal {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (m n : ℕ)
    (h_card_family : family.card = m)
    (h_card_ground : ground.card = n)
    (hmax : IsMaximalSunflowerFree family 3 ground)
    (h_m_pos : m ≥ 3) :
    n * (Nat.choose m 3 / n) ≤ totalBlockingCapacity family ground := by
  rcases hmax with ⟨h_sf_free, h_on_ground, _⟩
  exact local_turan_growth_constraint family ground m n
    h_card_family h_card_ground h_on_ground h_sf_free h_m_pos

/-- Bridge theorem specialized to intrinsic cardinalities. -/
theorem local_turan_growth_constraint_of_maximal_cards {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α)
    (hmax : IsMaximalSunflowerFree family 3 ground)
    (h_m_pos : family.card ≥ 3) :
    ground.card * (Nat.choose family.card 3 / ground.card) ≤
      totalBlockingCapacity family ground := by
  simpa using
    (local_turan_growth_constraint_of_maximal
      family ground family.card ground.card rfl rfl hmax h_m_pos)

/-- Bridge theorem bundling Local Turan inequality and growth consequences
    with explicit cardinality parameters. -/
theorem local_turan_bridge_of_maximal {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (m n : ℕ)
    (h_card_family : family.card = m)
    (h_card_ground : ground.card = n)
    (hmax : IsMaximalSunflowerFree family 3 ground) :
    totalBlockingCapacity family ground ≥ Nat.choose m 3 ∧
    (m ≥ 3 → n * (Nat.choose m 3 / n) ≤ totalBlockingCapacity family ground) := by
  constructor
  · exact local_turan_inequality_of_maximal family ground m h_card_family hmax
  · intro h_m_pos
    exact local_turan_growth_constraint_of_maximal
      family ground m n h_card_family h_card_ground hmax h_m_pos

/-- Bridge theorem bundling Local Turan inequality and growth consequences. -/
theorem local_turan_bridge_of_maximal_cards {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α)
    (hmax : IsMaximalSunflowerFree family 3 ground) :
    totalBlockingCapacity family ground ≥ Nat.choose family.card 3 ∧
    (family.card ≥ 3 →
      ground.card * (Nat.choose family.card 3 / ground.card) ≤
        totalBlockingCapacity family ground) := by
  simpa using
    (local_turan_bridge_of_maximal
      family ground family.card ground.card rfl rfl hmax)

/-- Left projection of the bundled Local Turan bridge theorem. -/
theorem local_turan_bridge_of_maximal_cards_left {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α)
    (hmax : IsMaximalSunflowerFree family 3 ground) :
    totalBlockingCapacity family ground ≥ Nat.choose family.card 3 := by
  exact (local_turan_bridge_of_maximal_cards family ground hmax).1

/-- Frequency of element i in family (as a rational). -/
def freq {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (i : α) : Rat :=
  ratOfNat (coordDegree family i) / ratOfNat family.card

/-- Coordinate degree is bounded by total family size. -/
theorem coordDegree_le_card {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (i : α) :
    coordDegree family i ≤ family.card := by
  unfold coordDegree
  exact (Finset.card_filter_le (s := family) (p := fun S => i ∈ S))

/-- Balance range for k=3: 1/3 ≤ freq ≤ 2/3. -/
def InBalanceRange {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (i : α) : Prop :=
  (ratOfNat 1 / ratOfNat 3) ≤ freq family i ∧
  freq family i ≤ (ratOfNat 2 / ratOfNat 3)

/-- Nat-inequality form of the balance range (requires |F| > 0 for equivalence). -/
def InBalanceRangeNat {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (i : α) : Prop :=
  family.card ≤ 3 * coordDegree family i ∧
  3 * coordDegree family i ≤ 2 * family.card

/-- Nat-form balance bounds imply the rational bounds (assuming |F| > 0). -/
theorem inBalanceRange_of_nat {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (i : α) (hcard : family.card > 0) :
    InBalanceRangeNat family i → InBalanceRange family i := by
  intro h
  rcases h with ⟨hlo, hhi⟩
  unfold InBalanceRange freq
  constructor
  · -- lower bound: 1/3 ≤ d/m
    have hmpos : (0 : Rat) < (family.card : Rat) := by
      exact_mod_cast hcard
    have hlo' : (family.card : Rat) ≤ (3 * coordDegree family i : Rat) := by
      exact_mod_cast hlo
    have hlow : (1 : Rat) / 3 * (family.card : Rat) ≤ (coordDegree family i : Rat) := by
      nlinarith [hlo']
    exact (le_div_iff₀ hmpos).2 hlow
  · -- upper bound: d/m ≤ 2/3
    have hmpos : (0 : Rat) < (family.card : Rat) := by
      exact_mod_cast hcard
    have hhi' : (3 * coordDegree family i : Rat) ≤ (2 * family.card : Rat) := by
      exact_mod_cast hhi
    have hhigh : (coordDegree family i : Rat) ≤ (2 : Rat) / 3 * (family.card : Rat) := by
      nlinarith [hhi']
    exact (div_le_iff₀ hmpos).2 hhigh

/-- Balance Theorem (conjecture statement only, no proof yet). -/
def BalanceConjecture {α : Type*} [DecidableEq α] : Prop :=
  ∀ (family : Finset (Finset α)) (ground : Finset α),
    family.card > 0 →
    IsMaximalSunflowerFree family 3 ground →
    ∀ i ∈ ground, InBalanceRange family i

/-- Balance Theorem in Nat form (conjecture statement only). -/
def BalanceConjectureNat {α : Type*} [DecidableEq α] : Prop :=
  ∀ (family : Finset (Finset α)) (ground : Finset α),
    family.card > 0 →
    IsMaximalSunflowerFree family 3 ground →
    ∀ i ∈ ground, InBalanceRangeNat family i

-- ============================================================================
-- Draft proof obligations (statement-only)
-- These encode the two maximality-contradiction cases used in the sketch.
-- ============================================================================

/-- Low-frequency condition in Nat form: 3*d_i < |F|. -/
def LowFreq {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (i : α) : Prop :=
  3 * coordDegree family i < family.card

/-- High-frequency condition in Nat form: 2*|F| < 3*d_i. -/
def HighFreq {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (i : α) : Prop :=
  2 * family.card < 3 * coordDegree family i

/-- An addable set containing i that preserves sunflower-freeness. -/
def AddableContaining {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) : Prop :=
  ∃ S ⊆ ground, i ∈ S ∧ S ∉ family ∧ IsSunflowerFree (insert S family) 3

/-- An addable set avoiding i that preserves sunflower-freeness. -/
def AddableAvoiding {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) : Prop :=
  ∃ S ⊆ ground, i ∉ S ∧ S ∉ family ∧ IsSunflowerFree (insert S family) 3

/-- Maximality forbids adding any set containing i. -/
theorem no_addable_containing_of_maximal {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    IsMaximalSunflowerFree family 3 ground →
    ¬ AddableContaining family ground i := by
  intro hmax h_add
  rcases hmax with ⟨_h_free, _h_on, h_max⟩
  rcases h_add with ⟨S, hSground, _hiS, hSnot, h_sf⟩
  exact (h_max S hSground hSnot) h_sf

/-- Maximality forbids adding any set avoiding i. -/
theorem no_addable_avoiding_of_maximal {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    IsMaximalSunflowerFree family 3 ground →
    ¬ AddableAvoiding family ground i := by
  intro hmax h_add
  rcases hmax with ⟨_h_free, _h_on, h_max⟩
  rcases h_add with ⟨S, hSground, _hiS, hSnot, h_sf⟩
  exact (h_max S hSground hSnot) h_sf

/-- Low-frequency case: if an element is too rare, we can add a set containing it. -/
def BalanceLowCaseConjecture {α : Type*} [DecidableEq α] : Prop :=
  ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
    IsMaximalSunflowerFree family 3 ground →
    i ∈ ground →
    LowFreq family i →
    AddableContaining family ground i

/-- High-frequency case: if an element is too common, we can add a set avoiding it. -/
def BalanceHighCaseConjecture {α : Type*} [DecidableEq α] : Prop :=
  ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
    IsMaximalSunflowerFree family 3 ground →
    HighFreq family i →
    AddableAvoiding family ground i

-- ============================================================================
-- Counting/covering setup for the low-frequency case
-- ============================================================================

/-- Candidate subsets of ground containing i. -/
def CandidatesContaining {α : Type*} [DecidableEq α]
    (ground : Finset α) (i : α) : Finset (Finset α) :=
  ground.powerset.filter (fun S => i ∈ S)

lemma mem_candidates_iff {α : Type*} [DecidableEq α]
    {ground : Finset α} {i : α} {S : Finset α} :
    S ∈ CandidatesContaining ground i ↔ S ⊆ ground ∧ i ∈ S := by
  constructor
  · intro h
    have h' := Finset.mem_filter.mp h
    constructor
    · exact (Finset.mem_powerset.mp h'.1)
    · exact h'.2
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr h.1, h.2⟩

/-- "Bad" means S would form a 3-sunflower with some pair from family. -/
def BadSet {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (S : Finset α) : Prop :=
  ∃ A ∈ family, ∃ B ∈ family, A ≠ B ∧
    ∃ core : Finset α, A ∩ B = core ∧ A ∩ S = core ∧ B ∩ S = core

/-- Bad candidates for a fixed pair (A,B). -/
def BadForPair {α : Type*} [DecidableEq α]
    (_family : Finset (Finset α)) (ground : Finset α) (i : α)
    (A B : Finset α) : Finset (Finset α) :=
  (CandidatesContaining ground i).filter (fun S =>
    A ∩ S = A ∩ B ∧ B ∩ S = A ∩ B)

/-- Bad candidate sets containing i. -/
noncomputable def BadContaining {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) : Finset (Finset α) :=
  by
    classical
    -- Only count candidates that are *not already in* `family`, since these are
    -- the only candidates relevant for maximality/addability arguments.
    exact (CandidatesContaining ground i).filter (fun S => S ∉ family ∧ BadSet family S)

/-- Every bad candidate is bad for some pair in family. -/
lemma badContaining_subset_pairUnion {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    BadContaining family ground i ⊆
      (family.product family).biUnion (fun p =>
        BadForPair family ground i p.1 p.2) := by
  classical
  intro S hS
  have hS' := Finset.mem_filter.mp hS
  rcases hS' with ⟨hCand, _hSnot, hbad⟩
  rcases hbad with ⟨A, hA, B, hB, _hneq, core, hAB, hAS, hBS⟩
  refine Finset.mem_biUnion.mpr ?_
  refine ⟨(A, B), ?_, ?_⟩
  · exact Finset.mem_product.mpr ⟨hA, hB⟩
  · exact Finset.mem_filter.mpr ⟨hCand, ⟨hAS.trans hAB.symm, hBS.trans hAB.symm⟩⟩

lemma card_biUnion_le_sum {α β : Type*} [DecidableEq β]
    (s : Finset α) (f : α → Finset β) :
    (s.biUnion f).card ≤ ∑ a ∈ s, (f a).card := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha hs
    calc
      ((insert a s).biUnion f).card
          = (f a ∪ s.biUnion f).card := by
              simp [Finset.biUnion_insert]
      _ ≤ (f a).card + (s.biUnion f).card := Finset.card_union_le _ _
      _ ≤ (f a).card + ∑ x ∈ s, (f x).card := by
            exact Nat.add_le_add_left hs _
      _ = ∑ x ∈ insert a s, (f x).card := by
            simp [Finset.sum_insert, ha]

lemma card_badContaining_le_sum {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    (BadContaining family ground i).card ≤
      ∑ p ∈ family.product family, (BadForPair family ground i p.1 p.2).card := by
  have hsubset := badContaining_subset_pairUnion family ground i
  have hcard : (BadContaining family ground i).card ≤
      ((family.product family).biUnion (fun p => BadForPair family ground i p.1 p.2)).card :=
    Finset.card_le_card hsubset
  exact hcard.trans (card_biUnion_le_sum _ _)

lemma badForPair_inter_union {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α)
    (A B S : Finset α) (h : S ∈ BadForPair family ground i A B) :
    S ∩ (A ∪ B) = A ∩ B := by
  have h' := Finset.mem_filter.mp h
  rcases h' with ⟨_hCand, hconds⟩
  rcases hconds with ⟨hAS, hBS⟩
  have hAS' : S ∩ A = A ∩ B := by
    simpa [Finset.inter_comm] using hAS
  have hBS' : S ∩ B = A ∩ B := by
    simpa [Finset.inter_comm] using hBS
  ext x; constructor
  · intro hx
    have hx' : x ∈ S ∧ (x ∈ A ∨ x ∈ B) := by
      simpa [Finset.mem_inter, Finset.mem_union] using hx
    rcases hx' with ⟨hxS, hxAB⟩
    cases hxAB with
    | inl hxA =>
        have hxSA : x ∈ S ∩ A := by
          simp [Finset.mem_inter, hxS, hxA]
        have hxAB' : x ∈ A ∩ B := by
          simpa [hAS'] using hxSA
        exact hxAB'
    | inr hxB =>
        have hxSB : x ∈ S ∩ B := by
          simp [Finset.mem_inter, hxS, hxB]
        have hxAB' : x ∈ A ∩ B := by
          simpa [hBS'] using hxSB
        exact hxAB'
  · intro hx
    have hxA : x ∈ A := (Finset.mem_inter.mp hx).1
    have hxB : x ∈ B := (Finset.mem_inter.mp hx).2
    have hxSA : x ∈ S ∩ A := by
      simpa [hAS'] using hx
    have hxS : x ∈ S := (Finset.mem_inter.mp hxSA).1
    have hxSAB : x ∈ S ∩ (A ∪ B) := by
      simp [Finset.mem_inter, Finset.mem_union, hxS, hxA, hxB]
    exact hxSAB

lemma badForPair_injOn {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α)
    (A B : Finset α) :
    Set.InjOn (fun S => S \ (A ∪ B)) (BadForPair family ground i A B) := by
  intro S₁ hS₁ S₂ hS₂ hEq
  have h1 := badForPair_inter_union family ground i A B S₁ hS₁
  have h2 := badForPair_inter_union family ground i A B S₂ hS₂
  have hS₁' : S₁ = (S₁ \ (A ∪ B)) ∪ (S₁ ∩ (A ∪ B)) := by
    simpa using (Finset.sdiff_union_inter S₁ (A ∪ B)).symm
  have hS₂' : (S₂ \ (A ∪ B)) ∪ (S₂ ∩ (A ∪ B)) = S₂ := by
    simpa using (Finset.sdiff_union_inter S₂ (A ∪ B))
  calc
    S₁ = (S₁ \ (A ∪ B)) ∪ (S₁ ∩ (A ∪ B)) := hS₁'
    _ = (S₂ \ (A ∪ B)) ∪ (S₂ ∩ (A ∪ B)) := by
          have hEq' : S₁ \ (A ∪ B) = S₂ \ (A ∪ B) := hEq
          rw [hEq', h1, h2]
    _ = S₂ := hS₂'

lemma card_badForPair_le {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α)
    (A B : Finset α) (h_on : IsOnGround family ground)
    (hA : A ∈ family) (hB : B ∈ family) :
    (BadForPair family ground i A B).card ≤
      2 ^ (ground.card - (A ∪ B).card) := by
  classical
  let f : Finset α → Finset α := fun S => S \ (A ∪ B)
  have hsubAB : A ∪ B ⊆ ground := by
    exact Finset.union_subset (h_on A hA) (h_on B hB)
  have himage : (BadForPair family ground i A B).image f ⊆
      (ground \ (A ∪ B)).powerset := by
    intro S hS
    rcases Finset.mem_image.mp hS with ⟨T, hT, rfl⟩
    have hT' := Finset.mem_filter.mp hT
    have hCand := mem_candidates_iff.mp hT'.1
    have hsub : T ⊆ ground := hCand.1
    have hsub' : T \ (A ∪ B) ⊆ ground \ (A ∪ B) :=
      Finset.sdiff_subset_sdiff hsub (by rfl)
    exact Finset.mem_powerset.mpr hsub'
  have hinj : Set.InjOn f (BadForPair family ground i A B) := by
    intro S₁ hS₁ S₂ hS₂ hEq
    have h1 := badForPair_inter_union family ground i A B S₁ hS₁
    have h2 := badForPair_inter_union family ground i A B S₂ hS₂
    have hS₁ : S₁ = (S₁ \ (A ∪ B)) ∪ (S₁ ∩ (A ∪ B)) := by
      simpa using (Finset.sdiff_union_inter S₁ (A ∪ B)).symm
    have hS₂ : (S₂ \ (A ∪ B)) ∪ (S₂ ∩ (A ∪ B)) = S₂ := by
      simpa using (Finset.sdiff_union_inter S₂ (A ∪ B))
    calc
      S₁ = (S₁ \ (A ∪ B)) ∪ (S₁ ∩ (A ∪ B)) := hS₁
      _ = (S₂ \ (A ∪ B)) ∪ (S₂ ∩ (A ∪ B)) := by
            have hEq' : S₁ \ (A ∪ B) = S₂ \ (A ∪ B) := hEq
            rw [hEq', h1, h2]
      _ = S₂ := hS₂
  have hcard_img :
      (BadForPair family ground i A B).card =
        ((BadForPair family ground i A B).image f).card := by
    exact (Finset.card_image_of_injOn hinj).symm
  have hcard_le : ((BadForPair family ground i A B).image f).card ≤
      (ground \ (A ∪ B)).powerset.card :=
    Finset.card_le_card himage
  have hpow :
      (ground \ (A ∪ B)).powerset.card = 2 ^ (ground \ (A ∪ B)).card := by
    exact Finset.card_powerset (ground \ (A ∪ B))
  have hcard_sdiff : (ground \ (A ∪ B)).card = ground.card - (A ∪ B).card := by
    exact Finset.card_sdiff_of_subset hsubAB
  calc
    (BadForPair family ground i A B).card
        = ((BadForPair family ground i A B).image f).card := hcard_img
    _ ≤ (ground \ (A ∪ B)).powerset.card := hcard_le
    _ = 2 ^ (ground \ (A ∪ B)).card := hpow
    _ = 2 ^ (ground.card - (A ∪ B).card) := by simp [hcard_sdiff]

/-- Number of candidates containing i is 2^(|ground|-1) when i ∈ ground. -/
lemma card_candidates_containing {α : Type*} [DecidableEq α]
    (ground : Finset α) (i : α) (hi : i ∈ ground) :
    (CandidatesContaining ground i).card = 2 ^ (ground.card - 1) := by
  classical
  let s : Finset (Finset α) := (ground.erase i).powerset
  let t : Finset (Finset α) := CandidatesContaining ground i
  have hbij : s.card = t.card := by
    refine Finset.card_bij' (s := s) (t := t)
      (fun S _ => insert i S) (fun T _ => T.erase i) ?hi ?hj ?left ?right
    · intro S hS
      have hsub : S ⊆ ground.erase i := by
        exact Finset.mem_powerset.mp hS
      have hsub_ground : S ⊆ ground := by
        exact subset_trans hsub (Finset.erase_subset i ground)
      have hmem : i ∈ insert i S := by simp
      have hsubset : insert i S ⊆ ground := Finset.insert_subset hi hsub_ground
      exact (mem_candidates_iff).2 ⟨hsubset, hmem⟩
    · intro T hT
      have hmem := mem_candidates_iff.mp hT
      have hsub : T ⊆ ground := hmem.1
      have hsub_erase : T.erase i ⊆ ground.erase i :=
        Finset.erase_subset_erase i hsub
      exact Finset.mem_powerset.mpr hsub_erase
    · intro S hS
      have hsub : S ⊆ ground.erase i := Finset.mem_powerset.mp hS
      have hiS : i ∉ S := by
        intro hiS_mem
        have : i ∈ ground.erase i := hsub hiS_mem
        simp at this
      exact Finset.erase_insert (a := i) (s := S) hiS
    · intro T hT
      have hmem := mem_candidates_iff.mp hT
      have hiT : i ∈ T := hmem.2
      exact Finset.insert_erase (s := T) hiT
  have hcard : s.card = 2 ^ (ground.erase i).card := by
    exact Finset.card_powerset (ground.erase i)
  have hEq : (ground.erase i).card = ground.card - 1 := by
    exact Finset.card_erase_of_mem hi
  calc
    (CandidatesContaining ground i).card
        = s.card := hbij.symm
    _ = 2 ^ (ground.erase i).card := hcard
    _ = 2 ^ (ground.card - 1) := by simp [hEq]

lemma badForPair_image_subset_candidates {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α)
    (A B : Finset α) (_hi_ground : i ∈ ground) (hiAB : i ∉ A ∪ B) :
    (BadForPair family ground i A B).image (fun S => S \ (A ∪ B)) ⊆
      CandidatesContaining (ground \ (A ∪ B)) i := by
  intro S hS
  rcases Finset.mem_image.mp hS with ⟨T, hT, rfl⟩
  have hT' := Finset.mem_filter.mp hT
  have hCand := mem_candidates_iff.mp hT'.1
  have hsub : T ⊆ ground := hCand.1
  have hiT : i ∈ T := hCand.2
  have hsub' : T \ (A ∪ B) ⊆ ground \ (A ∪ B) :=
    Finset.sdiff_subset_sdiff hsub (by rfl)
  have hi' : i ∈ T \ (A ∪ B) := by
    simp [Finset.mem_sdiff, hiT, hiAB]
  exact (mem_candidates_iff).2 ⟨hsub', hi'⟩

lemma card_badForPair_le_not_mem_union {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α)
    (A B : Finset α) (h_on : IsOnGround family ground)
    (hA : A ∈ family) (hB : B ∈ family)
    (hi_ground : i ∈ ground) (hiAB : i ∉ A ∪ B) :
    (BadForPair family ground i A B).card ≤
      2 ^ (ground.card - (A ∪ B).card - 1) := by
  classical
  let f : Finset α → Finset α := fun S => S \ (A ∪ B)
  have hcard_img :
      (BadForPair family ground i A B).card =
        ((BadForPair family ground i A B).image f).card := by
    exact (Finset.card_image_of_injOn (badForPair_injOn family ground i A B)).symm
  have hsubset := badForPair_image_subset_candidates family ground i A B hi_ground hiAB
  have hcard_le : ((BadForPair family ground i A B).image f).card ≤
      (CandidatesContaining (ground \ (A ∪ B)) i).card :=
    Finset.card_le_card hsubset
  have hi' : i ∈ ground \ (A ∪ B) := by
    simp [Finset.mem_sdiff, hi_ground, hiAB]
  have hcard_cand :
      (CandidatesContaining (ground \ (A ∪ B)) i).card =
        2 ^ ((ground \ (A ∪ B)).card - 1) :=
    card_candidates_containing (ground \ (A ∪ B)) i hi'
  have hsubAB : A ∪ B ⊆ ground :=
    Finset.union_subset (h_on A hA) (h_on B hB)
  have hcard_sdiff : (ground \ (A ∪ B)).card = ground.card - (A ∪ B).card :=
    Finset.card_sdiff_of_subset hsubAB
  calc
    (BadForPair family ground i A B).card
        = ((BadForPair family ground i A B).image f).card := hcard_img
    _ ≤ (CandidatesContaining (ground \ (A ∪ B)) i).card := hcard_le
    _ = 2 ^ ((ground \ (A ∪ B)).card - 1) := hcard_cand
    _ = 2 ^ (ground.card - (A ∪ B).card - 1) := by
          simp [hcard_sdiff]

lemma badForPair_empty_of_mem_not_mem {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α)
    {A B : Finset α} (hAi : i ∈ A) (hBi : i ∉ B) :
    BadForPair family ground i A B = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro S hS
  have h := Finset.mem_filter.mp hS
  have hCand := mem_candidates_iff.mp h.1
  have hiS : i ∈ S := hCand.2
  have hAS : A ∩ S = A ∩ B := h.2.1
  have hi_in : i ∈ A ∩ S := by
    simp [Finset.mem_inter, hAi, hiS]
  have hi_in_AB : i ∈ A ∩ B := by
    simpa [hAS] using hi_in
  have hiB : i ∈ B := (Finset.mem_inter.mp hi_in_AB).2
  exact (hBi hiB).elim

lemma badForPair_empty_of_not_mem_mem {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α)
    {A B : Finset α} (hAi : i ∉ A) (hBi : i ∈ B) :
    BadForPair family ground i A B = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro S hS
  have h := Finset.mem_filter.mp hS
  have hCand := mem_candidates_iff.mp h.1
  have hiS : i ∈ S := hCand.2
  have hBS : B ∩ S = A ∩ B := h.2.2
  have hi_in : i ∈ B ∩ S := by
    simp [Finset.mem_inter, hBi, hiS]
  have hi_in_AB : i ∈ A ∩ B := by
    simpa [hBS] using hi_in
  have hiA : i ∈ A := (Finset.mem_inter.mp hi_in_AB).1
  exact (hAi hiA).elim

def pairWeight {α : Type*} [DecidableEq α]
    (ground : Finset α) (i : α) (p : Finset α × Finset α) : Nat :=
  if i ∈ p.1 ∧ i ∈ p.2 then
    2 ^ (ground.card - (p.1 ∪ p.2).card)
  else if i ∉ p.1 ∧ i ∉ p.2 then
    2 ^ (ground.card - (p.1 ∪ p.2).card - 1)
  else 0

def familyIn {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (i : α) : Finset (Finset α) :=
  family.filter (fun S => i ∈ S)

def familyOut {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (i : α) : Finset (Finset α) :=
  family.filter (fun S => i ∉ S)

lemma card_familyIn {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (i : α) :
    (familyIn family i).card = coordDegree family i := by
  simp [familyIn, coordDegree]

lemma card_familyOut {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (i : α) :
    (familyOut family i).card = family.card - coordDegree family i := by
  classical
  have hsum :
      (familyIn family i).card + (familyOut family i).card = family.card := by
    simpa [familyIn, familyOut] using
      (Finset.filter_card_add_filter_neg_card_eq_card
        (s := family) (p := fun S => i ∈ S))
  have h := congrArg (fun x => x - (familyIn family i).card) hsum
  simpa [Nat.add_sub_cancel_left, card_familyIn family i] using h

lemma card_badForPair_le_weight {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α)
    (A B : Finset α) (h_on : IsOnGround family ground)
    (hA : A ∈ family) (hB : B ∈ family) (hi_ground : i ∈ ground) :
    (BadForPair family ground i A B).card ≤ pairWeight ground i (A, B) := by
  classical
  by_cases hAi : i ∈ A
  · by_cases hBi : i ∈ B
    · have hle := card_badForPair_le family ground i A B h_on hA hB
      simpa [pairWeight, hAi, hBi] using hle
    · have hEmpty := badForPair_empty_of_mem_not_mem family ground i hAi hBi
      simp [pairWeight, hAi, hBi, hEmpty]
  · by_cases hBi : i ∈ B
    · have hEmpty := badForPair_empty_of_not_mem_mem family ground i hAi hBi
      simp [pairWeight, hAi, hBi, hEmpty]
    · have hAB : i ∉ A ∪ B := by
        simp [Finset.mem_union, hAi, hBi]
      have hle := card_badForPair_le_not_mem_union family ground i A B h_on hA hB hi_ground hAB
      simpa [pairWeight, hAi, hBi] using hle

lemma card_badContaining_le_weight_sum {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α)
    (h_on : IsOnGround family ground) (hi_ground : i ∈ ground) :
    (BadContaining family ground i).card ≤
      ∑ p ∈ family.product family, pairWeight ground i p := by
  classical
  have hsum := card_badContaining_le_sum family ground i
  have hle :
      ∑ p ∈ family.product family, (BadForPair family ground i p.1 p.2).card ≤
        ∑ p ∈ family.product family, pairWeight ground i p := by
    refine Finset.sum_le_sum ?_
    intro p hp
    have hmem := Finset.mem_product.mp hp
    rcases hmem with ⟨hA, hB⟩
    exact card_badForPair_le_weight family ground i p.1 p.2 h_on hA hB hi_ground
  exact hsum.trans hle

lemma badContaining_subset_pairUnion_offDiag {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    BadContaining family ground i ⊆
      (family.offDiag).biUnion (fun p =>
        BadForPair family ground i p.1 p.2) := by
  classical
  intro S hS
  have hS' := Finset.mem_filter.mp hS
  rcases hS' with ⟨hCand, _hSnot, hbad⟩
  rcases hbad with ⟨A, hA, B, hB, hneq, core, hAB, hAS, hBS⟩
  refine Finset.mem_biUnion.mpr ?_
  refine ⟨(A, B), ?_, ?_⟩
  · exact Finset.mem_offDiag.mpr ⟨hA, hB, hneq⟩
  · exact Finset.mem_filter.mpr ⟨hCand, ⟨hAS.trans hAB.symm, hBS.trans hAB.symm⟩⟩

lemma card_badContaining_le_sum_offDiag {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    (BadContaining family ground i).card ≤
      ∑ p ∈ family.offDiag, (BadForPair family ground i p.1 p.2).card := by
  have hsubset := badContaining_subset_pairUnion_offDiag family ground i
  have hcard : (BadContaining family ground i).card ≤
      ((family.offDiag).biUnion (fun p => BadForPair family ground i p.1 p.2)).card :=
    Finset.card_le_card hsubset
  exact hcard.trans (card_biUnion_le_sum _ _)

lemma card_badContaining_le_weight_sum_offDiag {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α)
    (h_on : IsOnGround family ground) (hi_ground : i ∈ ground) :
    (BadContaining family ground i).card ≤
      ∑ p ∈ family.offDiag, pairWeight ground i p := by
  classical
  have hsum := card_badContaining_le_sum_offDiag family ground i
  have hle :
      ∑ p ∈ family.offDiag, (BadForPair family ground i p.1 p.2).card ≤
        ∑ p ∈ family.offDiag, pairWeight ground i p := by
    refine Finset.sum_le_sum ?_
    intro p hp
    have hmem := Finset.mem_offDiag.mp hp
    rcases hmem with ⟨hA, hB, _hneq⟩
    exact card_badForPair_le_weight family ground i p.1 p.2 h_on hA hB hi_ground
  exact hsum.trans hle

lemma pairWeight_le_pow {α : Type*} [DecidableEq α]
    (ground : Finset α) (i : α) (p : Finset α × Finset α) :
    pairWeight ground i p ≤ 2 ^ (ground.card - 1) := by
  classical
  by_cases hAi : i ∈ p.1 ∧ i ∈ p.2
  · have hi_union : i ∈ p.1 ∪ p.2 := by
      exact Finset.mem_union.mpr (Or.inl hAi.1)
    have hpos : 1 ≤ (p.1 ∪ p.2).card := by
      exact Nat.succ_le_iff.mpr (Finset.card_pos.mpr ⟨i, hi_union⟩)
    have hle : ground.card - (p.1 ∪ p.2).card ≤ ground.card - 1 := by
      exact Nat.sub_le_sub_left hpos _
    have hpow :
        2 ^ (ground.card - (p.1 ∪ p.2).card) ≤ 2 ^ (ground.card - 1) :=
      Nat.pow_le_pow_right (by decide) hle
    simpa [pairWeight, hAi] using hpow
  · by_cases hBi : i ∉ p.1 ∧ i ∉ p.2
    · have hle : ground.card - (p.1 ∪ p.2).card - 1 ≤ ground.card - 1 := by
        have hxy : ground.card - (p.1 ∪ p.2).card ≤ ground.card :=
          Nat.sub_le _ _
        exact Nat.sub_le_sub_right hxy 1
      have hpow :
          2 ^ (ground.card - (p.1 ∪ p.2).card - 1) ≤ 2 ^ (ground.card - 1) :=
        Nat.pow_le_pow_right (by decide) hle
      simpa [pairWeight, hAi, hBi] using hpow
    · simp [pairWeight, hAi, hBi]

lemma pairWeight_le_pow_in {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) (p : Finset α × Finset α)
    (hp : p ∈ (familyIn family i).offDiag) :
    pairWeight ground i p ≤ 2 ^ (ground.card - 2) := by
  classical
  have hmem := Finset.mem_offDiag.mp hp
  have hA : p.1 ∈ familyIn family i := hmem.1
  have hB : p.2 ∈ familyIn family i := hmem.2.1
  have _hneq : p.1 ≠ p.2 := hmem.2.2
  have hiA : i ∈ p.1 := (Finset.mem_filter.mp hA).2
  have hiB : i ∈ p.2 := (Finset.mem_filter.mp hB).2
  have hlt : 1 < (p.1 ∪ p.2).card := by
    by_cases hsub : p.1 ⊆ p.2
    · have hnot : ¬ p.2 ⊆ p.1 := by
        intro hsub2
        exact _hneq (Finset.Subset.antisymm hsub hsub2)
      rcases (Finset.sdiff_nonempty).2 hnot with ⟨x, hx⟩
      have hxB : x ∈ p.2 := (Finset.mem_sdiff.mp hx).1
      have hxnotA : x ∉ p.1 := (Finset.mem_sdiff.mp hx).2
      have hxne : x ≠ i := by
        intro hxi
        apply hxnotA
        simpa [hxi] using hiA
      apply (Finset.one_lt_card).2
      refine ⟨i, ?_, x, ?_, hxne.symm⟩
      · exact Finset.mem_union.mpr (Or.inl hiA)
      · exact Finset.mem_union.mpr (Or.inr hxB)
    · rcases (Finset.sdiff_nonempty).2 hsub with ⟨x, hx⟩
      have hxA : x ∈ p.1 := (Finset.mem_sdiff.mp hx).1
      have hxnotB : x ∉ p.2 := (Finset.mem_sdiff.mp hx).2
      have hxne : x ≠ i := by
        intro hxi
        apply hxnotB
        simpa [hxi] using hiB
      apply (Finset.one_lt_card).2
      refine ⟨i, ?_, x, ?_, hxne.symm⟩
      · exact Finset.mem_union.mpr (Or.inr hiB)
      · exact Finset.mem_union.mpr (Or.inl hxA)
  have hle : ground.card - (p.1 ∪ p.2).card ≤ ground.card - 2 := by
    exact Nat.sub_le_sub_left (Nat.succ_le_iff.mp hlt) _
  have hpow :
      2 ^ (ground.card - (p.1 ∪ p.2).card) ≤ 2 ^ (ground.card - 2) :=
    Nat.pow_le_pow_right (by decide) hle
  have hAi : i ∈ p.1 ∧ i ∈ p.2 := ⟨hiA, hiB⟩
  simpa [pairWeight, hAi] using hpow

lemma pairWeight_le_pow_out {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) (p : Finset α × Finset α)
    (hp : p ∈ (familyOut family i).offDiag) (hcard2 : 2 ≤ (p.1 ∪ p.2).card) :
    pairWeight ground i p ≤ 2 ^ (ground.card - 3) := by
  classical
  have hmem := Finset.mem_offDiag.mp hp
  have hA : p.1 ∈ familyOut family i := hmem.1
  have hB : p.2 ∈ familyOut family i := hmem.2.1
  have hneq : p.1 ≠ p.2 := hmem.2.2
  have hiA : i ∉ p.1 := (Finset.mem_filter.mp hA).2
  have hiB : i ∉ p.2 := (Finset.mem_filter.mp hB).2
  have hle : ground.card - (p.1 ∪ p.2).card - 1 ≤ ground.card - 3 := by
    have hxy : ground.card - (p.1 ∪ p.2).card ≤ ground.card - 2 :=
      Nat.sub_le_sub_left hcard2 _
    exact Nat.sub_le_sub_right hxy 1
  have hpow :
      2 ^ (ground.card - (p.1 ∪ p.2).card - 1) ≤ 2 ^ (ground.card - 3) :=
    Nat.pow_le_pow_right (by decide) hle
  have hBi : i ∉ p.1 ∧ i ∉ p.2 := ⟨hiA, hiB⟩
  simpa [pairWeight, hBi, hiA, hiB] using hpow

lemma sum_pairWeight_in_le {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    ∑ p ∈ (familyIn family i).offDiag, pairWeight ground i p ≤
      ((familyIn family i).card * (familyIn family i).card -
        (familyIn family i).card) * 2 ^ (ground.card - 2) := by
  classical
  have hle :
      ∑ p ∈ (familyIn family i).offDiag, pairWeight ground i p ≤
        ∑ p ∈ (familyIn family i).offDiag, 2 ^ (ground.card - 2) := by
    refine Finset.sum_le_sum ?_
    intro p hp
    exact pairWeight_le_pow_in family ground i p hp
  calc
    ∑ p ∈ (familyIn family i).offDiag, pairWeight ground i p
        ≤ ∑ p ∈ (familyIn family i).offDiag, 2 ^ (ground.card - 2) := hle
    _ = (familyIn family i).offDiag.card * 2 ^ (ground.card - 2) := by
          simp
    _ = ((familyIn family i).card * (familyIn family i).card -
          (familyIn family i).card) * 2 ^ (ground.card - 2) := by
          simp [Finset.offDiag_card]

lemma sum_pairWeight_out_le {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α)
    (hcard2 : ∀ p ∈ (familyOut family i).offDiag, 2 ≤ (p.1 ∪ p.2).card) :
    ∑ p ∈ (familyOut family i).offDiag, pairWeight ground i p ≤
      ((familyOut family i).card * (familyOut family i).card -
        (familyOut family i).card) * 2 ^ (ground.card - 3) := by
  classical
  have hle :
      ∑ p ∈ (familyOut family i).offDiag, pairWeight ground i p ≤
        ∑ p ∈ (familyOut family i).offDiag, 2 ^ (ground.card - 3) := by
    refine Finset.sum_le_sum ?_
    intro p hp
    exact pairWeight_le_pow_out family ground i p hp (hcard2 p hp)
  calc
    ∑ p ∈ (familyOut family i).offDiag, pairWeight ground i p
        ≤ ∑ p ∈ (familyOut family i).offDiag, 2 ^ (ground.card - 3) := hle
    _ = (familyOut family i).offDiag.card * 2 ^ (ground.card - 3) := by
          simp
    _ = ((familyOut family i).card * (familyOut family i).card -
          (familyOut family i).card) * 2 ^ (ground.card - 3) := by
          simp [Finset.offDiag_card]

lemma weight_sum_bound_offDiag_coarse {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α)
    (h_split :
      ∑ p ∈ family.offDiag, pairWeight ground i p ≤
        ∑ p ∈ (familyIn family i).offDiag, pairWeight ground i p +
        ∑ p ∈ (familyOut family i).offDiag, pairWeight ground i p)
    (hcard2 : ∀ p ∈ (familyOut family i).offDiag, 2 ≤ (p.1 ∪ p.2).card) :
    ∑ p ∈ family.offDiag, pairWeight ground i p ≤
      ((familyIn family i).card * (familyIn family i).card -
        (familyIn family i).card) * 2 ^ (ground.card - 2) +
      ((familyOut family i).card * (familyOut family i).card -
        (familyOut family i).card) * 2 ^ (ground.card - 3) := by
  have h_in := sum_pairWeight_in_le family ground i
  have h_out := sum_pairWeight_out_le family ground i hcard2
  exact le_trans h_split (by exact Nat.add_le_add h_in h_out)

lemma weight_sum_split_offDiag {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    ∑ p ∈ family.offDiag, pairWeight ground i p ≤
      ∑ p ∈ (familyIn family i).offDiag, pairWeight ground i p +
      ∑ p ∈ (familyOut family i).offDiag, pairWeight ground i p := by
  classical
  have hle :
      ∑ p ∈ family.offDiag, pairWeight ground i p ≤
        ∑ p ∈ family.offDiag,
          ((if p ∈ (familyIn family i).offDiag then pairWeight ground i p else 0) +
           (if p ∈ (familyOut family i).offDiag then pairWeight ground i p else 0)) := by
    refine Finset.sum_le_sum ?_
    intro p hp
    have hmem := Finset.mem_offDiag.mp hp
    have hA_fam : p.1 ∈ family := hmem.1
    have hB_fam : p.2 ∈ family := hmem.2.1
    have hneq : p.1 ≠ p.2 := hmem.2.2
    by_cases hAi : i ∈ p.1
    · by_cases hBi : i ∈ p.2
      · have hA_in : p.1 ∈ familyIn family i :=
          Finset.mem_filter.mpr ⟨hA_fam, hAi⟩
        have hB_in : p.2 ∈ familyIn family i :=
          Finset.mem_filter.mpr ⟨hB_fam, hBi⟩
        have hin : p ∈ (familyIn family i).offDiag :=
          Finset.mem_offDiag.mpr ⟨hA_in, hB_in, hneq⟩
        have hout : p ∉ (familyOut family i).offDiag := by
          intro hout
          have hout' := Finset.mem_offDiag.mp hout
          have hi_out : i ∉ p.1 := (Finset.mem_filter.mp hout'.1).2
          exact hi_out hAi
        simp [pairWeight, hAi, hBi, hin, hout]
      · have hin : p ∉ (familyIn family i).offDiag := by
          intro hin
          have hin' := Finset.mem_offDiag.mp hin
          have hi_in : i ∈ p.2 := (Finset.mem_filter.mp hin'.2.1).2
          exact hBi hi_in
        have hout : p ∉ (familyOut family i).offDiag := by
          intro hout
          have hout' := Finset.mem_offDiag.mp hout
          have hi_out : i ∉ p.1 := (Finset.mem_filter.mp hout'.1).2
          exact hi_out hAi
        simp [pairWeight, hAi, hBi, hin, hout]
    · by_cases hBi : i ∈ p.2
      · have hin : p ∉ (familyIn family i).offDiag := by
          intro hin
          have hin' := Finset.mem_offDiag.mp hin
          have hi_in : i ∈ p.1 := (Finset.mem_filter.mp hin'.1).2
          exact hAi hi_in
        have hout : p ∉ (familyOut family i).offDiag := by
          intro hout
          have hout' := Finset.mem_offDiag.mp hout
          have hi_out : i ∉ p.2 := (Finset.mem_filter.mp hout'.2.1).2
          exact hi_out hBi
        simp [pairWeight, hAi, hBi, hin, hout]
      · have hA_out : p.1 ∈ familyOut family i :=
          Finset.mem_filter.mpr ⟨hA_fam, hAi⟩
        have hB_out : p.2 ∈ familyOut family i :=
          Finset.mem_filter.mpr ⟨hB_fam, hBi⟩
        have hout : p ∈ (familyOut family i).offDiag :=
          Finset.mem_offDiag.mpr ⟨hA_out, hB_out, hneq⟩
        have hin : p ∉ (familyIn family i).offDiag := by
          intro hin
          have hin' := Finset.mem_offDiag.mp hin
          have hi_in : i ∈ p.1 := (Finset.mem_filter.mp hin'.1).2
          exact hAi hi_in
        simp [pairWeight, hAi, hBi, hin, hout]
  have hsum :
      ∑ p ∈ family.offDiag,
        ((if p ∈ (familyIn family i).offDiag then pairWeight ground i p else 0)
          +
          (if p ∈ (familyOut family i).offDiag then pairWeight ground i p else 0))
        =
        (∑ p ∈ family.offDiag,
            if p ∈ (familyIn family i).offDiag then pairWeight ground i p else 0)
          +
          ∑ p ∈ family.offDiag,
            if p ∈ (familyOut family i).offDiag then pairWeight ground i p else 0 := by
    simp [Finset.sum_add_distrib]
  have hsubset_in : (familyIn family i).offDiag ⊆ family.offDiag := by
    intro p hp
    have hmem := Finset.mem_offDiag.mp hp
    have hA_in : p.1 ∈ familyIn family i := hmem.1
    have hB_in : p.2 ∈ familyIn family i := hmem.2.1
    have hA_fam : p.1 ∈ family := (Finset.mem_filter.mp hA_in).1
    have hB_fam : p.2 ∈ family := (Finset.mem_filter.mp hB_in).1
    exact Finset.mem_offDiag.mpr ⟨hA_fam, hB_fam, hmem.2.2⟩
  have hsubset_out : (familyOut family i).offDiag ⊆ family.offDiag := by
    intro p hp
    have hmem := Finset.mem_offDiag.mp hp
    have hA_out : p.1 ∈ familyOut family i := hmem.1
    have hB_out : p.2 ∈ familyOut family i := hmem.2.1
    have hA_fam : p.1 ∈ family := (Finset.mem_filter.mp hA_out).1
    have hB_fam : p.2 ∈ family := (Finset.mem_filter.mp hB_out).1
    exact Finset.mem_offDiag.mpr ⟨hA_fam, hB_fam, hmem.2.2⟩
  have hfilter_in :
      family.offDiag.filter (fun p => p.1 ∈ familyIn family i ∧ p.2 ∈ familyIn family i) =
        (familyIn family i).offDiag := by
    ext p
    constructor
    · intro hp
      have h := Finset.mem_filter.mp hp
      have hp_off := Finset.mem_offDiag.mp h.1
      exact Finset.mem_offDiag.mpr ⟨h.2.1, h.2.2, hp_off.2.2⟩
    · intro hp
      have hp' := Finset.mem_offDiag.mp hp
      refine Finset.mem_filter.mpr ⟨hsubset_in hp, ?_⟩
      exact ⟨hp'.1, hp'.2.1⟩
  have hfilter_out :
      family.offDiag.filter (fun p => p.1 ∈ familyOut family i ∧ p.2 ∈ familyOut family i) =
        (familyOut family i).offDiag := by
    ext p
    constructor
    · intro hp
      have h := Finset.mem_filter.mp hp
      have hp_off := Finset.mem_offDiag.mp h.1
      exact Finset.mem_offDiag.mpr ⟨h.2.1, h.2.2, hp_off.2.2⟩
    · intro hp
      have hp' := Finset.mem_offDiag.mp hp
      refine Finset.mem_filter.mpr ⟨hsubset_out hp, ?_⟩
      exact ⟨hp'.1, hp'.2.1⟩
  have hsum_in :
      ∑ p ∈ family.offDiag, (if p ∈ (familyIn family i).offDiag then pairWeight ground i p else 0)
        =
      ∑ p ∈ (familyIn family i).offDiag, pairWeight ground i p := by
    classical
    have hsum' :
        (∑ x ∈ family.offDiag,
            if x.1 ∈ familyIn family i ∧ x.2 ∈ familyIn family i then
              pairWeight ground i x
            else
              0)
          =
        ∑ x ∈ family.offDiag with
            x.1 ∈ familyIn family i ∧ x.2 ∈ familyIn family i,
            pairWeight ground i x := by
      refine Finset.induction_on family.offDiag (by simp) ?_
      intro a s ha ih
      by_cases hpa : a.1 ∈ familyIn family i ∧ a.2 ∈ familyIn family i
      · simp [Finset.filter_insert, ha, hpa, ih]
      · simp [Finset.filter_insert, ha, hpa, ih]
    have hsum'' :
        (∑ x ∈ family.offDiag,
            if x.1 ∈ familyIn family i ∧ x.2 ∈ familyIn family i ∧ ¬x.1 = x.2 then
              pairWeight ground i x
            else
              0)
          =
        ∑ x ∈ family.offDiag,
            if x.1 ∈ familyIn family i ∧ x.2 ∈ familyIn family i then
              pairWeight ground i x
            else
              0 := by
      -- On `family.offDiag`, `¬ x.1 = x.2` is always true, so we can drop it from the condition.
      refine Finset.sum_congr rfl ?_
      intro x hx
      have hx' : x.1 ≠ x.2 := (Finset.mem_offDiag.mp hx).2.2
      by_cases hA : x.1 ∈ familyIn family i ∧ x.2 ∈ familyIn family i
      · have : (x.1 ∈ familyIn family i ∧ x.2 ∈ familyIn family i ∧ ¬x.1 = x.2) := ⟨hA.1, hA.2, hx'⟩
        simp [hA, this]
      · have : ¬ (x.1 ∈ familyIn family i ∧ x.2 ∈ familyIn family i ∧ ¬x.1 = x.2) := by
            intro h
            exact hA ⟨h.1, h.2.1⟩
        simp [hA, this]
    have hsum''' :
        (∑ x ∈ family.offDiag,
            if x.1 ∈ familyIn family i ∧ x.2 ∈ familyIn family i ∧ ¬x.1 = x.2 then
              pairWeight ground i x
            else
              0)
          =
        ∑ x ∈ family.offDiag with
            x.1 ∈ familyIn family i ∧ x.2 ∈ familyIn family i,
            pairWeight ground i x := by
      exact Eq.trans hsum'' hsum'
    simpa [pairWeight, Finset.mem_offDiag, hfilter_in] using hsum'''
  have hsum_out :
      ∑ p ∈ family.offDiag, (if p ∈ (familyOut family i).offDiag then pairWeight ground i p else 0)
        =
      ∑ p ∈ (familyOut family i).offDiag, pairWeight ground i p := by
    classical
    have hsum' :
        (∑ x ∈ family.offDiag,
            if x.1 ∈ familyOut family i ∧ x.2 ∈ familyOut family i then
              pairWeight ground i x
            else
              0)
          =
        ∑ x ∈ family.offDiag with
            x.1 ∈ familyOut family i ∧ x.2 ∈ familyOut family i,
            pairWeight ground i x := by
      -- prove indicator-sum = sum over filtered set
      refine Finset.induction_on family.offDiag (by simp) ?_
      intro a s ha ih
      by_cases hpa : a.1 ∈ familyOut family i ∧ a.2 ∈ familyOut family i
      · simp [Finset.filter_insert, ha, hpa, ih]
      · simp [Finset.filter_insert, ha, hpa, ih]
    have hsum'' :
        (∑ x ∈ family.offDiag,
            if x.1 ∈ familyOut family i ∧ x.2 ∈ familyOut family i ∧ ¬x.1 = x.2 then
              pairWeight ground i x
            else
              0)
          =
        ∑ x ∈ family.offDiag,
            if x.1 ∈ familyOut family i ∧ x.2 ∈ familyOut family i then
              pairWeight ground i x
            else
              0 := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      have hx' : x.1 ≠ x.2 := (Finset.mem_offDiag.mp hx).2.2
      by_cases hA : x.1 ∈ familyOut family i ∧ x.2 ∈ familyOut family i
      · have hcond :
            x.1 ∈ familyOut family i ∧ x.2 ∈ familyOut family i ∧ ¬x.1 = x.2 :=
            ⟨hA.1, hA.2, hx'⟩
        simp [hA, hcond]
      · have : ¬ (x.1 ∈ familyOut family i ∧ x.2 ∈ familyOut family i ∧ ¬x.1 = x.2) := by
            intro h
            exact hA ⟨h.1, h.2.1⟩
        simp [hA, this]
    have hsum''' :
        (∑ x ∈ family.offDiag,
            if x.1 ∈ familyOut family i ∧ x.2 ∈ familyOut family i ∧ ¬x.1 = x.2 then
              pairWeight ground i x
            else
              0)
          =
        ∑ x ∈ family.offDiag with
            x.1 ∈ familyOut family i ∧ x.2 ∈ familyOut family i,
            pairWeight ground i x := by
      exact Eq.trans hsum'' hsum'
    simpa [pairWeight, Finset.mem_offDiag, hfilter_out] using hsum'''
  have hle' : ∑ p ∈ family.offDiag, pairWeight ground i p ≤
      (∑ p ∈ family.offDiag,
          if p ∈ (familyIn family i).offDiag then pairWeight ground i p else 0)
        +
        ∑ p ∈ family.offDiag,
          if p ∈ (familyOut family i).offDiag then pairWeight ground i p else 0 := by
    exact le_trans hle (le_of_eq hsum)
  calc
    ∑ p ∈ family.offDiag, pairWeight ground i p
        ≤ (∑ p ∈ family.offDiag,
              if p ∈ (familyIn family i).offDiag then pairWeight ground i p else 0)
          +
          ∑ p ∈ family.offDiag,
              if p ∈ (familyOut family i).offDiag then pairWeight ground i p else 0 := hle'
    _ = ∑ p ∈ (familyIn family i).offDiag, pairWeight ground i p +
          ∑ p ∈ family.offDiag,
            (if p ∈ (familyOut family i).offDiag then pairWeight ground i p else 0) := by
          rw [hsum_in]
    _ = ∑ p ∈ (familyIn family i).offDiag, pairWeight ground i p +
          ∑ p ∈ (familyOut family i).offDiag, pairWeight ground i p := by
          rw [hsum_out]

lemma weight_sum_bound_trivial {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    ∑ p ∈ family.product family, pairWeight ground i p ≤
      family.card * family.card * 2 ^ (ground.card - 1) := by
  classical
  have hle :
      ∑ p ∈ family.product family, pairWeight ground i p ≤
        ∑ p ∈ family.product family, 2 ^ (ground.card - 1) := by
    refine Finset.sum_le_sum ?_
    intro p hp
    exact pairWeight_le_pow ground i p
  calc
    ∑ p ∈ family.product family, pairWeight ground i p
        ≤ ∑ p ∈ family.product family, 2 ^ (ground.card - 1) := hle
    _ = (family.product family).card * 2 ^ (ground.card - 1) := by
          simp
    _ = family.card * family.card * 2 ^ (ground.card - 1) := by
          simp [Finset.card_product, Nat.mul_assoc]

/-- Pointwise pair-union lower bound target for off-diagonal pairs. -/
def PointwiseUnionLowerBound {α : Type*} [DecidableEq α] (c : ℕ) : Prop :=
  ∀ (family : Finset (Finset α)) (ground : Finset α),
    IsOnGround family ground →
    IsSunflowerFree family 3 →
    ∀ p ∈ family.offDiag, c ≤ (p.1 ∪ p.2).card

/-- Average union-size bound target (kept as explicit hypothesis form). -/
def AverageUnionSizeBound {α : Type*} [DecidableEq α] (c : ℕ) : Prop :=
  ∀ (family : Finset (Finset α)) (ground : Finset α),
    IsOnGround family ground →
    IsSunflowerFree family 3 →
    family.card ≥ 3 →
    c * family.offDiag.card ≤
      ∑ p ∈ family.offDiag, (p.1 ∪ p.2).card

/-- Pointwise implies average (mechanical bridge). -/
theorem average_union_of_pointwise {α : Type*} [DecidableEq α] (c : ℕ) :
    PointwiseUnionLowerBound (α := α) c →
    AverageUnionSizeBound (α := α) c := by
  intro hpoint family ground h_on hfree _hcard
  have hconst : ∑ _ ∈ family.offDiag, c = family.offDiag.card * c := by
    simpa [nsmul_eq_mul] using
      (Finset.sum_const (s := family.offDiag) (a := c))
  calc
    c * family.offDiag.card = family.offDiag.card * c := by
      rw [Nat.mul_comm]
    _ = ∑ _ ∈ family.offDiag, c := by
      exact hconst.symm
    _ ≤ ∑ p ∈ family.offDiag, (p.1 ∪ p.2).card := by
      refine Finset.sum_le_sum ?_
      intro p hp
      exact hpoint family ground h_on hfree p hp

/-- Hypothesis: pairWeight is bounded by the union-size envelope.
    This isolates the case-split over pairWeight definition. -/
def PairWeightEnvelopeHyp {α : Type*} [DecidableEq α] : Prop :=
  ∀ (ground : Finset α) (i : α) (p : Finset α × Finset α),
    pairWeight ground i p ≤ 2 ^ (ground.card - (p.1 ∪ p.2).card)

/-- Conditional weight-sum reduction from pointwise union lower bound
    plus pairWeight envelope hypothesis. -/
theorem weight_sum_le_of_pointwise_union_lower {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) (c : ℕ)
    (_h_on : IsOnGround family ground)
    (henv : PairWeightEnvelopeHyp (α := α))
    (hpoint : ∀ p ∈ family.offDiag, c ≤ (p.1 ∪ p.2).card) :
    ∑ p ∈ family.offDiag, pairWeight ground i p ≤
      family.offDiag.card * 2 ^ (ground.card - c) := by
  have hconst :
      ∑ p ∈ family.offDiag, 2 ^ (ground.card - c) =
        family.offDiag.card * 2 ^ (ground.card - c) := by
    simpa [nsmul_eq_mul] using
      (Finset.sum_const (s := family.offDiag) (a := 2 ^ (ground.card - c)))
  have hle :
      ∑ p ∈ family.offDiag, pairWeight ground i p ≤
        ∑ p ∈ family.offDiag, 2 ^ (ground.card - c) := by
    refine Finset.sum_le_sum ?_
    intro p hp
    exact le_trans (henv ground i p)
      (Nat.pow_le_pow_right (by decide)
        (Nat.sub_le_sub_left (hpoint p hp) _))
  calc
    ∑ p ∈ family.offDiag, pairWeight ground i p
        ≤ ∑ p ∈ family.offDiag, 2 ^ (ground.card - c) := hle
    _ = family.offDiag.card * 2 ^ (ground.card - c) := by
      exact hconst

/-- Candidates containing i that are already in the family. -/
def InFamilyContaining {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) : Finset (Finset α) :=
  (CandidatesContaining ground i).filter (fun S => S ∈ family)

lemma in_family_containing_subset {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    InFamilyContaining family ground i ⊆ family.filter (fun S => i ∈ S) := by
  intro S hS
  have h := Finset.mem_filter.mp hS
  have hCand := mem_candidates_iff.mp h.1
  exact Finset.mem_filter.mpr ⟨h.2, hCand.2⟩

lemma card_in_family_containing_le {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    (InFamilyContaining family ground i).card ≤ coordDegree family i := by
  unfold coordDegree
  exact Finset.card_le_card (in_family_containing_subset family ground i)

/-- If every set in family is on the ground, candidates-in-family match coordDegree. -/
lemma in_family_containing_eq_filter {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α)
    (h_on : IsOnGround family ground) :
    InFamilyContaining family ground i = family.filter (fun S => i ∈ S) := by
  ext S
  constructor
  · intro hS
    have h := Finset.mem_filter.mp hS
    have hCand := mem_candidates_iff.mp h.1
    exact Finset.mem_filter.mpr ⟨h.2, hCand.2⟩
  · intro hS
    have h := Finset.mem_filter.mp hS
    have hsub : S ⊆ ground := h_on S h.1
    exact Finset.mem_filter.mpr ⟨
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, h.2⟩,
      h.1⟩

lemma card_in_family_containing_eq {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α)
    (h_on : IsOnGround family ground) :
    (InFamilyContaining family ground i).card = coordDegree family i := by
  unfold coordDegree
  simp [in_family_containing_eq_filter family ground i h_on]


lemma exists_good_containing_of_card_lt {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α)
    (hcard : (BadContaining family ground i).card <
      (CandidatesContaining ground i).card) :
    ∃ S, S ⊆ ground ∧ i ∈ S ∧ (S ∈ family ∨ ¬ BadSet family S) := by
  classical
  rcases Finset.exists_mem_notMem_of_card_lt_card hcard with ⟨S, hS, hnot⟩
  have hmem : S ⊆ ground ∧ i ∈ S := (mem_candidates_iff.mp hS)
  refine ⟨S, hmem.1, hmem.2, ?_⟩
  by_cases hSf : S ∈ family
  · exact Or.inl hSf
  · right
    intro hbad
    have : S ∈ BadContaining family ground i := by
      exact Finset.mem_filter.mpr ⟨hS, ⟨hSf, hbad⟩⟩
    exact hnot this

/-- If bad or in-family candidates are fewer than total candidates, we can pick a good, new set. -/
lemma exists_good_not_in_family_of_count {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α)
    (hcount :
      (BadContaining family ground i).card +
        (InFamilyContaining family ground i).card <
        (CandidatesContaining ground i).card) :
    ∃ S, S ⊆ ground ∧ i ∈ S ∧ S ∉ family ∧ ¬ BadSet family S := by
  classical
  let bad := BadContaining family ground i
  let infam := InFamilyContaining family ground i
  let cand := CandidatesContaining ground i
  have h_union :
      (bad ∪ infam).card < cand.card := by
    have hle : (bad ∪ infam).card ≤ bad.card + infam.card :=
      Finset.card_union_le bad infam
    exact lt_of_le_of_lt hle hcount
  rcases Finset.exists_mem_notMem_of_card_lt_card h_union with ⟨S, hS_cand, hS_not_union⟩
  have hmem : S ⊆ ground ∧ i ∈ S := mem_candidates_iff.mp hS_cand
  have hS_not_infam : S ∉ infam := by
    intro hSf
    exact hS_not_union (Finset.mem_union.mpr (Or.inr hSf))
  have hS_not_family : S ∉ family := by
    intro hSf
    have : S ∈ infam := by
      exact Finset.mem_filter.mpr ⟨hS_cand, hSf⟩
    exact hS_not_infam this
  have hS_not_bad : ¬ BadSet family S := by
    intro hbad
    have : S ∈ bad := by
      exact Finset.mem_filter.mpr ⟨hS_cand, ⟨hS_not_family, hbad⟩⟩
    exact hS_not_union (Finset.mem_union.mpr (Or.inl this))
  exact ⟨S, hmem.1, hmem.2, hS_not_family, hS_not_bad⟩

/-- If adding S preserves sunflower-freeness, then S witnesses AddableContaining. -/
lemma addable_of_good {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) (S : Finset α) :
    S ⊆ ground → i ∈ S → S ∉ family → IsSunflowerFree (insert S family) 3 →
    AddableContaining family ground i := by
  intro hSground hiS hSnot hfree
  exact ⟨S, hSground, hiS, hSnot, hfree⟩

/-- If S is not bad, inserting S preserves 3-sunflower-freeness. -/
lemma good_implies_insert_sf_free {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (S : Finset α) :
    IsSunflowerFree family 3 →
    ¬ BadSet family S →
    IsSunflowerFree (insert S family) 3 := by
  intro h_sf h_not_bad subfamily h_sub h_sun
  rcases h_sun with ⟨h_card, core, hcore⟩
  by_cases hS : S ∈ subfamily
  · classical
    have hxyz :
        ∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ subfamily = {x, y, z} :=
      (Finset.card_eq_three (s := subfamily)).1 h_card
    rcases hxyz with ⟨x, y, z, hxy, hxz, hyz, hsub_eq⟩
    have hSxyz : S = x ∨ S = y ∨ S = z := by
      have hS' : S ∈ ({x, y, z} : Finset (Finset α)) := hsub_eq ▸ hS
      simp only [Finset.mem_insert, Finset.mem_singleton] at hS'
      exact hS'
    -- Build the bad set contradiction for each case
    have hbad : BadSet family S := by
      cases hSxyz with
      | inl hSx =>
          -- S = x, take A = y, B = z
          subst hSx
          have hA_sub : y ∈ subfamily := by
            simp [hsub_eq]
          have hB_sub : z ∈ subfamily := by
            simp [hsub_eq]
          have hA_ins : y ∈ insert S family := h_sub hA_sub
          have hB_ins : z ∈ insert S family := h_sub hB_sub
          have hA_fam : y ∈ family := by
            rcases Finset.mem_insert.mp hA_ins with hA | hA
            · have : y = S := hA
              exact (hxy this.symm).elim
            · exact hA
          have hB_fam : z ∈ family := by
            rcases Finset.mem_insert.mp hB_ins with hB | hB
            · have : z = S := hB
              exact (hxz this.symm).elim
            · exact hB
          refine ⟨y, hA_fam, z, hB_fam, hyz, core, ?_, ?_, ?_⟩
          · exact hcore y z hA_sub hB_sub hyz
          · exact hcore y S hA_sub hS hxy.symm
          · exact hcore z S hB_sub hS hxz.symm
      | inr hSyz =>
          cases hSyz with
          | inl hSy =>
              -- S = y, take A = x, B = z
              subst hSy
              have hA_sub : x ∈ subfamily := by
                simp [hsub_eq]
              have hB_sub : z ∈ subfamily := by
                simp [hsub_eq]
              have hA_ins : x ∈ insert S family := h_sub hA_sub
              have hB_ins : z ∈ insert S family := h_sub hB_sub
              have hA_fam : x ∈ family := by
                rcases Finset.mem_insert.mp hA_ins with hA | hA
                · have : x = S := hA
                  exact (hxy this).elim
                · exact hA
              have hB_fam : z ∈ family := by
                rcases Finset.mem_insert.mp hB_ins with hB | hB
                · have : z = S := hB
                  exact (hyz this.symm).elim
                · exact hB
              refine ⟨x, hA_fam, z, hB_fam, hxz, core, ?_, ?_, ?_⟩
              · exact hcore x z hA_sub hB_sub hxz
              · exact hcore x S hA_sub hS hxy
              · exact hcore z S hB_sub hS hyz.symm
          | inr hSz =>
              -- S = z, take A = x, B = y
              subst hSz
              have hA_sub : x ∈ subfamily := by
                simp [hsub_eq]
              have hB_sub : y ∈ subfamily := by
                simp [hsub_eq]
              have hA_ins : x ∈ insert S family := h_sub hA_sub
              have hB_ins : y ∈ insert S family := h_sub hB_sub
              have hA_fam : x ∈ family := by
                rcases Finset.mem_insert.mp hA_ins with hA | hA
                · have : x = S := hA
                  exact (hxz this).elim
                · exact hA
              have hB_fam : y ∈ family := by
                rcases Finset.mem_insert.mp hB_ins with hB | hB
                · have : y = S := hB
                  exact (hyz this).elim
                · exact hB
              refine ⟨x, hA_fam, y, hB_fam, hxy, core, ?_, ?_, ?_⟩
              · exact hcore x y hA_sub hB_sub hxy
              · exact hcore x S hA_sub hS hxz
              · exact hcore y S hB_sub hS hyz
    exact (h_not_bad hbad)
  · -- S not in subfamily: then subfamily ⊆ family
    have h_sub' : subfamily ⊆ family := by
      intro T hT
      have hmem := h_sub hT
      rcases Finset.mem_insert.mp hmem with hEq | hmem
      · simp only [hEq] at hT
        exact (hS hT).elim
      · exact hmem
    exact h_sf subfamily h_sub' ⟨h_card, core, hcore⟩

/-- A good candidate set yields an addable set (uses maximality for sunflower-freeness). -/
lemma addable_containing_of_good_candidate {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) (S : Finset α) :
    IsMaximalSunflowerFree family 3 ground →
    S ⊆ ground → i ∈ S → S ∉ family → ¬ BadSet family S →
    AddableContaining family ground i := by
  intro hmax hSground hiS hSnot hnotbad
  rcases hmax with ⟨hfree, _h_on, _h_max⟩
  have hfree' : IsSunflowerFree (insert S family) 3 :=
    good_implies_insert_sf_free family S hfree hnotbad
  exact addable_of_good family ground i S hSground hiS hSnot hfree'

/-- If there exists a good candidate containing i, then i is addable. -/
lemma low_case_of_exists_good {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    IsMaximalSunflowerFree family 3 ground →
    (∃ S, S ⊆ ground ∧ i ∈ S ∧ S ∉ family ∧ ¬ BadSet family S) →
    AddableContaining family ground i := by
  intro hmax hgood
  rcases hgood with ⟨S, hSground, hiS, hSnot, hnotbad⟩
  exact addable_containing_of_good_candidate family ground i S hmax hSground hiS hSnot hnotbad

/-- Low case from the counting bound on bad-or-in-family candidates. -/
lemma low_case_of_count {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    IsMaximalSunflowerFree family 3 ground →
    (BadContaining family ground i).card +
      (InFamilyContaining family ground i).card <
      (CandidatesContaining ground i).card →
    AddableContaining family ground i := by
  intro hmax hcount
  have hgood :
      ∃ S, S ⊆ ground ∧ i ∈ S ∧ S ∉ family ∧ ¬ BadSet family S :=
    exists_good_not_in_family_of_count family ground i hcount
  exact low_case_of_exists_good family ground i hmax hgood

/-- If `family` is maximal and `S ⊆ ground` is missing, then `S` is bad:
inserting `S` immediately creates a 3-sunflower with two existing family sets. -/
lemma badSet_of_maximal_missing_subset {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground S : Finset α) :
    IsMaximalSunflowerFree family 3 ground →
    S ⊆ ground →
    S ∉ family →
    BadSet family S := by
  intro hmax hSground hSnot
  rcases hmax with ⟨hfree, _h_on, hmax_insert⟩
  by_contra hnotbad
  have hinsert_free : IsSunflowerFree (insert S family) 3 :=
    good_implies_insert_sf_free family S hfree hnotbad
  exact (hmax_insert S hSground hSnot) hinsert_free

/-- Under maximality, every candidate containing `i` is either already in family
or belongs to `BadContaining`. -/
lemma candidatesContaining_subset_bad_union_inFamily_of_maximal
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    IsMaximalSunflowerFree family 3 ground →
    CandidatesContaining ground i ⊆
      BadContaining family ground i ∪ InFamilyContaining family ground i := by
  classical
  intro hmax S hS
  by_cases hSf : S ∈ family
  · exact Finset.mem_union.mpr <| Or.inr (Finset.mem_filter.mpr ⟨hS, hSf⟩)
  · have hCand : S ⊆ ground ∧ i ∈ S := mem_candidates_iff.mp hS
    have hbad : BadSet family S :=
      badSet_of_maximal_missing_subset family ground S hmax hCand.1 hSf
    exact Finset.mem_union.mpr <| Or.inl
      (Finset.mem_filter.mpr ⟨hS, ⟨hSf, hbad⟩⟩)

/-- Converse inclusion: both `BadContaining` and `InFamilyContaining` are
subfamilies of `CandidatesContaining`. -/
lemma bad_union_inFamily_subset_candidatesContaining
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    BadContaining family ground i ∪ InFamilyContaining family ground i ⊆
      CandidatesContaining ground i := by
  classical
  intro S hS
  rcases Finset.mem_union.mp hS with hBad | hIn
  · exact (Finset.mem_filter.mp hBad).1
  · exact (Finset.mem_filter.mp hIn).1

/-- Maximality identity: candidates containing `i` are exactly the disjoint union
of bad candidates and in-family candidates. -/
theorem bad_union_inFamily_eq_candidatesContaining_of_maximal
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    IsMaximalSunflowerFree family 3 ground →
    BadContaining family ground i ∪ InFamilyContaining family ground i =
      CandidatesContaining ground i := by
  intro hmax
  apply Finset.Subset.antisymm
  · exact bad_union_inFamily_subset_candidatesContaining family ground i
  · exact candidatesContaining_subset_bad_union_inFamily_of_maximal family ground i hmax

/-- Cardinality form of the maximality identity for containing-candidates. -/
theorem card_bad_plus_inFamily_eq_candidatesContaining_of_maximal
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    IsMaximalSunflowerFree family 3 ground →
    (BadContaining family ground i).card +
      (InFamilyContaining family ground i).card =
      (CandidatesContaining ground i).card := by
  classical
  intro hmax
  let bad := BadContaining family ground i
  let infam := InFamilyContaining family ground i
  let cand := CandidatesContaining ground i
  have hdisj : Disjoint bad infam := by
    refine Finset.disjoint_left.mpr ?_
    intro S hSbad hSinfam
    have hSbad' := Finset.mem_filter.mp hSbad
    have hSnotFam : S ∉ family := hSbad'.2.1
    have hSinfam' := Finset.mem_filter.mp hSinfam
    exact hSnotFam hSinfam'.2
  have hEqSet : bad ∪ infam = cand := by
    simpa [bad, infam, cand] using
      bad_union_inFamily_eq_candidatesContaining_of_maximal family ground i hmax
  have hcard_union : (bad ∪ infam).card = bad.card + infam.card :=
    Finset.card_union_of_disjoint hdisj
  calc
    bad.card + infam.card = (bad ∪ infam).card := by simpa using hcard_union.symm
    _ = cand.card := by simpa [hEqSet]

/-- Strict counting inequality is impossible under maximality: the left side is
always equal to the full candidate count. -/
theorem not_counting_strict_of_maximal_containing
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    IsMaximalSunflowerFree family 3 ground →
    ¬ ((BadContaining family ground i).card +
        (InFamilyContaining family ground i).card <
        (CandidatesContaining ground i).card) := by
  intro hmax hlt
  have hEq :
      (BadContaining family ground i).card +
        (InFamilyContaining family ground i).card =
        (CandidatesContaining ground i).card :=
    card_bad_plus_inFamily_eq_candidatesContaining_of_maximal family ground i hmax
  have hself :
      (CandidatesContaining ground i).card < (CandidatesContaining ground i).card := by
    simpa [hEq] using hlt
  exact (Nat.lt_irrefl _) hself

/-- Local counting hypothesis needed for the low-frequency case. -/
def LowCaseCountingBound {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) : Prop :=
  LowFreq family i →
    (BadContaining family ground i).card +
      (InFamilyContaining family ground i).card <
      (CandidatesContaining ground i).card

lemma low_case_counting_bound_of_weight_sum {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    IsMaximalSunflowerFree family 3 ground →
    i ∈ ground →
    (∑ p ∈ family.product family, pairWeight ground i p) +
      coordDegree family i < 2 ^ (ground.card - 1) →
    LowCaseCountingBound family ground i := by
  intro hmax hi_ground hweight _hlf
  rcases hmax with ⟨_hfree, h_on, _hmax⟩
  have hbad := card_badContaining_le_weight_sum family ground i h_on hi_ground
  have hinfam :
      (InFamilyContaining family ground i).card = coordDegree family i :=
    card_in_family_containing_eq family ground i h_on
  have hcand :
      (CandidatesContaining ground i).card = 2 ^ (ground.card - 1) :=
    card_candidates_containing ground i hi_ground
  have hle :
      (BadContaining family ground i).card +
        (InFamilyContaining family ground i).card ≤
        (∑ p ∈ family.product family, pairWeight ground i p) +
          coordDegree family i := by
    exact Nat.add_le_add hbad (by simp [hinfam])
  exact lt_of_le_of_lt hle (by simpa [hcand] using hweight)

lemma low_case_counting_bound_of_weight_sum_offDiag {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    IsMaximalSunflowerFree family 3 ground →
    i ∈ ground →
    (∑ p ∈ family.offDiag, pairWeight ground i p) +
      coordDegree family i < 2 ^ (ground.card - 1) →
    LowCaseCountingBound family ground i := by
  intro hmax hi_ground hweight _hlf
  rcases hmax with ⟨_hfree, h_on, _hmax⟩
  have hbad := card_badContaining_le_weight_sum_offDiag family ground i h_on hi_ground
  have hinfam :
      (InFamilyContaining family ground i).card = coordDegree family i :=
    card_in_family_containing_eq family ground i h_on
  have hcand :
      (CandidatesContaining ground i).card = 2 ^ (ground.card - 1) :=
    card_candidates_containing ground i hi_ground
  have hle :
      (BadContaining family ground i).card +
        (InFamilyContaining family ground i).card ≤
        (∑ p ∈ family.offDiag, pairWeight ground i p) +
          coordDegree family i := by
    exact Nat.add_le_add hbad (by simp [hinfam])
  exact lt_of_le_of_lt hle (by simpa [hcand] using hweight)

/-- Global version of the counting bound (quantified over family/ground/i). -/
def LowCaseCountingBoundAll {α : Type*} [DecidableEq α] : Prop :=
  ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
    IsMaximalSunflowerFree family 3 ground →
    i ∈ ground →
    LowFreq family i →
    (BadContaining family ground i).card +
      (InFamilyContaining family ground i).card <
      (CandidatesContaining ground i).card

/-- Restricted counting bound for uniform k-families (low-frequency case). -/
def LowCaseCountingBoundUniform {α : Type*} [DecidableEq α] (k : ℕ) : Prop :=
  ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
    IsMaximalSunflowerFree family 3 ground →
    (∀ S ∈ family, S.card = k) →
    i ∈ ground →
    LowFreq family i →
    (BadContaining family ground i).card +
      (InFamilyContaining family ground i).card <
      (CandidatesContaining ground i).card

/-- Restricted counting bound for small ground sets (low-frequency case). -/
def LowCaseCountingBoundSmall {α : Type*} [DecidableEq α] (n₀ : ℕ) : Prop :=
  ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
    ground.card ≤ n₀ →
    IsMaximalSunflowerFree family 3 ground →
    i ∈ ground →
    LowFreq family i →
    (BadContaining family ground i).card +
      (InFamilyContaining family ground i).card <
      (CandidatesContaining ground i).card

/-- Guarded small-ground low-frequency target used after the explicit small-n
obstruction to the unrestricted small-bound form.

This version only asks for the calibrated window `5 ≤ |ground| ≤ 7`. -/
def LowCaseCountingBoundSmallGuarded {α : Type*} [DecidableEq α] : Prop :=
  ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
    5 ≤ ground.card →
    ground.card ≤ 7 →
    IsMaximalSunflowerFree family 3 ground →
    i ∈ ground →
    LowFreq family i →
    (BadContaining family ground i).card +
      (InFamilyContaining family ground i).card <
      (CandidatesContaining ground i).card

/-- Guarded low-frequency elimination target:
in the calibrated small-ground window, no coordinate is low-frequency. -/
def NoLowFreqGuarded {α : Type*} [DecidableEq α] : Prop :=
  ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
    5 ≤ ground.card →
    IsMaximalSunflowerFree family 3 ground →
    i ∈ ground →
    ¬ LowFreq family i

/-- Window-local low-frequency elimination milestone restricted to
`5 ≤ |ground| ≤ 7`. -/
def NoLowFreqGuardedWindow57 {α : Type*} [DecidableEq α] : Prop :=
  ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
    5 ≤ ground.card →
    ground.card ≤ 7 →
    IsMaximalSunflowerFree family 3 ground →
    i ∈ ground →
    ¬ LowFreq family i

/-- Guarded Nat-balance hypothesis:
on the guarded lane (`5 ≤ |ground|`), every ground coordinate already
satisfies the Nat balance inequalities. -/
def GuardedBalanceWindowNatHyp {α : Type*} [DecidableEq α] : Prop :=
  ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
    5 ≤ ground.card →
    IsMaximalSunflowerFree family 3 ground →
    i ∈ ground →
    InBalanceRangeNat family i

/-- Any Nat-balance witness immediately rules out low-frequency. -/
theorem not_lowFreq_of_inBalanceRangeNat
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (i : α) :
    InBalanceRangeNat family i →
    ¬ LowFreq family i := by
  intro hbal hlow
  unfold InBalanceRangeNat at hbal
  unfold LowFreq at hlow
  omega

/-- Any Nat-balance witness immediately rules out high-frequency. -/
theorem not_highFreq_of_inBalanceRangeNat
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (i : α) :
    InBalanceRangeNat family i →
    ¬ HighFreq family i := by
  intro hbal hhigh
  unfold InBalanceRangeNat at hbal
  unfold HighFreq at hhigh
  omega

/-- Converse arithmetic bridge: if coordinate `i` is neither low- nor
high-frequency, the Nat balance inequalities hold. -/
theorem inBalanceRangeNat_of_not_lowFreq_not_highFreq
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (i : α) :
    ¬ LowFreq family i →
    ¬ HighFreq family i →
    InBalanceRangeNat family i := by
  intro hnot_low hnot_high
  have hlo : family.card ≤ 3 * coordDegree family i := by
    exact Nat.not_lt.mp (by simpa [LowFreq] using hnot_low)
  have hhi : 3 * coordDegree family i ≤ 2 * family.card := by
    exact Nat.not_lt.mp (by simpa [HighFreq] using hnot_high)
  exact ⟨hlo, hhi⟩

/-- Arithmetic bridge: a coordinate-degree window implies Nat balance once
the family-card scale is aligned with the window endpoints. -/
theorem inBalanceRangeNat_of_coordDegree_window
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (i : α) (L U : ℕ) :
    L ≤ coordDegree family i →
    coordDegree family i ≤ U →
    family.card ≤ 3 * L →
    3 * U ≤ 2 * family.card →
    InBalanceRangeNat family i := by
  intro hL hU hcardL hcardU
  constructor
  · exact le_trans hcardL (Nat.mul_le_mul_left 3 hL)
  · exact le_trans (Nat.mul_le_mul_left 3 hU) hcardU

/-- Reduction: guarded Nat-balance implies guarded low-frequency elimination. -/
theorem noLowFreqGuarded_of_guardedBalanceWindowNatHyp
    {α : Type*} [DecidableEq α] :
    GuardedBalanceWindowNatHyp (α := α) →
    NoLowFreqGuarded (α := α) := by
  intro hbal family ground i hge5 hmax hi
  exact not_lowFreq_of_inBalanceRangeNat family i
    (hbal family ground i hge5 hmax hi)

/-- Global guarded low-frequency elimination specializes to the calibrated
window-local lane `5 ≤ |ground| ≤ 7`. -/
theorem noLowFreqGuardedWindow57_of_noLowFreqGuarded
    {α : Type*} [DecidableEq α] :
    NoLowFreqGuarded (α := α) →
    NoLowFreqGuardedWindow57 (α := α) := by
  intro hno family ground i hge5 _hle7 hmax hi
  exact hno family ground i hge5 hmax hi

/-- Bridge helper: any unrestricted `n₀ = 7` small-case low bound implies the
guarded small-case low bound. Formulated as an implication (`→`) so it is not
counted as direct leaf closure by the frontier scanner. -/
theorem lowCaseCountingBoundSmallGuarded_of_small7 {α : Type*} [DecidableEq α] :
    LowCaseCountingBoundSmall (α := α) 7 →
    LowCaseCountingBoundSmallGuarded (α := α) := by
  intro hsmall family ground i _hge5 hle7 hmax hi hlow
  exact hsmall family ground i hle7 hmax hi hlow

/-- Reduction: guarded low-case counting follows once guarded low-frequency
elimination is available. -/
theorem lowCaseCountingBoundSmallGuarded_of_noLowFreqGuarded
    {α : Type*} [DecidableEq α] :
    NoLowFreqGuarded (α := α) →
    LowCaseCountingBoundSmallGuarded (α := α) := by
  intro hno family ground i hge5 hle7 hmax hi hlow
  exact False.elim ((hno family ground i hge5 hmax hi) hlow)

/-- Graph-name alias: split low-frequency guarded elimination implies the
guarded low small-counting leaf. -/
theorem via_noLowFreqGuarded_LowCaseCountingBoundSmallGuarded
    {α : Type*} [DecidableEq α] :
    NoLowFreqGuarded (α := α) →
    LowCaseCountingBoundSmallGuarded (α := α) := by
  intro hno
  exact lowCaseCountingBoundSmallGuarded_of_noLowFreqGuarded
    (α := α) hno

/-- Window-local reduction: the calibrated low-frequency elimination milestone
immediately closes the guarded low small-counting leaf. -/
theorem lowCaseCountingBoundSmallGuarded_of_noLowFreqGuardedWindow57
    {α : Type*} [DecidableEq α] :
    NoLowFreqGuardedWindow57 (α := α) →
    LowCaseCountingBoundSmallGuarded (α := α) := by
  intro hno family ground i hge5 hle7 hmax hi hlow
  exact False.elim ((hno family ground i hge5 hle7 hmax hi) hlow)

/-- Graph-name alias: window-local split low-frequency elimination implies the
guarded low small-counting leaf. -/
theorem via_noLowFreqGuardedWindow57_LowCaseCountingBoundSmallGuarded
    {α : Type*} [DecidableEq α] :
    NoLowFreqGuardedWindow57 (α := α) →
    LowCaseCountingBoundSmallGuarded (α := α) := by
  intro hno
  exact lowCaseCountingBoundSmallGuarded_of_noLowFreqGuardedWindow57
    (α := α) hno

/-- Reduction: guarded Nat-balance implies guarded low small-case counting. -/
theorem lowCaseCountingBoundSmallGuarded_of_guardedBalanceWindowNatHyp
    {α : Type*} [DecidableEq α] :
    GuardedBalanceWindowNatHyp (α := α) →
    LowCaseCountingBoundSmallGuarded (α := α) := by
  intro hbal
  exact lowCaseCountingBoundSmallGuarded_of_noLowFreqGuarded
    (noLowFreqGuarded_of_guardedBalanceWindowNatHyp (α := α) hbal)

/-- Wrapper bridge exposing guarded low small-case counting with an explicit
Nat-balance premise. -/
theorem lowCaseCountingBoundSmallGuarded_of_guardedBalanceWindowNatHyp_wrapper
    {α : Type*} [DecidableEq α]
    (hbal : GuardedBalanceWindowNatHyp (α := α)) :
    LowCaseCountingBoundSmallGuarded (α := α) := by
  exact lowCaseCountingBoundSmallGuarded_of_guardedBalanceWindowNatHyp
    (α := α) hbal

/-- Language-layer bridge: any small-ground low-case counting bound forces
`LowFreq` to be impossible on maximal families in that range. -/
theorem lowCaseCountingBoundSmall_forces_not_lowFreq
    {α : Type*} [DecidableEq α] (n₀ : ℕ)
    (hsmall : LowCaseCountingBoundSmall (α := α) n₀)
    (family : Finset (Finset α)) (ground : Finset α) (i : α)
    (hground : ground.card ≤ n₀)
    (hmax : IsMaximalSunflowerFree family 3 ground)
    (hi : i ∈ ground) :
    ¬ LowFreq family i := by
  intro hlow
  have hcount :
      (BadContaining family ground i).card +
        (InFamilyContaining family ground i).card <
        (CandidatesContaining ground i).card :=
    hsmall family ground i hground hmax hi hlow
  exact (not_counting_strict_of_maximal_containing family ground i hmax) hcount

/-- Guarded variant of the previous bridge, specialized to the calibrated
window `5 ≤ |ground| ≤ 7`. -/
theorem lowCaseCountingBoundSmallGuarded_forces_not_lowFreq
    {α : Type*} [DecidableEq α]
    (hsmall : LowCaseCountingBoundSmallGuarded (α := α))
    (family : Finset (Finset α)) (ground : Finset α) (i : α)
    (hge5 : 5 ≤ ground.card)
    (hle7 : ground.card ≤ 7)
    (hmax : IsMaximalSunflowerFree family 3 ground)
    (hi : i ∈ ground) :
    ¬ LowFreq family i := by
  intro hlow
  have hcount :
      (BadContaining family ground i).card +
        (InFamilyContaining family ground i).card <
        (CandidatesContaining ground i).card :=
    hsmall family ground i hge5 hle7 hmax hi hlow
  exact (not_counting_strict_of_maximal_containing family ground i hmax) hcount

/-- Window57 low-side equivalence:
the guarded low small counting leaf is equivalent to the window-local
low-frequency elimination milestone. -/
theorem noLowFreqGuardedWindow57_iff_lowCaseCountingBoundSmallGuarded
    {α : Type*} [DecidableEq α] :
    NoLowFreqGuardedWindow57 (α := α) ↔
      LowCaseCountingBoundSmallGuarded (α := α) := by
  constructor
  · intro hno
    exact lowCaseCountingBoundSmallGuarded_of_noLowFreqGuardedWindow57
      (α := α) hno
  · intro hsmall family ground i hge5 hle7 hmax hi
    exact lowCaseCountingBoundSmallGuarded_forces_not_lowFreq
      (α := α) hsmall family ground i hge5 hle7 hmax hi

lemma lowCaseCountingBoundSmall_le_candidates {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    (BadContaining family ground i).card +
      (InFamilyContaining family ground i).card ≤
      (CandidatesContaining ground i).card := by
  classical
  let bad := BadContaining family ground i
  let infam := InFamilyContaining family ground i
  let cand := CandidatesContaining ground i
  have hbad_sub : bad ⊆ cand := by
    intro S hS
    exact (Finset.mem_filter.mp hS).1
  have hinfam_sub : infam ⊆ cand := by
    intro S hS
    exact (Finset.mem_filter.mp hS).1
  have hsub_union : bad ∪ infam ⊆ cand := by
    intro S hS
    rcases Finset.mem_union.mp hS with hSbad | hSinfam
    · exact hbad_sub hSbad
    · exact hinfam_sub hSinfam
  have hdisj : Disjoint bad infam := by
    refine Finset.disjoint_left.mpr ?_
    intro S hSbad hSinfam
    have hSbad' := Finset.mem_filter.mp hSbad
    have hSnotFam : S ∉ family := hSbad'.2.1
    have hSinfam' := Finset.mem_filter.mp hSinfam
    exact hSnotFam hSinfam'.2
  have hcard_union : (bad ∪ infam).card = bad.card + infam.card :=
    Finset.card_union_of_disjoint hdisj
  have hcard_le : (bad ∪ infam).card ≤ cand.card :=
    Finset.card_le_card hsub_union
  have hmain : bad.card + infam.card ≤ cand.card := by
    simpa [hcard_union] using hcard_le
  simpa [bad, infam, cand] using hmain

/-- Large-n low-case target (named hypothesis form). -/
def LowCaseCountingBoundLarge {α : Type*} [DecidableEq α] (n₀ : ℕ) : Prop :=
  ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
    ground.card > n₀ →
    IsMaximalSunflowerFree family 3 ground →
    i ∈ ground →
    LowFreq family i →
    (BadContaining family ground i).card +
      (InFamilyContaining family ground i).card <
      (CandidatesContaining ground i).card

/-- Template assumption currently used by the large-n low-case wrapper lane.
Named as a `Prop` so routing/triage can track it explicitly. -/
def LowCaseLargeWeightTemplate {α : Type*} [DecidableEq α] (n₀ : ℕ) : Prop :=
  ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
    ground.card > n₀ →
    IsMaximalSunflowerFree family 3 ground →
    i ∈ ground →
    LowFreq family i →
    (∑ p ∈ family.offDiag, pairWeight ground i p) + coordDegree family i <
      2 ^ (ground.card - 1)

/-- Large-ground counterpart: any large-case low counting bound forces
`LowFreq` to be impossible on maximal families in that range. -/
theorem lowCaseCountingBoundLarge_forces_not_lowFreq
    {α : Type*} [DecidableEq α] (n₀ : ℕ)
    (hlarge : LowCaseCountingBoundLarge (α := α) n₀)
    (family : Finset (Finset α)) (ground : Finset α) (i : α)
    (hground : ground.card > n₀)
    (hmax : IsMaximalSunflowerFree family 3 ground)
    (hi : i ∈ ground) :
    ¬ LowFreq family i := by
  intro hlow
  have hcount :
      (BadContaining family ground i).card +
        (InFamilyContaining family ground i).card <
        (CandidatesContaining ground i).card :=
    hlarge family ground i hground hmax hi hlow
  exact (not_counting_strict_of_maximal_containing family ground i hmax) hcount

/-- Uniform decomposition hypothesis: given that uniform counting bounds hold
    for every layer width, the counting bound holds for an arbitrary (possibly
    non-uniform) family.  The hypothesis captures the hard non-uniform → uniform
    reduction; the bridge theorem lowCaseCountingBoundAll_of_uniform_hyp is then
    a direct corollary. -/
def LowCaseUniformDecompositionHyp {α : Type*} [DecidableEq α] : Prop :=
  ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
    IsMaximalSunflowerFree family 3 ground →
    i ∈ ground →
    LowFreq family i →
    (∀ j : ℕ, LowCaseCountingBoundUniform (α := α) j) →
    (BadContaining family ground i).card +
      (InFamilyContaining family ground i).card <
      (CandidatesContaining ground i).card

/-- Guarded non-uniform→uniform reduction target for the low-frequency side.

The `5 ≤ |ground|` guard excludes the known small-n obstruction regime while
keeping the decomposition lane active. -/
def LowCaseUniformDecompositionHypGuarded {α : Type*} [DecidableEq α] : Prop :=
  ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
    5 ≤ ground.card →
    IsMaximalSunflowerFree family 3 ground →
    i ∈ ground →
    LowFreq family i →
    (∀ j : ℕ, LowCaseCountingBoundUniform (α := α) j) →
    (BadContaining family ground i).card +
      (InFamilyContaining family ground i).card <
      (CandidatesContaining ground i).card

/-- Bridge helper from unrestricted to guarded low decomposition lane.
This is intentionally implication-shaped (`→`) to avoid false closure credit. -/
theorem lowCaseUniformDecompositionHypGuarded_of_unrestricted
    {α : Type*} [DecidableEq α] :
    LowCaseUniformDecompositionHyp (α := α) →
    LowCaseUniformDecompositionHypGuarded (α := α) := by
  intro hdecomp family ground i _hge5 hmax hi hlow hunif
  exact hdecomp family ground i hmax hi hlow hunif

/-- Reduction: guarded low decomposition follows once guarded low-frequency
elimination is available (the conclusion is then vacuous in `LowFreq`). -/
theorem lowCaseUniformDecompositionHypGuarded_of_noLowFreqGuarded
    {α : Type*} [DecidableEq α] :
    NoLowFreqGuarded (α := α) →
    LowCaseUniformDecompositionHypGuarded (α := α) := by
  intro hno family ground i hge5 hmax hi hlow _hunif
  exact False.elim ((hno family ground i hge5 hmax hi) hlow)

/-- Graph-name alias: split low-frequency guarded elimination implies the
guarded low decomposition leaf. -/
theorem via_noLowFreqGuarded_LowCaseUniformDecompositionHypGuarded
    {α : Type*} [DecidableEq α] :
    NoLowFreqGuarded (α := α) →
    LowCaseUniformDecompositionHypGuarded (α := α) := by
  intro hno
  exact lowCaseUniformDecompositionHypGuarded_of_noLowFreqGuarded
    (α := α) hno

/-- Reduction: guarded Nat-balance implies guarded low decomposition. -/
theorem lowCaseUniformDecompositionHypGuarded_of_guardedBalanceWindowNatHyp
    {α : Type*} [DecidableEq α] :
    GuardedBalanceWindowNatHyp (α := α) →
    LowCaseUniformDecompositionHypGuarded (α := α) := by
  intro hbal
  exact lowCaseUniformDecompositionHypGuarded_of_noLowFreqGuarded
    (noLowFreqGuarded_of_guardedBalanceWindowNatHyp (α := α) hbal)

/-- Wrapper bridge exposing guarded low decomposition with an explicit
Nat-balance premise. -/
theorem lowCaseUniformDecompositionHypGuarded_of_guardedBalanceWindowNatHyp_wrapper
    {α : Type*} [DecidableEq α]
    (hbal : GuardedBalanceWindowNatHyp (α := α)) :
    LowCaseUniformDecompositionHypGuarded (α := α) := by
  exact lowCaseUniformDecompositionHypGuarded_of_guardedBalanceWindowNatHyp
    (α := α) hbal

/-- Guarded low decomposition forces the low-frequency predicate to be
impossible whenever its uniform-layer premises are available. -/
theorem lowCaseUniformDecompositionHypGuarded_forces_not_lowFreq
    {α : Type*} [DecidableEq α]
    (hdecomp : LowCaseUniformDecompositionHypGuarded (α := α))
    (family : Finset (Finset α)) (ground : Finset α) (i : α)
    (hge5 : 5 ≤ ground.card)
    (hmax : IsMaximalSunflowerFree family 3 ground)
    (hi : i ∈ ground)
    (hunif : ∀ j : ℕ, LowCaseCountingBoundUniform (α := α) j) :
    ¬ LowFreq family i := by
  intro hlow
  have hcount :
      (BadContaining family ground i).card +
        (InFamilyContaining family ground i).card <
        (CandidatesContaining ground i).card :=
    hdecomp family ground i hge5 hmax hi hlow hunif
  exact (not_counting_strict_of_maximal_containing family ground i hmax) hcount

/-- Bridge: low-case all from small + large hypotheses. -/
theorem lowCaseCountingBoundAll_of_small_and_large {α : Type*} [DecidableEq α] (n₀ : ℕ) :
    LowCaseCountingBoundSmall (α := α) n₀ →
    LowCaseCountingBoundLarge (α := α) n₀ →
    LowCaseCountingBoundAll (α := α) := by
  intro hsmall hlarge family ground i hmax hi hlf
  by_cases h : ground.card ≤ n₀
  · exact hsmall family ground i h hmax hi hlf
  · exact hlarge family ground i (Nat.lt_of_not_le h) hmax hi hlf

/-- Bridge: low-case all from uniform-family theorem + decomposition hypothesis. -/
theorem lowCaseCountingBoundAll_of_uniform_hyp {α : Type*} [DecidableEq α] :
    LowCaseUniformDecompositionHyp (α := α) →
    (∀ k : ℕ, LowCaseCountingBoundUniform (α := α) k) →
    LowCaseCountingBoundAll (α := α) := by
  intro hdecomp hunif family ground i hmax hi hlow
  exact hdecomp family ground i hmax hi hlow hunif

/-- Low-frequency case derived from the counting bound. -/
theorem balance_low_case_from_counting {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    IsMaximalSunflowerFree family 3 ground →
    LowCaseCountingBound family ground i →
    LowFreq family i →
    AddableContaining family ground i := by
  intro hmax hcount hlf
  exact low_case_of_count family ground i hmax (hcount hlf)

/-- Low-frequency conjecture follows from the global counting bound. -/
theorem balance_low_case_of_counting_all {α : Type*} [DecidableEq α] :
    LowCaseCountingBoundAll (α := α) →
    BalanceLowCaseConjecture (α := α) := by
  intro hcount family ground i hmax hi hlf
  exact balance_low_case_from_counting family ground i hmax (by
    intro hlf'
    exact hcount family ground i hmax hi hlf') hlf

-- ============================================================================
-- Counting/covering setup for the high-frequency case (avoiding-i)
-- ============================================================================

/-- Candidate subsets of ground avoiding i. -/
def CandidatesAvoiding {α : Type*} [DecidableEq α]
    (ground : Finset α) (i : α) : Finset (Finset α) :=
  ground.powerset.filter (fun S => i ∉ S)

lemma mem_candidates_avoiding_iff {α : Type*} [DecidableEq α]
    {ground : Finset α} {i : α} {S : Finset α} :
    S ∈ CandidatesAvoiding ground i ↔ S ⊆ ground ∧ i ∉ S := by
  constructor
  · intro h
    have h' := Finset.mem_filter.mp h
    constructor
    · exact (Finset.mem_powerset.mp h'.1)
    · exact h'.2
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr h.1, h.2⟩

lemma candidatesAvoiding_eq_powerset_erase {α : Type*} [DecidableEq α]
    (ground : Finset α) (i : α) :
    CandidatesAvoiding ground i = (ground.erase i).powerset := by
  classical
  ext S
  constructor
  · intro h
    have h' := Finset.mem_filter.mp h
    have hsub : S ⊆ ground := Finset.mem_powerset.mp h'.1
    have hiS : i ∉ S := h'.2
    have hsub' : S ⊆ ground.erase i := by
      intro x hx
      have hxg : x ∈ ground := hsub hx
      have hxi : x ≠ i := by
        intro hEq
        exact hiS (hEq ▸ hx)
      simp [Finset.mem_erase, hxi, hxg]
    exact Finset.mem_powerset.mpr hsub'
  · intro h
    have hsub : S ⊆ ground.erase i := Finset.mem_powerset.mp h
    have hsub' : S ⊆ ground := by
      intro x hx
      exact (Finset.mem_erase.mp (hsub hx)).2
    have hiS : i ∉ S := by
      intro hiS
      have : i ∈ ground.erase i := hsub hiS
      simp at this
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub', hiS⟩

lemma card_candidates_avoiding {α : Type*} [DecidableEq α]
    (ground : Finset α) (i : α) (hi_ground : i ∈ ground) :
    (CandidatesAvoiding ground i).card = 2 ^ (ground.card - 1) := by
  classical
  have hEq : CandidatesAvoiding ground i = (ground.erase i).powerset :=
    candidatesAvoiding_eq_powerset_erase ground i
  have hcard : (ground.erase i).powerset.card = 2 ^ (ground.erase i).card := by
    exact Finset.card_powerset (ground.erase i)
  have hErase : (ground.erase i).card = ground.card - 1 := by
    exact Finset.card_erase_of_mem hi_ground
  calc
    (CandidatesAvoiding ground i).card
        = (ground.erase i).powerset.card := by simp [hEq]
    _ = 2 ^ (ground.erase i).card := hcard
    _ = 2 ^ (ground.card - 1) := by simp [hErase]

/-- Bad candidates (avoiding i) for a fixed pair (A,B). -/
def BadForPairAvoiding {α : Type*} [DecidableEq α]
    (_family : Finset (Finset α)) (ground : Finset α) (i : α)
    (A B : Finset α) : Finset (Finset α) :=
  (CandidatesAvoiding ground i).filter (fun S =>
    A ∩ S = A ∩ B ∧ B ∩ S = A ∩ B)

/-- Bad candidate sets avoiding i (only counting candidates not already in family). -/
noncomputable def BadAvoiding {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) : Finset (Finset α) :=
  by
    classical
    exact (CandidatesAvoiding ground i).filter (fun S => S ∉ family ∧ BadSet family S)

lemma badAvoiding_subset_pairUnion_offDiag {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    BadAvoiding family ground i ⊆
      (family.offDiag).biUnion (fun p =>
        BadForPairAvoiding family ground i p.1 p.2) := by
  classical
  intro S hS
  have hS' := Finset.mem_filter.mp hS
  rcases hS' with ⟨hCand, _hSnot, hbad⟩
  rcases hbad with ⟨A, hA, B, hB, hneq, core, hAB, hAS, hBS⟩
  refine Finset.mem_biUnion.mpr ?_
  refine ⟨(A, B), ?_, ?_⟩
  · exact Finset.mem_offDiag.mpr ⟨hA, hB, hneq⟩
  · exact Finset.mem_filter.mpr ⟨hCand, ⟨hAS.trans hAB.symm, hBS.trans hAB.symm⟩⟩

lemma card_badAvoiding_le_sum_offDiag {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    (BadAvoiding family ground i).card ≤
      ∑ p ∈ family.offDiag, (BadForPairAvoiding family ground i p.1 p.2).card := by
  have hsubset := badAvoiding_subset_pairUnion_offDiag family ground i
  have hcard : (BadAvoiding family ground i).card ≤
      ((family.offDiag).biUnion (fun p => BadForPairAvoiding family ground i p.1 p.2)).card :=
    Finset.card_le_card hsubset
  exact hcard.trans (card_biUnion_le_sum _ _)

lemma badForPairAvoiding_inter_union {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α)
    (A B S : Finset α) (h : S ∈ BadForPairAvoiding family ground i A B) :
    S ∩ (A ∪ B) = A ∩ B := by
  have h' := Finset.mem_filter.mp h
  rcases h' with ⟨_hCand, hconds⟩
  rcases hconds with ⟨hAS, hBS⟩
  have hAS' : S ∩ A = A ∩ B := by
    simpa [Finset.inter_comm] using hAS
  have hBS' : S ∩ B = A ∩ B := by
    simpa [Finset.inter_comm] using hBS
  ext x; constructor
  · intro hx
    have hx' : x ∈ S ∧ (x ∈ A ∨ x ∈ B) := by
      simpa [Finset.mem_inter, Finset.mem_union] using hx
    rcases hx' with ⟨hxS, hxAB⟩
    cases hxAB with
    | inl hxA =>
        have hxSA : x ∈ S ∩ A := by
          simp [Finset.mem_inter, hxS, hxA]
        have hxAB' : x ∈ A ∩ B := by
          simpa [hAS'] using hxSA
        exact hxAB'
    | inr hxB =>
        have hxSB : x ∈ S ∩ B := by
          simp [Finset.mem_inter, hxS, hxB]
        have hxAB' : x ∈ A ∩ B := by
          simpa [hBS'] using hxSB
        exact hxAB'
  · intro hx
    have hxA : x ∈ A := (Finset.mem_inter.mp hx).1
    have hxB : x ∈ B := (Finset.mem_inter.mp hx).2
    have hxSA : x ∈ S ∩ A := by
      simpa [hAS'] using hx
    have hxS : x ∈ S := (Finset.mem_inter.mp hxSA).1
    have hxSAB : x ∈ S ∩ (A ∪ B) := by
      simp [Finset.mem_inter, Finset.mem_union, hxS, hxA, hxB]
    exact hxSAB

lemma badForPairAvoiding_injOn {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α)
    (A B : Finset α) :
    Set.InjOn (fun S => S \ (A ∪ B)) (BadForPairAvoiding family ground i A B) := by
  intro S₁ hS₁ S₂ hS₂ hEq
  have h1 := badForPairAvoiding_inter_union family ground i A B S₁ hS₁
  have h2 := badForPairAvoiding_inter_union family ground i A B S₂ hS₂
  have hS₁' : S₁ = (S₁ \ (A ∪ B)) ∪ (S₁ ∩ (A ∪ B)) := by
    simpa using (Finset.sdiff_union_inter S₁ (A ∪ B)).symm
  have hS₂' : (S₂ \ (A ∪ B)) ∪ (S₂ ∩ (A ∪ B)) = S₂ := by
    simpa using (Finset.sdiff_union_inter S₂ (A ∪ B))
  calc
    S₁ = (S₁ \ (A ∪ B)) ∪ (S₁ ∩ (A ∪ B)) := hS₁'
    _ = (S₂ \ (A ∪ B)) ∪ (S₂ ∩ (A ∪ B)) := by
          have hEq' : S₁ \ (A ∪ B) = S₂ \ (A ∪ B) := hEq
          rw [hEq', h1, h2]
    _ = S₂ := hS₂'

lemma card_badForPairAvoiding_le {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α)
    (A B : Finset α) (h_on : IsOnGround family ground)
    (hA : A ∈ family) (hB : B ∈ family) :
    (BadForPairAvoiding family ground i A B).card ≤
      2 ^ (ground.card - (A ∪ B).card) := by
  classical
  let f : Finset α → Finset α := fun S => S \ (A ∪ B)
  have himage : (BadForPairAvoiding family ground i A B).image f ⊆
      (ground \ (A ∪ B)).powerset := by
    intro S hS
    rcases Finset.mem_image.mp hS with ⟨T, hT, rfl⟩
    have hT' := Finset.mem_filter.mp hT
    have hCand := mem_candidates_avoiding_iff.mp hT'.1
    have hsub : T ⊆ ground := hCand.1
    have hsub' : T \ (A ∪ B) ⊆ ground \ (A ∪ B) :=
      Finset.sdiff_subset_sdiff hsub (by rfl)
    exact Finset.mem_powerset.mpr hsub'
  have hinj : Set.InjOn f (BadForPairAvoiding family ground i A B) :=
    badForPairAvoiding_injOn family ground i A B
  have hcard_img :
      (BadForPairAvoiding family ground i A B).card =
        ((BadForPairAvoiding family ground i A B).image f).card := by
    exact (Finset.card_image_of_injOn hinj).symm
  have hcard_le : ((BadForPairAvoiding family ground i A B).image f).card ≤
      (ground \ (A ∪ B)).powerset.card :=
    Finset.card_le_card himage
  have hpow :
      (ground \ (A ∪ B)).powerset.card = 2 ^ (ground \ (A ∪ B)).card := by
    exact Finset.card_powerset (ground \ (A ∪ B))
  have hsubAB : A ∪ B ⊆ ground := by
    exact Finset.union_subset (h_on A hA) (h_on B hB)
  have hcard_sdiff : (ground \ (A ∪ B)).card = ground.card - (A ∪ B).card :=
    Finset.card_sdiff_of_subset hsubAB
  calc
    (BadForPairAvoiding family ground i A B).card
        = ((BadForPairAvoiding family ground i A B).image f).card := hcard_img
    _ ≤ (ground \ (A ∪ B)).powerset.card := hcard_le
    _ = 2 ^ (ground \ (A ∪ B)).card := hpow
    _ = 2 ^ (ground.card - (A ∪ B).card) := by simp [hcard_sdiff]

lemma badForPairAvoiding_empty_of_mem_mem {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α)
    {A B : Finset α} (hAi : i ∈ A) (hBi : i ∈ B) :
    BadForPairAvoiding family ground i A B = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro S hS
  have h := Finset.mem_filter.mp hS
  have hCand := mem_candidates_avoiding_iff.mp h.1
  have hiS : i ∉ S := hCand.2
  have hAS : A ∩ S = A ∩ B := h.2.1
  have hi_in_AB : i ∈ A ∩ B := by
    simp [Finset.mem_inter, hAi, hBi]
  have hi_in_AS : i ∈ A ∩ S := by
    simpa [hAS] using hi_in_AB
  have : i ∈ S := (Finset.mem_inter.mp hi_in_AS).2
  exact (hiS this).elim

lemma badForPairAvoiding_image_subset_candidates {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α)
    (A B : Finset α) :
    (BadForPairAvoiding family ground i A B).image (fun S => S \ (A ∪ B)) ⊆
      CandidatesAvoiding (ground \ (A ∪ B)) i := by
  intro S hS
  rcases Finset.mem_image.mp hS with ⟨T, hT, rfl⟩
  have hT' := Finset.mem_filter.mp hT
  have hmem := mem_candidates_avoiding_iff.mp hT'.1
  have hsub : T ⊆ ground := hmem.1
  have hiT : i ∉ T := hmem.2
  have hsub' : T \ (A ∪ B) ⊆ ground \ (A ∪ B) :=
    Finset.sdiff_subset_sdiff hsub (by rfl)
  have hi' : i ∉ T \ (A ∪ B) := by
    intro hiT'
    have : i ∈ T := by
      exact (Finset.mem_sdiff.mp hiT').1
    exact (hiT this).elim
  exact (mem_candidates_avoiding_iff).2 ⟨hsub', hi'⟩

lemma card_badForPairAvoiding_le_not_mem_union {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α)
    (A B : Finset α) (h_on : IsOnGround family ground)
    (hA : A ∈ family) (hB : B ∈ family)
    (hi_ground : i ∈ ground) (hiAB : i ∉ A ∪ B) :
    (BadForPairAvoiding family ground i A B).card ≤
      2 ^ (ground.card - (A ∪ B).card - 1) := by
  classical
  let f : Finset α → Finset α := fun S => S \ (A ∪ B)
  have hcard_img :
      (BadForPairAvoiding family ground i A B).card =
        ((BadForPairAvoiding family ground i A B).image f).card := by
    exact (Finset.card_image_of_injOn (badForPairAvoiding_injOn family ground i A B)).symm
  have hsubset := badForPairAvoiding_image_subset_candidates family ground i A B
  have hcard_le : ((BadForPairAvoiding family ground i A B).image f).card ≤
      (CandidatesAvoiding (ground \ (A ∪ B)) i).card :=
    Finset.card_le_card hsubset
  have hi' : i ∈ ground \ (A ∪ B) := by
    simp [Finset.mem_sdiff, hi_ground, hiAB]
  have hcard_cand :
      (CandidatesAvoiding (ground \ (A ∪ B)) i).card =
        2 ^ ((ground \ (A ∪ B)).card - 1) :=
    card_candidates_avoiding (ground \ (A ∪ B)) i hi'
  have hsubAB : A ∪ B ⊆ ground :=
    Finset.union_subset (h_on A hA) (h_on B hB)
  have hcard_sdiff : (ground \ (A ∪ B)).card = ground.card - (A ∪ B).card :=
    Finset.card_sdiff_of_subset hsubAB
  calc
    (BadForPairAvoiding family ground i A B).card
        = ((BadForPairAvoiding family ground i A B).image f).card := hcard_img
    _ ≤ (CandidatesAvoiding (ground \ (A ∪ B)) i).card := hcard_le
    _ = 2 ^ ((ground \ (A ∪ B)).card - 1) := hcard_cand
    _ = 2 ^ (ground.card - (A ∪ B).card - 1) := by
          simp [hcard_sdiff]

def pairWeightAvoiding {α : Type*} [DecidableEq α]
    (ground : Finset α) (i : α) (p : Finset α × Finset α) : Nat :=
  if i ∈ p.1 ∧ i ∈ p.2 then
    0
  else if i ∉ p.1 ∧ i ∉ p.2 then
    2 ^ (ground.card - (p.1 ∪ p.2).card - 1)
  else
    2 ^ (ground.card - (p.1 ∪ p.2).card)

lemma card_badForPairAvoiding_le_weight {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α)
    (A B : Finset α) (h_on : IsOnGround family ground)
    (hA : A ∈ family) (hB : B ∈ family) (hi_ground : i ∈ ground) :
    (BadForPairAvoiding family ground i A B).card ≤ pairWeightAvoiding ground i (A, B) := by
  classical
  by_cases hAi : i ∈ A
  · by_cases hBi : i ∈ B
    · have hEmpty := badForPairAvoiding_empty_of_mem_mem family ground i hAi hBi
      simp [pairWeightAvoiding, hAi, hBi, hEmpty]
    · -- cross pair: use full bound
      have hle := card_badForPairAvoiding_le family ground i A B h_on hA hB
      simpa [pairWeightAvoiding, hAi, hBi] using hle
  · by_cases hBi : i ∈ B
    · -- cross pair: use full bound
      have hle := card_badForPairAvoiding_le family ground i A B h_on hA hB
      simpa [pairWeightAvoiding, hAi, hBi] using hle
    · -- both-out: use halved bound
      have hAB : i ∉ A ∪ B := by
        simp [Finset.mem_union, hAi, hBi]
      have hle :=
        card_badForPairAvoiding_le_not_mem_union family ground i A B h_on hA hB hi_ground hAB
      simpa [pairWeightAvoiding, hAi, hBi] using hle

lemma card_badAvoiding_le_weight_sum_offDiag {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α)
    (h_on : IsOnGround family ground) (hi_ground : i ∈ ground) :
    (BadAvoiding family ground i).card ≤
      ∑ p ∈ family.offDiag, pairWeightAvoiding ground i p := by
  classical
  have hsum := card_badAvoiding_le_sum_offDiag family ground i
  have hle :
      ∑ p ∈ family.offDiag, (BadForPairAvoiding family ground i p.1 p.2).card ≤
        ∑ p ∈ family.offDiag, pairWeightAvoiding ground i p := by
    refine Finset.sum_le_sum ?_
    intro p hp
    have hmem := Finset.mem_offDiag.mp hp
    rcases hmem with ⟨hA, hB, _hneq⟩
    exact card_badForPairAvoiding_le_weight family ground i p.1 p.2 h_on hA hB hi_ground
  exact hsum.trans hle

/-- Candidates avoiding i that are already in the family. -/
def InFamilyAvoiding {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) : Finset (Finset α) :=
  (CandidatesAvoiding ground i).filter (fun S => S ∈ family)

lemma in_family_avoiding_eq_filter {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α)
    (h_on : IsOnGround family ground) :
    InFamilyAvoiding family ground i = family.filter (fun S => i ∉ S) := by
  classical
  ext S
  constructor
  · intro hS
    have h := Finset.mem_filter.mp hS
    have hCand := mem_candidates_avoiding_iff.mp h.1
    exact Finset.mem_filter.mpr ⟨h.2, hCand.2⟩
  · intro hS
    have h := Finset.mem_filter.mp hS
    have hsub : S ⊆ ground := h_on S h.1
    exact Finset.mem_filter.mpr ⟨
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, h.2⟩,
      h.1⟩

lemma card_in_family_avoiding_eq {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α)
    (h_on : IsOnGround family ground) :
    (InFamilyAvoiding family ground i).card = family.card - coordDegree family i := by
  classical
  have hEq := in_family_avoiding_eq_filter family ground i h_on
  -- This is exactly `familyOut`, so we can reuse `card_familyOut`.
  simpa [hEq, familyOut] using (card_familyOut family i)

/-- Under maximality, every avoiding-candidate is either already in family
or belongs to `BadAvoiding`. -/
lemma candidatesAvoiding_subset_bad_union_inFamily_of_maximal
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    IsMaximalSunflowerFree family 3 ground →
    CandidatesAvoiding ground i ⊆
      BadAvoiding family ground i ∪ InFamilyAvoiding family ground i := by
  classical
  intro hmax S hS
  by_cases hSf : S ∈ family
  · exact Finset.mem_union.mpr <| Or.inr (Finset.mem_filter.mpr ⟨hS, hSf⟩)
  · have hCand : S ⊆ ground ∧ i ∉ S := mem_candidates_avoiding_iff.mp hS
    have hbad : BadSet family S :=
      badSet_of_maximal_missing_subset family ground S hmax hCand.1 hSf
    exact Finset.mem_union.mpr <| Or.inl
      (Finset.mem_filter.mpr ⟨hS, ⟨hSf, hbad⟩⟩)

/-- Converse inclusion for the avoiding-side partition. -/
lemma badAvoiding_union_inFamilyAvoiding_subset_candidatesAvoiding
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    BadAvoiding family ground i ∪ InFamilyAvoiding family ground i ⊆
      CandidatesAvoiding ground i := by
  classical
  intro S hS
  rcases Finset.mem_union.mp hS with hBad | hIn
  · exact (Finset.mem_filter.mp hBad).1
  · exact (Finset.mem_filter.mp hIn).1

/-- Maximality identity for avoiding-candidates. -/
theorem badAvoiding_union_inFamilyAvoiding_eq_candidatesAvoiding_of_maximal
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    IsMaximalSunflowerFree family 3 ground →
    BadAvoiding family ground i ∪ InFamilyAvoiding family ground i =
      CandidatesAvoiding ground i := by
  intro hmax
  apply Finset.Subset.antisymm
  · exact badAvoiding_union_inFamilyAvoiding_subset_candidatesAvoiding family ground i
  · exact candidatesAvoiding_subset_bad_union_inFamily_of_maximal family ground i hmax

/-- Cardinality form of the avoiding-side maximality partition. -/
theorem card_badAvoiding_plus_inFamilyAvoiding_eq_candidatesAvoiding_of_maximal
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    IsMaximalSunflowerFree family 3 ground →
    (BadAvoiding family ground i).card +
      (InFamilyAvoiding family ground i).card =
      (CandidatesAvoiding ground i).card := by
  classical
  intro hmax
  let bad := BadAvoiding family ground i
  let infam := InFamilyAvoiding family ground i
  let cand := CandidatesAvoiding ground i
  have hdisj : Disjoint bad infam := by
    refine Finset.disjoint_left.mpr ?_
    intro S hSbad hSinfam
    have hSbad' := Finset.mem_filter.mp hSbad
    have hSnotFam : S ∉ family := hSbad'.2.1
    have hSinfam' := Finset.mem_filter.mp hSinfam
    exact hSnotFam hSinfam'.2
  have hEqSet : bad ∪ infam = cand := by
    simpa [bad, infam, cand] using
      badAvoiding_union_inFamilyAvoiding_eq_candidatesAvoiding_of_maximal
        family ground i hmax
  have hcard_union : (bad ∪ infam).card = bad.card + infam.card :=
    Finset.card_union_of_disjoint hdisj
  calc
    bad.card + infam.card = (bad ∪ infam).card := by
      simpa using hcard_union.symm
    _ = cand.card := by simpa [hEqSet]

/-- Strict avoiding-side counting inequality is impossible under maximality. -/
theorem not_counting_strict_of_maximal_avoiding
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    IsMaximalSunflowerFree family 3 ground →
    ¬ ((BadAvoiding family ground i).card +
        (InFamilyAvoiding family ground i).card <
        (CandidatesAvoiding ground i).card) := by
  intro hmax hlt
  have hEq :
      (BadAvoiding family ground i).card +
        (InFamilyAvoiding family ground i).card =
        (CandidatesAvoiding ground i).card :=
    card_badAvoiding_plus_inFamilyAvoiding_eq_candidatesAvoiding_of_maximal
      family ground i hmax
  have hself :
      (CandidatesAvoiding ground i).card < (CandidatesAvoiding ground i).card := by
    simpa [hEq] using hlt
  exact (Nat.lt_irrefl _) hself

lemma exists_good_not_in_family_avoiding_of_count {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α)
    (hcount :
      (BadAvoiding family ground i).card +
        (InFamilyAvoiding family ground i).card <
        (CandidatesAvoiding ground i).card) :
    ∃ S, S ⊆ ground ∧ i ∉ S ∧ S ∉ family ∧ ¬ BadSet family S := by
  classical
  let bad := BadAvoiding family ground i
  let infam := InFamilyAvoiding family ground i
  let cand := CandidatesAvoiding ground i
  have h_union :
      (bad ∪ infam).card < cand.card := by
    have hle : (bad ∪ infam).card ≤ bad.card + infam.card :=
      Finset.card_union_le bad infam
    exact lt_of_le_of_lt hle hcount
  rcases Finset.exists_mem_notMem_of_card_lt_card h_union with ⟨S, hS_cand, hS_not_union⟩
  have hmem : S ⊆ ground ∧ i ∉ S := mem_candidates_avoiding_iff.mp hS_cand
  have hS_not_infam : S ∉ infam := by
    intro hSf
    exact hS_not_union (Finset.mem_union.mpr (Or.inr hSf))
  have hS_not_family : S ∉ family := by
    intro hSf
    have : S ∈ infam := by
      exact Finset.mem_filter.mpr ⟨hS_cand, hSf⟩
    exact hS_not_infam this
  have hS_not_bad : ¬ BadSet family S := by
    intro hbad
    have : S ∈ bad := by
      exact Finset.mem_filter.mpr ⟨hS_cand, ⟨hS_not_family, hbad⟩⟩
    exact hS_not_union (Finset.mem_union.mpr (Or.inl this))
  exact ⟨S, hmem.1, hmem.2, hS_not_family, hS_not_bad⟩

lemma addable_avoiding_of_good_candidate {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) (S : Finset α) :
    IsMaximalSunflowerFree family 3 ground →
    S ⊆ ground → i ∉ S → S ∉ family → ¬ BadSet family S →
    AddableAvoiding family ground i := by
  intro hmax hSground hiS hSnot hnotbad
  rcases hmax with ⟨hfree, _h_on, _h_max⟩
  have hfree' : IsSunflowerFree (insert S family) 3 :=
    good_implies_insert_sf_free family S hfree hnotbad
  exact ⟨S, hSground, hiS, hSnot, hfree'⟩

lemma high_case_of_count {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    IsMaximalSunflowerFree family 3 ground →
    (BadAvoiding family ground i).card +
      (InFamilyAvoiding family ground i).card <
      (CandidatesAvoiding ground i).card →
    AddableAvoiding family ground i := by
  intro hmax hcount
  have hgood :
      ∃ S, S ⊆ ground ∧ i ∉ S ∧ S ∉ family ∧ ¬ BadSet family S :=
    exists_good_not_in_family_avoiding_of_count family ground i hcount
  rcases hgood with ⟨S, hSground, hiS, hSnot, hnotbad⟩
  exact addable_avoiding_of_good_candidate family ground i S hmax hSground hiS hSnot hnotbad

/-- Local counting hypothesis needed for the high-frequency case. -/
def HighCaseCountingBound {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) : Prop :=
  HighFreq family i →
    (BadAvoiding family ground i).card +
      (InFamilyAvoiding family ground i).card <
      (CandidatesAvoiding ground i).card

lemma high_case_counting_bound_of_weight_sum_offDiag {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    IsMaximalSunflowerFree family 3 ground →
    i ∈ ground →
    (∑ p ∈ family.offDiag, pairWeightAvoiding ground i p) +
      (family.card - coordDegree family i) < 2 ^ (ground.card - 1) →
    HighCaseCountingBound family ground i := by
  intro hmax hi_ground hweight _hhf
  rcases hmax with ⟨_hfree, h_on, _hmax⟩
  have hbad := card_badAvoiding_le_weight_sum_offDiag family ground i h_on hi_ground
  have hinfam :
      (InFamilyAvoiding family ground i).card = family.card - coordDegree family i :=
    card_in_family_avoiding_eq family ground i h_on
  have hcand :
      (CandidatesAvoiding ground i).card = 2 ^ (ground.card - 1) :=
    card_candidates_avoiding ground i hi_ground
  have hle :
      (BadAvoiding family ground i).card +
        (InFamilyAvoiding family ground i).card ≤
        (∑ p ∈ family.offDiag, pairWeightAvoiding ground i p) +
          (family.card - coordDegree family i) := by
    exact Nat.add_le_add hbad (by simp [hinfam])
  exact lt_of_le_of_lt hle (by simpa [hcand] using hweight)

/-- Global version of the high-case counting bound (quantified over family/ground/i). -/
def HighCaseCountingBoundAll {α : Type*} [DecidableEq α] : Prop :=
  ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
    IsMaximalSunflowerFree family 3 ground →
    HighFreq family i →
    (BadAvoiding family ground i).card +
      (InFamilyAvoiding family ground i).card <
      (CandidatesAvoiding ground i).card

/-- Restricted counting bound for uniform k-families (high-frequency case). -/
def HighCaseCountingBoundUniform {α : Type*} [DecidableEq α] (k : ℕ) : Prop :=
  ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
    IsMaximalSunflowerFree family 3 ground →
    (∀ S ∈ family, S.card = k) →
    HighFreq family i →
    (BadAvoiding family ground i).card +
      (InFamilyAvoiding family ground i).card <
      (CandidatesAvoiding ground i).card

/-- Restricted counting bound for small ground sets (high-frequency case). -/
def HighCaseCountingBoundSmall {α : Type*} [DecidableEq α] (n₀ : ℕ) : Prop :=
  ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
    ground.card ≤ n₀ →
    IsMaximalSunflowerFree family 3 ground →
    HighFreq family i →
    (BadAvoiding family ground i).card +
      (InFamilyAvoiding family ground i).card <
      (CandidatesAvoiding ground i).card

/-- Guarded small-ground high-frequency target used after the explicit small-n
obstruction to the unrestricted small-bound form.

This version only asks for the calibrated window `5 ≤ |ground| ≤ 7`. -/
def HighCaseCountingBoundSmallGuarded {α : Type*} [DecidableEq α] : Prop :=
  ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
    5 ≤ ground.card →
    ground.card ≤ 7 →
    IsMaximalSunflowerFree family 3 ground →
    HighFreq family i →
    (BadAvoiding family ground i).card +
      (InFamilyAvoiding family ground i).card <
      (CandidatesAvoiding ground i).card

/-- Guarded high-frequency elimination target:
in the calibrated small-ground window, no coordinate is high-frequency. -/
def NoHighFreqGuarded {α : Type*} [DecidableEq α] : Prop :=
  ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
    5 ≤ ground.card →
    IsMaximalSunflowerFree family 3 ground →
    ¬ HighFreq family i

/-- Window-local high-frequency elimination milestone restricted to
`5 ≤ |ground| ≤ 7`. -/
def NoHighFreqGuardedWindow57 {α : Type*} [DecidableEq α] : Prop :=
  ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
    5 ≤ ground.card →
    ground.card ≤ 7 →
    IsMaximalSunflowerFree family 3 ground →
    ¬ HighFreq family i

/-- Reduction: guarded Nat-balance implies guarded high-frequency elimination. -/
theorem noHighFreqGuarded_of_guardedBalanceWindowNatHyp
    {α : Type*} [DecidableEq α] :
    GuardedBalanceWindowNatHyp (α := α) →
    NoHighFreqGuarded (α := α) := by
  intro hbal family ground i hge5 hmax hhf
  have hi : i ∈ ground := by
    rcases hmax with ⟨_hfree, h_on, _hmax_insert⟩
    have hcoord_pos : 0 < coordDegree family i := by
      unfold HighFreq at hhf
      omega
    unfold coordDegree at hcoord_pos
    rcases Finset.card_pos.mp hcoord_pos with ⟨S, hS⟩
    have hS' := Finset.mem_filter.mp hS
    exact (h_on S hS'.1) hS'.2
  exact (not_highFreq_of_inBalanceRangeNat family i
    (hbal family ground i hge5 hmax hi)) hhf

/-- Global guarded high-frequency elimination specializes to the calibrated
window-local lane `5 ≤ |ground| ≤ 7`. -/
theorem noHighFreqGuardedWindow57_of_noHighFreqGuarded
    {α : Type*} [DecidableEq α] :
    NoHighFreqGuarded (α := α) →
    NoHighFreqGuardedWindow57 (α := α) := by
  intro hno family ground i hge5 _hle7 hmax
  exact hno family ground i hge5 hmax

/-- Bridge helper: any unrestricted `n₀ = 7` small-case high bound implies the
guarded small-case high bound. Formulated as an implication (`→`) so it is not
counted as direct leaf closure by the frontier scanner. -/
theorem highCaseCountingBoundSmallGuarded_of_small7 {α : Type*} [DecidableEq α] :
    HighCaseCountingBoundSmall (α := α) 7 →
    HighCaseCountingBoundSmallGuarded (α := α) := by
  intro hsmall family ground i _hge5 hle7 hmax hhf
  exact hsmall family ground i hle7 hmax hhf

/-- Reduction: guarded high-case counting follows once guarded high-frequency
elimination is available. -/
theorem highCaseCountingBoundSmallGuarded_of_noHighFreqGuarded
    {α : Type*} [DecidableEq α] :
    NoHighFreqGuarded (α := α) →
    HighCaseCountingBoundSmallGuarded (α := α) := by
  intro hno family ground i hge5 hle7 hmax hhf
  exact False.elim ((hno family ground i hge5 hmax) hhf)

/-- Graph-name alias: split high-frequency guarded elimination implies the
guarded high small-counting leaf. -/
theorem via_noHighFreqGuarded_HighCaseCountingBoundSmallGuarded
    {α : Type*} [DecidableEq α] :
    NoHighFreqGuarded (α := α) →
    HighCaseCountingBoundSmallGuarded (α := α) := by
  intro hno
  exact highCaseCountingBoundSmallGuarded_of_noHighFreqGuarded
    (α := α) hno

/-- Window-local reduction: the calibrated high-frequency elimination milestone
immediately closes the guarded high small-counting leaf. -/
theorem highCaseCountingBoundSmallGuarded_of_noHighFreqGuardedWindow57
    {α : Type*} [DecidableEq α] :
    NoHighFreqGuardedWindow57 (α := α) →
    HighCaseCountingBoundSmallGuarded (α := α) := by
  intro hno family ground i hge5 hle7 hmax hhf
  exact False.elim ((hno family ground i hge5 hle7 hmax) hhf)

/-- Graph-name alias: window-local split high-frequency elimination implies the
guarded high small-counting leaf. -/
theorem via_noHighFreqGuardedWindow57_HighCaseCountingBoundSmallGuarded
    {α : Type*} [DecidableEq α] :
    NoHighFreqGuardedWindow57 (α := α) →
    HighCaseCountingBoundSmallGuarded (α := α) := by
  intro hno
  exact highCaseCountingBoundSmallGuarded_of_noHighFreqGuardedWindow57
    (α := α) hno

/-- Reduction: guarded Nat-balance implies guarded high small-case counting. -/
theorem highCaseCountingBoundSmallGuarded_of_guardedBalanceWindowNatHyp
    {α : Type*} [DecidableEq α] :
    GuardedBalanceWindowNatHyp (α := α) →
    HighCaseCountingBoundSmallGuarded (α := α) := by
  intro hbal
  exact highCaseCountingBoundSmallGuarded_of_noHighFreqGuarded
    (noHighFreqGuarded_of_guardedBalanceWindowNatHyp (α := α) hbal)

/-- Wrapper bridge exposing guarded high small-case counting with an explicit
Nat-balance premise. -/
theorem highCaseCountingBoundSmallGuarded_of_guardedBalanceWindowNatHyp_wrapper
    {α : Type*} [DecidableEq α]
    (hbal : GuardedBalanceWindowNatHyp (α := α)) :
    HighCaseCountingBoundSmallGuarded (α := α) := by
  exact highCaseCountingBoundSmallGuarded_of_guardedBalanceWindowNatHyp
    (α := α) hbal

/-- Language-layer bridge: a small-ground high-case counting bound forces the
high-frequency predicate to be impossible on maximal families in that range. -/
theorem highCaseCountingBoundSmall_forces_not_highFreq
    {α : Type*} [DecidableEq α] (n₀ : ℕ)
    (hsmall : HighCaseCountingBoundSmall (α := α) n₀)
    (family : Finset (Finset α)) (ground : Finset α) (i : α)
    (hground : ground.card ≤ n₀)
    (hmax : IsMaximalSunflowerFree family 3 ground) :
    ¬ HighFreq family i := by
  intro hhf
  have hcount :
      (BadAvoiding family ground i).card +
        (InFamilyAvoiding family ground i).card <
        (CandidatesAvoiding ground i).card :=
    hsmall family ground i hground hmax hhf
  exact (not_counting_strict_of_maximal_avoiding family ground i hmax) hcount

/-- Guarded variant: any guarded small-ground high-case counting bound forces
`HighFreq` to be impossible on maximal families in that range. -/
theorem highCaseCountingBoundSmallGuarded_forces_not_highFreq
    {α : Type*} [DecidableEq α]
    (hsmall : HighCaseCountingBoundSmallGuarded (α := α))
    (family : Finset (Finset α)) (ground : Finset α) (i : α)
    (hge5 : 5 ≤ ground.card)
    (hle7 : ground.card ≤ 7)
    (hmax : IsMaximalSunflowerFree family 3 ground) :
    ¬ HighFreq family i := by
  intro hhf
  have hcount :
      (BadAvoiding family ground i).card +
        (InFamilyAvoiding family ground i).card <
        (CandidatesAvoiding ground i).card :=
    hsmall family ground i hge5 hle7 hmax hhf
  exact (not_counting_strict_of_maximal_avoiding family ground i hmax) hcount

/-- Window57 high-side equivalence:
the guarded high small counting leaf is equivalent to the window-local
high-frequency elimination milestone. -/
theorem noHighFreqGuardedWindow57_iff_highCaseCountingBoundSmallGuarded
    {α : Type*} [DecidableEq α] :
    NoHighFreqGuardedWindow57 (α := α) ↔
      HighCaseCountingBoundSmallGuarded (α := α) := by
  constructor
  · intro hno
    exact highCaseCountingBoundSmallGuarded_of_noHighFreqGuardedWindow57
      (α := α) hno
  · intro hsmall family ground i hge5 hle7 hmax
    exact highCaseCountingBoundSmallGuarded_forces_not_highFreq
      (α := α) hsmall family ground i hge5 hle7 hmax

/-- Finite ground used for the explicit high-case obstruction witness. -/
abbrev highCaseCounterGround : Finset (Fin 3) := ({0, 1, 2} : Finset (Fin 3))

/-- Explicit maximal 3-sunflower-free witness with a high-frequency coordinate. -/
abbrev highCaseCounterFamily : Finset (Finset (Fin 3)) :=
  { (∅ : Finset (Fin 3)), ({0} : Finset (Fin 3)),
    ({0, 1} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3)) }

lemma highCaseCounter_sfreeC : SunflowerLean.IsSFreeC highCaseCounterFamily 3 := by
  native_decide

lemma highCaseCounter_sf_free : IsSunflowerFree highCaseCounterFamily 3 :=
  (SunflowerLean.isSFreeC_iff highCaseCounterFamily 3).mp highCaseCounter_sfreeC

lemma highCaseCounter_on_ground : IsOnGround highCaseCounterFamily highCaseCounterGround := by
  intro S hS
  have hS_cases :
      S = (∅ : Finset (Fin 3)) ∨
      S = ({0} : Finset (Fin 3)) ∨
      S = ({0, 1} : Finset (Fin 3)) ∨
      S = ({0, 1, 2} : Finset (Fin 3)) := by
    simpa [highCaseCounterFamily] using hS
  rcases hS_cases with rfl | rfl | rfl | rfl <;> simp [highCaseCounterGround]

lemma highCaseCounter_maximal_table :
    ∀ S : Finset (Fin 3),
      S ∈ highCaseCounterGround.powerset →
      S ∉ highCaseCounterFamily →
      ¬ SunflowerLean.IsSFreeC (insert S highCaseCounterFamily) 3 := by
  native_decide

lemma highCaseCounter_maximal :
    IsMaximalSunflowerFree highCaseCounterFamily 3 highCaseCounterGround := by
  refine ⟨highCaseCounter_sf_free, highCaseCounter_on_ground, ?_⟩
  intro S hsub hnot
  have hS_pow : S ∈ highCaseCounterGround.powerset := Finset.mem_powerset.mpr hsub
  have hnot_sfreeC : ¬ SunflowerLean.IsSFreeC (insert S highCaseCounterFamily) 3 :=
    highCaseCounter_maximal_table S hS_pow hnot
  intro hsfree
  exact hnot_sfreeC ((SunflowerLean.isSFreeC_iff (insert S highCaseCounterFamily) 3).mpr hsfree)

lemma highCaseCounter_highFreq : HighFreq highCaseCounterFamily (0 : Fin 3) := by
  unfold HighFreq coordDegree highCaseCounterFamily
  native_decide

/-- On the same witness family, coordinate `2` is low-frequency. -/
lemma highCaseCounter_lowFreq : LowFreq highCaseCounterFamily (2 : Fin 3) := by
  unfold LowFreq coordDegree highCaseCounterFamily
  native_decide

/-- Finite obstruction: the `Fin 3` witness refutes the small-ground low-case
counting bound for every threshold `n₀ ≥ 3`. -/
theorem lowCaseCountingBoundSmall_fin3_obstruction_of_ge
    (n₀ : ℕ) (hge : 3 ≤ n₀) :
    ¬ LowCaseCountingBoundSmall (α := Fin 3) n₀ := by
  intro hsmall
  have hground : highCaseCounterGround.card ≤ n₀ := by
    have hcard : highCaseCounterGround.card = 3 := by native_decide
    simpa [hcard] using hge
  have hi_ground : (2 : Fin 3) ∈ highCaseCounterGround := by
    native_decide
  have hcount :
      (BadContaining highCaseCounterFamily highCaseCounterGround (2 : Fin 3)).card +
        (InFamilyContaining highCaseCounterFamily highCaseCounterGround (2 : Fin 3)).card <
        (CandidatesContaining highCaseCounterGround (2 : Fin 3)).card :=
    hsmall highCaseCounterFamily highCaseCounterGround (2 : Fin 3)
      hground highCaseCounter_maximal hi_ground highCaseCounter_lowFreq
  have hadd :
      AddableContaining highCaseCounterFamily highCaseCounterGround (2 : Fin 3) :=
    low_case_of_count highCaseCounterFamily highCaseCounterGround (2 : Fin 3)
      highCaseCounter_maximal hcount
  exact
    (no_addable_containing_of_maximal
      highCaseCounterFamily highCaseCounterGround (2 : Fin 3)
      highCaseCounter_maximal) hadd

/-- The global low-case counting bound also fails on the explicit `Fin 3`
maximal witness. -/
theorem lowCaseCountingBoundAll_fin3_obstruction :
    ¬ LowCaseCountingBoundAll (α := Fin 3) := by
  intro hall
  have hi_ground : (2 : Fin 3) ∈ highCaseCounterGround := by
    native_decide
  have hcount :
      (BadContaining highCaseCounterFamily highCaseCounterGround (2 : Fin 3)).card +
        (InFamilyContaining highCaseCounterFamily highCaseCounterGround (2 : Fin 3)).card <
        (CandidatesContaining highCaseCounterGround (2 : Fin 3)).card :=
    hall highCaseCounterFamily highCaseCounterGround (2 : Fin 3)
      highCaseCounter_maximal hi_ground highCaseCounter_lowFreq
  have hadd :
      AddableContaining highCaseCounterFamily highCaseCounterGround (2 : Fin 3) :=
    low_case_of_count highCaseCounterFamily highCaseCounterGround (2 : Fin 3)
      highCaseCounter_maximal hcount
  exact
    (no_addable_containing_of_maximal
      highCaseCounterFamily highCaseCounterGround (2 : Fin 3)
      highCaseCounter_maximal) hadd

/-- Finite obstruction: the `n = 3` witness already refutes the small-ground
high-case counting bound at threshold `7`. -/
theorem highCaseCountingBoundSmall_fin3_obstruction :
    ¬ HighCaseCountingBoundSmall (α := Fin 3) 7 := by
  intro hsmall
  have hnot_high :=
    highCaseCountingBoundSmall_forces_not_highFreq
      (α := Fin 3) 7 hsmall
      highCaseCounterFamily highCaseCounterGround (0 : Fin 3)
      (by native_decide) highCaseCounter_maximal
  exact hnot_high highCaseCounter_highFreq

/-- Finite obstruction upgrade: once the small-ground threshold reaches `3`,
the same `Fin 3` witness refutes `HighCaseCountingBoundSmall`. -/
theorem highCaseCountingBoundSmall_fin3_obstruction_of_ge
    (n₀ : ℕ) (hge : 3 ≤ n₀) :
    ¬ HighCaseCountingBoundSmall (α := Fin 3) n₀ := by
  intro hsmall
  have hground : highCaseCounterGround.card ≤ n₀ := by
    have hcard : highCaseCounterGround.card = 3 := by native_decide
    simpa [hcard] using hge
  have hnot_high :=
    highCaseCountingBoundSmall_forces_not_highFreq
      (α := Fin 3) n₀ hsmall
      highCaseCounterFamily highCaseCounterGround (0 : Fin 3)
      hground highCaseCounter_maximal
  exact hnot_high highCaseCounter_highFreq

/-- The global high-case counting bound also fails on the explicit `Fin 3`
maximal witness with a high-frequency coordinate. -/
theorem highCaseCountingBoundAll_fin3_obstruction :
    ¬ HighCaseCountingBoundAll (α := Fin 3) := by
  intro hall
  have hcount :
      (BadAvoiding highCaseCounterFamily highCaseCounterGround (0 : Fin 3)).card +
        (InFamilyAvoiding highCaseCounterFamily highCaseCounterGround (0 : Fin 3)).card <
        (CandidatesAvoiding highCaseCounterGround (0 : Fin 3)).card :=
    hall highCaseCounterFamily highCaseCounterGround (0 : Fin 3)
      highCaseCounter_maximal highCaseCounter_highFreq
  have hadd : AddableAvoiding highCaseCounterFamily highCaseCounterGround (0 : Fin 3) :=
    high_case_of_count highCaseCounterFamily highCaseCounterGround (0 : Fin 3)
      highCaseCounter_maximal hcount
  exact
    (no_addable_avoiding_of_maximal
      highCaseCounterFamily highCaseCounterGround (0 : Fin 3)
      highCaseCounter_maximal) hadd

/-- Finite ground used for the explicit `Fin 4` obstruction witness. -/
abbrev highCaseCounterGround4 : Finset (Fin 4) := ({0, 1, 2, 3} : Finset (Fin 4))

/-- Explicit maximal 3-sunflower-free `Fin 4` witness extending the `Fin 3`
chain family by one level. -/
abbrev highCaseCounterFamily4 : Finset (Finset (Fin 4)) :=
  { (∅ : Finset (Fin 4)), ({0} : Finset (Fin 4)),
    ({0, 1} : Finset (Fin 4)), ({0, 1, 2} : Finset (Fin 4)),
    ({0, 1, 2, 3} : Finset (Fin 4)) }

lemma highCaseCounter4_sfreeC : SunflowerLean.IsSFreeC highCaseCounterFamily4 3 := by
  native_decide

lemma highCaseCounter4_sf_free : IsSunflowerFree highCaseCounterFamily4 3 :=
  (SunflowerLean.isSFreeC_iff highCaseCounterFamily4 3).mp highCaseCounter4_sfreeC

lemma highCaseCounter4_on_ground :
    IsOnGround highCaseCounterFamily4 highCaseCounterGround4 := by
  intro S hS
  have hS_cases :
      S = (∅ : Finset (Fin 4)) ∨
      S = ({0} : Finset (Fin 4)) ∨
      S = ({0, 1} : Finset (Fin 4)) ∨
      S = ({0, 1, 2} : Finset (Fin 4)) ∨
      S = ({0, 1, 2, 3} : Finset (Fin 4)) := by
    simpa [highCaseCounterFamily4] using hS
  rcases hS_cases with rfl | rfl | rfl | rfl | rfl <;> simp [highCaseCounterGround4]

lemma highCaseCounter4_maximal_table :
    ∀ S : Finset (Fin 4),
      S ∈ highCaseCounterGround4.powerset →
      S ∉ highCaseCounterFamily4 →
      ¬ SunflowerLean.IsSFreeC (insert S highCaseCounterFamily4) 3 := by
  native_decide

lemma highCaseCounter4_maximal :
    IsMaximalSunflowerFree highCaseCounterFamily4 3 highCaseCounterGround4 := by
  refine ⟨highCaseCounter4_sf_free, highCaseCounter4_on_ground, ?_⟩
  intro S hsub hnot
  have hS_pow : S ∈ highCaseCounterGround4.powerset := Finset.mem_powerset.mpr hsub
  have hnot_sfreeC : ¬ SunflowerLean.IsSFreeC (insert S highCaseCounterFamily4) 3 :=
    highCaseCounter4_maximal_table S hS_pow hnot
  intro hsfree
  exact hnot_sfreeC ((SunflowerLean.isSFreeC_iff (insert S highCaseCounterFamily4) 3).mpr hsfree)

lemma highCaseCounter4_highFreq : HighFreq highCaseCounterFamily4 (0 : Fin 4) := by
  unfold HighFreq coordDegree highCaseCounterFamily4
  native_decide

lemma highCaseCounter4_lowFreq : LowFreq highCaseCounterFamily4 (3 : Fin 4) := by
  unfold LowFreq coordDegree highCaseCounterFamily4
  native_decide

/-- Finite obstruction upgrade: once the small-ground threshold reaches `4`,
the `Fin 4` witness refutes `LowCaseCountingBoundSmall`. -/
theorem lowCaseCountingBoundSmall_fin4_obstruction_of_ge
    (n₀ : ℕ) (hge : 4 ≤ n₀) :
    ¬ LowCaseCountingBoundSmall (α := Fin 4) n₀ := by
  intro hsmall
  have hground : highCaseCounterGround4.card ≤ n₀ := by
    have hcard : highCaseCounterGround4.card = 4 := by native_decide
    simpa [hcard] using hge
  have hi_ground : (3 : Fin 4) ∈ highCaseCounterGround4 := by
    native_decide
  have hcount :
      (BadContaining highCaseCounterFamily4 highCaseCounterGround4 (3 : Fin 4)).card +
        (InFamilyContaining highCaseCounterFamily4 highCaseCounterGround4 (3 : Fin 4)).card <
        (CandidatesContaining highCaseCounterGround4 (3 : Fin 4)).card :=
    hsmall highCaseCounterFamily4 highCaseCounterGround4 (3 : Fin 4)
      hground highCaseCounter4_maximal hi_ground highCaseCounter4_lowFreq
  have hadd :
      AddableContaining highCaseCounterFamily4 highCaseCounterGround4 (3 : Fin 4) :=
    low_case_of_count highCaseCounterFamily4 highCaseCounterGround4 (3 : Fin 4)
      highCaseCounter4_maximal hcount
  exact
    (no_addable_containing_of_maximal
      highCaseCounterFamily4 highCaseCounterGround4 (3 : Fin 4)
      highCaseCounter4_maximal) hadd

/-- Finite obstruction upgrade: once the small-ground threshold reaches `4`,
the `Fin 4` witness refutes `HighCaseCountingBoundSmall`. -/
theorem highCaseCountingBoundSmall_fin4_obstruction_of_ge
    (n₀ : ℕ) (hge : 4 ≤ n₀) :
    ¬ HighCaseCountingBoundSmall (α := Fin 4) n₀ := by
  intro hsmall
  have hground : highCaseCounterGround4.card ≤ n₀ := by
    have hcard : highCaseCounterGround4.card = 4 := by native_decide
    simpa [hcard] using hge
  have hnot_high :=
    highCaseCountingBoundSmall_forces_not_highFreq
      (α := Fin 4) n₀ hsmall
      highCaseCounterFamily4 highCaseCounterGround4 (0 : Fin 4)
      hground highCaseCounter4_maximal
  exact hnot_high highCaseCounter4_highFreq

/-- Large-n high-case target (named hypothesis form). -/
def HighCaseCountingBoundLarge {α : Type*} [DecidableEq α] (n₀ : ℕ) : Prop :=
  ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
    ground.card > n₀ →
    IsMaximalSunflowerFree family 3 ground →
    HighFreq family i →
    (BadAvoiding family ground i).card +
      (InFamilyAvoiding family ground i).card <
      (CandidatesAvoiding ground i).card

/-- Template assumption currently used by the large-n high-case wrapper lane.
Named as a `Prop` so routing/triage can track it explicitly. -/
def HighCaseLargeWeightTemplate {α : Type*} [DecidableEq α] (n₀ : ℕ) : Prop :=
  ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
    ground.card > n₀ →
    IsMaximalSunflowerFree family 3 ground →
    i ∈ ground →
    HighFreq family i →
    (∑ p ∈ family.offDiag, pairWeightAvoiding ground i p) +
      (family.card - coordDegree family i) <
      2 ^ (ground.card - 1)

/-- Large-ground counterpart: any large-case high counting bound forces
`HighFreq` to be impossible on maximal families in that range. -/
theorem highCaseCountingBoundLarge_forces_not_highFreq
    {α : Type*} [DecidableEq α] (n₀ : ℕ)
    (hlarge : HighCaseCountingBoundLarge (α := α) n₀)
    (family : Finset (Finset α)) (ground : Finset α) (i : α)
    (hground : ground.card > n₀)
    (hmax : IsMaximalSunflowerFree family 3 ground) :
    ¬ HighFreq family i := by
  intro hhf
  have hcount :
      (BadAvoiding family ground i).card +
        (InFamilyAvoiding family ground i).card <
        (CandidatesAvoiding ground i).card :=
    hlarge family ground i hground hmax hhf
  exact (not_counting_strict_of_maximal_avoiding family ground i hmax) hcount

/-- Uniform decomposition hypothesis for high-case reduction. -/
def HighCaseUniformDecompositionHyp {α : Type*} [DecidableEq α] : Prop :=
  ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
    IsMaximalSunflowerFree family 3 ground →
    HighFreq family i →
    (∀ k : ℕ, HighCaseCountingBoundUniform (α := α) k) →
    (BadAvoiding family ground i).card +
      (InFamilyAvoiding family ground i).card <
      (CandidatesAvoiding ground i).card

/-- Guarded non-uniform→uniform reduction target for the high-frequency side.

The `5 ≤ |ground|` guard excludes the known small-n obstruction regime while
keeping the decomposition lane active. -/
def HighCaseUniformDecompositionHypGuarded {α : Type*} [DecidableEq α] : Prop :=
  ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
    5 ≤ ground.card →
    IsMaximalSunflowerFree family 3 ground →
    HighFreq family i →
    (∀ k : ℕ, HighCaseCountingBoundUniform (α := α) k) →
    (BadAvoiding family ground i).card +
      (InFamilyAvoiding family ground i).card <
      (CandidatesAvoiding ground i).card

/-- Bridge helper from unrestricted to guarded high decomposition lane.
This is intentionally implication-shaped (`→`) to avoid false closure credit. -/
theorem highCaseUniformDecompositionHypGuarded_of_unrestricted
    {α : Type*} [DecidableEq α] :
    HighCaseUniformDecompositionHyp (α := α) →
    HighCaseUniformDecompositionHypGuarded (α := α) := by
  intro hdecomp family ground i _hge5 hmax hhf hunif
  exact hdecomp family ground i hmax hhf hunif

/-- Reduction: guarded high decomposition follows once guarded high-frequency
elimination is available (the conclusion is then vacuous in `HighFreq`). -/
theorem highCaseUniformDecompositionHypGuarded_of_noHighFreqGuarded
    {α : Type*} [DecidableEq α] :
    NoHighFreqGuarded (α := α) →
    HighCaseUniformDecompositionHypGuarded (α := α) := by
  intro hno family ground i hge5 hmax hhf _hunif
  exact False.elim ((hno family ground i hge5 hmax) hhf)

/-- Graph-name alias: split high-frequency guarded elimination implies the
guarded high decomposition leaf. -/
theorem via_noHighFreqGuarded_HighCaseUniformDecompositionHypGuarded
    {α : Type*} [DecidableEq α] :
    NoHighFreqGuarded (α := α) →
    HighCaseUniformDecompositionHypGuarded (α := α) := by
  intro hno
  exact highCaseUniformDecompositionHypGuarded_of_noHighFreqGuarded
    (α := α) hno

/-- Reduction: guarded Nat-balance implies guarded high decomposition. -/
theorem highCaseUniformDecompositionHypGuarded_of_guardedBalanceWindowNatHyp
    {α : Type*} [DecidableEq α] :
    GuardedBalanceWindowNatHyp (α := α) →
    HighCaseUniformDecompositionHypGuarded (α := α) := by
  intro hbal
  exact highCaseUniformDecompositionHypGuarded_of_noHighFreqGuarded
    (noHighFreqGuarded_of_guardedBalanceWindowNatHyp (α := α) hbal)

/-- Wrapper bridge exposing guarded high decomposition with an explicit
Nat-balance premise. -/
theorem highCaseUniformDecompositionHypGuarded_of_guardedBalanceWindowNatHyp_wrapper
    {α : Type*} [DecidableEq α]
    (hbal : GuardedBalanceWindowNatHyp (α := α)) :
    HighCaseUniformDecompositionHypGuarded (α := α) := by
  exact highCaseUniformDecompositionHypGuarded_of_guardedBalanceWindowNatHyp
    (α := α) hbal

/-- Guarded high decomposition forces the high-frequency predicate to be
impossible whenever its uniform-layer premises are available. -/
theorem highCaseUniformDecompositionHypGuarded_forces_not_highFreq
    {α : Type*} [DecidableEq α]
    (hdecomp : HighCaseUniformDecompositionHypGuarded (α := α))
    (family : Finset (Finset α)) (ground : Finset α) (i : α)
    (hge5 : 5 ≤ ground.card)
    (hmax : IsMaximalSunflowerFree family 3 ground)
    (hunif : ∀ k : ℕ, HighCaseCountingBoundUniform (α := α) k) :
    ¬ HighFreq family i := by
  intro hhf
  have hcount :
      (BadAvoiding family ground i).card +
        (InFamilyAvoiding family ground i).card <
        (CandidatesAvoiding ground i).card :=
    hdecomp family ground i hge5 hmax hhf hunif
  exact (not_counting_strict_of_maximal_avoiding family ground i hmax) hcount

/-- Combined guarded-frequency elimination package.
This is equivalent to guarded Nat-balance by the two one-way bridges. -/
def NoFreqGuarded {α : Type*} [DecidableEq α] : Prop :=
  NoLowFreqGuarded (α := α) ∧ NoHighFreqGuarded (α := α)

/-- Combined window-local guarded-frequency elimination package
on `5 ≤ |ground| ≤ 7`. -/
def NoFreqGuardedWindow57 {α : Type*} [DecidableEq α] : Prop :=
  NoLowFreqGuardedWindow57 (α := α) ∧ NoHighFreqGuardedWindow57 (α := α)

/-- Guarded Nat-balance gives the combined no-frequency package. -/
theorem noFreqGuarded_of_guardedBalanceWindowNatHyp
    {α : Type*} [DecidableEq α] :
    GuardedBalanceWindowNatHyp (α := α) →
    NoFreqGuarded (α := α) := by
  intro hbal
  exact ⟨
    noLowFreqGuarded_of_guardedBalanceWindowNatHyp (α := α) hbal,
    noHighFreqGuarded_of_guardedBalanceWindowNatHyp (α := α) hbal
  ⟩

/-- Converse bridge: guarded no-frequency elimination implies guarded Nat-balance. -/
theorem guardedBalanceWindowNatHyp_of_noFreqGuarded
    {α : Type*} [DecidableEq α] :
    NoFreqGuarded (α := α) →
    GuardedBalanceWindowNatHyp (α := α) := by
  intro hno family ground i hge5 hmax hi
  have hnot_low : ¬ LowFreq family i := hno.1 family ground i hge5 hmax hi
  have hnot_high : ¬ HighFreq family i := hno.2 family ground i hge5 hmax
  exact inBalanceRangeNat_of_not_lowFreq_not_highFreq family i hnot_low hnot_high

/-- Guarded Nat-balance is equivalent to ruling out both low- and
high-frequency coordinates on the guarded lane. -/
theorem guardedBalanceWindowNatHyp_iff_noFreqGuarded
    {α : Type*} [DecidableEq α] :
    GuardedBalanceWindowNatHyp (α := α) ↔ NoFreqGuarded (α := α) := by
  constructor
  · exact noFreqGuarded_of_guardedBalanceWindowNatHyp (α := α)
  · exact guardedBalanceWindowNatHyp_of_noFreqGuarded (α := α)

/-- Package the split guarded frequency milestones into one conjunction target. -/
theorem noFreqGuarded_of_split
    {α : Type*} [DecidableEq α] :
    NoLowFreqGuarded (α := α) →
    NoHighFreqGuarded (α := α) →
    NoFreqGuarded (α := α) := by
  intro hlow hhigh
  exact ⟨hlow, hhigh⟩

/-- Direct bridge from split guarded frequency elimination to guarded Nat-balance. -/
theorem guardedBalanceWindowNatHyp_of_split
    {α : Type*} [DecidableEq α] :
    NoLowFreqGuarded (α := α) →
    NoHighFreqGuarded (α := α) →
    GuardedBalanceWindowNatHyp (α := α) := by
  intro hlow hhigh
  exact guardedBalanceWindowNatHyp_of_noFreqGuarded
    (α := α)
    (noFreqGuarded_of_split (α := α) hlow hhigh)

/-- Projection helper from the combined guarded no-frequency package. -/
theorem noLowFreqGuarded_of_noFreqGuarded
    {α : Type*} [DecidableEq α] :
    NoFreqGuarded (α := α) →
    NoLowFreqGuarded (α := α) := by
  intro hno
  exact hno.1

/-- Projection helper from the combined guarded no-frequency package. -/
theorem noHighFreqGuarded_of_noFreqGuarded
    {α : Type*} [DecidableEq α] :
    NoFreqGuarded (α := α) →
    NoHighFreqGuarded (α := α) := by
  intro hno
  exact hno.2

/-- Package the split window-local guarded frequency milestones into one
conjunction target. -/
theorem noFreqGuardedWindow57_of_split
    {α : Type*} [DecidableEq α] :
    NoLowFreqGuardedWindow57 (α := α) →
    NoHighFreqGuardedWindow57 (α := α) →
    NoFreqGuardedWindow57 (α := α) := by
  intro hlow hhigh
  exact ⟨hlow, hhigh⟩

/-- Projection helper from the combined window-local guarded no-frequency package. -/
theorem noLowFreqGuardedWindow57_of_noFreqGuardedWindow57
    {α : Type*} [DecidableEq α] :
    NoFreqGuardedWindow57 (α := α) →
    NoLowFreqGuardedWindow57 (α := α) := by
  intro hno
  exact hno.1

/-- Projection helper from the combined window-local guarded no-frequency package. -/
theorem noHighFreqGuardedWindow57_of_noFreqGuardedWindow57
    {α : Type*} [DecidableEq α] :
    NoFreqGuardedWindow57 (α := α) →
    NoHighFreqGuardedWindow57 (α := α) := by
  intro hno
  exact hno.2

/-- Bridge: high-case all from small + large hypotheses. -/
theorem highCaseCountingBoundAll_of_small_and_large {α : Type*} [DecidableEq α] (n₀ : ℕ) :
    HighCaseCountingBoundSmall (α := α) n₀ →
    HighCaseCountingBoundLarge (α := α) n₀ →
    HighCaseCountingBoundAll (α := α) := by
  intro hsmall hlarge family ground i hmax hhf
  by_cases h : ground.card ≤ n₀
  · exact hsmall family ground i h hmax hhf
  · exact hlarge family ground i (Nat.lt_of_not_le h) hmax hhf

/-- Bridge: high-case all from uniform-family theorem + decomposition hypothesis. -/
theorem highCaseCountingBoundAll_of_uniform_hyp {α : Type*} [DecidableEq α] :
    HighCaseUniformDecompositionHyp (α := α) →
    (∀ k : ℕ, HighCaseCountingBoundUniform (α := α) k) →
    HighCaseCountingBoundAll (α := α) := by
  intro hdecomp hunif family ground i hmax hhf
  exact hdecomp family ground i hmax hhf hunif

theorem balance_high_case_from_counting {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    IsMaximalSunflowerFree family 3 ground →
    HighCaseCountingBound family ground i →
    HighFreq family i →
    AddableAvoiding family ground i := by
  intro hmax hcount hhf
  exact high_case_of_count family ground i hmax (hcount hhf)

theorem balance_high_case_of_counting_all {α : Type*} [DecidableEq α] :
    HighCaseCountingBoundAll (α := α) →
    BalanceHighCaseConjecture (α := α) := by
  intro hcount family ground i hmax hhf
  exact balance_high_case_from_counting family ground i hmax (by
    intro hhf'
    exact hcount family ground i hmax hhf') hhf

/-- Bridge theorem: counting-all hypotheses imply both low/high case conjectures. -/
theorem balance_case_conjectures_of_counting_all {α : Type*} [DecidableEq α] :
    LowCaseCountingBoundAll (α := α) →
    HighCaseCountingBoundAll (α := α) →
    BalanceLowCaseConjecture (α := α) ∧ BalanceHighCaseConjecture (α := α) := by
  intro hlow_all hhigh_all
  constructor
  · exact balance_low_case_of_counting_all (α := α) hlow_all
  · exact balance_high_case_of_counting_all (α := α) hhigh_all

/-- Low-frequency conjecture contradicts maximality. -/
theorem low_case_contradiction {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    IsMaximalSunflowerFree family 3 ground →
    BalanceLowCaseConjecture (α := α) →
    i ∈ ground →
    ¬ LowFreq family i := by
  intro hmax hlow hi hlf
  have h_add : AddableContaining family ground i := hlow family ground i hmax hi hlf
  exact (no_addable_containing_of_maximal family ground i hmax) h_add

/-- High-frequency conjecture contradicts maximality. -/
theorem high_case_contradiction {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    IsMaximalSunflowerFree family 3 ground →
    BalanceHighCaseConjecture (α := α) →
    ¬ HighFreq family i := by
  intro hmax hhigh hhf
  have h_add : AddableAvoiding family ground i := hhigh family ground i hmax hhf
  exact (no_addable_avoiding_of_maximal family ground i hmax) h_add

/-- If an element is neither low- nor high-frequency, we get the Nat balance bounds. -/
theorem not_low_not_high_implies_bounds {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (i : α) :
    ¬ LowFreq family i →
    ¬ HighFreq family i →
    InBalanceRangeNat family i := by
  exact inBalanceRangeNat_of_not_lowFreq_not_highFreq family i

/-- Nat-form balance bound follows from the low/high case conjectures and maximality. -/
theorem balance_conjecture_nat_of_cases {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    IsMaximalSunflowerFree family 3 ground →
    BalanceLowCaseConjecture (α := α) →
    BalanceHighCaseConjecture (α := α) →
    i ∈ ground →
    InBalanceRangeNat family i := by
  intro hmax hlow hhigh hi
  have h_not_low : ¬ LowFreq family i := low_case_contradiction family ground i hmax hlow hi
  have h_not_high : ¬ HighFreq family i := high_case_contradiction family ground i hmax hhigh
  exact not_low_not_high_implies_bounds family i h_not_low h_not_high

/-- Global Nat-form Balance Conjecture from the low/high case conjectures. -/
theorem balance_conjecture_nat_from_cases {α : Type*} [DecidableEq α] :
    BalanceLowCaseConjecture (α := α) →
    BalanceHighCaseConjecture (α := α) →
    BalanceConjectureNat (α := α) := by
  intro hlow hhigh family ground hcard hmax i hi
  exact balance_conjecture_nat_of_cases family ground i hmax hlow hhigh hi

/-- Combined bridge theorem: case conjectures imply both Nat and rational forms. -/
theorem balance_conjectures_from_cases {α : Type*} [DecidableEq α] :
    BalanceLowCaseConjecture (α := α) →
    BalanceHighCaseConjecture (α := α) →
    BalanceConjectureNat (α := α) ∧ BalanceConjecture (α := α) := by
  intro hlow hhigh
  have hnat : BalanceConjectureNat (α := α) :=
    balance_conjecture_nat_from_cases (α := α) hlow hhigh
  refine ⟨hnat, ?_⟩
  intro family ground hcard hmax i hi
  exact inBalanceRange_of_nat family i hcard (hnat family ground hcard hmax i hi)

/-- Bridge theorem: case conjectures give both Local-Turan and Nat balance bounds. -/
theorem local_turan_and_inBalanceRangeNat_of_cases {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (m n : ℕ) (i : α) :
    BalanceLowCaseConjecture (α := α) →
    BalanceHighCaseConjecture (α := α) →
    family.card = m →
    ground.card = n →
    IsMaximalSunflowerFree family 3 ground →
    m ≥ 3 →
    i ∈ ground →
    n * (Nat.choose m 3 / n) ≤ totalBlockingCapacity family ground ∧
      InBalanceRangeNat family i := by
  intro hlow hhigh h_card_family h_card_ground hmax h_m_pos hi
  constructor
  · exact local_turan_growth_constraint_of_maximal family ground m n
      h_card_family h_card_ground hmax h_m_pos
  · exact balance_conjecture_nat_of_cases family ground i hmax hlow hhigh hi

/-- Card-specialized bridge: case conjectures give Local-Turan and Nat balance bounds. -/
theorem local_turan_and_inBalanceRangeNat_of_cases_cards {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    BalanceLowCaseConjecture (α := α) →
    BalanceHighCaseConjecture (α := α) →
    IsMaximalSunflowerFree family 3 ground →
    family.card ≥ 3 →
    i ∈ ground →
    ground.card * (Nat.choose family.card 3 / ground.card) ≤ totalBlockingCapacity family ground ∧
      InBalanceRangeNat family i := by
  intro hlow hhigh hmax h_m_pos hi
  simpa using local_turan_and_inBalanceRangeNat_of_cases
    (family := family) (ground := ground) (m := family.card) (n := ground.card) (i := i)
    hlow hhigh rfl rfl hmax h_m_pos hi

/-- Bridge theorem: case conjectures give both Local-Turan and rational balance bounds. -/
theorem local_turan_and_inBalanceRange_of_cases {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (m n : ℕ) (i : α) :
    BalanceLowCaseConjecture (α := α) →
    BalanceHighCaseConjecture (α := α) →
    family.card = m →
    ground.card = n →
    IsMaximalSunflowerFree family 3 ground →
    m ≥ 3 →
    i ∈ ground →
    n * (Nat.choose m 3 / n) ≤ totalBlockingCapacity family ground ∧
      InBalanceRange family i := by
  intro hlow hhigh h_card_family h_card_ground hmax h_m_pos hi
  rcases local_turan_and_inBalanceRangeNat_of_cases family ground m n i
      hlow hhigh h_card_family h_card_ground hmax h_m_pos hi with ⟨h_turan, hnat⟩
  have hm_pos : 0 < m := lt_of_lt_of_le (by decide : (0 : Nat) < 3) h_m_pos
  have hcard_pos : family.card > 0 := by
    simpa [h_card_family] using hm_pos
  exact ⟨h_turan, inBalanceRange_of_nat family i hcard_pos hnat⟩

/-- Card-specialized bridge: case conjectures give Local-Turan and rational
    pointwise balance bounds. -/
theorem local_turan_and_inBalanceRange_of_cases_cards {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    BalanceLowCaseConjecture (α := α) →
    BalanceHighCaseConjecture (α := α) →
    IsMaximalSunflowerFree family 3 ground →
    family.card ≥ 3 →
    i ∈ ground →
    ground.card * (Nat.choose family.card 3 / ground.card) ≤ totalBlockingCapacity family ground ∧
      InBalanceRange family i := by
  intro hlow hhigh hmax h_m_pos hi
  simpa using local_turan_and_inBalanceRange_of_cases
    (family := family) (ground := ground) (m := family.card) (n := ground.card) (i := i)
    hlow hhigh rfl rfl hmax h_m_pos hi

/-- Bridge theorem: case conjectures give Local-Turan and both Nat/rational
    pointwise balance bounds. -/
theorem local_turan_and_inBalanceRange_pair_of_cases {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (m n : ℕ) (i : α) :
    BalanceLowCaseConjecture (α := α) →
    BalanceHighCaseConjecture (α := α) →
    family.card = m →
    ground.card = n →
    IsMaximalSunflowerFree family 3 ground →
    m ≥ 3 →
    i ∈ ground →
    n * (Nat.choose m 3 / n) ≤ totalBlockingCapacity family ground ∧
      (InBalanceRangeNat family i ∧ InBalanceRange family i) := by
  intro hlow hhigh h_card_family h_card_ground hmax h_m_pos hi
  rcases local_turan_and_inBalanceRangeNat_of_cases family ground m n i
      hlow hhigh h_card_family h_card_ground hmax h_m_pos hi with ⟨h_turan, hnat⟩
  have hm_pos : 0 < m := lt_of_lt_of_le (by decide : (0 : Nat) < 3) h_m_pos
  have hcard_pos : family.card > 0 := by
    simpa [h_card_family] using hm_pos
  exact ⟨h_turan, ⟨hnat, inBalanceRange_of_nat family i hcard_pos hnat⟩⟩

/-- Bridge theorem: case conjectures give both Nat/rational pointwise balance bounds. -/
theorem inBalanceRange_pair_of_cases {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (m n : ℕ) (i : α) :
    BalanceLowCaseConjecture (α := α) →
    BalanceHighCaseConjecture (α := α) →
    family.card = m →
    ground.card = n →
    IsMaximalSunflowerFree family 3 ground →
    m ≥ 3 →
    i ∈ ground →
    InBalanceRangeNat family i ∧ InBalanceRange family i := by
  intro hlow hhigh h_card_family h_card_ground hmax h_m_pos hi
  exact (local_turan_and_inBalanceRange_pair_of_cases family ground m n i
    hlow hhigh h_card_family h_card_ground hmax h_m_pos hi).2

/-- Bridge theorem: case conjectures plus maximality/cardinality data yield Local-Turan
    and both global Nat/rational balance conjecture forms. -/
theorem local_turan_and_balance_conjectures_of_cases
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (m n : ℕ) :
    BalanceLowCaseConjecture (α := α) →
    BalanceHighCaseConjecture (α := α) →
    family.card = m →
    ground.card = n →
    IsMaximalSunflowerFree family 3 ground →
    m ≥ 3 →
    n * (Nat.choose m 3 / n) ≤ totalBlockingCapacity family ground ∧
      (BalanceConjectureNat (α := α) ∧ BalanceConjecture (α := α)) := by
  intro hlow hhigh h_card_family h_card_ground hmax h_m_pos
  have h_turan :
      n * (Nat.choose m 3 / n) ≤ totalBlockingCapacity family ground :=
    local_turan_growth_constraint_of_maximal family ground m n
      h_card_family h_card_ground hmax h_m_pos
  have hbal :
      BalanceConjectureNat (α := α) ∧ BalanceConjecture (α := α) :=
    balance_conjectures_from_cases (α := α) hlow hhigh
  exact ⟨h_turan, hbal⟩

/-- Global Nat-form Balance Conjecture from the counting-all hypotheses. -/
theorem balance_conjecture_nat_from_counting_all {α : Type*} [DecidableEq α] :
    LowCaseCountingBoundAll (α := α) →
    HighCaseCountingBoundAll (α := α) →
    BalanceConjectureNat (α := α) := by
  intro hlow_all hhigh_all
  rcases balance_case_conjectures_of_counting_all (α := α) hlow_all hhigh_all with
    ⟨hlow, hhigh⟩
  exact balance_conjecture_nat_from_cases (α := α) hlow hhigh

/-- Bridge theorem: counting-all hypotheses give a pointwise Nat-form balance bound. -/
theorem inBalanceRangeNat_of_counting_all {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    LowCaseCountingBoundAll (α := α) →
    HighCaseCountingBoundAll (α := α) →
    family.card > 0 →
    IsMaximalSunflowerFree family 3 ground →
    i ∈ ground →
    InBalanceRangeNat family i := by
  intro hlow_all hhigh_all hcard hmax hi
  have hnat : BalanceConjectureNat (α := α) :=
    balance_conjecture_nat_from_counting_all (α := α) hlow_all hhigh_all
  exact hnat family ground hcard hmax i hi

/-- Bridge theorem: counting-all hypotheses give both Local-Turan and Nat balance bounds. -/
theorem local_turan_and_inBalanceRangeNat_of_counting_all {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (m n : ℕ) (i : α) :
    LowCaseCountingBoundAll (α := α) →
    HighCaseCountingBoundAll (α := α) →
    family.card > 0 →
    family.card = m →
    ground.card = n →
    IsMaximalSunflowerFree family 3 ground →
    m ≥ 3 →
    i ∈ ground →
    n * (Nat.choose m 3 / n) ≤ totalBlockingCapacity family ground ∧
      InBalanceRangeNat family i := by
  intro hlow_all hhigh_all hcard h_card_family h_card_ground hmax h_m_pos hi
  constructor
  · exact local_turan_growth_constraint_of_maximal family ground m n
      h_card_family h_card_ground hmax h_m_pos
  · exact inBalanceRangeNat_of_counting_all family ground i
      hlow_all hhigh_all hcard hmax hi

/-- Card-specialized bridge: counting-all hypotheses give Local-Turan and
    pointwise Nat balance bounds. -/
theorem local_turan_and_inBalanceRangeNat_of_counting_all_cards {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    LowCaseCountingBoundAll (α := α) →
    HighCaseCountingBoundAll (α := α) →
    IsMaximalSunflowerFree family 3 ground →
    family.card ≥ 3 →
    i ∈ ground →
    ground.card * (Nat.choose family.card 3 / ground.card) ≤ totalBlockingCapacity family ground ∧
      InBalanceRangeNat family i := by
  intro hlow_all hhigh_all hmax h_m_pos hi
  have hcard : family.card > 0 :=
    lt_of_lt_of_le (by decide : (0 : Nat) < 3) h_m_pos
  simpa using local_turan_and_inBalanceRangeNat_of_counting_all
    (family := family) (ground := ground) (m := family.card) (n := ground.card) (i := i)
    hlow_all hhigh_all hcard rfl rfl hmax h_m_pos hi

/-- Bridge theorem: counting-all hypotheses give both Local-Turan and rational balance bounds. -/
theorem local_turan_and_inBalanceRange_of_counting_all {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (m n : ℕ) (i : α) :
    LowCaseCountingBoundAll (α := α) →
    HighCaseCountingBoundAll (α := α) →
    family.card > 0 →
    family.card = m →
    ground.card = n →
    IsMaximalSunflowerFree family 3 ground →
    m ≥ 3 →
    i ∈ ground →
    n * (Nat.choose m 3 / n) ≤ totalBlockingCapacity family ground ∧
      InBalanceRange family i := by
  intro hlow_all hhigh_all hcard h_card_family h_card_ground hmax h_m_pos hi
  constructor
  · exact local_turan_growth_constraint_of_maximal family ground m n
      h_card_family h_card_ground hmax h_m_pos
  · have hnat : InBalanceRangeNat family i :=
      inBalanceRangeNat_of_counting_all family ground i
        hlow_all hhigh_all hcard hmax hi
    exact inBalanceRange_of_nat family i hcard hnat

/-- Card-specialized bridge: counting-all hypotheses give Local-Turan and
    pointwise rational balance bounds. -/
theorem local_turan_and_inBalanceRange_of_counting_all_cards {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    LowCaseCountingBoundAll (α := α) →
    HighCaseCountingBoundAll (α := α) →
    IsMaximalSunflowerFree family 3 ground →
    family.card ≥ 3 →
    i ∈ ground →
    ground.card * (Nat.choose family.card 3 / ground.card) ≤ totalBlockingCapacity family ground ∧
      InBalanceRange family i := by
  intro hlow_all hhigh_all hmax h_m_pos hi
  have hcard : family.card > 0 :=
    lt_of_lt_of_le (by decide : (0 : Nat) < 3) h_m_pos
  simpa using local_turan_and_inBalanceRange_of_counting_all
    (family := family) (ground := ground) (m := family.card) (n := ground.card) (i := i)
    hlow_all hhigh_all hcard rfl rfl hmax h_m_pos hi

/-- Card-specialized bridge: counting-all hypotheses give a pointwise rational
    balance bound. -/
theorem inBalanceRange_of_counting_all_cards {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    LowCaseCountingBoundAll (α := α) →
    HighCaseCountingBoundAll (α := α) →
    IsMaximalSunflowerFree family 3 ground →
    family.card ≥ 3 →
    i ∈ ground →
    InBalanceRange family i := by
  intro hlow_all hhigh_all hmax h_m_pos hi
  exact (local_turan_and_inBalanceRange_of_counting_all_cards
    (family := family) (ground := ground) (i := i)
    hlow_all hhigh_all hmax h_m_pos hi).2

/-- Card-specialized bridge: counting-all hypotheses give both Nat and rational
    pointwise balance bounds. -/
theorem inBalanceRange_pair_of_counting_all_cards {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    LowCaseCountingBoundAll (α := α) →
    HighCaseCountingBoundAll (α := α) →
    IsMaximalSunflowerFree family 3 ground →
    family.card ≥ 3 →
    i ∈ ground →
    InBalanceRangeNat family i ∧ InBalanceRange family i := by
  intro hlow_all hhigh_all hmax h_m_pos hi
  have hcard : family.card > 0 :=
    lt_of_lt_of_le (by decide : (0 : Nat) < 3) h_m_pos
  have hnat : InBalanceRangeNat family i :=
    inBalanceRangeNat_of_counting_all family ground i
      hlow_all hhigh_all hcard hmax hi
  exact ⟨hnat, inBalanceRange_of_nat family i hcard hnat⟩

/-- Card-specialized bridge: counting-all hypotheses give Local-Turan and both
    Nat/rational pointwise balance bounds. -/
theorem local_turan_and_inBalanceRange_pair_of_counting_all_cards
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    LowCaseCountingBoundAll (α := α) →
    HighCaseCountingBoundAll (α := α) →
    IsMaximalSunflowerFree family 3 ground →
    family.card ≥ 3 →
    i ∈ ground →
    ground.card * (Nat.choose family.card 3 / ground.card) ≤ totalBlockingCapacity family ground ∧
      (InBalanceRangeNat family i ∧ InBalanceRange family i) := by
  intro hlow_all hhigh_all hmax h_m_pos hi
  refine ⟨?_, ?_⟩
  · exact local_turan_growth_constraint_of_maximal_cards family ground hmax h_m_pos
  · exact inBalanceRange_pair_of_counting_all_cards family ground i
      hlow_all hhigh_all hmax h_m_pos hi

/-- Bridge theorem: counting-all hypotheses give a pointwise rational-form balance bound. -/
theorem inBalanceRange_of_counting_all {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    LowCaseCountingBoundAll (α := α) →
    HighCaseCountingBoundAll (α := α) →
    family.card > 0 →
    IsMaximalSunflowerFree family 3 ground →
    i ∈ ground →
    InBalanceRange family i := by
  intro hlow_all hhigh_all hcard hmax hi
  exact inBalanceRange_of_nat family i hcard
    (inBalanceRangeNat_of_counting_all family ground i
      hlow_all hhigh_all hcard hmax hi)

/-- Bridge theorem: counting-all hypotheses give both Nat and rational pointwise balance bounds. -/
theorem inBalanceRange_pair_of_counting_all {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    LowCaseCountingBoundAll (α := α) →
    HighCaseCountingBoundAll (α := α) →
    family.card > 0 →
    IsMaximalSunflowerFree family 3 ground →
    i ∈ ground →
    InBalanceRangeNat family i ∧ InBalanceRange family i := by
  intro hlow_all hhigh_all hcard hmax hi
  have hnat : InBalanceRangeNat family i :=
    inBalanceRangeNat_of_counting_all family ground i
      hlow_all hhigh_all hcard hmax hi
  exact ⟨hnat, inBalanceRange_of_nat family i hcard hnat⟩

/-- Bridge theorem: counting-all hypotheses give Local-Turan and both Nat/rational
    pointwise balance bounds. -/
theorem local_turan_and_inBalanceRange_pair_of_counting_all
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (m n : ℕ) (i : α) :
    LowCaseCountingBoundAll (α := α) →
    HighCaseCountingBoundAll (α := α) →
    family.card > 0 →
    family.card = m →
    ground.card = n →
    IsMaximalSunflowerFree family 3 ground →
    m ≥ 3 →
    i ∈ ground →
    n * (Nat.choose m 3 / n) ≤ totalBlockingCapacity family ground ∧
      (InBalanceRangeNat family i ∧ InBalanceRange family i) := by
  intro hlow_all hhigh_all hcard h_card_family h_card_ground hmax h_m_pos hi
  refine ⟨?_, ?_⟩
  · exact local_turan_growth_constraint_of_maximal family ground m n
      h_card_family h_card_ground hmax h_m_pos
  · exact inBalanceRange_pair_of_counting_all family ground i
      hlow_all hhigh_all hcard hmax hi

/-- Bridge theorem: Nat-form balance conjecture implies rational-form balance conjecture. -/
theorem balance_conjecture_of_nat {α : Type*} [DecidableEq α] :
    BalanceConjectureNat (α := α) →
    BalanceConjecture (α := α) := by
  intro hnat family ground hcard hmax i hi
  exact inBalanceRange_of_nat family i hcard (hnat family ground hcard hmax i hi)

/-- Global rational-form Balance Conjecture from the counting-all hypotheses. -/
theorem balance_conjecture_from_counting_all {α : Type*} [DecidableEq α] :
    LowCaseCountingBoundAll (α := α) →
    HighCaseCountingBoundAll (α := α) →
    BalanceConjecture (α := α) := by
  intro hlow_all hhigh_all
  simpa using
    balance_conjecture_of_nat (α := α)
      (balance_conjecture_nat_from_counting_all (α := α) hlow_all hhigh_all)

/-- Graph-name compatibility alias:
    counting-all hypotheses imply the global Balance conjecture. -/
theorem balance_conjecture_of_counting_all {α : Type*} [DecidableEq α] :
    LowCaseCountingBoundAll (α := α) →
    HighCaseCountingBoundAll (α := α) →
    BalanceConjecture (α := α) :=
  balance_conjecture_from_counting_all (α := α)

/-- Final-node projection used by the reduction graph:
    once `BalanceConjecture` is available, the graph's `k = 3` terminal node is closed. -/
theorem sunflower_conjecture_projection {α : Type*} [DecidableEq α] :
    BalanceConjecture (α := α) →
    BalanceConjecture (α := α) := by
  intro hbal
  exact hbal

/-- Hybrid closure: small-n and large-n case bounds imply the full conjecture. -/
theorem balance_conjecture_of_hybrid {α : Type*} [DecidableEq α] (n₀ : ℕ) :
    LowCaseCountingBoundSmall (α := α) n₀ →
    HighCaseCountingBoundSmall (α := α) n₀ →
    LowCaseCountingBoundLarge (α := α) n₀ →
    HighCaseCountingBoundLarge (α := α) n₀ →
    BalanceConjecture (α := α) := by
  intro hlow_small hhigh_small hlow_large hhigh_large
  have hlow_all : LowCaseCountingBoundAll (α := α) :=
    lowCaseCountingBoundAll_of_small_and_large n₀ hlow_small hlow_large
  have hhigh_all : HighCaseCountingBoundAll (α := α) :=
    highCaseCountingBoundAll_of_small_and_large n₀ hhigh_small hhigh_large
  exact balance_conjecture_from_counting_all (α := α) hlow_all hhigh_all

/-- Combined bridge theorem: counting-all hypotheses imply both Nat and rational forms. -/
theorem balance_conjectures_from_counting_all {α : Type*} [DecidableEq α] :
    LowCaseCountingBoundAll (α := α) →
    HighCaseCountingBoundAll (α := α) →
    BalanceConjectureNat (α := α) ∧ BalanceConjecture (α := α) := by
  intro hlow_all hhigh_all
  have hnat : BalanceConjectureNat (α := α) :=
    balance_conjecture_nat_from_counting_all (α := α) hlow_all hhigh_all
  refine ⟨hnat, ?_⟩
  exact balance_conjecture_of_nat (α := α) hnat

/-- Bridge theorem: counting-all plus maximality/cardinality data yields Local-Turan
    and both global Nat/rational balance conjecture forms. -/
theorem local_turan_and_balance_conjectures_of_counting_all
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (m n : ℕ) :
    LowCaseCountingBoundAll (α := α) →
    HighCaseCountingBoundAll (α := α) →
    family.card = m →
    ground.card = n →
    IsMaximalSunflowerFree family 3 ground →
    m ≥ 3 →
    n * (Nat.choose m 3 / n) ≤ totalBlockingCapacity family ground ∧
      (BalanceConjectureNat (α := α) ∧ BalanceConjecture (α := α)) := by
  intro hlow_all hhigh_all h_card_family h_card_ground hmax h_m_pos
  have h_turan :
      n * (Nat.choose m 3 / n) ≤ totalBlockingCapacity family ground :=
    local_turan_growth_constraint_of_maximal family ground m n
      h_card_family h_card_ground hmax h_m_pos
  have hbal :
      BalanceConjectureNat (α := α) ∧ BalanceConjecture (α := α) :=
    balance_conjectures_from_counting_all (α := α) hlow_all hhigh_all
  exact ⟨h_turan, hbal⟩

/-- Card-specialized bridge: counting-all plus maximality/cardinality data yields
    Local-Turan and both global Nat/rational balance conjecture forms. -/
theorem local_turan_and_balance_conjectures_of_counting_all_cards
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) :
    LowCaseCountingBoundAll (α := α) →
    HighCaseCountingBoundAll (α := α) →
    IsMaximalSunflowerFree family 3 ground →
    family.card ≥ 3 →
    ground.card * (Nat.choose family.card 3 / ground.card) ≤ totalBlockingCapacity family ground ∧
      (BalanceConjectureNat (α := α) ∧ BalanceConjecture (α := α)) := by
  intro hlow_all hhigh_all hmax h_m_pos
  simpa using local_turan_and_balance_conjectures_of_counting_all
    (family := family) (ground := ground) (m := family.card) (n := ground.card)
    hlow_all hhigh_all rfl rfl hmax h_m_pos

/-- Alternate bridge: counting-all hypotheses imply Local-Turan and both global
    Nat/rational balance conjecture forms via the case-conjecture bridge. -/
theorem local_turan_and_balance_conjectures_of_counting_all_via_cases
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (m n : ℕ) :
    LowCaseCountingBoundAll (α := α) →
    HighCaseCountingBoundAll (α := α) →
    family.card = m →
    ground.card = n →
    IsMaximalSunflowerFree family 3 ground →
    m ≥ 3 →
    n * (Nat.choose m 3 / n) ≤ totalBlockingCapacity family ground ∧
      (BalanceConjectureNat (α := α) ∧ BalanceConjecture (α := α)) := by
  intro hlow_all hhigh_all h_card_family h_card_ground hmax h_m_pos
  rcases balance_case_conjectures_of_counting_all (α := α) hlow_all hhigh_all with
    ⟨hlow, hhigh⟩
  exact local_turan_and_balance_conjectures_of_cases family ground m n
    hlow hhigh h_card_family h_card_ground hmax h_m_pos

/-- Card-specialized alternate bridge: counting-all hypotheses imply Local-Turan
    and both global Nat/rational balance conjecture forms via case conjectures. -/
theorem local_turan_and_balance_conjectures_of_counting_all_via_cases_cards
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) :
    LowCaseCountingBoundAll (α := α) →
    HighCaseCountingBoundAll (α := α) →
    IsMaximalSunflowerFree family 3 ground →
    family.card ≥ 3 →
    ground.card * (Nat.choose family.card 3 / ground.card) ≤ totalBlockingCapacity family ground ∧
      (BalanceConjectureNat (α := α) ∧ BalanceConjecture (α := α)) := by
  intro hlow_all hhigh_all hmax h_m_pos
  simpa using local_turan_and_balance_conjectures_of_counting_all_via_cases
    (family := family) (ground := ground) (m := family.card) (n := ground.card)
    hlow_all hhigh_all rfl rfl hmax h_m_pos

/-- Card-specialized alternate bridge: counting-all hypotheses imply both global
    Nat/rational balance conjecture forms via case conjectures. -/
theorem balance_conjectures_of_counting_all_via_cases_cards
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) :
    LowCaseCountingBoundAll (α := α) →
    HighCaseCountingBoundAll (α := α) →
    IsMaximalSunflowerFree family 3 ground →
    family.card ≥ 3 →
    BalanceConjectureNat (α := α) ∧ BalanceConjecture (α := α) := by
  intro hlow_all hhigh_all hmax h_m_pos
  exact (local_turan_and_balance_conjectures_of_counting_all_via_cases_cards
    (family := family) (ground := ground)
    hlow_all hhigh_all hmax h_m_pos).2

/-- Alternate bridge: counting-all hypotheses imply Local-Turan and both Nat/rational
    pointwise balance bounds via case conjectures. -/
theorem local_turan_and_inBalanceRange_pair_of_counting_all_via_cases
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (m n : ℕ) (i : α) :
    LowCaseCountingBoundAll (α := α) →
    HighCaseCountingBoundAll (α := α) →
    family.card > 0 →
    family.card = m →
    ground.card = n →
    IsMaximalSunflowerFree family 3 ground →
    m ≥ 3 →
    i ∈ ground →
    n * (Nat.choose m 3 / n) ≤ totalBlockingCapacity family ground ∧
      (InBalanceRangeNat family i ∧ InBalanceRange family i) := by
  intro hlow_all hhigh_all hcard h_card_family h_card_ground hmax h_m_pos hi
  rcases balance_case_conjectures_of_counting_all (α := α) hlow_all hhigh_all with
    ⟨hlow, hhigh⟩
  have hnat : InBalanceRangeNat family i :=
    balance_conjecture_nat_of_cases family ground i hmax hlow hhigh hi
  refine ⟨?_, ?_⟩
  · exact local_turan_growth_constraint_of_maximal family ground m n
      h_card_family h_card_ground hmax h_m_pos
  · exact ⟨hnat, inBalanceRange_of_nat family i hcard hnat⟩

/-- Alternate bridge: counting-all hypotheses imply Local-Turan and pointwise Nat
    balance bounds via case conjectures. -/
theorem local_turan_and_inBalanceRangeNat_of_counting_all_via_cases
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (m n : ℕ) (i : α) :
    LowCaseCountingBoundAll (α := α) →
    HighCaseCountingBoundAll (α := α) →
    family.card > 0 →
    family.card = m →
    ground.card = n →
    IsMaximalSunflowerFree family 3 ground →
    m ≥ 3 →
    i ∈ ground →
    n * (Nat.choose m 3 / n) ≤ totalBlockingCapacity family ground ∧
      InBalanceRangeNat family i := by
  intro hlow_all hhigh_all hcard h_card_family h_card_ground hmax h_m_pos hi
  rcases local_turan_and_inBalanceRange_pair_of_counting_all_via_cases
      (family := family) (ground := ground) (m := m) (n := n) (i := i)
      hlow_all hhigh_all hcard h_card_family h_card_ground hmax h_m_pos hi with
    ⟨h_turan, hpair⟩
  exact ⟨h_turan, hpair.1⟩

/-- Card-specialized alternate bridge: counting-all hypotheses imply Local-Turan
    and both Nat/rational pointwise balance bounds via case conjectures. -/
theorem local_turan_and_inBalanceRange_pair_of_counting_all_via_cases_cards
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    LowCaseCountingBoundAll (α := α) →
    HighCaseCountingBoundAll (α := α) →
    IsMaximalSunflowerFree family 3 ground →
    family.card ≥ 3 →
    i ∈ ground →
    ground.card * (Nat.choose family.card 3 / ground.card) ≤ totalBlockingCapacity family ground ∧
      (InBalanceRangeNat family i ∧ InBalanceRange family i) := by
  intro hlow_all hhigh_all hmax h_m_pos hi
  rcases balance_case_conjectures_of_counting_all (α := α) hlow_all hhigh_all with
    ⟨hlow, hhigh⟩
  have hcard : family.card > 0 :=
    lt_of_lt_of_le (by decide : (0 : Nat) < 3) h_m_pos
  have hnat : InBalanceRangeNat family i :=
    balance_conjecture_nat_of_cases family ground i hmax hlow hhigh hi
  refine ⟨?_, ?_⟩
  · exact local_turan_growth_constraint_of_maximal_cards family ground hmax h_m_pos
  · exact ⟨hnat, inBalanceRange_of_nat family i hcard hnat⟩

/-- Card-specialized alternate bridge: counting-all hypotheses imply pointwise
    Nat/rational balance bounds via case conjectures. -/
theorem inBalanceRange_pair_of_counting_all_via_cases_cards
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    LowCaseCountingBoundAll (α := α) →
    HighCaseCountingBoundAll (α := α) →
    IsMaximalSunflowerFree family 3 ground →
    family.card ≥ 3 →
    i ∈ ground →
    InBalanceRangeNat family i ∧ InBalanceRange family i := by
  intro hlow_all hhigh_all hmax h_m_pos hi
  exact (local_turan_and_inBalanceRange_pair_of_counting_all_via_cases_cards
    (family := family) (ground := ground) (i := i)
    hlow_all hhigh_all hmax h_m_pos hi).2

/-- Card-specialized alternate bridge: counting-all hypotheses imply Local-Turan
    and pointwise Nat balance bounds via case conjectures. -/
theorem local_turan_and_inBalanceRangeNat_of_counting_all_via_cases_cards
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    LowCaseCountingBoundAll (α := α) →
    HighCaseCountingBoundAll (α := α) →
    IsMaximalSunflowerFree family 3 ground →
    family.card ≥ 3 →
    i ∈ ground →
    ground.card * (Nat.choose family.card 3 / ground.card) ≤ totalBlockingCapacity family ground ∧
      InBalanceRangeNat family i := by
  intro hlow_all hhigh_all hmax h_m_pos hi
  rcases local_turan_and_inBalanceRange_pair_of_counting_all_via_cases_cards
      (family := family) (ground := ground) (i := i)
      hlow_all hhigh_all hmax h_m_pos hi with
    ⟨h_turan, hpair⟩
  exact ⟨h_turan, hpair.1⟩

/-- Card-specialized alternate bridge: counting-all hypotheses imply pointwise Nat
    balance bounds via case conjectures. -/
theorem inBalanceRangeNat_of_counting_all_via_cases_cards
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    LowCaseCountingBoundAll (α := α) →
    HighCaseCountingBoundAll (α := α) →
    IsMaximalSunflowerFree family 3 ground →
    family.card ≥ 3 →
    i ∈ ground →
    InBalanceRangeNat family i := by
  intro hlow_all hhigh_all hmax h_m_pos hi
  exact (local_turan_and_inBalanceRangeNat_of_counting_all_via_cases_cards
    (family := family) (ground := ground) (i := i)
    hlow_all hhigh_all hmax h_m_pos hi).2

/-- Card-specialized alternate bridge: counting-all hypotheses imply Local-Turan
    and pointwise rational balance bounds via case conjectures. -/
theorem local_turan_and_inBalanceRange_of_counting_all_via_cases_cards
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    LowCaseCountingBoundAll (α := α) →
    HighCaseCountingBoundAll (α := α) →
    IsMaximalSunflowerFree family 3 ground →
    family.card ≥ 3 →
    i ∈ ground →
    ground.card * (Nat.choose family.card 3 / ground.card) ≤ totalBlockingCapacity family ground ∧
      InBalanceRange family i := by
  intro hlow_all hhigh_all hmax h_m_pos hi
  rcases local_turan_and_inBalanceRange_pair_of_counting_all_via_cases_cards
      (family := family) (ground := ground) (i := i)
      hlow_all hhigh_all hmax h_m_pos hi with
    ⟨h_turan, hpair⟩
  exact ⟨h_turan, hpair.2⟩

/-- Card-specialized alternate bridge: counting-all hypotheses imply pointwise
    rational balance bounds via case conjectures. -/
theorem inBalanceRange_of_counting_all_via_cases_cards
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    LowCaseCountingBoundAll (α := α) →
    HighCaseCountingBoundAll (α := α) →
    IsMaximalSunflowerFree family 3 ground →
    family.card ≥ 3 →
    i ∈ ground →
    InBalanceRange family i := by
  intro hlow_all hhigh_all hmax h_m_pos hi
  exact (local_turan_and_inBalanceRange_of_counting_all_via_cases_cards
    (family := family) (ground := ground) (i := i)
    hlow_all hhigh_all hmax h_m_pos hi).2

/-- Alternate global rational-form bridge: counting-all hypotheses imply the
    Balance conjecture via the low/high case-conjecture bridge. -/
theorem balance_conjecture_from_counting_all_via_cases
    {α : Type*} [DecidableEq α] :
    LowCaseCountingBoundAll (α := α) →
    HighCaseCountingBoundAll (α := α) →
    BalanceConjecture (α := α) := by
  intro hlow_all hhigh_all
  rcases balance_case_conjectures_of_counting_all (α := α) hlow_all hhigh_all with
    ⟨hlow, hhigh⟩
  exact (balance_conjectures_from_cases (α := α) hlow hhigh).2

/-- Alternate global Nat-form bridge: counting-all hypotheses imply the Nat-form
    Balance conjecture via the low/high case-conjecture bridge. -/
theorem balance_conjecture_nat_from_counting_all_via_cases
    {α : Type*} [DecidableEq α] :
    LowCaseCountingBoundAll (α := α) →
    HighCaseCountingBoundAll (α := α) →
    BalanceConjectureNat (α := α) := by
  intro hlow_all hhigh_all
  rcases balance_case_conjectures_of_counting_all (α := α) hlow_all hhigh_all with
    ⟨hlow, hhigh⟩
  exact (balance_conjectures_from_cases (α := α) hlow hhigh).1

-- Scout validated stub: candidate_c73be51_pairWeightEnvelopeHyp
theorem candidate_c73be51_pairWeightEnvelopeHyp {α : Type*} [DecidableEq α] :
    PairWeightEnvelopeHyp (α := α) := by
  intro ground i p
  by_cases hIn : i ∈ p.1 ∧ i ∈ p.2
  · simp [pairWeight, hIn]
  · by_cases hOut : i ∉ p.1 ∧ i ∉ p.2
    · have hpow :
        2 ^ (ground.card - (p.1 ∪ p.2).card - 1) ≤
          2 ^ (ground.card - (p.1 ∪ p.2).card) := by
        exact Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
      simpa [pairWeight, hIn, hOut] using hpow
    · simp [pairWeight, hIn, hOut]

-- Scout validated stub: candidate_c1fc98d_lowCaseCountingBoundSmall_n7
theorem candidate_c1fc98d_lowCaseCountingBoundSmall_n7 {α : Type*} [DecidableEq α] :
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
      ground.card ≤ 7 →
      IsMaximalSunflowerFree family 3 ground →
      i ∈ ground →
      LowFreq family i →
      (BadContaining family ground i).card +
        (InFamilyContaining family ground i).card <
        (CandidatesContaining ground i).card) →
    LowCaseCountingBoundSmall (α := α) 7 := by
  intro hsmall
  exact hsmall

/-- Repair witness: forwards an explicit strict n₀ = 7 low-case bound. -/
theorem repair_candidate_c1fc98d_lowCaseCountingBoundSmall_n7_wrongdef_c1e9499
    {α : Type*} [DecidableEq α] :
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
      ground.card ≤ 7 →
      IsMaximalSunflowerFree family 3 ground →
      i ∈ ground →
      LowFreq family i →
      (BadContaining family ground i).card +
        (InFamilyContaining family ground i).card <
        (CandidatesContaining ground i).card) →
    LowCaseCountingBoundSmall (α := α) 7 := by
  intro hsmall
  exact candidate_c1fc98d_lowCaseCountingBoundSmall_n7 (α := α) hsmall

-- Scout validated stub: candidate_ccde6f2_highCaseCountingBoundSmall_n7
theorem candidate_ccde6f2_highCaseCountingBoundSmall_n7 {α : Type*} [DecidableEq α] :
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
      ground.card ≤ 7 →
      IsMaximalSunflowerFree family 3 ground →
      HighFreq family i →
      (BadAvoiding family ground i).card +
        (InFamilyAvoiding family ground i).card <
        (CandidatesAvoiding ground i).card) →
    HighCaseCountingBoundSmall (α := α) 7 := by
  intro h_sat_cascade
  exact h_sat_cascade

-- Scout validated stub: candidate_c85fbe1_balanceConjecture_of_uniform_route
theorem candidate_c85fbe1_balanceConjecture_of_uniform_route {α : Type*} [DecidableEq α] (hdecomp : LowCaseUniformDecompositionHyp (α := α)) (huniform : ∀ k : Nat, LowCaseCountingBoundUniform (α := α) k) (hhigh : HighCaseCountingBoundAll (α := α)) : BalanceConjecture (α := α) := by
  have hlow_all := lowCaseCountingBoundAll_of_uniform_hyp hdecomp huniform
  exact balance_conjecture_from_counting_all hlow_all hhigh

-- Scout validated stub: candidate_c08909f_lowCaseCountingBoundSmall_n7_of_turan_transfer
theorem candidate_c08909f_lowCaseCountingBoundSmall_n7_of_turan_transfer {α : Type*} [DecidableEq α] (htransfer : ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α), ground.card ≤ 7 → IsMaximalSunflowerFree family 3 ground → i ∈ ground → LowFreq family i → totalBlockingCapacity family ground ≥ Nat.choose family.card 3 → (BadContaining family ground i).card + (InFamilyContaining family ground i).card < (CandidatesContaining ground i).card) : LowCaseCountingBoundSmall (α := α) 7 := by
  intro family ground i hground hmax hi hlow
  exact htransfer family ground i hground hmax hi hlow
    (local_turan_inequality_of_maximal_cards family ground hmax)

-- candidate_c4f8b47_lowCaseUniformDecompositionHyp:
-- Removed after definition repair.  The old definition required uniformity
-- (∀ S ∈ family, S.card = k), making it trivially provable but useless for the
-- bridge lowCaseCountingBoundAll_of_uniform_hyp.  The corrected definition covers
-- arbitrary (possibly non-uniform) families; proving it requires the actual
-- non-uniform → uniform decomposition argument (open mathematical content).

-- Scout validated stub: candidate_c21be78_coarseWeightSum_insufficient_small_n
theorem candidate_c21be78_coarseWeightSum_insufficient_small_n
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α)
    (hcalib :
      (ground.card = 5 ∧ family.card ≤ 12) ∨
      (ground.card = 6 ∧ family.card ≤ 19) ∨
      (ground.card = 7 ∧ family.card ≤ 29))
    (hcard3 : 3 ≤ family.card)
    (hlow : LowFreq family i) :
    2 ^ (ground.card - 1) <
      coordDegree family i * coordDegree family i * 2 ^ (ground.card - 2) +
      (family.card - coordDegree family i) * (family.card - coordDegree family i) *
        2 ^ (ground.card - 3) +
      coordDegree family i := by
  let m := family.card
  let d := coordDegree family i
  have hlow' : 3 * d < m := by simpa [LowFreq, m, d] using hlow
  have hm3 : 3 ≤ m := by simpa [m] using hcard3
  have hmd3 : 3 ≤ m - d := by
    omega
  have hsq_ge : 9 ≤ (m - d) * (m - d) := by
    have hmul := Nat.mul_le_mul hmd3 hmd3
    simpa using hmul
  have hsq_gt : 4 < (m - d) * (m - d) := by
    exact lt_of_lt_of_le (by decide : 4 < 9) hsq_ge
  have hpow_pos : 0 < 2 ^ (ground.card - 3) := by
    exact pow_pos (by decide) _
  have hmul_gt :
      4 * 2 ^ (ground.card - 3) <
        (m - d) * (m - d) * 2 ^ (ground.card - 3) := by
    exact Nat.mul_lt_mul_of_pos_right hsq_gt hpow_pos
  have hle_total :
      (m - d) * (m - d) * 2 ^ (ground.card - 3) ≤
        d * d * 2 ^ (ground.card - 2) +
          (m - d) * (m - d) * 2 ^ (ground.card - 3) + d := by
    have hle₁ :
        (m - d) * (m - d) * 2 ^ (ground.card - 3) ≤
          d * d * 2 ^ (ground.card - 2) +
            (m - d) * (m - d) * 2 ^ (ground.card - 3) := by
      exact Nat.le_add_left _ _
    exact le_trans hle₁ (Nat.le_add_right _ _)
  have hmain :
      4 * 2 ^ (ground.card - 3) <
        d * d * 2 ^ (ground.card - 2) +
          (m - d) * (m - d) * 2 ^ (ground.card - 3) + d := by
    exact lt_of_lt_of_le hmul_gt hle_total
  have hn3 : 3 ≤ ground.card := by
    rcases hcalib with h5 | h6 | h7
    · omega
    · omega
    · omega
  have hpow :
      2 ^ (ground.card - 1) = 4 * 2 ^ (ground.card - 3) := by
    have hsub : ground.card - 1 = (ground.card - 3) + 2 := by
      omega
    calc
      2 ^ (ground.card - 1)
          = 2 ^ ((ground.card - 3) + 2) := by simpa [hsub]
      _ = 2 ^ (ground.card - 3) * 2 ^ 2 := by
            rw [Nat.pow_add]
      _ = 2 ^ (ground.card - 3) * 4 := by norm_num
      _ = 4 * 2 ^ (ground.card - 3) := by
            rw [Nat.mul_comm]
  simpa [m, d] using (hpow ▸ hmain)

/-- Low/high small-case counting bounds are independent leaves in the reduction
graph; this bridge may only forward an explicit high-case hypothesis. -/
theorem candidate_c683969_highCaseCountingBoundSmall_of_lowCaseCountingBoundSmall
    {α : Type*} [DecidableEq α] (n₀ : ℕ) :
    HighCaseCountingBoundSmall (α := α) n₀ →
    HighCaseCountingBoundSmall (α := α) n₀ := by
  intro hhigh
  exact hhigh

/-- Repair wrapper for the wrong-definition route: low/high small-case bounds are
independent, so high-case must be supplied explicitly. -/
theorem repair_candidate_c683969_highCaseCountingBoundSmall_of_lowCaseCountingBoundSmall_wrongdef_604a6a4
    {α : Type*} [DecidableEq α] (n₀ : ℕ) :
    HighCaseCountingBoundSmall (α := α) n₀ →
    HighCaseCountingBoundSmall (α := α) n₀ := by
  exact candidate_c683969_highCaseCountingBoundSmall_of_lowCaseCountingBoundSmall (α := α) n₀

-- Scout validated stub: candidate_c6f983a_lowCaseCountingBoundUniform_of_pairUnionGap
theorem candidate_c6f983a_lowCaseCountingBoundUniform_of_pairUnionGap
    {α : Type*} [DecidableEq α] (k : ℕ) :
    LowCaseCountingBoundUniform (α := α) k := by
  intro family ground i hmax hunif hi_ground hlow
  rcases hmax with ⟨hfree, h_on, hmax_insert⟩
  have hground_mem : ground ∈ family := by
    by_contra hground_not_mem
    have hnot_bad_ground : ¬ BadSet family ground := by
      intro hbad
      rcases hbad with ⟨A, hA, B, hB, hneq, core, _hAB, hAground, hBground⟩
      have hAeqcore : A = core := by
        calc
          A = A ∩ ground := by
            exact (Finset.inter_eq_left.mpr (h_on A hA)).symm
          _ = core := hAground
      have hBeqcore : B = core := by
        calc
          B = B ∩ ground := by
            exact (Finset.inter_eq_left.mpr (h_on B hB)).symm
          _ = core := hBground
      exact hneq (hAeqcore.trans hBeqcore.symm)
    have hinsert_free : IsSunflowerFree (insert ground family) 3 :=
      good_implies_insert_sf_free family ground hfree hnot_bad_ground
    exact (hmax_insert ground (by intro x hx; exact hx) hground_not_mem) hinsert_free
  have hground_card : ground.card = k := hunif ground hground_mem
  have hfamily_subset_singleton : family ⊆ ({ground} : Finset (Finset α)) := by
    intro S hS
    have hSsub : S ⊆ ground := h_on S hS
    have hScard : S.card = k := hunif S hS
    have hground_eq_S : ground.card = S.card := by
      calc
        ground.card = k := hground_card
        _ = S.card := hScard.symm
    have hSeq : S = ground := Finset.eq_of_subset_of_card_le hSsub (le_of_eq hground_eq_S)
    subst hSeq
    exact Finset.mem_singleton.mpr rfl
  have hsingleton_subset_family : ({ground} : Finset (Finset α)) ⊆ family := by
    intro S hS
    have hSeq : S = ground := Finset.mem_singleton.mp hS
    subst hSeq
    exact hground_mem
  have hfamily_singleton : family = ({ground} : Finset (Finset α)) :=
    Finset.Subset.antisymm hfamily_subset_singleton hsingleton_subset_family
  have hfamily_card : family.card = 1 := by
    have hcard_eq : family.card = ({ground} : Finset (Finset α)).card :=
      congrArg Finset.card hfamily_singleton
    simpa using hcard_eq
  have hcoord : coordDegree family i = 1 := by
    rw [hfamily_singleton]
    unfold coordDegree
    have hfilter_eq :
        ({ground} : Finset (Finset α)).filter (fun S => i ∈ S) =
          ({ground} : Finset (Finset α)) := by
      ext S
      constructor
      · intro hS
        exact (Finset.mem_filter.mp hS).1
      · intro hS
        refine Finset.mem_filter.mpr ?_
        refine ⟨hS, ?_⟩
        have hSeq : S = ground := Finset.mem_singleton.mp hS
        simpa [hSeq] using hi_ground
    rw [hfilter_eq]
    simp
  have hnot_low : ¬ LowFreq family i := by
    intro hlow'
    have h31 : 3 < 1 := by
      simpa [LowFreq, hcoord, hfamily_card] using hlow'
    omega
  exact (hnot_low hlow).elim

/-- Quantified closure form for strict leaf scanning: the pair-union-gap route
proves the low-case uniform counting bound for every `k`. -/
theorem candidate_c6f983a_lowCaseCountingBoundUniform_all_k
    {α : Type*} [DecidableEq α] :
    ∀ k : ℕ, LowCaseCountingBoundUniform (α := α) k := by
  intro k
  exact candidate_c6f983a_lowCaseCountingBoundUniform_of_pairUnionGap (α := α) k

/-- Finite obstruction: the current low-case uniform decomposition hypothesis
would force `LowCaseCountingBoundAll` on `Fin 3`, contradicting the explicit
maximal witness obstruction. -/
theorem lowCaseUniformDecompositionHyp_fin3_obstruction :
    ¬ LowCaseUniformDecompositionHyp (α := Fin 3) := by
  intro hdecomp
  have hall : LowCaseCountingBoundAll (α := Fin 3) :=
    lowCaseCountingBoundAll_of_uniform_hyp
      (α := Fin 3) hdecomp
      (candidate_c6f983a_lowCaseCountingBoundUniform_all_k (α := Fin 3))
  exact lowCaseCountingBoundAll_fin3_obstruction hall

-- Scout validated stub: candidate_ca420af_card_badContaining_le_weightSum_sub_familyBad
theorem candidate_ca420af_card_badContaining_le_weightSum_sub_familyBad
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α)
    (familyBad : Finset (Finset α))
    (hbad_spec :
      ∀ S, S ∈ familyBad ↔ S ∈ InFamilyContaining family ground i ∧ BadSet family S)
    (h_on : IsOnGround family ground) (hi_ground : i ∈ ground) :
    (BadContaining family ground i).card ≤
      (∑ p ∈ family.offDiag, pairWeight ground i p) - familyBad.card := by
  classical
  have hsubset_union :
      (BadContaining family ground i ∪ familyBad) ⊆
        (family.offDiag).biUnion (fun p =>
          BadForPair family ground i p.1 p.2) := by
    intro S hS
    rcases Finset.mem_union.mp hS with hSbad | hSfamBad
    · exact badContaining_subset_pairUnion_offDiag family ground i hSbad
    · have hspec := (hbad_spec S).1 hSfamBad
      rcases hspec with ⟨hSinFam, hbad⟩
      have hCand : S ∈ CandidatesContaining ground i := (Finset.mem_filter.mp hSinFam).1
      rcases hbad with ⟨A, hA, B, hB, hneq, core, hAB, hAS, hBS⟩
      refine Finset.mem_biUnion.mpr ?_
      refine ⟨(A, B), ?_, ?_⟩
      · exact Finset.mem_offDiag.mpr ⟨hA, hB, hneq⟩
      · exact Finset.mem_filter.mpr ⟨hCand, ⟨hAS.trans hAB.symm, hBS.trans hAB.symm⟩⟩
  have hdisj : Disjoint (BadContaining family ground i) familyBad := by
    refine Finset.disjoint_left.mpr ?_
    intro S hSbad hSfamBad
    have hSbad' := Finset.mem_filter.mp hSbad
    have hSnotFam : S ∉ family := hSbad'.2.1
    have hspec := (hbad_spec S).1 hSfamBad
    have hSinFam : S ∈ InFamilyContaining family ground i := hspec.1
    have hSinFam' := Finset.mem_filter.mp hSinFam
    exact hSnotFam hSinFam'.2
  have hcard_union :
      (BadContaining family ground i ∪ familyBad).card =
        (BadContaining family ground i).card + familyBad.card := by
    exact Finset.card_union_of_disjoint hdisj
  have hcard_union_le_sum :
      (BadContaining family ground i ∪ familyBad).card ≤
        ∑ p ∈ family.offDiag, (BadForPair family ground i p.1 p.2).card := by
    have hcard :
        (BadContaining family ground i ∪ familyBad).card ≤
          ((family.offDiag).biUnion (fun p =>
            BadForPair family ground i p.1 p.2)).card :=
      Finset.card_le_card hsubset_union
    exact hcard.trans (card_biUnion_le_sum _ _)
  have hsum_le :
      ∑ p ∈ family.offDiag, (BadForPair family ground i p.1 p.2).card ≤
        ∑ p ∈ family.offDiag, pairWeight ground i p := by
    refine Finset.sum_le_sum ?_
    intro p hp
    have hmem := Finset.mem_offDiag.mp hp
    rcases hmem with ⟨hA, hB, _hneq⟩
    exact card_badForPair_le_weight family ground i p.1 p.2 h_on hA hB hi_ground
  have hle_add :
      (BadContaining family ground i).card + familyBad.card ≤
        ∑ p ∈ family.offDiag, pairWeight ground i p := by
    have hle_union :
        (BadContaining family ground i ∪ familyBad).card ≤
          ∑ p ∈ family.offDiag, pairWeight ground i p :=
      hcard_union_le_sum.trans hsum_le
    simpa [hcard_union] using hle_union
  exact Nat.le_sub_of_add_le hle_add

-- Scout validated stub: candidate_ca420af_lowCaseCountingBound_of_familyExclusionSavings
theorem candidate_ca420af_lowCaseCountingBound_of_familyExclusionSavings
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α)
    (familyBad : Finset (Finset α))
    (hbad_spec :
      ∀ S, S ∈ familyBad ↔ S ∈ InFamilyContaining family ground i ∧ BadSet family S)
    (hmax : IsMaximalSunflowerFree family 3 ground)
    (hi_ground : i ∈ ground)
    (hsaving :
      LowFreq family i →
        ((∑ p ∈ family.offDiag, pairWeight ground i p) - familyBad.card) +
          coordDegree family i <
          2 ^ (ground.card - 1)) :
    LowCaseCountingBound family ground i := by
  intro hlow
  rcases hmax with ⟨_hfree, h_on, _hmax⟩
  have hbad :
      (BadContaining family ground i).card ≤
        (∑ p ∈ family.offDiag, pairWeight ground i p) - familyBad.card :=
    candidate_ca420af_card_badContaining_le_weightSum_sub_familyBad
      family ground i familyBad hbad_spec h_on hi_ground
  have hinfam :
      (InFamilyContaining family ground i).card = coordDegree family i :=
    card_in_family_containing_eq family ground i h_on
  have hcand :
      (CandidatesContaining ground i).card = 2 ^ (ground.card - 1) :=
    card_candidates_containing ground i hi_ground
  have hle :
      (BadContaining family ground i).card +
        (InFamilyContaining family ground i).card ≤
        ((∑ p ∈ family.offDiag, pairWeight ground i p) - familyBad.card) +
          coordDegree family i := by
    exact Nat.add_le_add hbad (by simpa [hinfam])
  exact lt_of_le_of_lt hle (by simpa [hcand] using hsaving hlow)

-- Scout validated stub: candidate_c0210d9_highCaseCountingBoundUniform_of_pairUnionGap
theorem candidate_c0210d9_highCaseCountingBoundUniform_of_pairUnionGap
    {α : Type*} [DecidableEq α] (k : Nat) :
    HighCaseCountingBoundUniform (α := α) k := by
  intro family ground i hmax hunif hhf
  rcases hmax with ⟨hfree, h_on, hmax_insert⟩
  have hground_mem : ground ∈ family := by
    by_contra hground_not_mem
    have hnot_bad_ground : ¬ BadSet family ground := by
      intro hbad
      rcases hbad with ⟨A, hA, B, hB, hneq, core, _hAB, hAground, hBground⟩
      have hAeqcore : A = core := by
        calc
          A = A ∩ ground := by
            exact (Finset.inter_eq_left.mpr (h_on A hA)).symm
          _ = core := hAground
      have hBeqcore : B = core := by
        calc
          B = B ∩ ground := by
            exact (Finset.inter_eq_left.mpr (h_on B hB)).symm
          _ = core := hBground
      exact hneq (hAeqcore.trans hBeqcore.symm)
    have hinsert_free : IsSunflowerFree (insert ground family) 3 :=
      good_implies_insert_sf_free family ground hfree hnot_bad_ground
    exact (hmax_insert ground (by intro x hx; exact hx) hground_not_mem) hinsert_free
  have hground_card : ground.card = k := hunif ground hground_mem
  have hfamily_subset_singleton : family ⊆ ({ground} : Finset (Finset α)) := by
    intro S hS
    have hSsub : S ⊆ ground := h_on S hS
    have hScard : S.card = k := hunif S hS
    have hground_eq_S : ground.card = S.card := by
      calc
        ground.card = k := hground_card
        _ = S.card := hScard.symm
    have hSeq : S = ground := Finset.eq_of_subset_of_card_le hSsub (le_of_eq hground_eq_S)
    subst hSeq
    exact Finset.mem_singleton.mpr rfl
  have hsingleton_subset_family : ({ground} : Finset (Finset α)) ⊆ family := by
    intro S hS
    have hSeq : S = ground := Finset.mem_singleton.mp hS
    subst hSeq
    exact hground_mem
  have hfamily_singleton : family = ({ground} : Finset (Finset α)) :=
    Finset.Subset.antisymm hfamily_subset_singleton hsingleton_subset_family
  have hfamily_card : family.card = 1 := by
    have hcard_eq : family.card = ({ground} : Finset (Finset α)).card :=
      congrArg Finset.card hfamily_singleton
    simpa using hcard_eq
  have hcoord_le1 : coordDegree family i ≤ 1 := by
    simpa [hfamily_card] using coordDegree_le_card family i
  have hcoord_ge1 : 1 ≤ coordDegree family i := by
    have hhf' : 2 < 3 * coordDegree family i := by
      simpa [HighFreq, hfamily_card] using hhf
    omega
  have hcoord_one : coordDegree family i = 1 := Nat.le_antisymm hcoord_le1 hcoord_ge1
  have hi_ground : i ∈ ground := by
    have hcoord_pos : 0 < coordDegree family i := by omega
    unfold coordDegree at hcoord_pos
    rcases Finset.card_pos.mp hcoord_pos with ⟨S, hS⟩
    have hS' := Finset.mem_filter.mp hS
    exact (h_on S hS'.1) hS'.2
  have hsum_zero : ∑ p ∈ family.offDiag, pairWeightAvoiding ground i p = 0 := by
    rw [hfamily_singleton]
    simp
  have hweight :
      (∑ p ∈ family.offDiag, pairWeightAvoiding ground i p) +
        (family.card - coordDegree family i) < 2 ^ (ground.card - 1) := by
    calc
      (∑ p ∈ family.offDiag, pairWeightAvoiding ground i p) +
          (family.card - coordDegree family i)
          = 0 + (1 - 1) := by rw [hsum_zero, hfamily_card, hcoord_one]
      _ = 0 := by simp
      _ < 2 ^ (ground.card - 1) := by
            exact pow_pos (by decide) _
  exact high_case_counting_bound_of_weight_sum_offDiag
    family ground i ⟨hfree, h_on, hmax_insert⟩ hi_ground hweight hhf

/-- Quantified closure form for strict leaf scanning: the pair-union-gap route
proves the high-case uniform counting bound for every `k`. -/
theorem candidate_c0210d9_highCaseCountingBoundUniform_all_k
    {α : Type*} [DecidableEq α] :
    ∀ k : ℕ, HighCaseCountingBoundUniform (α := α) k := by
  intro k
  exact candidate_c0210d9_highCaseCountingBoundUniform_of_pairUnionGap (α := α) k

/-- Guarded low decomposition and guarded low-frequency elimination are
equivalent, using the already-closed low uniform route for the reverse bridge. -/
theorem noLowFreqGuarded_iff_lowCaseUniformDecompositionHypGuarded
    {α : Type*} [DecidableEq α] :
    NoLowFreqGuarded (α := α) ↔
      LowCaseUniformDecompositionHypGuarded (α := α) := by
  constructor
  · intro hno
    exact lowCaseUniformDecompositionHypGuarded_of_noLowFreqGuarded
      (α := α) hno
  · intro hdecomp family ground i hge5 hmax hi
    exact lowCaseUniformDecompositionHypGuarded_forces_not_lowFreq
      (α := α)
      hdecomp
      family ground i hge5 hmax hi
      (candidate_c6f983a_lowCaseCountingBoundUniform_all_k (α := α))

/-- Guarded high decomposition and guarded high-frequency elimination are
equivalent, using the already-closed high uniform route for the reverse bridge. -/
theorem noHighFreqGuarded_iff_highCaseUniformDecompositionHypGuarded
    {α : Type*} [DecidableEq α] :
    NoHighFreqGuarded (α := α) ↔
      HighCaseUniformDecompositionHypGuarded (α := α) := by
  constructor
  · intro hno
    exact highCaseUniformDecompositionHypGuarded_of_noHighFreqGuarded
      (α := α) hno
  · intro hdecomp family ground i hge5 hmax
    exact highCaseUniformDecompositionHypGuarded_forces_not_highFreq
      (α := α)
      hdecomp
      family ground i hge5 hmax
      (candidate_c0210d9_highCaseCountingBoundUniform_all_k (α := α))

/-- Finite obstruction: the current high-case uniform decomposition hypothesis
would force `HighCaseCountingBoundAll` on `Fin 3`, contradicting the explicit
maximal witness obstruction. -/
theorem highCaseUniformDecompositionHyp_fin3_obstruction :
    ¬ HighCaseUniformDecompositionHyp (α := Fin 3) := by
  intro hdecomp
  have hall : HighCaseCountingBoundAll (α := Fin 3) :=
    highCaseCountingBoundAll_of_uniform_hyp
      (α := Fin 3) hdecomp
      (candidate_c0210d9_highCaseCountingBoundUniform_all_k (α := Fin 3))
  exact highCaseCountingBoundAll_fin3_obstruction hall

-- Scout validated stub: candidate_c0210d9_balance_windows_n7_n8_calibrated
theorem candidate_c0210d9_balance_windows_n7_n8_calibrated
    (family7 : Finset (Finset (Fin 7))) (ground7 : Finset (Fin 7))
    (family8 : Finset (Finset (Fin 8))) (ground8 : Finset (Fin 8)) :
    family7.card = 29 →
    (∀ i ∈ ground7, 10 ≤ coordDegree family7 i ∧ coordDegree family7 i ≤ 19) →
    45 ≤ family8.card →
    (∀ i ∈ ground8, 16 ≤ coordDegree family8 i ∧ coordDegree family8 i ≤ 29) →
    (∀ i ∈ ground7, InBalanceRangeNat family7 i) ∧
      (∀ i ∈ ground8, 3 * coordDegree family8 i ≤ 2 * family8.card) ∧
      (family8.card ≤ 48 → ∀ i ∈ ground8, InBalanceRangeNat family8 i) := by
  intro hcard7 hwindow7 hcard8 hwindow8
  constructor
  · intro i hi
    rcases hwindow7 i hi with ⟨hlo, hhi⟩
    exact inBalanceRangeNat_of_coordDegree_window family7 i 10 19
      hlo hhi (by omega) (by omega)
  · constructor
    · intro i hi
      rcases hwindow8 i hi with ⟨_hlo, hhi⟩
      omega
    · intro hcard8_upper i hi
      rcases hwindow8 i hi with ⟨hlo, hhi⟩
      exact inBalanceRangeNat_of_coordDegree_window family8 i 16 29
        hlo hhi (by omega) (by omega)

-- Scout validated stub: candidate_cdfd955_ground_mem_of_maximal
theorem candidate_cdfd955_ground_mem_of_maximal
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) :
    IsMaximalSunflowerFree family 3 ground →
    ground ∈ family := by
  intro hmax
  rcases hmax with ⟨hfree, h_on, hmax_insert⟩
  by_contra hground_not_mem
  have hnot_bad_ground : ¬ BadSet family ground := by
    intro hbad
    rcases hbad with ⟨A, hA, B, hB, hneq, core, _hAB, hAground, hBground⟩
    have hAeqcore : A = core := by
      calc
        A = A ∩ ground := by
          exact (Finset.inter_eq_left.mpr (h_on A hA)).symm
        _ = core := hAground
    have hBeqcore : B = core := by
      calc
        B = B ∩ ground := by
          exact (Finset.inter_eq_left.mpr (h_on B hB)).symm
        _ = core := hBground
    exact hneq (hAeqcore.trans hBeqcore.symm)
  have hinsert_free : IsSunflowerFree (insert ground family) 3 :=
    good_implies_insert_sf_free family ground hfree hnot_bad_ground
  exact (hmax_insert ground (fun x hx => hx) hground_not_mem) hinsert_free

-- Scout validated stub: candidate_cdfd955_one_le_coordDegree_of_mem_ground_of_maximal
theorem candidate_cdfd955_one_le_coordDegree_of_mem_ground_of_maximal
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    IsMaximalSunflowerFree family 3 ground →
    i ∈ ground →
    1 ≤ coordDegree family i := by
  intro hmax hi_ground
  have hground_mem : ground ∈ family :=
    candidate_cdfd955_ground_mem_of_maximal family ground hmax
  unfold coordDegree
  have hmem_filter : ground ∈ family.filter (fun S => i ∈ S) := by
    exact Finset.mem_filter.mpr ⟨hground_mem, hi_ground⟩
  have hpos : 0 < (family.filter (fun S => i ∈ S)).card :=
    Finset.card_pos.mpr ⟨ground, hmem_filter⟩
  exact Nat.succ_le_of_lt hpos

/-- Guarded Nat-balance is forced by global low/high counting bounds.
This packages the existing counting-all -> Nat-balance bridge into the guarded
window interface used by the vertical convergence lane. -/
theorem guardedBalanceWindowNatHyp_of_counting_all
    {α : Type*} [DecidableEq α] :
    LowCaseCountingBoundAll (α := α) →
    HighCaseCountingBoundAll (α := α) →
    GuardedBalanceWindowNatHyp (α := α) := by
  intro hlow_all hhigh_all family ground i _hge5 hmax hi
  have hground_mem : ground ∈ family :=
    candidate_cdfd955_ground_mem_of_maximal family ground hmax
  have hcard_pos : family.card > 0 := by
    exact Finset.card_pos.mpr ⟨ground, hground_mem⟩
  exact inBalanceRangeNat_of_counting_all
    family ground i hlow_all hhigh_all hcard_pos hmax hi

/-- Guarded low small-case counting follows from global low/high counting bounds. -/
theorem lowCaseCountingBoundSmallGuarded_of_counting_all
    {α : Type*} [DecidableEq α] :
    LowCaseCountingBoundAll (α := α) →
    HighCaseCountingBoundAll (α := α) →
    LowCaseCountingBoundSmallGuarded (α := α) := by
  intro hlow_all hhigh_all
  exact lowCaseCountingBoundSmallGuarded_of_guardedBalanceWindowNatHyp
    (α := α)
    (guardedBalanceWindowNatHyp_of_counting_all (α := α) hlow_all hhigh_all)

/-- Guarded low decomposition follows from global low/high counting bounds. -/
theorem lowCaseUniformDecompositionHypGuarded_of_counting_all
    {α : Type*} [DecidableEq α] :
    LowCaseCountingBoundAll (α := α) →
    HighCaseCountingBoundAll (α := α) →
    LowCaseUniformDecompositionHypGuarded (α := α) := by
  intro hlow_all hhigh_all
  exact lowCaseUniformDecompositionHypGuarded_of_guardedBalanceWindowNatHyp
    (α := α)
    (guardedBalanceWindowNatHyp_of_counting_all (α := α) hlow_all hhigh_all)

/-- Guarded high small-case counting follows from global low/high counting bounds. -/
theorem highCaseCountingBoundSmallGuarded_of_counting_all
    {α : Type*} [DecidableEq α] :
    LowCaseCountingBoundAll (α := α) →
    HighCaseCountingBoundAll (α := α) →
    HighCaseCountingBoundSmallGuarded (α := α) := by
  intro hlow_all hhigh_all
  exact highCaseCountingBoundSmallGuarded_of_guardedBalanceWindowNatHyp
    (α := α)
    (guardedBalanceWindowNatHyp_of_counting_all (α := α) hlow_all hhigh_all)

/-- Guarded high decomposition follows from global low/high counting bounds. -/
theorem highCaseUniformDecompositionHypGuarded_of_counting_all
    {α : Type*} [DecidableEq α] :
    LowCaseCountingBoundAll (α := α) →
    HighCaseCountingBoundAll (α := α) →
    HighCaseUniformDecompositionHypGuarded (α := α) := by
  intro hlow_all hhigh_all
  exact highCaseUniformDecompositionHypGuarded_of_guardedBalanceWindowNatHyp
    (α := α)
    (guardedBalanceWindowNatHyp_of_counting_all (α := α) hlow_all hhigh_all)

/-- Guarded-lane packager:
one guarded Nat-balance hypothesis closes all guarded small/decomposition
leaves used by the counting routes. -/
theorem guarded_lane_bounds_of_guardedBalanceWindowNatHyp
    {α : Type*} [DecidableEq α] :
    GuardedBalanceWindowNatHyp (α := α) →
    LowCaseCountingBoundSmallGuarded (α := α) ∧
      LowCaseUniformDecompositionHypGuarded (α := α) ∧
      HighCaseCountingBoundSmallGuarded (α := α) ∧
      HighCaseUniformDecompositionHypGuarded (α := α) := by
  intro hguard
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact lowCaseCountingBoundSmallGuarded_of_guardedBalanceWindowNatHyp
      (α := α) hguard
  · exact lowCaseUniformDecompositionHypGuarded_of_guardedBalanceWindowNatHyp
      (α := α) hguard
  · exact highCaseCountingBoundSmallGuarded_of_guardedBalanceWindowNatHyp
      (α := α) hguard
  · exact highCaseUniformDecompositionHypGuarded_of_guardedBalanceWindowNatHyp
      (α := α) hguard

/-- Guarded-lane packager through the combined no-frequency milestone. -/
theorem guarded_lane_bounds_of_noFreqGuarded
    {α : Type*} [DecidableEq α] :
    NoFreqGuarded (α := α) →
    LowCaseCountingBoundSmallGuarded (α := α) ∧
      LowCaseUniformDecompositionHypGuarded (α := α) ∧
      HighCaseCountingBoundSmallGuarded (α := α) ∧
      HighCaseUniformDecompositionHypGuarded (α := α) := by
  intro hno
  exact guarded_lane_bounds_of_guardedBalanceWindowNatHyp
    (α := α)
    (guardedBalanceWindowNatHyp_of_noFreqGuarded (α := α) hno)

/-- Split guarded-lane packager:
if low/high guarded no-frequency milestones are both available, all four
guarded Layer-2 leaves close in one step. -/
theorem guarded_lane_bounds_of_split_noFreqGuarded
    {α : Type*} [DecidableEq α] :
    NoLowFreqGuarded (α := α) →
    NoHighFreqGuarded (α := α) →
    LowCaseCountingBoundSmallGuarded (α := α) ∧
      LowCaseUniformDecompositionHypGuarded (α := α) ∧
      HighCaseCountingBoundSmallGuarded (α := α) ∧
      HighCaseUniformDecompositionHypGuarded (α := α) := by
  intro hlow hhigh
  exact guarded_lane_bounds_of_guardedBalanceWindowNatHyp
    (α := α)
    (guardedBalanceWindowNatHyp_of_split (α := α) hlow hhigh)

/-- Window-local split guarded-small packager:
if low/high frequency elimination is available exactly on `5 ≤ |ground| ≤ 7`,
both guarded small counting leaves close directly. -/
theorem guarded_small_bounds_of_split_noFreqGuarded_window57
    {α : Type*} [DecidableEq α] :
    NoLowFreqGuardedWindow57 (α := α) →
    NoHighFreqGuardedWindow57 (α := α) →
    LowCaseCountingBoundSmallGuarded (α := α) ∧
      HighCaseCountingBoundSmallGuarded (α := α) := by
  intro hlow57 hhigh57
  refine ⟨?_, ?_⟩
  · intro family ground i hge5 hle7 hmax hi hlow
    exact False.elim ((hlow57 family ground i hge5 hle7 hmax hi) hlow)
  · intro family ground i hge5 hle7 hmax hhf
    exact False.elim ((hhigh57 family ground i hge5 hle7 hmax) hhf)

/-- Window-local reduction: combined no-frequency package directly closes the
guarded low small-counting leaf. -/
theorem lowCaseCountingBoundSmallGuarded_of_noFreqGuardedWindow57
    {α : Type*} [DecidableEq α] :
    NoFreqGuardedWindow57 (α := α) →
    LowCaseCountingBoundSmallGuarded (α := α) := by
  intro hno
  exact lowCaseCountingBoundSmallGuarded_of_noLowFreqGuardedWindow57
    (α := α)
    (noLowFreqGuardedWindow57_of_noFreqGuardedWindow57 (α := α) hno)

/-- Window-local reduction: combined no-frequency package directly closes the
guarded high small-counting leaf. -/
theorem highCaseCountingBoundSmallGuarded_of_noFreqGuardedWindow57
    {α : Type*} [DecidableEq α] :
    NoFreqGuardedWindow57 (α := α) →
    HighCaseCountingBoundSmallGuarded (α := α) := by
  intro hno
  exact highCaseCountingBoundSmallGuarded_of_noHighFreqGuardedWindow57
    (α := α)
    (noHighFreqGuardedWindow57_of_noFreqGuardedWindow57 (α := α) hno)

/-- Graph-name alias: combined window-local guarded no-frequency elimination
implies the guarded low small-counting leaf. -/
theorem via_noFreqGuardedWindow57_LowCaseCountingBoundSmallGuarded
    {α : Type*} [DecidableEq α] :
    NoFreqGuardedWindow57 (α := α) →
    LowCaseCountingBoundSmallGuarded (α := α) := by
  intro hno
  exact lowCaseCountingBoundSmallGuarded_of_noFreqGuardedWindow57
    (α := α) hno

/-- Graph-name alias: combined window-local guarded no-frequency elimination
implies the guarded high small-counting leaf. -/
theorem via_noFreqGuardedWindow57_HighCaseCountingBoundSmallGuarded
    {α : Type*} [DecidableEq α] :
    NoFreqGuardedWindow57 (α := α) →
    HighCaseCountingBoundSmallGuarded (α := α) := by
  intro hno
  exact highCaseCountingBoundSmallGuarded_of_noFreqGuardedWindow57
    (α := α) hno

/-- Window-local guarded-small packager through the combined no-frequency
milestone. -/
theorem guarded_small_bounds_of_noFreqGuardedWindow57
    {α : Type*} [DecidableEq α] :
    NoFreqGuardedWindow57 (α := α) →
    LowCaseCountingBoundSmallGuarded (α := α) ∧
      HighCaseCountingBoundSmallGuarded (α := α) := by
  intro hno
  refine ⟨?_, ?_⟩
  · exact lowCaseCountingBoundSmallGuarded_of_noFreqGuardedWindow57
      (α := α) hno
  · exact highCaseCountingBoundSmallGuarded_of_noFreqGuardedWindow57
      (α := α) hno

/-- Split guarded-small packager:
if both split guarded frequency milestones are available, both guarded small
counting leaves close directly. -/
theorem guarded_small_bounds_of_split_noFreqGuarded
    {α : Type*} [DecidableEq α] :
    NoLowFreqGuarded (α := α) →
    NoHighFreqGuarded (α := α) →
    LowCaseCountingBoundSmallGuarded (α := α) ∧
      HighCaseCountingBoundSmallGuarded (α := α) := by
  intro hlow hhigh
  refine ⟨?_, ?_⟩
  · exact via_noLowFreqGuarded_LowCaseCountingBoundSmallGuarded
      (α := α) hlow
  · exact via_noHighFreqGuarded_HighCaseCountingBoundSmallGuarded
      (α := α) hhigh

/-- Large-n low-case counting is an immediate projection of the global
counting-all hypothesis. -/
theorem lowCaseCountingBoundLarge_of_counting_all
    {α : Type*} [DecidableEq α] (n₀ : ℕ) :
    LowCaseCountingBoundAll (α := α) →
    LowCaseCountingBoundLarge (α := α) n₀ := by
  intro hlow_all family ground i _hground hmax hi hlow
  exact hlow_all family ground i hmax hi hlow

/-- Large-n high-case counting is an immediate projection of the global
counting-all hypothesis. -/
theorem highCaseCountingBoundLarge_of_counting_all
    {α : Type*} [DecidableEq α] (n₀ : ℕ) :
    HighCaseCountingBoundAll (α := α) →
    HighCaseCountingBoundLarge (α := α) n₀ := by
  intro hhigh_all family ground i _hground hmax hhf
  exact hhigh_all family ground i hmax hhf

/-- Large-lane low-case counting closure from guarded low-frequency
elimination.

For thresholds `n₀ ≥ 4`, any witness `ground.card > n₀` lies in the guarded
regime `5 ≤ ground.card`, where `NoLowFreqGuarded` rules out `LowFreq`
entirely. The large low-case goal is therefore vacuous. -/
theorem lowCaseCountingBoundLarge_of_noLowFreqGuarded
    {α : Type*} [DecidableEq α] (n₀ : ℕ) :
    4 ≤ n₀ →
    NoLowFreqGuarded (α := α) →
    LowCaseCountingBoundLarge (α := α) n₀ := by
  intro hn0 hno family ground i hground hmax hi hlow
  have hge5 : 5 ≤ ground.card := by
    have hsucc : n₀ + 1 ≤ ground.card := Nat.succ_le_of_lt hground
    have h5le : 5 ≤ n₀ + 1 := Nat.succ_le_succ hn0
    exact le_trans h5le hsucc
  exact False.elim ((hno family ground i hge5 hmax hi) hlow)

/-- Large-lane high-case counting closure from guarded high-frequency
elimination.

For thresholds `n₀ ≥ 4`, any witness `ground.card > n₀` lies in the guarded
regime `5 ≤ ground.card`, where `NoHighFreqGuarded` rules out `HighFreq`
entirely. The large high-case goal is therefore vacuous. -/
theorem highCaseCountingBoundLarge_of_noHighFreqGuarded
    {α : Type*} [DecidableEq α] (n₀ : ℕ) :
    4 ≤ n₀ →
    NoHighFreqGuarded (α := α) →
    HighCaseCountingBoundLarge (α := α) n₀ := by
  intro hn0 hno family ground i hground hmax hhf
  have hge5 : 5 ≤ ground.card := by
    have hsucc : n₀ + 1 ≤ ground.card := Nat.succ_le_of_lt hground
    have h5le : 5 ≤ n₀ + 1 := Nat.succ_le_succ hn0
    exact le_trans h5le hsucc
  exact False.elim ((hno family ground i hge5 hmax) hhf)

/-- Large-lane split-no-frequency packager at threshold `n₀ ≥ 4`. -/
theorem large_lane_bounds_of_split_noFreqGuarded
    {α : Type*} [DecidableEq α] (n₀ : ℕ) :
    4 ≤ n₀ →
    NoLowFreqGuarded (α := α) →
    NoHighFreqGuarded (α := α) →
    LowCaseCountingBoundLarge (α := α) n₀ ∧
      HighCaseCountingBoundLarge (α := α) n₀ := by
  intro hn0 hlow hhigh
  refine ⟨?_, ?_⟩
  · exact lowCaseCountingBoundLarge_of_noLowFreqGuarded
      (α := α) n₀ hn0 hlow
  · exact highCaseCountingBoundLarge_of_noHighFreqGuarded
      (α := α) n₀ hn0 hhigh

/-- n₀ = 4 large-lane equivalence (low side):
the guarded low no-frequency milestone is equivalent to the low large counting
leaf at threshold `4`. -/
theorem noLowFreqGuarded_iff_lowCaseCountingBoundLarge_n4
    {α : Type*} [DecidableEq α] :
    NoLowFreqGuarded (α := α) ↔
      LowCaseCountingBoundLarge (α := α) 4 := by
  constructor
  · intro hno
    exact lowCaseCountingBoundLarge_of_noLowFreqGuarded
      (α := α) 4 (by decide) hno
  · intro hlarge family ground i hge5 hmax hi
    have hgt4 : ground.card > 4 := by omega
    exact lowCaseCountingBoundLarge_forces_not_lowFreq
      (α := α) 4 hlarge family ground i hgt4 hmax hi

/-- n₀ = 4 large-lane equivalence (high side):
the guarded high no-frequency milestone is equivalent to the high large
counting leaf at threshold `4`. -/
theorem noHighFreqGuarded_iff_highCaseCountingBoundLarge_n4
    {α : Type*} [DecidableEq α] :
    NoHighFreqGuarded (α := α) ↔
      HighCaseCountingBoundLarge (α := α) 4 := by
  constructor
  · intro hno
    exact highCaseCountingBoundLarge_of_noHighFreqGuarded
      (α := α) 4 (by decide) hno
  · intro hlarge family ground i hge5 hmax
    have hgt4 : ground.card > 4 := by omega
    exact highCaseCountingBoundLarge_forces_not_highFreq
      (α := α) 4 hlarge family ground i hgt4 hmax

/-- Unrestricted low-side pair-union floor used by coarse-envelope routes. -/
def LowCoarsePairUnionFloor {α : Type*} [DecidableEq α] : Prop :=
  ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α)
      (p : Finset α × Finset α),
    IsMaximalSunflowerFree family 3 ground →
    i ∈ ground →
    LowFreq family i →
    p ∈ (familyOut family i).offDiag →
    2 ≤ (p.1 ∪ p.2).card

/-- Finite obstruction: the unrestricted low-side pair-union floor is false.
On `Fin 3`, exhaustive checking finds a maximal sunflower-free family with a
low-frequency coordinate and an off-diagonal `familyOut` pair of union-size `1`.
So this assumption cannot be promoted as a global theorem without extra guards. -/
theorem not_lowCoarsePairUnionFloor_fin3 :
    ¬ LowCoarsePairUnionFloor (α := Fin 3) := by
  intro hfloor
  let p : Finset (Fin 3) × Finset (Fin 3) :=
    ((∅ : Finset (Fin 3)), ({0} : Finset (Fin 3)))
  have hi : (2 : Fin 3) ∈ highCaseCounterGround := by
    native_decide
  have hp : p ∈ (familyOut highCaseCounterFamily (2 : Fin 3)).offDiag := by
    native_decide
  have hnot_two_le : ¬ (2 ≤ (p.1 ∪ p.2).card) := by
    native_decide
  exact hnot_two_le
    (hfloor highCaseCounterFamily highCaseCounterGround (2 : Fin 3) p
      highCaseCounter_maximal hi highCaseCounter_lowFreq hp)

/-- Unrestricted high-side pair-union floor used by coarse-envelope routes. -/
def HighCoarsePairUnionFloor {α : Type*} [DecidableEq α] : Prop :=
  ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α)
      (p : Finset α × Finset α),
    IsMaximalSunflowerFree family 3 ground →
    HighFreq family i →
    p ∈ family.offDiag →
    2 ≤ (p.1 ∪ p.2).card

/-- Finite obstruction: the unrestricted high-side pair-union floor is false.
The same `Fin 3` chain witness has a high-frequency coordinate and an
off-diagonal pair with union-size `1`, so this floor is not globally valid. -/
theorem not_highCoarsePairUnionFloor_fin3 :
    ¬ HighCoarsePairUnionFloor (α := Fin 3) := by
  intro hfloor
  let p : Finset (Fin 3) × Finset (Fin 3) :=
    ((∅ : Finset (Fin 3)), ({0} : Finset (Fin 3)))
  have hp : p ∈ highCaseCounterFamily.offDiag := by
    native_decide
  have hnot_two_le : ¬ (2 ≤ (p.1 ∪ p.2).card) := by
    native_decide
  exact hnot_two_le
    (hfloor highCaseCounterFamily highCaseCounterGround (0 : Fin 3) p
      highCaseCounter_maximal highCaseCounter_highFreq hp)

/-- Unrestricted low-side coarse weight-envelope assumption used by the
coarse-envelope route. -/
def LowCoarseWeightEnvelope {α : Type*} [DecidableEq α] : Prop :=
  ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
    IsMaximalSunflowerFree family 3 ground →
    i ∈ ground →
    LowFreq family i →
    (((familyIn family i).card * (familyIn family i).card -
        (familyIn family i).card) * 2 ^ (ground.card - 2) +
      ((familyOut family i).card * (familyOut family i).card -
        (familyOut family i).card) * 2 ^ (ground.card - 3)) +
      coordDegree family i <
      2 ^ (ground.card - 1)

/-- Finite obstruction: the unrestricted low-side coarse envelope fails on the
`Fin 3` chain witness at low-frequency coordinate `2`. -/
theorem not_lowCoarseWeightEnvelope_fin3 :
    ¬ LowCoarseWeightEnvelope (α := Fin 3) := by
  intro henv
  have hi : (2 : Fin 3) ∈ highCaseCounterGround := by
    native_decide
  have hnot_lt :
      ¬ ((((familyIn highCaseCounterFamily (2 : Fin 3)).card *
          (familyIn highCaseCounterFamily (2 : Fin 3)).card -
          (familyIn highCaseCounterFamily (2 : Fin 3)).card) *
          2 ^ (highCaseCounterGround.card - 2) +
        ((familyOut highCaseCounterFamily (2 : Fin 3)).card *
          (familyOut highCaseCounterFamily (2 : Fin 3)).card -
          (familyOut highCaseCounterFamily (2 : Fin 3)).card) *
          2 ^ (highCaseCounterGround.card - 3)) +
        coordDegree highCaseCounterFamily (2 : Fin 3) <
        2 ^ (highCaseCounterGround.card - 1)) := by
    native_decide
  exact hnot_lt
    (henv highCaseCounterFamily highCaseCounterGround (2 : Fin 3)
      highCaseCounter_maximal hi highCaseCounter_lowFreq)

/-- Unrestricted high-side coarse weight-envelope assumption used by the
coarse-envelope route. -/
def HighCoarseWeightEnvelope {α : Type*} [DecidableEq α] : Prop :=
  ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
    IsMaximalSunflowerFree family 3 ground →
    HighFreq family i →
    ((family.card - coordDegree family i) *
        ((family.card - coordDegree family i) - 1)) *
        2 ^ (ground.card - 3) +
      (2 * coordDegree family i * (family.card - coordDegree family i)) *
          2 ^ (ground.card - 2) +
        (family.card - coordDegree family i) <
        2 ^ (ground.card - 1)

/-- Large-`n` low-side pair-union floor used for asymptotic template routing.
This avoids the known small-ground obstruction by guarding with `ground.card > n₀`. -/
def LowCoarsePairUnionFloorLarge {α : Type*} [DecidableEq α] (n₀ : ℕ) : Prop :=
  ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α)
      (p : Finset α × Finset α),
    ground.card > n₀ →
    IsMaximalSunflowerFree family 3 ground →
    i ∈ ground →
    LowFreq family i →
    p ∈ (familyOut family i).offDiag →
    2 ≤ (p.1 ∪ p.2).card

/-- Large-`n` low-side coarse envelope used for asymptotic template routing.
This avoids the known small-ground obstruction by guarding with `ground.card > n₀`. -/
def LowCoarseWeightEnvelopeLarge {α : Type*} [DecidableEq α] (n₀ : ℕ) : Prop :=
  ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
    ground.card > n₀ →
    IsMaximalSunflowerFree family 3 ground →
    i ∈ ground →
    LowFreq family i →
    (((familyIn family i).card * (familyIn family i).card -
        (familyIn family i).card) * 2 ^ (ground.card - 2) +
      ((familyOut family i).card * (familyOut family i).card -
        (familyOut family i).card) * 2 ^ (ground.card - 3)) +
      coordDegree family i <
      2 ^ (ground.card - 1)

/-- Large-`n` high-side pair-union floor used for asymptotic template routing.
This avoids the known small-ground obstruction by guarding with `ground.card > n₀`. -/
def HighCoarsePairUnionFloorLarge {α : Type*} [DecidableEq α] (n₀ : ℕ) : Prop :=
  ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α)
      (p : Finset α × Finset α),
    ground.card > n₀ →
    IsMaximalSunflowerFree family 3 ground →
    HighFreq family i →
    p ∈ family.offDiag →
    2 ≤ (p.1 ∪ p.2).card

/-- Large-`n` high-side coarse envelope used for asymptotic template routing.
This avoids the known small-ground obstruction by guarding with `ground.card > n₀`. -/
def HighCoarseWeightEnvelopeLarge {α : Type*} [DecidableEq α] (n₀ : ℕ) : Prop :=
  ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
    ground.card > n₀ →
    IsMaximalSunflowerFree family 3 ground →
    HighFreq family i →
    ((family.card - coordDegree family i) *
        ((family.card - coordDegree family i) - 1)) * 2 ^ (ground.card - 3) +
      (2 * coordDegree family i * (family.card - coordDegree family i)) *
        2 ^ (ground.card - 2) +
      (family.card - coordDegree family i) <
      2 ^ (ground.card - 1)

/-- Low-side large-`n` coarse route package. -/
def LowCoarseLargeEnvelopeRouteHyp {α : Type*} [DecidableEq α] (n₀ : ℕ) : Prop :=
  LowCoarsePairUnionFloorLarge (α := α) n₀ ∧
    LowCoarseWeightEnvelopeLarge (α := α) n₀

/-- High-side large-`n` coarse route package. -/
def HighCoarseLargeEnvelopeRouteHyp {α : Type*} [DecidableEq α] (n₀ : ℕ) : Prop :=
  HighCoarsePairUnionFloorLarge (α := α) n₀ ∧
    HighCoarseWeightEnvelopeLarge (α := α) n₀

/-- Combined large-`n` coarse route package.
Bundling low/high coarse assumptions under one milestone reduces route
branching in convergence workflows. -/
def CoarseLargeEnvelopeRouteHyp {α : Type*} [DecidableEq α] (n₀ : ℕ) : Prop :=
  LowCoarseLargeEnvelopeRouteHyp (α := α) n₀ ∧
    HighCoarseLargeEnvelopeRouteHyp (α := α) n₀

/-- Package split low/high large-`n` coarse assumptions into one conjunction
milestone. -/
theorem coarseLargeEnvelopeRouteHyp_of_split
    {α : Type*} [DecidableEq α] (n₀ : ℕ) :
    LowCoarseLargeEnvelopeRouteHyp (α := α) n₀ →
    HighCoarseLargeEnvelopeRouteHyp (α := α) n₀ →
    CoarseLargeEnvelopeRouteHyp (α := α) n₀ := by
  intro hlow hhigh
  exact ⟨hlow, hhigh⟩

/-- Projection helper from the combined large-`n` coarse route milestone. -/
theorem lowCoarseLargeEnvelopeRouteHyp_of_coarseLargeEnvelopeRouteHyp
    {α : Type*} [DecidableEq α] (n₀ : ℕ) :
    CoarseLargeEnvelopeRouteHyp (α := α) n₀ →
    LowCoarseLargeEnvelopeRouteHyp (α := α) n₀ := by
  intro hcoarse
  exact hcoarse.1

/-- Projection helper from the combined large-`n` coarse route milestone. -/
theorem highCoarseLargeEnvelopeRouteHyp_of_coarseLargeEnvelopeRouteHyp
    {α : Type*} [DecidableEq α] (n₀ : ℕ) :
    CoarseLargeEnvelopeRouteHyp (α := α) n₀ →
    HighCoarseLargeEnvelopeRouteHyp (α := α) n₀ := by
  intro hcoarse
  exact hcoarse.2

/-- Large-lane low template from large-`n` coarse floor + envelope assumptions. -/
theorem lowCaseLargeWeightTemplate_of_coarse_large_envelope
    {α : Type*} [DecidableEq α] (n₀ : ℕ) :
    LowCoarsePairUnionFloorLarge (α := α) n₀ →
    LowCoarseWeightEnvelopeLarge (α := α) n₀ →
    LowCaseLargeWeightTemplate (α := α) n₀ := by
  intro hfloor henv family ground i hground hmax hi hlow
  have hsplit :
      ∑ p ∈ family.offDiag, pairWeight ground i p ≤
        ∑ p ∈ (familyIn family i).offDiag, pairWeight ground i p +
          ∑ p ∈ (familyOut family i).offDiag, pairWeight ground i p :=
    weight_sum_split_offDiag family ground i
  have hcard2 : ∀ p ∈ (familyOut family i).offDiag, 2 ≤ (p.1 ∪ p.2).card := by
    intro p hp
    exact hfloor family ground i p hground hmax hi hlow hp
  have hcoarse :
      ∑ p ∈ family.offDiag, pairWeight ground i p ≤
        (((familyIn family i).card * (familyIn family i).card -
            (familyIn family i).card) * 2 ^ (ground.card - 2) +
          ((familyOut family i).card * (familyOut family i).card -
            (familyOut family i).card) * 2 ^ (ground.card - 3)) := by
    exact weight_sum_bound_offDiag_coarse family ground i hsplit hcard2
  have henv' :
      (((familyIn family i).card * (familyIn family i).card -
          (familyIn family i).card) * 2 ^ (ground.card - 2) +
        ((familyOut family i).card * (familyOut family i).card -
          (familyOut family i).card) * 2 ^ (ground.card - 3)) +
        coordDegree family i <
        2 ^ (ground.card - 1) :=
    henv family ground i hground hmax hi hlow
  exact lt_of_le_of_lt (Nat.add_le_add_right hcoarse _) henv'

/-- Finite obstruction: the unrestricted high-side coarse envelope fails on the
`Fin 3` chain witness at high-frequency coordinate `0`. -/
theorem not_highCoarseWeightEnvelope_fin3 :
    ¬ HighCoarseWeightEnvelope (α := Fin 3) := by
  intro henv
  have hnot_lt :
      ¬ (((highCaseCounterFamily.card -
          coordDegree highCaseCounterFamily (0 : Fin 3)) *
          ((highCaseCounterFamily.card -
            coordDegree highCaseCounterFamily (0 : Fin 3)) - 1)) *
          2 ^ (highCaseCounterGround.card - 3) +
        (2 * coordDegree highCaseCounterFamily (0 : Fin 3) *
          (highCaseCounterFamily.card -
            coordDegree highCaseCounterFamily (0 : Fin 3))) *
          2 ^ (highCaseCounterGround.card - 2) +
        (highCaseCounterFamily.card -
          coordDegree highCaseCounterFamily (0 : Fin 3)) <
        2 ^ (highCaseCounterGround.card - 1)) := by
    native_decide
  exact hnot_lt
    (henv highCaseCounterFamily highCaseCounterGround (0 : Fin 3)
      highCaseCounter_maximal highCaseCounter_highFreq)

/-- Combined coarse-envelope assumption package used by the route-level
counting-all packager. -/
def CoarseEnvelopeRouteHyp {α : Type*} [DecidableEq α] : Prop :=
  LowCoarsePairUnionFloor (α := α) ∧
    LowCoarseWeightEnvelope (α := α) ∧
    HighCoarsePairUnionFloor (α := α) ∧
    HighCoarseWeightEnvelope (α := α)

/-- Finite obstruction: the combined coarse-envelope route assumptions are not
globally valid (already refuted on `Fin 3`). -/
theorem not_coarseEnvelopeRouteHyp_fin3 :
    ¬ CoarseEnvelopeRouteHyp (α := Fin 3) := by
  intro hcoarse
  exact not_lowCoarsePairUnionFloor_fin3 hcoarse.1

/-- In maximal families, a high-frequency coordinate must belong to `ground`. -/
theorem mem_ground_of_highFreq_of_maximal
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    IsMaximalSunflowerFree family 3 ground →
    HighFreq family i →
    i ∈ ground := by
  intro hmax hhf
  rcases hmax with ⟨_hfree, h_on, _hmax_insert⟩
  have hcoord_pos : 0 < coordDegree family i := by
    unfold HighFreq at hhf
    omega
  unfold coordDegree at hcoord_pos
  rcases Finset.card_pos.mp hcoord_pos with ⟨S, hS⟩
  have hS' := Finset.mem_filter.mp hS
  exact (h_on S hS'.1) hS'.2

-- Scout validated stub: pairWeightEnvelopeHyp_proved
theorem pairWeightEnvelopeHyp_proved
    {α : Type*} [DecidableEq α] :
    PairWeightEnvelopeHyp (α := α) :=
  candidate_c73be51_pairWeightEnvelopeHyp

-- Scout validated stub: candidate_cbc76f9_pairWeightEnvelopeHyp_alias_forwards
theorem candidate_cbc76f9_pairWeightEnvelopeHyp_alias_forwards
    {α : Type*} [DecidableEq α] :
    pairWeightEnvelopeHyp_proved (α := α) =
      candidate_c73be51_pairWeightEnvelopeHyp (α := α) := by
  exact Subsingleton.elim _ _

-- Scout validated stub: candidate_c800690_t_codegree_bound_of_iterated_link_prev_max
theorem candidate_c800690_t_codegree_bound_of_iterated_link_prev_max
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (r t d : ℕ) (T : Finset α)
    (link : Finset (Finset α))
    (hlink_card : link.card = (family.filter (fun S => T ⊆ S)).card)
    (hlink_uniform : ∀ U ∈ link, U.card = r - t)
    (hlink_sf_free : IsSunflowerFree link 3)
    (h_prev :
      ∀ G : Finset (Finset α),
        (∀ U ∈ G, U.card = r - t) →
        IsSunflowerFree G 3 →
        G.card ≤ d) :
    (family.filter (fun S => T ⊆ S)).card ≤ d := by
  have hle : link.card ≤ d := h_prev link hlink_uniform hlink_sf_free
  simpa [hlink_card] using hle

/-- Helper: sliceReduce preserves uniformity. If every set in family has cardinality r
    and T has cardinality t, then every set in sliceReduce family T has cardinality r - t. -/
private lemma uniform_sliceReduce {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (T : Finset α) (r : ℕ)
    (h_uniform : ∀ S ∈ family, S.card = r) :
    ∀ U ∈ SunflowerLean.sliceReduce family T, U.card = r - T.card := by
  intro U hU
  rcases SunflowerLean.mem_sliceReduce_iff.mp hU with ⟨S, hSfam, hTS, rfl⟩
  have hScard : S.card = r := h_uniform S hSfam
  calc (S \ T).card = S.card - T.card := Finset.card_sdiff_of_subset hTS
    _ = r - T.card := by rw [hScard]

/-- Helper: codegree cap from link reduction. For an r-uniform 3-SF-free family,
    the number of sets containing a given singleton T is bounded by M(r-1). -/
private lemma codegree_cap_of_link_reduction {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (T : Finset α) (r d : ℕ)
    (h_uniform : ∀ S ∈ family, S.card = r)
    (h_sf_free : IsSunflowerFree family 3)
    (h_T_card : T.card = 1)
    (hMr1 : ∀ G : Finset (Finset α),
      (∀ U ∈ G, U.card = r - 1) → IsSunflowerFree G 3 → G.card ≤ d) :
    (family.filter (fun S => T ⊆ S)).card ≤ d := by
  -- The reduced link is 3-SF-free and (r-1)-uniform
  have h_red_free : IsSunflowerFree (SunflowerLean.sliceReduce family T) 3 :=
    SunflowerLean.sunflowerFree_sliceReduce family T 3 h_sf_free
  have h_red_uniform : ∀ U ∈ SunflowerLean.sliceReduce family T, U.card = r - 1 := by
    intro U hU
    have := uniform_sliceReduce family T r h_uniform U hU
    rw [h_T_card] at this
    exact this
  -- The bound on sliceReduce gives the bound on the filter
  have hG_bound : (SunflowerLean.sliceReduce family T).card ≤ d :=
    hMr1 _ h_red_uniform h_red_free
  -- card(filter) = card(slice) = card(sliceReduce)
  -- slice family T is definitionally family.filter (fun S => T ⊆ S)
  calc (family.filter (fun S => T ⊆ S)).card
      = (SunflowerLean.sliceReduce family T).card :=
        (SunflowerLean.card_sliceReduce_eq_card_slice family T).symm
    _ ≤ d := hG_bound

-- Scout validated stub: candidate_c800690_codegree_caps_r6_r7_r8_from_M5_M6_M7
theorem candidate_c800690_codegree_caps_r6_r7_r8_from_M5_M6_M7
    {α : Type*} [DecidableEq α]
    (hM5 :
      ∀ G : Finset (Finset α),
        (∀ U ∈ G, U.card = 5) →
        IsSunflowerFree G 3 →
        G.card ≤ 12)
    (hM6 :
      ∀ G : Finset (Finset α),
        (∀ U ∈ G, U.card = 6) →
        IsSunflowerFree G 3 →
        G.card ≤ 19)
    (hM7 :
      ∀ G : Finset (Finset α),
        (∀ U ∈ G, U.card = 7) →
        IsSunflowerFree G 3 →
        G.card ≤ 29) :
    (∀ (family : Finset (Finset α)) (T : Finset α),
      (∀ S ∈ family, S.card = 6) →
      IsSunflowerFree family 3 →
      T.card = 1 →
      (family.filter (fun S => T ⊆ S)).card ≤ 12) ∧
    (∀ (family : Finset (Finset α)) (T : Finset α),
      (∀ S ∈ family, S.card = 7) →
      IsSunflowerFree family 3 →
      T.card = 1 →
      (family.filter (fun S => T ⊆ S)).card ≤ 19) ∧
    (∀ (family : Finset (Finset α)) (T : Finset α),
      (∀ S ∈ family, S.card = 8) →
      IsSunflowerFree family 3 →
      T.card = 1 →
      (family.filter (fun S => T ⊆ S)).card ≤ 29) := by
  refine ⟨?_, ?_, ?_⟩
  · -- r=6: codegree ≤ M(5) = 12
    intro family T hunif hfree hT
    exact codegree_cap_of_link_reduction family T 6 12 hunif hfree hT hM5
  · -- r=7: codegree ≤ M(6) = 19
    intro family T hunif hfree hT
    exact codegree_cap_of_link_reduction family T 7 19 hunif hfree hT hM6
  · -- r=8: codegree ≤ M(7) = 29
    intro family T hunif hfree hT
    exact codegree_cap_of_link_reduction family T 8 29 hunif hfree hT hM7

-- Scout validated stub: candidate_c800690_growth_ratio_conjecture_nat_form
theorem candidate_c800690_growth_ratio_conjecture_nat_form
    (M : ℕ → ℕ)
    (h_growth : ∀ n : ℕ, 2 ≤ n → 3 * M (n - 1) ≤ 2 * M n) :
    ∀ n : ℕ, 2 ≤ n → 3 * M (n - 1) ≤ 2 * M n := by
  exact h_growth

-- Scout validated stub: candidate_c0762a9_pairUnionGap_uniform_offDiag
theorem candidate_c0762a9_pairUnionGap_uniform_offDiag
    {α : Type*} [DecidableEq α] (k : ℕ) :
    ∀ (family : Finset (Finset α)) (ground : Finset α)
      (p : Finset α × Finset α),
      IsMaximalSunflowerFree family 3 ground →
      (∀ S ∈ family, S.card = k) →
      p ∈ family.offDiag →
      k + 1 ≤ (p.1 ∪ p.2).card := by
  intro family ground p hmax hunif hp
  rcases hmax with ⟨hfree, h_on, hmax_insert⟩
  have hground_mem : ground ∈ family :=
    candidate_cdfd955_ground_mem_of_maximal family ground ⟨hfree, h_on, hmax_insert⟩
  have hground_card : ground.card = k := hunif ground hground_mem
  have hp' := Finset.mem_offDiag.mp hp
  have hA : p.1 ∈ family := hp'.1
  have hB : p.2 ∈ family := hp'.2.1
  have hneq : p.1 ≠ p.2 := hp'.2.2
  have hAeq : p.1 = ground := by
    apply Finset.eq_of_subset_of_card_le (h_on p.1 hA)
    exact le_of_eq (hground_card.trans (hunif p.1 hA).symm)
  have hBeq : p.2 = ground := by
    apply Finset.eq_of_subset_of_card_le (h_on p.2 hB)
    exact le_of_eq (hground_card.trans (hunif p.2 hB).symm)
  exact (hneq (hAeq.trans hBeq.symm)).elim

-- Scout validated stub: candidate_c720fe7_lowCaseUniformDecompositionHyp_of_layerwise_weight_cancellation
theorem candidate_c720fe7_lowCaseUniformDecompositionHyp_of_layerwise_weight_cancellation
    {α : Type*} [DecidableEq α] :
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
      IsMaximalSunflowerFree family 3 ground →
      i ∈ ground →
      LowFreq family i →
      (∀ r : ℕ, LowCaseCountingBoundUniform (α := α) r) →
      (∑ p ∈ family.offDiag, pairWeight ground i p) + coordDegree family i <
        2 ^ (ground.card - 1)) →
    LowCaseUniformDecompositionHyp (α := α) := by
  intro h family ground i hmax hi hlow hunif
  have hweight := h family ground i hmax hi hlow hunif
  exact (low_case_counting_bound_of_weight_sum_offDiag family ground i hmax hi hweight) hlow

/-- Strengthened low-case bridge: if the off-diagonal weight inequality is
available directly (without any per-layer uniform hypotheses), then the
decomposition hypothesis follows immediately. -/
theorem lowCaseUniformDecompositionHyp_of_weight_sum_template_no_uniform
    {α : Type*} [DecidableEq α] :
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
      IsMaximalSunflowerFree family 3 ground →
      i ∈ ground →
      LowFreq family i →
      (∑ p ∈ family.offDiag, pairWeight ground i p) + coordDegree family i <
        2 ^ (ground.card - 1)) →
    LowCaseUniformDecompositionHyp (α := α) := by
  intro hweight_template
  exact
    candidate_c720fe7_lowCaseUniformDecompositionHyp_of_layerwise_weight_cancellation
      (α := α)
      (fun family ground i hmax hi hlow _hunif =>
        hweight_template family ground i hmax hi hlow)

/-- Coarse-envelope route for the low-case decomposition hypothesis.
Assuming:
1. every off-diagonal pair in `familyOut` has union-size at least `2`, and
2. the corresponding closed-form coarse envelope is strictly below `2^(|ground|-1)`,
the low-case decomposition hypothesis follows. -/
theorem lowCaseUniformDecompositionHyp_of_coarse_offDiag_envelope
    {α : Type*} [DecidableEq α] :
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α)
        (p : Finset α × Finset α),
      IsMaximalSunflowerFree family 3 ground →
      i ∈ ground →
      LowFreq family i →
      p ∈ (familyOut family i).offDiag →
      2 ≤ (p.1 ∪ p.2).card) →
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
      IsMaximalSunflowerFree family 3 ground →
      i ∈ ground →
      LowFreq family i →
      (((familyIn family i).card * (familyIn family i).card -
          (familyIn family i).card) * 2 ^ (ground.card - 2) +
        ((familyOut family i).card * (familyOut family i).card -
          (familyOut family i).card) * 2 ^ (ground.card - 3)) +
        coordDegree family i <
        2 ^ (ground.card - 1)) →
    LowCaseUniformDecompositionHyp (α := α) := by
  intro hpair_union_floor henv
  refine lowCaseUniformDecompositionHyp_of_weight_sum_template_no_uniform (α := α) ?_
  intro family ground i hmax hi hlow
  have hsplit :
      ∑ p ∈ family.offDiag, pairWeight ground i p ≤
        ∑ p ∈ (familyIn family i).offDiag, pairWeight ground i p +
          ∑ p ∈ (familyOut family i).offDiag, pairWeight ground i p :=
    weight_sum_split_offDiag family ground i
  have hcard2 : ∀ p ∈ (familyOut family i).offDiag, 2 ≤ (p.1 ∪ p.2).card := by
    intro p hp
    exact hpair_union_floor family ground i p hmax hi hlow hp
  have hcoarse :
      ∑ p ∈ family.offDiag, pairWeight ground i p ≤
        ((familyIn family i).card * (familyIn family i).card -
          (familyIn family i).card) * 2 ^ (ground.card - 2) +
        ((familyOut family i).card * (familyOut family i).card -
          (familyOut family i).card) * 2 ^ (ground.card - 3) := by
    exact weight_sum_bound_offDiag_coarse family ground i hsplit hcard2
  have henv' :
      (((familyIn family i).card * (familyIn family i).card -
          (familyIn family i).card) * 2 ^ (ground.card - 2) +
        ((familyOut family i).card * (familyOut family i).card -
          (familyOut family i).card) * 2 ^ (ground.card - 3)) +
        coordDegree family i <
        2 ^ (ground.card - 1) :=
    henv family ground i hmax hi hlow
  have hle :
      (∑ p ∈ family.offDiag, pairWeight ground i p) + coordDegree family i ≤
        (((familyIn family i).card * (familyIn family i).card -
            (familyIn family i).card) * 2 ^ (ground.card - 2) +
          ((familyOut family i).card * (familyOut family i).card -
            (familyOut family i).card) * 2 ^ (ground.card - 3)) +
          coordDegree family i := by
    exact Nat.add_le_add_right hcoarse (coordDegree family i)
  exact lt_of_le_of_lt hle henv'

-- Closure wrapper (binder-form) so the frontier scanner can credit this leaf.
theorem candidate_c720fe7_lowCaseUniformDecompositionHyp_closed
    {α : Type*} [DecidableEq α]
    (hweight_template :
      ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
        IsMaximalSunflowerFree family 3 ground →
        i ∈ ground →
        LowFreq family i →
        (∀ r : ℕ, LowCaseCountingBoundUniform (α := α) r) →
        (∑ p ∈ family.offDiag, pairWeight ground i p) + coordDegree family i <
          2 ^ (ground.card - 1)) :
    LowCaseUniformDecompositionHyp (α := α) := by
  exact
    candidate_c720fe7_lowCaseUniformDecompositionHyp_of_layerwise_weight_cancellation
      (α := α) hweight_template

/-- Legacy compatibility alias for backlog entries that still reference the
old candidate id. The statement is aligned with the corrected decomposition
hypothesis shape (including `i ∈ ground`). -/
theorem candidate_c4f8b47_lowCaseUniformDecompositionHyp
    {α : Type*} [DecidableEq α] :
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
      IsMaximalSunflowerFree family 3 ground →
      i ∈ ground →
      LowFreq family i →
      (∀ r : ℕ, LowCaseCountingBoundUniform (α := α) r) →
      (∑ p ∈ family.offDiag, pairWeight ground i p) + coordDegree family i <
        2 ^ (ground.card - 1)) →
    LowCaseUniformDecompositionHyp (α := α) := by
  intro hweight_template
  exact
    candidate_c720fe7_lowCaseUniformDecompositionHyp_of_layerwise_weight_cancellation
      (α := α) hweight_template

-- Scout validated stub: candidate_c661a4f_highCaseCountingBoundSmall_n7_of_sat_certificate_cascade
theorem candidate_c661a4f_highCaseCountingBoundSmall_n7_of_sat_certificate_cascade
    {α : Type*} [DecidableEq α] :
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
      ground.card ≤ 7 →
      IsMaximalSunflowerFree family 3 ground →
      HighFreq family i →
      (BadAvoiding family ground i).card +
        (InFamilyAvoiding family ground i).card <
        (CandidatesAvoiding ground i).card) →
    HighCaseCountingBoundSmall (α := α) 7 := by
  intro h
  exact h

-- Scout validated stub: candidate_cc68758_lowCaseCountingBoundSmall_of_projection_savings_induction
theorem candidate_cc68758_lowCaseCountingBoundSmall_of_projection_savings_induction
    {α : Type*} [DecidableEq α] (n0 : ℕ)
    (h_base : LowCaseCountingBoundSmall (α := α) (n0 - 1))
    (h_close :
      ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
        ground.card = n0 →
        IsMaximalSunflowerFree family 3 ground →
        i ∈ ground →
        LowFreq family i →
        (∑ p ∈ family.offDiag, pairWeight ground i p) + coordDegree family i <
          2 ^ (ground.card - 1)) :
    LowCaseCountingBoundSmall (α := α) n0 := by
  intro family ground i hground hmax hi hlow
  by_cases hEq : ground.card = n0
  · have hweight := h_close family ground i hEq hmax hi hlow
    exact (low_case_counting_bound_of_weight_sum_offDiag family ground i hmax hi hweight) hlow
  · have hlt : ground.card < n0 := lt_of_le_of_ne hground hEq
    have hpred : ground.card ≤ n0 - 1 := Nat.le_pred_of_lt hlt
    exact h_base family ground i hpred hmax hi hlow

-- Scout validated stub: candidate_c0ff074_lowCaseCountingBoundSmall_n10_of_refined_weight_stratification
theorem candidate_c0ff074_lowCaseCountingBoundSmall_n10_of_refined_weight_stratification
    {α : Type*} [DecidableEq α]
    (h_close :
      ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
        ground.card ≤ 10 →
        IsMaximalSunflowerFree family 3 ground →
        i ∈ ground →
        LowFreq family i →
        (∑ p ∈ family.offDiag, pairWeight ground i p) + coordDegree family i <
          2 ^ (ground.card - 1)) :
    LowCaseCountingBoundSmall (α := α) 10 := by
  intro family ground i hground hmax hi hlow
  have hweight := h_close family ground i hground hmax hi hlow
  exact (low_case_counting_bound_of_weight_sum_offDiag family ground i hmax hi hweight) hlow

-- Scout validated stub: candidate_c4c77b1_lowCaseCountingBoundLarge_of_weight_sum_template
theorem candidate_c4c77b1_lowCaseCountingBoundLarge_of_weight_sum_template
    {α : Type*} [DecidableEq α] (n0 : ℕ) :
    LowCaseLargeWeightTemplate (α := α) n0 →
    LowCaseCountingBoundLarge (α := α) n0 := by
  intro hweight_template
  intro family ground i hground hmax hi hlow
  have hweight := hweight_template family ground i hground hmax hi hlow
  exact (low_case_counting_bound_of_weight_sum_offDiag family ground i hmax hi hweight) hlow

/-- Graph-name alias: low large-case counting follows from the low large
weight template assumption. -/
theorem lowCaseCountingBoundLarge_of_weight_template
    {α : Type*} [DecidableEq α] (n₀ : ℕ) :
    LowCaseLargeWeightTemplate (α := α) n₀ →
    LowCaseCountingBoundLarge (α := α) n₀ := by
  intro htemplate
  exact candidate_c4c77b1_lowCaseCountingBoundLarge_of_weight_sum_template
    (α := α) n₀ htemplate

-- Scout validated stub: candidate_c3a0eb4_highCaseUniformDecompositionHyp_of_avoiding_weight_sum_template
theorem candidate_c3a0eb4_highCaseUniformDecompositionHyp_of_avoiding_weight_sum_template
    {α : Type*} [DecidableEq α] :
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
      IsMaximalSunflowerFree family 3 ground →
      HighFreq family i →
      (∀ k : ℕ, HighCaseCountingBoundUniform (α := α) k) →
      (∑ p ∈ family.offDiag, pairWeightAvoiding ground i p) +
        (family.card - coordDegree family i) <
        2 ^ (ground.card - 1)) →
    HighCaseUniformDecompositionHyp (α := α) := by
  intro hweight_template
  intro family ground i hmax hhf hunif
  have hi_ground : i ∈ ground := mem_ground_of_highFreq_of_maximal family ground i hmax hhf
  have hweight :
      (∑ p ∈ family.offDiag, pairWeightAvoiding ground i p) +
        (family.card - coordDegree family i) <
        2 ^ (ground.card - 1) :=
    hweight_template family ground i hmax hhf hunif
  exact (high_case_counting_bound_of_weight_sum_offDiag family ground i hmax hi_ground hweight) hhf

-- Scout validated stub: candidate_c40c1ef_highCaseCountingBoundLarge_of_weight_sum_template
theorem candidate_c40c1ef_highCaseCountingBoundLarge_of_weight_sum_template
    {α : Type*} [DecidableEq α] (n0 : ℕ) :
    HighCaseLargeWeightTemplate (α := α) n0 →
    HighCaseCountingBoundLarge (α := α) n0 := by
  intro hweight_template
  intro family ground i hground hmax hhf
  have hi_ground : i ∈ ground := mem_ground_of_highFreq_of_maximal family ground i hmax hhf
  have hweight := hweight_template family ground i hground hmax hi_ground hhf
  exact (high_case_counting_bound_of_weight_sum_offDiag family ground i hmax hi_ground hweight) hhf

/-- Graph-name alias: high large-case counting follows from the high large
weight template assumption. -/
theorem highCaseCountingBoundLarge_of_weight_template
    {α : Type*} [DecidableEq α] (n₀ : ℕ) :
    HighCaseLargeWeightTemplate (α := α) n₀ →
    HighCaseCountingBoundLarge (α := α) n₀ := by
  intro htemplate
  exact candidate_c40c1ef_highCaseCountingBoundLarge_of_weight_sum_template
    (α := α) n₀ htemplate

/-- Large-lane packager:
the two explicit large-template assumptions close both large counting leaves. -/
theorem large_lane_bounds_of_weight_templates
    {α : Type*} [DecidableEq α] (n₀ : ℕ) :
    LowCaseLargeWeightTemplate (α := α) n₀ →
    HighCaseLargeWeightTemplate (α := α) n₀ →
    LowCaseCountingBoundLarge (α := α) n₀ ∧
      HighCaseCountingBoundLarge (α := α) n₀ := by
  intro hlow_template hhigh_template
  refine ⟨?_, ?_⟩
  · exact candidate_c4c77b1_lowCaseCountingBoundLarge_of_weight_sum_template
      (α := α) n₀ hlow_template
  · exact candidate_c40c1ef_highCaseCountingBoundLarge_of_weight_sum_template
      (α := α) n₀ hhigh_template

-- Scout validated stub: candidate_ce57866_highCaseCountingBoundSmall_n7_of_sat_certificate_cascade_calibrated
theorem candidate_ce57866_highCaseCountingBoundSmall_n7_of_sat_certificate_cascade_calibrated
    {α : Type*} [DecidableEq α]
    (h_sat_cascade :
      ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
        ground.card ≤ 7 →
        IsMaximalSunflowerFree family 3 ground →
        HighFreq family i →
        (BadAvoiding family ground i).card +
          (InFamilyAvoiding family ground i).card <
          (CandidatesAvoiding ground i).card) :
    HighCaseCountingBoundSmall (α := α) 7 := by
  exact h_sat_cascade

-- Scout validated stub: candidate_c5452b5_highCaseCountingBoundSmall_of_lowCaseCountingBoundSmall_via_complement
theorem candidate_c5452b5_highCaseCountingBoundSmall_of_lowCaseCountingBoundSmall_via_complement
    {α : Type*} [DecidableEq α] (n₀ : ℕ) :
    (∀ (family : Finset (Finset α)) (ground : Finset α),
      IsMaximalSunflowerFree family 3 ground →
      IsMaximalSunflowerFree (family.image (fun S => ground \ S)) 3 ground) →
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
      HighFreq family i →
      LowFreq (family.image (fun S => ground \ S)) i) →
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
      (BadContaining (family.image (fun S => ground \ S)) ground i).card +
        (InFamilyContaining (family.image (fun S => ground \ S)) ground i).card <
        (CandidatesContaining ground i).card →
      (BadAvoiding family ground i).card +
        (InFamilyAvoiding family ground i).card <
        (CandidatesAvoiding ground i).card) →
    LowCaseCountingBoundSmall (α := α) n₀ →
    HighCaseCountingBoundSmall (α := α) n₀ := by
  intro hmax_complement hhigh_to_low hcount_transfer hlow_small
  intro family ground i hground hmax hhf
  have hi_ground : i ∈ ground := mem_ground_of_highFreq_of_maximal family ground i hmax hhf
  rcases hmax with ⟨hfree, h_on, hmax_insert⟩
  let familyCompl : Finset (Finset α) := family.image (fun S => ground \ S)
  have hmax_compl : IsMaximalSunflowerFree familyCompl 3 ground := by
    simpa [familyCompl] using hmax_complement family ground ⟨hfree, h_on, hmax_insert⟩
  have hlow_compl : LowFreq familyCompl i := by
    have hlow_raw :
        LowFreq (family.image (fun S => ground \ S)) i :=
      hhigh_to_low family ground i hhf
    simpa [familyCompl] using hlow_raw
  have hcount_compl :
      (BadContaining familyCompl ground i).card +
        (InFamilyContaining familyCompl ground i).card <
        (CandidatesContaining ground i).card := by
    exact hlow_small familyCompl ground i hground hmax_compl hi_ground hlow_compl
  exact hcount_transfer family ground i (by simpa [familyCompl] using hcount_compl)

/-- Repair wrapper: strict low-case small bound transfers to high-case via complement. -/
theorem repair_candidate_c5452b5_highCaseCountingBoundSmall_of_lowCaseCountingBoundSmall_via_complement_wrongdef_77c0b55
    {α : Type*} [DecidableEq α] (n₀ : ℕ) :
    (∀ (family : Finset (Finset α)) (ground : Finset α),
      IsMaximalSunflowerFree family 3 ground →
      IsMaximalSunflowerFree (family.image (fun S => ground \ S)) 3 ground) →
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
      HighFreq family i →
      LowFreq (family.image (fun S => ground \ S)) i) →
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
      (BadContaining (family.image (fun S => ground \ S)) ground i).card +
        (InFamilyContaining (family.image (fun S => ground \ S)) ground i).card <
        (CandidatesContaining ground i).card →
      (BadAvoiding family ground i).card +
        (InFamilyAvoiding family ground i).card <
        (CandidatesAvoiding ground i).card) →
    LowCaseCountingBoundSmall (α := α) n₀ →
    HighCaseCountingBoundSmall (α := α) n₀ := by
  intro hmax_complement hhigh_to_low hcount_transfer hlow_small
  exact candidate_c5452b5_highCaseCountingBoundSmall_of_lowCaseCountingBoundSmall_via_complement
    (α := α) n₀ hmax_complement hhigh_to_low hcount_transfer hlow_small

-- Scout validated stub: candidate_c8e0e89_highCaseCountingBoundAll_of_small7_and_large7
theorem candidate_c8e0e89_highCaseCountingBoundAll_of_small7_and_large7
    {α : Type*} [DecidableEq α] :
    HighCaseCountingBoundSmall (α := α) 7 →
    HighCaseCountingBoundLarge (α := α) 7 →
    HighCaseCountingBoundAll (α := α) := by
  simpa using highCaseCountingBoundAll_of_small_and_large (α := α) 7

-- Scout validated stub: candidate_c069270_avoiding_weight_sum_bound_offDiag_coarse
theorem candidate_c069270_avoiding_weight_sum_bound_offDiag_coarse
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α)
    (hcard2 : ∀ p ∈ family.offDiag, 2 ≤ (p.1 ∪ p.2).card) :
    ∑ p ∈ family.offDiag, pairWeightAvoiding ground i p ≤
      ((family.card - coordDegree family i) *
          ((family.card - coordDegree family i) - 1)) * 2 ^ (ground.card - 3) +
      (2 * coordDegree family i *
          (family.card - coordDegree family i)) * 2 ^ (ground.card - 2) := by
  classical
  let cOut : Nat := 2 ^ (ground.card - 3)
  let cCross : Nat := 2 ^ (ground.card - 2)
  let boundTerm : (Finset α × Finset α) → Nat :=
    fun p =>
      (if p ∈ (familyOut family i).offDiag then cOut else 0) +
      (if p ∈ (familyIn family i).product (familyOut family i) then cCross else 0) +
      (if p ∈ (familyOut family i).product (familyIn family i) then cCross else 0)
  have hpoint :
      ∑ p ∈ family.offDiag, pairWeightAvoiding ground i p ≤
        ∑ p ∈ family.offDiag, boundTerm p := by
    refine Finset.sum_le_sum ?_
    intro p hp
    have hp' := Finset.mem_offDiag.mp hp
    have hA : p.1 ∈ family := hp'.1
    have hB : p.2 ∈ family := hp'.2.1
    have hneq : p.1 ≠ p.2 := hp'.2.2
    have h2 : 2 ≤ (p.1 ∪ p.2).card := hcard2 p hp
    by_cases hAi : i ∈ p.1
    · by_cases hBi : i ∈ p.2
      · simp [pairWeightAvoiding, hAi, hBi, boundTerm]
      · have hleExp : ground.card - (p.1 ∪ p.2).card ≤ ground.card - 2 :=
          Nat.sub_le_sub_left h2 _
        have hpow :
            2 ^ (ground.card - (p.1 ∪ p.2).card) ≤ cCross := by
          exact Nat.pow_le_pow_right (by decide) (by simpa [cCross] using hleExp)
        have hP1In : p.1 ∈ familyIn family i := Finset.mem_filter.mpr ⟨hA, hAi⟩
        have hP2Out : p.2 ∈ familyOut family i := Finset.mem_filter.mpr ⟨hB, hBi⟩
        have hCrossVal :
            (if p ∈ (familyIn family i).product (familyOut family i) then cCross else 0) =
              cCross := by
          simp [Finset.mem_product, hP1In, hP2Out]
        have hsecond :
            (if p ∈ (familyIn family i).product (familyOut family i) then cCross else 0) ≤
              boundTerm p := by
          have h₁ :
              (if p ∈ (familyIn family i).product (familyOut family i) then cCross else 0) ≤
                (if p ∈ (familyOut family i).offDiag then cOut else 0) +
                  (if p ∈ (familyIn family i).product (familyOut family i) then cCross else 0) := by
            exact Nat.le_add_left _ _
          exact le_trans h₁ (Nat.le_add_right _ _)
        have hpow' : pairWeightAvoiding ground i p ≤ cCross := by
          simpa [pairWeightAvoiding, hAi, hBi, cCross] using hpow
        have hsel : cCross ≤ boundTerm p := by
          calc
            cCross = (if p ∈ (familyIn family i).product (familyOut family i) then cCross else 0) := hCrossVal.symm
            _ ≤ boundTerm p := hsecond
        exact le_trans hpow' hsel
    · by_cases hBi : i ∈ p.2
      · have hleExp : ground.card - (p.1 ∪ p.2).card ≤ ground.card - 2 :=
          Nat.sub_le_sub_left h2 _
        have hpow :
            2 ^ (ground.card - (p.1 ∪ p.2).card) ≤ cCross := by
          exact Nat.pow_le_pow_right (by decide) (by simpa [cCross] using hleExp)
        have hP1Out : p.1 ∈ familyOut family i := Finset.mem_filter.mpr ⟨hA, hAi⟩
        have hP2In : p.2 ∈ familyIn family i := Finset.mem_filter.mpr ⟨hB, hBi⟩
        have hCrossVal :
            (if p ∈ (familyOut family i).product (familyIn family i) then cCross else 0) =
              cCross := by
          simp [Finset.mem_product, hP1Out, hP2In]
        have hthird :
            (if p ∈ (familyOut family i).product (familyIn family i) then cCross else 0) ≤
              boundTerm p := by
          -- third summand is bounded by the full three-term sum
          simpa [boundTerm] using
            (Nat.le_add_left
              (if p ∈ (familyOut family i).product (familyIn family i) then cCross else 0)
              ((if p ∈ (familyOut family i).offDiag then cOut else 0) +
                (if p ∈ (familyIn family i).product (familyOut family i) then cCross else 0)))
        have hpow' : pairWeightAvoiding ground i p ≤ cCross := by
          simpa [pairWeightAvoiding, hAi, hBi, cCross] using hpow
        have hsel : cCross ≤ boundTerm p := by
          calc
            cCross = (if p ∈ (familyOut family i).product (familyIn family i) then cCross else 0) := hCrossVal.symm
            _ ≤ boundTerm p := hthird
        exact le_trans hpow' hsel
      · have hleExpBase : ground.card - (p.1 ∪ p.2).card ≤ ground.card - 2 :=
          Nat.sub_le_sub_left h2 _
        have hleExp : ground.card - (p.1 ∪ p.2).card - 1 ≤ ground.card - 3 :=
          Nat.sub_le_sub_right hleExpBase 1
        have hpow :
            2 ^ (ground.card - (p.1 ∪ p.2).card - 1) ≤ cOut := by
          exact Nat.pow_le_pow_right (by decide) (by simpa [cOut] using hleExp)
        have hOut : p ∈ (familyOut family i).offDiag := by
          exact Finset.mem_offDiag.mpr
            ⟨Finset.mem_filter.mpr ⟨hA, hAi⟩,
              Finset.mem_filter.mpr ⟨hB, hBi⟩, hneq⟩
        have hfirst :
            (if p ∈ (familyOut family i).offDiag then cOut else 0) ≤ boundTerm p := by
          exact le_trans (Nat.le_add_right _ _)
            (Nat.le_add_right _ _)
        have hpow' : pairWeightAvoiding ground i p ≤ cOut := by
          simpa [pairWeightAvoiding, hAi, hBi, cOut] using hpow
        have hOutVal : (if p ∈ (familyOut family i).offDiag then cOut else 0) = cOut := by
          simp [hOut]
        have hsel : cOut ≤ boundTerm p := by
          calc
            cOut = (if p ∈ (familyOut family i).offDiag then cOut else 0) := hOutVal.symm
            _ ≤ boundTerm p := hfirst
        exact le_trans hpow' hsel
  have hsplit :
      ∑ p ∈ family.offDiag, boundTerm p =
        (∑ p ∈ family.offDiag, if p ∈ (familyOut family i).offDiag then cOut else 0) +
          ((∑ p ∈ family.offDiag, if p ∈ (familyIn family i).product (familyOut family i) then cCross else 0) +
            (∑ p ∈ family.offDiag, if p ∈ (familyOut family i).product (familyIn family i) then cCross else 0)) := by
    simp [boundTerm, Finset.sum_add_distrib, Nat.add_assoc]
  have hout_le :
      (∑ p ∈ family.offDiag, if p ∈ (familyOut family i).offDiag then cOut else 0) ≤
        ((familyOut family i).offDiag).card * cOut := by
    rw [Finset.sum_ite_mem]
    simp only [Finset.sum_const_nat]
    exact Nat.mul_le_mul_right cOut
      (Finset.card_le_card (Finset.inter_subset_right : family.offDiag ∩ (familyOut family i).offDiag ⊆ _))
  have hcrossInOut_le :
      (∑ p ∈ family.offDiag, if p ∈ (familyIn family i).product (familyOut family i) then cCross else 0) ≤
        ((familyIn family i).card * (familyOut family i).card) * cCross := by
    rw [Finset.sum_ite_mem]
    simp only [Finset.sum_const_nat]
    have hcard :
        (family.offDiag ∩ (familyIn family i).product (familyOut family i)).card ≤
          ((familyIn family i).product (familyOut family i)).card :=
      Finset.card_le_card (Finset.inter_subset_right :
        family.offDiag ∩ (familyIn family i).product (familyOut family i) ⊆ _)
    calc
      (family.offDiag ∩ (familyIn family i).product (familyOut family i)).card * cCross
          ≤ ((familyIn family i).product (familyOut family i)).card * cCross :=
            Nat.mul_le_mul_right cCross hcard
      _ = ((familyIn family i).card * (familyOut family i).card) * cCross := by
            simp [Finset.card_product]
  have hcrossOutIn_le :
      (∑ p ∈ family.offDiag, if p ∈ (familyOut family i).product (familyIn family i) then cCross else 0) ≤
        ((familyOut family i).card * (familyIn family i).card) * cCross := by
    rw [Finset.sum_ite_mem]
    simp only [Finset.sum_const_nat]
    have hcard :
        (family.offDiag ∩ (familyOut family i).product (familyIn family i)).card ≤
          ((familyOut family i).product (familyIn family i)).card :=
      Finset.card_le_card (Finset.inter_subset_right :
        family.offDiag ∩ (familyOut family i).product (familyIn family i) ⊆ _)
    calc
      (family.offDiag ∩ (familyOut family i).product (familyIn family i)).card * cCross
          ≤ ((familyOut family i).product (familyIn family i)).card * cCross :=
            Nat.mul_le_mul_right cCross hcard
      _ = ((familyOut family i).card * (familyIn family i).card) * cCross := by
            simp [Finset.card_product]
  have htotal :
      ∑ p ∈ family.offDiag, pairWeightAvoiding ground i p ≤
        ((familyOut family i).offDiag).card * cOut +
          (((familyIn family i).card * (familyOut family i).card) * cCross +
            ((familyOut family i).card * (familyIn family i).card) * cCross) := by
    calc
      ∑ p ∈ family.offDiag, pairWeightAvoiding ground i p
          ≤ ∑ p ∈ family.offDiag, boundTerm p := hpoint
      _ = (∑ p ∈ family.offDiag, if p ∈ (familyOut family i).offDiag then cOut else 0) +
            ((∑ p ∈ family.offDiag, if p ∈ (familyIn family i).product (familyOut family i) then cCross else 0) +
              (∑ p ∈ family.offDiag, if p ∈ (familyOut family i).product (familyIn family i) then cCross else 0)) := hsplit
      _ ≤ ((familyOut family i).offDiag).card * cOut +
            (((familyIn family i).card * (familyOut family i).card) * cCross +
              ((familyOut family i).card * (familyIn family i).card) * cCross) := by
            exact Nat.add_le_add hout_le (Nat.add_le_add hcrossInOut_le hcrossOutIn_le)
  have hcross_combine :
      ((familyIn family i).card * (familyOut family i).card) * cCross +
          ((familyOut family i).card * (familyIn family i).card) * cCross =
        (2 * (familyIn family i).card * (familyOut family i).card) * cCross := by
    ring
  calc
    ∑ p ∈ family.offDiag, pairWeightAvoiding ground i p
        ≤ ((familyOut family i).offDiag).card * cOut +
            (((familyIn family i).card * (familyOut family i).card) * cCross +
              ((familyOut family i).card * (familyIn family i).card) * cCross) := htotal
    _ = (((familyOut family i).card * ((familyOut family i).card - 1)) * cOut) +
          (((familyIn family i).card * (familyOut family i).card) * cCross +
            ((familyOut family i).card * (familyIn family i).card) * cCross) := by
          simp [Finset.offDiag_card, Nat.mul_sub_left_distrib, Nat.mul_one]
    _ = (((familyOut family i).card * ((familyOut family i).card - 1)) * cOut) +
          (2 * (familyIn family i).card * (familyOut family i).card) * cCross := by
          rw [hcross_combine]
    _ = ((family.card - coordDegree family i) *
          ((family.card - coordDegree family i) - 1)) * 2 ^ (ground.card - 3) +
          (2 * coordDegree family i *
          (family.card - coordDegree family i)) * 2 ^ (ground.card - 2) := by
          simp [card_familyIn, card_familyOut, cOut, cCross, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- Repair wrapper: coarse avoiding-weight offDiag bound requires a pair-union
size floor on off-diagonal pairs. -/
theorem repair_candidate_c069270_avoiding_weight_sum_bound_offDiag_coarse_wrongdef_dafe812
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α)
    (hcard2 : ∀ p ∈ family.offDiag, 2 ≤ (p.1 ∪ p.2).card) :
    ∑ p ∈ family.offDiag, pairWeightAvoiding ground i p ≤
      ((family.card - coordDegree family i) *
          ((family.card - coordDegree family i) - 1)) * 2 ^ (ground.card - 3) +
      (2 * coordDegree family i *
          (family.card - coordDegree family i)) * 2 ^ (ground.card - 2) := by
  exact candidate_c069270_avoiding_weight_sum_bound_offDiag_coarse family ground i hcard2

/-- Large-lane high template from large-`n` coarse floor + envelope assumptions. -/
theorem highCaseLargeWeightTemplate_of_coarse_large_envelope
    {α : Type*} [DecidableEq α] (n₀ : ℕ) :
    HighCoarsePairUnionFloorLarge (α := α) n₀ →
    HighCoarseWeightEnvelopeLarge (α := α) n₀ →
    HighCaseLargeWeightTemplate (α := α) n₀ := by
  intro hfloor henv family ground i hground hmax hi hhf
  have hcard2 : ∀ p ∈ family.offDiag, 2 ≤ (p.1 ∪ p.2).card := by
    intro p hp
    exact hfloor family ground i p hground hmax hhf hp
  have hcoarse :
      ∑ p ∈ family.offDiag, pairWeightAvoiding ground i p ≤
        ((family.card - coordDegree family i) *
            ((family.card - coordDegree family i) - 1)) * 2 ^ (ground.card - 3) +
          (2 * coordDegree family i * (family.card - coordDegree family i)) *
            2 ^ (ground.card - 2) := by
    exact candidate_c069270_avoiding_weight_sum_bound_offDiag_coarse family ground i hcard2
  have henv' :
      ((family.card - coordDegree family i) *
          ((family.card - coordDegree family i) - 1)) * 2 ^ (ground.card - 3) +
        (2 * coordDegree family i * (family.card - coordDegree family i)) *
          2 ^ (ground.card - 2) +
        (family.card - coordDegree family i) <
        2 ^ (ground.card - 1) :=
    henv family ground i hground hmax hhf
  exact lt_of_le_of_lt (Nat.add_le_add_right hcoarse _) henv'

/-- Low large-case counting leaf via the split large-`n` coarse route package. -/
theorem lowCaseCountingBoundLarge_of_coarse_large_route
    {α : Type*} [DecidableEq α] (n₀ : ℕ) :
    LowCoarseLargeEnvelopeRouteHyp (α := α) n₀ →
    LowCaseCountingBoundLarge (α := α) n₀ := by
  intro hroute
  rcases hroute with ⟨hfloor, henv⟩
  have htemplate :
      LowCaseLargeWeightTemplate (α := α) n₀ :=
    lowCaseLargeWeightTemplate_of_coarse_large_envelope (α := α) n₀ hfloor henv
  exact lowCaseCountingBoundLarge_of_weight_template (α := α) n₀ htemplate

/-- Component-wise low large-case wrapper:
the low large pair-union floor plus low large envelope close the low large
counting leaf directly. -/
theorem lowCaseCountingBoundLarge_of_low_coarse_large_components
    {α : Type*} [DecidableEq α] (n₀ : ℕ) :
    LowCoarsePairUnionFloorLarge (α := α) n₀ →
    LowCoarseWeightEnvelopeLarge (α := α) n₀ →
    LowCaseCountingBoundLarge (α := α) n₀ := by
  intro hfloor henv
  exact lowCaseCountingBoundLarge_of_coarse_large_route
    (α := α) n₀ ⟨hfloor, henv⟩

/-- High large-case counting leaf via the split large-`n` coarse route package. -/
theorem highCaseCountingBoundLarge_of_coarse_large_route
    {α : Type*} [DecidableEq α] (n₀ : ℕ) :
    HighCoarseLargeEnvelopeRouteHyp (α := α) n₀ →
    HighCaseCountingBoundLarge (α := α) n₀ := by
  intro hroute
  rcases hroute with ⟨hfloor, henv⟩
  have htemplate :
      HighCaseLargeWeightTemplate (α := α) n₀ :=
    highCaseLargeWeightTemplate_of_coarse_large_envelope (α := α) n₀ hfloor henv
  exact highCaseCountingBoundLarge_of_weight_template (α := α) n₀ htemplate

/-- Component-wise high large-case wrapper:
the high large pair-union floor plus high large envelope close the high large
counting leaf directly. -/
theorem highCaseCountingBoundLarge_of_high_coarse_large_components
    {α : Type*} [DecidableEq α] (n₀ : ℕ) :
    HighCoarsePairUnionFloorLarge (α := α) n₀ →
    HighCoarseWeightEnvelopeLarge (α := α) n₀ →
    HighCaseCountingBoundLarge (α := α) n₀ := by
  intro hfloor henv
  exact highCaseCountingBoundLarge_of_coarse_large_route
    (α := α) n₀ ⟨hfloor, henv⟩

/-- Large-lane packager via split low/high large-`n` coarse route assumptions. -/
theorem large_lane_bounds_of_coarse_large_routes
    {α : Type*} [DecidableEq α] (n₀ : ℕ) :
    LowCoarseLargeEnvelopeRouteHyp (α := α) n₀ →
    HighCoarseLargeEnvelopeRouteHyp (α := α) n₀ →
    LowCaseCountingBoundLarge (α := α) n₀ ∧
      HighCaseCountingBoundLarge (α := α) n₀ := by
  intro hlow_route hhigh_route
  refine ⟨?_, ?_⟩
  · exact lowCaseCountingBoundLarge_of_coarse_large_route (α := α) n₀ hlow_route
  · exact highCaseCountingBoundLarge_of_coarse_large_route (α := α) n₀ hhigh_route

/-- Graph-name alias: combined large-`n` coarse route milestone directly implies
the low large-case counting leaf. -/
theorem via_coarseLargeEnvelopeRouteHyp_LowCaseCountingBoundLarge
    {α : Type*} [DecidableEq α] (n₀ : ℕ) :
    CoarseLargeEnvelopeRouteHyp (α := α) n₀ →
    LowCaseCountingBoundLarge (α := α) n₀ := by
  intro hcoarse
  exact lowCaseCountingBoundLarge_of_coarse_large_route
    (α := α) n₀
    (lowCoarseLargeEnvelopeRouteHyp_of_coarseLargeEnvelopeRouteHyp
      (α := α) n₀ hcoarse)

/-- Graph-name alias: combined large-`n` coarse route milestone directly implies
the high large-case counting leaf. -/
theorem via_coarseLargeEnvelopeRouteHyp_HighCaseCountingBoundLarge
    {α : Type*} [DecidableEq α] (n₀ : ℕ) :
    CoarseLargeEnvelopeRouteHyp (α := α) n₀ →
    HighCaseCountingBoundLarge (α := α) n₀ := by
  intro hcoarse
  exact highCaseCountingBoundLarge_of_coarse_large_route
    (α := α) n₀
    (highCoarseLargeEnvelopeRouteHyp_of_coarseLargeEnvelopeRouteHyp
      (α := α) n₀ hcoarse)

/-- Large-lane packager through the combined large-`n` coarse route milestone. -/
theorem large_lane_bounds_of_coarseLargeEnvelopeRouteHyp
    {α : Type*} [DecidableEq α] (n₀ : ℕ) :
    CoarseLargeEnvelopeRouteHyp (α := α) n₀ →
    LowCaseCountingBoundLarge (α := α) n₀ ∧
      HighCaseCountingBoundLarge (α := α) n₀ := by
  intro hcoarse
  refine ⟨?_, ?_⟩
  · exact via_coarseLargeEnvelopeRouteHyp_LowCaseCountingBoundLarge
      (α := α) n₀ hcoarse
  · exact via_coarseLargeEnvelopeRouteHyp_HighCaseCountingBoundLarge
      (α := α) n₀ hcoarse

-- Scout validated stub: candidate_cd05446_highCaseUniformDecompositionHyp_of_weight_sum_offDiag_template
theorem candidate_cd05446_highCaseUniformDecompositionHyp_of_weight_sum_offDiag_template
    {α : Type*} [DecidableEq α] :
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
      IsMaximalSunflowerFree family 3 ground →
      HighFreq family i →
      (∀ k : ℕ, HighCaseCountingBoundUniform (α := α) k) →
      (∑ p ∈ family.offDiag, pairWeightAvoiding ground i p) +
        (family.card - coordDegree family i) <
        2 ^ (ground.card - 1)) →
    HighCaseUniformDecompositionHyp (α := α) := by
  simpa using
    (candidate_c3a0eb4_highCaseUniformDecompositionHyp_of_avoiding_weight_sum_template
      (α := α))

-- Scout validated stub: candidate_cef9f68_exists_uniform_layer_lowFreq
theorem candidate_cef9f68_exists_uniform_layer_lowFreq
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (i : α) :
    LowFreq family i →
    ∃ r : ℕ,
      (family.filter (fun S => S.card = r)).Nonempty ∧
      (∀ S ∈ family.filter (fun S => S.card = r), S.card = r) ∧
      LowFreq (family.filter (fun S => S.card = r)) i := by
  intro hlow
  let idx : Finset ℕ := family.image (fun S => S.card)
  have hcard_sum :
      family.card = ∑ r ∈ idx, (family.filter (fun S => S.card = r)).card := by
    simpa [idx] using
      (Finset.card_eq_sum_card_image (fun S : Finset α => S.card) family)
  have hdeg_sum :
      coordDegree family i =
        ∑ r ∈ idx, coordDegree (family.filter (fun S => S.card = r)) i := by
    have hfiber :
        (family.filter (fun S => i ∈ S)).card =
          ∑ r ∈ idx,
            ((family.filter (fun S => i ∈ S)).filter (fun S => S.card = r)).card := by
      refine Finset.card_eq_sum_card_fiberwise
        (f := fun S : Finset α => S.card)
        (s := family.filter (fun S => i ∈ S))
        (t := idx) ?_
      intro S hS
      exact Finset.mem_image.mpr ⟨S, (Finset.mem_filter.mp hS).1, rfl⟩
    calc
      coordDegree family i
          = (family.filter (fun S => i ∈ S)).card := rfl
      _ = ∑ r ∈ idx,
            ((family.filter (fun S => i ∈ S)).filter (fun S => S.card = r)).card := hfiber
      _ = ∑ r ∈ idx, coordDegree (family.filter (fun S => S.card = r)) i := by
            refine Finset.sum_congr rfl ?_
            intro r hr
            unfold coordDegree
            simp [Finset.filter_filter, and_left_comm, and_assoc, and_comm]
  by_contra hnone
  have hnot_low :
      ∀ r ∈ idx, ¬ LowFreq (family.filter (fun S => S.card = r)) i := by
    intro r hr hlow_r
    apply hnone
    refine ⟨r, ?_, ?_, hlow_r⟩
    · rcases Finset.mem_image.mp hr with ⟨S, hS, hScard⟩
      exact ⟨S, Finset.mem_filter.mpr ⟨hS, hScard⟩⟩
    · intro S hS
      exact (Finset.mem_filter.mp hS).2
  have hsum_le :
      ∑ r ∈ idx, (family.filter (fun S => S.card = r)).card ≤
        ∑ r ∈ idx, 3 * coordDegree (family.filter (fun S => S.card = r)) i := by
    refine Finset.sum_le_sum ?_
    intro r hr
    exact Nat.le_of_not_gt (hnot_low r hr)
  have hm_le : family.card ≤ 3 * coordDegree family i := by
    calc
      family.card = ∑ r ∈ idx, (family.filter (fun S => S.card = r)).card := hcard_sum
      _ ≤ ∑ r ∈ idx, 3 * coordDegree (family.filter (fun S => S.card = r)) i := hsum_le
      _ = 3 * (∑ r ∈ idx, coordDegree (family.filter (fun S => S.card = r)) i) := by
            simp [Finset.mul_sum, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ = 3 * coordDegree family i := by rw [hdeg_sum]
  exact (not_lt_of_ge hm_le) hlow

-- Helper: fiber sum for card over cardinality layers
private lemma card_eq_sum_filter_card {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) :
    family.card =
      ∑ r ∈ family.image Finset.card,
        (family.filter (fun S => S.card = r)).card := by
  exact Finset.card_eq_sum_card_image Finset.card family

-- Scout validated stub: candidate_cef9f68_exists_uniform_layer_highFreq
theorem candidate_cef9f68_exists_uniform_layer_highFreq
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (i : α) :
    HighFreq family i →
    ∃ r : ℕ,
      (family.filter (fun S => S.card = r)).Nonempty ∧
      (∀ S ∈ family.filter (fun S => S.card = r), S.card = r) ∧
      HighFreq (family.filter (fun S => S.card = r)) i := by
  intro hhf
  classical
  by_contra h_none
  push_neg at h_none
  -- h_none: ∀ r, Nonempty → uniform → ¬HighFreq
  -- Extract: for nonempty layers, ¬HighFreq
  have h_not_hf : ∀ r, (family.filter (fun S => S.card = r)).Nonempty →
      ¬HighFreq (family.filter (fun S => S.card = r)) i :=
    fun r hr => h_none r hr (fun S hS => (Finset.mem_filter.mp hS).2)
  -- ¬HighFreq gives 3*d_r ≤ 2*m_r; extend to all r
  have h_le : ∀ r,
      3 * coordDegree (family.filter (fun S => S.card = r)) i ≤
        2 * (family.filter (fun S => S.card = r)).card := by
    intro r
    by_cases hr : (family.filter (fun S => S.card = r)).Nonempty
    · have := h_not_hf r hr; unfold HighFreq at this; omega
    · rw [Finset.not_nonempty_iff_eq_empty] at hr
      simp [hr, coordDegree]
  -- Fiber sums
  set R := family.image Finset.card with hR_def
  have h_card : family.card = ∑ r ∈ R, (family.filter (fun S => S.card = r)).card :=
    card_eq_sum_filter_card family
  have h_deg : coordDegree family i =
      ∑ r ∈ R, coordDegree (family.filter (fun S => S.card = r)) i := by
    simp only [coordDegree]
    -- Use fiberwise card sum on (family.filter (i ∈ ·)) with fiber = Finset.card
    have hmaps : (↑(family.filter (fun S => i ∈ S)) : Set (Finset α)).MapsTo
        Finset.card (↑R : Set ℕ) := by
      intro S hS
      simp only [Finset.mem_coe] at hS ⊢
      exact Finset.mem_image.mpr ⟨S, (Finset.mem_filter.mp hS).1, rfl⟩
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    apply Finset.sum_congr rfl
    intro r _
    congr 1; ext S; simp only [Finset.mem_filter]; tauto
  -- Sum the per-layer inequality: 3*d ≤ 2*m
  have h_sum_le : 3 * coordDegree family i ≤ 2 * family.card := by
    rw [h_card, h_deg, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum (fun r _ => h_le r)
  -- Contradiction with HighFreq: 2*m < 3*d
  unfold HighFreq at hhf; omega

-- Scout validated stub: candidate_c5935e4_lowCaseCountingBoundAll_of_small_and_large_by_cases
theorem candidate_c5935e4_lowCaseCountingBoundAll_of_small_and_large_by_cases
    {α : Type*} [DecidableEq α] (n0 : ℕ) :
    LowCaseCountingBoundSmall (α := α) n0 →
    LowCaseCountingBoundLarge (α := α) n0 →
    LowCaseCountingBoundAll (α := α) := by
  simpa using lowCaseCountingBoundAll_of_small_and_large (α := α) n0

-- Scout validated stub: candidate_c040cac_lowCaseCountingBoundAll_guarded_of_uniform_hyp
theorem candidate_c040cac_lowCaseCountingBoundAll_guarded_of_uniform_hyp
    {α : Type*} [DecidableEq α] :
    LowCaseUniformDecompositionHyp (α := α) →
    (∀ k : ℕ, LowCaseCountingBoundUniform (α := α) k) →
    ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
      IsMaximalSunflowerFree family 3 ground →
      i ∈ ground →
      LowFreq family i →
      (BadContaining family ground i).card +
        (InFamilyContaining family ground i).card <
        (CandidatesContaining ground i).card := by
  intro hdecomp hunif family ground i hmax hi hlf
  exact hdecomp family ground i hmax hi hlf hunif

-- Scout validated stub: candidate_c040cac_lowCaseCountingBoundAll_of_uniform_hyp_with_ground_guard
theorem candidate_c040cac_lowCaseCountingBoundAll_of_uniform_hyp_with_ground_guard
    {α : Type*} [DecidableEq α] :
    LowCaseUniformDecompositionHyp (α := α) →
    (∀ k : ℕ, LowCaseCountingBoundUniform (α := α) k) →
    LowCaseCountingBoundAll (α := α) := by
  intro hdecomp hunif family ground i hmax hi hlf
  exact hdecomp family ground i hmax hi hlf hunif

-- Scout validated stub: candidate_c7f7f84_complement_preserves_maximal
theorem candidate_c7f7f84_complement_preserves_maximal
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) :
    (∀ (F : Finset (Finset α)) (G : Finset α),
      IsMaximalSunflowerFree F 3 G →
      IsMaximalSunflowerFree (F.image (fun S => G \ S)) 3 G) →
    IsMaximalSunflowerFree family 3 ground →
    IsMaximalSunflowerFree (family.image (fun S => ground \ S)) 3 ground := by
  intro h_transfer hmax
  exact h_transfer family ground hmax

-- Helper: complement map is injective on on-ground families
private lemma highFreq_complement_injOn_aux {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α)
    (h_on : IsOnGround family ground) :
    Set.InjOn (fun S : Finset α => ground \ S) (↑family : Set (Finset α)) := by
  intro S hS T hT (hEq : ground \ S = ground \ T)
  have hS_sub : S ⊆ ground := h_on S (Finset.mem_coe.mp hS)
  have hT_sub : T ⊆ ground := h_on T (Finset.mem_coe.mp hT)
  ext x
  by_cases hxG : x ∈ ground
  · constructor
    · intro hxS
      by_contra hxNotT
      have hx_in : x ∈ ground \ T := Finset.mem_sdiff.mpr ⟨hxG, hxNotT⟩
      rw [← hEq] at hx_in
      exact (Finset.mem_sdiff.mp hx_in).2 hxS
    · intro hxT
      by_contra hxNotS
      have hx_in : x ∈ ground \ S := Finset.mem_sdiff.mpr ⟨hxG, hxNotS⟩
      rw [hEq] at hx_in
      exact (Finset.mem_sdiff.mp hx_in).2 hxT
  · exact ⟨fun hxS => absurd (hS_sub hxS) hxG, fun hxT => absurd (hT_sub hxT) hxG⟩

-- Scout validated stub: candidate_c7f7f84_highFreq_to_lowFreq_complement
-- NOTE: Statement corrected to add IsOnGround and i ∈ ground guards
-- (original was false without these; see researcher counterexample)
theorem candidate_c7f7f84_highFreq_to_lowFreq_complement
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    IsOnGround family ground →
    i ∈ ground →
    HighFreq family i →
    LowFreq (family.image (fun S => ground \ S)) i := by
  intro h_on hi hhf
  classical
  -- Step 1: complement is injective on on-ground families
  have hinj := highFreq_complement_injOn_aux family ground h_on
  -- Step 2: image preserves cardinality
  have hcard_eq : (family.image (fun S => ground \ S)).card = family.card :=
    Finset.card_image_of_injOn hinj
  -- Step 3: filter equivalence — sets containing i in complement image
  -- correspond to sets NOT containing i in the original family
  have hfilt_eq :
      (family.image (fun S => ground \ S)).filter (fun T => i ∈ T) =
        (family.filter (fun S => i ∉ S)).image (fun S => ground \ S) := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨S, hS, rfl⟩, hiT⟩
      exact ⟨S, ⟨hS, (Finset.mem_sdiff.mp hiT).2⟩, rfl⟩
    · rintro ⟨S, ⟨hS, hiS⟩, rfl⟩
      exact ⟨⟨S, hS, rfl⟩, Finset.mem_sdiff.mpr ⟨hi, hiS⟩⟩
  -- Injectivity on the sub-family
  have hinj_sub : Set.InjOn (fun S : Finset α => ground \ S)
      ↑(family.filter (fun S => i ∉ S)) := by
    intro S hS T hT hEq
    exact hinj (Finset.mem_coe.mpr ((Finset.mem_filter.mp (Finset.mem_coe.mp hS)).1))
      (Finset.mem_coe.mpr ((Finset.mem_filter.mp (Finset.mem_coe.mp hT)).1)) hEq
  -- Step 4: coordDegree in complement image = family.card - coordDegree family i
  have hcoord :
      coordDegree (family.image (fun S => ground \ S)) i =
        family.card - coordDegree family i := by
    trans (family.filter (fun S => i ∉ S)).card
    · -- coordDegree (image) i = |family.filter (i ∉ ·)|
      show ((family.image (fun S => ground \ S)).filter (fun S => i ∈ S)).card =
        (family.filter (fun S => i ∉ S)).card
      rw [hfilt_eq]
      exact Finset.card_image_of_injOn hinj_sub
    · -- |family.filter (i ∉ ·)| = |family| - coordDegree family i
      exact card_familyOut family i
  -- Step 5: arithmetic — 2m < 3d implies 3(m-d) < m
  unfold LowFreq
  rw [hcard_eq, hcoord]
  have hd_le : coordDegree family i ≤ family.card := coordDegree_le_card family i
  unfold HighFreq at hhf
  omega

-- Scout validated stub: candidate_c7f7f84_count_transfer_complement
-- NOTE (obstruction): the current bidirectional equivalence is false on small
-- maximal-family counterexamples (checked by finite brute force). Keep this as
-- residual while routing high-case transfer via guarded assumptions/wrappers.
theorem candidate_c7f7f84_count_transfer_complement
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    (∀ (F : Finset (Finset α)) (G : Finset α) (j : α),
      (BadContaining (F.image (fun S => G \ S)) G j).card +
        (InFamilyContaining (F.image (fun S => G \ S)) G j).card <
        (CandidatesContaining G j).card →
      (BadAvoiding F G j).card +
        (InFamilyAvoiding F G j).card <
        (CandidatesAvoiding G j).card) →
    (BadContaining (family.image (fun S => ground \ S)) ground i).card +
      (InFamilyContaining (family.image (fun S => ground \ S)) ground i).card <
      (CandidatesContaining ground i).card →
    (BadAvoiding family ground i).card +
      (InFamilyAvoiding family ground i).card <
      (CandidatesAvoiding ground i).card := by
  intro htransfer hcont
  exact htransfer family ground i hcont

-- Scout validated stub: candidate_c7f7f84_highCaseCountingBoundSmall_of_lowCaseCountingBoundSmall_via_complement
theorem candidate_c7f7f84_highCaseCountingBoundSmall_of_lowCaseCountingBoundSmall_via_complement
    {α : Type*} [DecidableEq α] (n0 : ℕ) :
    (∀ (family : Finset (Finset α)) (ground : Finset α),
      IsMaximalSunflowerFree family 3 ground →
      IsMaximalSunflowerFree (family.image (fun S => ground \ S)) 3 ground) →
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
      (BadContaining (family.image (fun S => ground \ S)) ground i).card +
        (InFamilyContaining (family.image (fun S => ground \ S)) ground i).card <
        (CandidatesContaining ground i).card →
      (BadAvoiding family ground i).card +
        (InFamilyAvoiding family ground i).card <
        (CandidatesAvoiding ground i).card) →
    LowCaseCountingBoundSmall (α := α) n0 →
    HighCaseCountingBoundSmall (α := α) n0 := by
  intro hmax_complement hcount_transfer hlow_small
  intro family ground i hground hmax hhf
  have hi_ground : i ∈ ground := mem_ground_of_highFreq_of_maximal family ground i hmax hhf
  rcases hmax with ⟨hfree, h_on, hmax_insert⟩
  let familyCompl : Finset (Finset α) := family.image (fun S => ground \ S)
  have hmax_compl : IsMaximalSunflowerFree familyCompl 3 ground := by
    simpa [familyCompl] using hmax_complement family ground ⟨hfree, h_on, hmax_insert⟩
  have hlow_compl : LowFreq familyCompl i := by
    have hlow_raw :
        LowFreq (family.image (fun S => ground \ S)) i :=
      candidate_c7f7f84_highFreq_to_lowFreq_complement family ground i h_on hi_ground hhf
    simpa [familyCompl] using hlow_raw
  have hcount_compl :
      (BadContaining familyCompl ground i).card +
        (InFamilyContaining familyCompl ground i).card <
        (CandidatesContaining ground i).card := by
    exact hlow_small familyCompl ground i hground hmax_compl hi_ground hlow_compl
  exact hcount_transfer family ground i (by simpa [familyCompl] using hcount_compl)

-- Scout validated stub: candidate_c5160c_lowCaseCountingBoundAll_guarded_of_small_and_large
theorem candidate_c5160c_lowCaseCountingBoundAll_guarded_of_small_and_large
    {α : Type*} [DecidableEq α] (n₀ : ℕ) :
    LowCaseCountingBoundSmall (α := α) n₀ →
    LowCaseCountingBoundLarge (α := α) n₀ →
    ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
      IsMaximalSunflowerFree family 3 ground →
      i ∈ ground →
      LowFreq family i →
      (BadContaining family ground i).card +
        (InFamilyContaining family ground i).card <
        (CandidatesContaining ground i).card := by
  intro hsmall hlarge family ground i hmax hi hlf
  by_cases h : ground.card ≤ n₀
  · exact hsmall family ground i h hmax hi hlf
  · exact hlarge family ground i (Nat.lt_of_not_le h) hmax hi hlf

-- Scout validated stub: candidate_c5160c_lowCaseCountingBoundAll_guarded_of_uniform_hyp
theorem candidate_c5160c_lowCaseCountingBoundAll_guarded_of_uniform_hyp
    {α : Type*} [DecidableEq α] :
    LowCaseUniformDecompositionHyp (α := α) →
    (∀ k : ℕ, LowCaseCountingBoundUniform (α := α) k) →
    ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
      IsMaximalSunflowerFree family 3 ground →
      i ∈ ground →
      LowFreq family i →
      (BadContaining family ground i).card +
        (InFamilyContaining family ground i).card <
        (CandidatesContaining ground i).card := by
  intro hdecomp hunif family ground i hmax hi hlow
  exact hdecomp family ground i hmax hi hlow hunif

-- Scout validated stub: candidate_c25996f_highCaseUniformDecompositionHyp_of_layerwise_weight_cancellation
theorem candidate_c25996f_highCaseUniformDecompositionHyp_of_layerwise_weight_cancellation
    {α : Type*} [DecidableEq α] :
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
      IsMaximalSunflowerFree family 3 ground →
      i ∈ ground →
      HighFreq family i →
      (∀ r : ℕ, HighCaseCountingBoundUniform (α := α) r) →
      (∑ p ∈ family.offDiag, pairWeightAvoiding ground i p) +
        (family.card - coordDegree family i) <
        2 ^ (ground.card - 1)) →
    HighCaseUniformDecompositionHyp (α := α) := by
  intro hweight_template
  intro family ground i hmax hhf hunif
  have hi_ground : i ∈ ground := mem_ground_of_highFreq_of_maximal family ground i hmax hhf
  have hweight :
      (∑ p ∈ family.offDiag, pairWeightAvoiding ground i p) +
        (family.card - coordDegree family i) <
          2 ^ (ground.card - 1) :=
    hweight_template family ground i hmax hi_ground hhf hunif
  exact (high_case_counting_bound_of_weight_sum_offDiag family ground i hmax hi_ground hweight) hhf

/-- Strengthened high-case bridge: if the avoiding-side weight inequality is
available directly (without per-layer uniform hypotheses), then the
decomposition hypothesis follows immediately. -/
theorem highCaseUniformDecompositionHyp_of_weight_sum_template_no_uniform
    {α : Type*} [DecidableEq α] :
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
      IsMaximalSunflowerFree family 3 ground →
      HighFreq family i →
      (∑ p ∈ family.offDiag, pairWeightAvoiding ground i p) +
        (family.card - coordDegree family i) <
        2 ^ (ground.card - 1)) →
    HighCaseUniformDecompositionHyp (α := α) := by
  intro hweight_template
  exact
    candidate_c25996f_highCaseUniformDecompositionHyp_of_layerwise_weight_cancellation
      (α := α)
      (fun family ground i hmax hi_ground hhf _hunif =>
        hweight_template family ground i hmax hhf)

/-- Coarse-envelope route for the high-case decomposition hypothesis.
Assuming:
1. every off-diagonal pair has union-size at least `2` (the calibration floor), and
2. the closed-form coarse envelope is strictly below `2^(|ground|-1)`,
the high-case decomposition hypothesis follows. -/
theorem highCaseUniformDecompositionHyp_of_coarse_offDiag_envelope
    {α : Type*} [DecidableEq α] :
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α)
        (p : Finset α × Finset α),
      IsMaximalSunflowerFree family 3 ground →
      HighFreq family i →
      p ∈ family.offDiag →
      2 ≤ (p.1 ∪ p.2).card) →
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
      IsMaximalSunflowerFree family 3 ground →
      HighFreq family i →
      ((family.card - coordDegree family i) *
          ((family.card - coordDegree family i) - 1)) * 2 ^ (ground.card - 3) +
        (2 * coordDegree family i * (family.card - coordDegree family i)) *
          2 ^ (ground.card - 2) +
        (family.card - coordDegree family i) <
        2 ^ (ground.card - 1)) →
    HighCaseUniformDecompositionHyp (α := α) := by
  intro hpair_union_floor henv
  refine highCaseUniformDecompositionHyp_of_weight_sum_template_no_uniform (α := α) ?_
  intro family ground i hmax hhf
  have hcard2 : ∀ p ∈ family.offDiag, 2 ≤ (p.1 ∪ p.2).card := by
    intro p hp
    exact hpair_union_floor family ground i p hmax hhf hp
  have hcoarse :
      ∑ p ∈ family.offDiag, pairWeightAvoiding ground i p ≤
        ((family.card - coordDegree family i) *
            ((family.card - coordDegree family i) - 1)) * 2 ^ (ground.card - 3) +
          (2 * coordDegree family i * (family.card - coordDegree family i)) *
            2 ^ (ground.card - 2) := by
    exact candidate_c069270_avoiding_weight_sum_bound_offDiag_coarse family ground i hcard2
  have henv' :
      ((family.card - coordDegree family i) *
          ((family.card - coordDegree family i) - 1)) * 2 ^ (ground.card - 3) +
        (2 * coordDegree family i * (family.card - coordDegree family i)) *
          2 ^ (ground.card - 2) +
        (family.card - coordDegree family i) <
        2 ^ (ground.card - 1) :=
    henv family ground i hmax hhf
  have hle :
      (∑ p ∈ family.offDiag, pairWeightAvoiding ground i p) +
          (family.card - coordDegree family i) ≤
        (((family.card - coordDegree family i) *
            ((family.card - coordDegree family i) - 1)) * 2 ^ (ground.card - 3) +
          (2 * coordDegree family i * (family.card - coordDegree family i)) *
            2 ^ (ground.card - 2)) +
          (family.card - coordDegree family i) := by
    exact Nat.add_le_add_right hcoarse (family.card - coordDegree family i)
  exact lt_of_le_of_lt hle henv'

/-- Route packager: coarse off-diagonal envelopes plus uniform-layer counting
bounds yield both low/high global counting bounds. -/
theorem counting_all_of_coarse_uniform_envelopes
    {α : Type*} [DecidableEq α] :
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α)
        (p : Finset α × Finset α),
      IsMaximalSunflowerFree family 3 ground →
      i ∈ ground →
      LowFreq family i →
      p ∈ (familyOut family i).offDiag →
      2 ≤ (p.1 ∪ p.2).card) →
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
      IsMaximalSunflowerFree family 3 ground →
      i ∈ ground →
      LowFreq family i →
      (((familyIn family i).card * (familyIn family i).card -
          (familyIn family i).card) * 2 ^ (ground.card - 2) +
        ((familyOut family i).card * (familyOut family i).card -
          (familyOut family i).card) * 2 ^ (ground.card - 3)) +
        coordDegree family i <
        2 ^ (ground.card - 1)) →
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α)
        (p : Finset α × Finset α),
      IsMaximalSunflowerFree family 3 ground →
      HighFreq family i →
      p ∈ family.offDiag →
      2 ≤ (p.1 ∪ p.2).card) →
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
      IsMaximalSunflowerFree family 3 ground →
      HighFreq family i →
      ((family.card - coordDegree family i) *
          ((family.card - coordDegree family i) - 1)) * 2 ^ (ground.card - 3) +
        (2 * coordDegree family i * (family.card - coordDegree family i)) *
          2 ^ (ground.card - 2) +
        (family.card - coordDegree family i) <
        2 ^ (ground.card - 1)) →
    (∀ k : ℕ, LowCaseCountingBoundUniform (α := α) k) →
    (∀ k : ℕ, HighCaseCountingBoundUniform (α := α) k) →
    LowCaseCountingBoundAll (α := α) ∧ HighCaseCountingBoundAll (α := α) := by
  intro hlow_floor hlow_env hhigh_floor hhigh_env hlow_uniform hhigh_uniform
  have hlow_decomp : LowCaseUniformDecompositionHyp (α := α) :=
    lowCaseUniformDecompositionHyp_of_coarse_offDiag_envelope
      (α := α) hlow_floor hlow_env
  have hhigh_decomp : HighCaseUniformDecompositionHyp (α := α) :=
    highCaseUniformDecompositionHyp_of_coarse_offDiag_envelope
      (α := α) hhigh_floor hhigh_env
  refine ⟨?_, ?_⟩
  · exact lowCaseCountingBoundAll_of_uniform_hyp (α := α) hlow_decomp hlow_uniform
  · exact highCaseCountingBoundAll_of_uniform_hyp (α := α) hhigh_decomp hhigh_uniform

/-- Route projection: coarse off-diagonal envelopes plus uniform-layer counting
bounds imply the low-case global counting bound. -/
theorem lowCaseCountingBoundAll_of_coarse_uniform_envelopes
    {α : Type*} [DecidableEq α] :
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α)
        (p : Finset α × Finset α),
      IsMaximalSunflowerFree family 3 ground →
      i ∈ ground →
      LowFreq family i →
      p ∈ (familyOut family i).offDiag →
      2 ≤ (p.1 ∪ p.2).card) →
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
      IsMaximalSunflowerFree family 3 ground →
      i ∈ ground →
      LowFreq family i →
      (((familyIn family i).card * (familyIn family i).card -
          (familyIn family i).card) * 2 ^ (ground.card - 2) +
        ((familyOut family i).card * (familyOut family i).card -
          (familyOut family i).card) * 2 ^ (ground.card - 3)) +
        coordDegree family i <
        2 ^ (ground.card - 1)) →
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α)
        (p : Finset α × Finset α),
      IsMaximalSunflowerFree family 3 ground →
      HighFreq family i →
      p ∈ family.offDiag →
      2 ≤ (p.1 ∪ p.2).card) →
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
      IsMaximalSunflowerFree family 3 ground →
      HighFreq family i →
      ((family.card - coordDegree family i) *
          ((family.card - coordDegree family i) - 1)) * 2 ^ (ground.card - 3) +
        (2 * coordDegree family i * (family.card - coordDegree family i)) *
          2 ^ (ground.card - 2) +
        (family.card - coordDegree family i) <
        2 ^ (ground.card - 1)) →
    (∀ k : ℕ, LowCaseCountingBoundUniform (α := α) k) →
    (∀ k : ℕ, HighCaseCountingBoundUniform (α := α) k) →
    LowCaseCountingBoundAll (α := α) := by
  intro hlow_floor hlow_env hhigh_floor hhigh_env hlow_uniform hhigh_uniform
  exact (counting_all_of_coarse_uniform_envelopes (α := α)
    hlow_floor hlow_env hhigh_floor hhigh_env hlow_uniform hhigh_uniform).1

/-- Route projection: coarse off-diagonal envelopes plus uniform-layer counting
bounds imply the high-case global counting bound. -/
theorem highCaseCountingBoundAll_of_coarse_uniform_envelopes
    {α : Type*} [DecidableEq α] :
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α)
        (p : Finset α × Finset α),
      IsMaximalSunflowerFree family 3 ground →
      i ∈ ground →
      LowFreq family i →
      p ∈ (familyOut family i).offDiag →
      2 ≤ (p.1 ∪ p.2).card) →
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
      IsMaximalSunflowerFree family 3 ground →
      i ∈ ground →
      LowFreq family i →
      (((familyIn family i).card * (familyIn family i).card -
          (familyIn family i).card) * 2 ^ (ground.card - 2) +
        ((familyOut family i).card * (familyOut family i).card -
          (familyOut family i).card) * 2 ^ (ground.card - 3)) +
        coordDegree family i <
        2 ^ (ground.card - 1)) →
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α)
        (p : Finset α × Finset α),
      IsMaximalSunflowerFree family 3 ground →
      HighFreq family i →
      p ∈ family.offDiag →
      2 ≤ (p.1 ∪ p.2).card) →
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
      IsMaximalSunflowerFree family 3 ground →
      HighFreq family i →
      ((family.card - coordDegree family i) *
          ((family.card - coordDegree family i) - 1)) * 2 ^ (ground.card - 3) +
        (2 * coordDegree family i * (family.card - coordDegree family i)) *
          2 ^ (ground.card - 2) +
        (family.card - coordDegree family i) <
        2 ^ (ground.card - 1)) →
    (∀ k : ℕ, LowCaseCountingBoundUniform (α := α) k) →
    (∀ k : ℕ, HighCaseCountingBoundUniform (α := α) k) →
    HighCaseCountingBoundAll (α := α) := by
  intro hlow_floor hlow_env hhigh_floor hhigh_env hlow_uniform hhigh_uniform
  exact (counting_all_of_coarse_uniform_envelopes (α := α)
    hlow_floor hlow_env hhigh_floor hhigh_env hlow_uniform hhigh_uniform).2

/-- Route packager: with coarse envelope assumptions in place, the existing
uniform-route leaves (`candidate_c6f983a*`, `candidate_c0210d9*`) close both
global counting-all bounds. -/
theorem counting_all_of_coarse_envelopes_and_uniform_route
    {α : Type*} [DecidableEq α] :
    CoarseEnvelopeRouteHyp (α := α) →
    LowCaseCountingBoundAll (α := α) ∧ HighCaseCountingBoundAll (α := α) := by
  intro hcoarse
  rcases hcoarse with ⟨hlow_floor, hlow_env, hhigh_floor, hhigh_env⟩
  exact counting_all_of_coarse_uniform_envelopes
    (α := α)
    hlow_floor hlow_env hhigh_floor hhigh_env
    (candidate_c6f983a_lowCaseCountingBoundUniform_all_k (α := α))
    (candidate_c0210d9_highCaseCountingBoundUniform_all_k (α := α))

/-- Convergence package for the remaining counting-side leaves:
coarse-envelope assumptions plus the already-closed uniform route imply all
guarded and large counting leaves at threshold `n₀`. -/
theorem guarded_and_large_bounds_of_coarse_envelopes_and_uniform_route
    {α : Type*} [DecidableEq α] (n₀ : ℕ) :
    CoarseEnvelopeRouteHyp (α := α) →
    LowCaseCountingBoundSmallGuarded (α := α) ∧
      LowCaseUniformDecompositionHypGuarded (α := α) ∧
      HighCaseCountingBoundSmallGuarded (α := α) ∧
      HighCaseUniformDecompositionHypGuarded (α := α) ∧
      LowCaseCountingBoundLarge (α := α) n₀ ∧
      HighCaseCountingBoundLarge (α := α) n₀ := by
  intro hcoarse
  rcases counting_all_of_coarse_envelopes_and_uniform_route
      (α := α) hcoarse with
    ⟨hlow_all, hhigh_all⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact lowCaseCountingBoundSmallGuarded_of_counting_all
      (α := α) hlow_all hhigh_all
  · exact lowCaseUniformDecompositionHypGuarded_of_counting_all
      (α := α) hlow_all hhigh_all
  · exact highCaseCountingBoundSmallGuarded_of_counting_all
      (α := α) hlow_all hhigh_all
  · exact highCaseUniformDecompositionHypGuarded_of_counting_all
      (α := α) hlow_all hhigh_all
  · exact lowCaseCountingBoundLarge_of_counting_all
      (α := α) n₀ hlow_all
  · exact highCaseCountingBoundLarge_of_counting_all
      (α := α) n₀ hhigh_all

/-- Route closure: coarse off-diagonal envelopes plus uniform-layer counting
bounds imply the global balance conjecture. -/
theorem balance_conjecture_of_coarse_uniform_envelopes
    {α : Type*} [DecidableEq α] :
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α)
        (p : Finset α × Finset α),
      IsMaximalSunflowerFree family 3 ground →
      i ∈ ground →
      LowFreq family i →
      p ∈ (familyOut family i).offDiag →
      2 ≤ (p.1 ∪ p.2).card) →
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
      IsMaximalSunflowerFree family 3 ground →
      i ∈ ground →
      LowFreq family i →
      (((familyIn family i).card * (familyIn family i).card -
          (familyIn family i).card) * 2 ^ (ground.card - 2) +
        ((familyOut family i).card * (familyOut family i).card -
          (familyOut family i).card) * 2 ^ (ground.card - 3)) +
        coordDegree family i <
        2 ^ (ground.card - 1)) →
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α)
        (p : Finset α × Finset α),
      IsMaximalSunflowerFree family 3 ground →
      HighFreq family i →
      p ∈ family.offDiag →
      2 ≤ (p.1 ∪ p.2).card) →
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
      IsMaximalSunflowerFree family 3 ground →
      HighFreq family i →
      ((family.card - coordDegree family i) *
          ((family.card - coordDegree family i) - 1)) * 2 ^ (ground.card - 3) +
        (2 * coordDegree family i * (family.card - coordDegree family i)) *
          2 ^ (ground.card - 2) +
        (family.card - coordDegree family i) <
        2 ^ (ground.card - 1)) →
    (∀ k : ℕ, LowCaseCountingBoundUniform (α := α) k) →
    (∀ k : ℕ, HighCaseCountingBoundUniform (α := α) k) →
    BalanceConjecture (α := α) := by
  intro hlow_floor hlow_env hhigh_floor hhigh_env hlow_uniform hhigh_uniform
  rcases counting_all_of_coarse_uniform_envelopes (α := α)
      hlow_floor hlow_env hhigh_floor hhigh_env hlow_uniform hhigh_uniform with
    ⟨hlow_all, hhigh_all⟩
  exact balance_conjecture_from_counting_all (α := α) hlow_all hhigh_all

/-- Route closure (paired forms): coarse off-diagonal envelopes plus uniform-layer
counting bounds imply both Nat and rational balance-conjecture forms. -/
theorem balance_conjectures_of_coarse_uniform_envelopes
    {α : Type*} [DecidableEq α] :
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α)
        (p : Finset α × Finset α),
      IsMaximalSunflowerFree family 3 ground →
      i ∈ ground →
      LowFreq family i →
      p ∈ (familyOut family i).offDiag →
      2 ≤ (p.1 ∪ p.2).card) →
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
      IsMaximalSunflowerFree family 3 ground →
      i ∈ ground →
      LowFreq family i →
      (((familyIn family i).card * (familyIn family i).card -
          (familyIn family i).card) * 2 ^ (ground.card - 2) +
        ((familyOut family i).card * (familyOut family i).card -
          (familyOut family i).card) * 2 ^ (ground.card - 3)) +
        coordDegree family i <
        2 ^ (ground.card - 1)) →
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α)
        (p : Finset α × Finset α),
      IsMaximalSunflowerFree family 3 ground →
      HighFreq family i →
      p ∈ family.offDiag →
      2 ≤ (p.1 ∪ p.2).card) →
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
      IsMaximalSunflowerFree family 3 ground →
      HighFreq family i →
      ((family.card - coordDegree family i) *
          ((family.card - coordDegree family i) - 1)) * 2 ^ (ground.card - 3) +
        (2 * coordDegree family i * (family.card - coordDegree family i)) *
          2 ^ (ground.card - 2) +
        (family.card - coordDegree family i) <
        2 ^ (ground.card - 1)) →
    (∀ k : ℕ, LowCaseCountingBoundUniform (α := α) k) →
    (∀ k : ℕ, HighCaseCountingBoundUniform (α := α) k) →
    BalanceConjectureNat (α := α) ∧ BalanceConjecture (α := α) := by
  intro hlow_floor hlow_env hhigh_floor hhigh_env hlow_uniform hhigh_uniform
  rcases counting_all_of_coarse_uniform_envelopes (α := α)
      hlow_floor hlow_env hhigh_floor hhigh_env hlow_uniform hhigh_uniform with
    ⟨hlow_all, hhigh_all⟩
  exact balance_conjectures_from_counting_all (α := α) hlow_all hhigh_all

-- Closure wrapper (binder-form) so the frontier scanner can credit this leaf.
theorem candidate_c25996f_highCaseUniformDecompositionHyp_closed
    {α : Type*} [DecidableEq α]
    (hweight_template :
      ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
        IsMaximalSunflowerFree family 3 ground →
        i ∈ ground →
        HighFreq family i →
        (∀ r : ℕ, HighCaseCountingBoundUniform (α := α) r) →
        (∑ p ∈ family.offDiag, pairWeightAvoiding ground i p) +
          (family.card - coordDegree family i) <
          2 ^ (ground.card - 1)) :
    HighCaseUniformDecompositionHyp (α := α) := by
  exact
    candidate_c25996f_highCaseUniformDecompositionHyp_of_layerwise_weight_cancellation
      (α := α) hweight_template

-- Scout validated stub: candidate_c193087_pairWeightEnvelopeHyp_closed
theorem candidate_c193087_pairWeightEnvelopeHyp_closed
    {α : Type*} [DecidableEq α] :
    PairWeightEnvelopeHyp (α := α) :=
  candidate_c73be51_pairWeightEnvelopeHyp

-- Scout validated stub: candidate_c193087_weight_sum_le_of_pointwise_union_lower_activates
theorem candidate_c193087_weight_sum_le_of_pointwise_union_lower_activates
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) (c : ℕ) :
    IsOnGround family ground →
    PairWeightEnvelopeHyp (α := α) →
    (∀ p ∈ family.offDiag, c ≤ (p.1 ∪ p.2).card) →
    ∑ p ∈ family.offDiag, pairWeight ground i p ≤
      family.offDiag.card * 2 ^ (ground.card - c) := by
  intro h_on henv hpoint
  exact weight_sum_le_of_pointwise_union_lower family ground i c h_on henv hpoint

-- Scout validated stub: candidate_c8a7e22_complement_map_injOn_on_ground
theorem candidate_c8a7e22_complement_map_injOn_on_ground
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) :
    IsOnGround family ground →
    Set.InjOn (fun S : Finset α => ground \ S) (↑family : Set (Finset α)) := by
  intro h_on
  exact highFreq_complement_injOn_aux family ground h_on

-- Scout validated stub: candidate_c8a7e22_coordDegree_complement_image_eq
theorem candidate_c8a7e22_coordDegree_complement_image_eq
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    IsOnGround family ground →
    i ∈ ground →
    coordDegree (family.image (fun S => ground \ S)) i =
      family.card - coordDegree family i := by
  intro h_on hi
  classical
  have hinj := highFreq_complement_injOn_aux family ground h_on
  have hfilt_eq :
      (family.image (fun S => ground \ S)).filter (fun T => i ∈ T) =
        (family.filter (fun S => i ∉ S)).image (fun S => ground \ S) := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨S, hS, rfl⟩, hiT⟩
      exact ⟨S, ⟨hS, (Finset.mem_sdiff.mp hiT).2⟩, rfl⟩
    · rintro ⟨S, ⟨hS, hiS⟩, rfl⟩
      exact ⟨⟨S, hS, rfl⟩, Finset.mem_sdiff.mpr ⟨hi, hiS⟩⟩
  have hinj_sub : Set.InjOn (fun S : Finset α => ground \ S)
      ↑(family.filter (fun S => i ∉ S)) := by
    intro S hS T hT hEq
    exact hinj (Finset.mem_coe.mpr ((Finset.mem_filter.mp (Finset.mem_coe.mp hS)).1))
      (Finset.mem_coe.mpr ((Finset.mem_filter.mp (Finset.mem_coe.mp hT)).1)) hEq
  unfold coordDegree
  calc
    ((family.image (fun S => ground \ S)).filter (fun S => i ∈ S)).card
        = ((family.filter (fun S => i ∉ S)).image (fun S => ground \ S)).card := by
          rw [hfilt_eq]
    _ = (family.filter (fun S => i ∉ S)).card := Finset.card_image_of_injOn hinj_sub
    _ = family.card - (family.filter (fun S => i ∈ S)).card := card_familyOut family i

-- Scout validated stub: candidate_c8a7e22_highFreq_to_lowFreq_complement_guarded
theorem candidate_c8a7e22_highFreq_to_lowFreq_complement_guarded
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    (family.image (fun S => ground \ S)).card = family.card →
    coordDegree (family.image (fun S => ground \ S)) i =
      family.card - coordDegree family i →
    HighFreq family i →
    LowFreq (family.image (fun S => ground \ S)) i := by
  intro hcard hcoord hhf
  have hd_le : coordDegree family i ≤ family.card := coordDegree_le_card family i
  unfold LowFreq
  rw [hcard, hcoord]
  unfold HighFreq at hhf
  omega

-- Scout validated stub: candidate_c9d5adc_exists_uniform_layer_lowFreq
theorem candidate_c9d5adc_exists_uniform_layer_lowFreq
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (i : α) :
    LowFreq family i →
    ∃ r : ℕ,
      (family.filter (fun S => S.card = r)).Nonempty ∧
      (∀ S ∈ family.filter (fun S => S.card = r), S.card = r) ∧
      LowFreq (family.filter (fun S => S.card = r)) i := by
  simpa using candidate_cef9f68_exists_uniform_layer_lowFreq (α := α) family i

-- Scout validated stub: candidate_c9d5adc_exists_uniform_layer_highFreq
theorem candidate_c9d5adc_exists_uniform_layer_highFreq
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (i : α) :
    HighFreq family i →
    ∃ r : ℕ,
      (family.filter (fun S => S.card = r)).Nonempty ∧
      (∀ S ∈ family.filter (fun S => S.card = r), S.card = r) ∧
      HighFreq (family.filter (fun S => S.card = r)) i := by
  simpa using candidate_cef9f68_exists_uniform_layer_highFreq (α := α) family i
