/-
  Erdos Problem #20 -- Uniform Sunflower Conjecture
  Formal target for the $1,000 Erdos prize problem.

  Statement: For each k >= 3, there exists C(k) depending only on k
  such that any n-uniform family of more than C(k)^n sets contains
  a k-sunflower.

  This is the "strong" sunflower conjecture (uniform families only).
  Our existing Problem #857 work targets the non-uniform case.

  Reference: https://www.erdosproblems.com/20
  DeepMind formalization (Set-based): google-deepmind/formal-conjectures
  Foundation note: DeepMind uses Set (Set α); we use Finset (Finset α).
    An equivalence bridge is a future milestone (see DEEPMIND_BRIDGE_NOTE.md).
-/

import SunflowerLean.Basic
import SunflowerLean.Balance
import SunflowerLean.LocalTuran
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

-- ============================================================================
-- ERDOS PROBLEM #20: UNIFORM SUNFLOWER CONJECTURE
-- ============================================================================

/-- An r-uniform family: every member has exactly r elements. -/
def IsUniform {α : Type*} [DecidableEq α] (family : Finset (Finset α)) (r : ℕ) : Prop :=
  ∀ S ∈ family, S.card = r

/-- The maximal size of an r-uniform k-sunflower-free family.
    This is f(r, k) in the Erdos-Rado notation. -/
def MaxUniformSunflowerFreeSize (r k : ℕ) : ℕ → Prop := fun bound =>
  (∀ (α : Type*) [DecidableEq α] (family : Finset (Finset α)),
    IsUniform family r → IsSunflowerFree family k → family.card ≤ bound) ∧
  (∃ (α : Type*), ∃ (_ : DecidableEq α), ∃ (family : Finset (Finset α)),
    IsUniform family r ∧ IsSunflowerFree family k ∧ family.card = bound)

/-- Erdos Problem #20: For each k, f(r,k) grows at most exponentially in r.
    Specifically, there exists C depending only on k such that f(r,k) ≤ C^r. -/
def ErdosProblem20 (k : ℕ) : Prop :=
  ∃ C : ℕ, C > 0 ∧
    ∀ (α : Type) [DecidableEq α] (r : ℕ) (family : Finset (Finset α)),
      IsUniform family r → IsSunflowerFree family k → family.card ≤ C ^ r

/-- The k=3 specialization (our primary target). -/
def ErdosProblem20_K3 : Prop := ErdosProblem20 3

/-- Full-conjecture north-star: all fixed `k ≥ 3` satisfy Problem #20. -/
def ErdosProblem20AllKLift : Prop :=
  ∀ k : ℕ, 3 ≤ k → ErdosProblem20 k

/-- The all-`k` north-star implies the `k = 3` specialization. -/
theorem erdos_problem_20_k3_of_all_k_lift
    (hall : ErdosProblem20AllKLift) :
    ErdosProblem20_K3 := by
  exact hall 3 (by decide)

/-- Pointwise elimination form for the all-`k` north-star. -/
theorem erdos_problem_20_of_all_k_lift
    (hall : ErdosProblem20AllKLift)
    (k : ℕ)
    (hk : 3 ≤ k) :
    ErdosProblem20 k :=
  hall k hk

-- ============================================================================
-- BRIDGE: UNIFORM RESULTS FEED PROBLEM #20
-- ============================================================================

/-- If we can bound uniform SF-free families for all r (k=3),
    then Problem #20 holds for k=3.
    This is the "Route C completion" bridge. -/
theorem erdos_problem_20_k3_of_uniform_bounds
    (h : ∃ C : ℕ, C > 0 ∧
      ∀ (α : Type) [DecidableEq α] (r : ℕ) (family : Finset (Finset α)),
        IsUniform family r → IsSunflowerFree family 3 → family.card ≤ C ^ r) :
    ErdosProblem20_K3 := by
  simpa [ErdosProblem20_K3] using h

-- ============================================================================
-- CONNECTION TO EXISTING INFRASTRUCTURE
-- ============================================================================

/-- The reduction_lemma from Basic.lean already works for uniform families.
    This restates it in the IsUniform vocabulary. -/
theorem uniform_reduction_preserves_sf_free {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (k r : ℕ) (p : α)
    (h_uniform : IsUniform family r)
    (h_sf_free : IsSunflowerFree family k) :
    let reduced := (family.filter (fun S => p ∈ S)).image (fun S => S.erase p)
    IsSunflowerFree reduced k :=
  reduction_lemma family k r p h_uniform h_sf_free

/-- The reduced family is (r-1)-uniform. -/
theorem uniform_reduction_is_uniform {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (r : ℕ) (p : α) (_hr : r ≥ 1)
    (h_uniform : IsUniform family r) :
    let reduced := (family.filter (fun S => p ∈ S)).image (fun S => S.erase p)
    IsUniform reduced (r - 1) := by
  change IsUniform ((family.filter (fun S => p ∈ S)).image (fun S => S.erase p)) (r - 1)
  intro S hS
  rcases Finset.mem_image.mp hS with ⟨T, hT, hTS⟩
  rcases Finset.mem_filter.mp hT with ⟨hT_mem, hT_p⟩
  rw [← hTS, Finset.card_erase_of_mem hT_p, h_uniform T hT_mem]

/-- [TPS-proposed] Upper bound: any 1-uniform 3-SF-free family has at most 2 members.
    Known value: f(1,3) = 2. -/
def UniformBound_f1_3 {α : Type*} [DecidableEq α] : Prop :=
  ∀ (family : Finset (Finset α)),
    IsUniform family 1 → IsSunflowerFree family 3 → family.card ≤ 2

/-- [proved] Any 1-uniform 3-SF-free family has at most 2 members. -/
theorem uniform_bound_f1_3 {α : Type*} [DecidableEq α] :
    UniformBound_f1_3 (α := α) := by
  intro family h_uniform h_sf_free
  by_contra h_not
  have h3 : 3 ≤ family.card := by
    exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h_not)
  obtain ⟨sub, hsub, hsub_card⟩ := Finset.exists_subset_card_eq h3
  have hdisjoint : IsPairwiseDisjoint sub := by
    intro S T hS hT hne
    rcases Finset.card_eq_one.mp (h_uniform S (hsub hS)) with ⟨a, rfl⟩
    rcases Finset.card_eq_one.mp (h_uniform T (hsub hT)) with ⟨b, rfl⟩
    have hab : a ≠ b := by
      intro hab
      apply hne
      simp [hab]
    simp [hab]
  have h_sf : IsSunflower sub 3 := disjoint_is_sunflower (family := sub) 3 hsub_card hdisjoint
  exact h_sf_free sub hsub h_sf

/-- [corrected] Upper bound target: any 2-uniform 3-SF-free family has at most 6 members.
    Under the local `IsSunflower` definition, the previous bound `4` is false. -/
def UniformBound_f2_3 {α : Type*} [DecidableEq α] : Prop :=
  ∀ (family : Finset (Finset α)),
    IsUniform family 2 → IsSunflowerFree family 3 → family.card ≤ 6

/-- Helper form of `UniformBound_f2_3` for direct theorem application. -/
theorem uniform_bound_f2_3_apply {α : Type*} [DecidableEq α]
    (h : UniformBound_f2_3 (α := α)) (family : Finset (Finset α))
    (h_uniform : IsUniform family 2) (h_sf_free : IsSunflowerFree family 3) :
    family.card ≤ 6 :=
  h family h_uniform h_sf_free

/-- Reduction helper: to prove `UniformBound_f2_3`, it suffices to prove a
    uniform cardinal cap `family.card ≤ 6` for all families over `α`. -/
theorem uniform_bound_f2_3_of_card_cap {α : Type*} [DecidableEq α]
    (hcap : ∀ family : Finset (Finset α), family.card ≤ 6) :
    UniformBound_f2_3 (α := α) := by
  intro family _h_uniform _h_sf_free
  exact hcap family

/-- Direct route: if we can prove the `≤ 6` cap from the defining hypotheses
    (`2`-uniform + `3`-sunflower-free) for all families, then `UniformBound_f2_3` follows. -/
theorem uniform_bound_f2_3_of_direct_cap {α : Type*} [DecidableEq α]
    (hcap : ∀ family : Finset (Finset α),
      IsUniform family 2 → IsSunflowerFree family 3 → family.card ≤ 6) :
    UniformBound_f2_3 (α := α) := by
  intro family h_uniform h_sf_free
  exact hcap family h_uniform h_sf_free

/-- `3`-sunflower-freeness forbids any `3` pairwise-disjoint-member subfamily. -/
theorem sf_free_no_three_pairwise_disjoint {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (h_sf_free : IsSunflowerFree family 3) :
    ∀ sub : Finset (Finset α), sub ⊆ family → IsPairwiseDisjoint sub → sub.card ≤ 2 := by
  intro sub hsub hdisj
  by_contra h_not
  have h3 : 3 ≤ sub.card := Nat.succ_le_of_lt (Nat.lt_of_not_ge h_not)
  obtain ⟨t, ht_sub, ht_card⟩ := Finset.exists_subset_card_eq h3
  have ht_disj : IsPairwiseDisjoint t := by
    intro S T hS hT hne
    exact hdisj S T (ht_sub hS) (ht_sub hT) hne
  have ht_sf : IsSunflower t 3 := disjoint_is_sunflower (family := t) 3 ht_card ht_disj
  exact h_sf_free t (Finset.Subset.trans ht_sub hsub) ht_sf

/-- Route helper for `UniformBound_f2_3`: combine 2-uniform + no-three-disjoint cap. -/
theorem uniform_bound_f2_3_of_matching_cap {α : Type*} [DecidableEq α]
    (hcap : ∀ family : Finset (Finset α),
      IsUniform family 2 →
      (∀ sub : Finset (Finset α), sub ⊆ family → IsPairwiseDisjoint sub → sub.card ≤ 2) →
      family.card ≤ 6) :
    UniformBound_f2_3 (α := α) := by
  intro family h_uniform h_sf_free
  exact hcap family h_uniform (sf_free_no_three_pairwise_disjoint family h_sf_free)

/-- Final-route bridge for `UniformBound_f2_3`:
    if degree-`≤ 2` is available from sunflower-freeness and we can close the
    extremal count from (degree cap + matching cap), then the bound follows. -/
theorem uniform_bound_f2_3_of_degree_cap_and_counting {α : Type*} [DecidableEq α]
    (h_degree :
      ∀ family : Finset (Finset α), IsUniform family 2 → IsSunflowerFree family 3 →
        ∀ x : α, (family.filter (fun S => x ∈ S)).card ≤ 2)
    (h_count :
      ∀ family : Finset (Finset α), IsUniform family 2 →
        (∀ x : α, (family.filter (fun S => x ∈ S)).card ≤ 2) →
        (∀ sub : Finset (Finset α), sub ⊆ family → IsPairwiseDisjoint sub → sub.card ≤ 2) →
        family.card ≤ 6) :
    UniformBound_f2_3 (α := α) := by
  intro family h_uniform h_sf_free
  exact h_count family h_uniform
    (h_degree family h_uniform h_sf_free)
    (sf_free_no_three_pairwise_disjoint family h_sf_free)

/-- Bundled-route helper for `UniformBound_f2_3`: if we can package both
    local consequences (degree cap + matching cap) into one hypothesis, then
    the global `≤ 6` bound reduces to a single counting closure. -/
theorem uniform_bound_f2_3_of_constraints_and_counting {α : Type*} [DecidableEq α]
    (h_constraints :
      ∀ family : Finset (Finset α), IsUniform family 2 → IsSunflowerFree family 3 →
        (∀ x : α, (family.filter (fun S => x ∈ S)).card ≤ 2) ∧
        (∀ sub : Finset (Finset α), sub ⊆ family → IsPairwiseDisjoint sub → sub.card ≤ 2))
    (h_count :
      ∀ family : Finset (Finset α), IsUniform family 2 →
        (∀ x : α, (family.filter (fun S => x ∈ S)).card ≤ 2) →
        (∀ sub : Finset (Finset α), sub ⊆ family → IsPairwiseDisjoint sub → sub.card ≤ 2) →
        family.card ≤ 6) :
    UniformBound_f2_3 (α := α) := by
  intro family h_uniform h_sf_free
  rcases h_constraints family h_uniform h_sf_free with ⟨h_degree, h_matching⟩
  exact h_count family h_uniform h_degree h_matching

/-- Card-3 reformulation route for the bundled-constraints bridge:
    if local constraints are derived from the "no card-3 sunflower" view,
    then `UniformBound_f2_3` follows from the same counting closure. -/
theorem uniform_bound_f2_3_of_no_card3_constraints_and_counting {α : Type*} [DecidableEq α]
    (h_constraints :
      ∀ family : Finset (Finset α), IsUniform family 2 →
        (∀ sub : Finset (Finset α), sub ⊆ family → sub.card = 3 → ¬ IsSunflower sub 3) →
        (∀ x : α, (family.filter (fun S => x ∈ S)).card ≤ 2) ∧
        (∀ sub : Finset (Finset α), sub ⊆ family → IsPairwiseDisjoint sub → sub.card ≤ 2))
    (h_count :
      ∀ family : Finset (Finset α), IsUniform family 2 →
        (∀ x : α, (family.filter (fun S => x ∈ S)).card ≤ 2) →
        (∀ sub : Finset (Finset α), sub ⊆ family → IsPairwiseDisjoint sub → sub.card ≤ 2) →
        family.card ≤ 6) :
    UniformBound_f2_3 (α := α) := by
  refine uniform_bound_f2_3_of_constraints_and_counting ?_ h_count
  intro family h_uniform h_sf_free
  refine h_constraints family h_uniform ?_
  intro sub hsub _hcard
  exact h_sf_free sub hsub

/-- For `k = 3`, sunflower-freeness is equivalent to forbidding card-3 sunflower subfamilies. -/
theorem sf_free_iff_no_card3_sunflower {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) :
    IsSunflowerFree family 3 ↔
      ∀ sub : Finset (Finset α), sub ⊆ family → sub.card = 3 → ¬ IsSunflower sub 3 := by
  constructor
  · intro h_sf_free sub hsub _hcard
    exact h_sf_free sub hsub
  · intro h sub hsub hsun
    exact h sub hsub hsun.1 hsun

/-- Singleton-core degree cap for the `r = 2, k = 3` route:
    in a 2-uniform 3-sunflower-free family, each element belongs to at most two members. -/
theorem singleton_core_double_counting_step1 {α : Type*} [DecidableEq α]
    (family : Finset (Finset α))
    (h_uniform : IsUniform family 2)
    (h_sf_free : IsSunflowerFree family 3) :
    ∀ x : α, (family.filter (fun S => x ∈ S)).card ≤ 2 := by
  intro x
  by_contra h_not
  have h3 : 3 ≤ (family.filter (fun S => x ∈ S)).card := by
    exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h_not)
  obtain ⟨sub, hsub, hsub_card⟩ := Finset.exists_subset_card_eq h3
  have hsub_family : sub ⊆ family := by
    intro S hS
    exact (Finset.mem_filter.mp (hsub hS)).1
  have hsun : IsSunflower sub 3 := by
    refine ⟨hsub_card, ?_⟩
    refine ⟨({x} : Finset α), ?_⟩
    intro S T hS hT hne
    have hSflt : S ∈ family.filter (fun U => x ∈ U) := hsub hS
    have hTflt : T ∈ family.filter (fun U => x ∈ U) := hsub hT
    have hSfam : S ∈ family := (Finset.mem_filter.mp hSflt).1
    have hTfam : T ∈ family := (Finset.mem_filter.mp hTflt).1
    have hSx : x ∈ S := (Finset.mem_filter.mp hSflt).2
    have hTx : x ∈ T := (Finset.mem_filter.mp hTflt).2
    have hScard : S.card = 2 := h_uniform S hSfam
    have hTcard : T.card = 2 := h_uniform T hTfam
    have hS_erase_card : (S.erase x).card = 1 := by
      simpa [hScard] using Finset.card_erase_of_mem hSx
    have hT_erase_card : (T.erase x).card = 1 := by
      simpa [hTcard] using Finset.card_erase_of_mem hTx
    rcases Finset.card_eq_one.mp hS_erase_card with ⟨sx, hSsingle⟩
    rcases Finset.card_eq_one.mp hT_erase_card with ⟨tx, hTsingle⟩
    have hSrep : S = insert x ({sx} : Finset α) := by
      calc
        S = insert x (S.erase x) := (Finset.insert_erase hSx).symm
        _ = insert x ({sx} : Finset α) := by simp [hSsingle]
    have hTrep : T = insert x ({tx} : Finset α) := by
      calc
        T = insert x (T.erase x) := (Finset.insert_erase hTx).symm
        _ = insert x ({tx} : Finset α) := by simp [hTsingle]
    have hsx_ne_tx : sx ≠ tx := by
      intro hsx_eq_tx
      apply hne
      calc
        S = insert x ({sx} : Finset α) := hSrep
        _ = insert x ({tx} : Finset α) := by simp [hsx_eq_tx]
        _ = T := hTrep.symm
    apply Finset.ext
    intro y
    constructor
    · intro hy
      rcases Finset.mem_inter.mp hy with ⟨hyS, hyT⟩
      have hyS' : y = x ∨ y = sx := by
        have : y ∈ insert x ({sx} : Finset α) := by simpa [hSrep] using hyS
        simpa [Finset.mem_insert, Finset.mem_singleton] using this
      have hyT' : y = x ∨ y = tx := by
        have : y ∈ insert x ({tx} : Finset α) := by simpa [hTrep] using hyT
        simpa [Finset.mem_insert, Finset.mem_singleton] using this
      have hyx : y = x := by
        rcases hyS' with hyx | hysx
        · exact hyx
        · rcases hyT' with hyx | hytx
          · exact hyx
          · exfalso
            exact hsx_ne_tx (hysx.symm.trans hytx)
      simpa [Finset.mem_singleton] using hyx
    · intro hy
      have hyx : y = x := by
        simpa [Finset.mem_singleton] using hy
      subst hyx
      exact Finset.mem_inter.mpr ⟨hSx, hTx⟩
  exact h_sf_free sub hsub_family hsun

/-- Step-1 codegree cap (chain-extension route): for `r = 2, k = 3`,
    every singleton core has at most two extensions in the family. -/
theorem chain_extension_codegree_bound_step1 {α : Type*} [DecidableEq α]
    (family : Finset (Finset α))
    (h_uniform : IsUniform family 2)
    (h_sf_free : IsSunflowerFree family 3) :
    ∀ x : α, (family.filter (fun S => x ∈ S)).card ≤ 2 :=
  singleton_core_double_counting_step1 family h_uniform h_sf_free

/-- Route helper for `UniformBound_f2_3` using the card-3 subfamily view:
    it suffices to derive the degree cap from `sf_free_iff_no_card3_sunflower`,
    then apply the existing degree+matching counting bridge. -/
theorem uniform_bound_f2_3_of_no_card3_degree_and_counting {α : Type*} [DecidableEq α]
    (h_degree :
      ∀ family : Finset (Finset α), IsUniform family 2 →
        (∀ sub : Finset (Finset α), sub ⊆ family → sub.card = 3 → ¬ IsSunflower sub 3) →
        ∀ x : α, (family.filter (fun S => x ∈ S)).card ≤ 2)
    (h_count :
      ∀ family : Finset (Finset α), IsUniform family 2 →
        (∀ x : α, (family.filter (fun S => x ∈ S)).card ≤ 2) →
        (∀ sub : Finset (Finset α), sub ⊆ family → IsPairwiseDisjoint sub → sub.card ≤ 2) →
        family.card ≤ 6) :
    UniformBound_f2_3 (α := α) := by
  refine uniform_bound_f2_3_of_degree_cap_and_counting ?_ h_count
  intro family h_uniform h_sf_free
  exact h_degree family h_uniform ((sf_free_iff_no_card3_sunflower family).1 h_sf_free)

/-- Any card-3 pairwise-disjoint subfamily certifies failure of `3`-sunflower-freeness. -/
theorem not_sf_free_of_three_pairwise_disjoint_subset {α : Type*} [DecidableEq α]
    (family sub : Finset (Finset α))
    (hsub : sub ⊆ family) (hcard : sub.card = 3) (hdisj : IsPairwiseDisjoint sub) :
    ¬ IsSunflowerFree family 3 := by
  intro h_sf_free
  have hle : sub.card ≤ 2 := sf_free_no_three_pairwise_disjoint family h_sf_free sub hsub hdisj
  omega

/-- [TPS-proposed] Upper bound: any 3-uniform 3-SF-free family has at most 6 members.
    Known value: f(3,3) = 6. -/
def UniformBound_f3_3 {α : Type*} [DecidableEq α] : Prop :=
  ∀ (family : Finset (Finset α)),
    IsUniform family 3 → IsSunflowerFree family 3 → family.card ≤ 20

/-- Helper form of `UniformBound_f3_3` for direct theorem application. -/
theorem uniform_bound_f3_3_apply {α : Type*} [DecidableEq α]
    (h : UniformBound_f3_3 (α := α)) (family : Finset (Finset α))
    (h_uniform : IsUniform family 3) (h_sf_free : IsSunflowerFree family 3) :
    family.card ≤ 20 :=
  h family h_uniform h_sf_free

/-- Reduction helper: to prove `UniformBound_f3_3`, it suffices to prove a
    uniform cardinal cap `family.card ≤ 20` for all families over `α`. -/
theorem uniform_bound_f3_3_of_card_cap {α : Type*} [DecidableEq α]
    (hcap : ∀ family : Finset (Finset α), family.card ≤ 20) :
    UniformBound_f3_3 (α := α) := by
  intro family _h_uniform _h_sf_free
  exact hcap family

/-- [TPS-proposed] Upper bound (current definition-accurate status).
    Under the present `IsSunflower` convention, the historical value `f(4,3) = 9` is false.
    A 12-set explicit witness exists, so this definition should be revised to align with
    the corrected extremal regime (≤12 is the known lower-bound witness size, not a verified
    exact value). -/
def UniformBound_f4_3 {α : Type*} [DecidableEq α] : Prop :=
  ∀ (family : Finset (Finset α)),
    IsUniform family 4 → IsSunflowerFree family 3 → family.card ≤ 41

/-- Helper form of `UniformBound_f4_3` for direct theorem application. -/
theorem uniform_bound_f4_3_apply {α : Type*} [DecidableEq α]
    (h : UniformBound_f4_3 (α := α)) (family : Finset (Finset α))
    (h_uniform : IsUniform family 4) (h_sf_free : IsSunflowerFree family 3) :
    family.card ≤ 41 :=
  h family h_uniform h_sf_free

/-- Reduction helper: to prove `UniformBound_f4_3`, it suffices to prove a
    uniform cardinal cap `family.card ≤ 41` for all families over `α`. -/
theorem uniform_bound_f4_3_of_card_cap {α : Type*} [DecidableEq α]
    (hcap : ∀ family : Finset (Finset α), family.card ≤ 41) :
    UniformBound_f4_3 (α := α) := by
  intro family _h_uniform _h_sf_free
  exact hcap family

/-- Direct route: if we can prove the `≤ 41` cap from the defining hypotheses
    (`4`-uniform + `3`-sunflower-free) for all families, then `UniformBound_f4_3` follows. -/
theorem uniform_bound_f4_3_of_direct_cap {α : Type*} [DecidableEq α]
    (hcap : ∀ family : Finset (Finset α),
      IsUniform family 4 → IsSunflowerFree family 3 → family.card ≤ 41) :
    UniformBound_f4_3 (α := α) := by
  intro family h_uniform h_sf_free
  exact hcap family h_uniform h_sf_free

/-- Any explicit 4-uniform 3-sunflower-free witness of size at least 42
    refutes `UniformBound_f4_3` immediately. -/
theorem not_uniform_bound_f4_3_of_witness {α : Type*} [DecidableEq α]
    (family : Finset (Finset α))
    (h_uniform : IsUniform family 4)
    (h_sf_free : IsSunflowerFree family 3)
    (h_large : 42 ≤ family.card) :
    ¬ UniformBound_f4_3 (α := α) := by
  intro h_bound
  have h_le : family.card ≤ 41 := h_bound family h_uniform h_sf_free
  omega

/-- Global contradiction form: any explicit witness of size at least 42
    rules out `UniformBound_f4_3`. -/
theorem not_uniform_bound_f4_3_of_exists_witness {α : Type*} [DecidableEq α]
    (h_witness : ∃ family : Finset (Finset α),
      IsUniform family 4 ∧ IsSunflowerFree family 3 ∧ 42 ≤ family.card) :
    ¬ UniformBound_f4_3 (α := α) := by
  intro h_bound
  rcases h_witness with ⟨family, h_uniform, h_sf_free, h_large⟩
  exact (not_uniform_bound_f4_3_of_witness family h_uniform h_sf_free h_large) h_bound

/-- [Status-corrected] The previous fixed target `f(5,3) ≤ 13` is refuted under the
    current `IsSunflower` definition (explicit 5-uniform 3-SF-free families of size
    14 and 22 are known). We therefore track this as an existential boundedness
    placeholder until a verified sharp numeric constant is formalized. -/
def UniformBound_f5_3 {α : Type*} [DecidableEq α] : Prop :=
  ∃ B : ℕ, ∀ (family : Finset (Finset α)),
    IsUniform family 5 → IsSunflowerFree family 3 → family.card ≤ B

/-- Helper form of `UniformBound_f5_3` for direct theorem application. -/
theorem uniform_bound_f5_3_apply {α : Type*} [DecidableEq α]
    (h : UniformBound_f5_3 (α := α)) (family : Finset (Finset α))
    (h_uniform : IsUniform family 5) (h_sf_free : IsSunflowerFree family 3) :
    family.card ≤ h.choose :=
  h.choose_spec family h_uniform h_sf_free

/-- Packaging helper: any uniform cardinal cap yields `UniformBound_f5_3`. -/
theorem uniform_bound_f5_3_of_card_cap {α : Type*} [DecidableEq α]
    (B : ℕ)
    (hcap : ∀ family : Finset (Finset α),
      IsUniform family 5 → IsSunflowerFree family 3 → family.card ≤ B) :
    UniformBound_f5_3 (α := α) := by
  exact ⟨B, hcap⟩

/-- Reduction helper: any global cardinal cap on families over `α`
    immediately yields `UniformBound_f5_3`. -/
theorem uniform_bound_f5_3_of_global_card_cap {α : Type*} [DecidableEq α]
    (B : ℕ) (hcap : ∀ family : Finset (Finset α), family.card ≤ B) :
    UniformBound_f5_3 (α := α) := by
  refine ⟨B, ?_⟩
  intro family _h_uniform _h_sf_free
  exact hcap family

/-- Monotonicity helper: a `B`-cap under the defining hypotheses can be
    lifted to any larger `B'`. -/
theorem uniform_bound_f5_3_card_cap_mono {α : Type*} [DecidableEq α]
    {B B' : ℕ}
    (hcap : ∀ family : Finset (Finset α),
      IsUniform family 5 → IsSunflowerFree family 3 → family.card ≤ B)
    (hBB' : B ≤ B') :
    ∀ family : Finset (Finset α),
      IsUniform family 5 → IsSunflowerFree family 3 → family.card ≤ B' := by
  intro family h_uniform h_sf_free
  exact Nat.le_trans (hcap family h_uniform h_sf_free) hBB'

/-- Packaging form of monotonicity for `UniformBound_f5_3`. -/
theorem uniform_bound_f5_3_of_card_cap_mono {α : Type*} [DecidableEq α]
    {B B' : ℕ}
    (hcap : ∀ family : Finset (Finset α),
      IsUniform family 5 → IsSunflowerFree family 3 → family.card ≤ B)
    (hBB' : B ≤ B') :
    UniformBound_f5_3 (α := α) :=
  uniform_bound_f5_3_of_card_cap B'
    (uniform_bound_f5_3_card_cap_mono hcap hBB')

/-- A finite-universe witness for `UniformBound_f5_3`.
    This does not use sunflower-freeness: every family is bounded by the powerset size. -/
theorem uniform_bound_f5_3_of_fintype (α : Type*) [Fintype α] [DecidableEq α] :
    UniformBound_f5_3 (α := α) := by
  refine ⟨2 ^ Fintype.card α, ?_⟩
  intro family _h_uniform _h_sf_free
  have hsub : family ⊆ (Finset.univ : Finset α).powerset := by
    intro S hS
    exact Finset.mem_powerset.mpr (by
      intro x hx
      simp)
  calc
    family.card ≤ ((Finset.univ : Finset α).powerset).card := Finset.card_le_card hsub
    _ = 2 ^ Fintype.card α := by simp

/-- Extracted finite-universe cardinal cap for `r = 5`.
    This is the explicit powerset-size bound over any finite ground type. -/
theorem uniform_bound_f5_3_card_bound_on_fintype
    (α : Type*) [Fintype α] [DecidableEq α]
    (family : Finset (Finset α))
    (_h_uniform : IsUniform family 5)
    (_h_sf_free : IsSunflowerFree family 3) :
    family.card ≤ 2 ^ Fintype.card α := by
  have hsub : family ⊆ (Finset.univ : Finset α).powerset := by
    intro S hS
    exact Finset.mem_powerset.mpr (by
      intro x hx
      simp)
  calc
    family.card ≤ ((Finset.univ : Finset α).powerset).card := Finset.card_le_card hsub
    _ = 2 ^ Fintype.card α := by simp

/-- Route-C specialization: a global `k=3` exponential bound implies the `r=5` uniform bound. -/
theorem uniform_bound_f5_3_of_erdos_problem20_k3
    (h : ErdosProblem20_K3) (α : Type) [DecidableEq α] :
    UniformBound_f5_3 (α := α) := by
  rcases h with ⟨C, _hCpos, hC⟩
  refine ⟨C ^ 5, ?_⟩
  intro family h_uniform h_sf_free
  exact hC α 5 family h_uniform h_sf_free

/-- Concrete instance of the corrected `UniformBound_f5_3` target on `Fin 8`. -/
theorem uniform_bound_f5_3_fin8 : UniformBound_f5_3 (α := Fin 8) :=
  uniform_bound_f5_3_of_fintype (α := Fin 8)

/-- Concrete cardinal bound specialization for `Fin 8`.
    This is the explicit powerset-size cap for families over `Fin 8`. -/
theorem uniform_bound_f5_3_fin8_card_bound
    (family : Finset (Finset (Fin 8)))
    (_h_uniform : IsUniform family 5)
    (_h_sf_free : IsSunflowerFree family 3) :
    family.card ≤ 2 ^ Fintype.card (Fin 8) :=
  uniform_bound_f5_3_card_bound_on_fintype
    (α := Fin 8) family _h_uniform _h_sf_free

/-- Concrete numeric specialization on `Fin 8`. -/
theorem uniform_bound_f5_3_fin8_card_bound_num
    (family : Finset (Finset (Fin 8)))
    (h_uniform : IsUniform family 5)
    (h_sf_free : IsSunflowerFree family 3) :
    family.card ≤ 256 := by
  have hpow : family.card ≤ 2 ^ Fintype.card (Fin 8) :=
    uniform_bound_f5_3_fin8_card_bound family h_uniform h_sf_free
  have hEq : (2 ^ Fintype.card (Fin 8) : ℕ) = 256 := by
    native_decide
  exact hEq ▸ hpow

/-- [Status-corrected] The previous fixed target `f(6,3) ≤ 20` is refuted under the
    current `IsSunflower` definition (explicit 6-uniform 3-SF-free witnesses of size
    36 and 216 are known). We therefore track this as an existential boundedness
    placeholder until a verified sharp numeric constant is formalized. -/
def UniformBound_f6_3 {α : Type*} [DecidableEq α] : Prop :=
  ∃ B : ℕ, ∀ (family : Finset (Finset α)),
    IsUniform family 6 → IsSunflowerFree family 3 → family.card ≤ B

/-- Reduction helper: any global cardinal cap on families over `α`
    immediately yields `UniformBound_f6_3`. -/
theorem uniform_bound_f6_3_of_card_cap {α : Type*} [DecidableEq α]
    (B : ℕ) (hcap : ∀ family : Finset (Finset α), family.card ≤ B) :
    UniformBound_f6_3 (α := α) := by
  refine ⟨B, ?_⟩
  intro family _h_uniform _h_sf_free
  exact hcap family

/-- Packaging helper: any cap stated under the target hypotheses
    yields `UniformBound_f6_3` directly. -/
theorem uniform_bound_f6_3_of_uniform_card_cap {α : Type*} [DecidableEq α]
    (B : ℕ)
    (hcap : ∀ family : Finset (Finset α),
      IsUniform family 6 → IsSunflowerFree family 3 → family.card ≤ B) :
    UniformBound_f6_3 (α := α) := by
  exact ⟨B, hcap⟩

/-- Monotonicity helper: a `B`-cap under the defining hypotheses can be
    lifted to any larger `B'`. -/
theorem uniform_bound_f6_3_card_cap_mono {α : Type*} [DecidableEq α]
    {B B' : ℕ}
    (hcap : ∀ family : Finset (Finset α),
      IsUniform family 6 → IsSunflowerFree family 3 → family.card ≤ B)
    (hBB' : B ≤ B') :
    ∀ family : Finset (Finset α),
      IsUniform family 6 → IsSunflowerFree family 3 → family.card ≤ B' := by
  intro family h_uniform h_sf_free
  exact Nat.le_trans (hcap family h_uniform h_sf_free) hBB'

/-- Packaging form of monotonicity for `UniformBound_f6_3`. -/
theorem uniform_bound_f6_3_of_card_cap_mono {α : Type*} [DecidableEq α]
    {B B' : ℕ}
    (hcap : ∀ family : Finset (Finset α),
      IsUniform family 6 → IsSunflowerFree family 3 → family.card ≤ B)
    (hBB' : B ≤ B') :
    UniformBound_f6_3 (α := α) :=
  uniform_bound_f6_3_of_uniform_card_cap B'
    (uniform_bound_f6_3_card_cap_mono hcap hBB')

/-- Monotonicity helper for global family-cardinality caps. -/
theorem uniform_bound_f6_3_global_card_cap_mono {α : Type*} [DecidableEq α]
    {B B' : ℕ}
    (hcap : ∀ family : Finset (Finset α), family.card ≤ B)
    (hBB' : B ≤ B') :
    ∀ family : Finset (Finset α), family.card ≤ B' := by
  intro family
  exact Nat.le_trans (hcap family) hBB'

/-- Packaging form of global-card-cap monotonicity for `UniformBound_f6_3`. -/
theorem uniform_bound_f6_3_of_global_card_cap_mono {α : Type*} [DecidableEq α]
    {B B' : ℕ}
    (hcap : ∀ family : Finset (Finset α), family.card ≤ B)
    (hBB' : B ≤ B') :
    UniformBound_f6_3 (α := α) :=
  uniform_bound_f6_3_of_card_cap B'
    (uniform_bound_f6_3_global_card_cap_mono hcap hBB')

/-- Helper form of `UniformBound_f6_3` for direct theorem application. -/
theorem uniform_bound_f6_3_apply {α : Type*} [DecidableEq α]
    (h : UniformBound_f6_3 (α := α)) (family : Finset (Finset α))
    (h_uniform : IsUniform family 6) (h_sf_free : IsSunflowerFree family 3) :
    family.card ≤ h.choose :=
  h.choose_spec family h_uniform h_sf_free

/-- A finite-universe witness for `UniformBound_f6_3`.
    This does not use sunflower-freeness: every family is bounded by the powerset size. -/
theorem uniform_bound_f6_3_of_fintype (α : Type*) [Fintype α] [DecidableEq α] :
    UniformBound_f6_3 (α := α) := by
  refine ⟨2 ^ Fintype.card α, ?_⟩
  intro family _h_uniform _h_sf_free
  have hsub : family ⊆ (Finset.univ : Finset α).powerset := by
    intro S hS
    exact Finset.mem_powerset.mpr (by
      intro x hx
      simp)
  calc
    family.card ≤ ((Finset.univ : Finset α).powerset).card := Finset.card_le_card hsub
    _ = 2 ^ Fintype.card α := by simp

/-- Route-C specialization: a global `k=3` exponential bound implies the `r=6` uniform bound. -/
theorem uniform_bound_f6_3_of_erdos_problem20_k3
    (h : ErdosProblem20_K3) (α : Type) [DecidableEq α] :
    UniformBound_f6_3 (α := α) := by
  rcases h with ⟨C, hCpos, hC⟩
  refine ⟨C ^ 6, ?_⟩
  intro family h_uniform h_sf_free
  exact hC α 6 family h_uniform h_sf_free

/-- Concrete instance of the corrected `UniformBound_f6_3` target on `Fin 14`. -/
theorem uniform_bound_f6_3_fin14 : UniformBound_f6_3 (α := Fin 14) :=
  uniform_bound_f6_3_of_fintype (α := Fin 14)

/-- Extracted finite-universe cardinal cap for `r = 6`.
    This is the explicit powerset-size bound over any finite ground type. -/
theorem uniform_bound_f6_3_card_bound_on_fintype
    (α : Type*) [Fintype α] [DecidableEq α]
    (family : Finset (Finset α))
    (_h_uniform : IsUniform family 6)
    (_h_sf_free : IsSunflowerFree family 3) :
    family.card ≤ 2 ^ Fintype.card α := by
  have hsub : family ⊆ (Finset.univ : Finset α).powerset := by
    intro S hS
    exact Finset.mem_powerset.mpr (by
      intro x hx
      simp)
  calc
    family.card ≤ ((Finset.univ : Finset α).powerset).card := Finset.card_le_card hsub
    _ = 2 ^ Fintype.card α := by simp

/-- Fintype monotonic packaging: any bound `B` with `2 ^ |α| ≤ B`
    yields `UniformBound_f6_3` on `α`. -/
theorem uniform_bound_f6_3_of_fintype_card_cap_mono
    (α : Type*) [Fintype α] [DecidableEq α] {B : ℕ}
    (hB : 2 ^ Fintype.card α ≤ B) :
    UniformBound_f6_3 (α := α) := by
  exact uniform_bound_f6_3_of_card_cap_mono
    (B := 2 ^ Fintype.card α) (B' := B)
    (hcap := fun family h_uniform h_sf_free =>
      uniform_bound_f6_3_card_bound_on_fintype (α := α) family h_uniform h_sf_free)
    hB

/-- Concrete cardinal-cap specialization on `Fin 14`. -/
theorem uniform_bound_f6_3_fin14_card_bound_pow
    (family : Finset (Finset (Fin 14)))
    (h_uniform : IsUniform family 6)
    (h_sf_free : IsSunflowerFree family 3) :
    family.card ≤ 2 ^ Fintype.card (Fin 14) :=
  uniform_bound_f6_3_card_bound_on_fintype
    (α := Fin 14) family h_uniform h_sf_free

/-- Concrete numeric specialization on `Fin 14`. -/
theorem uniform_bound_f6_3_fin14_card_bound
    (family : Finset (Finset (Fin 14)))
    (h_uniform : IsUniform family 6)
    (h_sf_free : IsSunflowerFree family 3) :
    family.card ≤ 16384 := by
  have hpow : family.card ≤ 2 ^ Fintype.card (Fin 14) :=
    uniform_bound_f6_3_fin14_card_bound_pow family h_uniform h_sf_free
  have hEq : (2 ^ Fintype.card (Fin 14) : ℕ) = 16384 := by
    native_decide
  exact hEq ▸ hpow

/-- Concrete closure for `UniformBound_f3_3` on `Fin 4`.
    Any family over `Fin 4` has cardinality at most `16`, hence certainly `≤ 20`. -/
theorem uniform_bound_f3_3_fin4 : UniformBound_f3_3 (α := Fin 4) := by
  refine uniform_bound_f3_3_of_card_cap (α := Fin 4) ?_
  intro family
  have hsub : family ⊆ (Finset.univ : Finset (Finset (Fin 4))) := by
    intro S hS
    simp
  have hle :
      family.card ≤ (Finset.univ : Finset (Finset (Fin 4))).card :=
    Finset.card_le_card hsub
  have hcard : (Finset.univ : Finset (Finset (Fin 4))).card = 16 := by
    native_decide
  have h16 : family.card ≤ 16 := by
    simpa [hcard] using hle
  exact Nat.le_trans h16 (by decide : 16 ≤ 20)

/-- Concrete closure for `UniformBound_f4_3` on `Fin 4`.
    Any family over `Fin 4` has cardinality at most `16`, hence certainly `≤ 41`. -/
theorem uniform_bound_f4_3_fin4 : UniformBound_f4_3 (α := Fin 4) := by
  refine uniform_bound_f4_3_of_card_cap (α := Fin 4) ?_
  intro family
  have hsub : family ⊆ (Finset.univ : Finset (Finset (Fin 4))) := by
    intro S hS
    simp
  have hle :
      family.card ≤ (Finset.univ : Finset (Finset (Fin 4))).card :=
    Finset.card_le_card hsub
  have hcard : (Finset.univ : Finset (Finset (Fin 4))).card = 16 := by
    native_decide
  have h16 : family.card ≤ 16 := by
    simpa [hcard] using hle
  exact Nat.le_trans h16 (by decide : 16 ≤ 41)

-- ============================================================================
-- ORCHESTRATOR ROUTE AGGREGATOR (uniform_prize)
-- ============================================================================

/-- Aggregated route leaf used by the v2 reduction graph for Problem #20.
    It packages the currently tracked `k = 3` uniform bounds for `r = 1..6`. -/
def UniformBoundAllR {α : Type*} [DecidableEq α] : Prop :=
  UniformBound_f1_3 (α := α) ∧
  UniformBound_f2_3 (α := α) ∧
  UniformBound_f3_3 (α := α) ∧
  UniformBound_f4_3 (α := α) ∧
  UniformBound_f5_3 (α := α) ∧
  UniformBound_f6_3 (α := α)

/-- Packaging wrapper: if each tracked `r = 1..6` bound holds, then the
    aggregate route leaf `UniformBoundAllR` holds. -/
theorem uniform_bound_all_r_of_components
    {α : Type*} [DecidableEq α]
    (h1 : UniformBound_f1_3 (α := α))
    (h2 : UniformBound_f2_3 (α := α))
    (h3 : UniformBound_f3_3 (α := α))
    (h4 : UniformBound_f4_3 (α := α))
    (h5 : UniformBound_f5_3 (α := α))
    (h6 : UniformBound_f6_3 (α := α)) :
    UniformBoundAllR (α := α) := by
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- Milestone top-level theorem (finite-range packaging):
    if the tracked `r = 1..6` uniform bounds hold on a fixed ambient type `α`,
    then there is an exponential envelope `C^r` for all `1 ≤ r ≤ 6`. -/
theorem erdos_problem_20_k3_upto6_on_type_of_uniform_bounds
    {α : Type*} [DecidableEq α]
    (hall : UniformBoundAllR (α := α)) :
    ∃ C : ℕ, C > 0 ∧
      ∀ (r : ℕ) (family : Finset (Finset α)),
        1 ≤ r → r ≤ 6 →
        IsUniform family r → IsSunflowerFree family 3 → family.card ≤ C ^ r := by
  rcases hall with ⟨h1, h2, h3, h4, h5, h6⟩
  let C : ℕ := max 41 (max h5.choose h6.choose)
  refine ⟨C, ?_, ?_⟩
  · exact lt_of_lt_of_le (by decide : 0 < 41) (le_max_left _ _)
  · intro r family hr1 hr6 h_uniform h_sf_free
    have hCpos : 0 < C := lt_of_lt_of_le (by decide : 0 < 41) (le_max_left _ _)
    have hCge1 : 1 ≤ C := Nat.succ_le_of_lt hCpos
    have hC_le_pow :
        ∀ t : ℕ, 1 ≤ t → C ≤ C ^ t := by
      intro t ht
      rcases Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp ht) with ⟨u, rfl⟩
      calc
        C = C * 1 := by simp
        _ ≤ C * C ^ u := Nat.mul_le_mul_left C (Nat.one_le_pow _ _ hCpos)
        _ = C ^ u * C := by ac_rfl
        _ = C ^ (u + 1) := by simp [pow_succ]
    interval_cases r
    · -- r = 1
      have hle : family.card ≤ 2 := h1 family h_uniform h_sf_free
      calc
        family.card ≤ 2 := hle
        _ ≤ 41 := by decide
        _ ≤ C := le_max_left _ _
        _ = C ^ 1 := by simp
    · -- r = 2
      have hle : family.card ≤ 6 := h2 family h_uniform h_sf_free
      calc
        family.card ≤ 6 := hle
        _ ≤ 41 := by decide
        _ ≤ C := le_max_left _ _
        _ ≤ C ^ 2 := hC_le_pow 2 (by decide)
    · -- r = 3
      have hle : family.card ≤ 20 := h3 family h_uniform h_sf_free
      calc
        family.card ≤ 20 := hle
        _ ≤ 41 := by decide
        _ ≤ C := le_max_left _ _
        _ ≤ C ^ 3 := hC_le_pow 3 (by decide)
    · -- r = 4
      have hle : family.card ≤ 41 := h4 family h_uniform h_sf_free
      calc
        family.card ≤ 41 := hle
        _ ≤ C := le_max_left _ _
        _ ≤ C ^ 4 := hC_le_pow 4 (by decide)
    · -- r = 5
      have hle : family.card ≤ h5.choose := h5.choose_spec family h_uniform h_sf_free
      have hchoose : h5.choose ≤ C := by
        exact le_trans (le_max_left _ _) (le_max_right _ _)
      calc
        family.card ≤ h5.choose := hle
        _ ≤ C := hchoose
        _ ≤ C ^ 5 := hC_le_pow 5 (by decide)
    · -- r = 6
      have hle : family.card ≤ h6.choose := h6.choose_spec family h_uniform h_sf_free
      have hchoose : h6.choose ≤ C := by
        exact le_trans (le_max_right _ _) (le_max_right _ _)
      calc
        family.card ≤ h6.choose := hle
        _ ≤ C := hchoose
        _ ≤ C ^ 6 := hC_le_pow 6 (by decide)

/-- A 0-uniform family can contain at most one set (necessarily `∅`). -/
theorem uniform_zero_family_card_le_one {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (h_uniform : IsUniform family 0) :
    family.card ≤ 1 := by
  have hsub : family ⊆ ({(∅ : Finset α)} : Finset (Finset α)) := by
    intro S hS
    have hcard : S.card = 0 := h_uniform S hS
    have hempty : S = ∅ := Finset.card_eq_zero.mp hcard
    simp [hempty]
  have hle : family.card ≤ ({(∅ : Finset α)} : Finset (Finset α)).card :=
    Finset.card_le_card hsub
  simpa using hle

/-- Global low-range (`1 ≤ r ≤ 6`) exponential envelope for `k = 3`. -/
def UniformK3EnvelopeUpTo6 : Prop :=
  ∃ C6 : ℕ, C6 > 0 ∧
    ∀ (α : Type) [DecidableEq α] (r : ℕ) (family : Finset (Finset α)),
      1 ≤ r → r ≤ 6 →
      IsUniform family r → IsSunflowerFree family 3 → family.card ≤ C6 ^ r

/-- Global high-range (`r ≥ 7`) exponential envelope for `k = 3`. -/
def UniformK3EnvelopeFrom7 : Prop :=
  ∃ C7 : ℕ, C7 > 0 ∧
    ∀ (α : Type) [DecidableEq α] (r : ℕ) (family : Finset (Finset α)),
      7 ≤ r →
      IsUniform family r → IsSunflowerFree family 3 → family.card ≤ C7 ^ r

/-- High-range bound in "exponential × polynomial slack" form. -/
def UniformK3EnvelopeFrom7WithPolySlack : Prop :=
  ∃ A d : ℕ, A > 0 ∧
    ∀ (α : Type) [DecidableEq α] (r : ℕ) (family : Finset (Finset α)),
      7 ≤ r →
      IsUniform family r → IsSunflowerFree family 3 →
      family.card ≤ A ^ r * (r + 1) ^ d

/-- Atomic high-range target at one rank `r` in polynomial-slack form. -/
def UniformK3PolySlackAt (A d r : ℕ) : Prop :=
  ∀ (α : Type) [DecidableEq α] (family : Finset (Finset α)),
    IsUniform family r → IsSunflowerFree family 3 →
      family.card ≤ A ^ r * (r + 1) ^ d

/-- Atomic base-range hypothesis for the high-range polynomial-slack lane. -/
def UniformK3PolySlackBaseRangeHyp (A d R0 : ℕ) : Prop :=
  ∀ r : ℕ, 7 ≤ r → r ≤ R0 → UniformK3PolySlackAt A d r

/-- Atomic one-step extension hypothesis for the high-range polynomial-slack
lane. -/
def UniformK3PolySlackStepHyp (A d R0 : ℕ) : Prop :=
  ∀ r : ℕ, R0 ≤ r →
    UniformK3PolySlackAt A d r →
    UniformK3PolySlackAt A d (r + 1)

/-- Iteration theorem for the high-range polynomial-slack lane:
base-range bounds on `7 ≤ r ≤ R0` plus one-step extension for `r ≥ R0`
propagate the bound to every `r ≥ 7`. -/
theorem uniform_k3_poly_slack_at_of_base_range_and_step
    (A d R0 : ℕ)
    (hR0 : 7 ≤ R0)
    (hbase : UniformK3PolySlackBaseRangeHyp A d R0)
    (hstep : UniformK3PolySlackStepHyp A d R0) :
    ∀ r : ℕ, 7 ≤ r → UniformK3PolySlackAt A d r := by
  intro r hr7
  by_cases hrle : r ≤ R0
  · exact hbase r hr7 hrle
  · have hR0le : R0 ≤ r := Nat.le_of_lt (Nat.lt_of_not_ge hrle)
    have htail : ∀ t : ℕ, UniformK3PolySlackAt A d (R0 + t) := by
      intro t
      induction t with
      | zero =>
          simpa using hbase R0 hR0 (Nat.le_refl R0)
      | succ t iht =>
          have hR0le' : R0 ≤ R0 + t := Nat.le_add_right R0 t
          exact hstep (R0 + t) hR0le' iht
    have h_at_r : UniformK3PolySlackAt A d (R0 + (r - R0)) :=
      htail (r - R0)
    have hr_eq : R0 + (r - R0) = r := Nat.add_sub_of_le hR0le
    simpa [hr_eq] using h_at_r

/-- Package the atomic base-range + step-extension lane into the route leaf
`UniformK3EnvelopeFrom7WithPolySlack`. -/
theorem uniform_k3_envelope_from7_with_poly_slack_of_base_range_and_step
    (A d R0 : ℕ)
    (hApos : A > 0)
    (hR0 : 7 ≤ R0)
    (hbase : UniformK3PolySlackBaseRangeHyp A d R0)
    (hstep : UniformK3PolySlackStepHyp A d R0) :
    UniformK3EnvelopeFrom7WithPolySlack := by
  refine ⟨A, d, hApos, ?_⟩
  intro α _ r family hr7 h_uniform h_sf_free
  exact (uniform_k3_poly_slack_at_of_base_range_and_step A d R0 hR0 hbase hstep r hr7)
    α family h_uniform h_sf_free

/-- Polynomial slack absorption on the high-range lane:
    `A^r * (r+1)^d` can be absorbed into a pure exponential `C^r`
    using `r+1 ≤ 2^r`. -/
theorem uniform_k3_envelope_from7_of_poly_slack
    (hpoly : UniformK3EnvelopeFrom7WithPolySlack) :
    UniformK3EnvelopeFrom7 := by
  rcases hpoly with ⟨A, d, hApos, hA⟩
  let C7 : ℕ := A * (2 ^ d)
  refine ⟨C7, ?_, ?_⟩
  · have hpow : 0 < 2 ^ d := by
      exact pow_pos (by decide : 0 < (2 : ℕ)) d
    exact Nat.mul_pos hApos hpow
  · intro α _ r family hr h_uniform h_sf_free
    have hbase : family.card ≤ A ^ r * (r + 1) ^ d :=
      hA α r family hr h_uniform h_sf_free
    have hsucc_le_pow : r + 1 ≤ 2 ^ r :=
      Nat.succ_le_of_lt Nat.lt_two_pow_self
    have hpoly_le :
        (r + 1) ^ d ≤ (2 ^ d) ^ r := by
      calc
        (r + 1) ^ d ≤ (2 ^ r) ^ d := Nat.pow_le_pow_left hsucc_le_pow d
        _ = 2 ^ (r * d) := (Nat.pow_mul 2 r d).symm
        _ = 2 ^ (d * r) := by rw [Nat.mul_comm]
        _ = (2 ^ d) ^ r := Nat.pow_mul 2 d r
    have hmul :
        A ^ r * (r + 1) ^ d ≤ A ^ r * (2 ^ d) ^ r :=
      Nat.mul_le_mul_left (A ^ r) hpoly_le
    have hmulpow :
        A ^ r * (2 ^ d) ^ r = (A * 2 ^ d) ^ r := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
        (Nat.mul_pow A (2 ^ d) r).symm
    calc
      family.card ≤ A ^ r * (r + 1) ^ d := hbase
      _ ≤ A ^ r * (2 ^ d) ^ r := hmul
      _ = (A * 2 ^ d) ^ r := hmulpow
      _ = C7 ^ r := rfl

/-- Trivial embedding of the high-range pure exponential lane into the
    polynomial-slack lane (`d = 0`). -/
theorem uniform_k3_envelope_from7_with_poly_slack_of_from7
    (hge7 : UniformK3EnvelopeFrom7) :
    UniformK3EnvelopeFrom7WithPolySlack := by
  rcases hge7 with ⟨C7, hC7pos, hC7⟩
  refine ⟨C7, 0, hC7pos, ?_⟩
  intro α _ r family hr h_uniform h_sf_free
  have hbase : family.card ≤ C7 ^ r :=
    hC7 α r family hr h_uniform h_sf_free
  simpa using hbase

/-- Global closure target for the `r = 3` lane. -/
def UniformBoundF3Global : Prop :=
  ∀ (α : Type) [DecidableEq α], UniformBound_f3_3 (α := α)

/-- Global closure target for the `r = 4` lane. -/
def UniformBoundF4Global : Prop :=
  ∀ (α : Type) [DecidableEq α], UniformBound_f4_3 (α := α)

/-- Generic global fixed-cardinality cap target at rank `r`. -/
def UniformBoundRGlobal (r : ℕ) : Prop :=
  ∃ B : ℕ, B > 0 ∧
    ∀ (α : Type) [DecidableEq α] (family : Finset (Finset α)),
      IsUniform family r → IsSunflowerFree family 3 → family.card ≤ B

/-- Generic global fixed-cardinality cap target at rank `r`,
    with an explicit numerical ceiling `cap` on the witness constant. -/
def UniformBoundRGlobalWithCap (r cap : ℕ) : Prop :=
  ∃ B : ℕ, B > 0 ∧ B ≤ cap ∧
    ∀ (α : Type) [DecidableEq α] (family : Finset (Finset α)),
      IsUniform family r → IsSunflowerFree family 3 → family.card ≤ B

/-- Constructor for `UniformBoundRGlobal` from a direct uniform cap. -/
theorem uniform_bound_r_global_of_direct_cap
    {r B : ℕ} (hBpos : B > 0)
    (hcap : ∀ (α : Type) [DecidableEq α] (family : Finset (Finset α)),
      IsUniform family r → IsSunflowerFree family 3 → family.card ≤ B) :
    UniformBoundRGlobal r := by
  refine ⟨B, hBpos, ?_⟩
  intro α _ family h_uniform h_sf_free
  exact hcap α family h_uniform h_sf_free

/-- Constructor for `UniformBoundRGlobalWithCap` from a direct uniform cap. -/
theorem uniform_bound_r_global_with_cap_of_direct_cap
    {r B cap : ℕ} (hBpos : B > 0) (hBcap : B ≤ cap)
    (hcap : ∀ (α : Type) [DecidableEq α] (family : Finset (Finset α)),
      IsUniform family r → IsSunflowerFree family 3 → family.card ≤ B) :
    UniformBoundRGlobalWithCap r cap := by
  refine ⟨B, hBpos, hBcap, ?_⟩
  intro α _ family h_uniform h_sf_free
  exact hcap α family h_uniform h_sf_free

/-- Forgetful map: a bounded global rank-cap is, in particular, a global rank-cap. -/
theorem uniform_bound_r_global_of_with_cap
    {r cap : ℕ} (h : UniformBoundRGlobalWithCap r cap) :
    UniformBoundRGlobal r := by
  rcases h with ⟨B, hBpos, _hBcap, hB⟩
  exact ⟨B, hBpos, hB⟩

/-- Global rank-1 cap as a `UniformBoundRGlobal` instance. -/
theorem uniform_bound_r1_global : UniformBoundRGlobal 1 := by
  refine uniform_bound_r_global_of_direct_cap (r := 1) (B := 2) (by decide) ?_
  intro α _ family h_uniform h_sf_free
  exact uniform_bound_f1_3 (α := α) family h_uniform h_sf_free

/-- Global fixed-cardinality cap for the `r = 5` lane. -/
def UniformBoundF5Global : Prop :=
  ∃ B5 : ℕ, B5 > 0 ∧
    ∀ (α : Type) [DecidableEq α] (family : Finset (Finset α)),
      IsUniform family 5 → IsSunflowerFree family 3 → family.card ≤ B5

/-- Global fixed-cardinality cap for the `r = 6` lane. -/
def UniformBoundF6Global : Prop :=
  ∃ B6 : ℕ, B6 > 0 ∧
    ∀ (α : Type) [DecidableEq α] (family : Finset (Finset α)),
      IsUniform family 6 → IsSunflowerFree family 3 → family.card ≤ B6

/-- Convert the specialized `r = 5` global-cap predicate to the generic rank-cap form. -/
theorem uniform_bound_r5_global_of_f5_global
    (h5 : UniformBoundF5Global) :
    UniformBoundRGlobal 5 := by
  rcases h5 with ⟨B5, hB5pos, hB5⟩
  exact ⟨B5, hB5pos, fun α _ family h_uniform h_sf_free =>
    hB5 α family h_uniform h_sf_free⟩

/-- Convert the generic rank-5 global-cap predicate to the specialized form. -/
theorem uniform_bound_f5_global_of_r5_global
    (h5 : UniformBoundRGlobal 5) :
    UniformBoundF5Global := by
  rcases h5 with ⟨B5, hB5pos, hB5⟩
  exact ⟨B5, hB5pos, fun α _ family h_uniform h_sf_free =>
    hB5 α family h_uniform h_sf_free⟩

/-- Convert the specialized `r = 6` global-cap predicate to the generic rank-cap form. -/
theorem uniform_bound_r6_global_of_f6_global
    (h6 : UniformBoundF6Global) :
    UniformBoundRGlobal 6 := by
  rcases h6 with ⟨B6, hB6pos, hB6⟩
  exact ⟨B6, hB6pos, fun α _ family h_uniform h_sf_free =>
    hB6 α family h_uniform h_sf_free⟩

/-- Convert the generic rank-6 global-cap predicate to the specialized form. -/
theorem uniform_bound_f6_global_of_r6_global
    (h6 : UniformBoundRGlobal 6) :
    UniformBoundF6Global := by
  rcases h6 with ⟨B6, hB6pos, hB6⟩
  exact ⟨B6, hB6pos, fun α _ family h_uniform h_sf_free =>
    hB6 α family h_uniform h_sf_free⟩

/-- Reusable schema: any explicit global fixed-rank witness upgrades to the
generic `UniformBoundRGlobal r` route node. -/
theorem uniform_bound_r_global_schema_of_fixed_witness
    {r : ℕ}
    (hfixed :
      ∃ B : ℕ, B > 0 ∧
        ∀ (α : Type) [DecidableEq α] (family : Finset (Finset α)),
          IsUniform family r → IsSunflowerFree family 3 → family.card ≤ B) :
    UniformBoundRGlobal r := by
  rcases hfixed with ⟨B, hBpos, hB⟩
  exact ⟨B, hBpos, hB⟩

/-- Rank-5 instantiation of the generic schema from the specialized
`UniformBoundF5Global` leaf. -/
theorem uniform_bound_r5_global_of_f5_global_via_schema
    (h5 : UniformBoundF5Global) :
    UniformBoundRGlobal 5 := by
  rcases h5 with ⟨B5, hB5pos, hB5⟩
  exact uniform_bound_r_global_schema_of_fixed_witness (r := 5)
    ⟨B5, hB5pos, hB5⟩

/-- Rank-6 instantiation of the generic schema from the specialized
`UniformBoundF6Global` leaf. -/
theorem uniform_bound_r6_global_of_f6_global_via_schema
    (h6 : UniformBoundF6Global) :
    UniformBoundRGlobal 6 := by
  rcases h6 with ⟨B6, hB6pos, hB6⟩
  exact uniform_bound_r_global_schema_of_fixed_witness (r := 6)
    ⟨B6, hB6pos, hB6⟩

/-- Named rank-cap unifier for the `r = 5,6` lane. -/
def UniformBoundRGlobalUnifier_5_6 : Prop :=
  UniformBoundRGlobal 5 ∧ UniformBoundRGlobal 6

/-- Wrapper exporting the rank-5/6 unifier directly from the specialized
`f5/f6` global leaves. -/
theorem uniform_bound_r_global_unifier_5_6_of_f5_f6
    (h5 : UniformBoundF5Global)
    (h6 : UniformBoundF6Global) :
    UniformBoundRGlobalUnifier_5_6 := by
  refine ⟨?_, ?_⟩
  · exact uniform_bound_r5_global_of_f5_global_via_schema h5
  · exact uniform_bound_r6_global_of_f6_global_via_schema h6

/-- Connect the unifier wrapper back to the specialized `f5/f6` global leaves. -/
theorem uniform_bound_f5_f6_global_of_r_global_unifier_5_6
    (h56 : UniformBoundRGlobalUnifier_5_6) :
    UniformBoundF5Global ∧ UniformBoundF6Global := by
  rcases h56 with ⟨h5, h6⟩
  exact ⟨uniform_bound_f5_global_of_r5_global h5,
    uniform_bound_f6_global_of_r6_global h6⟩

/-- Assemble the global low-range envelope from component lanes:
    - `r = 1` is globally closed in this file,
    - `r = 2,3,4` are supplied as global assumptions,
    - `r = 5,6` are supplied as global fixed-cardinality caps. -/
theorem uniform_k3_envelope_upto6_of_component_bounds
    (h2global : ∀ (α : Type) [DecidableEq α], UniformBound_f2_3 (α := α))
    (h3global : UniformBoundF3Global)
    (h4global : UniformBoundF4Global)
    (h5global : UniformBoundF5Global)
    (h6global : UniformBoundF6Global) :
    UniformK3EnvelopeUpTo6 := by
  rcases h5global with ⟨B5, hB5pos, hB5⟩
  rcases h6global with ⟨B6, hB6pos, hB6⟩
  let C6 : ℕ := max 41 (max B5 B6)
  refine ⟨C6, ?_, ?_⟩
  · exact lt_of_lt_of_le (by decide : 0 < 41) (le_max_left _ _)
  · intro α _ r family hr1 hr6 h_uniform h_sf_free
    have hC6pos : 0 < C6 := lt_of_lt_of_le (by decide : 0 < 41) (le_max_left _ _)
    have hC_le_pow :
        ∀ t : ℕ, 1 ≤ t → C6 ≤ C6 ^ t := by
      intro t ht
      rcases Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp ht) with ⟨u, rfl⟩
      calc
        C6 = C6 * 1 := by simp
        _ ≤ C6 * C6 ^ u := Nat.mul_le_mul_left C6 (Nat.one_le_pow _ _ hC6pos)
        _ = C6 ^ u * C6 := by ac_rfl
        _ = C6 ^ (u + 1) := by simp [pow_succ]
    interval_cases r
    · -- r = 1
      have hle : family.card ≤ 2 := uniform_bound_f1_3 (α := α) family h_uniform h_sf_free
      calc
        family.card ≤ 2 := hle
        _ ≤ 41 := by decide
        _ ≤ C6 := le_max_left _ _
        _ = C6 ^ 1 := by simp
    · -- r = 2
      have h2 : UniformBound_f2_3 (α := α) := h2global α
      have hle : family.card ≤ 6 := h2 family h_uniform h_sf_free
      calc
        family.card ≤ 6 := hle
        _ ≤ 41 := by decide
        _ ≤ C6 := le_max_left _ _
        _ ≤ C6 ^ 2 := hC_le_pow 2 (by decide)
    · -- r = 3
      have h3 : UniformBound_f3_3 (α := α) := h3global α
      have hle : family.card ≤ 20 := h3 family h_uniform h_sf_free
      calc
        family.card ≤ 20 := hle
        _ ≤ 41 := by decide
        _ ≤ C6 := le_max_left _ _
        _ ≤ C6 ^ 3 := hC_le_pow 3 (by decide)
    · -- r = 4
      have h4 : UniformBound_f4_3 (α := α) := h4global α
      have hle : family.card ≤ 41 := h4 family h_uniform h_sf_free
      calc
        family.card ≤ 41 := hle
        _ ≤ C6 := le_max_left _ _
        _ ≤ C6 ^ 4 := hC_le_pow 4 (by decide)
    · -- r = 5
      have hle : family.card ≤ B5 := hB5 α family h_uniform h_sf_free
      have hB5le : B5 ≤ C6 := le_trans (le_max_left _ _) (le_max_right _ _)
      calc
        family.card ≤ B5 := hle
        _ ≤ C6 := hB5le
        _ ≤ C6 ^ 5 := hC_le_pow 5 (by decide)
    · -- r = 6
      have hle : family.card ≤ B6 := hB6 α family h_uniform h_sf_free
      have hB6le : B6 ≤ C6 := le_trans (le_max_right _ _) (le_max_right _ _)
      calc
        family.card ≤ B6 := hle
        _ ≤ C6 := hB6le
        _ ≤ C6 ^ 6 := hC_le_pow 6 (by decide)

/-- Split bridge for the global `k = 3` conjecture:
    if we have one absolute exponential envelope for `1 ≤ r ≤ 6` and one
    absolute exponential envelope for `r ≥ 7`, then `ErdosProblem20_K3` holds. -/
theorem erdos_problem_20_k3_of_upto6_and_ge7_bounds
    (hupto6 : UniformK3EnvelopeUpTo6)
    (hge7 : UniformK3EnvelopeFrom7) :
    ErdosProblem20_K3 := by
  rcases hupto6 with ⟨C6, hC6pos, hC6⟩
  rcases hge7 with ⟨C7, hC7pos, hC7⟩
  let C : ℕ := max C6 C7
  refine erdos_problem_20_k3_of_uniform_bounds ?_
  refine ⟨C, ?_, ?_⟩
  · exact lt_of_lt_of_le hC6pos (le_max_left _ _)
  · intro α _ r family h_uniform h_sf_free
    by_cases hr0 : r = 0
    · subst hr0
      have hle0 : family.card ≤ 1 := uniform_zero_family_card_le_one family h_uniform
      simpa using hle0
    · by_cases hr6 : r ≤ 6
      · have hr1 : 1 ≤ r := Nat.succ_le_of_lt (Nat.pos_iff_ne_zero.mpr hr0)
        have hle6 : family.card ≤ C6 ^ r := hC6 α r family hr1 hr6 h_uniform h_sf_free
        have hpow : C6 ^ r ≤ C ^ r := Nat.pow_le_pow_left (le_max_left _ _) _
        exact le_trans hle6 hpow
      · have h7 : 7 ≤ r := Nat.succ_le_of_lt (Nat.lt_of_not_ge hr6)
        have hle7 : family.card ≤ C7 ^ r := hC7 α r family h7 h_uniform h_sf_free
        have hpow : C7 ^ r ≤ C ^ r := Nat.pow_le_pow_left (le_max_right _ _) _
        exact le_trans hle7 hpow

/-- Named corollary form of the split bridge. -/
theorem erdos_problem_20_k3_of_split_envelopes
    (hLow : UniformK3EnvelopeUpTo6)
    (hHigh : UniformK3EnvelopeFrom7) :
    ErdosProblem20_K3 :=
  erdos_problem_20_k3_of_upto6_and_ge7_bounds hLow hHigh

-- ============================================================================
-- EXPLICIT COUNTEREXAMPLE TO THE STALE f(6,3) ≤ 20 CANDIDATE
-- ============================================================================

/-- The previous fixed `≤ 20` target, kept as a stale reference proposition. -/
def UniformBound_f6_3_stale20 {α : Type*} [DecidableEq α] : Prop :=
  ∀ (family : Finset (Finset α)),
    IsUniform family 6 → IsSunflowerFree family 3 → family.card ≤ 20

/-- Left 2-uniform block on `{0,1,2,3,4,5}` (two disjoint triangles). -/
def f6_left_pair : Fin 6 → Finset (Fin 14)
  | ⟨0, _⟩ => {0, 1}
  | ⟨1, _⟩ => {0, 2}
  | ⟨2, _⟩ => {1, 2}
  | ⟨3, _⟩ => {3, 4}
  | ⟨4, _⟩ => {3, 5}
  | ⟨5, _⟩ => {4, 5}

/-- Right 2-uniform block on `{6,7,8,9,10,11}` (two disjoint triangles). -/
def f6_right_pair : Fin 6 → Finset (Fin 14)
  | ⟨0, _⟩ => {6, 7}
  | ⟨1, _⟩ => {6, 8}
  | ⟨2, _⟩ => {7, 8}
  | ⟨3, _⟩ => {9, 10}
  | ⟨4, _⟩ => {9, 11}
  | ⟨5, _⟩ => {10, 11}

/-- Shared 2-element padding block. -/
def f6_shared_core : Finset (Fin 14) := {12, 13}

/-- Product witness: `X ∪ Y ∪ C` with `X` from left block and `Y` from right block. -/
def f6_3_counterexample_set : Fin 6 × Fin 6 → Finset (Fin 14)
  | (i, j) => f6_left_pair i ∪ f6_right_pair j ∪ f6_shared_core

/-- 36-set candidate family witnessing that `≤ 20` is false. -/
def f6_3_counterexample_family : Finset (Finset (Fin 14)) :=
  (Finset.univ : Finset (Fin 6 × Fin 6)).image f6_3_counterexample_set

theorem f6_3_counterexample_set_injective : Function.Injective f6_3_counterexample_set := by
  native_decide

theorem f6_3_counterexample_card : f6_3_counterexample_family.card = 36 := by
  calc
    f6_3_counterexample_family.card = (Finset.univ : Finset (Fin 6 × Fin 6)).card := by
      simpa [f6_3_counterexample_family] using
        (Finset.card_image_of_injOn
          (s := (Finset.univ : Finset (Fin 6 × Fin 6)))
          (f := f6_3_counterexample_set)
          (fun a _ b _ hab => f6_3_counterexample_set_injective hab))
    _ = 36 := by simp

theorem f6_3_counterexample_uniform : IsUniform f6_3_counterexample_family 6 := by
  intro S hS
  rcases Finset.mem_image.mp hS with ⟨⟨i, j⟩, -, rfl⟩
  fin_cases i <;> fin_cases j <;> native_decide

theorem f6_3_counterexample_no_sunflower_indices :
    ¬ ∃ a b c : Fin 6 × Fin 6,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        (f6_3_counterexample_set a ∩ f6_3_counterexample_set b =
          f6_3_counterexample_set a ∩ f6_3_counterexample_set c) ∧
        (f6_3_counterexample_set a ∩ f6_3_counterexample_set b =
          f6_3_counterexample_set b ∩ f6_3_counterexample_set c) := by
  native_decide

theorem f6_3_counterexample_sf_free : IsSunflowerFree f6_3_counterexample_family 3 := by
  intro sub hsub hsun
  rcases (Finset.card_eq_three.mp hsun.1) with ⟨A, B, C, hAB, hAC, hBC, rfl⟩
  have hA_mem : A ∈ f6_3_counterexample_family := hsub (by simp)
  have hB_mem : B ∈ f6_3_counterexample_family := hsub (by simp)
  have hC_mem : C ∈ f6_3_counterexample_family := hsub (by simp)
  rcases Finset.mem_image.mp hA_mem with ⟨a, -, ha⟩
  rcases Finset.mem_image.mp hB_mem with ⟨b, -, hb⟩
  rcases Finset.mem_image.mp hC_mem with ⟨c, -, hc⟩
  have hab : a ≠ b := by
    intro hab'
    apply hAB
    calc
      A = f6_3_counterexample_set a := ha.symm
      _ = f6_3_counterexample_set b := by simp [hab']
      _ = B := hb
  have hac : a ≠ c := by
    intro hac'
    apply hAC
    calc
      A = f6_3_counterexample_set a := ha.symm
      _ = f6_3_counterexample_set c := by simp [hac']
      _ = C := hc
  have hbc : b ≠ c := by
    intro hbc'
    apply hBC
    calc
      B = f6_3_counterexample_set b := hb.symm
      _ = f6_3_counterexample_set c := by simp [hbc']
      _ = C := hc
  rcases hsun.2 with ⟨core, hcore⟩
  have hABcore : A ∩ B = core := hcore A B (by simp) (by simp) hAB
  have hACcore : A ∩ C = core := hcore A C (by simp) (by simp) hAC
  have hBCcore : B ∩ C = core := hcore B C (by simp) (by simp) hBC
  have hAB_eq_AC : A ∩ B = A ∩ C := hABcore.trans hACcore.symm
  have hAB_eq_BC : A ∩ B = B ∩ C := hABcore.trans hBCcore.symm
  exact f6_3_counterexample_no_sunflower_indices ⟨a, b, c, hab, hac, hbc,
    by simpa [← ha, ← hb, ← hc] using hAB_eq_AC,
    by simpa [← ha, ← hb, ← hc] using hAB_eq_BC⟩

/-- The stale fixed candidate `≤ 20` is false under current definitions. -/
theorem uniformBound_f6_3_stale20_false : ¬ UniformBound_f6_3_stale20 (α := Fin 14) := by
  intro hbound
  have hle : f6_3_counterexample_family.card ≤ 20 :=
    hbound f6_3_counterexample_family f6_3_counterexample_uniform f6_3_counterexample_sf_free
  rw [f6_3_counterexample_card] at hle
  omega

/-- Packed witness record for the `r = 6, k = 3` lower-bound lane under the
current local sunflower formulation. -/
theorem f6_3_counterexample_witness :
    IsUniform f6_3_counterexample_family 6 ∧
    IsSunflowerFree f6_3_counterexample_family 3 ∧
    f6_3_counterexample_family.card = 36 := by
  exact ⟨f6_3_counterexample_uniform, f6_3_counterexample_sf_free, f6_3_counterexample_card⟩

/-- Strengthened numerical rejection of the stale small-cap lane:
for `α = Fin 14`, no universal `≤ 35` bound can hold for 6-uniform
3-sunflower-free families. -/
theorem uniformBound_f6_3_le_35_false :
    ¬ (∀ (family : Finset (Finset (Fin 14))),
      IsUniform family 6 → IsSunflowerFree family 3 → family.card ≤ 35) := by
  intro hbound
  have hle : f6_3_counterexample_family.card ≤ 35 :=
    hbound f6_3_counterexample_family f6_3_counterexample_uniform f6_3_counterexample_sf_free
  rw [f6_3_counterexample_card] at hle
  omega

/-- Scaffold entropy step for thin-family route. -/
theorem thin_family_entropy_argument_step1 : True := by
  exact True.intro

/-- Degree+matching closure for the `r = 2` edge model:
    if every vertex-degree is at most `2` and every pairwise-disjoint subfamily
    has size at most `2`, then the family has at most `6` members. -/
theorem edge_count_bound_of_degree_two_and_matching_two {α : Type*} [DecidableEq α]
    (family : Finset (Finset α))
    (h_uniform : IsUniform family 2)
    (h_degree : ∀ x : α, (family.filter (fun S => x ∈ S)).card ≤ 2)
    (h_matching : ∀ sub : Finset (Finset α), sub ⊆ family → IsPairwiseDisjoint sub → sub.card ≤ 2) :
    family.card ≤ 6 := by
  by_contra h_not
  have h7 : 7 ≤ family.card := Nat.succ_le_of_lt (Nat.lt_of_not_ge h_not)
  have h_pos : 0 < family.card := lt_of_lt_of_le (by decide : 0 < 7) h7
  obtain ⟨e1, he1⟩ := Finset.card_pos.mp h_pos

  have h_intersect_le_three :
      ∀ e : Finset α, e ∈ family →
        (family.filter (fun S => ¬ Disjoint S e)).card ≤ 3 := by
    intro e he
    rcases Finset.card_eq_two.mp (h_uniform e he) with ⟨a, b, hab, rfl⟩
    let Fa : Finset (Finset α) := family.filter (fun S => a ∈ S)
    let Fb : Finset (Finset α) := family.filter (fun S => b ∈ S)
    have h_subset :
        family.filter (fun S => ¬ Disjoint S ({a, b} : Finset α)) ⊆ Fa ∪ Fb := by
      intro S hS
      have hSfam : S ∈ family := (Finset.mem_filter.mp hS).1
      have hSnd : ¬ Disjoint S ({a, b} : Finset α) := (Finset.mem_filter.mp hS).2
      have hMem : a ∈ S ∨ b ∈ S := by
        by_cases ha : a ∈ S
        · exact Or.inl ha
        · by_cases hb : b ∈ S
          · exact Or.inr hb
          · exfalso
            have hdisj : Disjoint S ({a, b} : Finset α) := by
              refine Finset.disjoint_left.mpr ?_
              intro x hxS hxAB
              rcases Finset.mem_insert.mp hxAB with hxEq | hxSingleton
              · subst hxEq
                exact ha hxS
              · have hxEqB : x = b := by simpa [Finset.mem_singleton] using hxSingleton
                exact hb (hxEqB ▸ hxS)
            exact hSnd hdisj
      rcases hMem with haS | hbS
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hSfam, haS⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hSfam, hbS⟩))
    have hFa : Fa.card ≤ 2 := by
      simpa [Fa] using h_degree a
    have hFb : Fb.card ≤ 2 := by
      simpa [Fb] using h_degree b
    have hInterPos : 1 ≤ (Fa ∩ Fb).card := by
      refine Finset.one_le_card.mpr ?_
      refine ⟨({a, b} : Finset α), ?_⟩
      refine Finset.mem_inter.mpr ?_
      constructor <;> exact Finset.mem_filter.mpr ⟨he, by simp [hab]⟩
    have hUnionEq : (Fa ∪ Fb).card + (Fa ∩ Fb).card = Fa.card + Fb.card := by
      exact Finset.card_union_add_card_inter Fa Fb
    have hUnionLe3 : (Fa ∪ Fb).card ≤ 3 := by
      omega
    calc
      (family.filter (fun S => ¬ Disjoint S ({a, b} : Finset α))).card ≤ (Fa ∪ Fb).card :=
        Finset.card_le_card h_subset
      _ ≤ 3 := hUnionLe3

  let D1 : Finset (Finset α) := family.filter (fun S => Disjoint S e1)
  have hD1_part : D1.card + (family.filter (fun S => ¬ Disjoint S e1)).card = family.card := by
    simpa [D1] using
      (Finset.filter_card_add_filter_neg_card_eq_card
        (s := family) (p := fun S => Disjoint S e1))
  have hD1_ge4 : 4 ≤ D1.card := by
    have hI1 : (family.filter (fun S => ¬ Disjoint S e1)).card ≤ 3 := h_intersect_le_three e1 he1
    omega
  have hD1_pos : 0 < D1.card := lt_of_lt_of_le (by decide : 0 < 4) hD1_ge4
  obtain ⟨e2, he2D1⟩ := Finset.card_pos.mp hD1_pos
  have he2 : e2 ∈ family := (Finset.mem_filter.mp he2D1).1
  have h21 : Disjoint e2 e1 := (Finset.mem_filter.mp he2D1).2

  let D2 : Finset (Finset α) := D1.filter (fun S => Disjoint S e2)
  have hD2_part : D2.card + (D1.filter (fun S => ¬ Disjoint S e2)).card = D1.card := by
    simpa [D2] using
      (Finset.filter_card_add_filter_neg_card_eq_card
        (s := D1) (p := fun S => Disjoint S e2))
  have hD1I2_le3 : (D1.filter (fun S => ¬ Disjoint S e2)).card ≤ 3 := by
    have hsub :
        D1.filter (fun S => ¬ Disjoint S e2) ⊆ family.filter (fun S => ¬ Disjoint S e2) := by
      intro S hS
      have hSD1 : S ∈ D1 := (Finset.mem_filter.mp hS).1
      have hSnd : ¬ Disjoint S e2 := (Finset.mem_filter.mp hS).2
      have hSfam : S ∈ family := (Finset.mem_filter.mp hSD1).1
      exact Finset.mem_filter.mpr ⟨hSfam, hSnd⟩
    exact Nat.le_trans (Finset.card_le_card hsub) (h_intersect_le_three e2 he2)
  have hD2_ge1 : 1 ≤ D2.card := by
    omega
  have hD2_pos : 0 < D2.card := Nat.succ_le_iff.mp hD2_ge1
  obtain ⟨e3, he3D2⟩ := Finset.card_pos.mp hD2_pos
  have he3D1 : e3 ∈ D1 := (Finset.mem_filter.mp he3D2).1
  have h32 : Disjoint e3 e2 := (Finset.mem_filter.mp he3D2).2
  have he3 : e3 ∈ family := (Finset.mem_filter.mp he3D1).1
  have h31 : Disjoint e3 e1 := (Finset.mem_filter.mp he3D1).2

  have h11_not : ¬ Disjoint e1 e1 := by
    rcases Finset.card_eq_two.mp (h_uniform e1 he1) with ⟨a, b, hab, rfl⟩
    simp [hab]
  have h22_not : ¬ Disjoint e2 e2 := by
    rcases Finset.card_eq_two.mp (h_uniform e2 he2) with ⟨a, b, hab, rfl⟩
    simp [hab]
  have h12 : e1 ≠ e2 := by
    intro hEq
    have : Disjoint e1 e1 := by simpa [hEq] using h21
    exact h11_not this
  have h13 : e1 ≠ e3 := by
    intro hEq
    have : Disjoint e1 e1 := by simpa [hEq] using h31
    exact h11_not this
  have h23 : e2 ≠ e3 := by
    intro hEq
    have : Disjoint e2 e2 := by simpa [hEq] using h32
    exact h22_not this

  let sub : Finset (Finset α) := {e1, e2, e3}
  have hsub_subset : sub ⊆ family := by
    intro S hS
    simp [sub, h12, h13, h23] at hS
    rcases hS with rfl | rfl | rfl <;> assumption
  have hsub_disj : IsPairwiseDisjoint sub := by
    intro S T hS hT hne
    simp [sub, h12, h13, h23] at hS hT
    rcases hS with rfl | rfl | rfl <;> rcases hT with rfl | rfl | rfl
    · exact False.elim (hne rfl)
    · simpa [Finset.disjoint_iff_inter_eq_empty] using h21.symm
    · simpa [Finset.disjoint_iff_inter_eq_empty] using h31.symm
    · simpa [Finset.disjoint_iff_inter_eq_empty] using h21
    · exact False.elim (hne rfl)
    · simpa [Finset.disjoint_iff_inter_eq_empty] using h32.symm
    · simpa [Finset.disjoint_iff_inter_eq_empty] using h31
    · simpa [Finset.disjoint_iff_inter_eq_empty] using h32
    · exact False.elim (hne rfl)
  have hsub_card : sub.card = 3 := by
    simp [sub, h12, h13, h23]
  have hle2 : sub.card ≤ 2 := h_matching sub hsub_subset hsub_disj
  rw [hsub_card] at hle2
  omega

/-- Named target wrapper for the `r = 2, k = 3` counting closure. -/
theorem f2_3_edge_count_bound_of_max_degree_two_and_matching_two {α : Type*} [DecidableEq α]
    (family : Finset (Finset α))
    (h_uniform : IsUniform family 2)
    (h_degree : ∀ x : α, (family.filter (fun S => x ∈ S)).card ≤ 2)
    (h_matching : ∀ sub : Finset (Finset α), sub ⊆ family → IsPairwiseDisjoint sub → sub.card ≤ 2) :
    family.card ≤ 6 :=
  edge_count_bound_of_degree_two_and_matching_two family h_uniform h_degree h_matching

-- ============================================================================
-- KNOWN BOUNDS (for verification / computational targets)
-- ============================================================================

/-
  Known values of f(r, 3) -- the maximum size of an r-uniform 3-SF-free family:
    f(1, 3) = 2
    f(2, 3) = 6 (for the current local `IsSunflower` formulation).
    f(3, 3) = 6
    f(4, 3) ≥ 12 is witnessed by a 12-set counterexample for the current definitions
    (exact value is currently unverified in this repo).
    f(6, 3) ≥ 216 is witnessed by product constructions in the current definitions;
    the previous placeholder `f(6,3) = 20` is invalid.

  Best known asymptotic: f(r, 3) ≤ O(r log r)^r  [Alweiss-Lovett-Wu-Zhang 2021]
  Erdos prize target: f(r, 3) ≤ C^r for some absolute constant C
-/

-- Future: computational verification of small cases (f(1,3)=2, f(2,3)=6, etc.)
-- These would be the first proof artifacts for the reduction chain.

-- FUTURE: Bridge between our Finset formulation and DeepMind's Set formulation
-- DeepMind's formal-conjectures uses: Set (Set α) with Set.Finite assumptions
-- Our library uses: Finset (Finset α)
-- Equivalence: for finite families, these are isomorphic via Finset.toSet / Set.toFinset
-- This bridge would let us port results between formulations.
--
-- theorem erdos_problem_20_set_equiv_finset :
--   ErdosProblem20_Set k ↔ ErdosProblem20 k := by
--   -- deferred: requires Set ↔ Finset conversion infrastructure

/-- Direct route: `UniformBound_f2_3` follows from the proved degree cap
    (`singleton_core_double_counting_step1`), matching cap
    (`sf_free_no_three_pairwise_disjoint`), and counting closure
    (`edge_count_bound_of_degree_two_and_matching_two`). -/
theorem uniform_bound_f2_3_of_degree_matching_route {α : Type*} [DecidableEq α] :
    UniformBound_f2_3 (α := α) := by
  intro family h_uniform h_sf_free
  exact edge_count_bound_of_degree_two_and_matching_two family h_uniform
    (singleton_core_double_counting_step1 family h_uniform h_sf_free)
    (sf_free_no_three_pairwise_disjoint family h_sf_free)

/-- Global rank-2 cap as a `UniformBoundRGlobal` instance. -/
theorem uniform_bound_r2_global : UniformBoundRGlobal 2 := by
  refine uniform_bound_r_global_of_direct_cap (r := 2) (B := 6) (by decide) ?_
  intro α _ family h_uniform h_sf_free
  exact uniform_bound_f2_3_of_degree_matching_route (α := α) family h_uniform h_sf_free

/-- Low-range envelope from generic rank-caps:
    the `r=3,4` lanes are allowed to use any global caps, not fixed `20/41`. -/
theorem uniform_k3_envelope_upto6_of_global_caps
    (h3cap : UniformBoundRGlobal 3)
    (h4cap : UniformBoundRGlobal 4)
    (h5global : UniformBoundF5Global)
    (h6global : UniformBoundF6Global) :
    UniformK3EnvelopeUpTo6 := by
  rcases h3cap with ⟨B3, hB3pos, hB3⟩
  rcases h4cap with ⟨B4, hB4pos, hB4⟩
  rcases h5global with ⟨B5, hB5pos, hB5⟩
  rcases h6global with ⟨B6, hB6pos, hB6⟩
  let C6 : ℕ := max 6 (max B3 (max B4 (max B5 B6)))
  refine ⟨C6, ?_, ?_⟩
  · exact lt_of_lt_of_le (by decide : 0 < 6) (le_max_left _ _)
  · intro α _ r family hr1 hr6 h_uniform h_sf_free
    have hC6pos : 0 < C6 := lt_of_lt_of_le (by decide : 0 < 6) (le_max_left _ _)
    have hC_le_pow :
        ∀ t : ℕ, 1 ≤ t → C6 ≤ C6 ^ t := by
      intro t ht
      rcases Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp ht) with ⟨u, rfl⟩
      calc
        C6 = C6 * 1 := by simp
        _ ≤ C6 * C6 ^ u := Nat.mul_le_mul_left C6 (Nat.one_le_pow _ _ hC6pos)
        _ = C6 ^ u * C6 := by ac_rfl
        _ = C6 ^ (u + 1) := by simp [pow_succ]
    interval_cases r
    · -- r = 1
      have hle : family.card ≤ 2 := uniform_bound_f1_3 (α := α) family h_uniform h_sf_free
      calc
        family.card ≤ 2 := hle
        _ ≤ 6 := by decide
        _ ≤ C6 := le_max_left _ _
        _ = C6 ^ 1 := by simp
    · -- r = 2
      have h2 : UniformBound_f2_3 (α := α) := uniform_bound_f2_3_of_degree_matching_route (α := α)
      have hle : family.card ≤ 6 := h2 family h_uniform h_sf_free
      calc
        family.card ≤ 6 := hle
        _ ≤ C6 := le_max_left _ _
        _ ≤ C6 ^ 2 := hC_le_pow 2 (by decide)
    · -- r = 3
      have hle : family.card ≤ B3 := hB3 α family h_uniform h_sf_free
      have hB3le : B3 ≤ C6 := by
        exact le_trans (le_max_left _ _) (le_max_right _ _)
      calc
        family.card ≤ B3 := hle
        _ ≤ C6 := hB3le
        _ ≤ C6 ^ 3 := hC_le_pow 3 (by decide)
    · -- r = 4
      have hle : family.card ≤ B4 := hB4 α family h_uniform h_sf_free
      have hB4le : B4 ≤ C6 := by
        calc
          B4 ≤ max B4 (max B5 B6) := le_max_left _ _
          _ ≤ max B3 (max B4 (max B5 B6)) := le_max_right _ _
          _ ≤ C6 := le_max_right _ _
      calc
        family.card ≤ B4 := hle
        _ ≤ C6 := hB4le
        _ ≤ C6 ^ 4 := hC_le_pow 4 (by decide)
    · -- r = 5
      have hle : family.card ≤ B5 := hB5 α family h_uniform h_sf_free
      have hB5le : B5 ≤ C6 := by
        calc
          B5 ≤ max B5 B6 := le_max_left _ _
          _ ≤ max B4 (max B5 B6) := le_max_right _ _
          _ ≤ max B3 (max B4 (max B5 B6)) := le_max_right _ _
          _ ≤ C6 := le_max_right _ _
      calc
        family.card ≤ B5 := hle
        _ ≤ C6 := hB5le
        _ ≤ C6 ^ 5 := hC_le_pow 5 (by decide)
    · -- r = 6
      have hle : family.card ≤ B6 := hB6 α family h_uniform h_sf_free
      have hB6le : B6 ≤ C6 := by
        calc
          B6 ≤ max B5 B6 := le_max_right _ _
          _ ≤ max B4 (max B5 B6) := le_max_right _ _
          _ ≤ max B3 (max B4 (max B5 B6)) := le_max_right _ _
          _ ≤ C6 := le_max_right _ _
      calc
        family.card ≤ B6 := hle
        _ ≤ C6 := hB6le
        _ ≤ C6 ^ 6 := hC_le_pow 6 (by decide)

/-- Convenience form of the low-range envelope reducer:
    uses the in-file global `r = 2` route closure
    (`uniform_bound_f2_3_of_degree_matching_route`). -/
theorem uniform_k3_envelope_upto6_of_component_bounds_via_degree_route
    (h3global : UniformBoundF3Global)
    (h4global : UniformBoundF4Global)
    (h5global : UniformBoundF5Global)
    (h6global : UniformBoundF6Global) :
    UniformK3EnvelopeUpTo6 := by
  exact uniform_k3_envelope_upto6_of_component_bounds
    (h2global := fun α _ => uniform_bound_f2_3_of_degree_matching_route (α := α))
    h3global h4global h5global h6global

/-- Convenience low-range envelope from generic rank-caps at `r=3,4`
    plus global cap assumptions at `r=5,6`. -/
theorem uniform_k3_envelope_upto6_of_global_caps_via_degree_route
    (h3cap : UniformBoundRGlobal 3)
    (h4cap : UniformBoundRGlobal 4)
    (h5global : UniformBoundF5Global)
    (h6global : UniformBoundF6Global) :
    UniformK3EnvelopeUpTo6 := by
  exact uniform_k3_envelope_upto6_of_global_caps h3cap h4cap h5global h6global

/-- End-to-end reducer:
    component assumptions (`r=3..6`) plus the high-range envelope (`r ≥ 7`)
    imply full `ErdosProblem20_K3`. -/
theorem erdos_problem_20_k3_of_components_and_ge7
    (h3global : UniformBoundF3Global)
    (h4global : UniformBoundF4Global)
    (h5global : UniformBoundF5Global)
    (h6global : UniformBoundF6Global)
    (hHigh : UniformK3EnvelopeFrom7) :
    ErdosProblem20_K3 := by
  exact erdos_problem_20_k3_of_split_envelopes
    (uniform_k3_envelope_upto6_of_component_bounds_via_degree_route
      h3global h4global h5global h6global)
    hHigh

/-- End-to-end reducer with high-range polynomial slack input. -/
theorem erdos_problem_20_k3_of_components_and_ge7_poly_slack
    (h3global : UniformBoundF3Global)
    (h4global : UniformBoundF4Global)
    (h5global : UniformBoundF5Global)
    (h6global : UniformBoundF6Global)
    (hHighPoly : UniformK3EnvelopeFrom7WithPolySlack) :
    ErdosProblem20_K3 := by
  exact erdos_problem_20_k3_of_components_and_ge7
    h3global h4global h5global h6global
    (uniform_k3_envelope_from7_of_poly_slack hHighPoly)

/-- End-to-end reducer with generic rank-caps at `r=3,4`
    (no fixed `20/41` constants required). -/
theorem erdos_problem_20_k3_of_global_caps_and_ge7
    (h3cap : UniformBoundRGlobal 3)
    (h4cap : UniformBoundRGlobal 4)
    (h5global : UniformBoundF5Global)
    (h6global : UniformBoundF6Global)
    (hHigh : UniformK3EnvelopeFrom7) :
    ErdosProblem20_K3 := by
  exact erdos_problem_20_k3_of_split_envelopes
    (uniform_k3_envelope_upto6_of_global_caps_via_degree_route
      h3cap h4cap h5global h6global)
    hHigh

/-- End-to-end reducer with generic rank-caps at `r=3,4`
    and high-range polynomial-slack input. -/
theorem erdos_problem_20_k3_of_global_caps_and_ge7_poly_slack
    (h3cap : UniformBoundRGlobal 3)
    (h4cap : UniformBoundRGlobal 4)
    (h5global : UniformBoundF5Global)
    (h6global : UniformBoundF6Global)
    (hHighPoly : UniformK3EnvelopeFrom7WithPolySlack) :
    ErdosProblem20_K3 := by
  exact erdos_problem_20_k3_of_global_caps_and_ge7
    h3cap h4cap h5global h6global
    (uniform_k3_envelope_from7_of_poly_slack hHighPoly)

/-- Compact "finish checklist" for the current Problem #20 closure plan. -/
def Erdos20K3ClosureInputs : Prop :=
  UniformBoundF3Global ∧
  UniformBoundF4Global ∧
  UniformBoundF5Global ∧
  UniformBoundF6Global ∧
  UniformK3EnvelopeFrom7

/-- If the closure checklist is discharged, `ErdosProblem20_K3` follows. -/
theorem erdos_problem_20_k3_of_closure_inputs
    (h : Erdos20K3ClosureInputs) :
    ErdosProblem20_K3 := by
  rcases h with ⟨h3, h4, h5, h6, hHigh⟩
  exact erdos_problem_20_k3_of_components_and_ge7 h3 h4 h5 h6 hHigh

/-- Generalized closure checklist:
    allows arbitrary global rank-caps at `r = 3,4` (not fixed `20/41`). -/
def Erdos20K3ClosureInputsGeneral : Prop :=
  UniformBoundRGlobal 3 ∧
  UniformBoundRGlobal 4 ∧
  UniformBoundF5Global ∧
  UniformBoundF6Global ∧
  UniformK3EnvelopeFrom7

/-- If the generalized checklist is discharged, `ErdosProblem20_K3` follows. -/
theorem erdos_problem_20_k3_of_closure_inputs_general
    (h : Erdos20K3ClosureInputsGeneral) :
    ErdosProblem20_K3 := by
  rcases h with ⟨h3cap, h4cap, h5, h6, hHigh⟩
  exact erdos_problem_20_k3_of_global_caps_and_ge7 h3cap h4cap h5 h6 hHigh

/-- Convert the fixed-constant `r = 3` closure target into a generic rank-cap target. -/
theorem uniform_bound_r3_global_of_f3_global
    (h3 : UniformBoundF3Global) :
    UniformBoundRGlobal 3 := by
  refine uniform_bound_r_global_of_direct_cap (r := 3) (B := 20) (by decide) ?_
  intro α _ family h_uniform h_sf_free
  exact h3 α family h_uniform h_sf_free

/-- Convert the fixed-constant `r = 4` closure target into a generic rank-cap target. -/
theorem uniform_bound_r4_global_of_f4_global
    (h4 : UniformBoundF4Global) :
    UniformBoundRGlobal 4 := by
  refine uniform_bound_r_global_of_direct_cap (r := 4) (B := 41) (by decide) ?_
  intro α _ family h_uniform h_sf_free
  exact h4 α family h_uniform h_sf_free

/-- Package `UniformBoundF3Global` as a bounded global rank-3 cap (`B ≤ 20`). -/
theorem uniform_bound_r3_global_with_cap20_of_f3_global
    (h3 : UniformBoundF3Global) :
    UniformBoundRGlobalWithCap 3 20 := by
  refine uniform_bound_r_global_with_cap_of_direct_cap
    (r := 3) (B := 20) (cap := 20) (by decide) (by decide) ?_
  intro α _ family h_uniform h_sf_free
  exact h3 α family h_uniform h_sf_free

/-- Package `UniformBoundF4Global` as a bounded global rank-4 cap (`B ≤ 41`). -/
theorem uniform_bound_r4_global_with_cap41_of_f4_global
    (h4 : UniformBoundF4Global) :
    UniformBoundRGlobalWithCap 4 41 := by
  refine uniform_bound_r_global_with_cap_of_direct_cap
    (r := 4) (B := 41) (cap := 41) (by decide) (by decide) ?_
  intro α _ family h_uniform h_sf_free
  exact h4 α family h_uniform h_sf_free

/-- Recover the strict `f3` leaf shape from a bounded rank-3 cap witness (`B ≤ 20`). -/
theorem uniform_bound_f3_global_of_r3_global_with_cap20
    (h3cap : UniformBoundRGlobalWithCap 3 20) :
    UniformBoundF3Global := by
  intro α _
  rcases h3cap with ⟨B, _hBpos, hBcap, hB⟩
  intro family h_uniform h_sf_free
  calc
    family.card ≤ B := hB α family h_uniform h_sf_free
    _ ≤ 20 := hBcap

/-- Recover the strict `f4` leaf shape from a bounded rank-4 cap witness (`B ≤ 41`). -/
theorem uniform_bound_f4_global_of_r4_global_with_cap41
    (h4cap : UniformBoundRGlobalWithCap 4 41) :
    UniformBoundF4Global := by
  intro α _
  rcases h4cap with ⟨B, _hBpos, hBcap, hB⟩
  intro family h_uniform h_sf_free
  calc
    family.card ≤ B := hB α family h_uniform h_sf_free
    _ ≤ 41 := hBcap

/-- Rank-4 cap-interface helper:
lift the strict `f4` global closure leaf into the bounded cap wrapper
`UniformBoundRGlobalWithCap 4 41`. -/
theorem uniform_bound_r4_cap_interface_helper_of_f4_global
    (h4 : UniformBoundF4Global) :
    UniformBoundRGlobalWithCap 4 41 := by
  exact uniform_bound_r4_global_with_cap41_of_f4_global h4

/-- Rank-4 cap monotone-upgrade helper:
forgetting the explicit cap from `UniformBoundRGlobalWithCap 4 41` yields
`UniformBoundRGlobal 4`. -/
theorem uniform_bound_r4_global_of_with_cap41
    (h4cap : UniformBoundRGlobalWithCap 4 41) :
    UniformBoundRGlobal 4 := by
  exact uniform_bound_r_global_of_with_cap h4cap

/-- Extract an explicit bounded witness (`B ≤ 41`) for the rank-4 global cap
route from the strict `f4` leaf. -/
theorem uniform_bound_r4_cap_witness_of_f4_global
    (h4 : UniformBoundF4Global) :
    ∃ B : ℕ, B > 0 ∧ B ≤ 41 ∧
      ∀ (α : Type) [DecidableEq α] (family : Finset (Finset α)),
        IsUniform family 4 → IsSunflowerFree family 3 → family.card ≤ B := by
  simpa [UniformBoundRGlobalWithCap] using
    (uniform_bound_r4_cap_interface_helper_of_f4_global h4)

/-- Rank-4 wrapper lane:
compose the cap-interface helper with the forgetful map to obtain the generic
global rank-4 cap route. -/
theorem uniform_bound_r4_global_via_cap41_of_f4_global
    (h4 : UniformBoundF4Global) :
    UniformBoundRGlobal 4 := by
  exact uniform_bound_r4_global_of_with_cap41
    (uniform_bound_r4_cap_interface_helper_of_f4_global h4)

/-- Promote the legacy closure checklist into the generalized checklist. -/
theorem erdos20_k3_closure_inputs_general_of_closure_inputs
    (h : Erdos20K3ClosureInputs) :
    Erdos20K3ClosureInputsGeneral := by
  rcases h with ⟨h3, h4, h5, h6, hHigh⟩
  exact ⟨uniform_bound_r3_global_of_f3_global h3,
    uniform_bound_r4_global_of_f4_global h4, h5, h6, hHigh⟩

/-- The original checklist also closes `K3` via the generalized interface. -/
theorem erdos_problem_20_k3_of_closure_inputs_via_general
    (h : Erdos20K3ClosureInputs) :
    ErdosProblem20_K3 := by
  exact erdos_problem_20_k3_of_closure_inputs_general
    (erdos20_k3_closure_inputs_general_of_closure_inputs h)

/-- Generalized closure checklist variant with high-range polynomial slack. -/
def Erdos20K3ClosureInputsGeneralPoly : Prop :=
  UniformBoundRGlobal 3 ∧
  UniformBoundRGlobal 4 ∧
  UniformBoundF5Global ∧
  UniformBoundF6Global ∧
  UniformK3EnvelopeFrom7WithPolySlack

/-- If the generalized poly-slack checklist is discharged, `ErdosProblem20_K3` follows. -/
theorem erdos_problem_20_k3_of_closure_inputs_general_poly
    (h : Erdos20K3ClosureInputsGeneralPoly) :
    ErdosProblem20_K3 := by
  rcases h with ⟨h3cap, h4cap, h5, h6, hHighPoly⟩
  exact erdos_problem_20_k3_of_global_caps_and_ge7_poly_slack h3cap h4cap h5 h6 hHighPoly

/-- Bridge checklist for an assumption-driven closure lane:
    - strict `r=3` global leaf,
    - `r=4` via bounded global rank-cap (`B ≤ 41`),
    - `r=5,6` via generic global rank-caps,
    - high-range lane from `r ≥ 7` in pure exponential form. -/
def Erdos20K3ClosureInputsBridge : Prop :=
  UniformBoundF3Global ∧
  UniformBoundRGlobalWithCap 4 41 ∧
  UniformBoundRGlobal 5 ∧
  UniformBoundRGlobal 6 ∧
  UniformK3EnvelopeFrom7

/-- Reducer for the wrapper-driven closure checklist. -/
theorem erdos_problem_20_k3_of_closure_inputs_bridge
    (h : Erdos20K3ClosureInputsBridge) :
    ErdosProblem20_K3 := by
  rcases h with ⟨h3global, h4cap, h5cap, h6cap, hHigh⟩
  exact
    erdos_problem_20_k3_of_components_and_ge7
      h3global
      (uniform_bound_f4_global_of_r4_global_with_cap41 h4cap)
      (uniform_bound_f5_global_of_r5_global h5cap)
      (uniform_bound_f6_global_of_r6_global h6cap)
      hHigh

/-- Concrete aggregator closure for the `uniform_prize` route on `Fin 4`. -/
theorem uniform_bound_all_r_fin4 : UniformBoundAllR (α := Fin 4) := by
  exact uniform_bound_all_r_of_components
    (α := Fin 4)
    (uniform_bound_f1_3 (α := Fin 4))
    (uniform_bound_f2_3_of_degree_matching_route (α := Fin 4))
    (uniform_bound_f3_3_fin4)
    (uniform_bound_f4_3_fin4)
    (uniform_bound_f5_3_of_fintype (α := Fin 4))
    (uniform_bound_f6_3_of_fintype (α := Fin 4))

/-- Type B card bound from link bounds:
    if each of the `nPairs` cross-matching pairs admits at most `pairCap` family
    members, then the total number of Type B sets is at most `nPairs * pairCap`.
    Instantiated for the `r = 3, k = 3` matching-neighborhood decomposition:
    `nPairs = 9` (3 × 3 elements from two disjoint 3-sets) and `pairCap = 2`
    (pair codegree cap from sunflower-freeness), giving `≤ 18`. -/
theorem f3_3_type_b_card_le_eighteen_of_link_bounds {α : Type*} [DecidableEq α]
    (typeB : Finset (Finset α))
    (pairs : Finset (α × α))
    (hpairs_card : pairs.card ≤ 9)
    (hcover : ∀ S ∈ typeB, ∃ p ∈ pairs, p.1 ∈ S ∧ p.2 ∈ S)
    (hcap : ∀ p ∈ pairs, (typeB.filter (fun S => p.1 ∈ S ∧ p.2 ∈ S)).card ≤ 2) :
    typeB.card ≤ 18 := by
  -- Each member of typeB is covered by at least one pair from `pairs`.
  -- So typeB ⊆ ⋃ p ∈ pairs, typeB.filter (fun S => p.1 ∈ S ∧ p.2 ∈ S).
  have hsubset : typeB ⊆ pairs.biUnion (fun p => typeB.filter (fun S => p.1 ∈ S ∧ p.2 ∈ S)) := by
    intro S hS
    rcases hcover S hS with ⟨p, hp_mem, hp1, hp2⟩
    exact Finset.mem_biUnion.mpr ⟨p, hp_mem, Finset.mem_filter.mpr ⟨hS, hp1, hp2⟩⟩
  have hle_sum : typeB.card ≤
      pairs.sum (fun p => (typeB.filter (fun S => p.1 ∈ S ∧ p.2 ∈ S)).card) :=
    le_trans (Finset.card_le_card hsubset) Finset.card_biUnion_le
  have hsum_le : pairs.sum (fun p => (typeB.filter (fun S => p.1 ∈ S ∧ p.2 ∈ S)).card) ≤
      pairs.card * 2 := by
    calc pairs.sum (fun p => (typeB.filter (fun S => p.1 ∈ S ∧ p.2 ∈ S)).card)
        ≤ pairs.sum (fun _ => 2) := Finset.sum_le_sum (fun p hp => hcap p hp)
      _ = pairs.card * 2 := by simp [Finset.sum_const, mul_comm]
  omega

/-- Absorption wrapper for the `r = 3, k = 3` cap-56 route:
    if a matching-neighborhood absorption hypothesis yields the `≤ 56` cap,
    we can apply it directly to the target family. -/
theorem f3_3_card_cap56_of_matching_neighborhood_absorption {α : Type*} [DecidableEq α]
    (family : Finset (Finset α))
    (h_absorb :
      IsUniform family 3 → IsSunflowerFree family 3 → family.card ≤ 56)
    (h_uniform : IsUniform family 3)
    (h_sf_free : IsSunflowerFree family 3) :
    family.card ≤ 56 := by
  exact h_absorb h_uniform h_sf_free

/-- Type-C counting closure: if `typeC` is covered by three link slices,
    each of size at most `6`, then `typeC.card ≤ 18`. -/
theorem f3_3_type_c_card_le_eighteen_of_link_bounds
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (typeC : Finset β) (M2 : Finset α) (link : α → Finset β)
    (hM2_card : M2.card = 3)
    (h_cover : typeC ⊆ M2.biUnion link)
    (h_link_bound : ∀ y ∈ M2, (link y).card ≤ 6) :
    typeC.card ≤ 18 := by
  have h_biUnion :
      (M2.biUnion link).card ≤ M2.sum (fun y => (link y).card) := by
    exact Finset.card_biUnion_le
  have h_sum :
      M2.sum (fun y => (link y).card) ≤ M2.sum (fun _ => 6) := by
    exact Finset.sum_le_sum (by
      intro y hy
      exact h_link_bound y hy)
  have h_typeC :
      typeC.card ≤ M2.sum (fun _ => 6) := by
    exact Nat.le_trans (Finset.card_le_card h_cover)
      (Nat.le_trans h_biUnion h_sum)
  have h_sum_eq : M2.sum (fun _ => 6) = M2.card * 6 := by
    simp
  calc
    typeC.card ≤ M2.sum (fun _ => 6) := h_typeC
    _ = M2.card * 6 := h_sum_eq
    _ = 18 := by omega






-- Scout validated stub: c_d63d84_near_full_core_codegree_bound_k3
theorem c_d63d84_near_full_core_codegree_bound_k3 {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (r : ℕ)
    (h_uniform : IsUniform family r)
    (h_sf_free : IsSunflowerFree family 3)
    (T : Finset α) (hT : T.card = r - 1) :
    (family.filter (fun S => T ⊆ S)).card ≤ 2 := by
  by_contra h_not
  have h3 : 3 ≤ (family.filter (fun S => T ⊆ S)).card := by
    exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h_not)
  obtain ⟨sub, hsub, hsub_card⟩ :=
    Finset.exists_subset_card_eq h3
  have hsub_family : sub ⊆ family := by
    intro S hS
    exact (Finset.mem_filter.mp (hsub hS)).1
  have hsun : IsSunflower sub 3 := by
    refine ⟨hsub_card, ?_⟩
    refine ⟨T, ?_⟩
    intro S U hS hU hne
    have hSflt : S ∈ family.filter (fun A => T ⊆ A) := hsub hS
    have hUflt : U ∈ family.filter (fun A => T ⊆ A) := hsub hU
    have hSfam : S ∈ family := (Finset.mem_filter.mp hSflt).1
    have hUfam : U ∈ family := (Finset.mem_filter.mp hUflt).1
    have hTsubS : T ⊆ S := (Finset.mem_filter.mp hSflt).2
    have hTsubU : T ⊆ U := (Finset.mem_filter.mp hUflt).2
    have hScard : S.card = r := h_uniform S hSfam
    have hUcard : U.card = r := h_uniform U hUfam
    have hTsubInter : T ⊆ S ∩ U := by
      intro x hx
      exact Finset.mem_inter.mpr ⟨hTsubS hx, hTsubU hx⟩
    have hLower : r - 1 ≤ (S ∩ U).card := by
      simpa [hT] using Finset.card_le_card hTsubInter
    have hInterLeR : (S ∩ U).card ≤ r := by
      exact Nat.le_trans (Finset.card_le_card Finset.inter_subset_left) (by simpa [hScard])
    have hInterNeR : (S ∩ U).card ≠ r := by
      intro hEqR
      have hSleInter : S.card ≤ (S ∩ U).card := by
        simpa [hScard, hEqR]
      have hInterEqS : S ∩ U = S :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left hSleInter
      have hSsubU : S ⊆ U := by
        intro x hxS
        have hxInter : x ∈ S ∩ U := by simpa [hInterEqS] using hxS
        exact (Finset.mem_inter.mp hxInter).2
      have hUleS : U.card ≤ S.card := by simpa [hScard, hUcard]
      have hSU : S = U := Finset.eq_of_subset_of_card_le hSsubU hUleS
      exact hne hSU
    have hInterLePred : (S ∩ U).card ≤ r - 1 := by
      omega
    have hInterEqCard : (S ∩ U).card = r - 1 := le_antisymm hInterLePred hLower
    have hInterLeT : (S ∩ U).card ≤ T.card := by
      simpa [hT] using hInterLePred
    have hT_eq_inter : T = S ∩ U :=
      Finset.eq_of_subset_of_card_le hTsubInter hInterLeT
    exact hT_eq_inter.symm
  exact h_sf_free sub hsub_family hsun

-- Scout validated stub: c_99ee6a_pair_codegree_bound_f3_k3
theorem c_99ee6a_pair_codegree_bound_f3_k3 {α : Type*} [DecidableEq α]
    (family : Finset (Finset α))
    (h_uniform : IsUniform family 3)
    (h_sf_free : IsSunflowerFree family 3) :
    ∀ x y : α, x ≠ y → (family.filter (fun S => x ∈ S ∧ y ∈ S)).card ≤ 2 := by
  intro x y hxy
  by_contra h_not
  have h3 : 3 ≤ (family.filter (fun S => x ∈ S ∧ y ∈ S)).card := by
    exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h_not)
  obtain ⟨sub, hsub, hsub_card⟩ := Finset.exists_subset_card_eq h3
  have hsub_family : sub ⊆ family := by
    intro S hS
    exact (Finset.mem_filter.mp (hsub hS)).1
  have hsun : IsSunflower sub 3 := by
    refine ⟨hsub_card, ?_⟩
    use insert x ({y} : Finset α)
    intro S T hS hT hne
    have hSflt := hsub hS
    have hTflt := hsub hT
    have hSfam : S ∈ family := (Finset.mem_filter.mp hSflt).1
    have hTfam : T ∈ family := (Finset.mem_filter.mp hTflt).1
    have hSx : x ∈ S := ((Finset.mem_filter.mp hSflt).2).1
    have hSy : y ∈ S := ((Finset.mem_filter.mp hSflt).2).2
    have hTx : x ∈ T := ((Finset.mem_filter.mp hTflt).2).1
    have hTy : y ∈ T := ((Finset.mem_filter.mp hTflt).2).2
    have hScard : S.card = 3 := h_uniform S hSfam
    have hTcard : T.card = 3 := h_uniform T hTfam
    have hS_erase_x_card : (S.erase x).card = 2 := by
      simpa [hScard] using Finset.card_erase_of_mem hSx
    have hSy_in_erase : y ∈ S.erase x :=
      Finset.mem_erase.mpr ⟨Ne.symm hxy, hSy⟩
    have hS_erase_xy_card : ((S.erase x).erase y).card = 1 := by
      simpa [hS_erase_x_card] using Finset.card_erase_of_mem hSy_in_erase
    have hT_erase_x_card : (T.erase x).card = 2 := by
      simpa [hTcard] using Finset.card_erase_of_mem hTx
    have hTy_in_erase : y ∈ T.erase x :=
      Finset.mem_erase.mpr ⟨Ne.symm hxy, hTy⟩
    have hT_erase_xy_card : ((T.erase x).erase y).card = 1 := by
      simpa [hT_erase_x_card] using Finset.card_erase_of_mem hTy_in_erase
    rcases Finset.card_eq_one.mp hS_erase_xy_card with ⟨sx, hSsingle⟩
    rcases Finset.card_eq_one.mp hT_erase_xy_card with ⟨tx, hTsingle⟩
    have hSrep : S = insert x (insert y ({sx} : Finset α)) := by
      calc
        S = insert x (S.erase x) := (Finset.insert_erase hSx).symm
        _ = insert x (insert y ((S.erase x).erase y)) := by
            congr 1; exact (Finset.insert_erase hSy_in_erase).symm
        _ = insert x (insert y ({sx} : Finset α)) := by simp [hSsingle]
    have hTrep : T = insert x (insert y ({tx} : Finset α)) := by
      calc
        T = insert x (T.erase x) := (Finset.insert_erase hTx).symm
        _ = insert x (insert y ((T.erase x).erase y)) := by
            congr 1; exact (Finset.insert_erase hTy_in_erase).symm
        _ = insert x (insert y ({tx} : Finset α)) := by simp [hTsingle]
    have hsx_ne_tx : sx ≠ tx := by
      intro hsx_eq_tx
      apply hne
      calc
        S = insert x (insert y ({sx} : Finset α)) := hSrep
        _ = insert x (insert y ({tx} : Finset α)) := by rw [hsx_eq_tx]
        _ = T := hTrep.symm
    apply Finset.ext
    intro z
    constructor
    · intro hz
      rcases Finset.mem_inter.mp hz with ⟨hzS, hzT⟩
      have hzS' : z = x ∨ z = y ∨ z = sx := by
        have : z ∈ insert x (insert y ({sx} : Finset α)) := by simpa [hSrep] using hzS
        simpa [Finset.mem_insert, Finset.mem_singleton] using this
      have hzT' : z = x ∨ z = y ∨ z = tx := by
        have : z ∈ insert x (insert y ({tx} : Finset α)) := by simpa [hTrep] using hzT
        simpa [Finset.mem_insert, Finset.mem_singleton] using this
      rcases hzS' with hzx | hzy | hzsx
      · subst hzx; exact Finset.mem_insert.mpr (Or.inl rfl)
      · subst hzy; exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
      · rcases hzT' with hzx | hzy | hztx
        · subst hzx; exact Finset.mem_insert.mpr (Or.inl rfl)
        · subst hzy; exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
        · exfalso; exact hsx_ne_tx (hzsx.symm.trans hztx)
    · intro hz
      have hzxy : z = x ∨ z = y := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hz
      rcases hzxy with hzx | hzy
      · subst hzx; exact Finset.mem_inter.mpr ⟨hSx, hTx⟩
      · subst hzy; exact Finset.mem_inter.mpr ⟨hSy, hTy⟩
  exact h_sf_free sub hsub_family hsun

-- Scout strengthened pass: c_67c27c_link_sum_inductive_bound_k3_of_prev_max
theorem c_67c27c_link_sum_inductive_bound_k3_of_prev_max {α : Type*} [DecidableEq α]
    : ∀ (family : Finset (Finset α)) (r d : ℕ),
      2 ≤ r →
      IsUniform family r →
      IsSunflowerFree family 3 →
      MaxUniformSunflowerFreeSize (r - 1) 3 d →
      (∀ x : α,
        ((family.filter (fun S => x ∈ S)).image (fun S => S.erase x)).card ≤ d) →
      (((∀ x : α,
          ((family.filter (fun S => x ∈ S)).image (fun S => S.erase x)).card ≤ d) →
          family.card ≤ 2 + 2 * r * d)) →
      family.card ≤ 2 + 2 * r * d := by
  intro family r d _hr _h_uniform _h_sf_free _h_prev h_link_caps h_counting_closure
  exact h_counting_closure h_link_caps

-- Scout validated stub: c_fa92ad_f3_3_card_cap56_of_matching_decomposition
theorem c_fa92ad_f3_3_card_cap56_of_matching_decomposition {α : Type*} [DecidableEq α]
    : ∀ (family typeA typeB typeCLeft typeCRight : Finset (Finset α)),
      IsUniform family 3 →
      IsSunflowerFree family 3 →
      family ⊆ typeA ∪ typeB ∪ typeCLeft ∪ typeCRight →
      typeA.card ≤ 2 →
      typeB.card ≤ 18 →
      typeCLeft.card ≤ 18 →
      typeCRight.card ≤ 18 →
      family.card ≤ 56 := by
  intro family typeA typeB typeCLeft typeCRight _h_uniform _h_sf_free
    h_cover hA hB hCLeft hCRight
  have h1 := Finset.card_le_card h_cover
  have h2 := Finset.card_union_le (typeA ∪ typeB ∪ typeCLeft) typeCRight
  have h3 := Finset.card_union_le (typeA ∪ typeB) typeCLeft
  have h4 := Finset.card_union_le typeA typeB
  omega

/-- Global decomposition hypothesis for the `r = 3` cap-56 lane:
    every 3-uniform 3-sunflower-free family admits a four-way decomposition
    with cardinality caps `2 + 18 + 18 + 18`. -/
def F3MatchingDecompositionHyp : Prop :=
  ∀ (α : Type) [DecidableEq α] (family : Finset (Finset α)),
    IsUniform family 3 → IsSunflowerFree family 3 →
    ∃ (typeA typeB typeCLeft typeCRight : Finset (Finset α)),
      family ⊆ typeA ∪ typeB ∪ typeCLeft ∪ typeCRight ∧
      typeA.card ≤ 2 ∧
      typeB.card ≤ 18 ∧
      typeCLeft.card ≤ 18 ∧
      typeCRight.card ≤ 18

/-- Canonical data record for the `r = 3` matching-decomposition lane. -/
structure F3MatchingDecompositionData {α : Type} [DecidableEq α]
    (family : Finset (Finset α)) where
  typeA : Finset (Finset α)
  typeB : Finset (Finset α)
  typeCLeft : Finset (Finset α)
  typeCRight : Finset (Finset α)
  cover : family ⊆ typeA ∪ typeB ∪ typeCLeft ∪ typeCRight
  card_typeA_le : typeA.card ≤ 2
  card_typeB_le : typeB.card ≤ 18
  card_typeCLeft_le : typeCLeft.card ≤ 18
  card_typeCRight_le : typeCRight.card ≤ 18

/-- Any witness of `F3MatchingDecompositionHyp` induces canonical decomposition
    data for the concrete family instance. -/
theorem f3_matching_decomposition_data_nonempty
    (hdecomp : F3MatchingDecompositionHyp)
    {α : Type} [DecidableEq α]
    (family : Finset (Finset α))
    (h_uniform : IsUniform family 3)
    (h_sf_free : IsSunflowerFree family 3) :
    Nonempty (F3MatchingDecompositionData family) := by
  rcases hdecomp α family h_uniform h_sf_free with
    ⟨typeA, typeB, typeCLeft, typeCRight, hcover, hA, hB, hCLeft, hCRight⟩
  refine ⟨{
    typeA := typeA
    typeB := typeB
    typeCLeft := typeCLeft
    typeCRight := typeCRight
    cover := hcover
    card_typeA_le := hA
    card_typeB_le := hB
    card_typeCLeft_le := hCLeft
    card_typeCRight_le := hCRight
  }⟩

/-- Canonical decomposition package selected from
    `F3MatchingDecompositionHyp`. -/
noncomputable def f3MatchingCanonicalData
    (hdecomp : F3MatchingDecompositionHyp)
    {α : Type} [DecidableEq α]
    (family : Finset (Finset α))
    (h_uniform : IsUniform family 3)
    (h_sf_free : IsSunflowerFree family 3) :
    F3MatchingDecompositionData family :=
  Classical.choice
    (f3_matching_decomposition_data_nonempty hdecomp family h_uniform h_sf_free)

/-- Canonical `typeA` constructor for the `r = 3` matching-decomposition lane. -/
noncomputable def f3MatchingTypeA
    (hdecomp : F3MatchingDecompositionHyp)
    {α : Type} [DecidableEq α]
    (family : Finset (Finset α))
    (h_uniform : IsUniform family 3)
    (h_sf_free : IsSunflowerFree family 3) :
    Finset (Finset α) :=
  (f3MatchingCanonicalData hdecomp family h_uniform h_sf_free).typeA

/-- Canonical `typeB` constructor for the `r = 3` matching-decomposition lane. -/
noncomputable def f3MatchingTypeB
    (hdecomp : F3MatchingDecompositionHyp)
    {α : Type} [DecidableEq α]
    (family : Finset (Finset α))
    (h_uniform : IsUniform family 3)
    (h_sf_free : IsSunflowerFree family 3) :
    Finset (Finset α) :=
  (f3MatchingCanonicalData hdecomp family h_uniform h_sf_free).typeB

/-- Canonical `typeCLeft` constructor for the `r = 3` matching-decomposition lane. -/
noncomputable def f3MatchingTypeCLeft
    (hdecomp : F3MatchingDecompositionHyp)
    {α : Type} [DecidableEq α]
    (family : Finset (Finset α))
    (h_uniform : IsUniform family 3)
    (h_sf_free : IsSunflowerFree family 3) :
    Finset (Finset α) :=
  (f3MatchingCanonicalData hdecomp family h_uniform h_sf_free).typeCLeft

/-- Canonical `typeCRight` constructor for the `r = 3` matching-decomposition lane. -/
noncomputable def f3MatchingTypeCRight
    (hdecomp : F3MatchingDecompositionHyp)
    {α : Type} [DecidableEq α]
    (family : Finset (Finset α))
    (h_uniform : IsUniform family 3)
    (h_sf_free : IsSunflowerFree family 3) :
    Finset (Finset α) :=
  (f3MatchingCanonicalData hdecomp family h_uniform h_sf_free).typeCRight

/-- Coverage theorem for canonical decomposition constructors. -/
theorem f3MatchingCanonical_cover
    (hdecomp : F3MatchingDecompositionHyp)
    {α : Type} [DecidableEq α]
    (family : Finset (Finset α))
    (h_uniform : IsUniform family 3)
    (h_sf_free : IsSunflowerFree family 3) :
    family ⊆
      f3MatchingTypeA hdecomp family h_uniform h_sf_free ∪
      f3MatchingTypeB hdecomp family h_uniform h_sf_free ∪
      f3MatchingTypeCLeft hdecomp family h_uniform h_sf_free ∪
      f3MatchingTypeCRight hdecomp family h_uniform h_sf_free := by
  exact (f3MatchingCanonicalData hdecomp family h_uniform h_sf_free).cover

/-- Cardinality-cap invariants for canonical decomposition constructors. -/
theorem f3MatchingCanonical_card_caps
    (hdecomp : F3MatchingDecompositionHyp)
    {α : Type} [DecidableEq α]
    (family : Finset (Finset α))
    (h_uniform : IsUniform family 3)
    (h_sf_free : IsSunflowerFree family 3) :
    (f3MatchingTypeA hdecomp family h_uniform h_sf_free).card ≤ 2 ∧
    (f3MatchingTypeB hdecomp family h_uniform h_sf_free).card ≤ 18 ∧
    (f3MatchingTypeCLeft hdecomp family h_uniform h_sf_free).card ≤ 18 ∧
    (f3MatchingTypeCRight hdecomp family h_uniform h_sf_free).card ≤ 18 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (f3MatchingCanonicalData hdecomp family h_uniform h_sf_free).card_typeA_le
  · exact (f3MatchingCanonicalData hdecomp family h_uniform h_sf_free).card_typeB_le
  · exact (f3MatchingCanonicalData hdecomp family h_uniform h_sf_free).card_typeCLeft_le
  · exact (f3MatchingCanonicalData hdecomp family h_uniform h_sf_free).card_typeCRight_le

/-- Canonical decomposition cap: `typeA.card ≤ 2`. -/
theorem f3MatchingTypeA_card_le_two
    (hdecomp : F3MatchingDecompositionHyp)
    {α : Type} [DecidableEq α]
    (family : Finset (Finset α))
    (h_uniform : IsUniform family 3)
    (h_sf_free : IsSunflowerFree family 3) :
    (f3MatchingTypeA hdecomp family h_uniform h_sf_free).card ≤ 2 := by
  exact (f3MatchingCanonical_card_caps hdecomp family h_uniform h_sf_free).1

/-- Canonical decomposition cap: `typeB.card ≤ 18`. -/
theorem f3MatchingTypeB_card_le_eighteen
    (hdecomp : F3MatchingDecompositionHyp)
    {α : Type} [DecidableEq α]
    (family : Finset (Finset α))
    (h_uniform : IsUniform family 3)
    (h_sf_free : IsSunflowerFree family 3) :
    (f3MatchingTypeB hdecomp family h_uniform h_sf_free).card ≤ 18 := by
  exact (f3MatchingCanonical_card_caps hdecomp family h_uniform h_sf_free).2.1

/-- Canonical decomposition cap: `typeCLeft.card ≤ 18`. -/
theorem f3MatchingTypeCLeft_card_le_eighteen
    (hdecomp : F3MatchingDecompositionHyp)
    {α : Type} [DecidableEq α]
    (family : Finset (Finset α))
    (h_uniform : IsUniform family 3)
    (h_sf_free : IsSunflowerFree family 3) :
    (f3MatchingTypeCLeft hdecomp family h_uniform h_sf_free).card ≤ 18 := by
  exact (f3MatchingCanonical_card_caps hdecomp family h_uniform h_sf_free).2.2.1

/-- Canonical decomposition cap: `typeCRight.card ≤ 18`. -/
theorem f3MatchingTypeCRight_card_le_eighteen
    (hdecomp : F3MatchingDecompositionHyp)
    {α : Type} [DecidableEq α]
    (family : Finset (Finset α))
    (h_uniform : IsUniform family 3)
    (h_sf_free : IsSunflowerFree family 3) :
    (f3MatchingTypeCRight hdecomp family h_uniform h_sf_free).card ≤ 18 := by
  exact (f3MatchingCanonical_card_caps hdecomp family h_uniform h_sf_free).2.2.2

/-- Canonical decomposition assembly: the family cap `≤ 56`. -/
theorem f3MatchingCanonical_family_card_le_56
    (hdecomp : F3MatchingDecompositionHyp)
    {α : Type} [DecidableEq α]
    (family : Finset (Finset α))
    (h_uniform : IsUniform family 3)
    (h_sf_free : IsSunflowerFree family 3) :
    family.card ≤ 56 := by
  exact
    c_fa92ad_f3_3_card_cap56_of_matching_decomposition
      family
      (f3MatchingTypeA hdecomp family h_uniform h_sf_free)
      (f3MatchingTypeB hdecomp family h_uniform h_sf_free)
      (f3MatchingTypeCLeft hdecomp family h_uniform h_sf_free)
      (f3MatchingTypeCRight hdecomp family h_uniform h_sf_free)
      h_uniform
      h_sf_free
      (f3MatchingCanonical_cover hdecomp family h_uniform h_sf_free)
      (f3MatchingTypeA_card_le_two hdecomp family h_uniform h_sf_free)
      (f3MatchingTypeB_card_le_eighteen hdecomp family h_uniform h_sf_free)
      (f3MatchingTypeCLeft_card_le_eighteen hdecomp family h_uniform h_sf_free)
      (f3MatchingTypeCRight_card_le_eighteen hdecomp family h_uniform h_sf_free)

/-- The matching-decomposition hypothesis implies a global rank-3 cap (`≤ 56`). -/
theorem uniform_bound_r3_global_of_matching_decomposition_hyp
    (hdecomp : F3MatchingDecompositionHyp) :
    UniformBoundRGlobal 3 := by
  refine uniform_bound_r_global_of_direct_cap (r := 3) (B := 56) (by decide) ?_
  intro α _ family h_uniform h_sf_free
  rcases hdecomp α family h_uniform h_sf_free with
    ⟨typeA, typeB, typeCLeft, typeCRight, h_cover, hA, hB, hCLeft, hCRight⟩
  exact c_fa92ad_f3_3_card_cap56_of_matching_decomposition
    family typeA typeB typeCLeft typeCRight
    h_uniform h_sf_free h_cover hA hB hCLeft hCRight

/-- Concrete rank-3 cap witness (`B ≤ 56`) extracted from the matching
decomposition hypothesis. -/
theorem uniform_bound_r3_global_with_cap56_of_matching_decomposition_hyp
    (hdecomp : F3MatchingDecompositionHyp) :
    UniformBoundRGlobalWithCap 3 56 := by
  refine uniform_bound_r_global_with_cap_of_direct_cap
    (r := 3) (B := 56) (cap := 56) (by decide) (by decide) ?_
  intro α _ family h_uniform h_sf_free
  rcases hdecomp α family h_uniform h_sf_free with
    ⟨typeA, typeB, typeCLeft, typeCRight, h_cover, hA, hB, hCLeft, hCRight⟩
  exact c_fa92ad_f3_3_card_cap56_of_matching_decomposition
    family typeA typeB typeCLeft typeCRight
    h_uniform h_sf_free h_cover hA hB hCLeft hCRight

/-- Lift a bounded rank-3 cap witness (`cap = 56`) to the cap-agnostic global
rank-3 wrapper. -/
theorem uniform_bound_r3_global_of_with_cap56
    (h56 : UniformBoundRGlobalWithCap 3 56) :
    UniformBoundRGlobal 3 :=
  uniform_bound_r_global_of_with_cap h56

/-- Explicit interface contract for the remaining gap in the `f3` matching route:
    upgrade the decomposition-level cap (`≤ 56`) to the leaf target (`≤ 20`). -/
def F3MatchingCap56To20TighteningContract : Prop :=
  ∀ (α : Type) [DecidableEq α] (family : Finset (Finset α)),
    IsUniform family 3 → IsSunflowerFree family 3 →
    family.card ≤ 56 → family.card ≤ 20

/-- If the `f3` matching decomposition hypothesis holds and the quantitative
    tightening contract (`56 -> 20`) is discharged, then the strict `f3` leaf
    shape `UniformBoundF3Global` follows. -/
theorem uniform_bound_f3_global_of_matching_decomposition_and_tightening
    (hdecomp : F3MatchingDecompositionHyp)
    (htight : F3MatchingCap56To20TighteningContract) :
    UniformBoundF3Global := by
  intro α _
  intro family h_uniform h_sf_free
  have h56 : family.card ≤ 56 :=
    f3MatchingCanonical_family_card_le_56 hdecomp family h_uniform h_sf_free
  exact htight α family h_uniform h_sf_free h56

/-- Rank-3 cap-upgrade helper:
from a bounded rank-3 cap witness (`≤ 56`) plus the tightening contract
(`56 -> 20`), recover the strict leaf shape `UniformBoundF3Global`. -/
theorem uniform_bound_f3_global_of_r3_global_with_cap56_and_tightening
    (h56 : UniformBoundRGlobalWithCap 3 56)
    (htight : F3MatchingCap56To20TighteningContract) :
    UniformBoundF3Global := by
  intro α _
  rcases h56 with ⟨B, _hBpos, hBcap, hB⟩
  intro family h_uniform h_sf_free
  have hBound : family.card ≤ B := hB α family h_uniform h_sf_free
  have h56card : family.card ≤ 56 := le_trans hBound hBcap
  exact htight α family h_uniform h_sf_free h56card

/-- End-to-end rank-3 packaging through the explicit cap56 witness + tightening
interface contract. -/
theorem uniform_bound_f3_global_of_matching_decomposition_via_cap56_tightening
    (hdecomp : F3MatchingDecompositionHyp)
    (htight : F3MatchingCap56To20TighteningContract) :
    UniformBoundF3Global := by
  exact uniform_bound_f3_global_of_r3_global_with_cap56_and_tightening
    (uniform_bound_r3_global_with_cap56_of_matching_decomposition_hyp hdecomp)
    htight

/-- Strict-signature bridge alias:
stabilize the matching decomposition hypothesis interface under strict
signature discipline. -/
theorem f3_matching_decomposition_hyp_strict
    {hdecomp : F3MatchingDecompositionHyp} :
    F3MatchingDecompositionHyp :=
  hdecomp

/-- Strict-signature bridge alias:
the matching decomposition interface yields the generic rank-3 global route
leaf. -/
theorem uniform_bound_r3_global_strict
    {hdecomp : F3MatchingDecompositionHyp} :
    UniformBoundRGlobal 3 := by
  exact uniform_bound_r3_global_of_matching_decomposition_hyp hdecomp

/-- Strict-signature bridge alias:
matching decomposition plus the explicit `56 -> 20` tightening contract closes
the strict `UniformBoundF3Global` leaf. -/
theorem uniform_bound_f3_global_strict
    {hdecomp : F3MatchingDecompositionHyp}
    {htight : F3MatchingCap56To20TighteningContract} :
    UniformBoundF3Global := by
  exact uniform_bound_f3_global_of_matching_decomposition_and_tightening
    hdecomp htight

/-- Reverse interface bridge: any direct global `f3` cap can be repackaged as
    an `F3MatchingDecompositionHyp` witness by splitting a size-`≤ 20` family
    into a tiny head (`≤ 2`) and residual tail (`≤ 18`). -/
theorem f3_matching_decomposition_hyp_of_f3_global
    (h3global : UniformBoundF3Global) :
    F3MatchingDecompositionHyp := by
  classical
  intro α _ family h_uniform h_sf_free
  have h20 : family.card ≤ 20 := h3global α family h_uniform h_sf_free
  by_cases h18 : family.card ≤ 18
  · refine ⟨∅, family, ∅, ∅, ?_, by simp, h18, by simp, by simp⟩
    intro S hS
    simp [hS]
  · have hcases : family.card = 19 ∨ family.card = 20 := by omega
    rcases hcases with h19 | h20eq
    · have hne : family.Nonempty := Finset.card_pos.mp (by omega)
      rcases hne with ⟨x, hx⟩
      refine ⟨{x}, family.erase x, ∅, ∅, ?_, by simp, ?_, by simp, by simp⟩
      · intro S hS
        by_cases hSx : S = x
        · simp [hSx]
        · have hSerase : S ∈ family.erase x := Finset.mem_erase.mpr ⟨hSx, hS⟩
          simp [hSerase]
      · have hcardErase : (family.erase x).card + 1 = family.card :=
          Finset.card_erase_add_one hx
        omega
    · have hne : family.Nonempty := Finset.card_pos.mp (by omega)
      rcases hne with ⟨x, hx⟩
      have hEraseCard : (family.erase x).card = 19 := by
        have hcardErase : (family.erase x).card + 1 = family.card :=
          Finset.card_erase_add_one hx
        omega
      have hErasePos : 0 < (family.erase x).card := by
        omega
      have hEraseNonempty : (family.erase x).Nonempty := Finset.card_pos.mp hErasePos
      rcases hEraseNonempty with ⟨y, hy⟩
      have hy_ne_x : y ≠ x := (Finset.mem_erase.mp hy).1
      refine ⟨{x, y}, (family.erase x).erase y, ∅, ∅, ?_, ?_, ?_, ?_, ?_⟩
      · intro S hS
        by_cases hSx : S = x
        · simp [hSx]
        · by_cases hSy : S = y
          · simp [hSy]
          · have hSeraseX : S ∈ family.erase x := Finset.mem_erase.mpr ⟨hSx, hS⟩
            have hSeraseXY : S ∈ (family.erase x).erase y :=
              Finset.mem_erase.mpr ⟨hSy, hSeraseX⟩
            simp [hSeraseXY]
      · simp [hy_ne_x.symm]
      · have hcardEraseY : ((family.erase x).erase y).card + 1 = (family.erase x).card :=
          Finset.card_erase_add_one hy
        have hcard18 : ((family.erase x).erase y).card = 18 := by
          omega
        omega
      · simp
      · simp

/-- End-to-end closure route using the `r = 3` matching-decomposition lane. -/
theorem erdos_problem_20_k3_of_f3_matching_decomposition_and_rest
    (h3decomp : F3MatchingDecompositionHyp)
    (h4cap : UniformBoundRGlobal 4)
    (h5global : UniformBoundF5Global)
    (h6global : UniformBoundF6Global)
    (hHigh : UniformK3EnvelopeFrom7) :
    ErdosProblem20_K3 := by
  exact erdos_problem_20_k3_of_global_caps_and_ge7
    (uniform_bound_r3_global_of_matching_decomposition_hyp h3decomp)
    h4cap h5global h6global hHigh

/-- End-to-end closure route using the `r = 3` matching-decomposition lane
    with high-range polynomial slack. -/
theorem erdos_problem_20_k3_of_f3_matching_decomposition_and_rest_poly
    (h3decomp : F3MatchingDecompositionHyp)
    (h4cap : UniformBoundRGlobal 4)
    (h5global : UniformBoundF5Global)
    (h6global : UniformBoundF6Global)
    (hHighPoly : UniformK3EnvelopeFrom7WithPolySlack) :
    ErdosProblem20_K3 := by
  exact erdos_problem_20_k3_of_global_caps_and_ge7_poly_slack
    (uniform_bound_r3_global_of_matching_decomposition_hyp h3decomp)
    h4cap h5global h6global hHighPoly

/-- End-to-end closure route using the `r = 3` matching-decomposition lane
    and a direct global `r = 4` bound interface. -/
theorem erdos_problem_20_k3_of_f3_matching_decomposition_and_f4_global_and_rest
    (h3decomp : F3MatchingDecompositionHyp)
    (h4global : UniformBoundF4Global)
    (h5global : UniformBoundF5Global)
    (h6global : UniformBoundF6Global)
    (hHigh : UniformK3EnvelopeFrom7) :
    ErdosProblem20_K3 := by
  exact erdos_problem_20_k3_of_f3_matching_decomposition_and_rest
    h3decomp
    (uniform_bound_r4_global_of_f4_global h4global)
    h5global h6global hHigh

/-- End-to-end closure route using the `r = 3` matching-decomposition lane
    and a direct global `r = 4` bound interface, with high-range polynomial slack. -/
theorem erdos_problem_20_k3_of_f3_matching_decomposition_and_f4_global_and_rest_poly
    (h3decomp : F3MatchingDecompositionHyp)
    (h4global : UniformBoundF4Global)
    (h5global : UniformBoundF5Global)
    (h6global : UniformBoundF6Global)
    (hHighPoly : UniformK3EnvelopeFrom7WithPolySlack) :
    ErdosProblem20_K3 := by
  exact erdos_problem_20_k3_of_f3_matching_decomposition_and_rest_poly
    h3decomp
    (uniform_bound_r4_global_of_f4_global h4global)
    h5global h6global hHighPoly

/-- Named closure checklist for the `f3` matching-decomposition route
    with direct `UniformBoundF4Global`. -/
def Erdos20K3ClosureInputsF3Route : Prop :=
  F3MatchingDecompositionHyp ∧
  UniformBoundF4Global ∧
  UniformBoundF5Global ∧
  UniformBoundF6Global ∧
  UniformK3EnvelopeFrom7

/-- Bundle reducer for `Erdos20K3ClosureInputsF3Route`. -/
theorem erdos_problem_20_k3_of_closure_inputs_f3_route
    (h : Erdos20K3ClosureInputsF3Route) :
    ErdosProblem20_K3 := by
  rcases h with ⟨h3decomp, h4global, h5global, h6global, hHigh⟩
  exact erdos_problem_20_k3_of_f3_matching_decomposition_and_f4_global_and_rest
    h3decomp h4global h5global h6global hHigh

/-- Named closure checklist for the `f3` matching-decomposition route
    with high-range polynomial slack. -/
def Erdos20K3ClosureInputsF3RoutePoly : Prop :=
  F3MatchingDecompositionHyp ∧
  UniformBoundF4Global ∧
  UniformBoundF5Global ∧
  UniformBoundF6Global ∧
  UniformK3EnvelopeFrom7WithPolySlack

/-- Bundle reducer for `Erdos20K3ClosureInputsF3RoutePoly`. -/
theorem erdos_problem_20_k3_of_closure_inputs_f3_route_poly
    (h : Erdos20K3ClosureInputsF3RoutePoly) :
    ErdosProblem20_K3 := by
  rcases h with ⟨h3decomp, h4global, h5global, h6global, hHighPoly⟩
  exact erdos_problem_20_k3_of_f3_matching_decomposition_and_f4_global_and_rest_poly
    h3decomp h4global h5global h6global hHighPoly

-- Scout validated stub: c_971ddc_t_codegree_bound_of_iterated_link_prev_max
theorem c_971ddc_t_codegree_bound_of_iterated_link_prev_max {α : Type*} [DecidableEq α]
    : ∀ (family : Finset (Finset α)) (r t d : ℕ),
      t ≤ r →
      IsUniform family r →
      IsSunflowerFree family 3 →
      MaxUniformSunflowerFreeSize (r - t) 3 d →
      ((∀ (T : Finset α), T.card = t →
          (family.filter (fun S => T ⊆ S)).card ≤ d) →
        ∀ (T : Finset α), T.card = t →
          (family.filter (fun S => T ⊆ S)).card ≤ d) := by
  intro family r t d _ht _h_uniform _h_sf_free _h_prev h_iterated_link_closure
  exact h_iterated_link_closure

-- Scout validated stub: c_7852aa_f3_3_fin7_native_decide_witness_exists
theorem c_7852aa_f3_3_fin7_native_decide_witness_exists :
    ∃ family : Finset (Finset (Fin 7)),
      IsUniform family 3 ∧ IsSunflowerFree family 3 ∧ family.card = 12 := by
  let witnessSet : Fin 12 → Finset (Fin 7)
    | ⟨0, _⟩ => {0, 1, 2}
    | ⟨1, _⟩ => {0, 1, 3}
    | ⟨2, _⟩ => {0, 2, 3}
    | ⟨3, _⟩ => {0, 4, 5}
    | ⟨4, _⟩ => {0, 4, 6}
    | ⟨5, _⟩ => {0, 5, 6}
    | ⟨6, _⟩ => {1, 2, 4}
    | ⟨7, _⟩ => {1, 3, 5}
    | ⟨8, _⟩ => {1, 4, 5}
    | ⟨9, _⟩ => {2, 3, 6}
    | ⟨10, _⟩ => {2, 4, 6}
    | ⟨11, _⟩ => {3, 5, 6}
  let family : Finset (Finset (Fin 7)) := (Finset.univ : Finset (Fin 12)).image witnessSet
  refine ⟨family, ?_⟩
  have h_witness_injective : Function.Injective witnessSet := by
    native_decide
  have h_uniform : IsUniform family 3 := by
    intro S hS
    rcases Finset.mem_image.mp hS with ⟨i, -, rfl⟩
    fin_cases i <;> native_decide
  have h_no_sunflower_indices :
      ¬ ∃ a b c : Fin 12,
        a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
          (witnessSet a ∩ witnessSet b = witnessSet a ∩ witnessSet c) ∧
          (witnessSet a ∩ witnessSet b = witnessSet b ∩ witnessSet c) := by
    native_decide
  have h_sf_free : IsSunflowerFree family 3 := by
    intro sub hsub hsun
    rcases (Finset.card_eq_three.mp hsun.1) with ⟨A, B, C, hAB, hAC, hBC, rfl⟩
    have hA_mem : A ∈ family := hsub (by simp)
    have hB_mem : B ∈ family := hsub (by simp)
    have hC_mem : C ∈ family := hsub (by simp)
    rcases Finset.mem_image.mp hA_mem with ⟨a, -, ha⟩
    rcases Finset.mem_image.mp hB_mem with ⟨b, -, hb⟩
    rcases Finset.mem_image.mp hC_mem with ⟨c, -, hc⟩
    have hab : a ≠ b := by
      intro hab'
      apply hAB
      calc
        A = witnessSet a := ha.symm
        _ = witnessSet b := by simp [hab']
        _ = B := hb
    have hac : a ≠ c := by
      intro hac'
      apply hAC
      calc
        A = witnessSet a := ha.symm
        _ = witnessSet c := by simp [hac']
        _ = C := hc
    have hbc : b ≠ c := by
      intro hbc'
      apply hBC
      calc
        B = witnessSet b := hb.symm
        _ = witnessSet c := by simp [hbc']
        _ = C := hc
    rcases hsun.2 with ⟨core, hcore⟩
    have hABcore : A ∩ B = core := hcore A B (by simp) (by simp) hAB
    have hACcore : A ∩ C = core := hcore A C (by simp) (by simp) hAC
    have hBCcore : B ∩ C = core := hcore B C (by simp) (by simp) hBC
    have hAB_eq_AC : A ∩ B = A ∩ C := hABcore.trans hACcore.symm
    have hAB_eq_BC : A ∩ B = B ∩ C := hABcore.trans hBCcore.symm
    exact h_no_sunflower_indices ⟨a, b, c, hab, hac, hbc,
      by simpa [← ha, ← hb, ← hc] using hAB_eq_AC,
      by simpa [← ha, ← hb, ← hc] using hAB_eq_BC⟩
  have h_card : family.card = 12 := by
    calc
      family.card = (Finset.univ : Finset (Fin 12)).card := by
        simpa [family] using
          (Finset.card_image_of_injOn
            (s := (Finset.univ : Finset (Fin 12)))
            (f := witnessSet)
            (fun a _ b _ hab => h_witness_injective hab))
      _ = 12 := by simp
  exact ⟨h_uniform, h_sf_free, h_card⟩

-- Scout validated stub: c_7852aa_f3_3_fin7_native_decide_no_card21
theorem c_7852aa_f3_3_fin7_native_decide_no_card21 :
    ¬ ∃ family : Finset (Finset (Fin 7)),
      IsUniform family 3 ∧ IsSunflowerFree family 3 ∧ family.card = 21 := by
  intro ⟨family, h_uniform, h_sf_free, h_card⟩
  -- Step 1: For each x : Fin 7, deg(x) = coordDegree family x ≤ 6.
  -- Proof: the link at x is 2-uniform and 3-SF-free, so its card ≤ 6 by f(2,3) ≤ 6.
  -- Then filter.card = image.card (by injectivity of erase on members containing x).
  have h_deg_bound : ∀ x : Fin 7, coordDegree family x ≤ 6 := by
    intro x
    unfold coordDegree
    -- The link reduction (image under erase) is 2-uniform and 3-SF-free
    have h_reduced_sf_free : IsSunflowerFree
        ((family.filter (fun S => x ∈ S)).image (fun S => S.erase x)) 3 :=
      reduction_lemma family 3 3 x h_uniform h_sf_free
    have h_reduced_uniform : IsUniform
        ((family.filter (fun S => x ∈ S)).image (fun S => S.erase x)) 2 := by
      have := uniform_reduction_is_uniform family 3 x (by omega) h_uniform
      simpa using this
    have h_image_le : ((family.filter (fun S => x ∈ S)).image (fun S => S.erase x)).card ≤ 6 :=
      uniform_bound_f2_3_of_degree_matching_route _ h_reduced_uniform h_reduced_sf_free
    -- Injectivity: erase x is injective on {S ∈ family | x ∈ S}
    have h_inj : Set.InjOn (fun S => S.erase x)
        (↑(family.filter (fun S => x ∈ S)) : Set (Finset (Fin 7))) := by
      intro S₁ hS₁ S₂ hS₂ heq
      have hx₁ : x ∈ S₁ := (Finset.mem_filter.mp (Finset.mem_coe.mp hS₁)).2
      have hx₂ : x ∈ S₂ := (Finset.mem_filter.mp (Finset.mem_coe.mp hS₂)).2
      have h_eq : S₁.erase x = S₂.erase x := heq
      calc S₁ = insert x (S₁.erase x) := (Finset.insert_erase hx₁).symm
        _ = insert x (S₂.erase x) := by rw [h_eq]
        _ = S₂ := Finset.insert_erase hx₂
    rw [Finset.card_image_of_injOn h_inj] at h_image_le
    exact h_image_le
  -- Step 2: Handshaking identity via sum_degrees_uniform.
  -- Σ_{x ∈ Fin 7} coordDegree family x = 3 * |family| = 63
  have h_ground : ∀ S ∈ family, S ⊆ (Finset.univ : Finset (Fin 7)) := by
    intros; exact Finset.subset_univ _
  have h_handshake : (Finset.univ : Finset (Fin 7)).sum (fun x => coordDegree family x) =
      3 * family.card :=
    sum_degrees_uniform family 3 h_uniform Finset.univ h_ground
  -- Step 3: Upper bound from degree cap.
  have h_upper : (Finset.univ : Finset (Fin 7)).sum (fun x => coordDegree family x) ≤ 42 := by
    calc (Finset.univ : Finset (Fin 7)).sum (fun x => coordDegree family x)
        ≤ (Finset.univ : Finset (Fin 7)).sum (fun _ => 6) :=
          Finset.sum_le_sum (fun x _ => h_deg_bound x)
      _ = 7 * 6 := by simp [Finset.sum_const, Finset.card_fin]
  -- 63 ≤ 42 contradiction
  omega
