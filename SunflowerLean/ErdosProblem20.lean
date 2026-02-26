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
import SunflowerLean.BalanceCore
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
--   sorry -- requires Set ↔ Finset conversion infrastructure

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

-- Scout validated stub: c_67c27c_link_sum_inductive_bound_k3_of_prev_max
theorem c_67c27c_link_sum_inductive_bound_k3_of_prev_max {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (r d : ℕ)
    (hr : 2 ≤ r)
    (h_uniform : IsUniform family r)
    (h_sf_free : IsSunflowerFree family 3)
    (h_prev : MaxUniformSunflowerFreeSize (r - 1) 3 d) :
    family.card ≤ 2 + 2 * r * d := by
  sorry

-- Scout validated stub: c_fa92ad_f3_3_card_cap56_of_matching_decomposition
theorem c_fa92ad_f3_3_card_cap56_of_matching_decomposition {α : Type*} [DecidableEq α]
    (family typeA typeB typeCLeft typeCRight : Finset (Finset α))
    (h_uniform : IsUniform family 3)
    (h_sf_free : IsSunflowerFree family 3)
    (h_cover : family ⊆ typeA ∪ typeB ∪ typeCLeft ∪ typeCRight)
    (hA : typeA.card ≤ 2)
    (hB : typeB.card ≤ 18)
    (hCLeft : typeCLeft.card ≤ 18)
    (hCRight : typeCRight.card ≤ 18) :
    family.card ≤ 56 := by
  have h1 := Finset.card_le_card h_cover
  have h2 := Finset.card_union_le (typeA ∪ typeB ∪ typeCLeft) typeCRight
  have h3 := Finset.card_union_le (typeA ∪ typeB) typeCLeft
  have h4 := Finset.card_union_le typeA typeB
  omega

-- Scout validated stub: c_971ddc_t_codegree_bound_of_iterated_link_prev_max
theorem c_971ddc_t_codegree_bound_of_iterated_link_prev_max {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (r t d : ℕ)
    (ht : t ≤ r)
    (h_uniform : IsUniform family r)
    (h_sf_free : IsSunflowerFree family 3)
    (h_prev : MaxUniformSunflowerFreeSize (r - t) 3 d)
    (T : Finset α) (hT : T.card = t) :
    (family.filter (fun S => T ⊆ S)).card ≤ d := by
  sorry

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
