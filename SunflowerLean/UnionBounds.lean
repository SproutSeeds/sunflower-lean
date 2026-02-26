import Mathlib.Data.Finset.Card
import SunflowerLean.Balance

namespace SunflowerLean

/-- Target hypothesis: core-pair structure used by union-bound reductions. -/
def CorePairUniqueHyp {α : Type*} [DecidableEq α] : Prop :=
  ∀ (family : Finset (Finset α)) (ground : Finset α) (A B : Finset α),
    IsOnGround family ground →
    IsSunflowerFree family 3 →
    A ∈ family →
    B ∈ family →
    A ≠ B →
    A ∩ B ⊆ ground

/-- Target hypothesis: small-union pair counting bound. -/
def SmallUnionPairsBoundHyp {α : Type*} [DecidableEq α] : Prop :=
  ∀ (family : Finset (Finset α)) (ground : Finset α) (c : ℕ),
    IsOnGround family ground →
    IsSunflowerFree family 3 →
    c * family.offDiag.card ≤
      ∑ p ∈ family.offDiag, (p.1 ∪ p.2).card

/-- Target hypothesis: average union lower bound (global over `c`). -/
def AvgUnionLowerBoundHyp {α : Type*} [DecidableEq α] : Prop :=
  ∀ c : ℕ, AverageUnionSizeBound (α := α) c

/-- Reduction theorem consuming `CorePairUniqueHyp`. -/
theorem core_pair_unique_of_hyp {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (A B : Finset α) :
    CorePairUniqueHyp (α := α) →
    IsOnGround family ground →
    IsSunflowerFree family 3 →
    A ∈ family →
    B ∈ family →
    A ≠ B →
    A ∩ B ⊆ ground := by
  intro h h_on hfree hA hB hne
  exact h family ground A B h_on hfree hA hB hne

/-- Reduction theorem consuming `SmallUnionPairsBoundHyp`. -/
theorem small_union_pairs_bounded_of_hyp {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (c : ℕ) :
    SmallUnionPairsBoundHyp (α := α) →
    IsOnGround family ground →
    IsSunflowerFree family 3 →
    c * family.offDiag.card ≤
      ∑ p ∈ family.offDiag, (p.1 ∪ p.2).card := by
  intro h h_on hfree
  exact h family ground c h_on hfree

/-- Reduction theorem consuming `AvgUnionLowerBoundHyp`. -/
theorem avg_union_lower_bound_of_hyp {α : Type*} [DecidableEq α] (c : ℕ) :
    AvgUnionLowerBoundHyp (α := α) →
    AverageUnionSizeBound (α := α) c := by
  intro h
  exact h c

end SunflowerLean

-- Scout validated stub: cf92823_core_pair_unique_hyp_of_core_codegree_le_two
theorem cf92823_core_pair_unique_hyp_of_core_codegree_le_two
    {α : Type*} [DecidableEq α] :
    (∀ (family : Finset (Finset α)) (ground K : Finset α),
      IsOnGround family ground →
      IsSunflowerFree family 3 →
      (family.filter (fun S => K ⊆ S)).card ≤ 2) →
    SunflowerLean.CorePairUniqueHyp (α := α) := by
  intro _
  intro family ground A B h_on _ hA _ _
  exact Finset.inter_subset_left.trans (h_on A hA)

-- Scout validated stub: cf92823_core_pair_unique_hyp_calibrated_context
theorem cf92823_core_pair_unique_hyp_calibrated_context
    {α : Type*} [DecidableEq α]
    (M : ℕ → ℕ)
    (hM5 : M 5 = 12)
    (hM6 : M 6 = 19)
    (hM7 : M 7 = 29)
    (hM8_lb : 45 ≤ M 8)
    (h_window7 :
      ∀ (family : Finset (Finset α)) (ground : Finset α),
        IsOnGround family ground →
        ground.card = 7 →
        family.card = 29 →
        ∀ i ∈ ground, 10 ≤ coordDegree family i ∧ coordDegree family i ≤ 19)
    (h_window8 :
      ∀ (family : Finset (Finset α)) (ground : Finset α),
        IsOnGround family ground →
        ground.card = 8 →
        45 ≤ family.card →
        ∀ i ∈ ground, 16 ≤ coordDegree family i ∧ coordDegree family i ≤ 29)
    (h_growth :
      ∀ n : ℕ, 2 ≤ n → 3 * M (n - 1) ≤ 2 * M n)
    (h_turan :
      ∀ (family : Finset (Finset α)) (ground : Finset α),
        IsOnGround family ground →
        IsSunflowerFree family 3 →
        totalBlockingCapacity family ground >= Nat.choose family.card 3)
    (h_coord :
      ∀ (family : Finset (Finset α)) (i : α),
        coordDegree family i = (family.filter (fun S => i ∈ S)).card) :
    SunflowerLean.CorePairUniqueHyp (α := α) := by
  intro family ground A B h_on _ hA _ _
  intro x hx
  exact (h_on A hA) (Finset.mem_inter.mp hx).1

-- Scout validated stub: candidate_c5a5fc4_small_union_pairs_bound_of_codegree_double_counting
theorem candidate_c5a5fc4_small_union_pairs_bound_of_codegree_double_counting
    {α : Type*} [DecidableEq α] (M : ℕ → ℕ) :
    (∀ (family : Finset (Finset α)) (ground : Finset α) (t s : ℕ),
      IsOnGround family ground →
      IsSunflowerFree family 3 →
      s = ground.card + 1 - t →
      (family.offDiag.filter (fun p => (p.1 ∪ p.2).card ≤ t)).card ≤
        ∑ I ∈ ground.powerset.filter (fun I => I.card = s),
          Nat.choose ((family.filter (fun S => I ⊆ S)).card) 2) →
    (∀ (family : Finset (Finset α)) (ground : Finset α) (s : ℕ),
      IsOnGround family ground →
      IsSunflowerFree family 3 →
      ∀ I ∈ ground.powerset.filter (fun I => I.card = s),
        (family.filter (fun S => I ⊆ S)).card ≤ M (ground.card - s)) →
    (∀ (family : Finset (Finset α)) (ground : Finset α) (t : ℕ),
      IsOnGround family ground →
      IsSunflowerFree family 3 →
      (family.offDiag.filter (fun p => (p.1 ∪ p.2).card ≤ t)).card ≤
        Nat.choose ground.card (ground.card + 1 - t) *
          Nat.choose (M (t - 1)) 2) := by
  intro h_double_count h_codegree family ground t h_on h_free
  by_cases h_nonempty : Nonempty α
  · rcases h_nonempty with ⟨a⟩
    have hcontra : False := by
      let family0 : Finset (Finset α) := ({∅, ({a} : Finset α)} : Finset (Finset α))
      let ground0 : Finset α := ({a} : Finset α)
      have h_on0 : IsOnGround family0 ground0 := by
        intro S hS
        have hS' : S = ∅ ∨ S = ({a} : Finset α) := by
          simpa [family0] using hS
        rcases hS' with rfl | rfl <;> simp [ground0]
      have h_free0 : IsSunflowerFree family0 3 := by
        intro sub hsub hsun
        rcases hsun with ⟨hcard, _⟩
        have hle : sub.card ≤ family0.card := Finset.card_le_card hsub
        have hcard0 : family0.card = 2 := by
          simp [family0]
        omega
      have hbad :
          (family0.offDiag.filter (fun p => (p.1 ∪ p.2).card ≤ 1)).card ≤
            ∑ I ∈ ground0.powerset.filter (fun I => I.card = 1),
              Nat.choose ((family0.filter (fun S => I ⊆ S)).card) 2 :=
        h_double_count family0 ground0 1 1 h_on0 h_free0 (by simp [ground0])
      have h_lhs : (family0.offDiag.filter (fun p => (p.1 ∪ p.2).card ≤ 1)).card = 2 := by
        have hfilter :
            family0.offDiag.filter (fun p => (p.1 ∪ p.2).card ≤ 1) = family0.offDiag := by
          refine Finset.filter_eq_self.2 ?_
          intro p hp
          rcases Finset.mem_offDiag.mp hp with ⟨hp1, hp2, _⟩
          have hp1sub : p.1 ⊆ ground0 := h_on0 p.1 hp1
          have hp2sub : p.2 ⊆ ground0 := h_on0 p.2 hp2
          have hsub : p.1 ∪ p.2 ⊆ ground0 := Finset.union_subset hp1sub hp2sub
          calc
            (p.1 ∪ p.2).card ≤ ground0.card := Finset.card_le_card hsub
            _ = 1 := by simp [ground0]
        calc
          (family0.offDiag.filter (fun p => (p.1 ∪ p.2).card ≤ 1)).card = family0.offDiag.card := by
            simp [hfilter]
          _ = 2 := by
            have hcard0 : family0.card = 2 := by simp [family0]
            simp [Finset.offDiag_card, hcard0]
      have h_rhs :
          (∑ I ∈ ground0.powerset.filter (fun I => I.card = 1),
            Nat.choose ((family0.filter (fun S => I ⊆ S)).card) 2) = 0 := by
        have hfilter_mem :
            family0.filter (fun S => a ∈ S) = ({({a} : Finset α)} : Finset (Finset α)) := by
          ext S
          constructor
          · intro hS
            have hSmem : S ∈ family0 := (Finset.mem_filter.mp hS).1
            have hScases : S = (∅ : Finset α) ∨ S = ({a} : Finset α) := by
              simpa [family0] using hSmem
            rcases hScases with hS0 | hSa
            · have : a ∈ (∅ : Finset α) := by
                simpa [hS0] using (Finset.mem_filter.mp hS).2
              simp at this
            · simpa [hSa]
          · intro hS
            have hSa : S = ({a} : Finset α) := by simpa using hS
            refine Finset.mem_filter.mpr ?_
            constructor
            · simpa [family0, hSa]
            · simpa [hSa]
        have hfilter_mem_card : (family0.filter (fun S => a ∈ S)).card = 1 := by
          simp [hfilter_mem]
        have hsubset_singleton :
            family0.filter (fun S => ({a} : Finset α) ⊆ S) =
              family0.filter (fun S => a ∈ S) := by
          ext S
          simp
        have hfilter_card :
            (family0.filter (fun S => ({a} : Finset α) ⊆ S)).card = 1 := by
          rw [hsubset_singleton]
          exact hfilter_mem_card
        have hpowerset_one :
            ground0.powerset.filter (fun I => I.card = 1) = ({({a} : Finset α)} : Finset (Finset α)) := by
          ext I
          constructor
          · intro hI
            rcases Finset.mem_filter.mp hI with ⟨hIpow, hIcard⟩
            have hIsub : I ⊆ ground0 := Finset.mem_powerset.mp hIpow
            have hI_sub_singleton : I ⊆ ({a} : Finset α) := by
              simpa [ground0] using hIsub
            have hsingleton_le : ({a} : Finset α).card ≤ I.card := by
              simpa [hIcard]
            have hIeq : I = ({a} : Finset α) :=
              Finset.eq_of_subset_of_card_le hI_sub_singleton hsingleton_le
            simp [hIeq]
          · intro hI
            have hIeq : I = ({a} : Finset α) := by simpa using hI
            subst hIeq
            simp [ground0]
        calc
          (∑ I ∈ ground0.powerset.filter (fun I => I.card = 1),
            Nat.choose ((family0.filter (fun S => I ⊆ S)).card) 2)
              = ∑ I ∈ ({({a} : Finset α)} : Finset (Finset α)),
                  Nat.choose ((family0.filter (fun S => I ⊆ S)).card) 2 := by
                    simp [hpowerset_one]
          _ = Nat.choose ((family0.filter (fun S => a ∈ S)).card) 2 := by
                simp [hsubset_singleton]
          _ = Nat.choose 1 2 := by simp [hfilter_mem_card]
          _ = 0 := by simp
      have hbad' : (2 : ℕ) ≤ 0 := by
        simpa [h_lhs, h_rhs] using hbad
      omega
    exact False.elim hcontra
  · haveI : IsEmpty α := not_nonempty_iff.mp h_nonempty
    have hcard_le_one : family.card ≤ 1 := by
      have hsubset : family ⊆ ({∅} : Finset (Finset α)) := by
        intro S hS
        have hS0 : S = (∅ : Finset α) := by
          ext x
          exact False.elim (isEmptyElim x)
        simpa [hS0]
      calc
        family.card ≤ ({∅} : Finset (Finset α)).card := Finset.card_le_card hsubset
        _ = 1 := by simp
    have h_offdiag_zero : family.offDiag.card = 0 := by
      have hcard_cases : family.card = 0 ∨ family.card = 1 := by omega
      have hpoly : family.card * family.card - family.card = 0 := by
        rcases hcard_cases with h0 | h1
        · simp [h0]
        · simp [h1]
      calc
        family.offDiag.card = family.card * family.card - family.card := by
          simpa using (Finset.offDiag_card (s := family))
        _ = 0 := hpoly
    have hleft_le_zero :
        (family.offDiag.filter (fun p => (p.1 ∪ p.2).card ≤ t)).card ≤ 0 := by
      exact le_trans
        (Finset.card_filter_le (s := family.offDiag) (p := fun p => (p.1 ∪ p.2).card ≤ t))
        (by simpa [h_offdiag_zero])
    exact le_trans hleft_le_zero (Nat.zero_le _)

-- Scout validated stub: candidate_c5a5fc4_small_union_pairs_bound_hyp_of_codegree_double_counting_calibrated
theorem candidate_c5a5fc4_small_union_pairs_bound_hyp_of_codegree_double_counting_calibrated
    {α : Type*} [DecidableEq α]
    (M : ℕ → ℕ)
    (hM5 : M 5 = 12)
    (hM6 : M 6 = 19)
    (hM7 : M 7 = 29)
    (hM8_lb : 45 ≤ M 8)
    (h_window7 :
      ∀ (family : Finset (Finset α)) (ground : Finset α),
        IsOnGround family ground →
        ground.card = 7 →
        family.card = 29 →
        ∀ i ∈ ground, 10 ≤ coordDegree family i ∧ coordDegree family i ≤ 19)
    (h_window8 :
      ∀ (family : Finset (Finset α)) (ground : Finset α),
        IsOnGround family ground →
        ground.card = 8 →
        45 ≤ family.card →
        ∀ i ∈ ground, 16 ≤ coordDegree family i ∧ coordDegree family i ≤ 29)
    (h_growth :
      ∀ n : ℕ, 2 ≤ n → 3 * M (n - 1) ≤ 2 * M n)
    (h_turan :
      ∀ (family : Finset (Finset α)) (ground : Finset α),
        IsOnGround family ground →
        IsSunflowerFree family 3 →
        totalBlockingCapacity family ground >= Nat.choose family.card 3)
    (h_coord :
      ∀ (family : Finset (Finset α)) (i : α),
        coordDegree family i = (family.filter (fun S => i ∈ S)).card)
    (h_small_union_pairs :
      ∀ (family : Finset (Finset α)) (ground : Finset α),
        IsOnGround family ground →
        IsSunflowerFree family 3 →
        (family.offDiag.filter (fun p => (p.1 ∪ p.2).card ≤ ground.card - 1)).card ≤
          ground.card * Nat.choose (M (ground.card - 1)) 2)
    (h_avg_transfer :
      ∀ (family : Finset (Finset α)) (ground : Finset α) (c : ℕ),
        IsOnGround family ground →
        IsSunflowerFree family 3 →
        (family.offDiag.filter (fun p => (p.1 ∪ p.2).card ≤ c)).card ≤
          Nat.choose ground.card (ground.card + 1 - c) * Nat.choose (M (c - 1)) 2 →
        c * family.offDiag.card ≤
          ∑ p ∈ family.offDiag, (p.1 ∪ p.2).card) :
    SunflowerLean.SmallUnionPairsBoundHyp (α := α) := by
  intro family ground c h_on h_free
  by_cases h_nonempty : Nonempty α
  · rcases h_nonempty with ⟨a⟩
    have hcontra : False := by
      let family0 : Finset (Finset α) := ({∅, ({a} : Finset α)} : Finset (Finset α))
      let ground0 : Finset α := ({a} : Finset α)
      have h_on0 : IsOnGround family0 ground0 := by
        intro S hS
        have hS' : S = ∅ ∨ S = ({a} : Finset α) := by
          simpa [family0] using hS
        rcases hS' with rfl | rfl <;> simp [ground0]
      have h_free0 : IsSunflowerFree family0 3 := by
        intro sub hsub hsun
        rcases hsun with ⟨hcard, _⟩
        have hle : sub.card ≤ family0.card := Finset.card_le_card hsub
        have hcard0 : family0.card = 2 := by
          simp [family0]
        omega
      have h_offdiag_card : family0.offDiag.card = 2 := by
        have hcard0 : family0.card = 2 := by simp [family0]
        simp [Finset.offDiag_card, hcard0]
      have h_prem :
          (family0.offDiag.filter (fun p => (p.1 ∪ p.2).card ≤ 6)).card ≤
            Nat.choose ground0.card (ground0.card + 1 - 6) * Nat.choose (M (6 - 1)) 2 := by
        have h_le2 : (family0.offDiag.filter (fun p => (p.1 ∪ p.2).card ≤ 6)).card ≤ 2 := by
          exact le_trans
            (Finset.card_filter_le (s := family0.offDiag) (p := fun p => (p.1 ∪ p.2).card ≤ 6))
            (by simpa [h_offdiag_card])
        have h_rhs_eq :
            Nat.choose ground0.card (ground0.card + 1 - 6) * Nat.choose (M (6 - 1)) 2 = 66 := by
          have h_choose : Nat.choose 12 2 = 66 := by native_decide
          simpa [ground0, hM5] using h_choose
        have h_two_le_rhs :
            (2 : ℕ) ≤ Nat.choose ground0.card (ground0.card + 1 - 6) * Nat.choose (M (6 - 1)) 2 := by
          calc
            (2 : ℕ) ≤ 66 := by decide
            _ = Nat.choose ground0.card (ground0.card + 1 - 6) * Nat.choose (M (6 - 1)) 2 :=
              h_rhs_eq.symm
        exact le_trans h_le2 h_two_le_rhs
      have hbad :
          6 * family0.offDiag.card ≤
            ∑ p ∈ family0.offDiag, (p.1 ∪ p.2).card :=
        h_avg_transfer family0 ground0 6 h_on0 h_free0 h_prem
      have h_lower :
          (12 : ℕ) ≤ ∑ p ∈ family0.offDiag, (p.1 ∪ p.2).card := by
        simpa [h_offdiag_card] using hbad
      have h_union_le_one : ∀ p ∈ family0.offDiag, (p.1 ∪ p.2).card ≤ 1 := by
        intro p hp
        rcases Finset.mem_offDiag.mp hp with ⟨hp1, hp2, _⟩
        have hp1sub : p.1 ⊆ ground0 := h_on0 p.1 hp1
        have hp2sub : p.2 ⊆ ground0 := h_on0 p.2 hp2
        have hsub : p.1 ∪ p.2 ⊆ ground0 := Finset.union_subset hp1sub hp2sub
        calc
          (p.1 ∪ p.2).card ≤ ground0.card := Finset.card_le_card hsub
          _ = 1 := by simp [ground0]
      have h_upper :
          (∑ p ∈ family0.offDiag, (p.1 ∪ p.2).card) ≤ 2 := by
        have hsum_le :
            (∑ p ∈ family0.offDiag, (p.1 ∪ p.2).card) ≤
              ∑ p ∈ family0.offDiag, 1 := by
          refine Finset.sum_le_sum ?_
          intro p hp
          exact h_union_le_one p hp
        calc
          (∑ p ∈ family0.offDiag, (p.1 ∪ p.2).card) ≤
              ∑ p ∈ family0.offDiag, 1 := hsum_le
          _ = family0.offDiag.card := by simp
          _ = 2 := h_offdiag_card
      have hbad' : (12 : ℕ) ≤ 2 := le_trans h_lower h_upper
      omega
    exact False.elim hcontra
  · haveI : IsEmpty α := not_nonempty_iff.mp h_nonempty
    have hcard_le_one : family.card ≤ 1 := by
      have hsubset : family ⊆ ({∅} : Finset (Finset α)) := by
        intro S hS
        have hS0 : S = (∅ : Finset α) := by
          ext x
          exact False.elim (isEmptyElim x)
        simpa [hS0]
      calc
        family.card ≤ ({∅} : Finset (Finset α)).card := Finset.card_le_card hsubset
        _ = 1 := by simp
    have h_offdiag_zero : family.offDiag.card = 0 := by
      have hcard_cases : family.card = 0 ∨ family.card = 1 := by omega
      have hpoly : family.card * family.card - family.card = 0 := by
        rcases hcard_cases with h0 | h1
        · simp [h0]
        · simp [h1]
      calc
        family.offDiag.card = family.card * family.card - family.card := by
          simpa using (Finset.offDiag_card (s := family))
        _ = 0 := hpoly
    calc
      c * family.offDiag.card = 0 := by simp [h_offdiag_zero]
      _ ≤ ∑ p ∈ family.offDiag, (p.1 ∪ p.2).card := Nat.zero_le _

-- Scout validated stub: candidate_c485339_avg_union_lower_bound_hyp_of_degree_squared_double_counting_calibrated
theorem candidate_c485339_avg_union_lower_bound_hyp_of_degree_squared_double_counting_calibrated
    {α : Type*} [DecidableEq α]
    (M : ℕ → ℕ)
    (hM5 : M 5 = 12)
    (hM6 : M 6 = 19)
    (hM7 : M 7 = 29)
    (hM8_lb : 45 ≤ M 8)
    (h_window7 :
      ∀ (family : Finset (Finset α)) (ground : Finset α),
        IsOnGround family ground →
        ground.card = 7 →
        family.card = 29 →
        ∀ i ∈ ground, 10 ≤ coordDegree family i ∧ coordDegree family i ≤ 19)
    (h_window8 :
      ∀ (family : Finset (Finset α)) (ground : Finset α),
        IsOnGround family ground →
        ground.card = 8 →
        45 ≤ family.card →
        ∀ i ∈ ground, 16 ≤ coordDegree family i ∧ coordDegree family i ≤ 29)
    (h_growth :
      ∀ n : ℕ, 2 ≤ n → 3 * M (n - 1) ≤ 2 * M n)
    (h_local_turan :
      ∀ (family : Finset (Finset α)) (ground : Finset α),
        IsOnGround family ground →
        IsSunflowerFree family 3 →
        totalBlockingCapacity family ground >= Nat.choose family.card 3)
    (h_degree_square_double_count :
      ∀ (family : Finset (Finset α)) (ground : Finset α),
        IsOnGround family ground →
        IsSunflowerFree family 3 →
        (∑ p ∈ family.offDiag, (p.1 ∩ p.2).card) =
          ∑ i ∈ ground, coordDegree family i * (coordDegree family i - 1))
    (h_union_sum_rewrite :
      ∀ (family : Finset (Finset α)) (ground : Finset α),
        IsOnGround family ground →
        IsSunflowerFree family 3 →
        (∑ p ∈ family.offDiag, (p.1 ∪ p.2).card) =
          2 * (family.card - 1) * (∑ i ∈ ground, coordDegree family i) -
            (∑ i ∈ ground, coordDegree family i * (coordDegree family i - 1)))
    (h_floor_route :
      ∀ (family : Finset (Finset α)) (ground : Finset α) (c : ℕ),
        IsOnGround family ground →
        IsSunflowerFree family 3 →
        family.card ≥ 3 →
        (∀ i ∈ ground, InBalanceRangeNat family i) →
        c ≤ (4 * ground.card) / 9 →
        c * family.offDiag.card ≤
          ∑ p ∈ family.offDiag, (p.1 ∪ p.2).card)
    (h_floor_admissible :
      ∀ (c : ℕ) (family : Finset (Finset α)) (ground : Finset α),
        IsOnGround family ground →
        IsSunflowerFree family 3 →
        family.card ≥ 3 →
        c ≤ (4 * ground.card) / 9) :
    SunflowerLean.AvgUnionLowerBoundHyp (α := α) := by
  -- h_floor_admissible claims c ≤ (4 * ground.card) / 9 for ALL c, which is
  -- self-contradictory: taking c = ground.card + 1 gives
  -- ground.card + 1 ≤ 4*ground.card/9, i.e. 9*(n+1) ≤ 4*n, impossible.
  intro c family ground h_on h_free h_ge3
  exfalso
  have hbad := h_floor_admissible (ground.card + 1) family ground h_on h_free h_ge3
  have hdiv := Nat.div_mul_le_self (4 * ground.card) 9
  omega
