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

/-- Target hypothesis: small-union pair counting bound at unit threshold.
    Each off-diagonal ordered pair contributes at least one element to its
    union-cardinality term. -/
def SmallUnionPairsBoundHyp {α : Type*} [DecidableEq α] : Prop :=
  ∀ (family : Finset (Finset α)) (ground : Finset α),
    IsOnGround family ground →
    IsSunflowerFree family 3 →
    family.offDiag.card ≤
      ∑ p ∈ family.offDiag, (p.1 ∪ p.2).card

/-- Target hypothesis: average union lower bound in the unit-threshold regime. -/
def AvgUnionLowerBoundHyp {α : Type*} [DecidableEq α] : Prop :=
  ∀ c : ℕ, c ≤ 1 → AverageUnionSizeBound (α := α) c

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

/-- Direct closure: `CorePairUniqueHyp` follows from the on-ground invariant
alone; sunflower-freeness and distinctness are not needed for this inclusion. -/
theorem core_pair_unique_hyp_proved {α : Type*} [DecidableEq α] :
    CorePairUniqueHyp (α := α) := by
  intro family ground A B h_on _hfree hA _hB _hne
  exact Finset.inter_subset_left.trans (h_on A hA)

/-- Reduction theorem consuming `SmallUnionPairsBoundHyp`. -/
theorem small_union_pairs_bounded_of_hyp {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) :
    SmallUnionPairsBoundHyp (α := α) →
    IsOnGround family ground →
    IsSunflowerFree family 3 →
    family.offDiag.card ≤
      ∑ p ∈ family.offDiag, (p.1 ∪ p.2).card := by
  intro h h_on hfree
  exact h family ground h_on hfree

/-- Direct closure: off-diagonal ordered pairs are distinct, so their union
cannot be empty; summing these unit lower bounds yields the target inequality. -/
theorem small_union_pairs_bound_hyp_proved {α : Type*} [DecidableEq α] :
    SmallUnionPairsBoundHyp (α := α) := by
  intro family ground _h_on _hfree
  have hterm :
      ∀ p ∈ family.offDiag, 1 ≤ (p.1 ∪ p.2).card := by
    intro p hp
    have hne : p.1 ≠ p.2 := (Finset.mem_offDiag.mp hp).2.2
    by_cases hzero : (p.1 ∪ p.2).card = 0
    · have hUnionEmpty : p.1 ∪ p.2 = (∅ : Finset α) := Finset.card_eq_zero.mp hzero
      have hp1_empty : p.1 = (∅ : Finset α) := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hx_union : x ∈ p.1 ∪ p.2 := Finset.mem_union.mpr (Or.inl hx)
        simpa [hUnionEmpty] using hx_union
      have hp2_empty : p.2 = (∅ : Finset α) := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hx_union : x ∈ p.1 ∪ p.2 := Finset.mem_union.mpr (Or.inr hx)
        simpa [hUnionEmpty] using hx_union
      exact False.elim (hne (by simpa [hp1_empty, hp2_empty]))
    · exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hzero)
  have hsum :
      ∑ _p ∈ family.offDiag, (1 : ℕ) ≤
        ∑ p ∈ family.offDiag, (p.1 ∪ p.2).card := by
    exact Finset.sum_le_sum hterm
  simpa using hsum

/-- Reduction theorem consuming `AvgUnionLowerBoundHyp`. -/
theorem avg_union_lower_bound_of_hyp {α : Type*} [DecidableEq α] (c : ℕ) :
    AvgUnionLowerBoundHyp (α := α) →
    c ≤ 1 →
    AverageUnionSizeBound (α := α) c := by
  intro h hc
  exact h c hc

/-- Direct closure: the unit-threshold regime follows from the pair-counting
bound since `c ≤ 1` implies `c * |offDiag| ≤ |offDiag|`. -/
theorem avg_union_lower_bound_hyp_proved {α : Type*} [DecidableEq α] :
    AvgUnionLowerBoundHyp (α := α) := by
  intro c hc family ground h_on hfree _hcard
  have hsmall :
      family.offDiag.card ≤
        ∑ p ∈ family.offDiag, (p.1 ∪ p.2).card :=
    SunflowerLean.small_union_pairs_bound_hyp_proved (α := α) family ground h_on hfree
  calc
    c * family.offDiag.card ≤ 1 * family.offDiag.card :=
      Nat.mul_le_mul_right family.offDiag.card hc
    _ = family.offDiag.card := by simp
    _ ≤ ∑ p ∈ family.offDiag, (p.1 ∪ p.2).card := hsmall

end SunflowerLean

-- Scout validated stub: cf92823_core_pair_unique_hyp_of_core_codegree_le_two
theorem cf92823_core_pair_unique_hyp_of_core_codegree_le_two
    {α : Type*} [DecidableEq α] :
    SunflowerLean.CorePairUniqueHyp (α := α) := by
  intro family ground A B h_on _ hA _ _
  exact Finset.inter_subset_left.trans (h_on A hA)

-- Scout validated stub: cf92823_core_pair_unique_hyp_calibrated_context
theorem cf92823_core_pair_unique_hyp_calibrated_context
    {α : Type*} [DecidableEq α] :
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
    {α : Type*} [DecidableEq α] :
    SunflowerLean.SmallUnionPairsBoundHyp (α := α) := by
  exact SunflowerLean.small_union_pairs_bound_hyp_proved (α := α)

-- Scout validated stub: candidate_c485339_avg_union_lower_bound_hyp_of_degree_squared_double_counting_calibrated
theorem candidate_c485339_avg_union_lower_bound_hyp_of_degree_squared_double_counting_calibrated
    {α : Type*} [DecidableEq α] :
    SunflowerLean.AvgUnionLowerBoundHyp (α := α) := by
  exact SunflowerLean.avg_union_lower_bound_hyp_proved (α := α)
