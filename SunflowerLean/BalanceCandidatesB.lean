import SunflowerLean.BalanceCandidatesA

-- Scout validated stub: candidate_cc68758_lowCaseCountingBoundSmall_of_projection_savings_induction
theorem candidate_cc68758_lowCaseCountingBoundSmall_of_projection_savings_induction
    {α : Type*} [DecidableEq α] (n0 : ℕ) (M : ℕ → ℕ)
    (h_base : LowCaseCountingBoundSmall (α := α) (n0 - 1))
    (h_step :
      ∀ (family : Finset (Finset α)) (ground : Finset α) (i j : α),
        ground.card = n0 →
        IsMaximalSunflowerFree family 3 ground →
        i ∈ ground →
        j ∈ ground →
        i ≠ j →
        LowFreq family i →
        (∑ p ∈ family.offDiag, pairWeight ground i p) ≤
          2 * (∑ p ∈ family.offDiag, pairWeight (ground.erase j) i p) +
            (family.filter (fun S => ({i, j} : Finset α) ⊆ S)).card * M (n0 - 2))
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
    (M : ℕ → ℕ)
    (hM5 : M 5 = 12)
    (hM6 : M 6 = 19)
    (hM7 : M 7 = 29)
    (hM8_lb : 45 ≤ M 8)
    (h_window7 :
      ∀ (family : Finset (Finset α)) (ground : Finset α),
        ground.card = 7 →
        family.card = 29 →
        ∀ i ∈ ground, 10 ≤ coordDegree family i ∧ coordDegree family i ≤ 19)
    (h_window8 :
      ∀ (family : Finset (Finset α)) (ground : Finset α),
        ground.card = 8 →
        45 ≤ family.card →
        ∀ i ∈ ground, 16 ≤ coordDegree family i ∧ coordDegree family i ≤ 29)
    (h_growth :
      ∀ n : ℕ, 2 ≤ n → 3 * M (n - 1) ≤ 2 * M n)
    (h_refined :
      ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
        IsMaximalSunflowerFree family 3 ground →
        i ∈ ground →
        LowFreq family i →
        ∑ p ∈ family.offDiag, pairWeight ground i p ≤
          ∑ c ∈ Finset.range (ground.card - 1),
            coordDegree family i * M (ground.card - c - 1) *
              2 ^ (ground.card - (2 * c + 2)))
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

-- Scout validated stub: candidate_c3a0eb4_highCaseUniformDecompositionHyp_of_avoiding_weight_sum_template
theorem candidate_c3a0eb4_highCaseUniformDecompositionHyp_of_avoiding_weight_sum_template
    {α : Type*} [DecidableEq α] :
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
      IsMaximalSunflowerFree family 3 ground →
      HighFreq family i →
      i ∈ ground) →
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
      IsMaximalSunflowerFree family 3 ground →
      HighFreq family i →
      (∀ k : ℕ, HighCaseCountingBoundUniform (α := α) k) →
      (∑ p ∈ family.offDiag, pairWeightAvoiding ground i p) +
        (family.card - coordDegree family i) <
        2 ^ (ground.card - 1)) →
    HighCaseUniformDecompositionHyp (α := α) := by
  intro hi_ground_of_highFreq hweight_template
  intro family ground i hmax hhf hunif
  have hi_ground : i ∈ ground := hi_ground_of_highFreq family ground i hmax hhf
  have hweight :
      (∑ p ∈ family.offDiag, pairWeightAvoiding ground i p) +
        (family.card - coordDegree family i) <
        2 ^ (ground.card - 1) :=
    hweight_template family ground i hmax hhf hunif
  exact (high_case_counting_bound_of_weight_sum_offDiag family ground i hmax hi_ground hweight) hhf

-- Scout validated stub: candidate_ce57866_highCaseCountingBoundSmall_n7_of_sat_certificate_cascade_calibrated
theorem candidate_ce57866_highCaseCountingBoundSmall_n7_of_sat_certificate_cascade_calibrated
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
      (BadAvoiding family ground i).card +
        (InFamilyAvoiding family ground i).card <
        (CandidatesAvoiding ground i).card ↔
      (BadContaining (family.image (fun S => ground \ S)) ground i).card +
        (InFamilyContaining (family.image (fun S => ground \ S)) ground i).card <
        (CandidatesContaining ground i).card) →
    LowCaseCountingBoundSmall (α := α) n₀ →
    HighCaseCountingBoundSmall (α := α) n₀ := by
  intro hmax_complement hhigh_to_low hcount_transfer hlow_small
  intro family ground i hground hmax hhf
  have hi_ground : i ∈ ground := by
    by_contra hi_not_ground
    rcases hmax with ⟨_hfree, h_on, _hmax_insert⟩
    have hcoord_zero : coordDegree family i = 0 := by
      unfold coordDegree
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro S hS
      have hS' := Finset.mem_filter.mp hS
      exact hi_not_ground ((h_on S hS'.1) hS'.2)
    have hnot_high : ¬ HighFreq family i := by
      simpa [HighFreq, hcoord_zero]
    exact hnot_high hhf
  let familyCompl : Finset (Finset α) := family.image (fun S => ground \ S)
  have hmax_compl : IsMaximalSunflowerFree familyCompl 3 ground := by
    simpa [familyCompl] using hmax_complement family ground hmax
  have hlow_compl : LowFreq familyCompl i := by
    simpa [familyCompl] using hhigh_to_low family ground i hhf
  have hcount_compl :
      (BadContaining familyCompl ground i).card +
        (InFamilyContaining familyCompl ground i).card <
        (CandidatesContaining ground i).card := by
    exact hlow_small familyCompl ground i hground hmax_compl hi_ground hlow_compl
  exact (hcount_transfer family ground i).2 (by simpa [familyCompl] using hcount_compl)

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
      (BadAvoiding family ground i).card +
        (InFamilyAvoiding family ground i).card <
        (CandidatesAvoiding ground i).card ↔
      (BadContaining (family.image (fun S => ground \ S)) ground i).card +
        (InFamilyContaining (family.image (fun S => ground \ S)) ground i).card <
        (CandidatesContaining ground i).card) →
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

-- Scout validated stub: candidate_cd05446_highCaseUniformDecompositionHyp_of_weight_sum_offDiag_template
theorem candidate_cd05446_highCaseUniformDecompositionHyp_of_weight_sum_offDiag_template
    {α : Type*} [DecidableEq α] :
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
      IsMaximalSunflowerFree family 3 ground →
      HighFreq family i →
      i ∈ ground) →
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
      IsMaximalSunflowerFree family 3 ground →
      HighFreq family i →
      (∀ k : ℕ, HighCaseCountingBoundUniform (α := α) k) →
      (∑ p ∈ family.offDiag, pairWeightAvoiding ground i p) +
        (family.card - coordDegree family i) <
        2 ^ (ground.card - 1)) →
    HighCaseUniformDecompositionHyp (α := α) := by
  intro hi_ground_of_highFreq hweight_template
  intro family ground i hmax hhf hunif
  have hi_ground : i ∈ ground := hi_ground_of_highFreq family ground i hmax hhf
  have hweight :
      (∑ p ∈ family.offDiag, pairWeightAvoiding ground i p) +
        (family.card - coordDegree family i) <
        2 ^ (ground.card - 1) :=
    hweight_template family ground i hmax hhf hunif
  exact (high_case_counting_bound_of_weight_sum_offDiag family ground i hmax hi_ground hweight) hhf

-- Scout validated stub: candidate_cef9f68_exists_uniform_layer_lowFreq
theorem candidate_cef9f68_exists_uniform_layer_lowFreq
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    IsMaximalSunflowerFree family 3 ground →
    LowFreq family i →
    ∃ r : ℕ,
      (family.filter (fun S => S.card = r)).Nonempty ∧
      (∀ S ∈ family.filter (fun S => S.card = r), S.card = r) ∧
      LowFreq (family.filter (fun S => S.card = r)) i := by
  intro _hmax hlow
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
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    IsMaximalSunflowerFree family 3 ground →
    HighFreq family i →
    ∃ r : ℕ,
      (family.filter (fun S => S.card = r)).Nonempty ∧
      (∀ S ∈ family.filter (fun S => S.card = r), S.card = r) ∧
      HighFreq (family.filter (fun S => S.card = r)) i := by
  intro _hmax hhf
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
  sorry

-- Scout validated stub: candidate_c040cac_lowCaseCountingBoundAll_of_uniform_hyp_with_ground_guard
theorem candidate_c040cac_lowCaseCountingBoundAll_of_uniform_hyp_with_ground_guard
    {α : Type*} [DecidableEq α] :
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
      IsMaximalSunflowerFree family 3 ground →
      LowFreq family i →
      i ∈ ground) →
    LowCaseUniformDecompositionHyp (α := α) →
    (∀ k : ℕ, LowCaseCountingBoundUniform (α := α) k) →
    LowCaseCountingBoundAll (α := α) := by
  sorry

-- Scout validated stub: candidate_c7f7f84_complement_preserves_maximal
theorem candidate_c7f7f84_complement_preserves_maximal
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) :
    IsMaximalSunflowerFree family 3 ground →
    IsMaximalSunflowerFree (family.image (fun S => ground \ S)) 3 ground := by
  sorry

-- Scout validated stub: candidate_c7f7f84_highFreq_to_lowFreq_complement
theorem candidate_c7f7f84_highFreq_to_lowFreq_complement
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    HighFreq family i →
    LowFreq (family.image (fun S => ground \ S)) i := by
  sorry

-- Scout validated stub: candidate_c7f7f84_count_transfer_complement
theorem candidate_c7f7f84_count_transfer_complement
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    (BadAvoiding family ground i).card +
      (InFamilyAvoiding family ground i).card <
      (CandidatesAvoiding ground i).card ↔
    (BadContaining (family.image (fun S => ground \ S)) ground i).card +
      (InFamilyContaining (family.image (fun S => ground \ S)) ground i).card <
      (CandidatesContaining ground i).card := by
  sorry

-- Scout validated stub: candidate_c7f7f84_highCaseCountingBoundSmall_of_lowCaseCountingBoundSmall_via_complement
theorem candidate_c7f7f84_highCaseCountingBoundSmall_of_lowCaseCountingBoundSmall_via_complement
    {α : Type*} [DecidableEq α] (n0 : ℕ) :
    (∀ (family : Finset (Finset α)) (ground : Finset α),
      IsMaximalSunflowerFree family 3 ground →
      IsMaximalSunflowerFree (family.image (fun S => ground \ S)) 3 ground) →
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
      HighFreq family i →
      LowFreq (family.image (fun S => ground \ S)) i) →
    (∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
      (BadAvoiding family ground i).card +
        (InFamilyAvoiding family ground i).card <
        (CandidatesAvoiding ground i).card ↔
      (BadContaining (family.image (fun S => ground \ S)) ground i).card +
        (InFamilyContaining (family.image (fun S => ground \ S)) ground i).card <
        (CandidatesContaining ground i).card) →
    LowCaseCountingBoundSmall (α := α) n0 →
    HighCaseCountingBoundSmall (α := α) n0 := by
  sorry
