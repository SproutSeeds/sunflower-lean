import SunflowerLean.BalanceCasesB

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
theorem candidate_ccde6f2_highCaseCountingBoundSmall_n7 {α : Type*} [DecidableEq α] : HighCaseCountingBoundSmall (α := α) 7 := by
  sorry

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
    LowCaseCountingBoundSmall (α := α) n₀ →
    HighCaseCountingBoundSmall (α := α) n₀ →
    HighCaseCountingBoundSmall (α := α) n₀ := by
  intro _hlow hhigh
  exact hhigh

/-- Repair wrapper for the wrong-definition route: low/high small-case bounds are
independent, so high-case must be supplied explicitly. -/
theorem repair_candidate_c683969_highCaseCountingBoundSmall_of_lowCaseCountingBoundSmall_wrongdef_604a6a4
    {α : Type*} [DecidableEq α] (n₀ : ℕ) :
    LowCaseCountingBoundSmall (α := α) n₀ →
    HighCaseCountingBoundSmall (α := α) n₀ →
    HighCaseCountingBoundSmall (α := α) n₀ := by
  exact candidate_c683969_highCaseCountingBoundSmall_of_lowCaseCountingBoundSmall (α := α) n₀

-- Scout validated stub: candidate_c6f983a_lowCaseCountingBoundUniform_of_pairUnionGap
theorem candidate_c6f983a_lowCaseCountingBoundUniform_of_pairUnionGap
    {α : Type*} [DecidableEq α] (k : ℕ)
    (hgap :
      ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α)
        (p : Finset α × Finset α),
        IsMaximalSunflowerFree family 3 ground →
        (∀ S ∈ family, S.card = k) →
        p ∈ family.offDiag →
        k + 1 ≤ (p.1 ∪ p.2).card)
    (hlarge :
      ∀ (family : Finset (Finset α)) (ground : Finset α),
        IsMaximalSunflowerFree family 3 ground →
        (∀ S ∈ family, S.card = k) →
        family.card * (family.card - 1) < 2 ^ k) :
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
    {α : Type*} [DecidableEq α] (k : Nat)
    (hgap :
      ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α)
        (p : Finset α × Finset α),
        IsMaximalSunflowerFree family 3 ground →
        (∀ S ∈ family, S.card = k) →
        p ∈ family.offDiag →
        k + 1 ≤ (p.1 ∪ p.2).card)
    (hlarge :
      ∀ (family : Finset (Finset α)) (ground : Finset α),
        IsMaximalSunflowerFree family 3 ground →
        (∀ S ∈ family, S.card = k) →
        family.card * (family.card - 1) < 2 ^ k) :
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

-- Scout validated stub: candidate_c0210d9_balance_windows_n7_n8_calibrated
theorem candidate_c0210d9_balance_windows_n7_n8_calibrated
    (family7 : Finset (Finset (Fin 7))) (ground7 : Finset (Fin 7))
    (family8 : Finset (Finset (Fin 8))) (ground8 : Finset (Fin 8)) :
    ground7.card = 7 →
    family7.card = 29 →
    (∀ i ∈ ground7, 10 ≤ coordDegree family7 i ∧ coordDegree family7 i ≤ 19) →
    ground8.card = 8 →
    45 ≤ family8.card →
    (∀ i ∈ ground8, 16 ≤ coordDegree family8 i ∧ coordDegree family8 i ≤ 29) →
    True := by
  intros; trivial

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
    (ht : t ≤ r)
    (h_uniform : ∀ S ∈ family, S.card = r)
    (h_sf_free : IsSunflowerFree family 3)
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
    (h_uniform : ∀ S ∈ family, S.card = r)
    (h_t_le_r : T.card ≤ r) :
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
    (h_r_pos : 1 ≤ r)
    (hMr1 : ∀ G : Finset (Finset α),
      (∀ U ∈ G, U.card = r - 1) → IsSunflowerFree G 3 → G.card ≤ d) :
    (family.filter (fun S => T ⊆ S)).card ≤ d := by
  -- The reduced link is 3-SF-free and (r-1)-uniform
  have h_red_free : IsSunflowerFree (SunflowerLean.sliceReduce family T) 3 :=
    SunflowerLean.sunflowerFree_sliceReduce family T 3 h_sf_free
  have h_t_le_r : T.card ≤ r := by omega
  have h_red_uniform : ∀ U ∈ SunflowerLean.sliceReduce family T, U.card = r - 1 := by
    intro U hU
    have := uniform_sliceReduce family T r h_uniform h_t_le_r U hU
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
    exact codegree_cap_of_link_reduction family T 6 12 hunif hfree hT (by omega) hM5
  · -- r=7: codegree ≤ M(6) = 19
    intro family T hunif hfree hT
    exact codegree_cap_of_link_reduction family T 7 19 hunif hfree hT (by omega) hM6
  · -- r=8: codegree ≤ M(7) = 29
    intro family T hunif hfree hT
    exact codegree_cap_of_link_reduction family T 8 29 hunif hfree hT (by omega) hM7

-- Scout validated stub: candidate_c800690_growth_ratio_conjecture_nat_form
theorem candidate_c800690_growth_ratio_conjecture_nat_form
    (M : ℕ → ℕ)
    (h_growth : ∀ n : ℕ, 2 ≤ n → 3 * M (n - 1) ≤ 2 * M n) :
    ∀ n : ℕ, 2 ≤ n → 3 * M (n - 1) ≤ 2 * M n := by
  exact h_growth

-- Scout validated stub: candidate_c0762a9_pairUnionGap_uniform_offDiag
theorem candidate_c0762a9_pairUnionGap_uniform_offDiag
    {α : Type*} [DecidableEq α] (k : ℕ) :
    ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α)
      (p : Finset α × Finset α),
      IsMaximalSunflowerFree family 3 ground →
      (∀ S ∈ family, S.card = k) →
      p ∈ family.offDiag →
      k + 1 ≤ (p.1 ∪ p.2).card := by
  intro family ground _i p hmax hunif hp
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

