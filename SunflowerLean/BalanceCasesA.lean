import SunflowerLean.UnionBounds

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

/-- Uniform decomposition hypothesis: given that uniform counting bounds hold
    for every layer width, the counting bound holds for an arbitrary (possibly
    non-uniform) family.  The hypothesis captures the hard non-uniform → uniform
    reduction; the bridge theorem lowCaseCountingBoundAll_of_uniform_hyp is then
    a direct corollary.
    Note: the conclusion requires i ∈ ground, matching LowCaseCountingBoundUniform.
    LowCaseCountingBoundAll omits this guard; the bridge keeps a sorry for that gap. -/
def LowCaseUniformDecompositionHyp {α : Type*} [DecidableEq α] : Prop :=
  ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
    IsMaximalSunflowerFree family 3 ground →
    i ∈ ground →
    LowFreq family i →
    (∀ j : ℕ, LowCaseCountingBoundUniform (α := α) j) →
    (BadContaining family ground i).card +
      (InFamilyContaining family ground i).card <
      (CandidatesContaining ground i).card

/-- Bridge: low-case all from small + large hypotheses. -/
theorem lowCaseCountingBoundAll_of_small_and_large {α : Type*} [DecidableEq α] (n₀ : ℕ) :
    LowCaseCountingBoundSmall (α := α) n₀ →
    LowCaseCountingBoundLarge (α := α) n₀ →
    LowCaseCountingBoundAll (α := α) := by
  sorry

/-- Bridge: low-case all from uniform-family theorem + decomposition hypothesis. -/
theorem lowCaseCountingBoundAll_of_uniform_hyp {α : Type*} [DecidableEq α] :
    LowCaseUniformDecompositionHyp (α := α) →
    (∀ k : ℕ, LowCaseCountingBoundUniform (α := α) k) →
    LowCaseCountingBoundAll (α := α) := by
  sorry

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
  intro hcount family ground i hmax hlf
  exact balance_low_case_from_counting family ground i hmax (by
    intro hlf'
    exact hcount family ground i hmax hlf') hlf

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

/-- Large-n high-case target (named hypothesis form). -/
def HighCaseCountingBoundLarge {α : Type*} [DecidableEq α] (n₀ : ℕ) : Prop :=
  ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
    ground.card > n₀ →
    IsMaximalSunflowerFree family 3 ground →
    HighFreq family i →
    (BadAvoiding family ground i).card +
      (InFamilyAvoiding family ground i).card <
      (CandidatesAvoiding ground i).card

/-- Uniform decomposition hypothesis for high-case reduction. -/
def HighCaseUniformDecompositionHyp {α : Type*} [DecidableEq α] : Prop :=
  ∀ (family : Finset (Finset α)) (ground : Finset α) (i : α),
    IsMaximalSunflowerFree family 3 ground →
    HighFreq family i →
    (∀ k : ℕ, HighCaseCountingBoundUniform (α := α) k) →
    (BadAvoiding family ground i).card +
      (InFamilyAvoiding family ground i).card <
      (CandidatesAvoiding ground i).card

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

