import SunflowerLean.BalanceCasesA

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
    ¬ LowFreq family i := by
  intro hmax hlow hlf
  have h_add : AddableContaining family ground i := hlow family ground i hmax hlf
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
  intro h_not_low h_not_high
  simp only [LowFreq, HighFreq, InBalanceRangeNat] at *
  constructor
  · -- ¬ (3*d_i < |F|) implies |F| ≤ 3*d_i
    exact Nat.le_of_not_gt h_not_low
  · -- ¬ (2*|F| < 3*d_i) implies 3*d_i ≤ 2*|F|
    exact Nat.le_of_not_gt h_not_high

/-- Nat-form balance bound follows from the low/high case conjectures and maximality. -/
theorem balance_conjecture_nat_of_cases {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    IsMaximalSunflowerFree family 3 ground →
    BalanceLowCaseConjecture (α := α) →
    BalanceHighCaseConjecture (α := α) →
    InBalanceRangeNat family i := by
  intro hmax hlow hhigh
  have h_not_low : ¬ LowFreq family i := low_case_contradiction family ground i hmax hlow
  have h_not_high : ¬ HighFreq family i := high_case_contradiction family ground i hmax hhigh
  exact not_low_not_high_implies_bounds family i h_not_low h_not_high

/-- Global Nat-form Balance Conjecture from the low/high case conjectures. -/
theorem balance_conjecture_nat_from_cases {α : Type*} [DecidableEq α] :
    BalanceLowCaseConjecture (α := α) →
    BalanceHighCaseConjecture (α := α) →
    BalanceConjectureNat (α := α) := by
  intro hlow hhigh family ground hcard hmax i hi
  exact balance_conjecture_nat_of_cases family ground i hmax hlow hhigh

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
    n * (Nat.choose m 3 / n) ≤ totalBlockingCapacity family ground ∧
      InBalanceRangeNat family i := by
  intro hlow hhigh h_card_family h_card_ground hmax h_m_pos
  constructor
  · exact local_turan_growth_constraint_of_maximal family ground m n
      h_card_family h_card_ground hmax h_m_pos
  · exact balance_conjecture_nat_of_cases family ground i hmax hlow hhigh

/-- Card-specialized bridge: case conjectures give Local-Turan and Nat balance bounds. -/
theorem local_turan_and_inBalanceRangeNat_of_cases_cards {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (i : α) :
    BalanceLowCaseConjecture (α := α) →
    BalanceHighCaseConjecture (α := α) →
    IsMaximalSunflowerFree family 3 ground →
    family.card ≥ 3 →
    ground.card * (Nat.choose family.card 3 / ground.card) ≤ totalBlockingCapacity family ground ∧
      InBalanceRangeNat family i := by
  intro hlow hhigh hmax h_m_pos
  simpa using local_turan_and_inBalanceRangeNat_of_cases
    (family := family) (ground := ground) (m := family.card) (n := ground.card) (i := i)
    hlow hhigh rfl rfl hmax h_m_pos

/-- Bridge theorem: case conjectures give both Local-Turan and rational balance bounds. -/
theorem local_turan_and_inBalanceRange_of_cases {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (m n : ℕ) (i : α) :
    BalanceLowCaseConjecture (α := α) →
    BalanceHighCaseConjecture (α := α) →
    family.card = m →
    ground.card = n →
    IsMaximalSunflowerFree family 3 ground →
    m ≥ 3 →
    n * (Nat.choose m 3 / n) ≤ totalBlockingCapacity family ground ∧
      InBalanceRange family i := by
  intro hlow hhigh h_card_family h_card_ground hmax h_m_pos
  rcases local_turan_and_inBalanceRangeNat_of_cases family ground m n i
      hlow hhigh h_card_family h_card_ground hmax h_m_pos with ⟨h_turan, hnat⟩
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
    ground.card * (Nat.choose family.card 3 / ground.card) ≤ totalBlockingCapacity family ground ∧
      InBalanceRange family i := by
  intro hlow hhigh hmax h_m_pos
  simpa using local_turan_and_inBalanceRange_of_cases
    (family := family) (ground := ground) (m := family.card) (n := ground.card) (i := i)
    hlow hhigh rfl rfl hmax h_m_pos

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
    n * (Nat.choose m 3 / n) ≤ totalBlockingCapacity family ground ∧
      (InBalanceRangeNat family i ∧ InBalanceRange family i) := by
  intro hlow hhigh h_card_family h_card_ground hmax h_m_pos
  rcases local_turan_and_inBalanceRangeNat_of_cases family ground m n i
      hlow hhigh h_card_family h_card_ground hmax h_m_pos with ⟨h_turan, hnat⟩
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
    InBalanceRangeNat family i ∧ InBalanceRange family i := by
  intro hlow hhigh h_card_family h_card_ground hmax h_m_pos
  exact (local_turan_and_inBalanceRange_pair_of_cases family ground m n i
    hlow hhigh h_card_family h_card_ground hmax h_m_pos).2

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
    balance_conjecture_nat_of_cases family ground i hmax hlow hhigh
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
    balance_conjecture_nat_of_cases family ground i hmax hlow hhigh
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
