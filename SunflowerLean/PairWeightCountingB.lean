import SunflowerLean.PairWeightCountingA

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

