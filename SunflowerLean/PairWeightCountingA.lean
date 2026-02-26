import SunflowerLean.BalanceCore

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

