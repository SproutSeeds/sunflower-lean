import SunflowerLean.ObstructionRecurrenceBridge
import SunflowerLean.Recurrence

namespace SunflowerLean
open scoped BigOperators
universe u

lemma mem_coreSliceProj_iff_liftAt_mem_family_of_mem_coreSliceAvoid
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {h : α} {S : Finset α}
    (hS0 : S ∈ coreSliceAvoid family h) :
    S ∈ coreSliceProj family h ↔ liftAt S h ∈ family := by
  classical
  constructor
  · intro hProj
    rcases Finset.mem_image.mp hProj with ⟨T, hT, hErase⟩
    have hTh : h ∈ T := (Finset.mem_filter.mp hT).2
    have hEqLift : liftAt S h = T := by
      calc
        liftAt S h = insert h S := by simp [liftAt]
        _ = insert h (T.erase h) := by simp [hErase]
        _ = T := Finset.insert_erase hTh
    exact hEqLift ▸ (Finset.mem_filter.mp hT).1
  · intro hLift
    have hhn : h ∉ S := (Finset.mem_filter.mp hS0).2
    refine Finset.mem_image.mpr ?_
    refine ⟨liftAt S h, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨hLift, by simp [liftAt]⟩
    · simpa [liftAt, hhn] using (Finset.erase_insert h S)

lemma mem_coreRemainder_iff_liftAt_not_mem_family_of_mem_coreSliceAvoid
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {h : α} {S : Finset α}
    (hS0 : S ∈ coreSliceAvoid family h) :
    S ∈ coreRemainder family h ↔ liftAt S h ∉ family := by
  constructor
  · intro hRem
    have hNotProj : S ∉ coreSliceProj family h := (Finset.mem_sdiff.mp hRem).2
    intro hLift
    exact hNotProj ((mem_coreSliceProj_iff_liftAt_mem_family_of_mem_coreSliceAvoid hS0).2 hLift)
  · intro hNotLift
    refine Finset.mem_sdiff.mpr ⟨hS0, ?_⟩
    intro hProj
    exact hNotLift ((mem_coreSliceProj_iff_liftAt_mem_family_of_mem_coreSliceAvoid hS0).1 hProj)

lemma mem_o1aWitnessLiftDom_iff_mem_coreRemainder
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {h : α} {S : Finset α} :
    S ∈ o1aWitnessLiftDom family h ↔ S ∈ coreRemainder family h := by
  constructor
  · intro hDom
    have hS0 : S ∈ coreSliceAvoid family h := (Finset.mem_filter.mp hDom).1
    exact (mem_coreRemainder_iff_liftAt_not_mem_family_of_mem_coreSliceAvoid hS0).2
      ((Finset.mem_filter.mp hDom).2)
  · intro hRem
    have hS0 : S ∈ coreSliceAvoid family h := (Finset.mem_sdiff.mp hRem).1
    exact Finset.mem_filter.mpr
      ⟨hS0, (mem_coreRemainder_iff_liftAt_not_mem_family_of_mem_coreSliceAvoid hS0).1 hRem⟩

lemma o1aWitnessLiftDom_eq_coreRemainder
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (h : α) :
    o1aWitnessLiftDom family h = coreRemainder family h := by
  ext S
  exact mem_o1aWitnessLiftDom_iff_mem_coreRemainder

lemma o1aWitnessLiftDomWL_subset_o1aWitnessLiftDom
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (h : α) :
    o1aWitnessLiftDomWL family h ⊆ o1aWitnessLiftDom family h := by
  classical
  exact Finset.filter_subset _ _

lemma o1aWitnessLiftDomWL_subset_coreRemainder
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (h : α) :
    o1aWitnessLiftDomWL family h ⊆ coreRemainder family h := by
  intro S hS
  exact (mem_o1aWitnessLiftDom_iff_mem_coreRemainder).1
    ((o1aWitnessLiftDomWL_subset_o1aWitnessLiftDom family h) hS)

lemma coreSliceProj_eq_sliceReduce_singleton
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (h : α) :
    coreSliceProj family h = sliceReduce family ({h} : Finset α) := by
  ext S
  simp [coreSliceProj, coreSliceContains, sliceReduce, Finset.sdiff_singleton_eq_erase,
    Finset.singleton_subset_iff]

lemma card_coreSliceContains_eq_card_coreSliceProj
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (h : α) :
    (coreSliceContains family h).card = (coreSliceProj family h).card := by
  classical
  have hInj :
      Set.InjOn (fun T : Finset α => T.erase h) {T | T ∈ coreSliceContains family h} := by
    intro T hT U hU hEq
    have hTh : h ∈ T := (Finset.mem_filter.mp hT).2
    have hUh : h ∈ U := (Finset.mem_filter.mp hU).2
    calc
      T = insert h (T.erase h) := by symm; exact Finset.insert_erase hTh
      _ = insert h (U.erase h) := by simp [hEq]
      _ = U := by exact Finset.insert_erase hUh
  simpa [coreSliceProj] using (Finset.card_image_of_injOn hInj).symm

lemma card_coreSliceContains_le_maxSunflowerFreeCard_sdiff
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {h : α}
    (hground : family ⊆ ground.powerset)
    (hfree : IsSunflowerFree family 3) :
    (coreSliceContains family h).card ≤
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 := by
  calc
    (coreSliceContains family h).card = (coreSliceProj family h).card :=
      card_coreSliceContains_eq_card_coreSliceProj family h
    _ = (sliceReduce family ({h} : Finset α)).card := by
      rw [coreSliceProj_eq_sliceReduce_singleton]
    _ ≤ maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 := by
      simpa using
        (card_sliceReduce_le_maxSunflowerFreeCard_sdiff
          (family := family) (ground := ground) (I := ({h} : Finset α)) (k := 3)
          hground hfree)

lemma card_coreOverlap_le_card_coreSliceProj
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (h : α) :
    (coreOverlap family h).card ≤ (coreSliceProj family h).card := by
  exact Finset.card_le_card (by
    intro S hS
    exact (Finset.mem_inter.mp hS).2)

lemma card_coreOverlap_le_maxSunflowerFreeCard_sdiff
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {h : α}
    (hground : family ⊆ ground.powerset)
    (hfree : IsSunflowerFree family 3) :
    (coreOverlap family h).card ≤
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 := by
  have hProjLe : (coreOverlap family h).card ≤ (coreSliceProj family h).card :=
    card_coreOverlap_le_card_coreSliceProj family h
  rw [← card_coreSliceContains_eq_card_coreSliceProj family h] at hProjLe
  exact hProjLe.trans (card_coreSliceContains_le_maxSunflowerFreeCard_sdiff hground hfree)

lemma card_o1aWitnessLiftDom_eq_card_coreRemainder
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (h : α) :
    (o1aWitnessLiftDom family h).card = (coreRemainder family h).card := by
  simp [o1aWitnessLiftDom_eq_coreRemainder]

lemma card_o1aWitnessLiftDomWL_le_card_coreRemainder
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (h : α) :
    (o1aWitnessLiftDomWL family h).card ≤ (coreRemainder family h).card := by
  exact Finset.card_le_card (o1aWitnessLiftDomWL_subset_coreRemainder family h)

lemma card_coreSliceAvoid_le_maxSunflowerFreeCard_sdiff_add_card_o1aWitnessLiftDom
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {h : α}
    (hground : family ⊆ ground.powerset)
    (hfree : IsSunflowerFree family 3) :
    (coreSliceAvoid family h).card ≤
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 + (o1aWitnessLiftDom family h).card := by
  have hpart := card_coreOverlap_add_card_coreRemainder_eq_card_coreSliceAvoid family h
  have hOverlapLe :=
    card_coreOverlap_le_maxSunflowerFreeCard_sdiff (family := family) (ground := ground) (h := h)
      hground hfree
  calc
    (coreSliceAvoid family h).card = (coreOverlap family h).card + (coreRemainder family h).card := by
      simpa using hpart.symm
    _ ≤ maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 + (coreRemainder family h).card := by
      exact Nat.add_le_add_right hOverlapLe _
    _ = maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 + (o1aWitnessLiftDom family h).card := by
      rw [← card_o1aWitnessLiftDom_eq_card_coreRemainder family h]

noncomputable def o1aChainBucket {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (h : α) : Finset (Finset α) := by
  classical
  exact (o1aWitnessLiftDom family h).filter (fun S => ChainExtension family S h)

noncomputable def o1aNonChainBucket {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (h : α) : Finset (Finset α) := by
  classical
  exact (o1aWitnessLiftDom family h).filter (fun S => ¬ ChainExtension family S h)

noncomputable def o1aSingletonCoreBucket {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (h : α) : Finset (Finset α) := by
  classical
  exact (o1aNonChainBucket family h).filter (fun S => WitnessHasHSingletonCore family (liftAt S h) h)

lemma mem_o1aSingletonCoreBucket_iff
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {h : α} {S : Finset α} :
    S ∈ o1aSingletonCoreBucket family h ↔
      S ∈ o1aWitnessLiftDom family h ∧
      ¬ ChainExtension family S h ∧
      WitnessHasHSingletonCore family (liftAt S h) h := by
  simp [o1aSingletonCoreBucket, o1aNonChainBucket, and_assoc, and_left_comm, and_comm]

lemma singletonCore_eq_singleton_of_inter_eq
    {α : Type*} [DecidableEq α]
    {A B core : Finset α} {h : α}
    (hhA : h ∈ A) (hhB : h ∈ B)
    (hcore : SingletonCore core h)
    (hAB : A ∩ B = core) :
    core = ({h} : Finset α) := by
  have hhcore : h ∈ core := by
    rw [← hAB]
    exact Finset.mem_inter.mpr ⟨hhA, hhB⟩
  refine Finset.Subset.antisymm hcore ?_
  intro x hx
  have hxEq : x = h := Finset.mem_singleton.mp hx
  simpa [hxEq] using hhcore

lemma inter_liftAt_eq_singleton_of_inter_eq_empty
    {α : Type*} [DecidableEq α]
    {A S : Finset α} {h : α}
    (hhA : h ∈ A) (hhnS : h ∉ S)
    (hAS : A ∩ S = (∅ : Finset α)) :
    A ∩ liftAt S h = ({h} : Finset α) := by
  calc
    A ∩ liftAt S h = A ∩ (S ∪ ({h} : Finset α)) := by simp [liftAt]
    _ = (A ∩ S) ∪ (A ∩ ({h} : Finset α)) := by
      simpa using Finset.inter_union_distrib_left A S ({h} : Finset α)
    _ = A ∩ ({h} : Finset α) := by simp [hAS]
    _ = ({h} : Finset α) := by
      ext x
      by_cases hx : x = h
      · subst hx
        simp [hhA]
      · simp [hx]

lemma inter_eq_empty_of_inter_liftAt_eq_singleton
    {α : Type*} [DecidableEq α]
    {A S : Finset α} {h : α}
    (hhnS : h ∉ S)
    (hAT : A ∩ liftAt S h = ({h} : Finset α)) :
    A ∩ S = (∅ : Finset α) := by
  refine Finset.eq_empty_iff_forall_not_mem.mpr ?_
  intro x hxAS
  have hxA : x ∈ A := (Finset.mem_inter.mp hxAS).1
  have hxS : x ∈ S := (Finset.mem_inter.mp hxAS).2
  have hxAT : x ∈ A ∩ liftAt S h := by
    refine Finset.mem_inter.mpr ⟨hxA, ?_⟩
    simp [liftAt, hxS]
  have hxSingleton : x ∈ ({h} : Finset α) := by
    rw [hAT] at hxAT
    exact hxAT
  have hxEq : x = h := Finset.mem_singleton.mp hxSingleton
  exact hhnS (hxEq ▸ hxS)

theorem exists_coreSliceContains_pair_of_mem_o1aSingletonCoreBucket
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {h : α} {S : Finset α}
    (hS : S ∈ o1aSingletonCoreBucket family h) :
    ∃ A ∈ coreSliceContains family h, ∃ B ∈ coreSliceContains family h,
      A ≠ B ∧
      A ∩ B = ({h} : Finset α) ∧
      A ∩ S = (∅ : Finset α) ∧
      B ∩ S = (∅ : Finset α) := by
  classical
  rcases (mem_o1aSingletonCoreBucket_iff.mp hS) with ⟨hDom, hnoChain, hWitness⟩
  have hhnS : h ∉ S := (Finset.mem_filter.mp ((Finset.mem_filter.mp hDom).1)).2
  rcases hWitness with ⟨A, hA, B, hB, hne, core, hcore, hAB, hAT, hBT⟩
  have hhA : h ∈ A := (Finset.mem_filter.mp hA).2
  have hhB : h ∈ B := (Finset.mem_filter.mp hB).2
  have hcoreEq : core = ({h} : Finset α) :=
    singletonCore_eq_singleton_of_inter_eq hhA hhB hcore hAB
  refine ⟨A, ?_, B, ?_, hne, ?_, ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hA).1, hhA⟩
  · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hB).1, hhB⟩
  · simpa [hcoreEq] using hAB
  · have hAT' : A ∩ liftAt S h = ({h} : Finset α) := by simpa [hcoreEq] using hAT
    exact inter_eq_empty_of_inter_liftAt_eq_singleton hhnS hAT'
  · have hBT' : B ∩ liftAt S h = ({h} : Finset α) := by simpa [hcoreEq] using hBT
    exact inter_eq_empty_of_inter_liftAt_eq_singleton hhnS hBT'

theorem mem_o1aSingletonCoreBucket_iff_exists_coreSliceContains_pair
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {h : α} {S : Finset α} :
    S ∈ o1aSingletonCoreBucket family h ↔
      S ∈ o1aWitnessLiftDom family h ∧
      ¬ ChainExtension family S h ∧
      ∃ A ∈ coreSliceContains family h, ∃ B ∈ coreSliceContains family h,
        A ≠ B ∧
        A ∩ B = ({h} : Finset α) ∧
        A ∩ S = (∅ : Finset α) ∧
        B ∩ S = (∅ : Finset α) := by
  constructor
  · intro hS
    rcases (mem_o1aSingletonCoreBucket_iff.mp hS) with ⟨hDom, hnoChain, _⟩
    rcases exists_coreSliceContains_pair_of_mem_o1aSingletonCoreBucket hS with
      ⟨A, hA, B, hB, hne, hAB, hAS, hBS⟩
    exact ⟨hDom, hnoChain, A, hA, B, hB, hne, hAB, hAS, hBS⟩
  · rintro ⟨hDom, hnoChain, A, hA, B, hB, hne, hAB, hAS, hBS⟩
    have hhnS : h ∉ S := (Finset.mem_filter.mp ((Finset.mem_filter.mp hDom).1)).2
    have hhA : h ∈ A := (Finset.mem_filter.mp hA).2
    have hhB : h ∈ B := (Finset.mem_filter.mp hB).2
    have hAT : A ∩ liftAt S h = ({h} : Finset α) :=
      inter_liftAt_eq_singleton_of_inter_eq_empty hhA hhnS hAS
    have hBT : B ∩ liftAt S h = ({h} : Finset α) :=
      inter_liftAt_eq_singleton_of_inter_eq_empty hhB hhnS hBS
    refine (mem_o1aSingletonCoreBucket_iff).2 ⟨hDom, hnoChain, ?_⟩
    refine ⟨A, ?_, B, ?_, hne, ({h} : Finset α), ?_, ?_, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hA).1, hhA⟩
    · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hB).1, hhB⟩
    · intro x hx
      simpa using hx
    · simpa using hAB
    · simpa using hAT
    · simpa using hBT

lemma o1aSingletonCoreBucket_subset_family
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (h : α) :
    o1aSingletonCoreBucket family h ⊆ family := by
  intro S hS
  have hDom : S ∈ o1aWitnessLiftDom family h := (mem_o1aSingletonCoreBucket_iff.mp hS).1
  exact (Finset.mem_filter.mp ((Finset.mem_filter.mp hDom).1)).1

noncomputable def o1aSingletonCoreFiber {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (h : α) (A B : Finset α) : Finset (Finset α) := by
  classical
  exact (o1aSingletonCoreBucket family h).filter (fun S => A ∩ S = ∅ ∧ B ∩ S = ∅)

lemma mem_o1aSingletonCoreFiber_iff
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {h : α} {A B S : Finset α} :
    S ∈ o1aSingletonCoreFiber family h A B ↔
      S ∈ o1aSingletonCoreBucket family h ∧
      A ∩ S = (∅ : Finset α) ∧
      B ∩ S = (∅ : Finset α) := by
  simp [o1aSingletonCoreFiber, and_assoc]

theorem exists_mem_o1aSingletonCoreFiber_of_mem_o1aSingletonCoreBucket
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {h : α} {S : Finset α}
    (hS : S ∈ o1aSingletonCoreBucket family h) :
    ∃ A ∈ coreSliceContains family h, ∃ B ∈ coreSliceContains family h,
      A ≠ B ∧
      A ∩ B = ({h} : Finset α) ∧
      S ∈ o1aSingletonCoreFiber family h A B := by
  rcases exists_coreSliceContains_pair_of_mem_o1aSingletonCoreBucket hS with
    ⟨A, hA, B, hB, hne, hAB, hAS, hBS⟩
  refine ⟨A, hA, B, hB, hne, hAB, ?_⟩
  exact (mem_o1aSingletonCoreFiber_iff).2 ⟨hS, hAS, hBS⟩

theorem o1aSingletonCoreFiber_subset_powerset_sdiff_union
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {h : α} {A B : Finset α}
    (hground : family ⊆ ground.powerset) :
    o1aSingletonCoreFiber family h A B ⊆ (ground \ (A ∪ B)).powerset := by
  intro S hS
  have hBucket : S ∈ o1aSingletonCoreBucket family h := (mem_o1aSingletonCoreFiber_iff.mp hS).1
  have hDisjA : A ∩ S = (∅ : Finset α) := (mem_o1aSingletonCoreFiber_iff.mp hS).2.1
  have hDisjB : B ∩ S = (∅ : Finset α) := (mem_o1aSingletonCoreFiber_iff.mp hS).2.2
  have hSfam : S ∈ family := o1aSingletonCoreBucket_subset_family family h hBucket
  have hSsub : S ⊆ ground := Finset.mem_powerset.mp (hground hSfam)
  refine Finset.mem_powerset.mpr ?_
  intro x hxS
  refine Finset.mem_sdiff.mpr ⟨hSsub hxS, ?_⟩
  intro hxAB
  rcases Finset.mem_union.mp hxAB with hxA | hxB
  · have hxAS : x ∈ A ∩ S := Finset.mem_inter.mpr ⟨hxA, hxS⟩
    have : x ∈ (∅ : Finset α) := by rw [← hDisjA]; exact hxAS
    exact Finset.notMem_empty x this
  · have hxBS : x ∈ B ∩ S := Finset.mem_inter.mpr ⟨hxB, hxS⟩
    have : x ∈ (∅ : Finset α) := by rw [← hDisjB]; exact hxBS
    exact Finset.notMem_empty x this

theorem sunflowerFree_o1aSingletonCoreFiber
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (h : α) (A B : Finset α) (k : ℕ)
    (hfree : IsSunflowerFree family k) :
    IsSunflowerFree (o1aSingletonCoreFiber family h A B) k := by
  intro sub hsub
  have hsub' : sub ⊆ family := by
    intro S hS
    exact o1aSingletonCoreBucket_subset_family family h
      ((mem_o1aSingletonCoreFiber_iff.mp (hsub hS)).1)
  exact hfree sub hsub'

theorem card_o1aSingletonCoreFiber_le_maxSunflowerFreeCard_sdiff_union
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {h : α} {A B : Finset α}
    (hground : family ⊆ ground.powerset)
    (hfree : IsSunflowerFree family 3) :
    (o1aSingletonCoreFiber family h A B).card ≤
      maxSunflowerFreeCard (ground \ (A ∪ B)) 3 := by
  exact
    card_le_maxSunflowerFreeCard
      (family := o1aSingletonCoreFiber family h A B)
      (ground := ground \ (A ∪ B)) (k := 3)
      (o1aSingletonCoreFiber_subset_powerset_sdiff_union (family := family)
        (ground := ground) (h := h) (A := A) (B := B) hground)
      (sunflowerFree_o1aSingletonCoreFiber family h A B 3 hfree)

noncomputable def o1aSingletonCorePairUniverse {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (h : α) : Finset (Finset α × Finset α) := by
  classical
  exact ((coreSliceContains family h).product (coreSliceContains family h)).filter
    (fun p => p.1 ≠ p.2 ∧ p.1 ∩ p.2 = ({h} : Finset α))

lemma mem_o1aSingletonCorePairUniverse_iff
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {h : α} {p : Finset α × Finset α} :
    p ∈ o1aSingletonCorePairUniverse family h ↔
      p.1 ∈ coreSliceContains family h ∧
      p.2 ∈ coreSliceContains family h ∧
      p.1 ≠ p.2 ∧
      p.1 ∩ p.2 = ({h} : Finset α) := by
  simp [o1aSingletonCorePairUniverse, and_assoc, and_left_comm, and_comm]

theorem mem_biUnion_o1aSingletonCoreFiberPairUniverse_of_mem_o1aSingletonCoreBucket
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {h : α} {S : Finset α}
    (hS : S ∈ o1aSingletonCoreBucket family h) :
    S ∈ (o1aSingletonCorePairUniverse family h).biUnion
      (fun p => o1aSingletonCoreFiber family h p.1 p.2) := by
  classical
  rcases exists_mem_o1aSingletonCoreFiber_of_mem_o1aSingletonCoreBucket hS with
    ⟨A, hA, B, hB, hne, hAB, hFiber⟩
  refine Finset.mem_biUnion.mpr ?_
  refine ⟨(A, B), ?_, ?_⟩
  · exact (mem_o1aSingletonCorePairUniverse_iff).2 ⟨hA, hB, hne, hAB⟩
  · simpa using hFiber

theorem o1aSingletonCoreBucket_eq_biUnion_pairUniverse
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (h : α) :
    o1aSingletonCoreBucket family h =
      (o1aSingletonCorePairUniverse family h).biUnion
        (fun p => o1aSingletonCoreFiber family h p.1 p.2) := by
  classical
  ext S
  constructor
  · intro hS
    exact mem_biUnion_o1aSingletonCoreFiberPairUniverse_of_mem_o1aSingletonCoreBucket hS
  · intro hS
    rcases Finset.mem_biUnion.mp hS with ⟨p, hp, hFiber⟩
    exact (mem_o1aSingletonCoreFiber_iff.mp (by simpa using hFiber)).1

theorem o1aChainBucket_subset_powerset_sdiff_singleton
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {h : α}
    (hground : family ⊆ ground.powerset) :
    o1aChainBucket family h ⊆ (ground \ ({h} : Finset α)).powerset := by
  classical
  intro S hS
  have hDom : S ∈ o1aWitnessLiftDom family h := (Finset.mem_filter.mp hS).1
  have hSAvoid : S ∈ coreSliceAvoid family h := (Finset.mem_filter.mp hDom).1
  have hSfam : S ∈ family := (Finset.mem_filter.mp hSAvoid).1
  have hhnS : h ∉ S := (Finset.mem_filter.mp hSAvoid).2
  have hSsub : S ⊆ ground := Finset.mem_powerset.mp (hground hSfam)
  refine Finset.mem_powerset.mpr ?_
  intro x hxS
  refine Finset.mem_sdiff.mpr ⟨hSsub hxS, ?_⟩
  intro hxH
  have hxEq : x = h := Finset.mem_singleton.mp hxH
  exact hhnS (hxEq ▸ hxS)


theorem sunflowerFree_o1aChainBucket
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (h : α) (k : ℕ)
    (hfree : IsSunflowerFree family k) :
    IsSunflowerFree (o1aChainBucket family h) k := by
  classical
  intro sub hsub
  have hsub' : sub ⊆ family := by
    intro S hS
    have hBucket : S ∈ o1aChainBucket family h := hsub hS
    have hDom : S ∈ o1aWitnessLiftDom family h := (Finset.mem_filter.mp hBucket).1
    have hSAvoid : S ∈ coreSliceAvoid family h := (Finset.mem_filter.mp hDom).1
    exact (Finset.mem_filter.mp hSAvoid).1
  exact hfree sub hsub'


theorem card_o1aChainBucket_le_maxSunflowerFreeCard_sdiff
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {h : α}
    (hground : family ⊆ ground.powerset)
    (hfree : IsSunflowerFree family 3) :
    (o1aChainBucket family h).card ≤
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 := by
  exact
    card_le_maxSunflowerFreeCard
      (family := o1aChainBucket family h)
      (ground := ground \ ({h} : Finset α)) (k := 3)
      (o1aChainBucket_subset_powerset_sdiff_singleton
        (family := family) (ground := ground) (h := h) hground)
      (sunflowerFree_o1aChainBucket family h 3 hfree)


theorem card_o1aSingletonCoreBucket_le_sum_pairUniverse
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {h : α}
    (hground : family ⊆ ground.powerset)
    (hfree : IsSunflowerFree family 3) :
    (o1aSingletonCoreBucket family h).card ≤
      ∑ p ∈ o1aSingletonCorePairUniverse family h,
        maxSunflowerFreeCard (ground \ (p.1 ∪ p.2)) 3 := by
  classical
  rw [o1aSingletonCoreBucket_eq_biUnion_pairUniverse family h]
  calc
    ((o1aSingletonCorePairUniverse family h).biUnion
        (fun p => o1aSingletonCoreFiber family h p.1 p.2)).card
      ≤ ∑ p ∈ o1aSingletonCorePairUniverse family h,
          (o1aSingletonCoreFiber family h p.1 p.2).card := by
            exact Finset.card_biUnion_le
    _ ≤ ∑ p ∈ o1aSingletonCorePairUniverse family h,
          maxSunflowerFreeCard (ground \ (p.1 ∪ p.2)) 3 := by
            refine Finset.sum_le_sum ?_
            intro p hp
            exact card_o1aSingletonCoreFiber_le_maxSunflowerFreeCard_sdiff_union
              (family := family) (ground := ground) (h := h) (A := p.1) (B := p.2) hground hfree

lemma card_o1aChainBucket_add_card_o1aNonChainBucket_eq_card_o1aWitnessLiftDom
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (h : α) :
    (o1aChainBucket family h).card + (o1aNonChainBucket family h).card =
      (o1aWitnessLiftDom family h).card := by
  classical
  simpa [o1aChainBucket, o1aNonChainBucket] using
    (Finset.filter_card_add_filter_neg_card_eq_card
      (s := o1aWitnessLiftDom family h)
      (p := fun S : Finset α => ChainExtension family S h))

open scoped Classical in
lemma o1aWitnessLiftDomWL_eq_o1aNonChainBucket_filter_not_singleton
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (h : α) :
    o1aWitnessLiftDomWL family h =
      (o1aNonChainBucket family h).filter
        (fun S => ¬ WitnessHasHSingletonCore family (liftAt S h) h) := by
  classical
  ext S
  simp only [o1aWitnessLiftDomWL, o1aNonChainBucket, Finset.mem_filter]
  constructor <;> intro hS <;> simpa [and_assoc, and_left_comm, and_comm] using hS

lemma card_o1aSingletonCoreBucket_add_card_o1aWitnessLiftDomWL_eq_card_o1aNonChainBucket
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (h : α) :
    (o1aSingletonCoreBucket family h).card + (o1aWitnessLiftDomWL family h).card =
      (o1aNonChainBucket family h).card := by
  classical
  have hpart :
      (o1aSingletonCoreBucket family h).card +
          (((o1aNonChainBucket family h).filter
            (fun S => ¬ WitnessHasHSingletonCore family (liftAt S h) h)).card) =
        (o1aNonChainBucket family h).card := by
    simpa [o1aSingletonCoreBucket] using
      (Finset.filter_card_add_filter_neg_card_eq_card
        (s := o1aNonChainBucket family h)
        (p := fun S : Finset α => WitnessHasHSingletonCore family (liftAt S h) h))
  simpa [o1aWitnessLiftDomWL_eq_o1aNonChainBucket_filter_not_singleton family h] using hpart

lemma card_o1aChainBucket_add_card_o1aSingletonCoreBucket_add_card_o1aWitnessLiftDomWL_eq_card_o1aWitnessLiftDom
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (h : α) :
    (o1aChainBucket family h).card +
        (o1aSingletonCoreBucket family h).card +
        (o1aWitnessLiftDomWL family h).card =
      (o1aWitnessLiftDom family h).card := by
  have h1 := card_o1aChainBucket_add_card_o1aNonChainBucket_eq_card_o1aWitnessLiftDom family h
  have h2 := card_o1aSingletonCoreBucket_add_card_o1aWitnessLiftDomWL_eq_card_o1aNonChainBucket family h
  calc
    (o1aChainBucket family h).card +
        (o1aSingletonCoreBucket family h).card +
        (o1aWitnessLiftDomWL family h).card
        = (o1aChainBucket family h).card +
            ((o1aSingletonCoreBucket family h).card + (o1aWitnessLiftDomWL family h).card) := by
          simp [Nat.add_assoc]
    _ = (o1aChainBucket family h).card + (o1aNonChainBucket family h).card := by rw [h2]
    _ = (o1aWitnessLiftDom family h).card := h1

lemma card_family_le_two_mul_maxSunflowerFreeCard_sdiff_add_card_o1aWitnessLiftDom
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {h : α}
    (hground : family ⊆ ground.powerset)
    (hfree : IsSunflowerFree family 3) :
    family.card ≤
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      (o1aWitnessLiftDom family h).card := by
  have hContainsLe :=
    card_coreSliceContains_le_maxSunflowerFreeCard_sdiff (family := family) (ground := ground) (h := h)
      hground hfree
  have hAvoidLe :=
    card_coreSliceAvoid_le_maxSunflowerFreeCard_sdiff_add_card_o1aWitnessLiftDom
      (family := family) (ground := ground) (h := h) hground hfree
  calc
    family.card = (coreSliceContains family h).card + (coreSliceAvoid family h).card := by
      simpa using (card_coreSliceContains_add_card_coreSliceAvoid_eq_card family h).symm
    _ ≤ maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
          (maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 + (o1aWitnessLiftDom family h).card) := by
      exact Nat.add_le_add hContainsLe hAvoidLe
    _ = maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
          maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
          (o1aWitnessLiftDom family h).card := by
      simp [Nat.add_assoc]

lemma card_family_le_two_mul_maxSunflowerFreeCard_sdiff_add_card_o1aChainBucket_add_card_o1aSingletonCoreBucket_add_card_o1aWitnessLiftDomWL
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {h : α}
    (hground : family ⊆ ground.powerset)
    (hfree : IsSunflowerFree family 3) :
    family.card ≤
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      (o1aChainBucket family h).card +
      (o1aSingletonCoreBucket family h).card +
      (o1aWitnessLiftDomWL family h).card := by
  have hBase :=
    card_family_le_two_mul_maxSunflowerFreeCard_sdiff_add_card_o1aWitnessLiftDom
      (family := family) (ground := ground) (h := h) hground hfree
  rw [← card_o1aChainBucket_add_card_o1aSingletonCoreBucket_add_card_o1aWitnessLiftDomWL_eq_card_o1aWitnessLiftDom family h] at hBase
  simpa [Nat.add_assoc] using hBase

lemma card_family_le_three_mul_maxSunflowerFreeCard_sdiff_add_A_add_card_o1aChainBucket_add_card_o1aSingletonCoreBucket
    {α : Type u} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h : α}
    (B : ℕ → ℕ) (A : ℕ)
    (hreg : O1aUpgradeRegime family ground A0 h)
    (h2 : 2 ≤ maxCoDegree family ground)
    (hKeyImage : o1a_wlcert_key_image_bound_target.{u} B)
    (hSplitBuilder :
      let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h
      let hdom : ∀ S ∈ dom, Nonempty (WLcert family S) :=
        wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
          (family := family) (ground := ground) (A0 := A0) (h := h) hreg
      let keyImage := dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)
      ∀ k : WLcertKey α, k ∈ keyImage →
        let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
        ∀ Sstar : {S // S ∈ dom}, ∀ hSstar : Sstar ∈ fiber,
          (∀ Ssub ∈ fiber, Ssub ≠ Sstar →
            ∃ x,
              x ∈ realizedXSet
                (dom := dom) fiber Sstar.1 (ground \ (k.2.2.1 ∪ k.2.2.2.1)) ∧
              x ∈ Ssub.1 ∧ x ∉ Sstar.1) →
          ((∃ j, j ∈ Sstar.1 ∧ j ∈ Nmax family ground h ∧
              ∃ U ∈ WmaxAt family ground h j, ∃ V ∈ WmaxAt family ground h j, U ≠ V) ∨
            Sstar.1 ∩ supportMaxCoDegreePairs family ground = ∅) →
          KeyBadAggZeroAt
            (family := family) (ground := ground) (A0 := A0) (h0 := h)
            hreg k Sstar (by simpa [fiber] using hSstar))
    (hRemainder :
      (B ground.card * (coreSliceContains family h).card ^ 2) * (ground.card ^ 20) ≤ A) :
    family.card ≤
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      A +
      (o1aChainBucket family h).card +
      (o1aSingletonCoreBucket family h).card := by
  have hground : family ⊆ ground.powerset := hreg.1
  have hfree : IsSunflowerFree family 3 := hreg.2.1
  have hFamilyLe :=
    card_family_le_two_mul_maxSunflowerFreeCard_sdiff_add_card_o1aChainBucket_add_card_o1aSingletonCoreBucket_add_card_o1aWitnessLiftDomWL
      (family := family) (ground := ground) (h := h) hground hfree
  have hDomWLLe :=
    b2_recurrence_bridge_of_split_to_KeyBadAgg_under_O1aUpgradeRegime
      (α := α) (family := family) (ground := ground) (A0 := A0) (h := h) (B := B) (A := A)
      hreg h2 hKeyImage hSplitBuilder hRemainder
  have hTail :
      (o1aChainBucket family h).card +
          (o1aSingletonCoreBucket family h).card +
          (o1aWitnessLiftDomWL family h).card
        ≤
      (o1aChainBucket family h).card +
          (o1aSingletonCoreBucket family h).card +
          (maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 + A) := by
    simpa [Nat.add_assoc] using
      Nat.add_le_add_left
        (Nat.add_le_add_left hDomWLLe ((o1aSingletonCoreBucket family h).card))
        ((o1aChainBucket family h).card)
  have hStep :
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
          maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
          ((o1aChainBucket family h).card +
            (o1aSingletonCoreBucket family h).card +
            (o1aWitnessLiftDomWL family h).card)
        ≤
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
          maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
          ((o1aChainBucket family h).card +
            (o1aSingletonCoreBucket family h).card +
            (maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 + A)) := by
    simpa [Nat.add_assoc] using
      Nat.add_le_add_left
        (Nat.add_le_add_left hTail (maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3))
        (maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3)
  calc
    family.card ≤
        maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
          maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
          ((o1aChainBucket family h).card +
            (o1aSingletonCoreBucket family h).card +
            (o1aWitnessLiftDomWL family h).card) := by
      simpa [Nat.add_assoc] using hFamilyLe
    _ ≤
        maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
          maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
          ((o1aChainBucket family h).card +
            (o1aSingletonCoreBucket family h).card +
            (maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 + A)) := hStep
    _ =
        maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
          maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
          maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
          A +
          (o1aChainBucket family h).card +
          (o1aSingletonCoreBucket family h).card := by
      ac_rfl

theorem global_family_card_export_under_O1aUpgradeRegime
    {α : Type u} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h : α}
    (B : ℕ → ℕ) (A : ℕ)
    (hreg : O1aUpgradeRegime family ground A0 h)
    (h2 : 2 ≤ maxCoDegree family ground)
    (hKeyImage : o1a_wlcert_key_image_bound_target.{u} B)
    (hSplitBuilder :
      let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h
      let hdom : ∀ S ∈ dom, Nonempty (WLcert family S) :=
        wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
          (family := family) (ground := ground) (A0 := A0) (h := h) hreg
      let keyImage := dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)
      ∀ k : WLcertKey α, k ∈ keyImage →
        let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
        ∀ Sstar : {S // S ∈ dom}, ∀ hSstar : Sstar ∈ fiber,
          (∀ Ssub ∈ fiber, Ssub ≠ Sstar →
            ∃ x,
              x ∈ realizedXSet
                (dom := dom) fiber Sstar.1 (ground \ (k.2.2.1 ∪ k.2.2.2.1)) ∧
              x ∈ Ssub.1 ∧ x ∉ Sstar.1) →
          ((∃ j, j ∈ Sstar.1 ∧ j ∈ Nmax family ground h ∧
              ∃ U ∈ WmaxAt family ground h j, ∃ V ∈ WmaxAt family ground h j, U ≠ V) ∨
            Sstar.1 ∩ supportMaxCoDegreePairs family ground = ∅) →
          KeyBadAggZeroAt
            (family := family) (ground := ground) (A0 := A0) (h0 := h)
            hreg k Sstar (by simpa [fiber] using hSstar))
    (hRemainder :
      (B ground.card * (coreSliceContains family h).card ^ 2) * (ground.card ^ 20) ≤ A) :
    family.card ≤
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      A +
      (o1aChainBucket family h).card +
      (o1aSingletonCoreBucket family h).card := by
  exact
    card_family_le_three_mul_maxSunflowerFreeCard_sdiff_add_A_add_card_o1aChainBucket_add_card_o1aSingletonCoreBucket
      (family := family) (ground := ground) (A0 := A0) (h := h) (B := B) (A := A)
      hreg h2 hKeyImage hSplitBuilder hRemainder

theorem global_family_card_export_with_singletonCore_sum_under_O1aUpgradeRegime
    {α : Type u} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h : α}
    (B : ℕ → ℕ) (A : ℕ)
    (hreg : O1aUpgradeRegime family ground A0 h)
    (h2 : 2 ≤ maxCoDegree family ground)
    (hKeyImage : o1a_wlcert_key_image_bound_target.{u} B)
    (hSplitBuilder :
      let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h
      let hdom : ∀ S ∈ dom, Nonempty (WLcert family S) :=
        wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
          (family := family) (ground := ground) (A0 := A0) (h := h) hreg
      let keyImage := dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)
      ∀ k : WLcertKey α, k ∈ keyImage →
        let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
        ∀ Sstar : {S // S ∈ dom}, ∀ hSstar : Sstar ∈ fiber,
          (∀ Ssub ∈ fiber, Ssub ≠ Sstar →
            ∃ x,
              x ∈ realizedXSet
                (dom := dom) fiber Sstar.1 (ground \ (k.2.2.1 ∪ k.2.2.2.1)) ∧
              x ∈ Ssub.1 ∧ x ∉ Sstar.1) →
          ((∃ j, j ∈ Sstar.1 ∧ j ∈ Nmax family ground h ∧
              ∃ U ∈ WmaxAt family ground h j, ∃ V ∈ WmaxAt family ground h j, U ≠ V) ∨
            Sstar.1 ∩ supportMaxCoDegreePairs family ground = ∅) →
          KeyBadAggZeroAt
            (family := family) (ground := ground) (A0 := A0) (h0 := h)
            hreg k Sstar (by simpa [fiber] using hSstar))
    (hRemainder :
      (B ground.card * (coreSliceContains family h).card ^ 2) * (ground.card ^ 20) ≤ A) :
    family.card ≤
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      A +
      (o1aChainBucket family h).card +
      ∑ p ∈ o1aSingletonCorePairUniverse family h,
        maxSunflowerFreeCard (ground \ (p.1 ∪ p.2)) 3 := by
  have hBase :=
    global_family_card_export_under_O1aUpgradeRegime
      (family := family) (ground := ground) (A0 := A0) (h := h) (B := B) (A := A)
      hreg h2 hKeyImage hSplitBuilder hRemainder
  have hSingleton :
      (o1aSingletonCoreBucket family h).card ≤
        ∑ p ∈ o1aSingletonCorePairUniverse family h,
          maxSunflowerFreeCard (ground \ (p.1 ∪ p.2)) 3 :=
    card_o1aSingletonCoreBucket_le_sum_pairUniverse
      (family := family) (ground := ground) (h := h) hreg.1 hreg.2.1
  have hStep :
      (o1aChainBucket family h).card + (o1aSingletonCoreBucket family h).card ≤
        (o1aChainBucket family h).card +
          ∑ p ∈ o1aSingletonCorePairUniverse family h,
            maxSunflowerFreeCard (ground \ (p.1 ∪ p.2)) 3 := by
    exact Nat.add_le_add_left hSingleton ((o1aChainBucket family h).card)
  calc
    family.card ≤
        maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
          maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
          maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
          A +
          ((o1aChainBucket family h).card + (o1aSingletonCoreBucket family h).card) := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hBase
    _ ≤
        maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
          maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
          maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
          A +
          ((o1aChainBucket family h).card +
            ∑ p ∈ o1aSingletonCorePairUniverse family h,
              maxSunflowerFreeCard (ground \ (p.1 ∪ p.2)) 3) := by
      exact Nat.add_le_add_left hStep
        (maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
          maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
          maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 + A)
    _ =
        maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
          maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
          maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
          A +
          (o1aChainBucket family h).card +
          ∑ p ∈ o1aSingletonCorePairUniverse family h,
            maxSunflowerFreeCard (ground \ (p.1 ∪ p.2)) 3 := by
      ac_rfl

theorem global_family_card_export_with_chain_bound_under_O1aUpgradeRegime
    {α : Type u} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h : α}
    (B : ℕ → ℕ) (A : ℕ)
    (hreg : O1aUpgradeRegime family ground A0 h)
    (h2 : 2 ≤ maxCoDegree family ground)
    (hKeyImage : o1a_wlcert_key_image_bound_target.{u} B)
    (hSplitBuilder :
      let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h
      let hdom : ∀ S ∈ dom, Nonempty (WLcert family S) :=
        wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
          (family := family) (ground := ground) (A0 := A0) (h := h) hreg
      let keyImage := dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)
      ∀ k : WLcertKey α, k ∈ keyImage →
        let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
        ∀ Sstar : {S // S ∈ dom}, ∀ hSstar : Sstar ∈ fiber,
          (∀ Ssub ∈ fiber, Ssub ≠ Sstar →
            ∃ x,
              x ∈ realizedXSet
                (dom := dom) fiber Sstar.1 (ground \ (k.2.2.1 ∪ k.2.2.2.1)) ∧
              x ∈ Ssub.1 ∧ x ∉ Sstar.1) →
          ((∃ j, j ∈ Sstar.1 ∧ j ∈ Nmax family ground h ∧
              ∃ U ∈ WmaxAt family ground h j, ∃ V ∈ WmaxAt family ground h j, U ≠ V) ∨
            Sstar.1 ∩ supportMaxCoDegreePairs family ground = ∅) →
          KeyBadAggZeroAt
            (family := family) (ground := ground) (A0 := A0) (h0 := h)
            hreg k Sstar (by simpa [fiber] using hSstar))
    (hRemainder :
      (B ground.card * (coreSliceContains family h).card ^ 2) * (ground.card ^ 20) ≤ A) :
    family.card ≤
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      A +
      (o1aSingletonCoreBucket family h).card := by
  let M := maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3
  have hBase :=
    global_family_card_export_under_O1aUpgradeRegime
      (family := family) (ground := ground) (A0 := A0) (h := h) (B := B) (A := A)
      hreg h2 hKeyImage hSplitBuilder hRemainder
  have hChain : (o1aChainBucket family h).card ≤ M := by
    simpa [M] using
      card_o1aChainBucket_le_maxSunflowerFreeCard_sdiff
        (family := family) (ground := ground) (h := h) hreg.1 hreg.2.1
  have hStep :
      M + M + M + A + (o1aChainBucket family h).card +
          (o1aSingletonCoreBucket family h).card ≤
        M + M + M + M + A + (o1aSingletonCoreBucket family h).card := by
    have h' :
        (o1aChainBucket family h).card + (A + (o1aSingletonCoreBucket family h).card) ≤
          M + (A + (o1aSingletonCoreBucket family h).card) :=
      Nat.add_le_add_right hChain _
    have h'' :
        M + M + M +
            ((o1aChainBucket family h).card + (A + (o1aSingletonCoreBucket family h).card)) ≤
          M + M + M + (M + (A + (o1aSingletonCoreBucket family h).card)) :=
      Nat.add_le_add_left h' (M + M + M)
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h''
  have hBase' :
      family.card ≤
        M + M + M + A + (o1aChainBucket family h).card +
          (o1aSingletonCoreBucket family h).card := by
    simpa [M, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hBase
  exact hBase'.trans hStep


theorem global_family_card_export_with_chain_bound_and_singletonCore_sum_under_O1aUpgradeRegime
    {α : Type u} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h : α}
    (B : ℕ → ℕ) (A : ℕ)
    (hreg : O1aUpgradeRegime family ground A0 h)
    (h2 : 2 ≤ maxCoDegree family ground)
    (hKeyImage : o1a_wlcert_key_image_bound_target.{u} B)
    (hSplitBuilder :
      let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h
      let hdom : ∀ S ∈ dom, Nonempty (WLcert family S) :=
        wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
          (family := family) (ground := ground) (A0 := A0) (h := h) hreg
      let keyImage := dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)
      ∀ k : WLcertKey α, k ∈ keyImage →
        let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
        ∀ Sstar : {S // S ∈ dom}, ∀ hSstar : Sstar ∈ fiber,
          (∀ Ssub ∈ fiber, Ssub ≠ Sstar →
            ∃ x,
              x ∈ realizedXSet
                (dom := dom) fiber Sstar.1 (ground \ (k.2.2.1 ∪ k.2.2.2.1)) ∧
              x ∈ Ssub.1 ∧ x ∉ Sstar.1) →
          ((∃ j, j ∈ Sstar.1 ∧ j ∈ Nmax family ground h ∧
              ∃ U ∈ WmaxAt family ground h j, ∃ V ∈ WmaxAt family ground h j, U ≠ V) ∨
            Sstar.1 ∩ supportMaxCoDegreePairs family ground = ∅) →
          KeyBadAggZeroAt
            (family := family) (ground := ground) (A0 := A0) (h0 := h)
            hreg k Sstar (by simpa [fiber] using hSstar))
    (hRemainder :
      (B ground.card * (coreSliceContains family h).card ^ 2) * (ground.card ^ 20) ≤ A) :
    family.card ≤
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      A +
      ∑ p ∈ o1aSingletonCorePairUniverse family h,
        maxSunflowerFreeCard (ground \ (p.1 ∪ p.2)) 3 := by
  let M := maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3
  have hBase :=
    global_family_card_export_with_singletonCore_sum_under_O1aUpgradeRegime
      (family := family) (ground := ground) (A0 := A0) (h := h) (B := B) (A := A)
      hreg h2 hKeyImage hSplitBuilder hRemainder
  have hChain : (o1aChainBucket family h).card ≤ M := by
    simpa [M] using
      card_o1aChainBucket_le_maxSunflowerFreeCard_sdiff
        (family := family) (ground := ground) (h := h) hreg.1 hreg.2.1
  have hStep :
      M + M + M + A + (o1aChainBucket family h).card +
          (∑ p ∈ o1aSingletonCorePairUniverse family h,
            maxSunflowerFreeCard (ground \ (p.1 ∪ p.2)) 3) ≤
        M + M + M + M + A +
          (∑ p ∈ o1aSingletonCorePairUniverse family h,
            maxSunflowerFreeCard (ground \ (p.1 ∪ p.2)) 3) := by
    have h' :
        (o1aChainBucket family h).card +
            (A +
              ∑ p ∈ o1aSingletonCorePairUniverse family h,
                maxSunflowerFreeCard (ground \ (p.1 ∪ p.2)) 3) ≤
          M +
            (A +
              ∑ p ∈ o1aSingletonCorePairUniverse family h,
                maxSunflowerFreeCard (ground \ (p.1 ∪ p.2)) 3) :=
      Nat.add_le_add_right hChain _
    have h'' :
        M + M + M +
            ((o1aChainBucket family h).card +
              (A +
                ∑ p ∈ o1aSingletonCorePairUniverse family h,
                  maxSunflowerFreeCard (ground \ (p.1 ∪ p.2)) 3)) ≤
          M + M + M +
            (M +
              (A +
                ∑ p ∈ o1aSingletonCorePairUniverse family h,
                  maxSunflowerFreeCard (ground \ (p.1 ∪ p.2)) 3)) :=
      Nat.add_le_add_left h' (M + M + M)
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h''
  have hBase' :
      family.card ≤
        M + M + M + A + (o1aChainBucket family h).card +
          (∑ p ∈ o1aSingletonCorePairUniverse family h,
            maxSunflowerFreeCard (ground \ (p.1 ∪ p.2)) 3) := by
    simpa [M, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hBase
  exact hBase'.trans hStep

theorem maxSunflowerFreeCard_mono_of_subset
    {α : Type*} [DecidableEq α]
    {ground₁ ground₂ : Finset α} {k : ℕ}
    (hsub : ground₁ ⊆ ground₂) :
    maxSunflowerFreeCard ground₁ k ≤ maxSunflowerFreeCard ground₂ k := by
  classical
  unfold maxSunflowerFreeCard
  refine Finset.sup_le ?_
  intro F hF
  have hpow₁ : F ⊆ ground₁.powerset := Finset.mem_powerset.mp ((Finset.mem_filter.mp hF).1)
  have hpow₂ : F ⊆ ground₂.powerset := by
    intro S hS
    refine Finset.mem_powerset.mpr ?_
    intro x hx
    exact hsub ((Finset.mem_powerset.mp (hpow₁ hS)) hx)
  have hF₂ :
      F ∈ ground₂.powerset.powerset.filter (fun G : Finset (Finset α) => IsSunflowerFree G k) := by
    refine Finset.mem_filter.mpr ?_
    exact ⟨Finset.mem_powerset.mpr hpow₂, (Finset.mem_filter.mp hF).2⟩
  exact
    Finset.le_sup
      (s := ground₂.powerset.powerset.filter (fun G : Finset (Finset α) => IsSunflowerFree G k))
      (f := Finset.card) hF₂

theorem o1aSingletonCorePairUniverse_subset_product_coreSliceContains
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (h : α) :
    o1aSingletonCorePairUniverse family h ⊆
      (coreSliceContains family h).product (coreSliceContains family h) := by
  intro p hp
  rcases (mem_o1aSingletonCorePairUniverse_iff.mp hp) with ⟨hA, hB, _hne, _hAB⟩
  exact Finset.mem_product.mpr ⟨hA, hB⟩

theorem card_o1aSingletonCorePairUniverse_le_coreSliceContains_sq
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (h : α) :
    (o1aSingletonCorePairUniverse family h).card ≤ (coreSliceContains family h).card ^ 2 := by
  calc
    (o1aSingletonCorePairUniverse family h).card ≤
        ((coreSliceContains family h).product (coreSliceContains family h)).card := by
          exact Finset.card_le_card
            (o1aSingletonCorePairUniverse_subset_product_coreSliceContains family h)
    _ = (coreSliceContains family h).card * (coreSliceContains family h).card := by
          simp [Finset.card_product]
    _ = (coreSliceContains family h).card ^ 2 := by
          simp [pow_two]

theorem sdiff_union_subset_sdiff_singleton_of_mem_o1aSingletonCorePairUniverse
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {h : α}
    {p : Finset α × Finset α}
    (hp : p ∈ o1aSingletonCorePairUniverse family h) :
    ground \ (p.1 ∪ p.2) ⊆ ground \ ({h} : Finset α) := by
  rcases (mem_o1aSingletonCorePairUniverse_iff.mp hp) with ⟨hA, _hB, _hne, _hAB⟩
  have hhA : h ∈ p.1 := (Finset.mem_filter.mp hA).2
  intro x hx
  rcases Finset.mem_sdiff.mp hx with ⟨hxg, hxnot⟩
  refine Finset.mem_sdiff.mpr ⟨hxg, ?_⟩
  intro hxh
  have hxEq : x = h := Finset.mem_singleton.mp hxh
  have hxUnion : x ∈ p.1 ∪ p.2 := Finset.mem_union.mpr (Or.inl (hxEq ▸ hhA))
  exact hxnot hxUnion

theorem sum_o1aSingletonCorePairUniverse_le_card_mul_maxSunflowerFreeCard_sdiff
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {h : α} :
    ∑ p ∈ o1aSingletonCorePairUniverse family h,
      maxSunflowerFreeCard (ground \ (p.1 ∪ p.2)) 3 ≤
        (o1aSingletonCorePairUniverse family h).card *
          maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 := by
  let M := maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3
  have hterm :
      ∀ p ∈ o1aSingletonCorePairUniverse family h,
        maxSunflowerFreeCard (ground \ (p.1 ∪ p.2)) 3 ≤ M := by
    intro p hp
    exact
      (maxSunflowerFreeCard_mono_of_subset (k := 3)
        (sdiff_union_subset_sdiff_singleton_of_mem_o1aSingletonCorePairUniverse
          (family := family) (ground := ground) (h := h) hp))
  calc
    ∑ p ∈ o1aSingletonCorePairUniverse family h,
        maxSunflowerFreeCard (ground \ (p.1 ∪ p.2)) 3
      ≤ ∑ p ∈ o1aSingletonCorePairUniverse family h, M := by
          refine Finset.sum_le_sum ?_
          intro p hp
          exact hterm p hp
    _ = (o1aSingletonCorePairUniverse family h).card * M := by
          simp [M, Finset.sum_const_nat]

theorem global_family_card_export_with_pair_count_under_O1aUpgradeRegime
    {α : Type u} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h : α}
    (B : ℕ → ℕ) (A : ℕ)
    (hreg : O1aUpgradeRegime family ground A0 h)
    (h2 : 2 ≤ maxCoDegree family ground)
    (hKeyImage : o1a_wlcert_key_image_bound_target.{u} B)
    (hSplitBuilder :
      let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h
      let hdom : ∀ S ∈ dom, Nonempty (WLcert family S) :=
        wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
          (family := family) (ground := ground) (A0 := A0) (h := h) hreg
      let keyImage := dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)
      ∀ k : WLcertKey α, k ∈ keyImage →
        let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
        ∀ Sstar : {S // S ∈ dom}, ∀ hSstar : Sstar ∈ fiber,
          (∀ Ssub ∈ fiber, Ssub ≠ Sstar →
            ∃ x,
              x ∈ realizedXSet
                (dom := dom) fiber Sstar.1 (ground \ (k.2.2.1 ∪ k.2.2.2.1)) ∧
              x ∈ Ssub.1 ∧ x ∉ Sstar.1) →
          ((∃ j, j ∈ Sstar.1 ∧ j ∈ Nmax family ground h ∧
              ∃ U ∈ WmaxAt family ground h j, ∃ V ∈ WmaxAt family ground h j, U ≠ V) ∨
            Sstar.1 ∩ supportMaxCoDegreePairs family ground = ∅) →
          KeyBadAggZeroAt
            (family := family) (ground := ground) (A0 := A0) (h0 := h)
            hreg k Sstar (by simpa [fiber] using hSstar))
    (hRemainder :
      (B ground.card * (coreSliceContains family h).card ^ 2) * (ground.card ^ 20) ≤ A) :
    family.card ≤
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      A +
      (o1aSingletonCorePairUniverse family h).card *
        maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 := by
  let M := maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3
  have hBase :=
    global_family_card_export_with_chain_bound_and_singletonCore_sum_under_O1aUpgradeRegime
      (family := family) (ground := ground) (A0 := A0) (h := h) (B := B) (A := A)
      hreg h2 hKeyImage hSplitBuilder hRemainder
  have hSum :
      ∑ p ∈ o1aSingletonCorePairUniverse family h,
        maxSunflowerFreeCard (ground \ (p.1 ∪ p.2)) 3 ≤
          (o1aSingletonCorePairUniverse family h).card * M := by
    simpa [M] using
      sum_o1aSingletonCorePairUniverse_le_card_mul_maxSunflowerFreeCard_sdiff
        (family := family) (ground := ground) (h := h)
  have hStep :
      M + M + M + M + A +
          (∑ p ∈ o1aSingletonCorePairUniverse family h,
            maxSunflowerFreeCard (ground \ (p.1 ∪ p.2)) 3) ≤
        M + M + M + M + A +
          (o1aSingletonCorePairUniverse family h).card * M := by
    have h' :
        A +
            (∑ p ∈ o1aSingletonCorePairUniverse family h,
              maxSunflowerFreeCard (ground \ (p.1 ∪ p.2)) 3) ≤
          A + (o1aSingletonCorePairUniverse family h).card * M :=
      Nat.add_le_add_left hSum A
    have h'' :
        M + M + M + M +
            (A +
              ∑ p ∈ o1aSingletonCorePairUniverse family h,
                maxSunflowerFreeCard (ground \ (p.1 ∪ p.2)) 3) ≤
          M + M + M + M + (A + (o1aSingletonCorePairUniverse family h).card * M) :=
      Nat.add_le_add_left h' (M + M + M + M)
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h''
  have hBase' :
      family.card ≤
        M + M + M + M + A +
          (∑ p ∈ o1aSingletonCorePairUniverse family h,
            maxSunflowerFreeCard (ground \ (p.1 ∪ p.2)) 3) := by
    simpa [M, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hBase
  exact hBase'.trans hStep

theorem global_family_card_export_with_coreSliceContains_sq_under_O1aUpgradeRegime
    {α : Type u} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h : α}
    (B : ℕ → ℕ) (A : ℕ)
    (hreg : O1aUpgradeRegime family ground A0 h)
    (h2 : 2 ≤ maxCoDegree family ground)
    (hKeyImage : o1a_wlcert_key_image_bound_target.{u} B)
    (hSplitBuilder :
      let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h
      let hdom : ∀ S ∈ dom, Nonempty (WLcert family S) :=
        wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
          (family := family) (ground := ground) (A0 := A0) (h := h) hreg
      let keyImage := dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)
      ∀ k : WLcertKey α, k ∈ keyImage →
        let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
        ∀ Sstar : {S // S ∈ dom}, ∀ hSstar : Sstar ∈ fiber,
          (∀ Ssub ∈ fiber, Ssub ≠ Sstar →
            ∃ x,
              x ∈ realizedXSet
                (dom := dom) fiber Sstar.1 (ground \ (k.2.2.1 ∪ k.2.2.2.1)) ∧
              x ∈ Ssub.1 ∧ x ∉ Sstar.1) →
          ((∃ j, j ∈ Sstar.1 ∧ j ∈ Nmax family ground h ∧
              ∃ U ∈ WmaxAt family ground h j, ∃ V ∈ WmaxAt family ground h j, U ≠ V) ∨
            Sstar.1 ∩ supportMaxCoDegreePairs family ground = ∅) →
          KeyBadAggZeroAt
            (family := family) (ground := ground) (A0 := A0) (h0 := h)
            hreg k Sstar (by simpa [fiber] using hSstar))
    (hRemainder :
      (B ground.card * (coreSliceContains family h).card ^ 2) * (ground.card ^ 20) ≤ A) :
    family.card ≤
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      A +
      (coreSliceContains family h).card ^ 2 *
        maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 := by
  let M := maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3
  have hBase :=
    global_family_card_export_with_pair_count_under_O1aUpgradeRegime
      (family := family) (ground := ground) (A0 := A0) (h := h) (B := B) (A := A)
      hreg h2 hKeyImage hSplitBuilder hRemainder
  have hPairs :
      (o1aSingletonCorePairUniverse family h).card * M ≤
        (coreSliceContains family h).card ^ 2 * M := by
    exact Nat.mul_le_mul_right M
      (card_o1aSingletonCorePairUniverse_le_coreSliceContains_sq family h)
  have hStep :
      M + M + M + M + A + (o1aSingletonCorePairUniverse family h).card * M ≤
        M + M + M + M + A + (coreSliceContains family h).card ^ 2 * M := by
    have h' :
        A + (o1aSingletonCorePairUniverse family h).card * M ≤
          A + (coreSliceContains family h).card ^ 2 * M :=
      Nat.add_le_add_left hPairs A
    have h'' :
        M + M + M + M + (A + (o1aSingletonCorePairUniverse family h).card * M) ≤
          M + M + M + M + (A + (coreSliceContains family h).card ^ 2 * M) :=
      Nat.add_le_add_left h' (M + M + M + M)
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h''
  have hBase' :
      family.card ≤
        M + M + M + M + A + (o1aSingletonCorePairUniverse family h).card * M := by
    simpa [M, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hBase
  exact hBase'.trans hStep

theorem global_family_card_export_with_M_cube_under_O1aUpgradeRegime
    {α : Type u} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h : α}
    (B : ℕ → ℕ) (A : ℕ)
    (hreg : O1aUpgradeRegime family ground A0 h)
    (h2 : 2 ≤ maxCoDegree family ground)
    (hKeyImage : o1a_wlcert_key_image_bound_target.{u} B)
    (hSplitBuilder :
      let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h
      let hdom : ∀ S ∈ dom, Nonempty (WLcert family S) :=
        wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
          (family := family) (ground := ground) (A0 := A0) (h := h) hreg
      let keyImage := dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)
      ∀ k : WLcertKey α, k ∈ keyImage →
        let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
        ∀ Sstar : {S // S ∈ dom}, ∀ hSstar : Sstar ∈ fiber,
          (∀ Ssub ∈ fiber, Ssub ≠ Sstar →
            ∃ x,
              x ∈ realizedXSet
                (dom := dom) fiber Sstar.1 (ground \ (k.2.2.1 ∪ k.2.2.2.1)) ∧
              x ∈ Ssub.1 ∧ x ∉ Sstar.1) →
          ((∃ j, j ∈ Sstar.1 ∧ j ∈ Nmax family ground h ∧
              ∃ U ∈ WmaxAt family ground h j, ∃ V ∈ WmaxAt family ground h j, U ≠ V) ∨
            Sstar.1 ∩ supportMaxCoDegreePairs family ground = ∅) →
          KeyBadAggZeroAt
            (family := family) (ground := ground) (A0 := A0) (h0 := h)
            hreg k Sstar (by simpa [fiber] using hSstar))
    (hRemainder :
      (B ground.card * (coreSliceContains family h).card ^ 2) * (ground.card ^ 20) ≤ A) :
    family.card ≤
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      A +
      (maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3) ^ 3 := by
  let M := maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3
  have hBase :=
    global_family_card_export_with_coreSliceContains_sq_under_O1aUpgradeRegime
      (family := family) (ground := ground) (A0 := A0) (h := h) (B := B) (A := A)
      hreg h2 hKeyImage hSplitBuilder hRemainder
  have hCore : (coreSliceContains family h).card ≤ M := by
    simpa [M] using
      card_coreSliceContains_le_maxSunflowerFreeCard_sdiff
        (family := family) (ground := ground) (h := h) hreg.1 hreg.2.1
  have hSq : (coreSliceContains family h).card ^ 2 ≤ M ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul hCore hCore
  have hCube :
      (coreSliceContains family h).card ^ 2 * M ≤ M ^ 2 * M := by
    exact Nat.mul_le_mul_right M hSq
  have hStep :
      M + M + M + M + A + (coreSliceContains family h).card ^ 2 * M ≤
        M + M + M + M + A + M ^ 3 := by
    have h' :
        A + (coreSliceContains family h).card ^ 2 * M ≤ A + M ^ 3 := by
      have h'' : A + (coreSliceContains family h).card ^ 2 * M ≤ A + (M ^ 2 * M) :=
        Nat.add_le_add_left hCube A
      simpa [pow_succ, Nat.add_assoc, Nat.mul_assoc] using h''
    have h'' :
        M + M + M + M + (A + (coreSliceContains family h).card ^ 2 * M) ≤
          M + M + M + M + (A + M ^ 3) :=
      Nat.add_le_add_left h' (M + M + M + M)
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h''
  have hBase' :
      family.card ≤
        M + M + M + M + A + (coreSliceContains family h).card ^ 2 * M := by
    simpa [M, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hBase
  exact hBase'.trans hStep

theorem global_family_card_export_with_explicit_remainder_under_O1aUpgradeRegime
    {α : Type u} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h : α}
    (B : ℕ → ℕ)
    (hreg : O1aUpgradeRegime family ground A0 h)
    (h2 : 2 ≤ maxCoDegree family ground)
    (hKeyImage : o1a_wlcert_key_image_bound_target.{u} B)
    (hSplitBuilder :
      let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h
      let hdom : ∀ S ∈ dom, Nonempty (WLcert family S) :=
        wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
          (family := family) (ground := ground) (A0 := A0) (h := h) hreg
      let keyImage := dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)
      ∀ k : WLcertKey α, k ∈ keyImage →
        let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
        ∀ Sstar : {S // S ∈ dom}, ∀ hSstar : Sstar ∈ fiber,
          (∀ Ssub ∈ fiber, Ssub ≠ Sstar →
            ∃ x,
              x ∈ realizedXSet
                (dom := dom) fiber Sstar.1 (ground \ (k.2.2.1 ∪ k.2.2.2.1)) ∧
              x ∈ Ssub.1 ∧ x ∉ Sstar.1) →
          ((∃ j, j ∈ Sstar.1 ∧ j ∈ Nmax family ground h ∧
              ∃ U ∈ WmaxAt family ground h j, ∃ V ∈ WmaxAt family ground h j, U ≠ V) ∨
            Sstar.1 ∩ supportMaxCoDegreePairs family ground = ∅) →
          KeyBadAggZeroAt
            (family := family) (ground := ground) (A0 := A0) (h0 := h)
            hreg k Sstar (by simpa [fiber] using hSstar)) :
    family.card ≤
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      (B ground.card * (coreSliceContains family h).card ^ 2) * (ground.card ^ 20) +
      (maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3) ^ 3 := by
  exact
    global_family_card_export_with_M_cube_under_O1aUpgradeRegime
      (family := family) (ground := ground) (A0 := A0) (h := h)
      (B := B)
      (A := (B ground.card * (coreSliceContains family h).card ^ 2) * (ground.card ^ 20))
      hreg h2 hKeyImage hSplitBuilder (le_rfl)

theorem global_family_card_export_with_explicit_M_remainder_under_O1aUpgradeRegime
    {α : Type u} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h : α}
    (B : ℕ → ℕ)
    (hreg : O1aUpgradeRegime family ground A0 h)
    (h2 : 2 ≤ maxCoDegree family ground)
    (hKeyImage : o1a_wlcert_key_image_bound_target.{u} B)
    (hSplitBuilder :
      let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h
      let hdom : ∀ S ∈ dom, Nonempty (WLcert family S) :=
        wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
          (family := family) (ground := ground) (A0 := A0) (h := h) hreg
      let keyImage := dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)
      ∀ k : WLcertKey α, k ∈ keyImage →
        let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
        ∀ Sstar : {S // S ∈ dom}, ∀ hSstar : Sstar ∈ fiber,
          (∀ Ssub ∈ fiber, Ssub ≠ Sstar →
            ∃ x,
              x ∈ realizedXSet
                (dom := dom) fiber Sstar.1 (ground \ (k.2.2.1 ∪ k.2.2.2.1)) ∧
              x ∈ Ssub.1 ∧ x ∉ Sstar.1) →
          ((∃ j, j ∈ Sstar.1 ∧ j ∈ Nmax family ground h ∧
              ∃ U ∈ WmaxAt family ground h j, ∃ V ∈ WmaxAt family ground h j, U ≠ V) ∨
            Sstar.1 ∩ supportMaxCoDegreePairs family ground = ∅) →
          KeyBadAggZeroAt
            (family := family) (ground := ground) (A0 := A0) (h0 := h)
            hreg k Sstar (by simpa [fiber] using hSstar)) :
    family.card ≤
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      (B ground.card * (maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3) ^ 2) *
        (ground.card ^ 20) +
      (maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3) ^ 3 := by
  let M := maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3
  have hBase :=
    global_family_card_export_with_explicit_remainder_under_O1aUpgradeRegime
      (family := family) (ground := ground) (A0 := A0) (h := h) (B := B)
      hreg h2 hKeyImage hSplitBuilder
  have hCore : (coreSliceContains family h).card ≤ M := by
    simpa [M] using
      card_coreSliceContains_le_maxSunflowerFreeCard_sdiff
        (family := family) (ground := ground) (h := h) hreg.1 hreg.2.1
  have hSq : (coreSliceContains family h).card ^ 2 ≤ M ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul hCore hCore
  have hRem :
      (B ground.card * (coreSliceContains family h).card ^ 2) * (ground.card ^ 20) ≤
        (B ground.card * M ^ 2) * (ground.card ^ 20) := by
    exact Nat.mul_le_mul_right (ground.card ^ 20) (Nat.mul_le_mul_left (B ground.card) hSq)
  have hStep :
      M + M + M + M +
          (B ground.card * (coreSliceContains family h).card ^ 2) * (ground.card ^ 20) +
          M ^ 3 ≤
        M + M + M + M + (B ground.card * M ^ 2) * (ground.card ^ 20) + M ^ 3 := by
    have h' :
        (B ground.card * (coreSliceContains family h).card ^ 2) * (ground.card ^ 20) + M ^ 3 ≤
          (B ground.card * M ^ 2) * (ground.card ^ 20) + M ^ 3 :=
      Nat.add_le_add_right hRem (M ^ 3)
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (Nat.add_le_add_left h' (M + M + M + M))
  have hBase' :
      family.card ≤
        M + M + M + M +
          (B ground.card * (coreSliceContains family h).card ^ 2) * (ground.card ^ 20) +
          M ^ 3 := by
    simpa [M, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hBase
  have hStep' :
      M + M + M + M +
          (B ground.card * M ^ 2) * (ground.card ^ 20) +
          M ^ 3 =
        M + M + M + M +
          (B ground.card * (maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3) ^ 2) *
            (ground.card ^ 20) +
          (maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3) ^ 3 := by
    simp [M]
  exact (hBase'.trans hStep).trans_eq hStep'

/--
Reusable packaged builder target for the O₁a global-export lane.

This names the exact split-to-`KeyBadAgg` builder hypothesis that feeds the
explicit polynomial remainder export, so later route theorems can quantify over
one compact predicate instead of repeating the full witness-lift domain shape.
-/
def o1aSplitBuilderTarget
    {α : Type u} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (A0 : ℕ) (h : α)
    (hreg : O1aUpgradeRegime family ground A0 h) : Prop :=
  let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h
  let hdom : ∀ S ∈ dom, Nonempty (WLcert family S) :=
    wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
      (family := family) (ground := ground) (A0 := A0) (h := h) hreg
  let keyImage := dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)
  ∀ k : WLcertKey α, k ∈ keyImage →
    let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
    ∀ Sstar : {S // S ∈ dom}, ∀ hSstar : Sstar ∈ fiber,
      (∀ Ssub ∈ fiber, Ssub ≠ Sstar →
        ∃ x,
          x ∈ realizedXSet
            (dom := dom) fiber Sstar.1 (ground \ (k.2.2.1 ∪ k.2.2.2.1)) ∧
          x ∈ Ssub.1 ∧ x ∉ Sstar.1) →
      ((∃ j, j ∈ Sstar.1 ∧ j ∈ Nmax family ground h ∧
          ∃ U ∈ WmaxAt family ground h j, ∃ V ∈ WmaxAt family ground h j, U ≠ V) ∨
        Sstar.1 ∩ supportMaxCoDegreePairs family ground = ∅) →
      KeyBadAggZeroAt
        (family := family) (ground := ground) (A0 := A0) (h0 := h)
        hreg k Sstar (by simpa [fiber] using hSstar)

/--
Compact interface form of the explicit polynomial remainder export.

This is the same global export theorem as
`global_family_card_export_with_explicit_M_remainder_under_O1aUpgradeRegime`,
but with the long split-builder hypothesis compressed into
`o1aSplitBuilderTarget`.
-/
theorem global_family_card_export_with_explicit_M_remainder_under_O1aUpgradeRegime_pkg
    {α : Type u} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h : α}
    (B : ℕ → ℕ)
    (hreg : O1aUpgradeRegime family ground A0 h)
    (h2 : 2 ≤ maxCoDegree family ground)
    (hKeyImage : o1a_wlcert_key_image_bound_target.{u} B)
    (hSplitBuilder : o1aSplitBuilderTarget family ground A0 h hreg) :
    family.card ≤
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
      (B ground.card * (maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3) ^ 2) *
        (ground.card ^ 20) +
      (maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3) ^ 3 := by
  simpa [o1aSplitBuilderTarget] using
    global_family_card_export_with_explicit_M_remainder_under_O1aUpgradeRegime
      (family := family) (ground := ground) (A0 := A0) (h := h) (B := B)
      hreg h2 hKeyImage hSplitBuilder

/--
Problem-facing O₁a export package above the anchored explicit-remainder theorem.

Given an `O₁a` obstruction witness and a packaged split-builder target, we can
choose an anchored coordinate `h` and export the whole family into the explicit
polynomial-remainder inequality on `ground \\ {h}`.
-/
theorem exists_anchor_with_explicit_M_remainder_export_of_ObstructionO1a
    {α : Type u} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ}
    (B : ℕ → ℕ)
    (hground : family ⊆ ground.powerset)
    (hfree : IsSunflowerFree family 3)
    (hmax : ∀ T ⊆ ground, T ∉ family → ¬ IsSunflowerFree (insert T family) 3)
    (hfail : hiFail family ground A0)
    (hO1a : ObstructionO1a family ground)
    (h2 : 2 ≤ maxCoDegree family ground)
    (hKeyImage : o1a_wlcert_key_image_bound_target.{u} B)
    (hSplitBuilder :
      ∀ {h : α}, (hreg : O1aUpgradeRegime family ground A0 h) →
        o1aSplitBuilderTarget family ground A0 h hreg) :
    ∃ h, maxPairsAnchoredAt family ground h ∧
      family.card ≤
        maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
        maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
        maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
        maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 +
        (B ground.card * (maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3) ^ 2) *
          (ground.card ^ 20) +
        (maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3) ^ 3 := by
  rcases hO1a with ⟨h, hanch⟩
  let hreg : O1aUpgradeRegime family ground A0 h :=
    ⟨hground, hfree, hmax, hfail, hanch⟩
  refine ⟨h, hanch, ?_⟩
  exact global_family_card_export_with_explicit_M_remainder_under_O1aUpgradeRegime_pkg
    (family := family) (ground := ground) (A0 := A0) (h := h) (B := B)
    hreg h2 hKeyImage (hSplitBuilder hreg)


end SunflowerLean
