/-
  M3 t=2 Mantel-tight reduction (goal-stack B3.2a).

  CONDITIONAL structural reduction: if the disjointness graph of a cap-2
  3-sunflower-free family is Turán-maximal (attains Mantel's triangle-free edge
  maximum), then the family splits into two intersecting cap-2 sunflower-free
  parts on disjoint supports — i.e. two `I3(l,2)`-admissible families. This
  reduces `M3(l,2)` to the intersecting bound `I3(l,2)` *within the Mantel-tight
  subclass*. It does NOT establish global `M3(l,2) = 2·I3(l,2)`: that would need
  every extremizer to be Mantel-tight, or a stability theorem (both open). See
  erdos-problems .../857/B3_T2_UPPER_BOUND_WORKNOTES.md §B3.2a.

  Reuses the B4 `disjGraph` + `isTuranMaximal_iff_nonempty_iso_turanGraph`
  colour-class bipartition machinery from `M3/T1MSide.lean`.
-/

import SunflowerLean.M3.T1MSide

namespace M3

variable {α : Type*} [DecidableEq α]

/-- General bipartition from Turán-maximality of the disjointness graph: if
    `disjGraph F` is `IsTuranMaximal 2`, the two Turán colour classes give a
    split `F = G ⊔ H` with each part intersecting and every cross-pair disjoint.
    No cap/uniformity is needed — `IsTuranMaximal 2` already encodes
    triangle-freeness, and within a colour class non-adjacency means
    not-disjoint, i.e. intersecting. -/
lemma disjGraph_turanMaximal_bipartition {F : Finset (Finset α)}
    (htm : (disjGraph F).IsTuranMaximal 2) :
    ∃ G H : Finset (Finset α),
      G ∪ H = F ∧ Disjoint G H ∧
      IsIntersectingFam G ∧ IsIntersectingFam H ∧
      (∀ a ∈ G, ∀ b ∈ H, a ∩ b = ∅) := by
  classical
  obtain ⟨f⟩ := (SimpleGraph.isTuranMaximal_iff_nonempty_iso_turanGraph
    (G := disjGraph F) (r := 2) (by norm_num)).mp htm
  have hadj : ∀ v w : {S : Finset α // S ∈ F},
      (disjGraph F).Adj v w ↔ (f v).val % 2 ≠ (f w).val % 2 :=
    fun v w => (f.map_adj_iff).symm.trans SimpleGraph.turanGraph_adj
  have himg : (Finset.univ : Finset {S : Finset α // S ∈ F}).image Subtype.val = F := by
    ext S
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨v, hv⟩ => hv ▸ v.2, fun hS => ⟨⟨S, hS⟩, rfl⟩⟩
  refine ⟨(Finset.univ.filter (fun v : {S // S ∈ F} => (f v).val % 2 = 0)).image Subtype.val,
          (Finset.univ.filter (fun v : {S // S ∈ F} => (f v).val % 2 = 1)).image Subtype.val,
          ?_, ?_, ?_, ?_, ?_⟩
  · -- union = F
    rw [← Finset.image_union]
    have hcover : (Finset.univ.filter (fun v : {S // S ∈ F} => (f v).val % 2 = 0))
        ∪ (Finset.univ.filter (fun v : {S // S ∈ F} => (f v).val % 2 = 1)) = Finset.univ := by
      ext v
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      rcases Nat.mod_two_eq_zero_or_one (f v).val with h | h
      · exact Or.inl h
      · exact Or.inr h
    rw [hcover, himg]
  · -- disjoint parts
    rw [Finset.disjoint_left]
    rintro S hSA hSB
    rw [Finset.mem_image] at hSA hSB
    obtain ⟨a, ha, rfl⟩ := hSA
    obtain ⟨b, hb, hba⟩ := hSB
    rw [Finset.mem_filter] at ha hb
    have hab : a = b := Subtype.ext hba.symm
    rw [hab] at ha
    omega
  · -- intersecting G
    intro S hS T hT hST
    rw [Finset.mem_image] at hS hT
    obtain ⟨a, ha, rfl⟩ := hS
    obtain ⟨b, hb, rfl⟩ := hT
    rw [Finset.mem_filter] at ha hb
    have hnadj : ¬ (disjGraph F).Adj a b := by rw [hadj a b]; push_neg; omega
    exact Finset.nonempty_iff_ne_empty.mpr (fun hemp => hnadj ⟨hemp, hST⟩)
  · -- intersecting H
    intro S hS T hT hST
    rw [Finset.mem_image] at hS hT
    obtain ⟨a, ha, rfl⟩ := hS
    obtain ⟨b, hb, rfl⟩ := hT
    rw [Finset.mem_filter] at ha hb
    have hnadj : ¬ (disjGraph F).Adj a b := by rw [hadj a b]; push_neg; omega
    exact Finset.nonempty_iff_ne_empty.mpr (fun hemp => hnadj ⟨hemp, hST⟩)
  · -- cross-disjoint
    intro S hS T hT
    rw [Finset.mem_image] at hS hT
    obtain ⟨a, ha, rfl⟩ := hS
    obtain ⟨b, hb, rfl⟩ := hT
    rw [Finset.mem_filter] at ha hb
    have hadj_ab : (disjGraph F).Adj a b := by rw [hadj a b]; omega
    exact hadj_ab.1

/-- **B3.2a (conditional Mantel-tight reduction).** If `F` is `l`-uniform,
    cap-2, 3-sunflower-free, and its disjointness graph is Turán-maximal
    (`IsTuranMaximal 2`), then `F` splits into two `I3(l,2)`-admissible
    (intersecting cap-2 SF-free) parts on disjoint supports. This reduces
    `M3(l,2)` to `I3(l,2)` **within the Mantel-tight subclass** — it does NOT
    prove global `M3(l,2) = 2·I3(l,2)` (which needs every extremizer Mantel-tight
    or a stability theorem). -/
theorem M3_mantel_tight_reduction {F : Finset (Finset α)} {l : ℕ}
    (hu : IsUniform F l) (hc : PairwiseCapped F 2) (hsf : IsSunflowerFree F 3)
    (htm : (disjGraph F).IsTuranMaximal 2) :
    ∃ G H : Finset (Finset α),
      G ∪ H = F ∧ Disjoint G H ∧
      I3Admissible G l 2 ∧ I3Admissible H l 2 ∧
      Disjoint (G.biUnion id) (H.biUnion id) := by
  obtain ⟨G, H, hunion, hdisj, hGint, hHint, hcross⟩ := disjGraph_turanMaximal_bipartition htm
  have hGsub : G ⊆ F := hunion ▸ Finset.subset_union_left
  have hHsub : H ⊆ F := hunion ▸ Finset.subset_union_right
  have inherit : ∀ {K : Finset (Finset α)}, K ⊆ F →
      IsUniform K l ∧ PairwiseCapped K 2 ∧ IsSunflowerFree K 3 :=
    fun {K} hK => ⟨fun S hS => hu S (hK hS),
                   fun S hS T hT hne => hc S (hK hS) T (hK hT) hne,
                   fun sub hsub => hsf sub (hsub.trans hK)⟩
  refine ⟨G, H, hunion, hdisj, ⟨inherit hGsub, hGint⟩, ⟨inherit hHsub, hHint⟩, ?_⟩
  rw [Finset.disjoint_left]
  intro x hxG hxH
  rw [Finset.mem_biUnion] at hxG hxH
  obtain ⟨a, ha, hxa⟩ := hxG
  obtain ⟨b, hb, hxb⟩ := hxH
  simp only [id_eq] at hxa hxb
  have hxab : x ∈ a ∩ b := Finset.mem_inter.mpr ⟨hxa, hxb⟩
  rw [hcross a ha b hb] at hxab
  exact Finset.not_mem_empty x hxab

end M3
