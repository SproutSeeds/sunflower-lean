/-
  M3 t=1 M-side classification (goal-stack B4), the global disjointness-graph
  route. Target: an extremal M3(l,1) family (card 2l+2) is two disjoint copies
  of the K_{l+1} vertex-star family. The assembly step (given the balanced
  bipartition) is `M3_extremal_two_disjoint_stars_of_split` in T1Rigidity.lean;
  this file builds toward producing that bipartition (B4.1/B4.2) via the
  disjointness graph and mathlib's Turán theory. See
  `B4_MSIDE_CLASSIFICATION_BLUEPRINT.md`.

  STATUS 2026-06-13: B4 CLOSED (kernel). Full chain done here — disjointness
  graph + triangle-freeness, the exact edge count (l+1)² (upper Turán bound +
  extremal lower bound + edge↔pair bridge), `IsTuranMaximal 2`, the isomorphism
  to `turanGraph (2l+2) 2`, the balanced Finset bipartition extracted from the
  Turán colour classes (`disjGraph_extremal_bipartition`), and finally the full
  M-side extremal classification `M3_extremal_classification` (extremal M3(l,1)
  family = two disjoint complete-graph star copies on disjoint supports), via
  `M3_extremal_two_disjoint_stars_of_split`.
-/

import SunflowerLean.M3.T1Rigidity
import SunflowerLean.M3.T2Counting

namespace M3

variable {α : Type*} [DecidableEq α]

/-- The **disjointness graph** of a family `F`: vertices are the members of `F`
    (as a subtype), with an edge between two distinct members iff they are
    disjoint. -/
def disjGraph (F : Finset (Finset α)) : SimpleGraph {S : Finset α // S ∈ F} where
  Adj a b := a.1 ∩ b.1 = ∅ ∧ a.1 ≠ b.1
  symm := by
    rintro a b ⟨h, hne⟩
    exact ⟨by rw [Finset.inter_comm]; exact h, hne.symm⟩
  loopless := by
    rintro a ⟨_, hne⟩
    exact hne rfl

instance disjGraph_decidableAdj (F : Finset (Finset α)) :
    DecidableRel (disjGraph F).Adj :=
  fun a b => inferInstanceAs (Decidable (a.1 ∩ b.1 = ∅ ∧ a.1 ≠ b.1))

/-- B4.2 step 1: in a 3-sunflower-free family, the disjointness graph is
    triangle-free — three pairwise-disjoint members would be an empty-core
    3-sunflower. -/
lemma disjGraph_cliqueFree {F : Finset (Finset α)} (hsf : IsSunflowerFree F 3) :
    (disjGraph F).CliqueFree 3 := by
  intro t ht
  rw [SimpleGraph.isNClique_iff] at ht
  obtain ⟨hclique, hcard⟩ := ht
  obtain ⟨a, b, c, hab, hac, hbc, ht_eq⟩ := Finset.card_eq_three.mp hcard
  have ha : a ∈ (t : Set {S : Finset α // S ∈ F}) := by rw [ht_eq]; simp
  have hb : b ∈ (t : Set {S : Finset α // S ∈ F}) := by rw [ht_eq]; simp
  have hc : c ∈ (t : Set {S : Finset α // S ∈ F}) := by rw [ht_eq]; simp
  have rab : (disjGraph F).Adj a b := hclique ha hb hab
  have rac : (disjGraph F).Adj a c := hclique ha hc hac
  have rbc : (disjGraph F).Adj b c := hclique hb hc hbc
  exact no_three_with_core hsf a.2 b.2 c.2
    rab.2 rac.2 rbc.2 rab.1 rac.1 rbc.1

/-- B4.2 step 2 (upper half): the Turán bound on the disjointness graph. For an
    SF-free family of size `2l+2`, the disjointness graph has at most `(l+1)²`
    edges (`= ⌊(2l+2)²/4⌋`). The matching *lower* bound (from extremality, via
    the intersecting-pair count) is the remaining piece that upgrades this to
    `IsTuranMaximal`. -/
lemma disjGraph_edge_le {F : Finset (Finset α)} {l : ℕ}
    (hsf : IsSunflowerFree F 3) (hcard : F.card = 2 * l + 2) :
    (disjGraph F).edgeFinset.card ≤ (l + 1) ^ 2 := by
  have hcf : (disjGraph F).CliqueFree 3 := disjGraph_cliqueFree hsf
  have hn : Fintype.card {S : Finset α // S ∈ F} = 2 * l + 2 := by
    rw [Fintype.card_coe]; exact hcard
  have hT := SimpleGraph.CliqueFree.card_edgeFinset_le (G := disjGraph F) (r := 2) hcf
  rw [hn] at hT
  dsimp only at hT
  have hmod : (2 * l + 2) % 2 = 0 := by omega
  rw [hmod] at hT
  have harith : ((2 * l + 2) ^ 2 - 0 ^ 2) * (2 - 1) / (2 * 2) + (0 : ℕ).choose 2
      = (l + 1) ^ 2 := by
    have h4 : (2 * l + 2) ^ 2 = 4 * (l + 1) ^ 2 := by ring
    rw [h4]
    norm_num
  rwa [harith] at hT

/-- B4.1 (lower-bound ingredient): the **global intersecting-pair bound** for a
    cap-1 family. `∑_{(A,B)∈offDiag} |A∩B| ≤ |F|·l`, i.e. `2·I ≤ ml` (so the
    unordered intersecting pairs satisfy `I ≤ ml/2`). Proof: the incidence
    identity `Σ|A∩B| = Σ_x deg(x)(deg(x)−1)`, then `deg(x) ≤ 2` (cap-1 degree
    control) gives `deg(x)(deg(x)−1) ≤ deg(x)` pointwise, and `Σ_x deg(x) = ml`. -/
lemma inter_pairs_le {F : Finset (Finset α)} {l : ℕ} (hF : M3Admissible F l 1) :
    ∑ p ∈ F.offDiag, (p.1 ∩ p.2).card ≤ F.card * l := by
  obtain ⟨hu, hc, hsf⟩ := hF
  rw [inter_card_sum_eq_deg_offDiag]
  calc ∑ x ∈ F.biUnion id, (F.filter (fun S => x ∈ S)).offDiag.card
      ≤ ∑ x ∈ F.biUnion id, (F.filter (fun S => x ∈ S)).card := by
        refine Finset.sum_le_sum (fun x _ => ?_)
        rw [Finset.offDiag_card]
        have hd : (F.filter (fun S => x ∈ S)).card ≤ 2 := degree_le_two hc hsf x
        set d := (F.filter (fun S => x ∈ S)).card with hdd
        interval_cases d <;> omega
    _ = F.card * l := degree_sum_eq_card_mul hu

/-- B4.1 (lower bound, offDiag form): at extremality (`|F| = 2l+2`) the number of
    **ordered disjoint pairs** is `≥ 2(l+1)²` — i.e. unordered disjoint pairs
    `D ≥ (l+1)²`. Proof: `offDiag = disjoint ⊎ intersecting`, with
    `|offDiag| = (2l+2)(2l+1)` and `intersecting ≤ |F|·l = (2l+2)l`
    (`inter_pairs_le`), so `disjoint ≥ (2l+2)(2l+1) − (2l+2)l = 2(l+1)²`.
    This is the matching lower half of `disjGraph_edge_le`; together they pin the
    disjoint-pair count at exactly `(l+1)²` (the Turán-maximal value). -/
lemma disjoint_pairs_ge {F : Finset (Finset α)} {l : ℕ}
    (hF : M3Admissible F l 1) (hcard : F.card = 2 * l + 2) :
    2 * (l + 1) ^ 2 ≤ (F.offDiag.filter (fun p => p.1 ∩ p.2 = ∅)).card := by
  -- intersecting (¬disjoint) ordered pairs are ≤ |F|·l, via inter_pairs_le
  have hI : (F.offDiag.filter (fun p => ¬ (p.1 ∩ p.2 = ∅))).card ≤ F.card * l := by
    calc (F.offDiag.filter (fun p => ¬ (p.1 ∩ p.2 = ∅))).card
        = ∑ p ∈ F.offDiag, (if ¬ (p.1 ∩ p.2 = ∅) then 1 else 0) := by
          rw [Finset.card_filter]
      _ ≤ ∑ p ∈ F.offDiag, (p.1 ∩ p.2).card := by
          refine Finset.sum_le_sum (fun p _ => ?_)
          by_cases h : p.1 ∩ p.2 = ∅
          · rw [if_neg (not_not.mpr h)]; exact Nat.zero_le _
          · rw [if_pos h]
            exact Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr h)
      _ ≤ F.card * l := inter_pairs_le hF
  -- offDiag splits into disjoint + ¬disjoint
  have hpart : (F.offDiag.filter (fun p => p.1 ∩ p.2 = ∅)).card
      + (F.offDiag.filter (fun p => ¬ (p.1 ∩ p.2 = ∅))).card = F.offDiag.card :=
    Finset.filter_card_add_filter_neg_card_eq_card _
  have hod : F.offDiag.card = (2 * l + 2) * (2 * l + 1) := by
    rw [Finset.offDiag_card, hcard]
    have h : (2 * l + 2) * (2 * l + 2) = (2 * l + 2) * (2 * l + 1) + (2 * l + 2) := by
      ring
    omega
  have hDeq : (F.offDiag.filter (fun p => p.1 ∩ p.2 = ∅)).card
      = F.offDiag.card - (F.offDiag.filter (fun p => ¬ (p.1 ∩ p.2 = ∅))).card :=
    Nat.eq_sub_of_add_eq hpart
  have hval : (2 * l + 2) * (2 * l + 1) - (2 * l + 2) * l = 2 * (l + 1) ^ 2 := by
    have h : (2 * l + 2) * (2 * l + 1) = 2 * (l + 1) ^ 2 + (2 * l + 2) * l := by ring
    omega
  have hsub : (2 * l + 2) * (2 * l + 1) - (2 * l + 2) * l
      ≤ (2 * l + 2) * (2 * l + 1)
        - (F.offDiag.filter (fun p => ¬ (p.1 ∩ p.2 = ∅))).card := by
    apply Nat.sub_le_sub_left
    rw [← hcard]; exact hI
  rw [hDeq, hod]
  exact le_trans (le_of_eq hval.symm) hsub

/-- B4.2 bridge: twice the disjointness-graph edge count equals the number of
    **ordered disjoint pairs** of `F`. The map `(a,b) ↦ (a.1, b.1)` bijects
    adjacent ordered vertex pairs (`univ.filter Adj`, which `two_mul_card_edgeFinset`
    equates with `2·#edges`) with the disjoint ordered member pairs of `F`. -/
lemma two_mul_edge_eq_disjoint_pairs {F : Finset (Finset α)} :
    2 * (disjGraph F).edgeFinset.card
      = (F.offDiag.filter (fun p => p.1 ∩ p.2 = ∅)).card := by
  rw [SimpleGraph.two_mul_card_edgeFinset]
  refine Finset.card_bij'
    (fun p _ => (p.1.1, p.2.1))
    (fun q hq => (⟨q.1, (Finset.mem_offDiag.mp (Finset.mem_filter.mp hq).1).1⟩,
                  ⟨q.2, (Finset.mem_offDiag.mp (Finset.mem_filter.mp hq).1).2.1⟩))
    ?_ ?_ ?_ ?_
  · intro p hp
    have hadj : (disjGraph F).Adj p.1 p.2 := (Finset.mem_filter.mp hp).2
    obtain ⟨hdis, hne⟩ := hadj
    rw [Finset.mem_filter, Finset.mem_offDiag]
    exact ⟨⟨p.1.2, p.2.2, hne⟩, hdis⟩
  · intro q hq
    obtain ⟨hod, hdis⟩ := Finset.mem_filter.mp hq
    have hne := (Finset.mem_offDiag.mp hod).2.2
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hdis, hne⟩
  · intro p hp; rfl
  · intro q hq; rfl

/-- B4.1 complete (exact edge count): combining the Turán upper bound
    (`disjGraph_edge_le`), the extremal lower bound (`disjoint_pairs_ge`), and the
    edge↔pair bridge, the disjointness graph of an extremal M3(l,1) family has
    **exactly `(l+1)²` edges** — the Turán-maximal value `⌊(2l+2)²/4⌋`. This is
    the edge-count hypothesis for `IsTuranMaximal`. -/
lemma disjGraph_edge_eq {F : Finset (Finset α)} {l : ℕ}
    (hF : M3Admissible F l 1) (hcard : F.card = 2 * l + 2) :
    (disjGraph F).edgeFinset.card = (l + 1) ^ 2 := by
  have hupper := disjGraph_edge_le hF.2.2 hcard
  have hlower := disjoint_pairs_ge hF hcard
  have hbridge := two_mul_edge_eq_disjoint_pairs (F := F)
  omega

/-- B4.2 (Turán maximality): the disjointness graph of an extremal M3(l,1) family
    is Turán-maximal for triangles. It is `CliqueFree 3` (`disjGraph_cliqueFree`)
    and achieves the maximum edge count `(l+1)²` among all triangle-free graphs on
    its `2l+2` vertices (`disjGraph_edge_eq` meets the universal Turán bound). This
    is the hypothesis of mathlib's `isTuranMaximal_iff_nonempty_iso_turanGraph`,
    the next link toward the balanced bipartition. -/
lemma disjGraph_isTuranMaximal {F : Finset (Finset α)} {l : ℕ}
    (hF : M3Admissible F l 1) (hcard : F.card = 2 * l + 2) :
    (disjGraph F).IsTuranMaximal 2 := by
  refine ⟨disjGraph_cliqueFree hF.2.2, fun H _ hHcf => ?_⟩
  rw [disjGraph_edge_eq hF hcard]
  have hn : Fintype.card {S : Finset α // S ∈ F} = 2 * l + 2 := by
    rw [Fintype.card_coe]; exact hcard
  have hT := SimpleGraph.CliqueFree.card_edgeFinset_le (G := H) (r := 2) hHcf
  rw [hn] at hT
  dsimp only at hT
  have hmod : (2 * l + 2) % 2 = 0 := by omega
  rw [hmod] at hT
  have harith : ((2 * l + 2) ^ 2 - 0 ^ 2) * (2 - 1) / (2 * 2) + (0 : ℕ).choose 2
      = (l + 1) ^ 2 := by
    have h4 : (2 * l + 2) ^ 2 = 4 * (l + 1) ^ 2 := by ring
    rw [h4]; norm_num
  rwa [harith] at hT

/-- B4.2 (iso step): the extremal disjointness graph is isomorphic to the Turán
    graph `turanGraph (2l+2) 2` (the balanced complete bipartite graph) — the
    first half of the bipartition extraction. Immediate from
    `disjGraph_isTuranMaximal` via mathlib's Turán uniqueness theorem. -/
lemma disjGraph_nonempty_iso_turanGraph {F : Finset (Finset α)} {l : ℕ}
    (hF : M3Admissible F l 1) (hcard : F.card = 2 * l + 2) :
    Nonempty (disjGraph F ≃g SimpleGraph.turanGraph (2 * l + 2) 2) := by
  have hn : Fintype.card {S : Finset α // S ∈ F} = 2 * l + 2 := by
    rw [Fintype.card_coe]; exact hcard
  have h := (SimpleGraph.isTuranMaximal_iff_nonempty_iso_turanGraph
    (G := disjGraph F) (r := 2) (by norm_num)).mp (disjGraph_isTuranMaximal hF hcard)
  rwa [hn] at h

/-- Counting helper for the balanced split: exactly `l+1` of the `2l+2` residues
    are even (`= 0 mod 2`), via the bijection `k ↦ 2k` from `Fin (l+1)`. -/
lemma fin_residue0_card (l : ℕ) :
    (Finset.univ.filter (fun i : Fin (2 * l + 2) => i.val % 2 = 0)).card = l + 1 := by
  have hinj : Function.Injective
      (fun k : Fin (l + 1) => (⟨2 * k.val, by have := k.isLt; omega⟩ : Fin (2 * l + 2))) := by
    intro a b hab
    simp only [Fin.mk.injEq] at hab
    exact Fin.ext (by omega)
  have hset : (Finset.univ.filter (fun i : Fin (2 * l + 2) => i.val % 2 = 0))
      = (Finset.univ : Finset (Fin (l + 1))).image
          (fun k => (⟨2 * k.val, by have := k.isLt; omega⟩ : Fin (2 * l + 2))) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hi
      exact ⟨⟨i.val / 2, by have := i.isLt; omega⟩,
        by apply Fin.ext; change 2 * (i.val / 2) = i.val; omega⟩
    · rintro ⟨k, rfl⟩
      change 2 * k.val % 2 = 0; omega
  rw [hset, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-- Counting helper (odd residues), via `k ↦ 2k+1`. -/
lemma fin_residue1_card (l : ℕ) :
    (Finset.univ.filter (fun i : Fin (2 * l + 2) => i.val % 2 = 1)).card = l + 1 := by
  have hinj : Function.Injective
      (fun k : Fin (l + 1) => (⟨2 * k.val + 1, by have := k.isLt; omega⟩ : Fin (2 * l + 2))) := by
    intro a b hab
    simp only [Fin.mk.injEq] at hab
    exact Fin.ext (by omega)
  have hset : (Finset.univ.filter (fun i : Fin (2 * l + 2) => i.val % 2 = 1))
      = (Finset.univ : Finset (Fin (l + 1))).image
          (fun k => (⟨2 * k.val + 1, by have := k.isLt; omega⟩ : Fin (2 * l + 2))) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hi
      exact ⟨⟨i.val / 2, by have := i.isLt; omega⟩,
        by apply Fin.ext; change 2 * (i.val / 2) + 1 = i.val; omega⟩
    · rintro ⟨k, rfl⟩
      change (2 * k.val + 1) % 2 = 1; omega
  rw [hset, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-- **B4 complete (M-side extremal bipartition).** An extremal M3(l,1) family `F`
    (`|F| = 2l+2`) splits as two disjoint, equal-size (`l+1`), intersecting parts
    whose every cross-pair is disjoint — the balanced bipartition forced by the
    Turán structure of the disjointness graph. Feeding this to
    `M3_extremal_two_disjoint_stars_of_split` gives the full
    two-disjoint-star-copies classification of extremal M3(l,1) families. -/
theorem disjGraph_extremal_bipartition {F : Finset (Finset α)} {l : ℕ}
    (hF : M3Admissible F l 1) (hcard : F.card = 2 * l + 2) :
    ∃ A B : Finset (Finset α),
      A ∪ B = F ∧ Disjoint A B ∧
      A.card = l + 1 ∧ B.card = l + 1 ∧
      IsIntersectingFam A ∧ IsIntersectingFam B ∧
      (∀ a ∈ A, ∀ b ∈ B, a ∩ b = ∅) := by
  classical
  obtain ⟨f⟩ := disjGraph_nonempty_iso_turanGraph hF hcard
  -- adjacency in disjGraph ↔ residues differ
  have hadj : ∀ v w : {S : Finset α // S ∈ F},
      (disjGraph F).Adj v w ↔ (f v).val % 2 ≠ (f w).val % 2 :=
    fun v w => (f.map_adj_iff).symm.trans SimpleGraph.turanGraph_adj
  -- the subtype's univ maps onto F under val
  have himg : (Finset.univ : Finset {S : Finset α // S ∈ F}).image Subtype.val = F := by
    ext S
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨v, hv⟩ => hv ▸ v.2, fun hS => ⟨⟨S, hS⟩, rfl⟩⟩
  -- card transports through the iso
  have htransA : (Finset.univ.filter (fun v : {S // S ∈ F} => (f v).val % 2 = 0)).card
      = (Finset.univ.filter (fun i : Fin (2 * l + 2) => i.val % 2 = 0)).card := by
    apply Finset.card_bij' (fun v _ => f v) (fun i _ => f.symm i)
    · intro v hv; rw [Finset.mem_filter] at hv ⊢; exact ⟨Finset.mem_univ _, hv.2⟩
    · intro i hi; rw [Finset.mem_filter] at hi ⊢
      exact ⟨Finset.mem_univ _, by rw [f.apply_symm_apply]; exact hi.2⟩
    · intro v _; exact f.symm_apply_apply v
    · intro i _; exact f.apply_symm_apply i
  have htransB : (Finset.univ.filter (fun v : {S // S ∈ F} => (f v).val % 2 = 1)).card
      = (Finset.univ.filter (fun i : Fin (2 * l + 2) => i.val % 2 = 1)).card := by
    apply Finset.card_bij' (fun v _ => f v) (fun i _ => f.symm i)
    · intro v hv; rw [Finset.mem_filter] at hv ⊢; exact ⟨Finset.mem_univ _, hv.2⟩
    · intro i hi; rw [Finset.mem_filter] at hi ⊢
      exact ⟨Finset.mem_univ _, by rw [f.apply_symm_apply]; exact hi.2⟩
    · intro v _; exact f.symm_apply_apply v
    · intro i _; exact f.apply_symm_apply i
  refine ⟨(Finset.univ.filter (fun v : {S // S ∈ F} => (f v).val % 2 = 0)).image Subtype.val,
          (Finset.univ.filter (fun v : {S // S ∈ F} => (f v).val % 2 = 1)).image Subtype.val,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · -- disjoint
    rw [Finset.disjoint_left]
    rintro S hSA hSB
    rw [Finset.mem_image] at hSA hSB
    obtain ⟨a, ha, rfl⟩ := hSA
    obtain ⟨b, hb, hba⟩ := hSB
    rw [Finset.mem_filter] at ha hb
    have : a = b := Subtype.ext hba.symm
    rw [this] at ha
    omega
  · -- card A
    rw [Finset.card_image_of_injective _ Subtype.val_injective, htransA, fin_residue0_card]
  · -- card B
    rw [Finset.card_image_of_injective _ Subtype.val_injective, htransB, fin_residue1_card]
  · -- intersecting A
    intro S hS T hT hST
    rw [Finset.mem_image] at hS hT
    obtain ⟨a, ha, rfl⟩ := hS
    obtain ⟨b, hb, rfl⟩ := hT
    rw [Finset.mem_filter] at ha hb
    have hnadj : ¬ (disjGraph F).Adj a b := by rw [hadj a b]; push_neg; omega
    have hint : a.1 ∩ b.1 ≠ ∅ := fun hemp => hnadj ⟨hemp, hST⟩
    exact Finset.nonempty_iff_ne_empty.mpr hint
  · -- intersecting B
    intro S hS T hT hST
    rw [Finset.mem_image] at hS hT
    obtain ⟨a, ha, rfl⟩ := hS
    obtain ⟨b, hb, rfl⟩ := hT
    rw [Finset.mem_filter] at ha hb
    have hnadj : ¬ (disjGraph F).Adj a b := by rw [hadj a b]; push_neg; omega
    have hint : a.1 ∩ b.1 ≠ ∅ := fun hemp => hnadj ⟨hemp, hST⟩
    exact Finset.nonempty_iff_ne_empty.mpr hint
  · -- cross disjoint
    intro S hS T hT
    rw [Finset.mem_image] at hS hT
    obtain ⟨a, ha, rfl⟩ := hS
    obtain ⟨b, hb, rfl⟩ := hT
    rw [Finset.mem_filter] at ha hb
    have hadj_ab : (disjGraph F).Adj a b := by rw [hadj a b]; omega
    exact hadj_ab.1

/-- **B4 CLOSED — full M-side extremal classification of M3(l,1).** An extremal
    family `F` (`|F| = 2l+2`) is exactly two disjoint copies of the complete-graph
    vertex-star family: it splits into `A, B` with `A∪B=F`, `Disjoint A B`,
    `|A|=|B|=l+1`, each carrying a complete-graph star incidence, on disjoint
    supports. Combines `disjGraph_extremal_bipartition` (the Turán-forced balanced
    bipartition) with `M3_extremal_two_disjoint_stars_of_split` (the star
    structure of each part). -/
theorem M3_extremal_classification {F : Finset (Finset α)} {l : ℕ}
    (hF : M3Admissible F l 1) (hcard : F.card = 2 * l + 2) :
    ∃ A B : Finset (Finset α),
      A ∪ B = F ∧ Disjoint A B ∧ A.card = l + 1 ∧ B.card = l + 1 ∧
      IsCompleteGraphStarIncidence A ∧ IsCompleteGraphStarIncidence B ∧
      Disjoint (A.biUnion id) (B.biUnion id) := by
  obtain ⟨A, B, hunion, hdisj, hcardA, hcardB, hintA, hintB, hcross⟩ :=
    disjGraph_extremal_bipartition hF hcard
  have hAsub : A ⊆ F := hunion ▸ Finset.subset_union_left
  have hBsub : B ⊆ F := hunion ▸ Finset.subset_union_right
  obtain ⟨hstarA, hstarB, hsupp⟩ :=
    M3_extremal_two_disjoint_stars_of_split hF hAsub hBsub hcardA hcardB hintA hintB hcross
  exact ⟨A, B, hunion, hdisj, hcardA, hcardB, hstarA, hstarB, hsupp⟩

end M3
