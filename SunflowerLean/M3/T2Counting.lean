/-
  M3 sharp t=2 counting bound.

  This module formalizes the paper's improved counting argument for
  M3(l,2): split ordered pairs into intersection sizes 0, 1, and 2;
  use Mantel/Turan for the disjoint layer and the singleton-intersection
  layers; use codegree <= 2 for the two-point layer.
-/

import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Group.Nat.Even
import SunflowerLean.M3.LinkRecursion

open scoped BigOperators

namespace M3

variable {α : Type*} [DecidableEq α]

/-- Ordered-edge Mantel wrapper.  If `R` is a symmetric loopless relation on
`F` with no triangle, then the number of ordered related pairs in `F` is at
most `|F|^2/2`, expressed without division. -/
lemma triangleFree_orderedRel_card_le_sq {β : Type*} [DecidableEq β]
    (F : Finset β) (R : β → β → Prop) [DecidableRel R]
    (hsym : ∀ ⦃a b⦄, a ∈ F → b ∈ F → R a b → R b a)
    (hloop : ∀ ⦃a⦄, a ∈ F → ¬ R a a)
    (htri : ∀ ⦃a b c⦄, a ∈ F → b ∈ F → c ∈ F → a ≠ b → a ≠ c → b ≠ c →
      R a b → R a c → R b c → False) :
    2 * ((F.offDiag.filter (fun p : β × β => R p.1 p.2)).card) ≤ F.card ^ 2 := by
  classical
  let V := {x // x ∈ F}
  let G : SimpleGraph V := SimpleGraph.mk
    (fun a b : V => R a.1 b.1)
    (by intro a b hab; exact hsym a.2 b.2 hab)
    (by intro a; exact hloop a.2)
  letI : DecidableRel G.Adj := fun a b => inferInstanceAs (Decidable (R a.1 b.1))
  have hcf : G.CliqueFree 3 := by
    intro t ht
    rw [SimpleGraph.isNClique_iff] at ht
    obtain ⟨hclique, hcard⟩ := ht
    obtain ⟨a, b, c, hab, hac, hbc, ht_eq⟩ := Finset.card_eq_three.mp hcard
    have ha : a ∈ (t : Set V) := by rw [ht_eq]; simp
    have hb : b ∈ (t : Set V) := by rw [ht_eq]; simp
    have hc : c ∈ (t : Set V) := by rw [ht_eq]; simp
    have rab : R a.1 b.1 := hclique ha hb hab
    have rac : R a.1 c.1 := hclique ha hc hac
    have rbc : R b.1 c.1 := hclique hb hc hbc
    exact htri a.2 b.2 c.2 (fun h => hab (Subtype.ext h))
      (fun h => hac (Subtype.ext h)) (fun h => hbc (Subtype.ext h)) rab rac rbc
  have hT := SimpleGraph.CliqueFree.card_edgeFinset_le (G := G) (r := 2) hcf
  have hEdge4 : 4 * G.edgeFinset.card ≤ F.card ^ 2 := by
    have hn : Fintype.card V = F.card := by
      rw [← Finset.card_univ, Finset.univ_eq_attach F, Finset.card_attach]
    rw [hn] at hT
    dsimp at hT
    norm_num at hT
    have hchoose : (F.card % 2).choose 2 = 0 := by
      have hmod : F.card % 2 < 2 := Nat.mod_lt _ (by decide)
      interval_cases F.card % 2 <;> simp
    rw [hchoose, add_zero] at hT
    have hmain : G.edgeFinset.card ≤ (F.card ^ 2 - (F.card % 2) ^ 2) / 4 := by
      simpa using hT
    have hmul := Nat.mul_le_mul_left 4 hmain
    have hdiv : 4 * ((F.card ^ 2 - (F.card % 2) ^ 2) / 4) ≤
        F.card ^ 2 - (F.card % 2) ^ 2 := Nat.mul_div_le _ _
    have hsub : F.card ^ 2 - (F.card % 2) ^ 2 ≤ F.card ^ 2 := Nat.sub_le _ _
    exact hmul.trans (hdiv.trans hsub)
  let s := F.offDiag.filter (fun p : β × β => R p.1 p.2)
  let t : Finset (V × V) := Finset.univ.filter (fun p => G.Adj p.1 p.2)
  let toSubPair : s → t := fun p => by
    have hp := Finset.mem_filter.mp p.2
    refine ⟨((⟨p.1.1, (Finset.mem_offDiag.mp hp.1).1⟩ : V),
      (⟨p.1.2, (Finset.mem_offDiag.mp hp.1).2.1⟩ : V)), ?_⟩
    simp only [t, G, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hp.2
  have hle_ordered : s.card ≤ t.card := by
    refine Finset.card_le_card_of_injective (s := s) (t := t) (f := toSubPair) ?_
    intro p q hpq
    apply Subtype.ext
    have hval := congrArg (fun z : t => (z.1.1.1, z.1.2.1)) hpq
    simpa [toSubPair] using hval
  have hgraph_ordered : t.card = 2 * G.edgeFinset.card := by
    change (Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2)).card =
      2 * G.edgeFinset.card
    simpa [G] using (SimpleGraph.two_mul_card_edgeFinset (G := G)).symm
  have hordered_le : 2 * s.card ≤ 4 * G.edgeFinset.card := by
    calc 2 * s.card
        ≤ 2 * t.card := Nat.mul_le_mul_left 2 hle_ordered
      _ = 2 * (2 * G.edgeFinset.card) := by rw [hgraph_ordered]
      _ = 4 * G.edgeFinset.card := by ring
  simpa [s] using hordered_le.trans hEdge4

lemma no_three_with_core {F : Finset (Finset α)} (hsf : IsSunflowerFree F 3)
    {A B C core : Finset α} (hA : A ∈ F) (hB : B ∈ F) (hC : C ∈ F)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (eAB : A ∩ B = core) (eAC : A ∩ C = core) (eBC : B ∩ C = core) : False := by
  refine hsf {A, B, C} ?_ ⟨?_, core, ?_⟩
  · intro W hW
    simp only [Finset.mem_insert, Finset.mem_singleton] at hW
    rcases hW with rfl | rfl | rfl <;> assumption
  · exact Finset.card_eq_three.mpr ⟨A, B, C, hAB, hAC, hBC, rfl⟩
  · intro S T hS hT hST
    simp only [Finset.mem_insert, Finset.mem_singleton] at hS hT
    rcases hS with rfl | rfl | rfl <;> rcases hT with rfl | rfl | rfl
    · exact absurd rfl hST
    · exact eAB
    · exact eAC
    · rw [Finset.inter_comm]; exact eAB
    · exact absurd rfl hST
    · exact eBC
    · rw [Finset.inter_comm]; exact eAC
    · rw [Finset.inter_comm]; exact eBC
    · exact absurd rfl hST

lemma ordered_disjoint_pairs_le_sq {F : Finset (Finset α)} {l : ℕ}
    (hl : 0 < l) (hu : IsUniform F l) (hsf : IsSunflowerFree F 3) :
    2 * ((F.offDiag.filter (fun p : Finset α × Finset α => p.1 ∩ p.2 = ∅)).card)
      ≤ F.card ^ 2 := by
  classical
  refine triangleFree_orderedRel_card_le_sq F (fun A B : Finset α => A ∩ B = ∅) ?_ ?_ ?_
  · intro A B _ _ h
    rw [Finset.inter_comm]
    exact h
  · intro A hA h
    have hnon : A.Nonempty := Finset.card_pos.mp (by rw [hu A hA]; exact hl)
    rw [Finset.inter_self] at h
    exact hnon.ne_empty h
  · intro A B C hA hB hC hAB hAC hBC eAB eAC eBC
    exact no_three_with_core hsf hA hB hC hAB hAC hBC eAB eAC eBC

lemma singleton_pair_filter_eq (F : Finset (Finset α)) (x : α) :
    ((F.filter (fun S => x ∈ S)).offDiag.filter
      (fun p : Finset α × Finset α => p.1 ∩ p.2 = {x})) =
    (F.offDiag.filter (fun p : Finset α × Finset α => p.1 ∩ p.2 = {x})) := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_offDiag]
  constructor
  · rintro ⟨⟨⟨hp1F, _⟩, ⟨hp2F, _⟩, hne⟩, hcore⟩
    exact ⟨⟨hp1F, hp2F, hne⟩, hcore⟩
  · rintro ⟨⟨hp1F, hp2F, hne⟩, hcore⟩
    have hx : x ∈ p.1 ∩ p.2 := by rw [hcore]; simp
    exact ⟨⟨⟨hp1F, (Finset.mem_inter.mp hx).1⟩,
      ⟨hp2F, (Finset.mem_inter.mp hx).2⟩, hne⟩, hcore⟩

lemma ordered_singleton_pairs_le_degree_sq {F : Finset (Finset α)} {l : ℕ}
    (hl : 2 ≤ l) (hu : IsUniform F l) (hsf : IsSunflowerFree F 3) (x : α) :
    2 * ((F.offDiag.filter (fun p : Finset α × Finset α => p.1 ∩ p.2 = {x})).card)
      ≤ (F.filter (fun S => x ∈ S)).card ^ 2 := by
  classical
  let Fx := F.filter (fun S => x ∈ S)
  have hbound := triangleFree_orderedRel_card_le_sq Fx
    (fun A B : Finset α => A ∩ B = {x})
    (by
      intro A B _ _ h
      rw [Finset.inter_comm]
      exact h)
    (by
      intro A hA h
      have hAF : A ∈ F := (Finset.mem_filter.mp hA).1
      have hcard : A.card = 1 := by
        rw [Finset.inter_self] at h
        rw [h, Finset.card_singleton]
      rw [hu A hAF] at hcard
      omega)
    (by
      intro A B C hA hB hC hAB hAC hBC eAB eAC eBC
      exact no_three_with_core hsf (Finset.mem_filter.mp hA).1 (Finset.mem_filter.mp hB).1
        (Finset.mem_filter.mp hC).1 hAB hAC hBC eAB eAC eBC)
  simpa [Fx, singleton_pair_filter_eq F x] using hbound

lemma degree_sum_eq_card_mul {F : Finset (Finset α)} {l : ℕ} (hu : IsUniform F l) :
    ∑ x ∈ F.biUnion id, (F.filter (fun S => x ∈ S)).card = F.card * l := by
  classical
  have hsubU : ∀ S ∈ F, S ⊆ F.biUnion id := fun S hS x hx =>
    Finset.mem_biUnion.mpr ⟨S, hS, hx⟩
  calc ∑ x ∈ F.biUnion id, (F.filter (fun S => x ∈ S)).card
      = ∑ S ∈ F, S.card := by
        simp only [Finset.card_filter]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun S hS => ?_
        rw [← Finset.card_filter, Finset.filter_mem_eq_inter,
          Finset.inter_eq_right.mpr (hsubU S hS)]
    _ = ∑ _S ∈ F, l := Finset.sum_congr rfl (fun S hS => hu S hS)
    _ = F.card * l := by rw [Finset.sum_const, smul_eq_mul]

lemma ordered_one_point_pairs_le {F : Finset (Finset α)} {l : ℕ}
    (hl : 2 ≤ l) (hF : M3Admissible F l 2) :
    2 * ((F.offDiag.filter (fun p : Finset α × Finset α => (p.1 ∩ p.2).card = 1)).card)
      ≤ 2 * F.card * l ^ 2 := by
  classical
  have hF0 := hF
  obtain ⟨hu, _hc, hsf⟩ := hF
  let P1 := F.offDiag.filter (fun p : Finset α × Finset α => (p.1 ∩ p.2).card = 1)
  let Q : α → Finset (Finset α × Finset α) :=
    fun x => F.offDiag.filter (fun p : Finset α × Finset α => p.1 ∩ p.2 = {x})
  have hcover : P1 ⊆ (F.biUnion id).biUnion Q := by
    intro p hp
    obtain ⟨hpoff, hpone⟩ := Finset.mem_filter.mp hp
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hpone
    have hxmem : x ∈ F.biUnion id := by
      have hxin : x ∈ p.1 ∩ p.2 := by rw [hx]; simp
      exact Finset.mem_biUnion.mpr
        ⟨p.1, (Finset.mem_offDiag.mp hpoff).1, (Finset.mem_inter.mp hxin).1⟩
    exact Finset.mem_biUnion.mpr ⟨x, hxmem, Finset.mem_filter.mpr ⟨hpoff, hx⟩⟩
  have hP1sum : P1.card ≤ ∑ x ∈ F.biUnion id, (Q x).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hsumBound : 2 * (∑ x ∈ F.biUnion id, (Q x).card) ≤ 2 * F.card * l ^ 2 := by
    rw [Finset.mul_sum]
    calc ∑ x ∈ F.biUnion id, 2 * (Q x).card
        ≤ ∑ x ∈ F.biUnion id, (F.filter (fun S => x ∈ S)).card ^ 2 := by
          refine Finset.sum_le_sum ?_
          intro x hx
          exact ordered_singleton_pairs_le_degree_sq hl hu hsf x
      _ ≤ ∑ x ∈ F.biUnion id, (2 * l) * (F.filter (fun S => x ∈ S)).card := by
          refine Finset.sum_le_sum ?_
          intro x hx
          have hdeg : (F.filter (fun S => x ∈ S)).card ≤ 2 * l := by
            have hb := card_through_le hF0 (fun G hG => by simpa using (M3_card_le_t1 hG)) x
            have hcalc : 2 * (l - 1) + 2 ≤ 2 * l := by omega
            exact hb.trans hcalc
          have := Nat.mul_le_mul_right (F.filter (fun S => x ∈ S)).card hdeg
          simpa [pow_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
      _ = (2 * l) * (F.card * l) := by
          rw [← Finset.mul_sum, degree_sum_eq_card_mul hu]
      _ = 2 * F.card * l ^ 2 := by ring
  exact (Nat.mul_le_mul_left 2 hP1sum).trans hsumBound

lemma ordered_two_point_pairs_le {F : Finset (Finset α)} {l : ℕ}
    (hF : M3Admissible F l 2) :
    (F.offDiag.filter (fun p : Finset α × Finset α => (p.1 ∩ p.2).card = 2)).card
      ≤ F.card * l.choose 2 := by
  classical
  have hF0 := hF
  obtain ⟨hu, hc, hsf⟩ := hF
  let P2 := F.offDiag.filter (fun p : Finset α × Finset α => (p.1 ∩ p.2).card = 2)
  let PA : Finset α → Finset (Finset α × Finset α) := fun A => P2.filter (fun p => p.1 = A)
  have hcover : P2 ⊆ F.biUnion PA := by
    intro p hp
    have hA : p.1 ∈ F := (Finset.mem_offDiag.mp (Finset.mem_filter.mp hp).1).1
    exact Finset.mem_biUnion.mpr ⟨p.1, hA, Finset.mem_filter.mpr ⟨hp, rfl⟩⟩
  have hP2sum : P2.card ≤ ∑ A ∈ F, (PA A).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hfiber : ∀ A ∈ F, (PA A).card ≤ l.choose 2 := by
    intro A hA
    let target := A.powersetCard 2
    have hle : (PA A).card ≤ target.card := by
      refine Finset.card_le_card_of_injective (s := PA A) (t := target)
        (f := fun p : PA A => ?_) ?_
      · have hp := Finset.mem_filter.mp p.2
        have hp2 := Finset.mem_filter.mp hp.1
        refine ⟨p.1.1 ∩ p.1.2, ?_⟩
        exact Finset.mem_powersetCard.mpr ⟨(by rw [hp.2]; exact Finset.inter_subset_left), hp2.2⟩
      · intro p q hpq
        apply Subtype.ext
        have hp := Finset.mem_filter.mp p.2
        have hq := Finset.mem_filter.mp q.2
        have hp2 := Finset.mem_filter.mp hp.1
        have hq2 := Finset.mem_filter.mp hq.1
        have hpOff := Finset.mem_offDiag.mp hp2.1
        have hqOff := Finset.mem_offDiag.mp hq2.1
        have hpA : p.1.1 = A := hp.2
        have hqA : q.1.1 = A := hq.2
        have hinter : p.1.1 ∩ p.1.2 = q.1.1 ∩ q.1.2 := by
          exact congrArg Subtype.val hpq
        apply Prod.ext
        · exact hpA.trans hqA.symm
        · by_contra hBC
          have hB : p.1.2 ∈ F := hpOff.2.1
          have hC : q.1.2 ∈ F := hqOff.2.1
          have hAB : A ≠ p.1.2 := by
            intro h
            exact hpOff.2.2 (hpA.trans h)
          have hAC : A ≠ q.1.2 := by
            intro h
            exact hqOff.2.2 (hqA.trans h)
          have eAB : A ∩ p.1.2 = p.1.1 ∩ p.1.2 :=
            congrArg (fun X => X ∩ p.1.2) hpA.symm
          have eAC0 : A ∩ q.1.2 = q.1.1 ∩ q.1.2 :=
            congrArg (fun X => X ∩ q.1.2) hqA.symm
          have eAC : A ∩ q.1.2 = p.1.1 ∩ p.1.2 := eAC0.trans hinter.symm
          have eBC : p.1.2 ∩ q.1.2 = p.1.1 ∩ p.1.2 := by
            have hsub : p.1.1 ∩ p.1.2 ⊆ p.1.2 ∩ q.1.2 := by
              intro x hx
              have hxA : x ∈ A := by rw [← hpA]; exact (Finset.mem_inter.mp hx).1
              have hxB : x ∈ p.1.2 := (Finset.mem_inter.mp hx).2
              have hxC : x ∈ q.1.2 := by
                have : x ∈ q.1.1 ∩ q.1.2 := by rwa [← hinter]
                exact (Finset.mem_inter.mp this).2
              exact Finset.mem_inter.mpr ⟨hxB, hxC⟩
            have hcardle := hc p.1.2 hB q.1.2 hC hBC
            have hcardeq : (p.1.1 ∩ p.1.2).card = 2 := hp2.2
            exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcardeq]; exact hcardle)).symm
          exact no_three_with_core hsf hA hB hC hAB hAC hBC eAB eAC eBC
    rw [Finset.card_powersetCard, hu A hA] at hle
    exact hle
  calc P2.card
      ≤ ∑ A ∈ F, (PA A).card := hP2sum
    _ ≤ ∑ _A ∈ F, l.choose 2 := Finset.sum_le_sum hfiber
    _ = F.card * l.choose 2 := by rw [Finset.sum_const, smul_eq_mul]

/-- Paper Theorem 1.2, sharp counting upper bound: `M3(l,2) ≤ 3l²-l+2`. -/
theorem M3_card_le_t2_sharp {F : Finset (Finset α)} {l : ℕ}
    (hl : 3 ≤ l) (hF : M3Admissible F l 2) :
    F.card ≤ 3 * l ^ 2 - l + 2 := by
  classical
  have hF0 := hF
  obtain ⟨hu, hc, hsf⟩ := hF
  let D := F.offDiag.filter (fun p : Finset α × Finset α => p.1 ∩ p.2 = ∅)
  let P1 := F.offDiag.filter (fun p : Finset α × Finset α => (p.1 ∩ p.2).card = 1)
  let P2 := F.offDiag.filter (fun p : Finset α × Finset α => (p.1 ∩ p.2).card = 2)
  have hcover : F.offDiag ⊆ D ∪ P1 ∪ P2 := by
    intro p hp
    have hpinfo := Finset.mem_offDiag.mp hp
    have hcap := hc p.1 hpinfo.1 p.2 hpinfo.2.1 hpinfo.2.2
    have hk : (p.1 ∩ p.2).card = 0 ∨ (p.1 ∩ p.2).card = 1 ∨
        (p.1 ∩ p.2).card = 2 := by omega
    simp only [D, P1, P2, Finset.mem_union, Finset.mem_filter]
    rcases hk with h0 | h1 | h2
    · exact Or.inl (Or.inl ⟨hp, Finset.card_eq_zero.mp h0⟩)
    · exact Or.inl (Or.inr ⟨hp, h1⟩)
    · exact Or.inr ⟨hp, h2⟩
  have hpairCover : F.offDiag.card ≤ D.card + P1.card + P2.card := by
    calc F.offDiag.card
        ≤ (D ∪ P1 ∪ P2).card := Finset.card_le_card hcover
      _ ≤ (D ∪ P1).card + P2.card := Finset.card_union_le _ _
      _ ≤ D.card + P1.card + P2.card := by
          have h := Finset.card_union_le D P1
          omega
  have hD : 2 * D.card ≤ F.card ^ 2 := by
    simpa [D] using ordered_disjoint_pairs_le_sq (show 0 < l by omega) hu hsf
  have hP1 : 2 * P1.card ≤ 2 * F.card * l ^ 2 := by
    simpa [P1] using ordered_one_point_pairs_le (show 2 ≤ l by omega) hF0
  have hP2 : 2 * P2.card ≤ F.card * (l * (l - 1)) := by
    have h := ordered_two_point_pairs_le hF0
    have hmul := Nat.mul_le_mul_left 2 h
    have hchoose : 2 * (F.card * l.choose 2) = F.card * (l * (l - 1)) := by
      have hchoose' : 2 * l.choose 2 = l * (l - 1) := by
        rw [Nat.choose_two_right]
        exact Nat.mul_div_cancel' (even_iff_two_dvd.mp (Nat.even_mul_pred_self l))
      calc 2 * (F.card * l.choose 2)
          = F.card * (2 * l.choose 2) := by ring
        _ = F.card * (l * (l - 1)) := by rw [hchoose']
    exact hmul.trans (le_of_eq hchoose)
  rcases F.eq_empty_or_nonempty with hEmpty | hNonempty
  · rw [hEmpty]; simp
  set m := F.card with hmdef
  have hmpos : 0 < m := by
    rw [hmdef]
    exact Finset.card_pos.mpr hNonempty
  have hoff : F.offDiag.card = m * (m - 1) := by
    rw [Finset.offDiag_card, hmdef]
    rw [Nat.mul_sub_left_distrib]
    simp
  have htotal2 : 2 * F.offDiag.card ≤
      F.card ^ 2 + 2 * F.card * l ^ 2 + F.card * (l * (l - 1)) := by
    calc 2 * F.offDiag.card
        ≤ 2 * (D.card + P1.card + P2.card) := Nat.mul_le_mul_left 2 hpairCover
      _ = 2 * D.card + 2 * P1.card + 2 * P2.card := by ring
      _ ≤ F.card ^ 2 + 2 * F.card * l ^ 2 + F.card * (l * (l - 1)) := by
          simpa [Nat.add_assoc] using Nat.add_le_add (Nat.add_le_add hD hP1) hP2
  have hcancelShape : m * (m - 2) ≤ m * (3 * l ^ 2 - l) := by
    rw [hoff] at htotal2
    rw [← hmdef] at htotal2
    by_cases hm2 : m ≤ 2
    · rw [Nat.sub_eq_zero_of_le hm2]
      exact Nat.zero_le _
    · have h2m : 2 ≤ m := by omega
      have h1m : 1 ≤ m := by omega
      have h1l : 1 ≤ l := by omega
      have hl_rhs : l ≤ 3 * l ^ 2 := by nlinarith [sq_nonneg (l : ℤ)]
      zify [h1m, h2m, h1l, hl_rhs] at htotal2 ⊢
      nlinarith
  have hcancel : m - 2 ≤ 3 * l ^ 2 - l := Nat.le_of_mul_le_mul_left hcancelShape hmpos
  have hfinal : m ≤ 3 * l ^ 2 - l + 2 := by omega
  simpa [hmdef] using hfinal

/-- B3.1 incidence identity (goal-stack, ordered form): the double-count
    `∑_{(A,B)∈offDiag} |A∩B| = ∑_x deg(x)·(deg(x)−1)`. Equivalent to the
    unordered `P₁ + 2P₂ = Σ_x C(d_x,2)` — the algebraic handle behind the t=2
    constant analysis. (`(F.filter (x∈·)).offDiag.card = deg(x)·(deg(x)−1)`.) -/
theorem inter_card_sum_eq_deg_offDiag {F : Finset (Finset α)} :
    ∑ p ∈ F.offDiag, (p.1 ∩ p.2).card
      = ∑ x ∈ F.biUnion id, (F.filter (fun S => x ∈ S)).offDiag.card := by
  classical
  have hstep : ∀ p ∈ F.offDiag,
      (p.1 ∩ p.2).card
        = ∑ x ∈ F.biUnion id, (if x ∈ p.1 ∧ x ∈ p.2 then 1 else 0) := by
    intro p hp
    have hp1 : p.1 ∈ F := (Finset.mem_offDiag.mp hp).1
    have hsub : p.1 ∩ p.2 ⊆ F.biUnion id := fun y hy =>
      Finset.mem_biUnion.mpr ⟨p.1, hp1, (Finset.mem_inter.mp hy).1⟩
    calc (p.1 ∩ p.2).card
        = ((F.biUnion id).filter (fun x => x ∈ p.1 ∩ p.2)).card := by
          rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsub]
      _ = ∑ x ∈ F.biUnion id, (if x ∈ p.1 ∩ p.2 then 1 else 0) := by
          rw [Finset.card_filter]
      _ = ∑ x ∈ F.biUnion id, (if x ∈ p.1 ∧ x ∈ p.2 then 1 else 0) := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          simp [Finset.mem_inter]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [← Finset.card_filter]
  congr 1
  ext p
  simp only [Finset.mem_offDiag, Finset.mem_filter]
  constructor
  · rintro ⟨⟨h1, h2, hne⟩, hx1, hx2⟩; exact ⟨⟨h1, hx1⟩, ⟨h2, hx2⟩, hne⟩
  · rintro ⟨⟨h1, hx1⟩, ⟨h2, hx2⟩, hne⟩; exact ⟨⟨h1, h2, hne⟩, hx1, hx2⟩

/-- Prop 5 (goal-stack B3, conditional constant-1 bound): a t=2-admissible
    family with **no** pair meeting in exactly one point (every pair disjoint or
    meeting in exactly 2 — the doubled-pencil construction's own profile) obeys
    the far tighter `l²−l+2`. So the whole gap between the general `3l²−l+2` and
    this is exactly the *permission for singleton intersections*. -/
theorem M3_card_le_t2_no_singletons {F : Finset (Finset α)} {l : ℕ}
    (hl : 1 ≤ l) (hF : M3Admissible F l 2)
    (hno1 : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → (S ∩ T).card ≠ 1) :
    F.card ≤ l ^ 2 - l + 2 := by
  classical
  have hF0 := hF
  obtain ⟨hu, hc, hsf⟩ := hF
  let D := F.offDiag.filter (fun p : Finset α × Finset α => p.1 ∩ p.2 = ∅)
  let P2 := F.offDiag.filter (fun p : Finset α × Finset α => (p.1 ∩ p.2).card = 2)
  have hcover : F.offDiag ⊆ D ∪ P2 := by
    intro p hp
    have hpinfo := Finset.mem_offDiag.mp hp
    have hcap := hc p.1 hpinfo.1 p.2 hpinfo.2.1 hpinfo.2.2
    have hne1 := hno1 p.1 hpinfo.1 p.2 hpinfo.2.1 hpinfo.2.2
    have hk : (p.1 ∩ p.2).card = 0 ∨ (p.1 ∩ p.2).card = 2 := by omega
    simp only [D, P2, Finset.mem_union, Finset.mem_filter]
    rcases hk with h0 | h2
    · exact Or.inl ⟨hp, Finset.card_eq_zero.mp h0⟩
    · exact Or.inr ⟨hp, h2⟩
  have hpairCover : F.offDiag.card ≤ D.card + P2.card :=
    (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  have hD : 2 * D.card ≤ F.card ^ 2 := by
    simpa [D] using ordered_disjoint_pairs_le_sq (show 0 < l by omega) hu hsf
  have hP2 : 2 * P2.card ≤ F.card * (l * (l - 1)) := by
    have hmul := Nat.mul_le_mul_left 2 (ordered_two_point_pairs_le hF0)
    have hchoose' : 2 * l.choose 2 = l * (l - 1) := by
      rw [Nat.choose_two_right]
      exact Nat.mul_div_cancel' (even_iff_two_dvd.mp (Nat.even_mul_pred_self l))
    calc 2 * P2.card ≤ 2 * (F.card * l.choose 2) := by simpa [P2] using hmul
      _ = F.card * (2 * l.choose 2) := by ring
      _ = F.card * (l * (l - 1)) := by rw [hchoose']
  rcases F.eq_empty_or_nonempty with hEmpty | hNonempty
  · rw [hEmpty]; simp
  set m := F.card with hmdef
  have hmpos : 0 < m := Finset.card_pos.mpr hNonempty
  have hoff : F.offDiag.card = m * (m - 1) := by
    rw [Finset.offDiag_card, hmdef, Nat.mul_sub_left_distrib]; simp
  have htotal2 : 2 * F.offDiag.card ≤ F.card ^ 2 + F.card * (l * (l - 1)) := by
    calc 2 * F.offDiag.card
        ≤ 2 * (D.card + P2.card) := Nat.mul_le_mul_left 2 hpairCover
      _ = 2 * D.card + 2 * P2.card := by ring
      _ ≤ F.card ^ 2 + F.card * (l * (l - 1)) := Nat.add_le_add hD hP2
  have hcancelShape : m * (m - 2) ≤ m * (l * (l - 1)) := by
    rw [hoff, ← hmdef] at htotal2
    by_cases hm2 : m ≤ 2
    · rw [Nat.sub_eq_zero_of_le hm2]; exact Nat.zero_le _
    · have h2m : 2 ≤ m := by omega
      have h1m : 1 ≤ m := by omega
      zify [h1m, h2m, hl] at htotal2 ⊢
      nlinarith
  have hcancel : m - 2 ≤ l * (l - 1) := Nat.le_of_mul_le_mul_left hcancelShape hmpos
  have hll : l * (l - 1) = l ^ 2 - l := by
    cases l with
    | zero => simp
    | succ k => simp only [pow_two, Nat.succ_sub_one, Nat.mul_succ]; omega
  have hfinal : m ≤ l ^ 2 - l + 2 := by rw [← hll]; omega
  simpa [hmdef] using hfinal

/-- A4.1 localization (goal-stack Lane A): a `t=3`-admissible family with **no**
    pair meeting in exactly 3 points is `t=2`-admissible, hence obeys the sharp
    t=2 bound `3l²−l+2 = O(l²)`. Consequently `θ(3) > 2` can only arise via
    exact-3 intersections — and the best known `t=3` construction (the doubled
    pencil) has none. -/
theorem M3_t3_no_exact3_card_le_t2_sharp {F : Finset (Finset α)} {l : ℕ}
    (hl : 3 ≤ l) (hF : M3Admissible F l 3)
    (hno3 : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → (S ∩ T).card ≠ 3) :
    F.card ≤ 3 * l ^ 2 - l + 2 := by
  obtain ⟨hu, hc, hsf⟩ := hF
  have hc2 : PairwiseCapped F 2 := by
    intro S hS T hT hST
    have h3 := hc S hS T hT hST
    have hne := hno3 S hS T hT hST
    omega
  exact M3_card_le_t2_sharp hl ⟨hu, hc2, hsf⟩

end M3
