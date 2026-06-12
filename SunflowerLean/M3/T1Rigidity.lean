/-
  M3 t=1 rigidity.

  This file records the equality-case structure behind Theorem 1.1.  For
  an extremal intersecting cap-1 family, every support point has degree
  exactly two, and every pair of members has a unique common point.  Thus
  the incidence structure is the edge/vertex-star incidence of a complete
  graph on the members.
-/

import SunflowerLean.M3.T1Exact

namespace M3

variable {α : Type*} [DecidableEq α]

/-- The incidence form of the `K_m` vertex-star family: every support point
    lies in exactly two members, and every pair of distinct members has a
    unique common point. -/
def IsCompleteGraphStarIncidence (F : Finset (Finset α)) : Prop :=
  (∀ x ∈ F.biUnion id, (F.filter (fun S => x ∈ S)).card = 2) ∧
  (∀ A, A ∈ F → ∀ B, B ∈ F → A ≠ B → ∃! x, x ∈ A ∧ x ∈ B)

/-- If a point of `A` is private to `A`, then the members meeting `A` inject
    into `A \ {x}`. -/
lemma meets_part_card_le_erase_of_private {F : Finset (Finset α)}
    (hc : PairwiseCapped F 1) (hsf : IsSunflowerFree F 3)
    {A : Finset α} (hA : A ∈ F) {x : α} (hxA : x ∈ A)
    (hprivate : ∀ B ∈ F, B ≠ A → x ∉ B) :
    (F.filter (fun B => B ≠ A ∧ (A ∩ B).Nonempty)).card ≤ A.card - 1 := by
  classical
  rcases (F.filter (fun B => B ≠ A ∧ (A ∩ B).Nonempty)).eq_empty_or_nonempty
    with he | ⟨B0, hB0⟩
  · rw [he]
    exact Nat.zero_le _
  obtain ⟨x0, _⟩ := (Finset.mem_filter.mp hB0).2.2
  set f : Finset α → α :=
    fun B => if h : (A ∩ B).Nonempty then h.choose else x0 with hf
  have hfmem : ∀ B ∈ F.filter (fun B => B ≠ A ∧ (A ∩ B).Nonempty),
      f B ∈ A ∩ B := by
    intro B hB
    have hne := (Finset.mem_filter.mp hB).2.2
    simp only [hf, dif_pos hne]
    exact hne.choose_spec
  have htarget : ∀ B ∈ F.filter (fun B => B ≠ A ∧ (A ∩ B).Nonempty),
      f B ∈ A.erase x := by
    intro B hB
    obtain ⟨hBF, hBA, _⟩ := Finset.mem_filter.mp hB
    have hfb := hfmem B hB
    exact Finset.mem_erase.mpr ⟨fun hfx => hprivate B hBF hBA (by
      rw [← hfx]
      exact (Finset.mem_inter.mp hfb).2), (Finset.mem_inter.mp hfb).1⟩
  have hinj : Set.InjOn f (F.filter (fun B => B ≠ A ∧ (A ∩ B).Nonempty)) := by
    intro B hB C hC hfeq
    rw [Finset.mem_coe] at hB hC
    by_contra hBC
    obtain ⟨hBF, hBA, _⟩ := Finset.mem_filter.mp hB
    obtain ⟨hCF, hCA, _⟩ := Finset.mem_filter.mp hC
    have hxB := hfmem B hB
    have hxC := hfmem C hC
    rw [hfeq] at hxB
    exact no_three_through_point hc hsf hA hBF hCF (Ne.symm hBA) (Ne.symm hCA)
      hBC (Finset.mem_inter.mp hxC).1 (Finset.mem_inter.mp hxB).2
      (Finset.mem_inter.mp hxC).2
  calc (F.filter (fun B => B ≠ A ∧ (A ∩ B).Nonempty)).card
      ≤ (A.erase x).card := Finset.card_le_card_of_injOn f htarget hinj
    _ = A.card - 1 := Finset.card_erase_of_mem hxA

/-- In an extremal intersecting cap-1 family, no point of a member is private
    to that member. -/
lemma I3_extremal_no_private_points {F : Finset (Finset α)} {l : ℕ}
    (hF : I3Admissible F l 1) (hcard : F.card = l + 1)
    {A : Finset α} (hA : A ∈ F) {x : α} (hxA : x ∈ A) :
    ∃ B ∈ F, B ≠ A ∧ x ∈ B := by
  classical
  obtain ⟨⟨hu, hc, hsf⟩, hint⟩ := hF
  by_contra hnone
  push_neg at hnone
  have hprivate : ∀ B ∈ F, B ≠ A → x ∉ B := by
    intro B hB hBA hxB
    exact hnone B hB hBA hxB
  set Mee := F.filter (fun B => B ≠ A ∧ (A ∩ B).Nonempty) with hMee
  have hMeeEq : Mee = F.erase A := by
    ext B
    simp only [hMee, Finset.mem_filter, Finset.mem_erase]
    constructor
    · intro h
      exact ⟨h.2.1, h.1⟩
    · intro h
      have hne : (A ∩ B).Nonempty := hint A hA B h.2 (Ne.symm h.1)
      exact ⟨h.2, h.1, hne⟩
  have hMeeCard : Mee.card = l := by
    rw [hMeeEq, Finset.card_erase_of_mem hA, hcard]
    omega
  have hle := meets_part_card_le_erase_of_private hc hsf hA hxA hprivate
  have hleMee : Mee.card ≤ l - 1 := by
    simpa [hMee, hu A hA] using hle
  have himp : l ≤ l - 1 := by
    simpa [hMeeCard] using hleMee
  have hlpos : 0 < l := by
    have : 0 < A.card := Finset.card_pos.mpr ⟨x, hxA⟩
    rwa [hu A hA] at this
  omega

/-- In an extremal intersecting cap-1 family, every support point has degree
    exactly two. -/
lemma I3_extremal_degree_eq_two {F : Finset (Finset α)} {l : ℕ}
    (hF : I3Admissible F l 1) (hcard : F.card = l + 1) {x : α}
    (hx : x ∈ F.biUnion id) :
    (F.filter (fun S => x ∈ S)).card = 2 := by
  classical
  have hF0 := hF
  obtain ⟨⟨_, hc, hsf⟩, _⟩ := hF
  obtain ⟨A, hA, hxA⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨B, hB, hBA, hxB⟩ := I3_extremal_no_private_points hF0 hcard hA hxA
  have hsub : ({A, B} : Finset (Finset α)) ⊆ F.filter (fun S => x ∈ S) := by
    intro S hS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hS
    rcases hS with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hA, hxA⟩
    · exact Finset.mem_filter.mpr ⟨hB, hxB⟩
  have hge : 2 ≤ (F.filter (fun S => x ∈ S)).card := by
    have hpair : ({A, B} : Finset (Finset α)).card = 2 := by
      have hAB : A ≠ B := Ne.symm hBA
      simp [hAB]
    rw [← hpair]
    exact Finset.card_le_card hsub
  have hle : (F.filter (fun S => x ∈ S)).card ≤ 2 :=
    degree_le_two hc hsf x
  exact le_antisymm hle hge

/-- Distinct members of an intersecting cap-1 family have a unique common
    point. -/
lemma I3_unique_common_point_t1 {F : Finset (Finset α)} {l : ℕ}
    (hF : I3Admissible F l 1) {A B : Finset α}
    (hA : A ∈ F) (hB : B ∈ F) (hAB : A ≠ B) :
    ∃! x, x ∈ A ∧ x ∈ B := by
  classical
  obtain ⟨⟨_, hc, _⟩, hint⟩ := hF
  obtain ⟨x, hx⟩ := hint A hA B hB hAB
  obtain ⟨hxA, hxB⟩ := Finset.mem_inter.mp hx
  have hsingle := inter_eq_singleton_of_capped hc hA hB hAB hxA hxB
  refine ⟨x, ⟨hxA, hxB⟩, ?_⟩
  intro y hy
  have hyi : y ∈ A ∩ B := Finset.mem_inter.mpr hy
  rw [hsingle, Finset.mem_singleton] at hyi
  exact hyi

/-- Equality-case rigidity for the intersecting t=1 theorem.  Together with
    `F.card = l+1` and uniformity, this is the complete-graph star incidence
    model, hence the `K_{l+1}` vertex-star family up to relabeling. -/
theorem I3_extremal_star_incidence {F : Finset (Finset α)} {l : ℕ}
    (hF : I3Admissible F l 1) (hcard : F.card = l + 1) :
    IsCompleteGraphStarIncidence F := by
  constructor
  · intro x hx
    exact I3_extremal_degree_eq_two hF hcard hx
  · intro A hA B hB hAB
    exact I3_unique_common_point_t1 hF hA hB hAB

end M3
