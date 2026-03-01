/-
  Obstruction Definitions for the B2 (Recurrence) Track

  This file defines the first obstruction signature O₁ used in the paper roadmap:
  “pair-anchor / saturated co-degree pairs.”

  Current scope:
  - Definitions only + small structural lemmas (no heavy combinatorics yet).

  Authors: Cody Mitchell, Claude (Opus)
  Date: January 2026
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import SunflowerLean.LocalTuran
import SunflowerLean.Slice
import SunflowerLean.Recurrence

namespace SunflowerLean

open scoped BigOperators

/-- Maximum co-degree over ordered distinct pairs in `ground`.

This is used to define the set of max co-degree pairs (the “pair-anchor” signature).
We use ordered pairs `(i,j)` with `i ≠ j` because it is convenient in Lean; `coDegree` is symmetric
in practice since it is defined via `{i,j}`.
-/
def maxCoDegree {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) : ℕ :=
  (ground.offDiag).sup (fun p => coDegree family p.1 p.2)

/-- The set of ordered max co-degree pairs `(i,j)` in `ground.offDiag`. -/
def maxCoDegreePairs {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) : Finset (α × α) :=
  (ground.offDiag).filter (fun p => coDegree family p.1 p.2 = maxCoDegree family ground)

/-!
Near-max variant (Nat slack).

We will likely need a *fatter* reservoir than exact max pairs to make the O₁a witness-upgrade bite:
exact max pairs can be brittle under ties/thin maxima. The near-max selector keeps the same engine
(anchoring + reservoir + counting), but replaces `=` by “within slack `s`”.
-/

/-- The set of ordered near-max co-degree pairs `(i,j)` in `ground.offDiag`:
those whose co-degree is within Nat slack `s` of the maximum. -/
def nearMaxCoDegreePairs {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (s : ℕ) : Finset (α × α) :=
  (ground.offDiag).filter (fun p => maxCoDegree family ground - s ≤ coDegree family p.1 p.2)

lemma nearMaxCoDegreePairs_subset_offDiag {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (s : ℕ) :
    nearMaxCoDegreePairs family ground s ⊆ ground.offDiag := by
  intro p hp
  exact (Finset.mem_filter.mp hp).1

lemma coDegree_le_maxCoDegree_of_mem_offDiag {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) {p : α × α}
    (hp : p ∈ ground.offDiag) :
    coDegree family p.1 p.2 ≤ maxCoDegree family ground := by
  classical
  -- Each `coDegree` is bounded above by the supremum over `ground.offDiag`.
  have : coDegree family p.1 p.2 ≤
      (ground.offDiag).sup (fun q : α × α => coDegree family q.1 q.2) :=
    Finset.le_sup (s := ground.offDiag) (f := fun q : α × α => coDegree family q.1 q.2) hp
  simpa [maxCoDegree] using this

lemma maxCoDegree_le_coDegree_of_mem_maxCoDegreePairs {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {p : α × α}
    (hp : p ∈ maxCoDegreePairs family ground) :
    maxCoDegree family ground ≤ coDegree family p.1 p.2 := by
  classical
  have hpEq : coDegree family p.1 p.2 = maxCoDegree family ground :=
    (Finset.mem_filter.mp hp).2
  exact hpEq.symm ▸ le_rfl

lemma nearMaxCoDegreePairs_zero_eq_maxCoDegreePairs {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) :
    nearMaxCoDegreePairs family ground 0 = maxCoDegreePairs family ground := by
  classical
  ext p
  constructor
  · intro hp
    have hpOff : p ∈ ground.offDiag := (Finset.mem_filter.mp hp).1
    have hpGe : maxCoDegree family ground ≤ coDegree family p.1 p.2 := by
      simpa [nearMaxCoDegreePairs, Nat.sub_zero] using (Finset.mem_filter.mp hp).2
    have hpLe : coDegree family p.1 p.2 ≤ maxCoDegree family ground :=
      coDegree_le_maxCoDegree_of_mem_offDiag (family := family) (ground := ground) hpOff
    have hpEq : coDegree family p.1 p.2 = maxCoDegree family ground :=
      Nat.le_antisymm hpLe hpGe
    exact Finset.mem_filter.mpr ⟨hpOff, hpEq⟩
  · intro hp
    have hpOff : p ∈ ground.offDiag := (Finset.mem_filter.mp hp).1
    have hpEq : coDegree family p.1 p.2 = maxCoDegree family ground :=
      (Finset.mem_filter.mp hp).2
    have hpGe : maxCoDegree family ground ≤ coDegree family p.1 p.2 := by
      exact hpEq.symm ▸ le_rfl
    exact Finset.mem_filter.mpr ⟨hpOff, by
      simpa [nearMaxCoDegreePairs, Nat.sub_zero] using hpGe⟩

lemma nearMaxCoDegreePairs_mono {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) {s t : ℕ} (hst : s ≤ t) :
    nearMaxCoDegreePairs family ground s ⊆ nearMaxCoDegreePairs family ground t := by
  intro p hp
  have hpOff : p ∈ ground.offDiag := (Finset.mem_filter.mp hp).1
  have hpGe : maxCoDegree family ground - s ≤ coDegree family p.1 p.2 :=
    (Finset.mem_filter.mp hp).2
  have hth : maxCoDegree family ground - t ≤ maxCoDegree family ground - s :=
    Nat.sub_le_sub_left hst (maxCoDegree family ground)
  exact Finset.mem_filter.mpr ⟨hpOff, hth.trans hpGe⟩

lemma maxCoDegreePairs_subset_nearMaxCoDegreePairs {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (s : ℕ) :
    maxCoDegreePairs family ground ⊆ nearMaxCoDegreePairs family ground s := by
  have hmono :
      nearMaxCoDegreePairs family ground 0 ⊆ nearMaxCoDegreePairs family ground s :=
    nearMaxCoDegreePairs_mono (family := family) (ground := ground) (s := 0) (t := s)
      (Nat.zero_le s)
  simpa [nearMaxCoDegreePairs_zero_eq_maxCoDegreePairs] using hmono

lemma maxCoDegreePairs_subset_offDiag {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) :
    maxCoDegreePairs family ground ⊆ ground.offDiag := by
  intro p hp
  exact (Finset.mem_filter.mp hp).1

/-- The support of max co-degree pairs: the set of coordinates that appear in some max pair. -/
def supportMaxCoDegreePairs {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) : Finset α :=
  (maxCoDegreePairs family ground).biUnion (fun p => ({p.1, p.2} : Finset α))

lemma mem_supportMaxCoDegreePairs_iff {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {x : α} :
    x ∈ supportMaxCoDegreePairs family ground ↔
      ∃ p ∈ maxCoDegreePairs family ground, x = p.1 ∨ x = p.2 := by
  classical
  simp [supportMaxCoDegreePairs, Finset.mem_biUnion]

lemma supportMaxCoDegreePairs_subset_ground {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) :
    supportMaxCoDegreePairs family ground ⊆ ground := by
  classical
  intro x hx
  rcases (mem_supportMaxCoDegreePairs_iff (family := family) (ground := ground) (x := x)).1 hx with
    ⟨p, hp, hx⟩
  have hp' : p ∈ ground.offDiag := maxCoDegreePairs_subset_offDiag family ground hp
  have hmem := Finset.mem_offDiag.mp hp'
  rcases hx with rfl | rfl
  · exact hmem.1
  · exact hmem.2.1

/-- “Anchored” max co-degree pairs: there is a hub coordinate `h` that lies in every max pair. -/
def maxPairsAnchoredAt {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (h : α) : Prop :=
  h ∈ ground ∧ ∀ p ∈ maxCoDegreePairs family ground, p.1 = h ∨ p.2 = h

/-- Obstruction O₁a (anchored max-pairs): there exists a hub coordinate `h` in every max pair. -/
def ObstructionO1a {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) : Prop :=
  ∃ h, maxPairsAnchoredAt family ground h

/-- Near-max anchored pairs (Nat slack `s`): every near-max pair touches the hub `h`. -/
def nearMaxPairsAnchoredAt {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (s : ℕ) (h : α) : Prop :=
  h ∈ ground ∧ ∀ p ∈ nearMaxCoDegreePairs family ground s, p.1 = h ∨ p.2 = h

/-- Obstruction O₁a-near (v1): anchored *near-max* pairs for a fixed Nat slack `s`. -/
def ObstructionO1aNear {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (s : ℕ) : Prop :=
  ∃ h, nearMaxPairsAnchoredAt family ground s h

lemma nearMaxPairsAnchoredAt_zero_iff_maxPairsAnchoredAt {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (h : α) :
    nearMaxPairsAnchoredAt family ground 0 h ↔ maxPairsAnchoredAt family ground h := by
  classical
  simp [nearMaxPairsAnchoredAt, maxPairsAnchoredAt, nearMaxCoDegreePairs_zero_eq_maxCoDegreePairs]

lemma ObstructionO1aNear_zero_iff_ObstructionO1a {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) :
    ObstructionO1aNear family ground 0 ↔ ObstructionO1a family ground := by
  classical
  simp [ObstructionO1aNear, ObstructionO1a, nearMaxPairsAnchoredAt_zero_iff_maxPairsAnchoredAt]

/-- Obstruction O₁b (small support): the support of max co-degree pairs has size ≤ 4. -/
def ObstructionO1b {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) : Prop :=
  (supportMaxCoDegreePairs family ground).card ≤ 4

/-- Obstruction O₁ signature (v0): `O₁ = O₁a ∨ O₁b`. -/
def ObstructionO1 {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) : Prop :=
  ObstructionO1a family ground ∨ ObstructionO1b family ground

/-- Max-neighbors of `h`: coordinates that form a max co-degree pair with `h`. -/
def Nmax {α : Type*} [DecidableEq α]
    (family : Finset (Finset α))
    (ground : Finset α)
    (h : α) : Finset α :=
  ((maxCoDegreePairs family ground).filter (fun p => p.1 = h)).image Prod.snd ∪
    ((maxCoDegreePairs family ground).filter (fun p => p.2 = h)).image Prod.fst

/--
Near-max neighbors of `h` (Nat slack `s`):
coordinates that form a near-max co-degree pair with `h`.
-/
def Nnear {α : Type*} [DecidableEq α]
    (family : Finset (Finset α))
    (ground : Finset α)
    (s : ℕ)
    (h : α) : Finset α :=
  ((nearMaxCoDegreePairs family ground s).filter (fun p => p.1 = h)).image Prod.snd ∪
    ((nearMaxCoDegreePairs family ground s).filter (fun p => p.2 = h)).image Prod.fst

lemma Nnear_zero_eq_Nmax {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (h : α) :
    Nnear family ground 0 h = Nmax family ground h := by
  classical
  simp [Nnear, Nmax, nearMaxCoDegreePairs_zero_eq_maxCoDegreePairs]

theorem mem_Nnear_iff_mem_and_ge {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {s : ℕ} {h j : α} :
    j ∈ Nnear family ground s h ↔
      h ∈ ground ∧ j ∈ ground.erase h ∧ maxCoDegree family ground - s ≤ coDegree family h j := by
  classical
  constructor
  · intro hj
    rcases Finset.mem_union.mp hj with hj | hj
    · rcases Finset.mem_image.mp hj with ⟨p, hp, rfl⟩
      have hp' : p ∈ nearMaxCoDegreePairs family ground s := (Finset.mem_filter.mp hp).1
      have hp1 : p.1 = h := (Finset.mem_filter.mp hp).2
      have hpOff : p ∈ ground.offDiag :=
        nearMaxCoDegreePairs_subset_offDiag (family := family) (ground := ground) (s := s) hp'
      have hmem := Finset.mem_offDiag.mp hpOff
      have hne : p.2 ≠ h := by
        intro hEq
        exact hmem.2.2 (hp1 ▸ hEq.symm)
      have hhg : h ∈ ground := hp1 ▸ hmem.1
      have hjg : p.2 ∈ ground.erase h := Finset.mem_erase.mpr ⟨hne, hmem.2.1⟩
      have hge : maxCoDegree family ground - s ≤ coDegree family h p.2 := by
        have := (Finset.mem_filter.mp hp').2
        simpa [hp1] using this
      exact ⟨hhg, hjg, hge⟩
    · rcases Finset.mem_image.mp hj with ⟨p, hp, rfl⟩
      have hp' : p ∈ nearMaxCoDegreePairs family ground s := (Finset.mem_filter.mp hp).1
      have hp2 : p.2 = h := (Finset.mem_filter.mp hp).2
      have hpOff : p ∈ ground.offDiag :=
        nearMaxCoDegreePairs_subset_offDiag (family := family) (ground := ground) (s := s) hp'
      have hmem := Finset.mem_offDiag.mp hpOff
      have hne : p.1 ≠ h := by
        intro hEq
        exact hmem.2.2 (hEq.trans hp2.symm)
      have hhg : h ∈ ground := hp2 ▸ hmem.2.1
      have hjg : p.1 ∈ ground.erase h := Finset.mem_erase.mpr ⟨hne, hmem.1⟩
      have hge : maxCoDegree family ground - s ≤ coDegree family h p.1 := by
        have := (Finset.mem_filter.mp hp').2
        have : maxCoDegree family ground - s ≤ coDegree family p.1 h := by
          simpa [hp2] using this
        simpa [coDegree_comm] using this
      exact ⟨hhg, hjg, hge⟩
  · rintro ⟨hhg, hjg, hge⟩
    have hjg' := Finset.mem_erase.mp hjg
    have hpOff : (h, j) ∈ ground.offDiag :=
      (Finset.mem_offDiag).2 ⟨hhg, hjg'.2, hjg'.1.symm⟩
    have hpNear : (h, j) ∈ nearMaxCoDegreePairs family ground s :=
      Finset.mem_filter.mpr ⟨hpOff, by simpa using hge⟩
    refine Finset.mem_union.mpr (Or.inl ?_)
    refine Finset.mem_image.mpr ?_
    refine ⟨(h, j), ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨hpNear, rfl⟩

theorem mem_Nnear_imp {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {s : ℕ} {h j : α} :
    j ∈ Nnear family ground s h →
      h ∈ ground ∧ j ∈ ground.erase h ∧ maxCoDegree family ground - s ≤ coDegree family h j := by
  intro hj
  exact (mem_Nnear_iff_mem_and_ge (family := family) (ground := ground) (s := s) (h := h) (j := j)).1 hj

lemma Nmax_subset_Nnear {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (s : ℕ) (h : α) :
    Nmax family ground h ⊆ Nnear family ground s h := by
  classical
  intro j hj
  rcases Finset.mem_union.mp hj with hj | hj
  · rcases Finset.mem_image.mp hj with ⟨p, hp, rfl⟩
    have hp' : p ∈ maxCoDegreePairs family ground := (Finset.mem_filter.mp hp).1
    have hp1 : p.1 = h := (Finset.mem_filter.mp hp).2
    have hpNear : p ∈ nearMaxCoDegreePairs family ground s :=
      maxCoDegreePairs_subset_nearMaxCoDegreePairs
        (family := family) (ground := ground) (s := s) hp'
    refine Finset.mem_union.mpr (Or.inl ?_)
    refine Finset.mem_image.mpr ?_
    refine ⟨p, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨hpNear, hp1⟩
  · rcases Finset.mem_image.mp hj with ⟨p, hp, rfl⟩
    have hp' : p ∈ maxCoDegreePairs family ground := (Finset.mem_filter.mp hp).1
    have hp2 : p.2 = h := (Finset.mem_filter.mp hp).2
    have hpNear : p ∈ nearMaxCoDegreePairs family ground s :=
      maxCoDegreePairs_subset_nearMaxCoDegreePairs
        (family := family) (ground := ground) (s := s) hp'
    refine Finset.mem_union.mpr (Or.inr ?_)
    refine Finset.mem_image.mpr ?_
    refine ⟨p, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨hpNear, hp2⟩

lemma Nnear_mono {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) {s t : ℕ} (hst : s ≤ t) (h : α) :
    Nnear family ground s h ⊆ Nnear family ground t h := by
  classical
  intro j hj
  rcases Finset.mem_union.mp hj with hj | hj
  · rcases Finset.mem_image.mp hj with ⟨p, hp, rfl⟩
    have hp' : p ∈ nearMaxCoDegreePairs family ground s := (Finset.mem_filter.mp hp).1
    have hp1 : p.1 = h := (Finset.mem_filter.mp hp).2
    have hp'' : p ∈ nearMaxCoDegreePairs family ground t :=
      nearMaxCoDegreePairs_mono (family := family) (ground := ground) (s := s) (t := t) hst hp'
    refine Finset.mem_union.mpr (Or.inl ?_)
    refine Finset.mem_image.mpr ?_
    refine ⟨p, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨hp'', hp1⟩
  · rcases Finset.mem_image.mp hj with ⟨p, hp, rfl⟩
    have hp' : p ∈ nearMaxCoDegreePairs family ground s := (Finset.mem_filter.mp hp).1
    have hp2 : p.2 = h := (Finset.mem_filter.mp hp).2
    have hp'' : p ∈ nearMaxCoDegreePairs family ground t :=
      nearMaxCoDegreePairs_mono (family := family) (ground := ground) (s := s) (t := t) hst hp'
    refine Finset.mem_union.mpr (Or.inr ?_)
    refine Finset.mem_image.mpr ?_
    refine ⟨p, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨hp'', hp2⟩

/-- Membership in `Nmax(h)` certifies `(h,j)` has maximal co-degree. -/
theorem coDegree_eq_maxCoDegree_of_mem_Nmax {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {h j : α}
    (hj : j ∈ Nmax family ground h) :
    coDegree family h j = maxCoDegree family ground := by
  classical
  rcases Finset.mem_union.mp hj with hj | hj
  · rcases Finset.mem_image.mp hj with ⟨p, hp, rfl⟩
    have hp_in : p ∈ maxCoDegreePairs family ground := (Finset.mem_filter.mp hp).1
    have hp1 : p.1 = h := (Finset.mem_filter.mp hp).2
    have hp_max : coDegree family p.1 p.2 = maxCoDegree family ground :=
      (Finset.mem_filter.mp hp_in).2
    simpa [hp1] using hp_max
  · rcases Finset.mem_image.mp hj with ⟨p, hp, rfl⟩
    have hp_in : p ∈ maxCoDegreePairs family ground := (Finset.mem_filter.mp hp).1
    have hp2 : p.2 = h := (Finset.mem_filter.mp hp).2
    have hp_max : coDegree family p.1 p.2 = maxCoDegree family ground :=
      (Finset.mem_filter.mp hp_in).2
    have : coDegree family h p.1 = maxCoDegree family ground := by
      simpa [hp2, coDegree_comm] using hp_max
    simpa using this

/-- If `ground.offDiag` is nonempty, then there exists a max co-degree pair. -/
theorem maxCoDegreePairs_nonempty_of_offDiag_nonempty {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α)
    (h : ground.offDiag.Nonempty) :
    (maxCoDegreePairs family ground).Nonempty := by
  classical
  -- The supremum of a nonempty finset is attained.
  have hsup :
      maxCoDegree family ground ∈
        (fun p : α × α => coDegree family p.1 p.2) '' ground.offDiag := by
    simpa [maxCoDegree] using
      (Finset.sup_mem_of_nonempty (s := ground.offDiag)
        (f := fun p : α × α => coDegree family p.1 p.2) h)
  rcases hsup with ⟨p, hp, hpEq⟩
  refine ⟨p, ?_⟩
  refine Finset.mem_filter.mpr ?_
  refine ⟨hp, ?_⟩
  simpa [maxCoDegree] using hpEq

/-- Under the anchor condition, a nonempty max-pair set yields a nonempty `Nmax`. -/
theorem Nmax_nonempty_of_anchor_of_maxCoDegreePairs_nonempty {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {h : α}
    (hanch : maxPairsAnchoredAt family ground h)
    (hne : (maxCoDegreePairs family ground).Nonempty) :
    (Nmax family ground h).Nonempty := by
  classical
  rcases hne with ⟨p, hp⟩
  have hp_anchor : p.1 = h ∨ p.2 = h := hanch.2 p hp
  rcases hp_anchor with hp1 | hp2
  · refine ⟨p.2, ?_⟩
    refine Finset.mem_union.mpr (Or.inl ?_)
    refine Finset.mem_image.mpr ?_
    refine ⟨p, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨hp, hp1⟩
  · refine ⟨p.1, ?_⟩
    refine Finset.mem_union.mpr (Or.inr ?_)
    refine Finset.mem_image.mpr ?_
    refine ⟨p, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨hp, hp2⟩

/-- Remainder class template (first pass): h-free sets that meet `Nmax` in at most `r` points. -/
def RClass {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (h : α) (r : ℕ) (S : Finset α) : Prop :=
  S ⊆ ground ∧ h ∉ S ∧ (S ∩ Nmax family ground h).card ≤ r

/-- Lift a set `S` by forcing inclusion of a coordinate `h`. -/
def liftAt {α : Type*} [DecidableEq α] (S : Finset α) (h : α) : Finset α :=
  S ∪ ({h} : Finset α)

/--
`T` is blocked by a sunflower witness in `family` if there exist two distinct sets `A,B ∈ family`
such that `A∩B = A∩T = B∩T`.

This is the basic “maximality certificate” for why a missing set cannot be added.
-/
def BlockedByTwo {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (T : Finset α) : Prop :=
  ∃ A ∈ family, ∃ B ∈ family, A ≠ B ∧
    ∃ core : Finset α, A ∩ B = core ∧ A ∩ T = core ∧ B ∩ T = core

/--
Strengthened blocking predicate: `T` is blocked by two witness sets
drawn from a specified reservoir `W`.

This is the “pin the witness to a subfamily” upgrade needed for O₁a → Nmax-style constraints.
-/
def BlockedByTwoFrom {α : Type*} [DecidableEq α]
    (W : Finset (Finset α)) (T : Finset α) : Prop :=
  ∃ A ∈ W, ∃ B ∈ W, A ≠ B ∧
    ∃ core : Finset α, A ∩ B = core ∧ A ∩ T = core ∧ B ∩ T = core

theorem blockedByTwo_of_blockedByTwoFrom {α : Type*} [DecidableEq α]
    {family W : Finset (Finset α)} {T : Finset α}
    (hW : W ⊆ family) (h : BlockedByTwoFrom W T) :
    BlockedByTwo family T := by
  classical
  rcases h with ⟨A, hAW, B, hBW, hAB, core, hcore⟩
  refine ⟨A, hW hAW, B, hW hBW, hAB, core, hcore⟩

/-- If `h ∈ T` and `A ∩ T = core`, then `h ∈ A ↔ h ∈ core`. -/
lemma mem_left_iff_mem_core_of_mem_T_of_inter_eq {α : Type*} [DecidableEq α]
    {A T core : Finset α} {h : α} (hT : h ∈ T) (hAT : A ∩ T = core) :
    (h ∈ A ↔ h ∈ core) := by
  constructor
  · intro hA
    have : h ∈ A ∩ T := Finset.mem_inter.mpr ⟨hA, hT⟩
    simpa [hAT] using this
  · intro hcore
    have : h ∈ A ∩ T := by simpa [hAT] using hcore
    exact (Finset.mem_inter.mp this).1

/-- In a blocking witness, any coordinate in `T` is either in both witnesses or in neither. -/
theorem blockedByTwo_mem_witnesses_iff_mem_core {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {T : Finset α} {h : α}
    (hT : h ∈ T) (hblocked : BlockedByTwo family T) :
    ∃ A ∈ family, ∃ B ∈ family, A ≠ B ∧
      ∃ core : Finset α, A ∩ B = core ∧ A ∩ T = core ∧ B ∩ T = core ∧
        (h ∈ A ↔ h ∈ core) ∧ (h ∈ B ↔ h ∈ core) := by
  classical
  rcases hblocked with ⟨A, hA, B, hB, hAB, core, hcoreAB, hcoreAT, hcoreBT⟩
  refine ⟨A, hA, B, hB, hAB, core, hcoreAB, hcoreAT, hcoreBT, ?_, ?_⟩
  · exact mem_left_iff_mem_core_of_mem_T_of_inter_eq (A := A) (T := T) (core := core) hT hcoreAT
  · exact mem_left_iff_mem_core_of_mem_T_of_inter_eq (A := B) (T := T) (core := core) hT hcoreBT

/-- If `liftAt S h` is blocked by two witnesses avoiding `h`, then the witness must include `S`. -/
theorem blockedByTwo_liftAt_chain_case {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {S : Finset α} {h : α}
    (hS : S ∈ family) (hhnS : h ∉ S) (hfree : IsSunflowerFree family 3)
    (hblocked : BlockedByTwo family (liftAt S h)) :
    ∃ A ∈ family, ∃ B ∈ family, A ≠ B ∧
      ∃ core : Finset α, A ∩ B = core ∧ A ∩ liftAt S h = core ∧ B ∩ liftAt S h = core ∧
        (h ∉ core → A = S ∨ B = S) := by
  classical
  rcases hblocked with ⟨A, hA, B, hB, hAB, core, hcoreAB, hcoreAT, hcoreBT⟩
  refine ⟨A, hA, B, hB, hAB, core, hcoreAB, hcoreAT, hcoreBT, ?_⟩
  intro hcore
  -- If `h ∉ core`, then `h ∉ A` and `h ∉ B`.
  have hT : h ∈ liftAt S h := by
    simp [liftAt]
  have hAiff :
      (h ∈ A ↔ h ∈ core) :=
    mem_left_iff_mem_core_of_mem_T_of_inter_eq (A := A) (T := liftAt S h) (core := core) hT hcoreAT
  have hBiff :
      (h ∈ B ↔ h ∈ core) :=
    mem_left_iff_mem_core_of_mem_T_of_inter_eq (A := B) (T := liftAt S h) (core := core) hT hcoreBT
  have hhA : h ∉ A := by
    intro hhA
    have : h ∈ core := (hAiff.1 hhA)
    exact hcore this
  have hhB : h ∉ B := by
    intro hhB
    have : h ∈ core := (hBiff.1 hhB)
    exact hcore this
  -- With `h ∉ A,B`, the witness equalities reduce to intersections with `S`.
  have hAS : A ∩ S = core := by
    ext x
    constructor
    · intro hx
      have hxA : x ∈ A := (Finset.mem_inter.mp hx).1
      have hxS : x ∈ S := (Finset.mem_inter.mp hx).2
      have hxT' : x ∈ liftAt S h := by
        simp [liftAt, hxS]
      have hxAT : x ∈ A ∩ liftAt S h := Finset.mem_inter.mpr ⟨hxA, hxT'⟩
      simpa [hcoreAT] using hxAT
    · intro hxcore
      have hxAT : x ∈ A ∩ liftAt S h := by simpa [hcoreAT] using hxcore
      have hxA : x ∈ A := (Finset.mem_inter.mp hxAT).1
      have hxT' : x ∈ liftAt S h := (Finset.mem_inter.mp hxAT).2
      have hxU : x ∈ S ∨ x ∈ ({h} : Finset α) := by
        have : x ∈ S ∪ ({h} : Finset α) := by simpa [liftAt] using hxT'
        exact Finset.mem_union.mp this
      rcases hxU with hxS | hxH
      · exact Finset.mem_inter.mpr ⟨hxA, hxS⟩
      · have hxEq : x = h := by simpa using (Finset.mem_singleton.mp hxH)
        exact False.elim (hhA (hxEq ▸ hxA))
  have hBS : B ∩ S = core := by
    ext x
    constructor
    · intro hx
      have hxB : x ∈ B := (Finset.mem_inter.mp hx).1
      have hxS : x ∈ S := (Finset.mem_inter.mp hx).2
      have hxT' : x ∈ liftAt S h := by
        simp [liftAt, hxS]
      have hxBT : x ∈ B ∩ liftAt S h := Finset.mem_inter.mpr ⟨hxB, hxT'⟩
      simpa [hcoreBT] using hxBT
    · intro hxcore
      have hxBT : x ∈ B ∩ liftAt S h := by simpa [hcoreBT] using hxcore
      have hxB : x ∈ B := (Finset.mem_inter.mp hxBT).1
      have hxT' : x ∈ liftAt S h := (Finset.mem_inter.mp hxBT).2
      have hxU : x ∈ S ∨ x ∈ ({h} : Finset α) := by
        have : x ∈ S ∪ ({h} : Finset α) := by simpa [liftAt] using hxT'
        exact Finset.mem_union.mp this
      rcases hxU with hxS | hxH
      · exact Finset.mem_inter.mpr ⟨hxB, hxS⟩
      · have hxEq : x = h := by simpa using (Finset.mem_singleton.mp hxH)
        exact False.elim (hhB (hxEq ▸ hxB))
  -- If neither witness is `S`, we get a 3-sunflower `{A,B,S}` inside `family`, contradiction.
  by_cases hAS_eq : A = S
  · exact Or.inl hAS_eq
  by_cases hBS_eq : B = S
  · exact Or.inr hBS_eq
  have hsun : IsSunflower ({A, B, S} : Finset (Finset α)) 3 := by
    refine ⟨?_, ?_⟩
    · -- card = 3
      have hBnot : B ∉ ({S} : Finset (Finset α)) := by
        simp [hBS_eq]
      have hAnot : A ∉ insert B ({S} : Finset (Finset α)) := by
        simp [hAB, hAS_eq]
      have hcardB : (insert B ({S} : Finset (Finset α))).card = 2 := by
        simp [Finset.card_insert_of_notMem, hBnot]
      have hcard : (insert A (insert B ({S} : Finset (Finset α)))).card = 3 := by
        calc
          (insert A (insert B ({S} : Finset (Finset α)))).card =
              (insert B ({S} : Finset (Finset α))).card + 1 := by
                simp [Finset.card_insert_of_notMem, hAnot]
          _ = 3 := by
                simp [hcardB]
      simpa using hcard
    · refine ⟨core, ?_⟩
      intro X Y hX hY hXY
      have hX' : X = A ∨ X = B ∨ X = S := by
        simpa using (Finset.mem_insert.mp hX)
      have hY' : Y = A ∨ Y = B ∨ Y = S := by
        simpa using (Finset.mem_insert.mp hY)
      rcases hX' with rfl | hX'
      · rcases hY' with rfl | hY'
        · exact False.elim (hXY rfl)
        · rcases hY' with rfl | rfl
          · exact hcoreAB
          · simpa [Finset.inter_comm] using hAS
      · rcases hX' with rfl | rfl
        · rcases hY' with rfl | hY'
          · simpa [Finset.inter_comm] using hcoreAB
          · rcases hY' with rfl | rfl
            · exact False.elim (hXY rfl)
            · simpa [Finset.inter_comm] using hBS
        · rcases hY' with rfl | hY'
          · simpa [Finset.inter_comm] using hAS
          · rcases hY' with rfl | rfl
            · simpa [Finset.inter_comm] using hBS
            · exact False.elim (hXY rfl)
  have hsub : ({A, B, S} : Finset (Finset α)) ⊆ family := by
    intro X hX
    have hX' : X = A ∨ X = B ∨ X = S := by
      simpa using (Finset.mem_insert.mp hX)
    rcases hX' with rfl | hX'
    · exact hA
    rcases hX' with rfl | rfl
    · exact hB
    · exact hS
  exact False.elim (hfree ({A, B, S} : Finset (Finset α)) hsub hsun)

/-- In a blocking witness for `liftAt S h`, either the core contains `h` or the witness uses `S`. -/
theorem blockedByTwo_liftAt_core_mem_or_chain {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {S : Finset α} {h : α}
    (hS : S ∈ family) (hhnS : h ∉ S) (hfree : IsSunflowerFree family 3)
    (hblocked : BlockedByTwo family (liftAt S h)) :
    ∃ A ∈ family, ∃ B ∈ family, A ≠ B ∧
      ∃ core : Finset α, A ∩ B = core ∧ A ∩ liftAt S h = core ∧ B ∩ liftAt S h = core ∧
        (h ∈ core ∨ A = S ∨ B = S) := by
  classical
  rcases
    blockedByTwo_liftAt_chain_case (family := family) (S := S) (h := h) hS hhnS hfree hblocked with
    ⟨A, hA, B, hB, hAB, core, hcoreAB, hcoreAT, hcoreBT, hchain⟩
  refine ⟨A, hA, B, hB, hAB, core, hcoreAB, hcoreAT, hcoreBT, ?_⟩
  by_cases hhcore : h ∈ core
  · exact Or.inl hhcore
  · have : A = S ∨ B = S := hchain hhcore
    exact Or.inr this

/-- Chain-extension certificate in the `h=0` slice: a strict superset of `S` still avoids `h`. -/
def ChainExtension {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (S : Finset α) (h : α) : Prop :=
  ∃ T ∈ family, S ⊂ T ∧ h ∉ T

/-- Predicate packaging: a blocking witness for `T` drawn from the `h=1` slice of `family`. -/
def WitnessHasH {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (T : Finset α) (h : α) : Prop :=
  BlockedByTwoFrom (family.filter (fun A => h ∈ A)) T

theorem witnessHasH_unpacks {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {T : Finset α} {h : α}
    (hW : WitnessHasH family T h) :
    ∃ A ∈ family, ∃ B ∈ family, A ≠ B ∧ h ∈ A ∧ h ∈ B ∧
      ∃ core : Finset α,
        A ∩ B = core ∧ A ∩ T = core ∧ B ∩ T = core := by
  classical
  rcases hW with ⟨A, hA, B, hB, hAB, core, hcoreAB, hcoreAT, hcoreBT⟩
  have hAfam : A ∈ family := (Finset.mem_filter.mp hA).1
  have hBfam : B ∈ family := (Finset.mem_filter.mp hB).1
  have hhA : h ∈ A := (Finset.mem_filter.mp hA).2
  have hhB : h ∈ B := (Finset.mem_filter.mp hB).2
  exact ⟨A, hAfam, B, hBfam, hAB, hhA, hhB, core, hcoreAB, hcoreAT, hcoreBT⟩

/-- Predicate: a witness core supported on the singleton `{h}`. -/
def SingletonCore {α : Type*} [DecidableEq α] (core : Finset α) (h : α) : Prop :=
  core ⊆ ({h} : Finset α)

/--
Singleton-core branch (local, v0):
`T` has a `WitnessHasH` certificate whose common core is supported on `{h}`.
-/
def WitnessHasHSingletonCore {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (T : Finset α) (h : α) : Prop :=
  ∃ A ∈ family.filter (fun X => h ∈ X),
    ∃ B ∈ family.filter (fun X => h ∈ X), A ≠ B ∧
      ∃ core : Finset α,
        SingletonCore core h ∧ A ∩ B = core ∧ A ∩ T = core ∧ B ∩ T = core

/--
Non-singleton-core branch (local, v0):
there is a `WitnessHasH` certificate with `core ⊄ {h}`.
-/
def WitnessHasHNonSingletonCore {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (T : Finset α) (h : α) : Prop :=
  ∃ A ∈ family.filter (fun X => h ∈ X),
    ∃ B ∈ family.filter (fun X => h ∈ X), A ≠ B ∧
      ∃ core : Finset α,
        ¬ SingletonCore core h ∧ A ∩ B = core ∧ A ∩ T = core ∧ B ∩ T = core

/--
Case split for `WitnessHasH`: every witness core is either supported on `{h}` or not.

This is purely structural and is intended to keep later routers clean.
-/
theorem witnessHasH_cases_core {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {T : Finset α} {h : α}
    (hW : WitnessHasH family T h) :
    WitnessHasHSingletonCore family T h ∨ WitnessHasHNonSingletonCore family T h := by
  classical
  rcases hW with ⟨A, hA, B, hB, hne, core, hcoreAB, hcoreAT, hcoreBT⟩
  by_cases hcore : SingletonCore core h
  · exact Or.inl ⟨A, hA, B, hB, hne, core, hcore, hcoreAB, hcoreAT, hcoreBT⟩
  · exact Or.inr ⟨A, hA, B, hB, hne, core, hcore, hcoreAB, hcoreAT, hcoreBT⟩

/-- If a core is not supported on `{h}`, then it contains some element `j ≠ h`. -/
theorem exists_mem_core_ne_of_not_singletonCore {α : Type*} [DecidableEq α]
    {core : Finset α} {h : α} (hcore : ¬ SingletonCore core h) :
    ∃ j, j ∈ core ∧ j ≠ h := by
  classical
  -- `¬ core ⊆ {h}` gives a witness `j ∈ core` with `j ∉ {h}`.
  have : ¬ core ⊆ ({h} : Finset α) := hcore
  rcases (Finset.not_subset.mp this) with ⟨j, hjcore, hjnot⟩
  refine ⟨j, hjcore, ?_⟩
  intro hEq
  exact hjnot (hEq ▸ by simp)

/--
Unpack a non-singleton-core `WitnessHasH` certificate for `liftAt S h` and extract a witness element
`j ∈ S` (with `j ≠ h`) from the common core.
-/
theorem exists_mem_S_of_witnessHasHNonSingletonCore {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {S : Finset α} {h : α}
    (hW : WitnessHasHNonSingletonCore family (liftAt S h) h) :
    ∃ j, j ∈ S ∧ j ≠ h := by
  classical
  rcases hW with ⟨A, _hA, B, _hB, _hAB, core, hcore, _hcoreAB, hcoreAT, _hcoreBT⟩
  rcases exists_mem_core_ne_of_not_singletonCore (core := core) (h := h) hcore with
    ⟨j, hjcore, hjne⟩
  have hjT : j ∈ liftAt S h := by
    have : j ∈ A ∩ liftAt S h := by simpa [hcoreAT] using hjcore
    exact (Finset.mem_inter.mp this).2
  have hjU : j ∈ S ∪ ({h} : Finset α) := by
    simpa [liftAt] using hjT
  rcases Finset.mem_union.mp hjU with hjS | hjh
  · exact ⟨j, hjS, hjne⟩
  · have : j = h := by simpa using (Finset.mem_singleton.mp hjh)
    exact False.elim (hjne this)

-- ============================================================================
-- Option-2 (witness-lift) certificates (v0)
-- ============================================================================

/-
We keep this certificate universe-polymorphic (it lives in the same universe as `α`).

Lean note: writing `: Type` here defaults to `Type 0` and causes a universe mismatch because the
fields involve `Finset α` (which lives in `Type u` when `α : Type u`).
-/
universe uWL

/--
Witness-lift certificate (Option 2, v0).

This packages a non-singleton-core `WitnessHasH` witness for `liftAt S h` into a reusable object.
The key point is that we no longer try to force a selector condition like `j ∈ Nmax(h)`; instead we
produce a bounded-size certificate that can later be counted.
-/
structure WLcert {α : Type uWL} [DecidableEq α]
    (family : Finset (Finset α)) (S : Finset α) : Type uWL where
  (h : α)
  (A : Finset α)
  (B : Finset α)
  (core : Finset α)
  (j : α)
  (hmemA : A ∈ family ∧ h ∈ A)
  (hmemB : B ∈ family ∧ h ∈ B)
  (hneAB : A ≠ B)
  (hjcore : j ∈ core ∧ j ≠ h)
  (hcoreAB : A ∩ B = core)
  (hcoreAT : A ∩ liftAt S h = core)
  (hcoreBT : B ∩ liftAt S h = core)

abbrev WLcertKey (α : Type uWL) := α × α × Finset α × Finset α × Finset α

def WLcert.key {α : Type uWL} [DecidableEq α] {family : Finset (Finset α)} {S : Finset α}
    (cert : WLcert family S) : WLcertKey α :=
  (cert.h, cert.j, cert.A, cert.B, cert.core)

lemma wlcert_mem_core_h {α : Type uWL} [DecidableEq α]
    {family : Finset (Finset α)} {S : Finset α} (cert : WLcert family S) :
    cert.h ∈ cert.core := by
  classical
  have hT : cert.h ∈ liftAt S cert.h := by
    simp [liftAt]
  have hhA : cert.h ∈ cert.A := cert.hmemA.2
  have : cert.h ∈ cert.A ∩ liftAt S cert.h := Finset.mem_inter.mpr ⟨hhA, hT⟩
  simpa [cert.hcoreAT] using this

lemma wlcert_mem_core_j {α : Type uWL} [DecidableEq α]
    {family : Finset (Finset α)} {S : Finset α} (cert : WLcert family S) :
    cert.j ∈ cert.core :=
  cert.hjcore.1

lemma wlcert_h_ne_j {α : Type uWL} [DecidableEq α]
    {family : Finset (Finset α)} {S : Finset α} (cert : WLcert family S) :
    cert.h ≠ cert.j := by
  intro hEq
  exact cert.hjcore.2 (by simp [hEq])

lemma wlcert_mem_core_erase_h_of_ne {α : Type uWL} [DecidableEq α]
    {family : Finset (Finset α)} {S : Finset α} (cert : WLcert family S)
    {x : α} (hx : x ∈ cert.core) (hne : x ≠ cert.h) :
    x ∈ cert.core.erase cert.h := by
  exact Finset.mem_erase.mpr ⟨hne, hx⟩

lemma wlcert_inter_left_eq_core_erase_h {α : Type uWL} [DecidableEq α]
    {family : Finset (Finset α)} {S : Finset α} (cert : WLcert family S)
    (hhnS : cert.h ∉ S) :
    cert.A ∩ S = cert.core.erase cert.h := by
  classical
  ext x
  by_cases hx : x = cert.h
  · subst hx
    have : cert.h ∉ cert.core.erase cert.h := by
      simp
    simp [hhnS, this]
  · constructor
    · intro hxAS
      have hxA : x ∈ cert.A := (Finset.mem_inter.mp hxAS).1
      have hxS : x ∈ S := (Finset.mem_inter.mp hxAS).2
      have hxT : x ∈ liftAt S cert.h := by
        simp [liftAt, hxS]
      have hxAT : x ∈ cert.A ∩ liftAt S cert.h := Finset.mem_inter.mpr ⟨hxA, hxT⟩
      have hxcore : x ∈ cert.core := by
        simpa [cert.hcoreAT] using hxAT
      exact Finset.mem_erase.mpr ⟨hx, hxcore⟩
    · intro hxcore
      have hxcore' : x ∈ cert.core := (Finset.mem_erase.mp hxcore).2
      have hxAT : x ∈ cert.A ∩ liftAt S cert.h := by
        simpa [cert.hcoreAT] using hxcore'
      have hxA : x ∈ cert.A := (Finset.mem_inter.mp hxAT).1
      have hxT : x ∈ liftAt S cert.h := (Finset.mem_inter.mp hxAT).2
      have hxU : x ∈ S ∨ x ∈ ({cert.h} : Finset α) := by
        have : x ∈ S ∪ ({cert.h} : Finset α) := by
          simpa [liftAt] using hxT
        exact Finset.mem_union.mp this
      rcases hxU with hxS | hxH
      · exact Finset.mem_inter.mpr ⟨hxA, hxS⟩
      · have hxEq : x = cert.h := by
          simpa using (Finset.mem_singleton.mp hxH)
        exact False.elim (hx hxEq)

lemma wlcert_inter_right_eq_core_erase_h {α : Type uWL} [DecidableEq α]
    {family : Finset (Finset α)} {S : Finset α} (cert : WLcert family S)
    (hhnS : cert.h ∉ S) :
    cert.B ∩ S = cert.core.erase cert.h := by
  classical
  ext x
  by_cases hx : x = cert.h
  · subst hx
    have : cert.h ∉ cert.core.erase cert.h := by
      simp
    simp [hhnS, this]
  · constructor
    · intro hxBS
      have hxB : x ∈ cert.B := (Finset.mem_inter.mp hxBS).1
      have hxS : x ∈ S := (Finset.mem_inter.mp hxBS).2
      have hxT : x ∈ liftAt S cert.h := by
        simp [liftAt, hxS]
      have hxBT : x ∈ cert.B ∩ liftAt S cert.h := Finset.mem_inter.mpr ⟨hxB, hxT⟩
      have hxcore : x ∈ cert.core := by
        simpa [cert.hcoreBT] using hxBT
      exact Finset.mem_erase.mpr ⟨hx, hxcore⟩
    · intro hxcore
      have hxcore' : x ∈ cert.core := (Finset.mem_erase.mp hxcore).2
      have hxBT : x ∈ cert.B ∩ liftAt S cert.h := by
        simpa [cert.hcoreBT] using hxcore'
      have hxB : x ∈ cert.B := (Finset.mem_inter.mp hxBT).1
      have hxT : x ∈ liftAt S cert.h := (Finset.mem_inter.mp hxBT).2
      have hxU : x ∈ S ∨ x ∈ ({cert.h} : Finset α) := by
        have : x ∈ S ∪ ({cert.h} : Finset α) := by
          simpa [liftAt] using hxT
        exact Finset.mem_union.mp this
      rcases hxU with hxS | hxH
      · exact Finset.mem_inter.mpr ⟨hxB, hxS⟩
      · have hxEq : x = cert.h := by
          simpa using (Finset.mem_singleton.mp hxH)
        exact False.elim (hx hxEq)

/--
If a witness-lift certificate uses `h ∈ S` (so `liftAt S h = S`), then sunflower-freeness forces
the witness to reuse `S` as one of the two sets.

This is a useful “degenerate-certificate” eliminator: such certificates contribute at most
constantly many `S` to any fixed-key fiber (since the key stores `A` and `B`).
-/
lemma wlcert_A_eq_S_or_B_eq_S_of_h_mem_S {α : Type uWL} [DecidableEq α]
    {family : Finset (Finset α)} {S : Finset α}
    (hS : S ∈ family) (cert : WLcert family S)
    (hmemS : cert.h ∈ S) (hfree : IsSunflowerFree family 3) :
    cert.A = S ∨ cert.B = S := by
  classical
  by_contra hne
  have hAS : cert.A ≠ S := by
    intro hEq; exact hne (Or.inl hEq)
  have hBS : cert.B ≠ S := by
    intro hEq; exact hne (Or.inr hEq)
  have hsub : ({cert.A, cert.B, S} : Finset (Finset α)) ⊆ family := by
    intro X hX
    have hX' : X = cert.A ∨ X = cert.B ∨ X = S := by
      simpa using (Finset.mem_insert.mp hX)
    rcases hX' with rfl | hX'
    · exact cert.hmemA.1
    rcases hX' with rfl | rfl
    · exact cert.hmemB.1
    · exact hS
  have hlift : liftAt S cert.h = S := by
    ext x
    by_cases hx : x = cert.h
    · subst hx
      simp [liftAt, hmemS]
    · simp [liftAt, hx]
  have hsun : IsSunflower ({cert.A, cert.B, S} : Finset (Finset α)) 3 := by
    refine ⟨?_, cert.core, ?_⟩
    · -- card = 3, using `A ≠ B`, `A ≠ S`, `B ≠ S`.
      have hAB : cert.A ∉ ({cert.B, S} : Finset (Finset α)) := by
        simp [cert.hneAB, hAS]
      have hBS' : cert.B ∉ ({S} : Finset (Finset α)) := by
        simp [hBS]
      simp [Finset.card_insert_of_notMem, hAB, hBS']
    · intro X Y hX hY hXY
      have hX' : X = cert.A ∨ X = cert.B ∨ X = S := by
        simpa using (Finset.mem_insert.mp hX)
      have hY' : Y = cert.A ∨ Y = cert.B ∨ Y = S := by
        simpa using (Finset.mem_insert.mp hY)
      rcases hX' with rfl | hX'
      · rcases hY' with rfl | hY'
        · exact False.elim (hXY rfl)
        rcases hY' with rfl | rfl
        · simpa using cert.hcoreAB
        · simpa [hlift] using cert.hcoreAT
      rcases hX' with rfl | rfl
      · rcases hY' with rfl | hY'
        · simpa [Finset.inter_comm] using cert.hcoreAB
        rcases hY' with rfl | rfl
        · exact False.elim (hXY rfl)
        · simpa [hlift] using cert.hcoreBT
      · rcases hY' with rfl | hY'
        · simpa [Finset.inter_comm, hlift] using cert.hcoreAT
        rcases hY' with rfl | rfl
        · simpa [Finset.inter_comm, hlift] using cert.hcoreBT
        · exact False.elim (hXY rfl)
  exact False.elim (hfree ({cert.A, cert.B, S} : Finset (Finset α)) hsub hsun)

/--
Choice-free admissibility fiber: the `S ∈ dom` that admit *some* witness-lift certificate
with key `k`.

This is the preferred object for multiplicity bounds: it avoids depending on a specific
choice function.
-/
noncomputable def wlcertAdmissibleFiber {α : Type uWL} [DecidableEq α]
    {family : Finset (Finset α)} (dom : Finset (Finset α)) (k : WLcertKey α) :
    Finset {S // S ∈ dom} :=
by
  classical
  exact dom.attach.filter (fun Ssub => ∃ cert : WLcert family Ssub.1, WLcert.key cert = k)

/-- Choice-free admissibility fiber, restricted to certificates with `cert.h ∈ S`. -/
noncomputable def wlcertAdmissibleFiber_hMem {α : Type uWL} [DecidableEq α]
    {family : Finset (Finset α)} (dom : Finset (Finset α)) (k : WLcertKey α) :
    Finset {S // S ∈ dom} :=
by
  classical
  exact dom.attach.filter (fun Ssub =>
    ∃ cert : WLcert family Ssub.1, WLcert.key cert = k ∧ cert.h ∈ Ssub.1)

/-- Choice-free admissibility fiber, restricted to certificates with `cert.h ∉ S`. -/
noncomputable def wlcertAdmissibleFiber_hNotMem {α : Type uWL} [DecidableEq α]
    {family : Finset (Finset α)} (dom : Finset (Finset α)) (k : WLcertKey α) :
    Finset {S // S ∈ dom} :=
by
  classical
  exact dom.attach.filter (fun Ssub =>
    ∃ cert : WLcert family Ssub.1, WLcert.key cert = k ∧ cert.h ∉ Ssub.1)

lemma wlcertAdmissibleFiber_eq_hMem_union_hNotMem {α : Type uWL} [DecidableEq α]
    {family : Finset (Finset α)} (dom : Finset (Finset α)) (k : WLcertKey α) :
    wlcertAdmissibleFiber (family := family) dom k =
      (wlcertAdmissibleFiber_hMem (family := family) dom k) ∪
        (wlcertAdmissibleFiber_hNotMem (family := family) dom k) := by
  classical
  ext Ssub
  constructor
  · intro hSsub
    have hSsub' :
        ∃ cert : WLcert family Ssub.1, WLcert.key cert = k := (Finset.mem_filter.mp hSsub).2
    rcases hSsub' with ⟨cert, hk⟩
    by_cases hh : cert.h ∈ Ssub.1
    · refine Finset.mem_union.mpr (Or.inl ?_)
      refine Finset.mem_filter.mpr ?_
      exact ⟨(Finset.mem_filter.mp hSsub).1, ⟨cert, hk, hh⟩⟩
    · refine Finset.mem_union.mpr (Or.inr ?_)
      refine Finset.mem_filter.mpr ?_
      exact ⟨(Finset.mem_filter.mp hSsub).1, ⟨cert, hk, hh⟩⟩
  · intro hSsub
    rcases Finset.mem_union.mp hSsub with hSsub | hSsub
    · -- `hMem` case
      refine Finset.mem_filter.mpr ?_
      refine ⟨(Finset.mem_filter.mp hSsub).1, ?_⟩
      rcases (Finset.mem_filter.mp hSsub).2 with ⟨cert, hk, _hh⟩
      exact ⟨cert, hk⟩
    · -- `hNotMem` case
      refine Finset.mem_filter.mpr ?_
      refine ⟨(Finset.mem_filter.mp hSsub).1, ?_⟩
      rcases (Finset.mem_filter.mp hSsub).2 with ⟨cert, hk, _hh⟩
      exact ⟨cert, hk⟩

/--
Degenerate certificates (`cert.h ∈ S`) force `S` to equal one of the two witness sets `A` or `B`.
So for a fixed key `(h,j,A,B,core)` this branch contributes at most 2 sets.
-/
theorem wlcertAdmissibleFiber_hMem_card_le_two {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} (dom : Finset (Finset α))
    (k : WLcertKey α)
    (hdomFam : ∀ S ∈ dom, S ∈ family)
    (hfree : IsSunflowerFree family 3) :
    (wlcertAdmissibleFiber_hMem (family := family) dom k).card ≤ 2 := by
  classical
  rcases k with ⟨kh, kj, kA, kB, kcore⟩
  -- Use `Subtype.val` image: it is injective, and values lie in `{kA,kB}`.
  let s : Finset {S // S ∈ dom} :=
    wlcertAdmissibleFiber_hMem (family := family) dom (kh, kj, kA, kB, kcore)
  have hinj : Function.Injective (fun x : {S // S ∈ dom} => x.1) := by
    intro x y hxy
    exact Subtype.ext hxy
  have hcard_image :
      (s.image (fun x : {S // S ∈ dom} => x.1)).card = s.card :=
    Finset.card_image_of_injective (f := fun x : {S // S ∈ dom} => x.1) s hinj
  -- Image is contained in `{kA,kB}`.
  have hsub : s.image (fun x : {S // S ∈ dom} => x.1) ⊆ ({kA, kB} : Finset (Finset α)) := by
    intro S hS
    rcases Finset.mem_image.mp hS with ⟨Ssub, hSsub, rfl⟩
    rcases (Finset.mem_filter.mp hSsub).2 with ⟨cert, hk, hmem⟩
    have hSfam : Ssub.1 ∈ family := hdomFam Ssub.1 Ssub.2
    have hkA : cert.A = kA := by
      -- key equality gives componentwise equality.
      have : (cert.h, cert.j, cert.A, cert.B, cert.core) = (kh, kj, kA, kB, kcore) := by
        simpa [WLcert.key] using hk
      exact congrArg (fun t => t.2.2.1) this
    have hkB : cert.B = kB := by
      have : (cert.h, cert.j, cert.A, cert.B, cert.core) = (kh, kj, kA, kB, kcore) := by
        simpa [WLcert.key] using hk
      exact congrArg (fun t => t.2.2.2.1) this
    have hAB : cert.A = Ssub.1 ∨ cert.B = Ssub.1 :=
      wlcert_A_eq_S_or_B_eq_S_of_h_mem_S (family := family) (S := Ssub.1) hSfam cert hmem hfree
    have : Ssub.1 = kA ∨ Ssub.1 = kB := by
      rcases hAB with hEqA | hEqB
      · left; simpa [hkA] using hEqA.symm
      · right; simpa [hkB] using hEqB.symm
    simpa [Finset.mem_insert, Finset.mem_singleton] using this
  have hcard_image_le : (s.image (fun x : {S // S ∈ dom} => x.1)).card ≤ 2 := by
    have : (s.image (fun x : {S // S ∈ dom} => x.1)).card ≤ ({kA, kB} : Finset (Finset α)).card :=
      Finset.card_le_card hsub
    have hchoices : ({kA, kB} : Finset (Finset α)).card ≤ 2 := by
      by_cases hEq : kA = kB
      · subst hEq
        simp
      · simp [Finset.card_insert_of_notMem, hEq]
    exact this.trans hchoices
  -- Conclude
  have : s.card ≤ 2 :=
    (hcard_image.symm.le).trans hcard_image_le
  simpa [s] using this
/--
Noncomputable key-selection on a finite domain: choose one certificate for each `S ∈ dom`
and return its key. This is intended for later bounded-multiplicity counting arguments.
-/
noncomputable def wlcertKeyOnDom {α : Type uWL} [DecidableEq α]
    {family : Finset (Finset α)} (dom : Finset (Finset α))
    (hdom : ∀ S ∈ dom, Nonempty (WLcert family S)) :
    {S // S ∈ dom} → WLcertKey α :=
  fun Ssub => WLcert.key (Classical.choice (hdom Ssub.1 Ssub.2))

/-- Fiber of `wlcertKeyOnDom` over a fixed key `k`. -/
noncomputable def wlcertKeyFiber {α : Type uWL} [DecidableEq α]
    {family : Finset (Finset α)} (dom : Finset (Finset α))
    (hdom : ∀ S ∈ dom, Nonempty (WLcert family S)) (k : WLcertKey α) :
    Finset {S // S ∈ dom} :=
  dom.attach.filter (fun Ssub => wlcertKeyOnDom (family := family) dom hdom Ssub = k)

/-- The chosen-map fiber is always contained in the choice-free admissibility fiber. -/
theorem wlcertKeyFiber_subset_admissibleFiber {α : Type uWL} [DecidableEq α]
    {family : Finset (Finset α)} (dom : Finset (Finset α))
    (hdom : ∀ S ∈ dom, Nonempty (WLcert family S)) (k : WLcertKey α) :
    wlcertKeyFiber (family := family) dom hdom k ⊆
      wlcertAdmissibleFiber (family := family) dom k := by
  classical
  intro Ssub hSsub
  have hEq : wlcertKeyOnDom (family := family) dom hdom Ssub = k :=
    (Finset.mem_filter.mp hSsub).2
  have hcert : WLcert.key (Classical.choice (hdom Ssub.1 Ssub.2)) = k := by
    simpa [wlcertKeyOnDom] using hEq
  refine Finset.mem_filter.mpr ?_
  refine ⟨Finset.mem_attach dom Ssub, ?_⟩
  exact ⟨Classical.choice (hdom Ssub.1 Ssub.2), hcert⟩

/-- Convert a choice-free multiplicity bound into a bound for the chosen-map fiber. -/
theorem wlcertKeyFiber_card_le_of_admissible {α : Type uWL} [DecidableEq α]
    {family : Finset (Finset α)} (dom : Finset (Finset α))
    (hdom : ∀ S ∈ dom, Nonempty (WLcert family S)) (K : ℕ)
    (hK : ∀ k : WLcertKey α, (wlcertAdmissibleFiber (family := family) dom k).card ≤ K)
    (k : WLcertKey α) :
    (wlcertKeyFiber (family := family) dom hdom k).card ≤ K := by
  classical
  have hsub :=
    wlcertKeyFiber_subset_admissibleFiber (family := family) dom hdom k
  exact (Finset.card_le_card hsub).trans (hK k)

/--
Counting target (statement-only):
bounded multiplicity of witness-lift keys on a finite domain.

This is the core combinatorial lever of Option 2: once each `S` yields a certificate,
we bound the size of each fiber and then sum over possible keys.
-/
def wlcert_bounded_multiplicity_target_const (K : ℕ) : Prop :=
  ∀ {α : Type uWL} [DecidableEq α]
    {family : Finset (Finset α)} (dom : Finset (Finset α))
    (hdom : ∀ S ∈ dom, Nonempty (WLcert family S)) (k : WLcertKey α),
      (wlcertKeyFiber (family := family) dom hdom k).card ≤ K

/--
Choice-free multiplicity target: bound the size of the admissibility fiber.

This is usually easier to prove than a bound for a specific choice function; the latter follows by
`wlcertKeyFiber_subset_admissibleFiber`.
-/
def wlcert_choiceFree_multiplicity_target_const (K : ℕ) : Prop :=
  ∀ {α : Type uWL} [DecidableEq α]
    {family : Finset (Finset α)} (dom : Finset (Finset α)) (k : WLcertKey α),
      (wlcertAdmissibleFiber (family := family) dom k).card ≤ K

/--
Preferred multiplicity target: allow polynomial (or otherwise `n`-dependent) bounds.

Interpretation: for a domain whose ambient ground has size `n`, each key fiber has size ≤ `K n`.
The choice of `n` is external (typically `ground.card` in the O₁a leaf).
-/
def wlcert_bounded_multiplicity_target (K : ℕ → ℕ) : Prop :=
  ∀ {α : Type uWL} [DecidableEq α]
    (ground : Finset α) {family : Finset (Finset α)} (dom : Finset (Finset α))
    (hdom : ∀ S ∈ dom, Nonempty (WLcert family S)) (k : WLcertKey α),
      (wlcertKeyFiber (family := family) dom hdom k).card ≤ K ground.card

/-- Preferred choice-free multiplicity target: bound admissible fibers by `K ground.card`. -/
def wlcert_choiceFree_multiplicity_target (K : ℕ → ℕ) : Prop :=
  ∀ {α : Type uWL} [DecidableEq α]
    (ground : Finset α) {family : Finset (Finset α)} (dom : Finset (Finset α))
    (k : WLcertKey α),
      (wlcertAdmissibleFiber (family := family) dom k).card ≤ K ground.card

/-- Concrete (slack) polynomial multiplicity bound for the first full pass. -/
def wlcertK20 (n : ℕ) : ℕ := n ^ 20

/-- Operational multiplicity target: `K(n) = n^20`. -/
def wlcert_bounded_multiplicity_target_pow20 : Prop :=
  wlcert_bounded_multiplicity_target.{uWL} wlcertK20

/-- Operational choice-free multiplicity target: `K(n) = n^20`. -/
def wlcert_choiceFree_multiplicity_target_pow20 : Prop :=
  wlcert_choiceFree_multiplicity_target.{uWL} wlcertK20

/--
Basic counting glue: if every key fiber has size ≤ `K`, then `dom.card ≤ |image| * K`,
where `image` is the set of realized keys on `dom`.
-/
theorem card_le_card_image_mul_of_fiber_le {α : Type uWL} [DecidableEq α]
    {family : Finset (Finset α)} (dom : Finset (Finset α))
    (hdom : ∀ S ∈ dom, Nonempty (WLcert family S)) (K : ℕ)
    (hK : ∀ k : WLcertKey α, (wlcertKeyFiber (family := family) dom hdom k).card ≤ K) :
    dom.card ≤ (dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)).card * K := by
  classical
  -- Expand `dom.attach.card` via fiberwise counting over the key image.
  have hsum :
      dom.attach.card =
        ∑ k ∈ dom.attach.image (wlcertKeyOnDom (family := family) dom hdom),
          (wlcertKeyFiber (family := family) dom hdom k).card := by
    -- `card_eq_sum_card_image` counts fibers `{a ∈ dom.attach | f a = k}` over `k ∈ image f`.
    simpa [wlcertKeyFiber, Nat.card_eq_fintype_card] using
      (Finset.card_eq_sum_card_image
        (f := wlcertKeyOnDom (family := family) dom hdom) (s := dom.attach))
  -- Bound each fiber by `K` and collapse the sum.
  have hsum_le :
      (∑ k ∈ dom.attach.image (wlcertKeyOnDom (family := family) dom hdom),
          (wlcertKeyFiber (family := family) dom hdom k).card) ≤
        (dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)).card * K := by
    classical
    -- `∑_{k ∈ image} fiber(k) ≤ ∑_{k ∈ image} K = |image| * K`.
    calc
      (∑ k ∈ dom.attach.image (wlcertKeyOnDom (family := family) dom hdom),
            (wlcertKeyFiber (family := family) dom hdom k).card)
          ≤ ∑ _k ∈ dom.attach.image (wlcertKeyOnDom (family := family) dom hdom), K := by
              refine Finset.sum_le_sum ?_
              intro k hk
              exact hK k
      _ = (dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)).card * K := by
            simp [Nat.mul_comm]
  -- Convert back from `dom.attach.card` to `dom.card`.
  have hatt : dom.attach.card = dom.card := by
    exact Finset.card_attach (s := dom)
  have : dom.card ≤ (dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)).card * K := by
    -- `dom.card = dom.attach.card = sum fibers ≤ ...`.
    calc
      dom.card = dom.attach.card := hatt.symm
      _ = _ := hsum
      _ ≤ _ := hsum_le
  simpa using this

/--
Build a witness-lift certificate from a non-singleton-core `WitnessHasH` certificate.

This is pure packaging: it does not use anchoring, near-max selectors, or counting.
-/
theorem exists_WLcert_of_WitnessHasHNonSingletonCore {α : Type uWL} [DecidableEq α]
    {family : Finset (Finset α)} {S : Finset α} {h : α}
    (hW : WitnessHasHNonSingletonCore family (liftAt S h) h) :
    Nonempty (WLcert family S) := by
  classical
  rcases hW with ⟨A, hA, B, hB, hne, core, hcore, hcoreAB, hcoreAT, hcoreBT⟩
  have hAfam : A ∈ family := (Finset.mem_filter.mp hA).1
  have hhA : h ∈ A := (Finset.mem_filter.mp hA).2
  have hBfam : B ∈ family := (Finset.mem_filter.mp hB).1
  have hhB : h ∈ B := (Finset.mem_filter.mp hB).2
  rcases exists_mem_core_ne_of_not_singletonCore (core := core) (h := h) hcore with
    ⟨j, hjcore, hjne⟩
  refine ⟨
    { h := h
      A := A
      B := B
      core := core
      j := j
      hmemA := ⟨hAfam, hhA⟩
      hmemB := ⟨hBfam, hhB⟩
      hneAB := hne
      hjcore := ⟨hjcore, hjne⟩
      hcoreAB := hcoreAB
      hcoreAT := hcoreAT
      hcoreBT := hcoreBT }⟩

theorem offDiag_nonempty_of_witnessHasH {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {T : Finset α} {h : α}
    (hground : family ⊆ ground.powerset)
    (hW : WitnessHasH family T h) :
    ground.offDiag.Nonempty := by
  classical
  rcases hW with ⟨A, hA, B, hB, hAB, _core, _hcore⟩
  have hA_fam : A ∈ family := (Finset.mem_filter.mp hA).1
  have hB_fam : B ∈ family := (Finset.mem_filter.mp hB).1
  have hhA : h ∈ A := (Finset.mem_filter.mp hA).2
  have hhB : h ∈ B := (Finset.mem_filter.mp hB).2
  have hA_sub : A ⊆ ground := Finset.mem_powerset.mp (hground hA_fam)
  have hB_sub : B ⊆ ground := Finset.mem_powerset.mp (hground hB_fam)
  have hh_ground : h ∈ ground := hA_sub hhA
  have hnot_both : ¬ (A ⊆ B ∧ B ⊆ A) := by
    intro hsub
    exact hAB (Finset.Subset.antisymm hsub.1 hsub.2)
  rcases not_and_or.mp hnot_both with hAnot | hBnot
  · have hnon : (A \ B).Nonempty := (Finset.sdiff_nonempty).2 hAnot
    rcases hnon with ⟨x, hx⟩
    have hxA : x ∈ A := (Finset.mem_sdiff.mp hx).1
    have hxB : x ∉ B := (Finset.mem_sdiff.mp hx).2
    have hx_ground : x ∈ ground := hA_sub hxA
    have hne : h ≠ x := by
      intro hEq
      exact hxB (hEq ▸ hhB)
    refine ⟨(h, x), ?_⟩
    exact (Finset.mem_offDiag).2 ⟨hh_ground, hx_ground, hne⟩
  · have hnon : (B \ A).Nonempty := (Finset.sdiff_nonempty).2 hBnot
    rcases hnon with ⟨x, hx⟩
    have hxB : x ∈ B := (Finset.mem_sdiff.mp hx).1
    have hxA : x ∉ A := (Finset.mem_sdiff.mp hx).2
    have hx_ground : x ∈ ground := hB_sub hxB
    have hne : h ≠ x := by
      intro hEq
      exact hxA (hEq ▸ hhA)
    refine ⟨(h, x), ?_⟩
    exact (Finset.mem_offDiag).2 ⟨hh_ground, hx_ground, hne⟩

theorem maxCoDegreePairs_nonempty_of_witnessHasH {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {T : Finset α} {h : α}
    (hground : family ⊆ ground.powerset)
    (hW : WitnessHasH family T h) :
    (maxCoDegreePairs family ground).Nonempty := by
  classical
  have hOff : ground.offDiag.Nonempty := offDiag_nonempty_of_witnessHasH
    (family := family) (ground := ground) (T := T) (h := h) hground hW
  exact maxCoDegreePairs_nonempty_of_offDiag_nonempty (family := family) (ground := ground) hOff

theorem exists_mem_Nmax_of_anchor_of_witnessHasH {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {T : Finset α} {h : α}
    (hground : family ⊆ ground.powerset)
    (hanch : maxPairsAnchoredAt family ground h)
    (hW : WitnessHasH family T h) :
    ∃ j, j ∈ Nmax family ground h := by
  classical
  have hne : (maxCoDegreePairs family ground).Nonempty :=
    maxCoDegreePairs_nonempty_of_witnessHasH (family := family) (ground := ground) (T := T) (h := h)
      hground hW
  have hNne : (Nmax family ground h).Nonempty :=
    Nmax_nonempty_of_anchor_of_maxCoDegreePairs_nonempty
      (family := family) (ground := ground) (h := h) hanch hne
  rcases hNne with ⟨j, hj⟩
  exact ⟨j, hj⟩

/--
If a blocking witness for `liftAt S h` uses `A = S`,
then `S` has a strict `h`-free extension in `family`.
-/
theorem chainExtension_of_blockedByTwo_liftAt_of_left_eq {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {S B core : Finset α} {h : α}
    (hhnS : h ∉ S)
    (hB : B ∈ family) (hSB : S ≠ B)
    (hcoreAB : S ∩ B = core)
    (hcoreAT : S ∩ liftAt S h = core)
    (hcoreBT : B ∩ liftAt S h = core) :
    ChainExtension family S h := by
  classical
  have hcoreEq : core = S := by
    have hleft : S ∩ liftAt S h = S := by
      unfold liftAt
      -- rewrite to match `Finset.inter_union_self`
      rw [Finset.union_comm S ({h} : Finset α)]
      exact Finset.inter_union_self S ({h} : Finset α)
    exact hcoreAT.symm.trans hleft
  have hSsubB : S ⊆ B := by
    have hSB' : S ∩ B = S := by
      simpa [hcoreEq] using hcoreAB
    -- Use `S = S ∩ B` via `hSB'` to avoid simp loops
    intro x hx
    have hx' : x ∈ S ∩ B := by
      have hx' := hx
      rw [hSB'.symm] at hx'
      exact hx'
    exact (Finset.mem_inter.mp hx').2
  have hSssubB : S ⊂ B := Finset.ssubset_iff_subset_ne.2 ⟨hSsubB, hSB⟩
  have hhB : h ∉ B := by
    intro hhB
    have hT : h ∈ liftAt S h := by simp [liftAt]
    have hx : h ∈ B ∩ liftAt S h := Finset.mem_inter.mpr ⟨hhB, hT⟩
    have : h ∈ core := by simpa [hcoreBT] using hx
    have : h ∈ S := by simpa [hcoreEq] using this
    exact hhnS this
  exact ⟨B, hB, hSssubB, hhB⟩

/-- Symmetric version of `chainExtension_of_blockedByTwo_liftAt_of_left_eq`. -/
theorem chainExtension_of_blockedByTwo_liftAt_of_right_eq {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {S A core : Finset α} {h : α}
    (hhnS : h ∉ S)
    (hA : A ∈ family) (hSA : S ≠ A)
    (hcoreAB : A ∩ S = core)
    (hcoreAT : A ∩ liftAt S h = core)
    (hcoreBT : S ∩ liftAt S h = core) :
    ChainExtension family S h := by
  classical
  have hcoreEq : core = S := by
    have hleft : S ∩ liftAt S h = S := by
      unfold liftAt
      rw [Finset.union_comm S ({h} : Finset α)]
      exact Finset.inter_union_self S ({h} : Finset α)
    exact hcoreBT.symm.trans hleft
  have hSsubA : S ⊆ A := by
    have hSA' : S ∩ A = S := by
      have : S ∩ A = core := by simpa [Finset.inter_comm] using hcoreAB
      simpa [hcoreEq] using this
    intro x hx
    have hx' : x ∈ S ∩ A := by
      have hx' := hx
      rw [hSA'.symm] at hx'
      exact hx'
    exact (Finset.mem_inter.mp hx').2
  have hSssubA : S ⊂ A := Finset.ssubset_iff_subset_ne.2 ⟨hSsubA, hSA⟩
  have hhA : h ∉ A := by
    intro hhA
    have hT : h ∈ liftAt S h := by simp [liftAt]
    have hx : h ∈ A ∩ liftAt S h := Finset.mem_inter.mpr ⟨hhA, hT⟩
    have : h ∈ core := by simpa [hcoreAT] using hx
    have : h ∈ S := by simpa [hcoreEq] using this
    exact hhnS this
  exact ⟨A, hA, hSssubA, hhA⟩

/--
If `liftAt S h` is blocked, then either the witness can be chosen from the `h=1` slice,
or `S` has a strict extension still avoiding `h` (the chain-case).
-/
theorem blockedByTwoFrom_contains_h_or_chainExtension {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {S : Finset α} {h : α}
    (hS : S ∈ family) (hhnS : h ∉ S) (hfree : IsSunflowerFree family 3)
    (hblocked : BlockedByTwo family (liftAt S h)) :
    WitnessHasH family (liftAt S h) h ∨ ChainExtension family S h := by
  classical
  rcases
    blockedByTwo_liftAt_chain_case (family := family) (S := S) (h := h) hS hhnS hfree hblocked with
    ⟨A, hA, B, hB, hAB, core, hcoreAB, hcoreAT, hcoreBT, hchain⟩
  by_cases hhcore : h ∈ core
  · -- Both witnesses contain `h`, so we can pin them to the `h=1` slice.
    have hT : h ∈ liftAt S h := by simp [liftAt]
    have hAh : h ∈ A := (mem_left_iff_mem_core_of_mem_T_of_inter_eq
      (A := A) (T := liftAt S h) (core := core) hT hcoreAT).2 hhcore
    have hBh : h ∈ B := (mem_left_iff_mem_core_of_mem_T_of_inter_eq
      (A := B) (T := liftAt S h) (core := core) hT hcoreBT).2 hhcore
    refine Or.inl ?_
    refine ⟨A, ?_, B, ?_, hAB, core, hcoreAB, hcoreAT, hcoreBT⟩
    · exact Finset.mem_filter.mpr ⟨hA, hAh⟩
    · exact Finset.mem_filter.mpr ⟨hB, hBh⟩
  · -- Chain-case: one witness equals `S`, so `S` has a strict `h`-free extension.
    have hchain' : A = S ∨ B = S := hchain hhcore
    rcases hchain' with hAS | hBS
    · -- A = S
      have hSB : S ≠ B := by
        intro hEq
        exact hAB (hAS ▸ hEq ▸ rfl)
      have hcoreAB' : S ∩ B = core := by simpa [hAS] using hcoreAB
      have hcoreAT' : S ∩ liftAt S h = core := by simpa [hAS] using hcoreAT
      exact Or.inr
        (chainExtension_of_blockedByTwo_liftAt_of_left_eq
          (family := family) (S := S) (B := B) (core := core) (h := h)
          hhnS hB hSB hcoreAB' hcoreAT' hcoreBT)
    · -- B = S
      have hSA : S ≠ A := by
        intro hEq
        exact hAB (hEq ▸ hBS ▸ rfl)
      have hcoreAB' : A ∩ S = core := by simpa [hBS] using hcoreAB
      have hcoreBT' : S ∩ liftAt S h = core := by simpa [hBS] using hcoreBT
      exact Or.inr
        (chainExtension_of_blockedByTwo_liftAt_of_right_eq
          (family := family) (S := S) (A := A) (core := core) (h := h)
          hhnS hA hSA hcoreAB' hcoreAT hcoreBT')

/-- Max-pair reservoir around an anchor `h`: sets containing `h` and at least one max-neighbor. -/
def Wmax {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (h : α) : Finset (Finset α) :=
  family.filter (fun A => h ∈ A ∧ ∃ j ∈ Nmax family ground h, j ∈ A)

/-- Max-pair reservoir at a *fixed* neighbor `j`: sets containing both `h` and `j`. -/
def WmaxAt {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (_ground : Finset α) (h j : α) : Finset (Finset α) :=
  family.filter (fun A => h ∈ A ∧ j ∈ A)

lemma Wmax_subset_family {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (h : α) :
    Wmax family ground h ⊆ family := by
  intro A hA
  exact (Finset.mem_filter.mp hA).1

lemma WmaxAt_subset_family {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (h j : α) :
    WmaxAt family ground h j ⊆ family := by
  intro A hA
  exact (Finset.mem_filter.mp hA).1

lemma WmaxAt_subset_Wmax {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (h j : α)
    (hj : j ∈ Nmax family ground h) :
    WmaxAt family ground h j ⊆ Wmax family ground h := by
  classical
  intro A hA
  have hA' := Finset.mem_filter.mp hA
  refine Finset.mem_filter.mpr ?_
  refine ⟨hA'.1, ?_⟩
  refine ⟨hA'.2.1, ?_⟩
  refine ⟨j, hj, hA'.2.2⟩

/-- Any `WmaxAt(h,j)` blocking witness for `liftAt S h` forces `j ∈ liftAt S h`. -/
theorem mem_liftAt_of_blockedByTwoFrom_WmaxAt {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {S : Finset α} {h j : α}
    (hblocked : BlockedByTwoFrom (WmaxAt family ground h j) (liftAt S h)) :
    j ∈ liftAt S h := by
  classical
  rcases hblocked with ⟨A, hA, B, hB, _hAB, core, hcoreAB, hcoreAT, _hcoreBT⟩
  have hjA : j ∈ A := (Finset.mem_filter.mp hA).2.2
  have hjB : j ∈ B := (Finset.mem_filter.mp hB).2.2
  have hjcore : j ∈ core := by
    have : j ∈ A ∩ B := Finset.mem_inter.mpr ⟨hjA, hjB⟩
    simpa [hcoreAB] using this
  have : j ∈ A ∩ liftAt S h := by
    simpa [hcoreAT] using hjcore
  exact (Finset.mem_inter.mp this).2

/--
In particular, if `j ∈ Nmax(h)`, then a `WmaxAt(h,j)` witness for `liftAt S h`
implies `j ∈ S`.
-/
theorem mem_S_of_blockedByTwoFrom_WmaxAt_liftAt_of_mem_Nmax {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {S : Finset α} {h j : α}
    (hj : j ∈ Nmax family ground h)
    (hblocked : BlockedByTwoFrom (WmaxAt family ground h j) (liftAt S h)) :
    j ∈ S := by
  classical
  have hjT : j ∈ liftAt S h :=
    mem_liftAt_of_blockedByTwoFrom_WmaxAt
      (family := family) (ground := ground) (S := S) (h := h) (j := j) hblocked
  have hjU : j ∈ S ∪ ({h} : Finset α) := by
    simpa [liftAt] using hjT
  rcases Finset.mem_union.mp hjU with hjS | hjh
  · exact hjS
  · have hjEq : j = h := by
      simpa using (Finset.mem_singleton.mp hjh)
    have hj_ne : j ≠ h := by
      intro heq
      -- Unpack `j ∈ Nmax(h)` to extract an off-diagonal max pair containing `h`.
      rcases Finset.mem_union.mp hj with hjL | hjR
      · rcases Finset.mem_image.mp hjL with ⟨p, hp, hpj⟩
        have hp_in : p ∈ maxCoDegreePairs family ground := (Finset.mem_filter.mp hp).1
        have hp_off : p ∈ ground.offDiag := maxCoDegreePairs_subset_offDiag family ground hp_in
        have hoff := Finset.mem_offDiag.mp hp_off
        have hp1 : p.1 = h := (Finset.mem_filter.mp hp).2
        have : p.2 ≠ h := by
          intro hEq
          have : p.2 = p.1 := by simp [hp1, hEq]
          exact hoff.2.2 this.symm
        exact this (hpj.trans heq)
      · rcases Finset.mem_image.mp hjR with ⟨p, hp, hpj⟩
        have hp_in : p ∈ maxCoDegreePairs family ground := (Finset.mem_filter.mp hp).1
        have hp_off : p ∈ ground.offDiag := maxCoDegreePairs_subset_offDiag family ground hp_in
        have hoff := Finset.mem_offDiag.mp hp_off
        have hp2 : p.2 = h := (Finset.mem_filter.mp hp).2
        have : p.1 ≠ h := by
          intro hEq
          have : p.1 = p.2 := by simp [hp2, hEq]
          exact hoff.2.2 this
        exact this (hpj.trans heq)
    exact False.elim (hj_ne hjEq)

theorem blockedByTwo_of_not_sunflowerFree_insert {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {T : Finset α}
    (hfree : IsSunflowerFree family 3)
    (hTnot : T ∉ family)
    (hnot : ¬ IsSunflowerFree (insert T family) 3) :
    BlockedByTwo family T := by
  classical
  -- Extract a 3-sunflower subfamily of `insert T family`.
  have hex :
      ∃ sub : Finset (Finset α), sub ⊆ insert T family ∧ IsSunflower sub 3 := by
    simpa [IsSunflowerFree] using hnot
  rcases hex with ⟨sub, hsub, hsun⟩
  have hcard : sub.card = 3 := hsun.1
  have hTmem : T ∈ sub := by
    by_contra hTmem
    have hsub' : sub ⊆ family := by
      intro U hU
      have hU' : U ∈ insert T family := hsub hU
      have hUT : U = T ∨ U ∈ family := by simpa using (Finset.mem_insert.mp hU')
      rcases hUT with rfl | hUfam
      · exact False.elim (hTmem hU)
      · exact hUfam
    exact hfree sub hsub' hsun
  -- Pick the other two sets from `sub.erase T`.
  have hcard2 : (sub.erase T).card = 2 := by
    simpa [hcard] using (Finset.card_erase_of_mem hTmem)
  rcases Finset.card_eq_two.mp hcard2 with ⟨A, B, hAB, hsubAB⟩
  have hA_erase : A ∈ sub.erase T := by
    simp [hsubAB]
  have hB_erase : B ∈ sub.erase T := by
    simp [hsubAB]
  have hA_mem_sub : A ∈ sub := Finset.mem_of_mem_erase hA_erase
  have hB_mem_sub : B ∈ sub := Finset.mem_of_mem_erase hB_erase
  have hA_ne_T : A ≠ T := (Finset.mem_erase.mp hA_erase).1
  have hB_ne_T : B ≠ T := (Finset.mem_erase.mp hB_erase).1
  have hA_mem_ins : A ∈ insert T family := hsub hA_mem_sub
  have hB_mem_ins : B ∈ insert T family := hsub hB_mem_sub
  have hA_mem_fam : A ∈ family := by
    have hAT : A = T ∨ A ∈ family := by simpa using (Finset.mem_insert.mp hA_mem_ins)
    rcases hAT with hAT | hAfam
    · exact False.elim (hA_ne_T hAT)
    · exact hAfam
  have hB_mem_fam : B ∈ family := by
    have hBT : B = T ∨ B ∈ family := by simpa using (Finset.mem_insert.mp hB_mem_ins)
    rcases hBT with hBT | hBfam
    · exact False.elim (hB_ne_T hBT)
    · exact hBfam
  -- Use sunflower core property for the triple `{A,B,T}`.
  rcases hsun.2 with ⟨core, hcore⟩
  refine ⟨A, hA_mem_fam, B, hB_mem_fam, hAB, core, ?_, ?_, ?_⟩
  · exact hcore A B hA_mem_sub hB_mem_sub hAB
  · exact hcore A T hA_mem_sub hTmem hA_ne_T
  · exact hcore B T hB_mem_sub hTmem hB_ne_T

lemma Nmax_subset_erase {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (h : α) :
    Nmax family ground h ⊆ ground.erase h := by
  classical
  intro j hj
  rcases Finset.mem_union.mp hj with hj | hj
  · rcases Finset.mem_image.mp hj with ⟨p, hp, rfl⟩
    have hp_in : p ∈ maxCoDegreePairs family ground := (Finset.mem_filter.mp hp).1
    have hp' : p ∈ ground.offDiag := maxCoDegreePairs_subset_offDiag family ground hp_in
    have hoff := Finset.mem_offDiag.mp hp'
    have hph : p.1 = h := (Finset.mem_filter.mp hp).2
    -- `p.2 ∈ ground` and `p.2 ≠ p.1 = h`
    refine Finset.mem_erase.mpr ?_
    refine ⟨?_, hoff.2.1⟩
    intro hEq
    -- If `p.2 = h` and `p.1 = h`, then `p` is not off-diagonal.
    have : p.2 = p.1 := by simp [hph, hEq]
    exact hoff.2.2 this.symm
  · rcases Finset.mem_image.mp hj with ⟨p, hp, rfl⟩
    have hp_in : p ∈ maxCoDegreePairs family ground := (Finset.mem_filter.mp hp).1
    have hp' : p ∈ ground.offDiag := maxCoDegreePairs_subset_offDiag family ground hp_in
    have hoff := Finset.mem_offDiag.mp hp'
    have hph : p.2 = h := (Finset.mem_filter.mp hp).2
    refine Finset.mem_erase.mpr ?_
    refine ⟨?_, hoff.1⟩
    intro hEq
    have : p.1 = p.2 := by simp [hph, hEq]
    exact hoff.2.2 this

lemma Nmax_subset_supportMaxCoDegreePairs {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (h : α) :
    Nmax family ground h ⊆ supportMaxCoDegreePairs family ground := by
  classical
  intro j hj
  rcases Finset.mem_union.mp hj with hj | hj
  · rcases Finset.mem_image.mp hj with ⟨p, hp, rfl⟩
    refine (mem_supportMaxCoDegreePairs_iff (family := family) (ground := ground) (x := p.2)).2 ?_
    refine ⟨p, ?_, Or.inr rfl⟩
    exact (Finset.mem_filter.mp hp).1
  · rcases Finset.mem_image.mp hj with ⟨p, hp, rfl⟩
    refine (mem_supportMaxCoDegreePairs_iff (family := family) (ground := ground) (x := p.1)).2 ?_
    refine ⟨p, ?_, Or.inl rfl⟩
    exact (Finset.mem_filter.mp hp).1

lemma Nmax_subset_supportMaxCoDegreePairs_erase {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (h : α) :
    Nmax family ground h ⊆ (supportMaxCoDegreePairs family ground).erase h := by
  classical
  intro j hj
  have hj_supp : j ∈ supportMaxCoDegreePairs family ground :=
    Nmax_subset_supportMaxCoDegreePairs (family := family) (ground := ground) (h := h) hj
  have hj_erase_ground : j ∈ ground.erase h :=
    Nmax_subset_erase (family := family) (ground := ground) (h := h) hj
  have hj_ne : j ≠ h := (Finset.mem_erase.mp hj_erase_ground).1
  exact Finset.mem_erase.mpr ⟨hj_ne, hj_supp⟩

theorem supportMaxCoDegreePairs_erase_subset_Nmax_of_anchor {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {h : α}
    (hanch : maxPairsAnchoredAt family ground h) :
    (supportMaxCoDegreePairs family ground).erase h ⊆ Nmax family ground h := by
  classical
  intro j hj
  have hj_ne : j ≠ h := (Finset.mem_erase.mp hj).1
  have hj_supp : j ∈ supportMaxCoDegreePairs family ground := (Finset.mem_erase.mp hj).2
  have hjp' :
      ∃ p ∈ maxCoDegreePairs family ground, j = p.1 ∨ j = p.2 :=
    (mem_supportMaxCoDegreePairs_iff (family := family) (ground := ground) (x := j)).1 hj_supp
  rcases hjp' with ⟨p, hp, hjp⟩
  have hp_anchor : p.1 = h ∨ p.2 = h := hanch.2 p hp
  rcases hjp with rfl | rfl
  · -- `j = p.1`
    rcases hp_anchor with hp1 | hp2
    · exact False.elim (hj_ne hp1)
    · -- `p.2 = h`, so `j` is the other endpoint: `p.1 ∈ Nmax`
      refine Finset.mem_union.mpr ?_
      refine Or.inr ?_
      refine Finset.mem_image.mpr ?_
      refine ⟨p, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨hp, hp2⟩
  · -- `j = p.2`
    rcases hp_anchor with hp1 | hp2
    · -- `p.1 = h`, so `j` is the other endpoint: `p.2 ∈ Nmax`
      refine Finset.mem_union.mpr ?_
      refine Or.inl ?_
      refine Finset.mem_image.mpr ?_
      refine ⟨p, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨hp, hp1⟩
    · exact False.elim (hj_ne hp2)

theorem supportMaxCoDegreePairs_erase_eq_Nmax_of_anchor {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {h : α}
    (hanch : maxPairsAnchoredAt family ground h) :
    (supportMaxCoDegreePairs family ground).erase h = Nmax family ground h := by
  classical
  apply Finset.Subset.antisymm
  · exact
      supportMaxCoDegreePairs_erase_subset_Nmax_of_anchor
        (family := family) (ground := ground) (h := h) hanch
  · exact Nmax_subset_supportMaxCoDegreePairs_erase (family := family) (ground := ground) (h := h)

/--
Target “O₁a → constrained remainder” statement (no proof yet).

For a chosen parameter `r`, every set in the `h=0` slice is forced into `RClass` (a restricted class
expressed in terms of the max-neighbor set `Nmax`).

This is the first nontrivial Type-II brick: it should use maximality + anchored max-pairs to produce
a countable description of the remainder.
-/
def O1a_constrains_h0 (r : ℕ) : Prop :=
  ∀ {α : Type*} [DecidableEq α] (family : Finset (Finset α)) (ground : Finset α),
    family ⊆ ground.powerset →
    IsSunflowerFree family 3 →
    (∀ S ⊆ ground, S ∉ family → ¬ IsSunflowerFree (insert S family) 3) →
    ObstructionO1a family ground →
    ∃ h, maxPairsAnchoredAt family ground h ∧
      ∀ S ∈ family, h ∉ S → RClass family ground h r S

/--
Certificate-style remainder class: either the `h`-lift is present,
or it is blocked by a sunflower witness.
-/
def RClassWitness {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (h : α) (S : Finset α) : Prop :=
  S ⊆ ground ∧ h ∉ S ∧
    (liftAt S h ∈ family ∨ BlockedByTwo family (liftAt S h))

theorem o1a_constrains_h0_witness {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α}
    (hground : family ⊆ ground.powerset)
    (hfree : IsSunflowerFree family 3)
    (hmax : ∀ S ⊆ ground, S ∉ family → ¬ IsSunflowerFree (insert S family) 3)
    (hO1a : ObstructionO1a family ground) :
    ∃ h, maxPairsAnchoredAt family ground h ∧
      ∀ S ∈ family, h ∉ S → RClassWitness family ground h S := by
  classical
  rcases hO1a with ⟨h, hanch⟩
  refine ⟨h, hanch, ?_⟩
  intro S hS hhnS
  have hSsub : S ⊆ ground := Finset.mem_powerset.mp (hground hS)
  refine ⟨hSsub, hhnS, ?_⟩
  by_cases hLift : liftAt S h ∈ family
  · exact Or.inl hLift
  · have hLiftSub : liftAt S h ⊆ ground := by
      intro x hx
      have hx' : x ∈ S ∨ x = h := by
        simpa [liftAt] using (Finset.mem_union.mp hx)
      rcases hx' with hxS | rfl
      · exact hSsub hxS
      · exact hanch.1
    have hnot : ¬ IsSunflowerFree (insert (liftAt S h) family) 3 :=
      hmax (liftAt S h) hLiftSub hLift
    exact Or.inr (blockedByTwo_of_not_sunflowerFree_insert (family := family) (T := liftAt S h)
      hfree hLift hnot)

/--
Target statement (no proof yet): upgrade the generic maximality witness
into the max-pair reservoir.
-/
def o1a_witness_upgrade : Prop :=
  ∀ {α : Type*} [DecidableEq α] (family : Finset (Finset α)) (ground : Finset α),
    family ⊆ ground.powerset →
    IsSunflowerFree family 3 →
    (∀ T ⊆ ground, T ∉ family → ¬ IsSunflowerFree (insert T family) 3) →
    ObstructionO1a family ground →
    ∃ h, maxPairsAnchoredAt family ground h ∧
      ∀ S ∈ family, h ∉ S →
        liftAt S h ∈ family ∨ BlockedByTwoFrom (Wmax family ground h) (liftAt S h)

/--
Stronger witness-upgrade target (no proof yet):
produce the witness together with a specific max-neighbor `j`.

This is the version that should let `Nmax` start constraining `S`,
because it gives a handle to pigeonhole on `j`.
-/
def o1a_witness_upgrade_at : Prop :=
  ∀ {α : Type*} [DecidableEq α] (family : Finset (Finset α)) (ground : Finset α),
    family ⊆ ground.powerset →
    IsSunflowerFree family 3 →
    (∀ T ⊆ ground, T ∉ family → ¬ IsSunflowerFree (insert T family) 3) →
    ObstructionO1a family ground →
    ∃ h, maxPairsAnchoredAt family ground h ∧
      ∀ S ∈ family, h ∉ S →
        liftAt S h ∈ family ∨
          ∃ j, j ∈ S ∧ j ∈ Nmax family ground h ∧
            BlockedByTwoFrom (WmaxAt family ground h j) (liftAt S h)

/--
Split target (router, v1):
under O₁a, each `h=0` set either lifts, upgrades to a specific `WmaxAt(h,j)` witness,
or falls into the chain-extension bucket.

This is the explicit “two-leaf” boundary:
- the *upgrade leaf* is `o1a_witness_upgrade_at` (no chain extensions allowed),
- the *chain leaf* is treated as residual until we can show it collapses to Type I.
-/
def o1a_witness_upgrade_at_or_chain : Prop :=
  ∀ {α : Type*} [DecidableEq α] (family : Finset (Finset α)) (ground : Finset α),
    family ⊆ ground.powerset →
    IsSunflowerFree family 3 →
    (∀ T ⊆ ground, T ∉ family → ¬ IsSunflowerFree (insert T family) 3) →
    ObstructionO1a family ground →
    ∃ h, maxPairsAnchoredAt family ground h ∧
      ∀ S ∈ family, h ∉ S →
        liftAt S h ∈ family ∨
          (∃ j, j ∈ S ∧ j ∈ Nmax family ground h ∧
            BlockedByTwoFrom (WmaxAt family ground h j) (liftAt S h)) ∨
          ChainExtension family S h

/--
Leaf target (upgrade, v1):
on the non-chain branch where `liftAt S h` has an `h=1` witness (`WitnessHasH`),
upgrade to a specific max-neighbor `j ∈ Nmax(h)` and witnesses from `WmaxAt(h,j)`.

This is the “real” O₁a mechanism and the current chokepoint.
-/
def hiFail {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (A : ℕ) : Prop :=
  ∀ i ∈ ground,
    Nat.min (sliceAvoid family i).card
      (sliceReduce family ({i} : Finset α)).card > A

def o1a_upgrade_hasH_to_WmaxAt : Prop :=
  ∀ {α : Type*} [DecidableEq α] (family : Finset (Finset α)) (ground : Finset α) (A : ℕ),
    family ⊆ ground.powerset →
    IsSunflowerFree family 3 →
    (∀ T ⊆ ground, T ∉ family → ¬ IsSunflowerFree (insert T family) 3) →
    hiFail family ground A →
    2 ≤ maxCoDegree family ground →
    ObstructionO1a family ground →
    ∃ h, maxPairsAnchoredAt family ground h ∧
      ∀ S ∈ family, h ∉ S →
        liftAt S h ∈ family ∨
          (WitnessHasH family (liftAt S h) h →
            (∃ j, j ∈ S ∧ j ∈ Nmax family ground h ∧
              BlockedByTwoFrom (WmaxAt family ground h j) (liftAt S h)) ∨
            ¬ WitnessHasHNonSingletonCore family (liftAt S h) h)

/--
Provable router lemma (v0):
under maximality + O₁a, every `h=0` set either lifts, has an `h=1`-slice witness,
or is in the chain bucket.

This is the “clean fork” we use to keep the O₁a pipeline modular.
-/
theorem o1a_router_hasH_or_chain {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α}
    (hground : family ⊆ ground.powerset)
    (hfree : IsSunflowerFree family 3)
    (hmax : ∀ T ⊆ ground, T ∉ family → ¬ IsSunflowerFree (insert T family) 3)
    (hO1a : ObstructionO1a family ground) :
    ∃ h, maxPairsAnchoredAt family ground h ∧
      ∀ S ∈ family, h ∉ S →
        liftAt S h ∈ family ∨
          WitnessHasH family (liftAt S h) h ∨
          ChainExtension family S h := by
  classical
  rcases o1a_constrains_h0_witness
      (family := family) (ground := ground) hground hfree hmax hO1a with ⟨h, hanch, hcert⟩
  refine ⟨h, hanch, ?_⟩
  intro S hS hhnS
  rcases hcert S hS hhnS with ⟨_hSsub, _hhnS, hcases⟩
  rcases hcases with hLift | hBlocked
  · exact Or.inl hLift
  · -- Either upgrade the witness to the `h=1` slice, or fall into the chain bucket.
    have := blockedByTwoFrom_contains_h_or_chainExtension
      (family := family) (S := S) (h := h) hS hhnS hfree hBlocked
    exact Or.inr this

/-- Target statement (no proof yet): strong witness ⇒ Nmax-style remainder class. -/
def o1a_rclass (r : ℕ) : Prop :=
  ∀ {α : Type*} [DecidableEq α] (family : Finset (Finset α)) (ground : Finset α),
    family ⊆ ground.powerset →
    IsSunflowerFree family 3 →
    (∀ T ⊆ ground, T ∉ family → ¬ IsSunflowerFree (insert T family) 3) →
    ObstructionO1a family ground →
    ∃ h, maxPairsAnchoredAt family ground h ∧
      ∀ S ∈ family, h ∉ S → RClass family ground h r S

/--
Target statement for the first completed Type-II leaf (O₁a: anchored max co-degree pairs).

This is statement-only (no proof yet). It encodes the “base 3/2 with slack” recurrence step:
for a fixed constant `ε = epsNum/epsDen`, show `|F| ≤ (3/2 + ε)·M(n−1,3)` under maximality + O₁a.

Numerically we avoid division by stating the inequality after multiplying by `2*epsDen`.
-/
def O1a_recurrence_step (epsNum epsDen : ℕ) : Prop :=
  epsDen > 0 ∧
  ∀ {α : Type*} [DecidableEq α] (family : Finset (Finset α)) (ground : Finset α),
    family ⊆ ground.powerset →
    IsSunflowerFree family 3 →
    (∀ S ⊆ ground, S ∉ family → ¬ IsSunflowerFree (insert S family) 3) →
    ObstructionO1a family ground →
    ∃ h, maxPairsAnchoredAt family ground h ∧
      (2 * epsDen) * family.card ≤
        (3 * epsDen + 2 * epsNum) * maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3

/-- Near-max anchored neighbors at a coordinate `h`:
the set of `j ∈ ground \\ {h}` such that `T ≤ c_{h j}`. -/
def nearAnchorSet {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (h : α) (T : ℕ) : Finset α :=
  (ground.erase h).filter (fun j => T ≤ coDegree family h j)

lemma nearAnchorSet_subset_erase {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (h : α) (T : ℕ) :
    nearAnchorSet family ground h T ⊆ ground.erase h := by
  intro j hj
  exact (Finset.mem_filter.mp hj).1

lemma nearAnchorSet_forall {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (h : α) (T : ℕ) :
    ∀ j ∈ nearAnchorSet family ground h T, T ≤ coDegree family h j := by
  intro j hj
  exact (Finset.mem_filter.mp hj).2

lemma coDegree_eq_card_filter {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (i j : α) :
    coDegree family i j = (family.filter (fun S => i ∈ S ∧ j ∈ S)).card := by
  classical
  -- `coDegree` is defined via the reduced pair-slice, which is equinumerous with the raw slice.
  unfold coDegree pairSlice
  calc
    (sliceReduce family ({i, j} : Finset α)).card = (slice family ({i, j} : Finset α)).card := by
      simpa using card_sliceReduce_eq_card_slice family ({i, j} : Finset α)
    _ = (family.filter (fun S => i ∈ S ∧ j ∈ S)).card := by
      -- rewrite `{i,j} ⊆ S` into `i ∈ S ∧ j ∈ S`
      have hEq :
          family.filter (fun S => ({i, j} : Finset α) ⊆ S) =
            family.filter (fun S => i ∈ S ∧ j ∈ S) := by
        ext S
        simp [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      simp [slice, hEq]

/-- `WmaxAt(h,j)` is the raw `{h,j}`-slice, so its card is the co-degree `c_{h j}`. -/
lemma card_WmaxAt_eq_coDegree {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (h j : α) :
    (WmaxAt family ground h j).card = coDegree family h j := by
  classical
  simpa [WmaxAt] using (coDegree_eq_card_filter (family := family) (i := h) (j := j)).symm

/-- If `c_{h j} ≥ 2`, then the reservoir `WmaxAt(h,j)` contains two distinct sets. -/
theorem exists_two_mem_WmaxAt_of_two_le_coDegree {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {h j : α}
    (h2 : 2 ≤ coDegree family h j) :
    ∃ A ∈ WmaxAt family ground h j, ∃ B ∈ WmaxAt family ground h j, A ≠ B := by
  classical
  have hlt : 1 < (WmaxAt family ground h j).card := by
    have hlt' : 1 < coDegree family h j := Nat.lt_of_lt_of_le (by decide : 1 < 2) h2
    simpa [card_WmaxAt_eq_coDegree (family := family) (ground := ground) (h := h) (j := j)] using
      hlt'
  exact (Finset.one_lt_card).1 hlt

/-- If `j ∈ Nmax(h)` and the maximum co-degree is at least `2`, then `WmaxAt(h,j)` is nontrivial. -/
theorem exists_two_mem_WmaxAt_of_mem_Nmax_of_two_le_maxCoDegree {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {h j : α}
    (hj : j ∈ Nmax family ground h) (h2 : 2 ≤ maxCoDegree family ground) :
    ∃ A ∈ WmaxAt family ground h j, ∃ B ∈ WmaxAt family ground h j, A ≠ B := by
  classical
  have hEq : maxCoDegree family ground = coDegree family h j :=
    (coDegree_eq_maxCoDegree_of_mem_Nmax (family := family) (ground := ground) (h := h) hj).symm
  have h2' : 2 ≤ coDegree family h j := by
    simpa [hEq] using h2
  exact exists_two_mem_WmaxAt_of_two_le_coDegree (family := family) (ground := ground) (h := h) h2'

theorem exists_j_with_two_mem_WmaxAt_of_anchor_of_witnessHasH_of_two_le_maxCoDegree
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {T : Finset α} {h : α}
    (hground : family ⊆ ground.powerset)
    (hanch : maxPairsAnchoredAt family ground h)
    (hW : WitnessHasH family T h)
    (h2 : 2 ≤ maxCoDegree family ground) :
    ∃ j ∈ Nmax family ground h,
      ∃ A ∈ WmaxAt family ground h j, ∃ B ∈ WmaxAt family ground h j, A ≠ B := by
  classical
  rcases exists_mem_Nmax_of_anchor_of_witnessHasH
      (family := family) (ground := ground) (T := T) (h := h) hground hanch hW with ⟨j, hj⟩
  rcases exists_two_mem_WmaxAt_of_mem_Nmax_of_two_le_maxCoDegree
      (family := family) (ground := ground) (h := h) (j := j) hj h2 with ⟨A, hA, B, hB, hAB⟩
  exact ⟨j, hj, A, hA, B, hB, hAB⟩

/-- A co-degree is bounded by the degree at its left endpoint. -/
theorem coDegree_le_coordDegree_left {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (i j : α) :
    coDegree family i j ≤ coordDegree family i := by
  classical
  have hsubset :
      family.filter (fun S => i ∈ S ∧ j ∈ S) ⊆ family.filter (fun S => i ∈ S) := by
    intro S hS
    have hS' := Finset.mem_filter.mp hS
    exact Finset.mem_filter.mpr ⟨hS'.1, hS'.2.1⟩
  calc
    coDegree family i j = (family.filter (fun S => i ∈ S ∧ j ∈ S)).card := by
      simpa using coDegree_eq_card_filter (family := family) (i := i) (j := j)
    _ ≤ (family.filter (fun S => i ∈ S)).card := Finset.card_le_card hsubset
    _ = coordDegree family i := rfl

/-- A co-degree is bounded by the degree at its right endpoint. -/
theorem coDegree_le_coordDegree_right {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (i j : α) :
    coDegree family i j ≤ coordDegree family j := by
  simpa [coDegree_comm] using coDegree_le_coordDegree_left (family := family) (i := j) (j := i)

/--
Double-counting identity for co-degrees anchored at a coordinate `h`.

If `family` lives on `ground`, then summing co-degrees `c_{h j}` over `j ∈ ground \\ {h}`
counts the total number of “(other) coordinates” appearing in sets that contain `h`.
-/
theorem sum_coDegree_anchor_eq_sum_erase_card {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (h : α)
    (h_ground : ∀ S ∈ family, S ⊆ ground) :
    (ground.erase h).sum (fun j => coDegree family h j) =
      (family.filter (fun S => h ∈ S)).sum (fun S => (S.erase h).card) := by
  classical
  -- Convert each co-degree into an indicator sum over `family`.
  have hco :
      ∀ j, coDegree family h j =
        family.sum (fun S => if h ∈ S ∧ j ∈ S then (1 : ℕ) else 0) := by
    intro j
    calc
      coDegree family h j = (family.filter (fun S => h ∈ S ∧ j ∈ S)).card := by
        simpa using coDegree_eq_card_filter (family := family) (i := h) (j := j)
      _ = ∑ S ∈ family.filter (fun S => h ∈ S ∧ j ∈ S), (1 : ℕ) := by
        exact Finset.card_eq_sum_ones (family.filter (fun S => h ∈ S ∧ j ∈ S))
      _ = family.sum (fun S => if h ∈ S ∧ j ∈ S then (1 : ℕ) else 0) := by
        exact (Finset.sum_filter (s := family) (f := fun _ => (1 : ℕ))
          (p := fun S => h ∈ S ∧ j ∈ S))
  have hswap :
      (ground.erase h).sum (fun j =>
          family.sum (fun S => if h ∈ S ∧ j ∈ S then (1 : ℕ) else 0)) =
        family.sum (fun S =>
          (ground.erase h).sum (fun j => if h ∈ S ∧ j ∈ S then (1 : ℕ) else 0)) := by
    have h1 :=
      (Finset.sum_product' (s := ground.erase h) (t := family)
        (f := fun j S => if h ∈ S ∧ j ∈ S then (1 : ℕ) else 0))
    have h2 :=
      (Finset.sum_product_right' (s := ground.erase h) (t := family)
        (f := fun j S => if h ∈ S ∧ j ∈ S then (1 : ℕ) else 0))
    exact h1.symm.trans h2
  calc
    (ground.erase h).sum (fun j => coDegree family h j)
        = (ground.erase h).sum (fun j =>
            family.sum (fun S => if h ∈ S ∧ j ∈ S then (1 : ℕ) else 0)) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            exact hco j
    _ = family.sum (fun S =>
          (ground.erase h).sum (fun j => if h ∈ S ∧ j ∈ S then (1 : ℕ) else 0)) := hswap
    _ = family.sum (fun S => if h ∈ S then (S.erase h).card else 0) := by
          refine Finset.sum_congr rfl ?_
          intro S hS
          have hSsub : S ⊆ ground := h_ground S hS
          by_cases hhS : h ∈ S
          · -- reduce to counting `j ∈ S` inside `ground.erase h`
            have hfilter : (ground.erase h).filter (fun j => j ∈ S) = S.erase h := by
              ext j
              constructor
              · intro hj
                have hj' := Finset.mem_filter.mp hj
                have hjg : j ∈ ground.erase h := hj'.1
                have hjS : j ∈ S := hj'.2
                have hjg' := Finset.mem_erase.mp hjg
                exact Finset.mem_erase.mpr ⟨hjg'.1, hjS⟩
              · intro hj
                have hj' := Finset.mem_erase.mp hj
                have hjS : j ∈ S := hj'.2
                have hjg : j ∈ ground.erase h := Finset.mem_erase.mpr ⟨hj'.1, hSsub hjS⟩
                exact Finset.mem_filter.mpr ⟨hjg, hjS⟩
            -- Convert the sum to a card of a filter, then rewrite via hfilter.
            have hsum :
                (ground.erase h).sum (fun j => if h ∈ S ∧ j ∈ S then (1 : ℕ) else 0) =
                  (S.erase h).card := by
              calc
                (ground.erase h).sum (fun j => if h ∈ S ∧ j ∈ S then (1 : ℕ) else 0)
                    = (ground.erase h).sum (fun j => if j ∈ S then (1 : ℕ) else 0) := by
                        simp [hhS]
                _ = ((ground.erase h).filter (fun j => j ∈ S)).card := by
                      -- `card = sum_ones` + `sum_filter`
                      calc
                        (ground.erase h).sum (fun j => if j ∈ S then (1 : ℕ) else 0)
                            = ∑ j ∈ (ground.erase h).filter (fun j => j ∈ S), (1 : ℕ) := by
                                exact
                                  (Finset.sum_filter (s := ground.erase h) (f := fun _ => (1 : ℕ))
                                    (p := fun j => j ∈ S)).symm
                        _ = ((ground.erase h).filter (fun j => j ∈ S)).card := by
                              exact (Finset.card_eq_sum_ones
                                ((ground.erase h).filter (fun j => j ∈ S))).symm
                _ = (S.erase h).card := by
                      simp [hfilter]
            simpa [hhS] using hsum
          · -- if `h ∉ S` then the indicator is always false
            simp [hhS]
    _ = (family.filter (fun S => h ∈ S)).sum (fun S => (S.erase h).card) := by
          -- Filter out the `h ∉ S` terms.
          exact (Finset.sum_filter (s := family) (f := fun S => (S.erase h).card)
            (p := fun S => h ∈ S)).symm

/--
Lower bound for anchored co-degree sums.

If `J ⊆ ground \\ {h}` and every `j ∈ J` satisfies `T ≤ c_{h j}`, then the total anchored co-degree
sum over `ground \\ {h}` is at least `T * |J|`.

This is a simple bookkeeping lemma used in the O₁ “near-max anchored pairs” variants.
-/
theorem mul_card_le_sum_coDegree_of_forall_ge {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (h : α)
    (J : Finset α) (T : ℕ)
    (hJ : J ⊆ ground.erase h)
    (hT : ∀ j ∈ J, T ≤ coDegree family h j) :
    T * J.card ≤ (ground.erase h).sum (fun j => coDegree family h j) := by
  classical
  have hJsum : T * J.card = J.sum (fun _ => T) := by
    simp [Nat.mul_comm]
  have hsumJ : J.sum (fun _ => T) ≤ J.sum (fun j => coDegree family h j) := by
    refine Finset.sum_le_sum ?_
    intro j hj
    exact hT j hj
  have hsumSubset :
      J.sum (fun j => coDegree family h j) ≤
        (ground.erase h).sum (fun j => coDegree family h j) := by
    -- Monotonicity of sums over subsets (all terms are nonnegative in ℕ).
    refine Finset.sum_le_sum_of_subset_of_nonneg hJ ?_
    intro j _hjground _hjnot
    exact Nat.zero_le _
  -- Chain the bounds.
  calc
    T * J.card = J.sum (fun _ => T) := hJsum
    _ ≤ J.sum (fun j => coDegree family h j) := hsumJ
    _ ≤ (ground.erase h).sum (fun j => coDegree family h j) := hsumSubset

theorem mul_card_nearAnchorSet_le_sum_coDegree {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (h : α) (T : ℕ) :
    T * (nearAnchorSet family ground h T).card ≤
      (ground.erase h).sum (fun j => coDegree family h j) := by
  classical
  exact
    mul_card_le_sum_coDegree_of_forall_ge (family := family) (ground := ground) (h := h)
      (J := nearAnchorSet family ground h T) (T := T)
      (hJ := nearAnchorSet_subset_erase family ground h T)
      (hT := nearAnchorSet_forall family ground h T)

theorem mul_card_nearAnchorSet_le_sum_erase_card {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (h : α) (T : ℕ)
    (h_ground : ∀ S ∈ family, S ⊆ ground) :
    T * (nearAnchorSet family ground h T).card ≤
      (family.filter (fun S => h ∈ S)).sum (fun S => (S.erase h).card) := by
  classical
  have h1 :
      T * (nearAnchorSet family ground h T).card ≤
        (ground.erase h).sum (fun j => coDegree family h j) :=
    mul_card_nearAnchorSet_le_sum_coDegree (family := family) (ground := ground) (h := h) (T := T)
  have h2 :
      (ground.erase h).sum (fun j => coDegree family h j) =
        (family.filter (fun S => h ∈ S)).sum (fun S => (S.erase h).card) :=
    sum_coDegree_anchor_eq_sum_erase_card (family := family) (ground := ground) (h := h)
      (h_ground := h_ground)
  exact h1.trans_eq h2

/--
Upper bound on the anchored co-degree sum via a trivial size bound:
each set `S` containing `h` contributes at most `|(ground \\ {h})|` other coordinates.
-/
theorem sum_erase_card_le_card_mul_erase_ground {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (h : α)
    (h_ground : ∀ S ∈ family, S ⊆ ground) :
    (family.filter (fun S => h ∈ S)).sum (fun S => (S.erase h).card) ≤
      (family.filter (fun S => h ∈ S)).card * (ground.erase h).card := by
  classical
  set s : Finset (Finset α) := family.filter (fun S => h ∈ S)
  have hpoint : ∀ S ∈ s, (S.erase h).card ≤ (ground.erase h).card := by
    intro S hS
    have hSfam : S ∈ family := (Finset.mem_filter.mp hS).1
    have hSsub : S ⊆ ground := h_ground S hSfam
    have hSub : S.erase h ⊆ ground.erase h := by
      intro x hx
      have hx' := Finset.mem_erase.mp hx
      exact Finset.mem_erase.mpr ⟨hx'.1, hSsub hx'.2⟩
    exact Finset.card_le_card hSub
  calc
    s.sum (fun S => (S.erase h).card) ≤ s.sum (fun _ => (ground.erase h).card) := by
      refine Finset.sum_le_sum ?_
      intro S hS
      exact hpoint S hS
    _ = s.card * (ground.erase h).card := by
      simp [Nat.mul_comm]

theorem mul_card_nearAnchorSet_le_coordDegree_mul_erase_ground {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (h : α) (T : ℕ)
    (h_ground : ∀ S ∈ family, S ⊆ ground) :
    T * (nearAnchorSet family ground h T).card ≤
      coordDegree family h * (ground.erase h).card := by
  classical
  have hlow :
      T * (nearAnchorSet family ground h T).card ≤
        (family.filter (fun S => h ∈ S)).sum (fun S => (S.erase h).card) :=
    mul_card_nearAnchorSet_le_sum_erase_card (family := family) (ground := ground) (h := h) (T := T)
      (h_ground := h_ground)
  have hhigh :
      (family.filter (fun S => h ∈ S)).sum (fun S => (S.erase h).card) ≤
        coordDegree family h * (ground.erase h).card := by
    have := sum_erase_card_le_card_mul_erase_ground (family := family) (ground := ground) (h := h)
      (h_ground := h_ground)
    -- `coordDegree` is the filter card by definition.
    simpa [coordDegree] using this
  exact hlow.trans hhigh

theorem supportMaxCoDegreePairs_erase_subset_nearAnchorSet_of_anchor {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {h : α}
    (hanch : maxPairsAnchoredAt family ground h) :
    (supportMaxCoDegreePairs family ground).erase h ⊆
      nearAnchorSet family ground h (maxCoDegree family ground) := by
  classical
  intro j hj
  have hj_ne : j ≠ h := (Finset.mem_erase.mp hj).1
  have hj_supp : j ∈ supportMaxCoDegreePairs family ground := (Finset.mem_erase.mp hj).2
  have hj_ground : j ∈ ground := supportMaxCoDegreePairs_subset_ground family ground hj_supp
  have hj_ground_erase : j ∈ ground.erase h := Finset.mem_erase.mpr ⟨hj_ne, hj_ground⟩
  have hjp' :=
    (mem_supportMaxCoDegreePairs_iff (family := family) (ground := ground) (x := j)).1 hj_supp
  rcases hjp' with ⟨p, hp, hjp⟩
  have hp_max : coDegree family p.1 p.2 = maxCoDegree family ground := (Finset.mem_filter.mp hp).2
  have hp_anchor : p.1 = h ∨ p.2 = h := hanch.2 p hp
  have hT : maxCoDegree family ground ≤ coDegree family h j := by
    rcases hjp with rfl | rfl
    · -- j = p.1
      rcases hp_anchor with hp1 | hp2
      · exact False.elim (hj_ne hp1)
      · -- p.2 = h, so coDegree family h p.1 = maxCoDegree by symmetry
        have : coDegree family h p.1 = maxCoDegree family ground := by
          -- hp_max gives coDegree family p.1 p.2 = maxCoDegree
          -- rewrite p.2 = h and commute
          simpa [hp2, coDegree_comm] using hp_max
        exact le_of_eq this.symm
    · -- j = p.2
      rcases hp_anchor with hp1 | hp2
      · -- p.1 = h, so hp_max already has the right orientation
        have : coDegree family h p.2 = maxCoDegree family ground := by
          simpa [hp1] using hp_max
        exact le_of_eq this.symm
      · exact False.elim (hj_ne hp2)
  exact Finset.mem_filter.mpr ⟨hj_ground_erase, hT⟩

theorem mul_card_supportMaxCoDegreePairs_erase_le_coordDegree_mul_erase_ground
    {α : Type*} [DecidableEq α] {family : Finset (Finset α)} {ground : Finset α} {h : α}
    (hanch : maxPairsAnchoredAt family ground h)
    (h_ground : ∀ S ∈ family, S ⊆ ground) :
    maxCoDegree family ground * ((supportMaxCoDegreePairs family ground).erase h).card ≤
      coordDegree family h * (ground.erase h).card := by
  classical
  have hsubset :
      (supportMaxCoDegreePairs family ground).erase h ⊆
        nearAnchorSet family ground h (maxCoDegree family ground) :=
    supportMaxCoDegreePairs_erase_subset_nearAnchorSet_of_anchor
      (family := family) (ground := ground) (h := h) hanch
  have hcard :
      ((supportMaxCoDegreePairs family ground).erase h).card ≤
        (nearAnchorSet family ground h (maxCoDegree family ground)).card :=
    Finset.card_le_card hsubset
  have hmul :
      maxCoDegree family ground * ((supportMaxCoDegreePairs family ground).erase h).card ≤
        maxCoDegree family ground *
          (nearAnchorSet family ground h (maxCoDegree family ground)).card :=
    Nat.mul_le_mul_left _ hcard
  have hnear :
      maxCoDegree family ground *
          (nearAnchorSet family ground h (maxCoDegree family ground)).card ≤
        coordDegree family h * (ground.erase h).card :=
    mul_card_nearAnchorSet_le_coordDegree_mul_erase_ground (family := family) (ground := ground)
      (h := h) (T := maxCoDegree family ground) (h_ground := h_ground)
  exact hmul.trans hnear

lemma ObstructionO1a_of_anchor {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {h : α}
    (hanch : maxPairsAnchoredAt family ground h) :
    ObstructionO1a family ground := by
  exact ⟨h, hanch⟩

lemma ObstructionO1_of_anchor {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {h : α}
    (hanch : maxPairsAnchoredAt family ground h) :
    ObstructionO1 family ground := by
  exact Or.inl (ObstructionO1a_of_anchor (family := family) (ground := ground) (h := h) hanch)

-- ============================================================================
-- Obstruction O₂ scaffold (core-slice decomposition)
--
-- This is a light “mechanics” layer: definitions + partition cardinalities.
-- The hypergraph constraints and |Y| bounds are developed in analysis and will
-- be formalized later if needed.
-- ============================================================================

/-- O₂ core slice: sets in `family` that contain `h`. -/
def coreSliceContains {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (h : α) : Finset (Finset α) :=
  family.filter (fun S => h ∈ S)

/-- O₂ core complement slice: sets in `family` that avoid `h`. -/
def coreSliceAvoid {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (h : α) : Finset (Finset α) :=
  family.filter (fun S => h ∉ S)

/-- O₂ projection A' = {S \ {h} : S ∈ coreSliceContains}. -/
def coreSliceProj {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (h : α) : Finset (Finset α) :=
  (coreSliceContains family h).image (fun S => S.erase h)

/-- O₂ overlap X = coreSliceAvoid ∩ coreSliceProj. -/
def coreOverlap {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (h : α) : Finset (Finset α) :=
  coreSliceAvoid family h ∩ coreSliceProj family h

/-- O₂ remainder Y = coreSliceAvoid \ coreSliceProj. -/
def coreRemainder {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (h : α) : Finset (Finset α) :=
  coreSliceAvoid family h \ coreSliceProj family h

/-!
Domain for Option 2 (witness-lift) counting in the O₁a leaf:
`S` is in the `h=0` slice, and `liftAt S h ∉ family` so maximality forces a blocking witness.
-/
def o1aWitnessLiftDom {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (h : α) : Finset (Finset α) :=
  (coreSliceAvoid family h).filter (fun S => liftAt S h ∉ family)

/--
Certificate domain for Option 2: the witness-lift domain, excluding the chain-case and
singleton-core branches (kept as residual buckets for now).
-/
noncomputable def o1aWitnessLiftDomWL {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (h : α) : Finset (Finset α) :=
by
  classical
  exact
    (o1aWitnessLiftDom family h).filter
      (fun S => ¬ ChainExtension family S h ∧
        ¬ WitnessHasHSingletonCore family (liftAt S h) h)

-- ============================================================================
-- Type II bridge scaffold (v0)
--
-- This is a deliberately minimal statement that makes the “Type I fails everywhere”
-- regime into a shared hypothesis and partitions it into “O₁a or residual”.
-- ============================================================================

/-- Residual Type II bucket (v0): Type I fails everywhere but O₁a does not hold. -/
def ResidualV0 {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (A : ℕ) : Prop :=
  hiFail family ground A ∧ ¬ ObstructionO1a family ground

/-- Type II bridge (v0, stub): `HI_FAIL_A(F)` implies `O₁a(F)` or falls into a residual bucket. -/
theorem typeII_bridge_v0 {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A : ℕ}
    (hfail : hiFail family ground A) :
    ObstructionO1a family ground ∨ ResidualV0 family ground A := by
  classical
  by_cases hO1 : ObstructionO1a family ground
  · exact Or.inl hO1
  · exact Or.inr ⟨hfail, hO1⟩

/--
Chain-extension bucket (v1, auxiliary):
there exist `h ∈ ground` and `S ∈ family` that admit a strict `h=0` chain extension.

This is treated as a separate residual leaf until we prove it collapses to Type I or is impossible
under the global Type II regime (`hiFail`).
-/
def ObstructionChainExtension {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) : Prop :=
  ∃ h ∈ ground, ∃ S ∈ family, ChainExtension family S h

/--
Residual Type II bucket (v1):
either the old residual (`hiFail ∧ ¬O₁a`) or a chain-extension witness.

This keeps the bridge statement stable while we split the downstream O₁a proof into two leaves:
the “upgrade-to-`WmaxAt`” leaf and the chain-extension leaf.
-/
def ResidualV1 {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (A : ℕ) : Prop :=
  ResidualV0 family ground A ∨ ObstructionChainExtension family ground

/--
Thin max-coDegree bucket (v2, auxiliary):
the maximum pair co-degree is at most `1`, i.e. every pair slice has size ≤ 1.

We route this to a residual bucket for now (decision A), and later aim to prove it is impossible
under the intended upgrade regime (`hiFail` + maximality + sunflower-free).
-/
def ObstructionThinMaxCoDegree {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) : Prop :=
  maxCoDegree family ground ≤ 1

/--
Residual Type II bucket (v2):
either the v1 residual, or the thin max-coDegree case.
-/
def ResidualV2 {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (A : ℕ) : Prop :=
  ResidualV1 family ground A ∨ ObstructionThinMaxCoDegree family ground

/--
Singleton-core bucket (v3, auxiliary):
there exist `h ∈ ground` and `S ∈ family` in the `h=0` slice such that
`liftAt S h` admits a `WitnessHasH` certificate whose core is supported on `{h}`.

We route this to a residual bucket for now. Later cleanup is to show it is impossible
under the intended O₁a upgrade regime (or collapses to Type I / chain).
-/
def ObstructionSingletonCore {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) : Prop :=
  ∃ h ∈ ground, ∃ S ∈ family, h ∉ S ∧
    WitnessHasH family (liftAt S h) h ∧
    ¬ WitnessHasHNonSingletonCore family (liftAt S h) h

/--
Residual Type II bucket (v3):
either the v2 residual, or the singleton-core case.
-/
def ResidualV3 {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (A : ℕ) : Prop :=
  ResidualV2 family ground A ∨ ObstructionSingletonCore family ground

/--
Core-misses-`Nmax` bucket (v4, auxiliary):
there exist `h ∈ ground` and `S ∈ family` in the `h=0` slice such that
`liftAt S h` admits a non-singleton-core `WitnessHasH` certificate,
but `S` contains no max-neighbor of `h` (so the `WmaxAt(h,j)` upgrade cannot fire).

This is a staging residual: the intended cleanup is to show it is impossible under the intended
O₁a upgrade regime, or to replace `Nmax` by a near-max anchored reservoir.
-/
def ObstructionCoreMissesNmax {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) : Prop :=
  ∃ h ∈ ground, ∃ S ∈ family, h ∉ S ∧
    WitnessHasHNonSingletonCore family (liftAt S h) h ∧
    (S ∩ Nmax family ground h) = ∅

/--
Core-misses-`Nnear` bucket (staging, v0):
the same as `ObstructionCoreMissesNmax`, but using the near-max neighbor set `Nnear(h,s)`.

This is the post-`s=2` fallback: if `coreHitsNnear` does not close for small slack, route here
and record why. After the `s=1`/`s=2` time-box misses, the intended next move is Option 2
(witness-lift certificates), not further widening `s`.
-/
def ObstructionCoreMissesNnear {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (s : ℕ) : Prop :=
  ∃ h ∈ ground, ∃ S ∈ family, h ∉ S ∧
    WitnessHasHNonSingletonCore family (liftAt S h) h ∧
    (S ∩ Nnear family ground s h) = ∅

/--
Residual Type II bucket (v4):
either the v3 residual, or the core-misses-`Nmax` case.
-/
def ResidualV4 {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (A : ℕ) : Prop :=
  ResidualV3 family ground A ∨ ObstructionCoreMissesNmax family ground

/-- Type II bridge (v1, stub): `HI_FAIL_A(F)` implies `O₁a(F)` or falls into `ResidualV1`. -/
theorem typeII_bridge_v1 {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A : ℕ}
    (hfail : hiFail family ground A) :
    ObstructionO1a family ground ∨ ResidualV1 family ground A := by
  classical
  by_cases hO1 : ObstructionO1a family ground
  · exact Or.inl hO1
  · exact Or.inr (Or.inl ⟨hfail, hO1⟩)

/-- Type II bridge (v2, stub): `HI_FAIL_A(F)` implies `O₁a(F)` or falls into `ResidualV2`. -/
theorem typeII_bridge_v2 {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A : ℕ}
    (hfail : hiFail family ground A) :
    ObstructionO1a family ground ∨ ResidualV2 family ground A := by
  classical
  have h := typeII_bridge_v1 (family := family) (ground := ground) (A := A) hfail
  rcases h with hO1 | hRes
  · exact Or.inl hO1
  · exact Or.inr (Or.inl hRes)

/-- Type II bridge (v3, stub): `HI_FAIL_A(F)` implies `O₁a(F)` or falls into `ResidualV3`. -/
theorem typeII_bridge_v3 {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A : ℕ}
    (hfail : hiFail family ground A) :
    ObstructionO1a family ground ∨ ResidualV3 family ground A := by
  classical
  have h := typeII_bridge_v2 (family := family) (ground := ground) (A := A) hfail
  rcases h with hO1 | hRes
  · exact Or.inl hO1
  · exact Or.inr (Or.inl hRes)

/-- Type II bridge (v4, stub): `HI_FAIL_A(F)` implies `O₁a(F)` or falls into `ResidualV4`. -/
theorem typeII_bridge_v4 {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A : ℕ}
    (hfail : hiFail family ground A) :
    ObstructionO1a family ground ∨ ResidualV4 family ground A := by
  classical
  have h := typeII_bridge_v3 (family := family) (ground := ground) (A := A) hfail
  rcases h with hO1 | hRes
  · exact Or.inl hO1
  · exact Or.inr (Or.inl hRes)

-- ============================================================================
-- O₁a upgrade leaf: pressure bundle (v0)
-- ============================================================================

/--
Bundle the hypotheses we expect to use in the O₁a upgrade leaf.

`A` is the Type-I threshold (Lean's parameter for `HI_FAIL_A`).

This keeps the upgrade leaf honest: if we later find `hiFail` isn't needed,
we can remove it cleanly without changing the obstruction definition.
-/
def O1aUpgradeRegime {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (A : ℕ) (h : α) : Prop :=
  family ⊆ ground.powerset ∧
  IsSunflowerFree family 3 ∧
  (∀ T ⊆ ground, T ∉ family → ¬ IsSunflowerFree (insert T family) 3) ∧
  hiFail family ground A ∧
  maxPairsAnchoredAt family ground h

/--
Reduction lemma for the hard branch (`cert.h ∉ S`) in the O₁a witness-lift domain.

For a fixed key `k = (h,j,A,B,core)` and `S ∈ o1aWitnessLiftDomWL family h₀`,
any certificate with key `k` and `h ∉ S` forces:
- the trace of `S` on `A ∪ B` is exactly `core.erase h` (so the remaining freedom is in
  `X := ground \\ (A ∪ B)`), and
- every one-step `h₀`-avoiding extension by an element of `X` is missing from `family` and
  is blocked by two sets in `family` (by maximality).

This is the handoff point for the collision→sunflower multiplicity argument.
-/
theorem wlcert_hNotMem_reduction_o1aDomWL {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h0 : α}
    (hreg : O1aUpgradeRegime family ground A0 h0)
    {k : WLcertKey α} {S : Finset α}
    (hSdom : S ∈ o1aWitnessLiftDomWL family h0)
    (hcert : ∃ cert : WLcert family S, WLcert.key cert = k ∧ cert.h ∉ S) :
    let kh : α := k.1
    let kA : Finset α := k.2.2.1
    let kB : Finset α := k.2.2.2.1
    let kcore : Finset α := k.2.2.2.2
    let X : Finset α := ground \ (kA ∪ kB)
    (kA ∩ S = kcore.erase kh) ∧
      (kB ∩ S = kcore.erase kh) ∧
      (S ∩ (kA ∪ kB) = kcore.erase kh) ∧
      (S \ (kA ∪ kB)) ⊆ X ∧
      (S = (kcore.erase kh) ∪ (S \ (kA ∪ kB))) ∧
      (∀ x, x ∈ X → x ∉ S → x ≠ h0 →
        (S ∪ ({x} : Finset α)) ∉ family ∧
          BlockedByTwo family (S ∪ ({x} : Finset α))) := by
  classical
  rcases hreg with ⟨hground, hfree, hmax, _hfail, _hanch⟩
  -- Unpack `S ∈ domWL` to get family membership and `¬ChainExtension`.
  have hS' :
      S ∈
        (o1aWitnessLiftDom family h0).filter
          (fun S => ¬ ChainExtension family S h0 ∧
            ¬ WitnessHasHSingletonCore family (liftAt S h0) h0) := by
    simpa [o1aWitnessLiftDomWL] using hSdom
  have hS0 : S ∈ o1aWitnessLiftDom family h0 := (Finset.mem_filter.mp hS').1
  have hno : ¬ ChainExtension family S h0 ∧
      ¬ WitnessHasHSingletonCore family (liftAt S h0) h0 :=
    (Finset.mem_filter.mp hS').2
  have hnoChain : ¬ ChainExtension family S h0 := hno.1
  have hSAvoid : S ∈ coreSliceAvoid family h0 := (Finset.mem_filter.mp hS0).1
  have hSfam : S ∈ family := (Finset.mem_filter.mp hSAvoid).1
  have hh0nS : h0 ∉ S := (Finset.mem_filter.mp hSAvoid).2
  have hSsub : S ⊆ ground := Finset.mem_powerset.mp (hground hSfam)
  -- Unpack the certificate and normalize to component form.
  rcases hcert with ⟨cert, hk, hhnS⟩
  rcases k with ⟨kh, kj, kA, kB, kcore⟩
  -- Rewrite certificate fields using `hk`.
  have hk_h : cert.h = kh := by
    have : (cert.h, cert.j, cert.A, cert.B, cert.core) = (kh, kj, kA, kB, kcore) := by
      simpa [WLcert.key] using hk
    exact congrArg (fun t => t.1) this
  have hk_A : cert.A = kA := by
    have : (cert.h, cert.j, cert.A, cert.B, cert.core) = (kh, kj, kA, kB, kcore) := by
      simpa [WLcert.key] using hk
    exact congrArg (fun t => t.2.2.1) this
  have hk_B : cert.B = kB := by
    have : (cert.h, cert.j, cert.A, cert.B, cert.core) = (kh, kj, kA, kB, kcore) := by
      simpa [WLcert.key] using hk
    exact congrArg (fun t => t.2.2.2.1) this
  have hk_core : cert.core = kcore := by
    have : (cert.h, cert.j, cert.A, cert.B, cert.core) = (kh, kj, kA, kB, kcore) := by
      simpa [WLcert.key] using hk
    exact congrArg (fun t => t.2.2.2.2) this
  -- Trace equalities on `A` and `B`.
  have hA : kA ∩ S = kcore.erase kh := by
    subst hk_h
    subst hk_A
    subst hk_core
    simpa using wlcert_inter_left_eq_core_erase_h (cert := cert) hhnS
  have hB : kB ∩ S = kcore.erase kh := by
    subst hk_h
    subst hk_B
    subst hk_core
    simpa using wlcert_inter_right_eq_core_erase_h (cert := cert) hhnS
  -- Assemble the completion decomposition on `X = ground \\ (A ∪ B)`.
  have hAB : S ∩ (kA ∪ kB) = kcore.erase kh := by
    have : S ∩ (kA ∪ kB) = (S ∩ kA) ∪ (S ∩ kB) := by
      simpa using (Finset.inter_union_distrib_left S kA kB)
    calc
      S ∩ (kA ∪ kB) = (S ∩ kA) ∪ (S ∩ kB) := this
      _ = (kA ∩ S) ∪ (kB ∩ S) := by
            ext x
            simp [Finset.inter_comm]
      _ = (kcore.erase kh) ∪ (kcore.erase kh) := by simp [hA, hB]
      _ = kcore.erase kh := by simp
  have hTsub : (S \ (kA ∪ kB)) ⊆ (ground \ (kA ∪ kB)) := by
    intro x hx
    have hxS : x ∈ S := (Finset.mem_sdiff.mp hx).1
    have hxg : x ∈ ground := hSsub hxS
    exact Finset.mem_sdiff.mpr ⟨hxg, (Finset.mem_sdiff.mp hx).2⟩
  have hdecomp : S = (kcore.erase kh) ∪ (S \ (kA ∪ kB)) := by
    have : S = (S ∩ (kA ∪ kB)) ∪ (S \ (kA ∪ kB)) := by
      -- `S = (S \ T) ∪ (S ∩ T)` (and commute the union).
      simpa [Finset.union_comm, Finset.union_left_comm, Finset.union_assoc] using
        (Finset.sdiff_union_inter S (kA ∪ kB)).symm
    simpa [hAB] using this
  have hext :
      ∀ x, x ∈ (ground \ (kA ∪ kB)) → x ∉ S → x ≠ h0 →
        (S ∪ ({x} : Finset α)) ∉ family ∧
          BlockedByTwo family (S ∪ ({x} : Finset α)) := by
    intro x hxX hxnot hxne0
    have hxg : x ∈ ground := (Finset.mem_sdiff.mp hxX).1
    have hTsub : S ∪ ({x} : Finset α) ⊆ ground := by
      intro y hy
      rcases Finset.mem_union.mp hy with hy | hy
      · exact hSsub hy
      · have : y = x := by simpa using (Finset.mem_singleton.mp hy)
        exact this ▸ hxg
    have hTnot : (S ∪ ({x} : Finset α)) ∉ family := by
      intro hTin
      have hss : S ⊂ (S ∪ ({x} : Finset α)) := by
        have hsub : S ⊆ S ∪ ({x} : Finset α) := by
          intro y hy
          exact Finset.mem_union.mpr (Or.inl hy)
        refine (Finset.ssubset_iff_of_subset hsub).2 ?_
        refine ⟨x, Finset.mem_union.mpr (Or.inr (by simp)), ?_⟩
        exact hxnot
      exact hnoChain ⟨S ∪ ({x} : Finset α), hTin, hss, by
        simpa [Finset.mem_union, hh0nS] using hxne0.symm⟩
    have hnotSF : ¬ IsSunflowerFree (insert (S ∪ ({x} : Finset α)) family) 3 :=
      hmax (S ∪ ({x} : Finset α)) hTsub hTnot
    refine ⟨hTnot, ?_⟩
    exact
      blockedByTwo_of_not_sunflowerFree_insert
        (family := family) (T := S ∪ ({x} : Finset α)) hfree hTnot hnotSF
  refine ⟨hA, hB, hAB, ?_, hdecomp, ?_⟩
  · simpa using hTsub
  · simpa using hext

/-- In a blocking witness for `S ∪ {x}`, either the core contains `x` or the witness uses `S`. -/
theorem blockedByTwo_union_singleton_core_mem_or_uses_S {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {S : Finset α} {x : α}
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked : BlockedByTwo family (S ∪ ({x} : Finset α))) :
    ∃ A ∈ family, ∃ B ∈ family, A ≠ B ∧
      ∃ core : Finset α, A ∩ B = core ∧ A ∩ (S ∪ ({x} : Finset α)) = core ∧
        B ∩ (S ∪ ({x} : Finset α)) = core ∧ (x ∈ core ∨ A = S ∨ B = S) := by
  classical
  rcases hblocked with ⟨A, hA, B, hB, hAB, core, hcoreAB, hcoreAT, hcoreBT⟩
  by_cases hxcore : x ∈ core
  · refine ⟨A, hA, B, hB, hAB, core, hcoreAB, hcoreAT, hcoreBT, Or.inl hxcore⟩
  · have hxT : x ∈ S ∪ ({x} : Finset α) := by simp
    have hxAiff :
        (x ∈ A ↔ x ∈ core) :=
      mem_left_iff_mem_core_of_mem_T_of_inter_eq (A := A) (T := S ∪ ({x} : Finset α))
        (core := core) hxT hcoreAT
    have hxBiff :
        (x ∈ B ↔ x ∈ core) :=
      mem_left_iff_mem_core_of_mem_T_of_inter_eq (A := B) (T := S ∪ ({x} : Finset α))
        (core := core) hxT hcoreBT
    have hxA : x ∉ A := by
      intro hxA
      exact hxcore (hxAiff.1 hxA)
    have hxB : x ∉ B := by
      intro hxB
      exact hxcore (hxBiff.1 hxB)
    have hAS : A ∩ S = core := by
      have hEq := (Finset.inter_union_distrib_left A S ({x} : Finset α))
      have hcoreAT' := hcoreAT
      rw [hEq] at hcoreAT'
      have hxInter : A ∩ ({x} : Finset α) = ∅ := by
        simp [hxA]
      simpa [hxInter] using hcoreAT'
    have hBS : B ∩ S = core := by
      have hEq := (Finset.inter_union_distrib_left B S ({x} : Finset α))
      have hcoreBT' := hcoreBT
      rw [hEq] at hcoreBT'
      have hxInter : B ∩ ({x} : Finset α) = ∅ := by
        simp [hxB]
      simpa [hxInter] using hcoreBT'
    by_cases hAS_eq : A = S
    · refine ⟨A, hA, B, hB, hAB, core, hcoreAB, hcoreAT, hcoreBT, ?_⟩
      exact Or.inr (Or.inl hAS_eq)
    by_cases hBS_eq : B = S
    · refine ⟨A, hA, B, hB, hAB, core, hcoreAB, hcoreAT, hcoreBT, ?_⟩
      exact Or.inr (Or.inr hBS_eq)
    have hsun : IsSunflower ({A, B, S} : Finset (Finset α)) 3 := by
      refine ⟨?_, ?_⟩
      · have hBnot : B ∉ ({S} : Finset (Finset α)) := by
          simp [hBS_eq]
        have hAnot : A ∉ insert B ({S} : Finset (Finset α)) := by
          simp [hAB, hAS_eq]
        have hcardB : (insert B ({S} : Finset (Finset α))).card = 2 := by
          simp [Finset.card_insert_of_notMem, hBnot]
        have hcard : (insert A (insert B ({S} : Finset (Finset α)))).card = 3 := by
          calc
            (insert A (insert B ({S} : Finset (Finset α)))).card =
                (insert B ({S} : Finset (Finset α))).card + 1 := by
                  simp [Finset.card_insert_of_notMem, hAnot]
            _ = 3 := by
                  simp [hcardB]
        simpa using hcard
      · refine ⟨core, ?_⟩
        intro X Y hX hY hXY
        have hX' : X = A ∨ X = B ∨ X = S := by
          simpa using (Finset.mem_insert.mp hX)
        have hY' : Y = A ∨ Y = B ∨ Y = S := by
          simpa using (Finset.mem_insert.mp hY)
        rcases hX' with rfl | hX'
        · rcases hY' with rfl | hY'
          · exact False.elim (hXY rfl)
          · rcases hY' with rfl | rfl
            · exact hcoreAB
            · simpa [Finset.inter_comm] using hAS
        · rcases hX' with rfl | rfl
          · rcases hY' with rfl | hY'
            · simpa [Finset.inter_comm] using hcoreAB
            · rcases hY' with rfl | rfl
              · exact False.elim (hXY rfl)
              · simpa [Finset.inter_comm] using hBS
          · rcases hY' with rfl | hY'
            · simpa [Finset.inter_comm] using hAS
            · rcases hY' with rfl | rfl
              · simpa [Finset.inter_comm] using hBS
              · exact False.elim (hXY rfl)
    have hsub : ({A, B, S} : Finset (Finset α)) ⊆ family := by
      intro X hX
      have hX' : X = A ∨ X = B ∨ X = S := by
        simpa using (Finset.mem_insert.mp hX)
      rcases hX' with rfl | hX'
      · exact hA
      rcases hX' with rfl | rfl
      · exact hB
      · exact hS
    exact False.elim (hfree ({A, B, S} : Finset (Finset α)) hsub hsun)

/-- A chosen blocking witness for `S ∪ {x}` tagged by the disjunction `x ∈ core ∨ uses S`. -/
structure BlockedUnionWitness {α : Type uWL} [DecidableEq α]
    (family : Finset (Finset α)) (S : Finset α) (x : α) : Type uWL where
  (A : Finset α)
  (hA : A ∈ family)
  (B : Finset α)
  (hB : B ∈ family)
  (hneAB : A ≠ B)
  (core : Finset α)
  (hcoreAB : A ∩ B = core)
  (hcoreAT : A ∩ (S ∪ ({x} : Finset α)) = core)
  (hcoreBT : B ∩ (S ∪ ({x} : Finset α)) = core)
  (htag : x ∈ core ∨ A = S ∨ B = S)

noncomputable def chooseBlockedUnionWitness {α : Type uWL} [DecidableEq α]
    {family : Finset (Finset α)} {S : Finset α} {x : α}
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked : BlockedByTwo family (S ∪ ({x} : Finset α))) :
    BlockedUnionWitness family S x := by
  classical
  refine Classical.choice ?_
  rcases
      blockedByTwo_union_singleton_core_mem_or_uses_S
        (family := family) (S := S) (x := x) hS hfree hblocked with
    ⟨A, hA, B, hB, hAB, core, hcoreAB, hcoreAT, hcoreBT, htag⟩
  exact ⟨⟨A, hA, B, hB, hAB, core, hcoreAB, hcoreAT, hcoreBT, htag⟩⟩

noncomputable def badXSet {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} (S X : Finset α) (h0 : α)
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α))) :
    Finset α := by
  classical
  exact
    X.filter (fun x =>
      if hxX : x ∈ X then
        if hxnot : x ∉ S then
          if hxne0 : x ≠ h0 then
            let w :=
              chooseBlockedUnionWitness (family := family) (S := S) (x := x) hS hfree
                (hblocked x hxX hxnot hxne0)
            w.A = S ∨ w.B = S
          else False
        else False
      else False)

noncomputable def goodXSet {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} (S X : Finset α) (h0 : α)
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α))) :
    Finset α := by
  classical
  exact
    X.filter (fun x =>
      if hxX : x ∈ X then
        if hxnot : x ∉ S then
          if hxne0 : x ≠ h0 then
            let w :=
              chooseBlockedUnionWitness (family := family) (S := S) (x := x) hS hfree
                (hblocked x hxX hxnot hxne0)
            x ∈ w.core
          else False
        else False
      else False)

theorem core_erase_subset_S_of_blockedUnionWitness {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {S : Finset α} {x : α}
    (w : BlockedUnionWitness family S x) :
    (w.core.erase x) ⊆ S := by
  classical
  intro z hz
  have hzw : z ∈ w.core := (Finset.mem_erase.mp hz).2
  have hzSx : z ∈ S ∪ ({x} : Finset α) := by
    have : z ∈ w.A ∩ (S ∪ ({x} : Finset α)) := by
      -- rewrite membership along `w.hcoreAT`
      have hz'' : z ∈ w.core := hzw
      rw [← w.hcoreAT] at hz''
      exact hz''
    exact (Finset.mem_inter.mp this).2
  rcases Finset.mem_union.mp hzSx with hzS | hzx
  · exact hzS
  · have hzEq : z = x := by simpa using (Finset.mem_singleton.mp hzx)
    have : z ≠ x := (Finset.mem_erase.mp hz).1
    exact False.elim (this hzEq)

theorem core_eq_inter_left_union_singleton_of_blockedUnionWitness_of_mem_core
    {α : Type*} [DecidableEq α] {family : Finset (Finset α)} {S : Finset α} {x : α}
    (w : BlockedUnionWitness family S x) (hxcore : x ∈ w.core) :
    w.core = (w.A ∩ S) ∪ ({x} : Finset α) := by
  classical
  have hx' : x ∈ w.A ∩ (S ∪ ({x} : Finset α)) := by
    have hx'' : x ∈ w.core := hxcore
    -- rewrite membership along `w.hcoreAT` (in reverse)
    have hx''' := hx''
    rw [← w.hcoreAT] at hx'''
    exact hx'''
  have hAin : x ∈ w.A := (Finset.mem_inter.mp hx').1
  have hdistrib := Finset.inter_union_distrib_left w.A S ({x} : Finset α)
  have hAx : w.A ∩ ({x} : Finset α) = ({x} : Finset α) := by
    ext y
    by_cases hy : y = x
    · subst hy
      simp [hAin]
    · simp [hy]
  calc
    w.core = w.A ∩ (S ∪ ({x} : Finset α)) := by
      simpa using w.hcoreAT.symm
    _ = (w.A ∩ S) ∪ (w.A ∩ ({x} : Finset α)) := by
      simpa using hdistrib
    _ = (w.A ∩ S) ∪ ({x} : Finset α) := by simp [hAx]

theorem inter_left_eq_core_erase_of_blockedUnionWitness_of_mem_core_of_not_mem_S
    {α : Type*} [DecidableEq α] {family : Finset (Finset α)} {S : Finset α} {x : α}
    (w : BlockedUnionWitness family S x) (hxnot : x ∉ S) :
    w.A ∩ S = w.core.erase x := by
  classical
  ext y
  by_cases hyx : y = x
  · -- `y = x`: both sides are false since `x ∉ S` and `x ∉ erase x _`
    simp [hyx, hxnot]
  · constructor
    · intro hyAS
      have hyA : y ∈ w.A := (Finset.mem_inter.mp hyAS).1
      have hyS : y ∈ S := (Finset.mem_inter.mp hyAS).2
      have hyT : y ∈ S ∪ ({x} : Finset α) := Finset.mem_union.mpr (Or.inl hyS)
      have hyAT : y ∈ w.A ∩ (S ∪ ({x} : Finset α)) := Finset.mem_inter.mpr ⟨hyA, hyT⟩
      have hycore : y ∈ w.core := by
        -- rewrite membership along `w.hcoreAT`
        have hy' : y ∈ w.A ∩ (S ∪ ({x} : Finset α)) := hyAT
        have hy'' := hy'
        rw [w.hcoreAT] at hy''
        exact hy''
      exact Finset.mem_erase.mpr ⟨hyx, hycore⟩
    · intro hycoreErase
      have hycore : y ∈ w.core := (Finset.mem_erase.mp hycoreErase).2
      have hyAT : y ∈ w.A ∩ (S ∪ ({x} : Finset α)) := by
        -- rewrite membership using `w.hcoreAT` in reverse
        have hy' : y ∈ w.core := hycore
        have hy'' := hy'
        rw [← w.hcoreAT] at hy''
        exact hy''
      have hyA : y ∈ w.A := (Finset.mem_inter.mp hyAT).1
      have hyT : y ∈ S ∪ ({x} : Finset α) := (Finset.mem_inter.mp hyAT).2
      have hyS : y ∈ S := by
        rcases Finset.mem_union.mp hyT with hyS | hyx'
        · exact hyS
        · have : y = x := by simpa using (Finset.mem_singleton.mp hyx')
          exact False.elim (hyx this)
      exact Finset.mem_inter.mpr ⟨hyA, hyS⟩

theorem inter_right_eq_core_erase_of_blockedUnionWitness_of_mem_core_of_not_mem_S
    {α : Type*} [DecidableEq α] {family : Finset (Finset α)} {S : Finset α} {x : α}
    (w : BlockedUnionWitness family S x) (hxnot : x ∉ S) :
    w.B ∩ S = w.core.erase x := by
  classical
  ext y
  by_cases hyx : y = x
  · -- `y = x`: both sides are false since `x ∉ S` and `x ∉ erase x _`
    simp [hyx, hxnot]
  · constructor
    · intro hyBS
      have hyB : y ∈ w.B := (Finset.mem_inter.mp hyBS).1
      have hyS : y ∈ S := (Finset.mem_inter.mp hyBS).2
      have hyT : y ∈ S ∪ ({x} : Finset α) := Finset.mem_union.mpr (Or.inl hyS)
      have hyBT : y ∈ w.B ∩ (S ∪ ({x} : Finset α)) := Finset.mem_inter.mpr ⟨hyB, hyT⟩
      have hycore : y ∈ w.core := by
        have hy' : y ∈ w.B ∩ (S ∪ ({x} : Finset α)) := hyBT
        have hy'' := hy'
        rw [w.hcoreBT] at hy''
        exact hy''
      exact Finset.mem_erase.mpr ⟨hyx, hycore⟩
    · intro hycoreErase
      have hycore : y ∈ w.core := (Finset.mem_erase.mp hycoreErase).2
      have hyBT : y ∈ w.B ∩ (S ∪ ({x} : Finset α)) := by
        have hy' : y ∈ w.core := hycore
        have hy'' := hy'
        rw [← w.hcoreBT] at hy''
        exact hy''
      have hyB : y ∈ w.B := (Finset.mem_inter.mp hyBT).1
      have hyT : y ∈ S ∪ ({x} : Finset α) := (Finset.mem_inter.mp hyBT).2
      have hyS : y ∈ S := by
        rcases Finset.mem_union.mp hyT with hyS | hyx'
        · exact hyS
        · have : y = x := by simpa using (Finset.mem_singleton.mp hyx')
          exact False.elim (hyx this)
      exact Finset.mem_inter.mpr ⟨hyB, hyS⟩


theorem rx_subset_S_of_goodX {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {S X : Finset α} {h0 : α}
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    {x : α} (hx : x ∈ goodXSet (family := family) S X h0 hS hfree hblocked) :
    ∃ w : BlockedUnionWitness family S x, (w.core.erase x) ⊆ S := by
  classical
  have hxX : x ∈ X := (Finset.mem_filter.mp hx).1
  have hxgood := (Finset.mem_filter.mp hx).2
  have hxnot : x ∉ S := by
    by_contra hxS
    have : False := by
      have hxgood' := hxgood
      simp [hxX, hxS] at hxgood'
    exact this
  have hxne0 : x ≠ h0 := by
    intro hxEq
    have : False := by
      have hxgood' := hxgood
      simp [hxEq] at hxgood'
    exact this
  let w :=
    chooseBlockedUnionWitness (family := family) (S := S) (x := x) hS hfree
      (hblocked x hxX hxnot hxne0)
  exact ⟨w, core_erase_subset_S_of_blockedUnionWitness (family := family) (S := S) (x := x) w⟩

theorem badXSet_card_le_ground_card {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {S X : Finset α} {h0 : α}
    (hXsub : X ⊆ ground)
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α))) :
    (badXSet (family := family) S X h0 hS hfree hblocked).card ≤ ground.card := by
  classical
  have hsubX : badXSet (family := family) S X h0 hS hfree hblocked ⊆ X := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  have hcardX :
      (badXSet (family := family) S X h0 hS hfree hblocked).card ≤ X.card :=
    Finset.card_le_card hsubX
  have hcardG : X.card ≤ ground.card := Finset.card_le_card hXsub
  exact hcardX.trans hcardG

/-!
`goodXSet` pigeonhole setup: attach the subtype `GoodX := {x // x ∈ goodXSet ...}`, define the
map `rx` sending `x` to the chosen witness core (with `x` erased), and prove a coarse pigeonhole
bound for collisions of `rx`.
-/

section GoodXPigeonhole

variable {α : Type*} [DecidableEq α]
variable {family : Finset (Finset α)} {S X : Finset α} {h0 : α}
abbrev GoodX
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α))) :=
  {x : α // x ∈ goodXSet (family := family) S X h0 hS hfree hblocked}

noncomputable def goodX
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α))) :
    Finset (GoodX hS hfree hblocked) :=
  (goodXSet (family := family) S X h0 hS hfree hblocked).attach

noncomputable def goodXWitness
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    {x : α} (hx : x ∈ goodXSet (family := family) S X h0 hS hfree hblocked) :
    BlockedUnionWitness family S x := by
  classical
  have hxX : x ∈ X := (Finset.mem_filter.mp hx).1
  have hxgood := (Finset.mem_filter.mp hx).2
  have hxnot : x ∉ S := by
    by_contra hxS
    have hxgood' := hxgood
    simp [hxX, hxS] at hxgood'
  have hxne0 : x ≠ h0 := by
    intro hxEq
    have hxgood' := hxgood
    simp [hxEq] at hxgood'
  exact
    chooseBlockedUnionWitness (family := family) (S := S) (x := x) hS hfree
      (hblocked x hxX hxnot hxne0)

noncomputable def rx
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (gx : GoodX hS hfree hblocked) :
    Finset α :=
  let w :=
    goodXWitness (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked (x := gx.1) gx.2
  w.core.erase gx.1

theorem rx_subset_S
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (gx : GoodX hS hfree hblocked) :
    rx hS hfree hblocked gx ⊆ S := by
  classical
  let w : BlockedUnionWitness family S gx.1 :=
    goodXWitness (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked (x := gx.1) gx.2
  simpa [rx, w] using
    core_erase_subset_S_of_blockedUnionWitness (family := family) (S := S) (x := gx.1) w

/-!
Trace refinement (one-field, Option-valued).

We attach a single optional "outside witness element" to the `x ↦ core.erase x` map. This is the
one allowed refinement after the `r_x`-collision counterexample: it lets the collision argument
distinguish witness-pairs that otherwise look identical when only `r_x` is recorded.
-/

/-- Finite range helper for Option-valued traces. -/
def optionOfFinset (T : Finset α) : Finset (Option α) :=
  insert none (T.image some)

theorem optionOfFinset_mono {T U : Finset α} (hTU : T ⊆ U) :
    optionOfFinset (α := α) T ⊆ optionOfFinset (α := α) U := by
  classical
  intro o ho
  -- Unfold membership in `insert none (T.image some)`.
  dsimp [optionOfFinset] at ho ⊢
  rcases Finset.mem_insert.mp ho with rfl | ho
  · exact Finset.mem_insert_self _ _
  · rcases Finset.mem_image.mp ho with ⟨t, htT, rfl⟩
    have htU : t ∈ U := hTU htT
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨t, htU, rfl⟩)

theorem mem_optionOfFinset_iff {T : Finset α} {o : Option α} :
    o ∈ optionOfFinset (α := α) T ↔ o = none ∨ ∃ t ∈ T, o = some t := by
  classical
  constructor
  · intro ho
    rcases Finset.mem_insert.mp ho with ho | ho
    · exact Or.inl ho
    · rcases Finset.mem_image.mp ho with ⟨t, htT, rfl⟩
      exact Or.inr ⟨t, htT, rfl⟩
  · intro ho
    rcases ho with rfl | ho
    · simp [optionOfFinset]
    · rcases ho with ⟨t, htT, rfl⟩
      simp [optionOfFinset, htT]

theorem mem_optionOfFinset_imp {T : Finset α} {o : Option α} :
    o ∈ optionOfFinset (α := α) T →
      o = none ∨ ∃ t ∈ T, o = some t := by
  intro ho
  exact (mem_optionOfFinset_iff (α := α) (T := T) (o := o)).1 ho

theorem card_optionOfFinset_le_succ (T : Finset α) :
    (optionOfFinset (α := α) T).card ≤ T.card + 1 := by
  classical
  -- `insert none (T.image some)` has card ≤ `card (T.image some) + 1`,
  -- and `image some` preserves card since `some` is injective.
  have hinsert :
      (optionOfFinset (α := α) T).card ≤ (T.image some).card + 1 := by
    dsimp [optionOfFinset]
    exact Finset.card_insert_le (none : Option α) (T.image some)
  have himg : (T.image some).card = T.card := by
    simpa using
      (Finset.card_image_of_injective (s := T) (f := some)
        (fun _a _b hab => by cases hab; rfl))
  simpa [himg] using hinsert

/--
Trace `t_x` for the chosen blocked-union witness of `S ∪ {x}`:
pick an element from the extra part `A \\ (S ∪ {x})` if nonempty, otherwise `none`.

This is intentionally *not* forced to exist; the `none` case corresponds to a "tight" witness.
-/
noncomputable def tx
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (gx : GoodX hS hfree hblocked) :
    Option α := by
  classical
  let w : BlockedUnionWitness family S gx.1 :=
    goodXWitness (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked (x := gx.1) gx.2
  let extras : Finset α := w.A \ (S ∪ ({gx.1} : Finset α))
  by_cases hex : extras.Nonempty
  · exact some (Classical.choose hex)
  · exact none

noncomputable def rtx
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (gx : GoodX hS hfree hblocked) :
    Finset α × Option α :=
  (rx hS hfree hblocked gx, tx hS hfree hblocked gx)

/--
Two-field trace `t_x = (t₁, t₂?)` for the chosen blocked-union witness of `S ∪ {x}`:
pick `t₁` as *some* element of the extra part `A \\ (S ∪ {x})` if nonempty, and
pick `t₂` as *some* element of the remaining extras after erasing `t₁` (if any).

This is intentionally a "first two by choice" selector: it does **not** record whether there are
more extras beyond `t₂`.
-/
noncomputable def tx2
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (gx : GoodX hS hfree hblocked) :
    Option (α × Option α) := by
  classical
  let w : BlockedUnionWitness family S gx.1 :=
    goodXWitness (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked (x := gx.1) gx.2
  let extras : Finset α := w.A \ insert gx.1 S
  by_cases hex : extras.Nonempty
  · let t1 : α := Classical.choose hex
    let extras2 : Finset α := extras.erase t1
    by_cases hex2 : extras2.Nonempty
    · let t2 : α := Classical.choose hex2
      exact some (t1, some t2)
    · exact some (t1, none)
  · exact none

noncomputable def rtx2
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (gx : GoodX hS hfree hblocked) :
    Finset α × Option (α × Option α) :=
  (rx hS hfree hblocked gx, tx2 hS hfree hblocked gx)

/--
Three-field trace `t_x = (t₁, t₂?, hasMore)` for the chosen blocked-union witness of `S ∪ {x}`.

This refines `tx2` by adding a 1-bit tag `hasMore` indicating whether there exists a third extra
element beyond the chosen first two. Concretely, in the `some (t₁, some t₂, _)` branch it checks
whether `(extras.erase t₁).erase t₂` is nonempty.
-/
noncomputable def tx2Plus
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (gx : GoodX hS hfree hblocked) :
    Option (α × Option α × Bool) := by
  classical
  let w : BlockedUnionWitness family S gx.1 :=
    goodXWitness (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked (x := gx.1) gx.2
  let extras : Finset α := w.A \ insert gx.1 S
  by_cases hex : extras.Nonempty
  · let t1 : α := Classical.choose hex
    let extras2 : Finset α := extras.erase t1
    by_cases hex2 : extras2.Nonempty
    · let t2 : α := Classical.choose hex2
      let extras3 : Finset α := extras2.erase t2
      by_cases hex3 : extras3.Nonempty
      · exact some (t1, some t2, true)
      · exact some (t1, some t2, false)
    · exact some (t1, none, false)
  · exact none

noncomputable def rtx2Plus
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (gx : GoodX hS hfree hblocked) :
    Finset α × Option (α × Option α × Bool) :=
  (rx hS hfree hblocked gx, tx2Plus hS hfree hblocked gx)

theorem mem_core_of_goodXWitness
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    {x : α} (hx : x ∈ goodXSet (family := family) S X h0 hS hfree hblocked) :
    x ∈ (goodXWitness (family := family) (S := S) (X := X) (h0 := h0)
          hS hfree hblocked (x := x) hx).core := by
  classical
  -- Extract the `if`-binder facts from `hx : x ∈ goodXSet ...`.
  have hxX : x ∈ X := (Finset.mem_filter.mp hx).1
  have hxP : _ := (Finset.mem_filter.mp hx).2
  have hxnot : x ∉ S := by
    intro hxS
    have hxP' := hxP
    simp [hxS] at hxP'
  have hxne0 : x ≠ h0 := by
    intro hxEq
    have hxP' := hxP
    simp [hxEq] at hxP'
  -- Simplify the predicate proof `hxP` to the core-membership statement for the chosen witness.
  have hxcore0 :
      x ∈ (chooseBlockedUnionWitness (family := family) (S := S) (x := x)
            hS hfree (hblocked x hxX hxnot hxne0)).core := by
    simpa [hxX, hxnot, hxne0] using hxP
  -- `goodXWitness` returns the same chosen witness (independent of Prop-irrelevant inputs),
  -- so we can reuse `hxcore0`.
  -- Unfold `goodXWitness` and rewrite the `BlockedByTwo` proof by proof irrelevance.
  -- (We avoid depending on the particular proofs of `x ∉ S` / `x ≠ h0`.)
  simpa [goodXWitness] using hxcore0

theorem mem_A_of_goodXWitness
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    {x : α} (hx : x ∈ goodXSet (family := family) S X h0 hS hfree hblocked) :
    x ∈ (goodXWitness (family := family) (S := S) (X := X) (h0 := h0)
          hS hfree hblocked (x := x) hx).A := by
  classical
  let w : BlockedUnionWitness family S x :=
    goodXWitness (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked (x := x) hx
  have hxcore : x ∈ w.core :=
    mem_core_of_goodXWitness (family := family) (S := S) (X := X) (h0 := h0)
      hS hfree hblocked hx
  have hxAT : x ∈ w.A ∩ (S ∪ ({x} : Finset α)) := by
    have : x ∈ w.core := hxcore
    -- rewrite membership along `w.hcoreAT` (in reverse)
    have hx' := this
    rw [← w.hcoreAT] at hx'
    exact hx'
  have hxA : x ∈ w.A := (Finset.mem_inter.mp hxAT).1
  simpa [w] using hxA

theorem tx_mem_optionOfFinset_family_biUnion
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (gx : GoodX hS hfree hblocked) :
    tx (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked gx ∈
      optionOfFinset (α := α) (family.biUnion id) := by
  classical
  -- Prove membership via the characterization lemma.
  refine (mem_optionOfFinset_iff (α := α) (T := family.biUnion id)
    (o := tx (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked gx)).2 ?_
  let w : BlockedUnionWitness family S gx.1 :=
    goodXWitness (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked (x := gx.1)
      gx.2
  let extras : Finset α := w.A \ (S ∪ ({gx.1} : Finset α))
  by_cases hex : extras.Nonempty
  · -- Use the *same* `Nonempty` proof as the one required to reduce `tx` after unfolding.
    have hex0 :
        ((goodXWitness hS hfree hblocked gx.2).A \ (S ∪ ({gx.1} : Finset α))).Nonempty := by
      simpa [w, extras] using hex
    have hex_ins :
        ((goodXWitness hS hfree hblocked gx.2).A \ insert gx.1 S).Nonempty := by
      simpa [Finset.union_singleton] using hex0
    let t : α := Classical.choose hex_ins
    have ht_extras_ins : t ∈ ((goodXWitness hS hfree hblocked gx.2).A \ insert gx.1 S) :=
      Classical.choose_spec hex_ins
    have ht_extras0 :
        t ∈ ((goodXWitness hS hfree hblocked gx.2).A \ (S ∪ ({gx.1} : Finset α))) := by
      simpa [Finset.union_singleton, t] using ht_extras_ins
    have ht_extras : t ∈ extras := by
      simpa [t, w, extras] using ht_extras0
    have htA : t ∈ w.A := (Finset.mem_sdiff.mp ht_extras).1
    have ht_union : t ∈ family.biUnion id := by
      refine Finset.mem_biUnion.mpr ?_
      exact ⟨w.A, w.hA, htA⟩
    have htx :
        tx (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked gx = some t := by
      -- Reduce `tx` using the syntactically matching `hex0`.
      simp [tx, hex_ins, t]
    exact Or.inr ⟨t, ht_union, htx⟩
  · have hex0 :
        ¬((goodXWitness hS hfree hblocked gx.2).A \ (S ∪ ({gx.1} : Finset α))).Nonempty := by
      simpa [w, extras] using hex
    have hex_ins : ¬((goodXWitness hS hfree hblocked gx.2).A \ insert gx.1 S).Nonempty := by
      simpa [Finset.union_singleton] using hex0
    have htx : tx (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked gx = none := by
      simp [tx, hex_ins]
    exact Or.inl htx

theorem image_rx_subset_powerset
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α))) :
    (goodX hS hfree hblocked).image (rx hS hfree hblocked)
      ⊆ S.powerset := by
  classical
  intro r hr
  rcases Finset.mem_image.mp hr with ⟨gx, hgx, rfl⟩
  exact Finset.mem_powerset.mpr (rx_subset_S hS hfree hblocked gx)

theorem card_image_rx_le_powerset_card
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α))) :
    ((goodX hS hfree hblocked).image (rx hS hfree hblocked)).card
      ≤ S.powerset.card := by
  classical
  exact Finset.card_le_card (image_rx_subset_powerset hS hfree hblocked)

theorem exists_rx_fiber_ge_div_powerset
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α))) :
    ∃ r ∈ S.powerset,
      ((goodX hS hfree hblocked).filter (fun gx => rx hS hfree hblocked gx = r)).card ≥
        (goodX hS hfree hblocked).card / S.powerset.card := by
  classical
  by_cases hGX :
      (goodX hS hfree hblocked).Nonempty
  · have himgNonempty :
        (((goodX hS hfree hblocked).image (rx hS hfree hblocked)).Nonempty) := by
        rcases hGX with ⟨gx, hgx⟩
        refine ⟨rx hS hfree hblocked gx, ?_⟩
        exact Finset.mem_image.mpr ⟨gx, hgx, rfl⟩
    -- Choose an `r` in the image that maximizes the fiber size.
    let img :=
      (goodX hS hfree hblocked).image (rx hS hfree hblocked)
    let fiber : Finset α → ℕ :=
      fun r => ((goodX hS hfree hblocked).filter (fun gx => rx hS hfree hblocked gx = r)).card
    obtain ⟨r, hrimg, hrmax⟩ :=
      Finset.exists_max_image img fiber (by simpa [img] using himgNonempty)
    have hrpow : r ∈ S.powerset := by
      exact (image_rx_subset_powerset hS hfree hblocked) hrimg
    have hsum :
        (goodX hS hfree hblocked).card =
          ∑ r' ∈ img, fiber r' := by
      -- Fiber decomposition over the image of `rx`.
      simpa [img, fiber] using
        (Finset.card_eq_sum_card_image
          (f := rx hS hfree hblocked)
          (s := goodX hS hfree hblocked))
    have hsum_le :
        (∑ r' ∈ img, fiber r') ≤ img.card * fiber r := by
      calc
        (∑ r' ∈ img, fiber r')
            ≤ ∑ _r' ∈ img, fiber r := by
                refine Finset.sum_le_sum ?_
                intro r' hr'
                exact hrmax r' hr'
        _ = img.card * fiber r := by
                simp
    have hcard_le : (goodX hS hfree hblocked).card ≤
        img.card * fiber r := by
      -- combine `hsum` and `hsum_le`
      simpa [hsum] using hsum_le
    have himg_le : img.card ≤ S.powerset.card :=
      card_image_rx_le_powerset_card hS hfree hblocked
    have hcard_le' :
        (goodX hS hfree hblocked).card ≤
          S.powerset.card * fiber r := by
      -- replace `img.card` by `S.powerset.card` using monotonicity of multiplication
      exact le_trans hcard_le (Nat.mul_le_mul_right (fiber r) himg_le)
    refine ⟨r, hrpow, ?_⟩
    -- Convert to the desired division bound.
    -- `Nat.div_le_of_le_mul` expects `m ≤ k * n`.
    simpa [fiber] using (Nat.div_le_of_le_mul hcard_le')
  · -- Trivial case: `goodX` is empty.
    have hGX0 :
        (goodX hS hfree hblocked) = ∅ := by
      simpa [Finset.not_nonempty_iff_eq_empty] using hGX
    refine ⟨∅, by simp, ?_⟩
    simp [hGX0]

theorem exists_rx_fiber_ge_three_of_three_mul_powerset_card_le
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (h3 :
      3 * S.powerset.card ≤ (goodX hS hfree hblocked).card) :
    ∃ r ∈ S.powerset,
      ((goodX hS hfree hblocked).filter (fun gx => rx hS hfree hblocked gx = r)).card ≥ 3 := by
  classical
  rcases
      exists_rx_fiber_ge_div_powerset (family := family) (S := S) (X := X) (h0 := h0) hS hfree
        hblocked with
    ⟨r, hrpow, hrfiber⟩
  refine ⟨r, hrpow, ?_⟩
  have hpos : 0 < S.powerset.card := by
    refine Finset.card_pos.mpr ?_
    refine ⟨(∅ : Finset α), ?_⟩
    simp [Finset.mem_powerset]
  have hdiv : 3 ≤ (goodX hS hfree hblocked).card / S.powerset.card := by
    exact (Nat.le_div_iff_mul_le hpos).2 h3
  -- `hrfiber` gives `fiber ≥ card/|powerset|`, and `hdiv` upgrades the RHS to `≥ 3`.
  exact le_trans hdiv hrfiber

/-- Range bound for `x ↦ (rx, tx)`: the first component is a subset of `S`, the second is in
`optionOfFinset (⋃ family)`. -/
theorem image_rtx_subset_powerset_product_option
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α))) :
    (goodX hS hfree hblocked).image
        (rtx (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked) ⊆
      S.powerset.product (optionOfFinset (α := α) (family.biUnion id)) := by
  classical
  intro rt hrt
  rcases Finset.mem_image.mp hrt with ⟨gx, hgx, rfl⟩
  refine Finset.mem_product.mpr ?_
  refine ⟨?_, ?_⟩
  · exact Finset.mem_powerset.mpr (rx_subset_S (family := family) (S := S) (X := X) (h0 := h0)
        hS hfree hblocked gx)
  · exact tx_mem_optionOfFinset_family_biUnion (family := family) (S := S) (X := X) (h0 := h0)
        hS hfree hblocked gx

theorem card_image_rtx_le_range_card
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α))) :
    ((goodX hS hfree hblocked).image
          (rtx (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked)).card ≤
      S.powerset.card * (optionOfFinset (α := α) (family.biUnion id)).card := by
  classical
  have hsub :
      (goodX hS hfree hblocked).image
          (rtx (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked) ⊆
        S.powerset.product (optionOfFinset (α := α) (family.biUnion id)) :=
    image_rtx_subset_powerset_product_option (family := family) (S := S) (X := X) (h0 := h0)
      hS hfree hblocked
  have hcard_le :
      ((goodX hS hfree hblocked).image
            (rtx (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked)).card ≤
        (S.powerset.product (optionOfFinset (α := α) (family.biUnion id))).card :=
    Finset.card_le_card hsub
  simpa [Finset.card_product, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hcard_le

theorem exists_rtx_fiber_ge_div_range
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α))) :
    ∃ rt ∈ S.powerset.product (optionOfFinset (α := α) (family.biUnion id)),
      ((goodX hS hfree hblocked).filter
          (fun gx =>
            rtx (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked gx = rt)).card ≥
        (goodX hS hfree hblocked).card /
          (S.powerset.product (optionOfFinset (α := α) (family.biUnion id))).card := by
  classical
  let range := S.powerset.product (optionOfFinset (α := α) (family.biUnion id))
  by_cases hGX : (goodX hS hfree hblocked).Nonempty
  · have himgNonempty :
        ((goodX hS hfree hblocked).image
            (rtx (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked)).Nonempty := by
      rcases hGX with ⟨gx, hgx⟩
      refine ⟨rtx (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked gx, ?_⟩
      exact Finset.mem_image.mpr ⟨gx, hgx, rfl⟩
    let img :=
      (goodX hS hfree hblocked).image
        (rtx (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked)
    let fiberFn : (Finset α × Option α) → ℕ :=
      fun rt =>
        ((goodX hS hfree hblocked).filter
            (fun gx =>
              rtx (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked gx = rt)).card
    obtain ⟨rt, hrtImg, hrtMax⟩ :=
      Finset.exists_max_image img fiberFn (by simpa [img] using himgNonempty)
    have hrtRange : rt ∈ range :=
      (image_rtx_subset_powerset_product_option (family := family) (S := S) (X := X) (h0 := h0)
          hS hfree hblocked) hrtImg
    have hsum :
        (goodX hS hfree hblocked).card =
          ∑ rt' ∈ img, fiberFn rt' := by
      simpa [img, fiberFn] using
        (Finset.card_eq_sum_card_image
          (f := rtx (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked)
          (s := goodX hS hfree hblocked))
    have hsum_le :
        (∑ rt' ∈ img, fiberFn rt') ≤ img.card * fiberFn rt := by
      calc
        (∑ rt' ∈ img, fiberFn rt')
            ≤ ∑ _rt' ∈ img, fiberFn rt := by
                refine Finset.sum_le_sum ?_
                intro rt' hrt'
                exact hrtMax rt' hrt'
        _ = img.card * fiberFn rt := by
                simp
    have hcard_le : (goodX hS hfree hblocked).card ≤ img.card * fiberFn rt := by
      simpa [hsum] using hsum_le
    have himg_le : img.card ≤ range.card := by
      have : img ⊆ range := by
        intro rt' hrt'
        exact (image_rtx_subset_powerset_product_option (family := family) (S := S) (X := X)
          (h0 := h0) hS hfree hblocked) hrt'
      exact Finset.card_le_card this
    have hcard_le' :
        (goodX hS hfree hblocked).card ≤ range.card * fiberFn rt := by
      exact le_trans hcard_le (Nat.mul_le_mul_right (fiberFn rt) himg_le)
    refine ⟨rt, hrtRange, ?_⟩
    simpa [fiberFn, range, Finset.card_product] using (Nat.div_le_of_le_mul hcard_le')
  · have hGX0 : goodX hS hfree hblocked = ∅ := by
      simpa [Finset.not_nonempty_iff_eq_empty] using hGX
    refine ⟨(∅, none), by simp [optionOfFinset, Finset.mem_powerset], ?_⟩
    simp [hGX0]

theorem exists_rtx_fiber_ge_three_of_three_mul_range_card_le
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (h3 :
      3 * (S.powerset.card * (optionOfFinset (α := α) (family.biUnion id)).card) ≤
        (goodX hS hfree hblocked).card) :
    ∃ rt ∈ S.powerset.product (optionOfFinset (α := α) (family.biUnion id)),
      ((goodX hS hfree hblocked).filter (fun gx =>
            rtx (family := family) (S := S) (X := X) (h0 := h0)
              hS hfree hblocked gx = rt)).card ≥ 3 := by
  classical
  let range := S.powerset.product (optionOfFinset (α := α) (family.biUnion id))
  rcases exists_rtx_fiber_ge_div_range (family := family) (S := S) (X := X) (h0 := h0) hS hfree
      hblocked with
    ⟨rt, hrtRange, hrtFiber⟩
  refine ⟨rt, hrtRange, ?_⟩
  have hpos : 0 < range.card := by
    refine Finset.card_pos.mpr ?_
    refine ⟨(∅, none), ?_⟩
    simp [range, optionOfFinset, Finset.mem_powerset]
  have hdiv : 3 ≤ (goodX hS hfree hblocked).card / range.card := by
    have h3' : 3 * range.card ≤ (goodX hS hfree hblocked).card := by
      simpa [range, Finset.card_product, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h3
    exact (Nat.le_div_iff_mul_le hpos).2 h3'
  exact le_trans hdiv hrtFiber

theorem exists_three_mem_pairwise_ne_of_card_ge_three {β : Type*} {F : Finset β} (hF : 3 ≤ F.card) :
    ∃ x1 x2 x3,
      x1 ∈ F ∧ x2 ∈ F ∧ x3 ∈ F ∧ x1 ≠ x2 ∧ x1 ≠ x3 ∧ x2 ≠ x3 := by
  classical
  have hFne : F.Nonempty := by
    refine Finset.card_pos.mp ?_
    exact lt_of_lt_of_le (by decide : 0 < 3) hF
  rcases hFne with ⟨x1, hx1⟩
  have h2 : 2 ≤ (F.erase x1).card := by
    have : 2 ≤ F.card - 1 := by
      simpa using (Nat.sub_le_sub_right hF 1)
    simpa [Finset.card_erase_of_mem hx1] using this
  have hF1ne : (F.erase x1).Nonempty := by
    refine Finset.card_pos.mp ?_
    exact lt_of_lt_of_le (by decide : 0 < 2) h2
  rcases hF1ne with ⟨x2, hx2'⟩
  have hx2 : x2 ∈ F := (Finset.mem_erase.mp hx2').2
  have hx12 : x1 ≠ x2 := (Finset.mem_erase.mp hx2').1.symm
  have h1 : 1 ≤ ((F.erase x1).erase x2).card := by
    have : 1 ≤ (F.erase x1).card - 1 := by
      simpa using (Nat.sub_le_sub_right h2 1)
    simpa [Finset.card_erase_of_mem hx2'] using this
  have hF2ne : ((F.erase x1).erase x2).Nonempty := by
    refine Finset.card_pos.mp ?_
    exact lt_of_lt_of_le (by decide : 0 < 1) h1
  rcases hF2ne with ⟨x3, hx3''⟩
  have hx3' : x3 ∈ F.erase x1 := (Finset.mem_erase.mp hx3'').2
  have hx3 : x3 ∈ F := (Finset.mem_erase.mp hx3').2
  have hx23 : x2 ≠ x3 := (Finset.mem_erase.mp hx3'').1.symm
  have hx13 : x1 ≠ x3 := (Finset.mem_erase.mp hx3').1.symm
  refine ⟨x1, x2, x3, hx1, hx2, hx3, hx12, hx13, hx23⟩

end GoodXPigeonhole

theorem sunflower_contradiction_of_three_sets {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} (hfree : IsSunflowerFree family 3)
    {S1 S2 S3 core : Finset α}
    (hS1 : S1 ∈ family) (hS2 : S2 ∈ family) (hS3 : S3 ∈ family)
    (h12 : S1 ∩ S2 = core) (h13 : S1 ∩ S3 = core) (h23 : S2 ∩ S3 = core)
    (h12ne : S1 ≠ S2) (h13ne : S1 ≠ S3) (h23ne : S2 ≠ S3) :
    False := by
  classical
  let F3 : Finset (Finset α) := {S1, S2, S3}
  have hsub : F3 ⊆ family := by
    intro T hT
    have hT' : T = S1 ∨ T = S2 ∨ T = S3 := by
      simpa [F3] using (Finset.mem_insert.mp hT)
    rcases hT' with rfl | hT'
    · exact hS1
    rcases hT' with rfl | rfl
    · exact hS2
    · exact hS3
  have hcard : F3.card = 3 := by
    have hS2not : S2 ∉ ({S3} : Finset (Finset α)) := by
      simp [h23ne]
    have hS1not : S1 ∉ insert S2 ({S3} : Finset (Finset α)) := by
      simp [h12ne, h13ne]
    have hcardB : (insert S2 ({S3} : Finset (Finset α))).card = 2 := by
      simp [Finset.card_insert_of_notMem, hS2not]
    have hcard' : (insert S1 (insert S2 ({S3} : Finset (Finset α)))).card = 3 := by
      calc
        (insert S1 (insert S2 ({S3} : Finset (Finset α)))).card =
            (insert S2 ({S3} : Finset (Finset α))).card + 1 := by
              simp [Finset.card_insert_of_notMem, hS1not]
        _ = 3 := by
              simp [hcardB]
    simpa [F3] using hcard'
  have hsun : IsSunflower F3 3 := by
    refine ⟨hcard, ?_⟩
    refine ⟨core, ?_⟩
    intro A B hA hB hAB
    have hA' : A = S1 ∨ A = S2 ∨ A = S3 := by
      simpa [F3] using (Finset.mem_insert.mp hA)
    have hB' : B = S1 ∨ B = S2 ∨ B = S3 := by
      simpa [F3] using (Finset.mem_insert.mp hB)
    rcases hA' with rfl | hA'
    · rcases hB' with rfl | hB'
      · exact False.elim (hAB rfl)
      · rcases hB' with rfl | rfl
        · exact h12
        · exact h13
    · rcases hA' with rfl | rfl
      · rcases hB' with rfl | hB'
        · simpa [Finset.inter_comm] using h12
        · rcases hB' with rfl | rfl
          · exact False.elim (hAB rfl)
          · exact h23
      · rcases hB' with rfl | hB'
        · simpa [Finset.inter_comm] using h13
        · rcases hB' with rfl | rfl
          · simpa [Finset.inter_comm] using h23
          · exact False.elim (hAB rfl)
  exact (hfree F3 hsub) hsun

/-!
`RealizedGoodX(S)` refinement:
when pigeonholing on `x ↦ rx` for a fixed reference completion `S`, we restrict attention to
`x` that are *realized* by some other completion in the (hard-branch) admissible fiber.

This avoids chasing collisions among `x ∈ X \\ S` that never actually occur in the fiber we are
counting.
-/

section RealizedGoodX

variable {α : Type*} [DecidableEq α]
variable {family : Finset (Finset α)}
variable {dom : Finset (Finset α)}

noncomputable def realizedXSet
    (fiber : Finset {T // T ∈ dom}) (S X : Finset α) : Finset α := by
  classical
  exact
    fiber.biUnion (fun Tsub => (Tsub.1 \ S) ∩ X)

theorem mem_realizedXSet_imp_mem_X
    (fiber : Finset {T // T ∈ dom}) {S X : Finset α} {x : α}
    (hx : x ∈ realizedXSet (dom := dom) fiber S X) : x ∈ X := by
  classical
  rcases (Finset.mem_biUnion.mp hx) with ⟨Tsub, _hTsub, hx'⟩
  exact (Finset.mem_inter.mp hx').2

theorem mem_realizedXSet_imp_not_mem_S
    (fiber : Finset {T // T ∈ dom}) {S X : Finset α} {x : α}
    (hx : x ∈ realizedXSet (dom := dom) fiber S X) : x ∉ S := by
  classical
  rcases (Finset.mem_biUnion.mp hx) with ⟨Tsub, _hTsub, hx'⟩
  have hxSdiff : x ∈ Tsub.1 \ S := (Finset.mem_inter.mp hx').1
  exact (Finset.mem_sdiff.mp hxSdiff).2

noncomputable def chooseCompletionForX
    (fiber : Finset {T // T ∈ dom}) {S X : Finset α} {x : α}
    (hx : x ∈ realizedXSet (dom := dom) fiber S X) :
    {T // T ∈ dom} :=
  Classical.choose (Finset.mem_biUnion.mp hx)

theorem chooseCompletionForX_spec
    (fiber : Finset {T // T ∈ dom}) {S X : Finset α} {x : α}
    (hx : x ∈ realizedXSet (dom := dom) fiber S X) :
    chooseCompletionForX (dom := dom) fiber (S := S) (X := X) (x := x) hx ∈ fiber ∧
      x ∈ (chooseCompletionForX (dom := dom) fiber (S := S) (X := X) (x := x) hx).1 := by
  classical
  have hx' : ∃ Tsub ∈ fiber, x ∈ (Tsub.1 \ S) ∩ X := Finset.mem_biUnion.mp hx
  have hspec : Classical.choose hx' ∈ fiber ∧ x ∈ ((Classical.choose hx').1 \ S) ∩ X :=
    Classical.choose_spec hx'
  refine ⟨?_, ?_⟩
  · simpa [chooseCompletionForX, hx'] using hspec.1
  · -- `hspec.2 : x ∈ ((choose hx').1 \ S) ∩ X`
    have : x ∈ (Classical.choose hx').1 \ S := (Finset.mem_inter.mp hspec.2).1
    exact (Finset.mem_sdiff.mp this).1

variable {S X : Finset α} {h0 : α}

noncomputable def realizedGoodXSet
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α))) :
    Finset α := by
  classical
  exact
    realizedXSet (dom := dom) fiber S X ∩
      goodXSet (family := family) S X h0 hS hfree hblocked

theorem mem_realizedGoodXSet_iff
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α))) {x : α} :
    x ∈ realizedGoodXSet (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked ↔
      x ∈ realizedXSet (dom := dom) fiber S X ∧
        x ∈ goodXSet (family := family) S X h0 hS hfree hblocked := by
  classical
  simp [realizedGoodXSet]

theorem mem_realizedGoodXSet_imp
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α))) {x : α} :
    x ∈ realizedGoodXSet (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked →
      x ∈ realizedXSet (dom := dom) fiber S X ∧
        x ∈ goodXSet (family := family) S X h0 hS hfree hblocked := by
  intro hx
  exact
    (mem_realizedGoodXSet_iff (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
      fiber hS hfree hblocked).1 hx

abbrev RealizedGoodX
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α))) :=
  {x : α // x ∈ realizedGoodXSet (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
    fiber hS hfree hblocked}

noncomputable def realizedGoodX
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α))) :
    Finset (RealizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
      fiber hS hfree hblocked) :=
  (realizedGoodXSet (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
    fiber hS hfree hblocked).attach

noncomputable def rxRealized
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (gx :
      RealizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked) :
    Finset α :=
  let hxGood :
      gx.1 ∈ goodXSet (family := family) S X h0 hS hfree hblocked := by
        have : gx.1 ∈
            realizedXSet (dom := dom) fiber S X ∩
              goodXSet (family := family) S X h0 hS hfree hblocked := by
            have hx :
                gx.1 ∈
                  realizedGoodXSet (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
                    fiber hS hfree hblocked := gx.2
            have hx' :=
              (mem_realizedGoodXSet_iff (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
                    fiber hS hfree hblocked).1 hx
            exact Finset.mem_inter.mpr hx'
        exact (Finset.mem_inter.mp this).2
  let w :=
    goodXWitness (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked
      (x := gx.1) hxGood
  w.core.erase gx.1

theorem rxRealized_subset_S
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (gx :
      RealizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked) :
    rxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked gx ⊆ S := by
  classical
  have hxGood :
      gx.1 ∈ goodXSet (family := family) S X h0 hS hfree hblocked := by
    have : gx.1 ∈
        realizedXSet (dom := dom) fiber S X ∩
          goodXSet (family := family) S X h0 hS hfree hblocked := by
      have hx :
          gx.1 ∈
            realizedGoodXSet (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
              fiber hS hfree hblocked := gx.2
      have hx' :=
        (mem_realizedGoodXSet_iff (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
              fiber hS hfree hblocked).1 hx
      exact Finset.mem_inter.mpr hx'
    exact (Finset.mem_inter.mp this).2
  let w : BlockedUnionWitness family S gx.1 :=
    goodXWitness (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked
      (x := gx.1) hxGood
  simpa [rxRealized, w] using
    core_erase_subset_S_of_blockedUnionWitness (family := family) (S := S) (x := gx.1) w

/-!
Trace refinement for `RealizedGoodX(S)`: reuse the `GoodX` trace `tx` by forgetting the
realization proof and keeping only membership in `goodXSet`.
-/

noncomputable def toGoodX_of_realizedGoodX
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (gx :
      RealizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked) :
    GoodX (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked :=
by
  classical
  have hxGood :
      gx.1 ∈ goodXSet (family := family) S X h0 hS hfree hblocked := by
    have hx' :=
      (mem_realizedGoodXSet_iff (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked).1 gx.2
    exact hx'.2
  exact ⟨gx.1, hxGood⟩

noncomputable def txRealized
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (gx :
      RealizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked) :
    Option α :=
  tx (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked
    (toGoodX_of_realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
      fiber hS hfree hblocked gx)

noncomputable def tx2Realized
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (gx :
      RealizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked) :
    Option (α × Option α) :=
  tx2 (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked
    (toGoodX_of_realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
      fiber hS hfree hblocked gx)

noncomputable def tx2PlusRealized
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (gx :
      RealizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked) :
    Option (α × Option α × Bool) :=
  tx2Plus (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked
    (toGoodX_of_realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
      fiber hS hfree hblocked gx)

noncomputable def rtxRealized
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (gx :
      RealizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked) :
    Finset α × Option α :=
  (rxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
      fiber hS hfree hblocked gx,
    txRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
      fiber hS hfree hblocked gx)

noncomputable def rtx2Realized
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (gx :
      RealizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked) :
    Finset α × Option (α × Option α) :=
  (rxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
      fiber hS hfree hblocked gx,
    tx2Realized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
      fiber hS hfree hblocked gx)

noncomputable def rtx2PlusRealized
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (gx :
      RealizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked) :
    Finset α × Option (α × Option α × Bool) :=
  (rxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
      fiber hS hfree hblocked gx,
    tx2PlusRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
      fiber hS hfree hblocked gx)

/-!
`hasMore = true` overhead bucket for `RealizedGoodX(S)`.

We treat this case with a coarse polynomial bound (no collision argument), per guidance.
-/

noncomputable def realizedGoodX_hasMoreTrue
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α))) :
    Finset (RealizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
      fiber hS hfree hblocked) := by
  classical
  exact
    (realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked).filter (fun gx =>
      ∃ t1 t2 : α,
        tx2PlusRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked gx =
          some (t1, some t2, true))

theorem txRealized_mem_optionOfFinset_family_biUnion
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (gx :
      RealizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked) :
    txRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked gx ∈ optionOfFinset (α := α) (family.biUnion id) := by
  classical
  simpa [txRealized] using
    tx_mem_optionOfFinset_family_biUnion (family := family) (S := S) (X := X) (h0 := h0)
      hS hfree hblocked
      (toGoodX_of_realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked gx)

noncomputable def chooseCompletionForRealizedGoodX
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (gx :
      RealizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked) :
    {T // T ∈ dom} :=
  let hxReal :
      gx.1 ∈ realizedXSet (dom := dom) fiber S X :=
    (mem_realizedGoodXSet_iff (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked).1 gx.2 |>.1
  chooseCompletionForX (dom := dom) fiber (S := S) (X := X) (x := gx.1) hxReal

theorem chooseCompletionForRealizedGoodX_spec
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (gx :
      RealizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked) :
    chooseCompletionForRealizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked gx ∈ fiber ∧
      gx.1 ∈
        (chooseCompletionForRealizedGoodX (family := family) (dom := dom) (S := S) (X := X)
            (h0 := h0) fiber hS hfree hblocked gx).1 := by
  classical
  let hxReal :
      gx.1 ∈ realizedXSet (dom := dom) fiber S X :=
    (mem_realizedGoodXSet_iff (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked).1 gx.2 |>.1
  -- unfold to reuse the generic chooser spec
  simpa [chooseCompletionForRealizedGoodX, hxReal] using
    (chooseCompletionForX_spec (dom := dom) (fiber := fiber) (S := S) (X := X) (x := gx.1) hxReal)

theorem A_subset_insert_of_txRealized_eq_none
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (gx :
      RealizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked)
    (htx : txRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
      fiber hS hfree hblocked gx = none) :
    let g :=
      toGoodX_of_realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked gx
    (goodXWitness (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked
        (x := gx.1) g.2).A ⊆ insert gx.1 S := by
  classical
  intro g
  let w : BlockedUnionWitness family S gx.1 :=
    goodXWitness (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked
      (x := gx.1) g.2
  have htx' :
      tx (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g = none := by
    simpa [txRealized] using htx
  -- If there were an element of `w.A` outside `S ∪ {x}`,
  -- `tx` would be `some _`, contradicting `htx'`.
  have hNoExtras : ¬(w.A \ insert gx.1 S).Nonempty := by
    intro hex
    have hex' :
        ((goodXWitness (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked
                (x := gx.1) g.2).A \ insert gx.1 S).Nonempty := by
      simpa [w] using hex
    have hexg :
        ((goodXWitness (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked
                (x := gx.1) g.2).A \ insert (↑g) S).Nonempty := by
      simpa [g] using hex'
    have hsome :
        tx (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g =
          some (Classical.choose hexg) := by
      simp [tx, hexg]
    have hcontr : False := by
      have h := htx'
      simp [hsome] at h
    exact hcontr
  have hEmpty : w.A \ insert gx.1 S = ∅ := by
    simpa [Finset.not_nonempty_iff_eq_empty] using hNoExtras
  have hsub : w.A ⊆ insert gx.1 S :=
    (Finset.sdiff_eq_empty_iff_subset).1 hEmpty
  simpa [w] using hsub

theorem mem_A_of_txRealized_eq_some
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (gx :
      RealizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked)
    {t : α}
    (htx : txRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
      fiber hS hfree hblocked gx = some t) :
    let g :=
      toGoodX_of_realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked gx
    t ∈ (goodXWitness (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked
        (x := gx.1) g.2).A := by
  classical
  intro g
  let w : BlockedUnionWitness family S g.1 :=
    goodXWitness (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked
      (x := g.1) g.2
  have htx' :
      tx (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g = some t := by
    simpa [txRealized] using htx
  let extras : Finset α := w.A \ insert g.1 S
  by_cases hex : extras.Nonempty
  · have htx_def :
        tx (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g =
          some (Classical.choose hex) := by
      simp [tx, w, extras, Finset.union_singleton, hex]
    have htEq : Classical.choose hex = t := by
      simpa [htx_def] using htx'
    have htMem : Classical.choose hex ∈ extras := Classical.choose_spec hex
    have htA : Classical.choose hex ∈ w.A := (Finset.mem_sdiff.mp htMem).1
    simpa [w, htEq] using htA
  · have htx_none :
        tx (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g = none := by
      simp [tx, w, extras, Finset.union_singleton, hex]
    have : False := by
      have : (none : Option α) = some t := by simpa [htx_none] using htx'
      cases this
    exact False.elim this

theorem not_mem_insert_of_txRealized_eq_some
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (gx :
      RealizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked)
    {t : α}
    (htx : txRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
      fiber hS hfree hblocked gx = some t) :
    let g :=
      toGoodX_of_realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked gx
    t ∉ insert gx.1 S := by
  classical
  intro g
  let w : BlockedUnionWitness family S g.1 :=
    goodXWitness (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked
      (x := g.1) g.2
  have htx' :
      tx (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g = some t := by
    simpa [txRealized] using htx
  let extras : Finset α := w.A \ insert g.1 S
  by_cases hex : extras.Nonempty
  · have htx_def :
        tx (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g =
          some (Classical.choose hex) := by
      simp [tx, w, extras, Finset.union_singleton, hex]
    have htEq : Classical.choose hex = t := by
      simpa [htx_def] using htx'
    have htMem : Classical.choose hex ∈ extras := Classical.choose_spec hex
    have htNot : Classical.choose hex ∉ insert g.1 S := (Finset.mem_sdiff.mp htMem).2
    simpa [htEq] using htNot
  · have htx_none :
        tx (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g = none := by
      simp [tx, w, extras, Finset.union_singleton, hex]
    have : False := by
      have : (none : Option α) = some t := by simpa [htx_none] using htx'
      cases this
    exact False.elim this

theorem A_subset_insert_of_tx2Realized_eq_none
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (gx :
      RealizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked)
    (htx : tx2Realized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
      fiber hS hfree hblocked gx = none) :
    let g :=
      toGoodX_of_realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked gx
    (goodXWitness (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked
        (x := gx.1) g.2).A ⊆ insert gx.1 S := by
  classical
  intro g
  let w : BlockedUnionWitness family S g.1 :=
    goodXWitness (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked
      (x := g.1) g.2
  have htx' :
      tx2 (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g = none := by
    simpa [tx2Realized] using htx
  let extras : Finset α := w.A \ insert g.1 S
  have hNoExtras : ¬extras.Nonempty := by
    by_contra hex
    have htx_def :
        tx2 (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g ≠ none := by
      -- unfolding `tx2`, the `Nonempty` branch returns `some _` (regardless of the second choice).
      by_cases hex2 : (extras.erase (Classical.choose hex)).Nonempty
      · simp [tx2, w, extras, hex, hex2]
      · simp [tx2, w, extras, hex, hex2]
    exact htx_def htx'
  have hEmpty : extras = ∅ := by
    simpa [Finset.not_nonempty_iff_eq_empty] using hNoExtras
  -- If `A \\ (S ∪ {x}) = ∅`, then `A ⊆ S ∪ {x}`.
  have hsub0 :
      w.A ⊆ insert g.1 S :=
    (Finset.sdiff_eq_empty_iff_subset).1 hEmpty
  simpa [w] using hsub0

theorem mem_A_of_tx2Realized_eq_some_fst
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (gx :
      RealizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked)
    {t1 : α} {ot2 : Option α}
    (htx : tx2Realized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
      fiber hS hfree hblocked gx = some (t1, ot2)) :
    let g :=
      toGoodX_of_realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked gx
    t1 ∈ (goodXWitness (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked
        (x := gx.1) g.2).A := by
  classical
  intro g
  let w : BlockedUnionWitness family S g.1 :=
    goodXWitness (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked
      (x := g.1) g.2
  have htx' :
      tx2 (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g =
        some (t1, ot2) := by
    simpa [tx2Realized] using htx
  let extras : Finset α := w.A \ insert g.1 S
  by_cases hex : extras.Nonempty
  · -- In the nonempty branch, `tx2` returns `some (choose hex, _)`.
    by_cases hex2 : (extras.erase (Classical.choose hex)).Nonempty
    · have hsome :
          some (Classical.choose hex, some (Classical.choose hex2)) = some (t1, ot2) := by
        simpa [tx2, w, extras, hex, hex2] using htx'
      have hpair : (Classical.choose hex, some (Classical.choose hex2)) = (t1, ot2) :=
        Option.some.inj hsome
      have htEq : Classical.choose hex = t1 := congrArg Prod.fst hpair
      have htMem : Classical.choose hex ∈ extras := Classical.choose_spec hex
      have htA : Classical.choose hex ∈ w.A := (Finset.mem_sdiff.mp htMem).1
      simpa [w, htEq] using htA
    · have hsome :
          some (Classical.choose hex, none) = some (t1, ot2) := by
        simpa [tx2, w, extras, hex, hex2] using htx'
      have hpair : (Classical.choose hex, none) = (t1, ot2) := Option.some.inj hsome
      have htEq : Classical.choose hex = t1 := congrArg Prod.fst hpair
      have htMem : Classical.choose hex ∈ extras := Classical.choose_spec hex
      have htA : Classical.choose hex ∈ w.A := (Finset.mem_sdiff.mp htMem).1
      simpa [w, htEq] using htA
  · -- If `extras` is empty, `tx2` is `none`, contradiction.
    have htx_none :
        tx2 (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g = none := by
      simp [tx2, w, extras, hex]
    have : False := by
      have : (none : Option (α × Option α)) = some (t1, ot2) := by
        simpa [htx_none] using htx'
      cases this
    exact False.elim this

theorem not_mem_insert_of_tx2Realized_eq_some_fst
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (gx :
      RealizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked)
    {t1 : α} {ot2 : Option α}
    (htx : tx2Realized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
      fiber hS hfree hblocked gx = some (t1, ot2)) :
    let g :=
      toGoodX_of_realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked gx
    t1 ∉ insert gx.1 S := by
  classical
  intro g
  let w : BlockedUnionWitness family S g.1 :=
    goodXWitness (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked
      (x := g.1) g.2
  have htx' :
      tx2 (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g =
        some (t1, ot2) := by
    simpa [tx2Realized] using htx
  let extras : Finset α := w.A \ insert g.1 S
  by_cases hex : extras.Nonempty
  · by_cases hex2 : (extras.erase (Classical.choose hex)).Nonempty
    · have hsome :
          some (Classical.choose hex, some (Classical.choose hex2)) = some (t1, ot2) := by
        simpa [tx2, w, extras, hex, hex2] using htx'
      have hpair : (Classical.choose hex, some (Classical.choose hex2)) = (t1, ot2) :=
        Option.some.inj hsome
      have htEq : Classical.choose hex = t1 := congrArg Prod.fst hpair
      have htMem : Classical.choose hex ∈ extras := Classical.choose_spec hex
      have htNot : Classical.choose hex ∉ insert g.1 S := (Finset.mem_sdiff.mp htMem).2
      simpa [htEq] using htNot
    · have hsome :
          some (Classical.choose hex, none) = some (t1, ot2) := by
        simpa [tx2, w, extras, hex, hex2] using htx'
      have hpair : (Classical.choose hex, none) = (t1, ot2) := Option.some.inj hsome
      have htEq : Classical.choose hex = t1 := congrArg Prod.fst hpair
      have htMem : Classical.choose hex ∈ extras := Classical.choose_spec hex
      have htNot : Classical.choose hex ∉ insert g.1 S := (Finset.mem_sdiff.mp htMem).2
      simpa [htEq] using htNot
  · have htx_none :
        tx2 (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g = none := by
      simp [tx2, w, extras, hex]
    have : False := by
      have : (none : Option (α × Option α)) = some (t1, ot2) := by
        simpa [htx_none] using htx'
      cases this
    exact False.elim this

theorem mem_A_of_tx2Realized_eq_some_snd
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (gx :
      RealizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked)
    {t1 t2 : α}
    (htx : tx2Realized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
      fiber hS hfree hblocked gx = some (t1, some t2)) :
    let g :=
      toGoodX_of_realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked gx
    t2 ∈ (goodXWitness (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked
        (x := gx.1) g.2).A := by
  classical
  intro g
  let w : BlockedUnionWitness family S g.1 :=
    goodXWitness (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked
      (x := g.1) g.2
  have htx' :
      tx2 (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g =
        some (t1, some t2) := by
    simpa [tx2Realized] using htx
  let extras : Finset α := w.A \ insert g.1 S
  by_cases hex : extras.Nonempty
  · by_cases hex2 : (extras.erase (Classical.choose hex)).Nonempty
    · have hsome :
          some (Classical.choose hex, some (Classical.choose hex2)) = some (t1, some t2) := by
        simpa [tx2, w, extras, hex, hex2] using htx'
      have hpair := Option.some.inj hsome
      have htEq2 : Classical.choose hex2 = t2 := by
        have : some (Classical.choose hex2) = some t2 := congrArg Prod.snd hpair
        exact Option.some.inj this
      have htMem : Classical.choose hex2 ∈ (extras.erase (Classical.choose hex)) :=
        Classical.choose_spec hex2
      have htInExtras : Classical.choose hex2 ∈ extras := (Finset.mem_erase.mp htMem).2
      have htA : Classical.choose hex2 ∈ w.A := (Finset.mem_sdiff.mp htInExtras).1
      simpa [w, htEq2] using htA
    · -- If there is no second extra, `tx2` returns `some (t1, none)`, contradiction.
      have htx_def :
          tx2 (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g =
            some (Classical.choose hex, none) := by
        simp [tx2, w, extras, hex, hex2]
      have : False := by
        have : some (Classical.choose hex, none) = some (t1, some t2) := by
          simpa [htx_def] using htx'
        cases this
      exact False.elim this
  · -- If `extras` is empty, `tx2` is `none`, contradiction.
    have htx_none :
        tx2 (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g = none := by
      simp [tx2, w, extras, hex]
    have : False := by
      have : (none : Option (α × Option α)) = some (t1, some t2) := by
        simpa [htx_none] using htx'
      cases this
    exact False.elim this

theorem not_mem_insert_of_tx2Realized_eq_some_snd
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (gx :
      RealizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked)
    {t1 t2 : α}
    (htx : tx2Realized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
      fiber hS hfree hblocked gx = some (t1, some t2)) :
    let g :=
      toGoodX_of_realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked gx
    t2 ∉ insert gx.1 S := by
  classical
  intro g
  let w : BlockedUnionWitness family S g.1 :=
    goodXWitness (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked
      (x := g.1) g.2
  have htx' :
      tx2 (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g =
        some (t1, some t2) := by
    simpa [tx2Realized] using htx
  let extras : Finset α := w.A \ insert g.1 S
  by_cases hex : extras.Nonempty
  · by_cases hex2 : (extras.erase (Classical.choose hex)).Nonempty
    · have hsome :
          some (Classical.choose hex, some (Classical.choose hex2)) = some (t1, some t2) := by
        simpa [tx2, w, extras, hex, hex2] using htx'
      have hpair := Option.some.inj hsome
      have htEq2 : Classical.choose hex2 = t2 := by
        have : some (Classical.choose hex2) = some t2 := congrArg Prod.snd hpair
        exact Option.some.inj this
      have htMem : Classical.choose hex2 ∈ (extras.erase (Classical.choose hex)) :=
        Classical.choose_spec hex2
      have htInExtras : Classical.choose hex2 ∈ extras := (Finset.mem_erase.mp htMem).2
      have htNot : Classical.choose hex2 ∉ insert g.1 S := (Finset.mem_sdiff.mp htInExtras).2
      simpa [htEq2] using htNot
    · have htx_def :
          tx2 (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g =
            some (Classical.choose hex, none) := by
        simp [tx2, w, extras, hex, hex2]
      have : False := by
        have : some (Classical.choose hex, none) = some (t1, some t2) := by
          simpa [htx_def] using htx'
        cases this
      exact False.elim this
  · have htx_none :
        tx2 (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g = none := by
      simp [tx2, w, extras, hex]
    have : False := by
      have : (none : Option (α × Option α)) = some (t1, some t2) := by
        simpa [htx_none] using htx'
      cases this
    exact False.elim this

theorem mem_sdiff_erase_fst_of_tx2Realized_eq_some_snd
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (gx :
      RealizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked)
    {t1 t2 : α}
    (htx : tx2Realized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
      fiber hS hfree hblocked gx = some (t1, some t2)) :
    let g :=
      toGoodX_of_realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked gx
    let w : BlockedUnionWitness family S g.1 :=
      goodXWitness (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked
        (x := g.1) g.2
    t2 ∈ (w.A \ insert g.1 S).erase t1 := by
  classical
  intro g w
  have htx' :
      tx2 (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g =
        some (t1, some t2) := by
    simpa [tx2Realized] using htx
  let extras : Finset α := w.A \ insert g.1 S
  by_cases hex : extras.Nonempty
  · by_cases hex2 : (extras.erase (Classical.choose hex)).Nonempty
    · have hsome :
          some (Classical.choose hex, some (Classical.choose hex2)) = some (t1, some t2) := by
        simpa [tx2, w, extras, hex, hex2] using htx'
      have hpair := Option.some.inj hsome
      have htEq1 : Classical.choose hex = t1 := congrArg Prod.fst hpair
      have htEq2 : Classical.choose hex2 = t2 := by
        have : some (Classical.choose hex2) = some t2 := congrArg Prod.snd hpair
        exact Option.some.inj this
      have htMem : Classical.choose hex2 ∈ (extras.erase (Classical.choose hex)) :=
        Classical.choose_spec hex2
      have htMem1 : Classical.choose hex2 ∈ (extras.erase t1) := by
        simpa [htEq1] using htMem
      have htMem' : t2 ∈ (extras.erase t1) := by
        simpa [htEq2] using htMem1
      -- `t2 ∈ erase t1 extras` is exactly membership in `(extras.erase t1)`.
      simpa [extras] using htMem'
    · -- If there is no second extra, `tx2` returns `some (t1, none)`, contradiction.
      have htx_def :
          tx2 (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g =
            some (Classical.choose hex, none) := by
        simp [tx2, w, extras, hex, hex2]
      have : False := by
        have : some (Classical.choose hex, none) = some (t1, some t2) := by
          simpa [htx_def] using htx'
        cases this
      exact False.elim this
  · -- If `extras` is empty, `tx2` is `none`, contradiction.
    have htx_none :
        tx2 (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g = none := by
      simp [tx2, w, extras, hex]
    have : False := by
      have : (none : Option (α × Option α)) = some (t1, some t2) := by
        simpa [htx_none] using htx'
      cases this
    exact False.elim this

theorem A_sdiff_insert_subset_singleton_of_tx2Realized_eq_some_none
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (gx :
      RealizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked)
    {t1 : α}
    (htx :
      tx2Realized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked gx =
        some (t1, (none : Option α))) :
    let g :=
      toGoodX_of_realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked gx
    let w : BlockedUnionWitness family S g.1 :=
      goodXWitness (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked
        (x := g.1) g.2
    w.A \ insert g.1 S ⊆ ({t1} : Finset α) := by
  classical
  intro g w
  have htx' :
      tx2 (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g =
        some (t1, (none : Option α)) := by
    simpa [tx2Realized] using htx
  let extras : Finset α := w.A \ insert g.1 S
  by_cases hex : extras.Nonempty
  · by_cases hex2 : (extras.erase (Classical.choose hex)).Nonempty
    · -- If there is a second extra, `tx2` returns `some (_, some _)`, contradiction.
      have htx_def :
          tx2 (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g =
            some (Classical.choose hex, some (Classical.choose hex2)) := by
        simp [tx2, w, extras, hex, hex2]
      have : False := by
        have : some (Classical.choose hex, some (Classical.choose hex2)) =
            some (t1, (none : Option α)) := by
          simpa [htx_def] using htx'
        cases this
      exact False.elim this
    · -- No second extra: `extras.erase t1 = ∅`, hence `extras ⊆ {t1}`.
      have htx_def :
          tx2 (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g =
            some (Classical.choose hex, (none : Option α)) := by
        simp [tx2, w, extras, hex, hex2]
      have hsome :
          some (Classical.choose hex, (none : Option α)) = some (t1, (none : Option α)) := by
        simpa [htx_def] using htx'
      have htEq : Classical.choose hex = t1 := by
        have hpair := Option.some.inj hsome
        exact congrArg Prod.fst hpair
      have hNoExtras : extras.erase t1 = (∅ : Finset α) := by
        have hNo : extras.erase (Classical.choose hex) = (∅ : Finset α) := by
          simpa [Finset.not_nonempty_iff_eq_empty] using hex2
        simpa [htEq] using hNo
      intro z hz
      by_cases hzEq : z = t1
      · subst hzEq
        simpa using Finset.mem_singleton_self t1
      · have hzErase : z ∈ extras.erase t1 := Finset.mem_erase.mpr ⟨hzEq, hz⟩
        have : False := by
          have : z ∈ (∅ : Finset α) := by simpa [hNoExtras] using hzErase
          simpa using this
        exact False.elim this
  · -- If `extras` is empty, `tx2` is `none`, contradiction.
    have htx_none :
        tx2 (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g = none := by
      simp [tx2, w, extras, hex]
    have : False := by
      have : (none : Option (α × Option α)) = some (t1, (none : Option α)) := by
        simpa [htx_none] using htx'
      cases this
    exact False.elim this

theorem tx2Realized_eq_some_of_tx2PlusRealized_eq_some_some
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (gx :
      RealizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked)
    {t1 t2 : α} {b : Bool}
    (htx :
      tx2PlusRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked gx =
        some (t1, some t2, b)) :
    tx2Realized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked gx =
      some (t1, some t2) := by
  classical
  let g :=
    toGoodX_of_realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
      fiber hS hfree hblocked gx
  let w : BlockedUnionWitness family S g.1 :=
    goodXWitness (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked
      (x := g.1) g.2
  have htx' :
      tx2Plus (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g =
        some (t1, some t2, b) := by
    simpa [tx2PlusRealized] using htx
  let extras : Finset α := w.A \ insert g.1 S
  by_cases hex : extras.Nonempty
  · let t1' : α := Classical.choose hex
    let extras2 : Finset α := extras.erase t1'
    by_cases hex2 : extras2.Nonempty
    · let t2' : α := Classical.choose hex2
      let extras3 : Finset α := extras2.erase t2'
      by_cases hex3 : extras3.Nonempty
      · have htx_def :
            tx2Plus (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g =
              some (t1', some t2', true) := by
          simp [tx2Plus, w, extras, hex, t1', extras2, hex2, t2', extras3, hex3]
        have hsome : some (t1', some t2', true) = some (t1, some t2, b) := by
          simpa [htx_def] using htx'
        have hpair := Option.some.inj hsome
        have htEq1 : t1' = t1 := congrArg Prod.fst hpair
        have htEq2 : t2' = t2 := by
          have : (some t2', true) = (some t2, b) := congrArg Prod.snd hpair
          have : some t2' = some t2 := congrArg Prod.fst this
          exact Option.some.inj this
        have htx2_def :
            tx2 (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g =
              some (t1', some t2') := by
          simp [tx2, w, extras, hex, t1', extras2, hex2, t2']
        have htx2_def' :
            tx2 (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g =
              some (t1, some t2) := by
          simpa [htEq1, htEq2] using htx2_def
        simpa [tx2Realized, g] using htx2_def'
      · have htx_def :
            tx2Plus (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g =
              some (t1', some t2', false) := by
          simp [tx2Plus, w, extras, hex, t1', extras2, hex2, t2', extras3, hex3]
        have hsome : some (t1', some t2', false) = some (t1, some t2, b) := by
          simpa [htx_def] using htx'
        have hpair := Option.some.inj hsome
        have htEq1 : t1' = t1 := congrArg Prod.fst hpair
        have htEq2 : t2' = t2 := by
          have : (some t2', false) = (some t2, b) := congrArg Prod.snd hpair
          have : some t2' = some t2 := congrArg Prod.fst this
          exact Option.some.inj this
        have htx2_def :
            tx2 (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g =
              some (t1', some t2') := by
          simp [tx2, w, extras, hex, t1', extras2, hex2, t2']
        have htx2_def' :
            tx2 (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g =
              some (t1, some t2) := by
          simpa [htEq1, htEq2] using htx2_def
        simpa [tx2Realized, g] using htx2_def'
    · -- If there is no second extra, `tx2Plus` returns `some (t1, none, false)`, contradiction.
      have htx_def :
          tx2Plus (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g =
            some (t1', (none : Option α), false) := by
        simp [tx2Plus, w, extras, hex, t1', extras2, hex2]
      have : False := by
        have hsome : some (t1', (none : Option α), false) = some (t1, some t2, b) := by
          simpa [htx_def] using htx'
        have hpair := Option.some.inj hsome
        have hsecond : ((none : Option α), false) = (some t2, b) := congrArg Prod.snd hpair
        have hnone : (none : Option α) = some t2 := congrArg Prod.fst hsecond
        cases hnone
      exact False.elim this
  · -- If `extras` is empty, `tx2Plus` is `none`, contradiction.
    have htx_none :
        tx2Plus (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g = none := by
      simp [tx2Plus, w, extras, hex]
    have : False := by
      have : (none : Option (α × Option α × Bool)) = some (t1, some t2, b) := by
        simpa [htx_none] using htx'
      cases this
    exact False.elim this

theorem A_sdiff_insert_subset_pair_of_tx2PlusRealized_eq_some_some_false
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (gx :
      RealizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked)
    {t1 t2 : α}
    (htx :
      tx2PlusRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked gx =
        some (t1, some t2, false)) :
    let g :=
      toGoodX_of_realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked gx
    let w : BlockedUnionWitness family S g.1 :=
      goodXWitness (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked
        (x := g.1) g.2
    w.A \ insert g.1 S ⊆ ({t1, t2} : Finset α) := by
  classical
  intro g w
  have htx' :
      tx2Plus (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g =
        some (t1, some t2, false) := by
    simpa [tx2PlusRealized] using htx
  let extras : Finset α := w.A \ insert g.1 S
  by_cases hex : extras.Nonempty
  · let t1' : α := Classical.choose hex
    let extras2 : Finset α := extras.erase t1'
    by_cases hex2 : extras2.Nonempty
    · let t2' : α := Classical.choose hex2
      let extras3 : Finset α := extras2.erase t2'
      by_cases hex3 : extras3.Nonempty
      · have htx_def :
            tx2Plus (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g =
              some (t1', some t2', true) := by
          simp [tx2Plus, w, extras, hex, t1', extras2, hex2, t2', extras3, hex3]
        have : False := by
          have hsome : some (t1', some t2', true) = some (t1, some t2, false) := by
            simpa [htx_def] using htx'
          have hpair := Option.some.inj hsome
          have hsecond : (some t2', true) = (some t2, false) := congrArg Prod.snd hpair
          have hbool : true = false := congrArg Prod.snd hsecond
          cases hbool
        exact False.elim this
      · have htx_def :
            tx2Plus (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g =
              some (t1', some t2', false) := by
          simp [tx2Plus, w, extras, hex, t1', extras2, hex2, t2', extras3, hex3]
        have hsome : some (t1', some t2', false) = some (t1, some t2, false) := by
          simpa [htx_def] using htx'
        have hpair := Option.some.inj hsome
        have htEq1 : t1' = t1 := congrArg Prod.fst hpair
        have htEq2 : t2' = t2 := by
          have : (some t2', false) = (some t2, false) := congrArg Prod.snd hpair
          have : some t2' = some t2 := congrArg Prod.fst this
          exact Option.some.inj this
        have hNoMore : extras3 = (∅ : Finset α) := by
          simpa [Finset.not_nonempty_iff_eq_empty] using hex3
        have hNoMore' : (extras.erase t1).erase t2 = (∅ : Finset α) := by
          simpa [extras2, extras3, htEq1, htEq2] using hNoMore
        intro z hz
        by_cases hz1 : z = t1
        · subst hz1
          simp
        · have hzErase1 : z ∈ extras.erase t1 := Finset.mem_erase.mpr ⟨hz1, hz⟩
          by_cases hz2 : z = t2
          · subst hz2
            simp [hz1]
          · have hzErase2 : z ∈ (extras.erase t1).erase t2 := Finset.mem_erase.mpr ⟨hz2, hzErase1⟩
            have : False := by
              have : z ∈ (∅ : Finset α) := by simpa [hNoMore'] using hzErase2
              simpa using this
            exact False.elim this
    · -- If there is no second extra, `tx2Plus` returns `some (t1, none, false)`, contradiction.
      have htx_def :
          tx2Plus (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g =
            some (t1', (none : Option α), false) := by
        simp [tx2Plus, w, extras, hex, t1', extras2, hex2]
      have : False := by
        have hsome : some (t1', (none : Option α), false) = some (t1, some t2, false) := by
          simpa [htx_def] using htx'
        have hpair := Option.some.inj hsome
        have hsecond : ((none : Option α), false) = (some t2, false) := congrArg Prod.snd hpair
        have hnone : (none : Option α) = some t2 := congrArg Prod.fst hsecond
        cases hnone
      exact False.elim this
  · -- If `extras` is empty, `tx2Plus` is `none`, contradiction.
    have htx_none :
        tx2Plus (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g = none := by
      simp [tx2Plus, w, extras, hex]
    have : False := by
      have : (none : Option (α × Option α × Bool)) = some (t1, some t2, false) := by
        simpa [htx_none] using htx'
      cases this
    exact False.elim this

theorem sunflower_contradiction_of_two_realizedGoodX_rtxRealized_none_collision
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    {gx1 gx2 :
      RealizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked}
    (hxne : gx1.1 ≠ gx2.1)
    (hr : rtxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked gx1 =
      rtxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked gx2)
    (htx : txRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked gx1 = none) :
    False := by
  classical
  -- Extract the corresponding `GoodX` and witnesses for each `gx`.
  let g1 :=
    toGoodX_of_realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
      fiber hS hfree hblocked gx1
  let g2 :=
    toGoodX_of_realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
      fiber hS hfree hblocked gx2
  let w1 : BlockedUnionWitness family S gx1.1 :=
    goodXWitness (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked
      (x := gx1.1) g1.2
  let w2 : BlockedUnionWitness family S gx2.1 :=
    goodXWitness (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked
      (x := gx2.1) g2.2
  -- The collided core value (first component of `rtxRealized`) will be the sunflower core.
  let r :
      Finset α :=
    (rtxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked gx1).1
  have hr1 :
      rxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked gx1 = r := by
    rfl
  have hr2 :
      rxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked gx2 = r := by
    -- First components are equal under `hr`.
    have : (rtxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked gx2).1 = r := by
      simpa [r] using congrArg Prod.fst hr.symm
    simpa [rtxRealized, r] using this
  -- Both traces are `none`, so the witness sets have no extra elements outside `S ∪ {x}`.
  have htx2 :
      txRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked gx2 = none := by
    have hEq :
        txRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked gx2 =
          txRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked gx1 := by
      simpa [rtxRealized] using (congrArg Prod.snd hr).symm
    exact hEq.trans htx
  have hsub1 : w1.A ⊆ insert gx1.1 S := by
    simpa [g1, w1] using
      A_subset_insert_of_txRealized_eq_none (family := family) (dom := dom) (S := S) (X := X)
        (h0 := h0) (fiber := fiber) hS hfree hblocked gx1 htx
  have hsub2 : w2.A ⊆ insert gx2.1 S := by
    simpa [g2, w2] using
      A_subset_insert_of_txRealized_eq_none (family := family) (dom := dom) (S := S) (X := X)
        (h0 := h0) (fiber := fiber) hS hfree hblocked gx2 htx2
  -- `x1` and `x2` are not in `S` because they are realized (they come from `T \\ S`).
  have hxReal1 :
      gx1.1 ∈ realizedXSet (dom := dom) fiber S X :=
    (mem_realizedGoodXSet_iff (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked).1 gx1.2 |>.1
  have hxReal2 :
      gx2.1 ∈ realizedXSet (dom := dom) fiber S X :=
    (mem_realizedGoodXSet_iff (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked).1 gx2.2 |>.1
  have hxnot1 : gx1.1 ∉ S := mem_realizedXSet_imp_not_mem_S (dom := dom) (fiber := fiber) hxReal1
  have hxnot2 : gx2.1 ∉ S := mem_realizedXSet_imp_not_mem_S (dom := dom) (fiber := fiber) hxReal2
  -- Intersections with `S` match the collided core value `r`.
  have hAS1 : w1.A ∩ S = r := by
    have hcore :
        w1.A ∩ S = w1.core.erase gx1.1 :=
      inter_left_eq_core_erase_of_blockedUnionWitness_of_mem_core_of_not_mem_S
        (family := family) (S := S) (x := gx1.1) w1 hxnot1
    -- `rxRealized gx1` reduces to `w1.core.erase gx1.1` under our chosen witness `w1`.
    have hrx_w1 :
        rxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked gx1 = w1.core.erase gx1.1 := by
      simp [rxRealized, w1]
    calc
      w1.A ∩ S = w1.core.erase gx1.1 := hcore
      _ = rxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked gx1 := hrx_w1.symm
      _ = r := by simp [r, rtxRealized]
  have hAS2 : w2.A ∩ S = r := by
    have hcore :
        w2.A ∩ S = w2.core.erase gx2.1 :=
      inter_left_eq_core_erase_of_blockedUnionWitness_of_mem_core_of_not_mem_S
        (family := family) (S := S) (x := gx2.1) w2 hxnot2
    have hrx_w2 :
        rxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked gx2 = w2.core.erase gx2.1 := by
      simp [rxRealized, w2]
    calc
      w2.A ∩ S = w2.core.erase gx2.1 := hcore
      _ = rxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked gx2 := hrx_w2.symm
      _ = r := hr2
  -- Compute the intersection of `w1.A` and `w2.A`: it lies in `S`, hence in `r`.
  have hA12_sub : w1.A ∩ w2.A ⊆ r := by
    intro z hz
    have hzS : z ∈ S := by
      have hz1 : z ∈ insert gx1.1 S := hsub1 (Finset.mem_inter.mp hz).1
      have hz2 : z ∈ insert gx2.1 S := hsub2 (Finset.mem_inter.mp hz).2
      rcases Finset.mem_insert.mp hz1 with hz1S | hz1S
      · -- `z = x1`; but then `z ∈ insert x2 S` forces `z ∈ S` since `x1 ≠ x2` and `x2 ∉ S`.
        subst hz1S
        rcases Finset.mem_insert.mp hz2 with hzEq | hzS
        · exact False.elim (hxne hzEq)
        · exact hzS
      · exact hz1S
    have hzR : z ∈ w1.A ∩ S := Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hz).1, hzS⟩
    -- Rewrite `w1.A ∩ S` as `r`.
    simpa [hAS1] using hzR
  have hA12_sup : r ⊆ w1.A ∩ w2.A := by
    intro z hz
    have hz1 : z ∈ w1.A := (Finset.mem_inter.mp (by simpa [hAS1] using hz : z ∈ w1.A ∩ S)).1
    have hz2 : z ∈ w2.A := (Finset.mem_inter.mp (by simpa [hAS2] using hz : z ∈ w2.A ∩ S)).1
    exact Finset.mem_inter.mpr ⟨hz1, hz2⟩
  have hA12 : w1.A ∩ w2.A = r := by
    exact Finset.Subset.antisymm hA12_sub hA12_sup
  -- Distinctness: each witness contains its own `x`,
  -- and `tx = none` prevents it from containing the other.
  have hxA1 : gx1.1 ∈ w1.A := by
    have hxGood : gx1.1 ∈ goodXSet (family := family) S X h0 hS hfree hblocked := g1.2
    simpa [g1, w1] using
      mem_A_of_goodXWitness (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked
        (x := gx1.1) hxGood
  have hxA2 : gx2.1 ∈ w2.A := by
    have hxGood : gx2.1 ∈ goodXSet (family := family) S X h0 hS hfree hblocked := g2.2
    simpa [g2, w2] using
      mem_A_of_goodXWitness (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked
        (x := gx2.1) hxGood
  have hS_ne_A1 : S ≠ w1.A := by
    intro hEq
    have : gx1.1 ∈ S := by simpa [hEq] using hxA1
    exact hxnot1 this
  have hS_ne_A2 : S ≠ w2.A := by
    intro hEq
    have : gx2.1 ∈ S := by simpa [hEq] using hxA2
    exact hxnot2 this
  have hA12_ne : w1.A ≠ w2.A := by
    intro hEq
    have : gx1.1 ∈ insert gx2.1 S := hsub2 (by simpa [hEq] using hxA1)
    rcases Finset.mem_insert.mp this with hEq' | hInS
    · exact hxne hEq'
    · exact hxnot1 hInS
  -- Finish: {S, w1.A, w2.A} is a 3-sunflower with core `r`.
  exact
    sunflower_contradiction_of_three_sets (family := family) hfree
      (S1 := S) (S2 := w1.A) (S3 := w2.A) (core := r)
      hS w1.hA w2.hA
      (by simpa [Finset.inter_comm] using hAS1) (by simpa [Finset.inter_comm] using hAS2) hA12
      hS_ne_A1 hS_ne_A2 hA12_ne

theorem realizedGoodX_eq_of_rtxRealized_eq_of_txRealized_eq_none
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    {gx1 gx2 :
      RealizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked}
    (hr :
      rtxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked gx1 =
        rtxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked gx2)
    (htx :
      txRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked gx1 = none) :
    gx1 = gx2 := by
  classical
  have hxval : gx1.1 = gx2.1 := by
    by_contra hxne
    exact
      sunflower_contradiction_of_two_realizedGoodX_rtxRealized_none_collision
        (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        (fiber := fiber) hS hfree hblocked hxne hr htx
  ext
  exact hxval

theorem card_filter_rtxRealized_eq_pair_none_le_one
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (r : Finset α) :
    ((realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked).filter (fun gx =>
          rtxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
              fiber hS hfree hblocked gx = (r, (none : Option α)))).card ≤ 1 := by
  classical
  -- Use `Finset.card_le_one` via uniqueness: any two members have the same `rtxRealized` value
  -- with `tx = none`, hence are equal.
  refine (Finset.card_le_one).2 ?_
  intro gx1 hgx1 gx2 hgx2
  have hrtx1 :
      rtxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked gx1 =
        (r, (none : Option α)) := by
    exact (Finset.mem_filter.mp hgx1).2
  have hrtx2 :
      rtxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked gx2 =
        (r, (none : Option α)) := by
    exact (Finset.mem_filter.mp hgx2).2
  have htx1 :
      txRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked gx1 = none := by
    have := congrArg Prod.snd hrtx1
    simpa [rtxRealized] using this
  have hr :
      rtxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked gx1 =
        rtxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked gx2 := by
    exact hrtx1.trans hrtx2.symm
  exact
    realizedGoodX_eq_of_rtxRealized_eq_of_txRealized_eq_none
      (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
      (fiber := fiber) hS hfree hblocked hr htx1

theorem sunflower_contradiction_of_three_realizedGoodX_rtx2Realized_some_none_collision
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    {r : Finset α} {t1 : α}
    {gx1 gx2 gx3 :
      RealizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked}
    (hx12 : gx1.1 ≠ gx2.1) (hx13 : gx1.1 ≠ gx3.1) (hx23 : gx2.1 ≠ gx3.1)
    (h1 :
      rtx2Realized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked gx1 =
        (r, some (t1, (none : Option α))))
    (h2 :
      rtx2Realized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked gx2 =
        (r, some (t1, (none : Option α))))
    (h3 :
      rtx2Realized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked gx3 =
        (r, some (t1, (none : Option α)))) :
    False := by
  classical
  -- Extract witnesses.
  let g1 :=
    toGoodX_of_realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
      fiber hS hfree hblocked gx1
  let g2 :=
    toGoodX_of_realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
      fiber hS hfree hblocked gx2
  let g3 :=
    toGoodX_of_realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
      fiber hS hfree hblocked gx3
  let w1 : BlockedUnionWitness family S gx1.1 :=
    goodXWitness (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked
      (x := gx1.1) g1.2
  let w2 : BlockedUnionWitness family S gx2.1 :=
    goodXWitness (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked
      (x := gx2.1) g2.2
  let w3 : BlockedUnionWitness family S gx3.1 :=
    goodXWitness (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked
      (x := gx3.1) g3.2
  -- Realized elements are not in `S`.
  have hxReal1 :
      gx1.1 ∈ realizedXSet (dom := dom) fiber S X :=
    (mem_realizedGoodXSet_iff (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked).1 gx1.2 |>.1
  have hxReal2 :
      gx2.1 ∈ realizedXSet (dom := dom) fiber S X :=
    (mem_realizedGoodXSet_iff (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked).1 gx2.2 |>.1
  have hxReal3 :
      gx3.1 ∈ realizedXSet (dom := dom) fiber S X :=
    (mem_realizedGoodXSet_iff (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked).1 gx3.2 |>.1
  have hxnot1 : gx1.1 ∉ S := mem_realizedXSet_imp_not_mem_S (dom := dom) (fiber := fiber) hxReal1
  have hxnot2 : gx2.1 ∉ S := mem_realizedXSet_imp_not_mem_S (dom := dom) (fiber := fiber) hxReal2
  have hxnot3 : gx3.1 ∉ S := mem_realizedXSet_imp_not_mem_S (dom := dom) (fiber := fiber) hxReal3
  -- Each `A`-witness meets `S` in exactly `r`.
  have hAS1 : w1.A ∩ S = r := by
    have hcore :
        w1.A ∩ S = w1.core.erase gx1.1 :=
      inter_left_eq_core_erase_of_blockedUnionWitness_of_mem_core_of_not_mem_S
        (family := family) (S := S) (x := gx1.1) w1 hxnot1
    have hrx_w1 :
        rxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked gx1 = w1.core.erase gx1.1 := by
      simp [rxRealized, w1]
    calc
      w1.A ∩ S = w1.core.erase gx1.1 := hcore
      _ = rxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked gx1 := hrx_w1.symm
      _ = r := by
            have : (rtx2Realized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
                fiber hS hfree hblocked gx1).1 = r := by
              simpa [h1] using congrArg Prod.fst h1
            simpa [rtx2Realized] using this
  have hAS2 : w2.A ∩ S = r := by
    have hcore :
        w2.A ∩ S = w2.core.erase gx2.1 :=
      inter_left_eq_core_erase_of_blockedUnionWitness_of_mem_core_of_not_mem_S
        (family := family) (S := S) (x := gx2.1) w2 hxnot2
    have hrx_w2 :
        rxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked gx2 = w2.core.erase gx2.1 := by
      simp [rxRealized, w2]
    calc
      w2.A ∩ S = w2.core.erase gx2.1 := hcore
      _ = rxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked gx2 := hrx_w2.symm
      _ = r := by
            have : (rtx2Realized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
                fiber hS hfree hblocked gx2).1 = r := by
              simpa [h2] using congrArg Prod.fst h2
            simpa [rtx2Realized] using this
  have hAS3 : w3.A ∩ S = r := by
    have hcore :
        w3.A ∩ S = w3.core.erase gx3.1 :=
      inter_left_eq_core_erase_of_blockedUnionWitness_of_mem_core_of_not_mem_S
        (family := family) (S := S) (x := gx3.1) w3 hxnot3
    have hrx_w3 :
        rxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked gx3 = w3.core.erase gx3.1 := by
      simp [rxRealized, w3]
    calc
      w3.A ∩ S = w3.core.erase gx3.1 := hcore
      _ = rxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked gx3 := hrx_w3.symm
      _ = r := by
            have : (rtx2Realized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
                fiber hS hfree hblocked gx3).1 = r := by
              simpa [h3] using congrArg Prod.fst h3
            simpa [rtx2Realized] using this
  -- Each witness has trace `some (t1, none)`, so its extra part is exactly `{t1}`.
  have htx1 :
      tx2Realized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked gx1 = some (t1, (none : Option α)) := by
    have : (rtx2Realized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked gx1).2 = some (t1, (none : Option α)) := by
      simpa [h1] using congrArg Prod.snd h1
    simpa [rtx2Realized] using this
  have htx2 :
      tx2Realized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked gx2 = some (t1, (none : Option α)) := by
    have : (rtx2Realized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked gx2).2 = some (t1, (none : Option α)) := by
      simpa [h2] using congrArg Prod.snd h2
    simpa [rtx2Realized] using this
  have htx3 :
      tx2Realized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked gx3 = some (t1, (none : Option α)) := by
    have : (rtx2Realized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked gx3).2 = some (t1, (none : Option α)) := by
      simpa [h3] using congrArg Prod.snd h3
    simpa [rtx2Realized] using this
  -- Membership of `t1` in each witness, and `t1 ∉ insert x S`.
  have htA1 : t1 ∈ w1.A := by
    simpa [g1, w1] using
      mem_A_of_tx2Realized_eq_some_fst (family := family) (dom := dom) (S := S) (X := X)
        (h0 := h0) (fiber := fiber) hS hfree hblocked gx1 htx1
  have htA2 : t1 ∈ w2.A := by
    simpa [g2, w2] using
      mem_A_of_tx2Realized_eq_some_fst (family := family) (dom := dom) (S := S) (X := X)
        (h0 := h0) (fiber := fiber) hS hfree hblocked gx2 htx2
  have htA3 : t1 ∈ w3.A := by
    simpa [g3, w3] using
      mem_A_of_tx2Realized_eq_some_fst (family := family) (dom := dom) (S := S) (X := X)
        (h0 := h0) (fiber := fiber) hS hfree hblocked gx3 htx3
  have htt1 : t1 ∉ S := by
    -- `t1 ∉ insert x S` for any `x` implies `t1 ∉ S`.
    have : t1 ∉ insert gx1.1 S := by
      simpa [g1] using
        not_mem_insert_of_tx2Realized_eq_some_fst (family := family) (dom := dom) (S := S) (X := X)
          (h0 := h0) (fiber := fiber) hS hfree hblocked gx1 htx1
    intro htS
    exact this (Finset.mem_insert_of_mem htS)
  -- In the `tx2 = some (t1, none)` bucket, the extra part of each witness is contained in `{t1}`.
  have hsub1 : w1.A \ insert gx1.1 S ⊆ ({t1} : Finset α) := by
    simpa [g1, w1] using
      A_sdiff_insert_subset_singleton_of_tx2Realized_eq_some_none (family := family) (dom := dom)
        (S := S) (X := X) (h0 := h0) (fiber := fiber) hS hfree hblocked gx1 htx1
  have hsub2 : w2.A \ insert gx2.1 S ⊆ ({t1} : Finset α) := by
    simpa [g2, w2] using
      A_sdiff_insert_subset_singleton_of_tx2Realized_eq_some_none (family := family) (dom := dom)
        (S := S) (X := X) (h0 := h0) (fiber := fiber) hS hfree hblocked gx2 htx2
  have hsub3 : w3.A \ insert gx3.1 S ⊆ ({t1} : Finset α) := by
    simpa [g3, w3] using
      A_sdiff_insert_subset_singleton_of_tx2Realized_eq_some_none (family := family) (dom := dom)
        (S := S) (X := X) (h0 := h0) (fiber := fiber) hS hfree hblocked gx3 htx3
  -- Pairwise intersection identities: `wᵢ.A ∩ wⱼ.A = insert t1 r`.
  have hA12 : w1.A ∩ w2.A = insert t1 r := by
    apply Finset.Subset.antisymm
    · intro z hz
      have hz1 : z ∈ w1.A := (Finset.mem_inter.mp hz).1
      have hz2 : z ∈ w2.A := (Finset.mem_inter.mp hz).2
      by_cases hzT : z = t1
      · subst hzT
        simp
      · have hzIns1 : z ∈ insert gx1.1 S := by
          by_contra hzNot
          have hzDiff : z ∈ w1.A \ insert gx1.1 S := Finset.mem_sdiff.mpr ⟨hz1, hzNot⟩
          have : z ∈ ({t1} : Finset α) := hsub1 hzDiff
          exact hzT (Finset.mem_singleton.mp this)
        have hzIns2 : z ∈ insert gx2.1 S := by
          by_contra hzNot
          have hzDiff : z ∈ w2.A \ insert gx2.1 S := Finset.mem_sdiff.mpr ⟨hz2, hzNot⟩
          have : z ∈ ({t1} : Finset α) := hsub2 hzDiff
          exact hzT (Finset.mem_singleton.mp this)
        have hzS : z ∈ S := by
          rcases Finset.mem_insert.mp hzIns1 with hzEq1 | hzS1
          · subst hzEq1
            rcases Finset.mem_insert.mp hzIns2 with hzEq2 | hzS2
            · exact False.elim (hx12 hzEq2)
            · exact False.elim (hxnot1 hzS2)
          · exact hzS1
        have hzR : z ∈ r := by
          have : z ∈ w1.A ∩ S := Finset.mem_inter.mpr ⟨hz1, hzS⟩
          simpa [hAS1] using this
        simp [hzR, hzT]
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hzR
      · exact Finset.mem_inter.mpr ⟨htA1, htA2⟩
      · have hz1 : z ∈ w1.A :=
          (Finset.mem_inter.mp (by simpa [hAS1] using hzR : z ∈ w1.A ∩ S)).1
        have hz2 : z ∈ w2.A :=
          (Finset.mem_inter.mp (by simpa [hAS2] using hzR : z ∈ w2.A ∩ S)).1
        exact Finset.mem_inter.mpr ⟨hz1, hz2⟩
  have hA13 : w1.A ∩ w3.A = insert t1 r := by
    apply Finset.Subset.antisymm
    · intro z hz
      have hz1 : z ∈ w1.A := (Finset.mem_inter.mp hz).1
      have hz3 : z ∈ w3.A := (Finset.mem_inter.mp hz).2
      by_cases hzT : z = t1
      · subst hzT
        simp
      · have hzIns1 : z ∈ insert gx1.1 S := by
          by_contra hzNot
          have hzDiff : z ∈ w1.A \ insert gx1.1 S := Finset.mem_sdiff.mpr ⟨hz1, hzNot⟩
          have : z ∈ ({t1} : Finset α) := hsub1 hzDiff
          exact hzT (Finset.mem_singleton.mp this)
        have hzIns3 : z ∈ insert gx3.1 S := by
          by_contra hzNot
          have hzDiff : z ∈ w3.A \ insert gx3.1 S := Finset.mem_sdiff.mpr ⟨hz3, hzNot⟩
          have : z ∈ ({t1} : Finset α) := hsub3 hzDiff
          exact hzT (Finset.mem_singleton.mp this)
        have hzS : z ∈ S := by
          rcases Finset.mem_insert.mp hzIns1 with hzEq1 | hzS1
          · subst hzEq1
            rcases Finset.mem_insert.mp hzIns3 with hzEq3 | hzS3
            · exact False.elim (hx13 hzEq3)
            · exact False.elim (hxnot1 hzS3)
          · exact hzS1
        have hzR : z ∈ r := by
          have : z ∈ w1.A ∩ S := Finset.mem_inter.mpr ⟨hz1, hzS⟩
          simpa [hAS1] using this
        simp [hzR, hzT]
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hzR
      · exact Finset.mem_inter.mpr ⟨htA1, htA3⟩
      · have hz1 : z ∈ w1.A :=
          (Finset.mem_inter.mp (by simpa [hAS1] using hzR : z ∈ w1.A ∩ S)).1
        have hz3 : z ∈ w3.A :=
          (Finset.mem_inter.mp (by simpa [hAS3] using hzR : z ∈ w3.A ∩ S)).1
        exact Finset.mem_inter.mpr ⟨hz1, hz3⟩
  have hA23 : w2.A ∩ w3.A = insert t1 r := by
    apply Finset.Subset.antisymm
    · intro z hz
      have hz2 : z ∈ w2.A := (Finset.mem_inter.mp hz).1
      have hz3 : z ∈ w3.A := (Finset.mem_inter.mp hz).2
      by_cases hzT : z = t1
      · subst hzT
        simp
      · have hzIns2 : z ∈ insert gx2.1 S := by
          by_contra hzNot
          have hzDiff : z ∈ w2.A \ insert gx2.1 S := Finset.mem_sdiff.mpr ⟨hz2, hzNot⟩
          have : z ∈ ({t1} : Finset α) := hsub2 hzDiff
          exact hzT (Finset.mem_singleton.mp this)
        have hzIns3 : z ∈ insert gx3.1 S := by
          by_contra hzNot
          have hzDiff : z ∈ w3.A \ insert gx3.1 S := Finset.mem_sdiff.mpr ⟨hz3, hzNot⟩
          have : z ∈ ({t1} : Finset α) := hsub3 hzDiff
          exact hzT (Finset.mem_singleton.mp this)
        have hzS : z ∈ S := by
          rcases Finset.mem_insert.mp hzIns2 with hzEq2 | hzS2
          · subst hzEq2
            rcases Finset.mem_insert.mp hzIns3 with hzEq3 | hzS3
            · exact False.elim (hx23 hzEq3)
            · exact False.elim (hxnot2 hzS3)
          · exact hzS2
        have hzR : z ∈ r := by
          have : z ∈ w2.A ∩ S := Finset.mem_inter.mpr ⟨hz2, hzS⟩
          simpa [hAS2] using this
        simp [hzR, hzT]
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hzR
      · exact Finset.mem_inter.mpr ⟨htA2, htA3⟩
      · have hz2 : z ∈ w2.A :=
          (Finset.mem_inter.mp (by simpa [hAS2] using hzR : z ∈ w2.A ∩ S)).1
        have hz3 : z ∈ w3.A :=
          (Finset.mem_inter.mp (by simpa [hAS3] using hzR : z ∈ w3.A ∩ S)).1
        exact Finset.mem_inter.mpr ⟨hz2, hz3⟩
  -- Contradiction: `{w1.A, w2.A, w3.A}` forms a 3-sunflower inside `family`.
  have hsub : ({w1.A, w2.A, w3.A} : Finset (Finset α)) ⊆ family := by
    intro T hT
    have hT' : T = w1.A ∨ T = w2.A ∨ T = w3.A := by
      simpa using (Finset.mem_insert.mp hT)
    rcases hT' with rfl | hT'
    · exact w1.hA
    rcases hT' with rfl | rfl
    · exact w2.hA
    · exact w3.hA
  have hsun : IsSunflower ({w1.A, w2.A, w3.A} : Finset (Finset α)) 3 := by
    refine ⟨?_, ?_⟩
    · -- card = 3: the three witness sets are distinct (each contains its own realized `x`).
      have hxA1 : gx1.1 ∈ w1.A := by
        have hxcore : gx1.1 ∈ w1.core :=
          mem_core_of_goodXWitness (family := family) (S := S) (X := X) (h0 := h0)
            (hS := hS) (hfree := hfree) (hblocked := hblocked) g1.2
        have hxAT : gx1.1 ∈ w1.A ∩ (S ∪ ({gx1.1} : Finset α)) := by
          have hx' := hxcore
          rw [← w1.hcoreAT] at hx'
          exact hx'
        exact (Finset.mem_inter.mp hxAT).1
      have hxA2 : gx2.1 ∈ w2.A := by
        have hxcore : gx2.1 ∈ w2.core :=
          mem_core_of_goodXWitness (family := family) (S := S) (X := X) (h0 := h0)
            (hS := hS) (hfree := hfree) (hblocked := hblocked) g2.2
        have hxAT : gx2.1 ∈ w2.A ∩ (S ∪ ({gx2.1} : Finset α)) := by
          have hx' := hxcore
          rw [← w2.hcoreAT] at hx'
          exact hx'
        exact (Finset.mem_inter.mp hxAT).1
      have hxA3 : gx3.1 ∈ w3.A := by
        have hxcore : gx3.1 ∈ w3.core :=
          mem_core_of_goodXWitness (family := family) (S := S) (X := X) (h0 := h0)
            (hS := hS) (hfree := hfree) (hblocked := hblocked) g3.2
        have hxAT : gx3.1 ∈ w3.A ∩ (S ∪ ({gx3.1} : Finset α)) := by
          have hx' := hxcore
          rw [← w3.hcoreAT] at hx'
          exact hx'
        exact (Finset.mem_inter.mp hxAT).1
      have htNotIns1 : t1 ∉ insert gx1.1 S := by
        simpa [g1] using
          not_mem_insert_of_tx2Realized_eq_some_fst (family := family) (dom := dom) (S := S) (X := X)
            (h0 := h0) (fiber := fiber) hS hfree hblocked gx1 htx1
      have htNotIns2 : t1 ∉ insert gx2.1 S := by
        simpa [g2] using
          not_mem_insert_of_tx2Realized_eq_some_fst (family := family) (dom := dom) (S := S) (X := X)
            (h0 := h0) (fiber := fiber) hS hfree hblocked gx2 htx2
      have htNotIns3 : t1 ∉ insert gx3.1 S := by
        simpa [g3] using
          not_mem_insert_of_tx2Realized_eq_some_fst (family := family) (dom := dom) (S := S) (X := X)
            (h0 := h0) (fiber := fiber) hS hfree hblocked gx3 htx3
      have hx1_ne_t1 : gx1.1 ≠ t1 := by
        intro hxEq; subst hxEq
        exact htNotIns1 (Finset.mem_insert_self _ _)
      have hx2_ne_t1 : gx2.1 ≠ t1 := by
        intro hxEq; subst hxEq
        exact htNotIns2 (Finset.mem_insert_self _ _)
      have hx3_ne_t1 : gx3.1 ≠ t1 := by
        intro hxEq; subst hxEq
        exact htNotIns3 (Finset.mem_insert_self _ _)
      have hxnotIns12 : gx1.1 ∉ insert gx2.1 S := by
        intro hxIn
        rcases Finset.mem_insert.mp hxIn with hxEq | hxInS
        · exact hx12 hxEq
        · exact hxnot1 hxInS
      have hxnotIns13 : gx1.1 ∉ insert gx3.1 S := by
        intro hxIn
        rcases Finset.mem_insert.mp hxIn with hxEq | hxInS
        · exact hx13 hxEq
        · exact hxnot1 hxInS
      have hxnotIns21 : gx2.1 ∉ insert gx1.1 S := by
        intro hxIn
        rcases Finset.mem_insert.mp hxIn with hxEq | hxInS
        · exact hx12 hxEq.symm
        · exact hxnot2 hxInS
      have hxnotIns23 : gx2.1 ∉ insert gx3.1 S := by
        intro hxIn
        rcases Finset.mem_insert.mp hxIn with hxEq | hxInS
        · exact hx23 hxEq
        · exact hxnot2 hxInS
      have hxnotIns31 : gx3.1 ∉ insert gx1.1 S := by
        intro hxIn
        rcases Finset.mem_insert.mp hxIn with hxEq | hxInS
        · exact hx13 hxEq.symm
        · exact hxnot3 hxInS
      have hxnotIns32 : gx3.1 ∉ insert gx2.1 S := by
        intro hxIn
        rcases Finset.mem_insert.mp hxIn with hxEq | hxInS
        · exact hx23 hxEq.symm
        · exact hxnot3 hxInS
      have hxA1_not2 : gx1.1 ∉ w2.A := by
        intro hxIn
        have hxDiff : gx1.1 ∈ w2.A \ insert gx2.1 S := Finset.mem_sdiff.mpr ⟨hxIn, hxnotIns12⟩
        have : gx1.1 ∈ ({t1} : Finset α) := hsub2 hxDiff
        exact hx1_ne_t1 (Finset.mem_singleton.mp this)
      have hxA1_not3 : gx1.1 ∉ w3.A := by
        intro hxIn
        have hxDiff : gx1.1 ∈ w3.A \ insert gx3.1 S := Finset.mem_sdiff.mpr ⟨hxIn, hxnotIns13⟩
        have : gx1.1 ∈ ({t1} : Finset α) := hsub3 hxDiff
        exact hx1_ne_t1 (Finset.mem_singleton.mp this)
      have hxA2_not1 : gx2.1 ∉ w1.A := by
        intro hxIn
        have hxDiff : gx2.1 ∈ w1.A \ insert gx1.1 S := Finset.mem_sdiff.mpr ⟨hxIn, hxnotIns21⟩
        have : gx2.1 ∈ ({t1} : Finset α) := hsub1 hxDiff
        exact hx2_ne_t1 (Finset.mem_singleton.mp this)
      have hxA2_not3 : gx2.1 ∉ w3.A := by
        intro hxIn
        have hxDiff : gx2.1 ∈ w3.A \ insert gx3.1 S := Finset.mem_sdiff.mpr ⟨hxIn, hxnotIns23⟩
        have : gx2.1 ∈ ({t1} : Finset α) := hsub3 hxDiff
        exact hx2_ne_t1 (Finset.mem_singleton.mp this)
      have hxA3_not1 : gx3.1 ∉ w1.A := by
        intro hxIn
        have hxDiff : gx3.1 ∈ w1.A \ insert gx1.1 S := Finset.mem_sdiff.mpr ⟨hxIn, hxnotIns31⟩
        have : gx3.1 ∈ ({t1} : Finset α) := hsub1 hxDiff
        exact hx3_ne_t1 (Finset.mem_singleton.mp this)
      have hxA3_not2 : gx3.1 ∉ w2.A := by
        intro hxIn
        have hxDiff : gx3.1 ∈ w2.A \ insert gx2.1 S := Finset.mem_sdiff.mpr ⟨hxIn, hxnotIns32⟩
        have : gx3.1 ∈ ({t1} : Finset α) := hsub2 hxDiff
        exact hx3_ne_t1 (Finset.mem_singleton.mp this)
      have hA12_ne : w1.A ≠ w2.A := by
        intro hEq
        have : gx1.1 ∈ w2.A := by simpa [hEq] using hxA1
        exact hxA1_not2 this
      have hA13_ne : w1.A ≠ w3.A := by
        intro hEq
        have : gx1.1 ∈ w3.A := by simpa [hEq] using hxA1
        exact hxA1_not3 this
      have hA23_ne : w2.A ≠ w3.A := by
        intro hEq
        have : gx2.1 ∈ w3.A := by simpa [hEq] using hxA2
        exact hxA2_not3 this
      have hBnot : w2.A ∉ ({w3.A} : Finset (Finset α)) := by
        simp [hA23_ne]
      have hAnot : w1.A ∉ insert w2.A ({w3.A} : Finset (Finset α)) := by
        simp [hA12_ne, hA13_ne]
      have hcardB : (insert w2.A ({w3.A} : Finset (Finset α))).card = 2 := by
        simp [Finset.card_insert_of_notMem, hBnot]
      have hcard : (insert w1.A (insert w2.A ({w3.A} : Finset (Finset α)))).card = 3 := by
        calc
          (insert w1.A (insert w2.A ({w3.A} : Finset (Finset α)))).card =
              (insert w2.A ({w3.A} : Finset (Finset α))).card + 1 := by
                simp [Finset.card_insert_of_notMem, hAnot]
          _ = 3 := by simp [hcardB]
      simpa using hcard
    · refine ⟨insert t1 r, ?_⟩
      intro A B hA hB hAB
      have hA' : A = w1.A ∨ A = w2.A ∨ A = w3.A := by
        simpa using (Finset.mem_insert.mp hA)
      have hB' : B = w1.A ∨ B = w2.A ∨ B = w3.A := by
        simpa using (Finset.mem_insert.mp hB)
      rcases hA' with rfl | hA'
      · rcases hB' with rfl | hB'
        · exact False.elim (hAB rfl)
        rcases hB' with rfl | rfl
        · exact hA12
        · exact hA13
      rcases hA' with rfl | rfl
      · rcases hB' with rfl | hB'
        · simpa [Finset.inter_comm] using hA12
        rcases hB' with rfl | rfl
        · exact False.elim (hAB rfl)
        · exact hA23
      · rcases hB' with rfl | hB'
        · simpa [Finset.inter_comm] using hA13
        rcases hB' with rfl | rfl
        · simpa [Finset.inter_comm] using hA23
        · exact False.elim (hAB rfl)
  exact hfree ({w1.A, w2.A, w3.A} : Finset (Finset α)) hsub hsun

theorem card_filter_rtx2Realized_eq_pair_some_none_le_two
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (r : Finset α) (t1 : α) :
    ((realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked).filter (fun gx =>
          rtx2Realized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
              fiber hS hfree hblocked gx = (r, some (t1, (none : Option α))))).card ≤ 2 := by
  classical
  by_contra h
  have hlt : 2 < ((realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked).filter (fun gx =>
          rtx2Realized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
              fiber hS hfree hblocked gx = (r, some (t1, (none : Option α))))).card := by
    exact Nat.lt_of_not_ge h
  have h3 :
      3 ≤ ((realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked).filter (fun gx =>
          rtx2Realized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
              fiber hS hfree hblocked gx = (r, some (t1, (none : Option α))))).card :=
    Nat.succ_le_of_lt hlt
  rcases exists_three_mem_pairwise_ne_of_card_ge_three (F := (realizedGoodX (family := family)
        (dom := dom) (S := S) (X := X) (h0 := h0) fiber hS hfree hblocked).filter (fun gx =>
        rtx2Realized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked gx = (r, some (t1, (none : Option α))))) h3 with
    ⟨gx1, gx2, gx3, hgx1, hgx2, hgx3, hx12, hx13, hx23⟩
  have hx12' : gx1.1 ≠ gx2.1 := by
    intro hEq
    apply hx12
    ext
    exact hEq
  have hx13' : gx1.1 ≠ gx3.1 := by
    intro hEq
    apply hx13
    ext
    exact hEq
  have hx23' : gx2.1 ≠ gx3.1 := by
    intro hEq
    apply hx23
    ext
    exact hEq
  have h1 : rtx2Realized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked gx1 = (r, some (t1, (none : Option α))) :=
    (Finset.mem_filter.mp hgx1).2
  have h2 : rtx2Realized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked gx2 = (r, some (t1, (none : Option α))) :=
    (Finset.mem_filter.mp hgx2).2
  have h3' : rtx2Realized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked gx3 = (r, some (t1, (none : Option α))) :=
    (Finset.mem_filter.mp hgx3).2
  exact
    sunflower_contradiction_of_three_realizedGoodX_rtx2Realized_some_none_collision
      (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
      (fiber := fiber) hS hfree hblocked hx12' hx13' hx23' h1 h2 h3'

theorem tx2Realized_eq_some_none_of_tx2PlusRealized_eq_some_none_false
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (gx :
      RealizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked)
    {t1 : α}
    (htx :
      tx2PlusRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked gx =
        some (t1, (none : Option α), false)) :
    tx2Realized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked gx =
      some (t1, (none : Option α)) := by
  classical
  let g :=
    toGoodX_of_realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
      fiber hS hfree hblocked gx
  let w : BlockedUnionWitness family S g.1 :=
    goodXWitness (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked
      (x := g.1) g.2
  have htx' :
      tx2Plus (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g =
        some (t1, (none : Option α), false) := by
    simpa [tx2PlusRealized] using htx
  let extras : Finset α := w.A \ insert g.1 S
  by_cases hex : extras.Nonempty
  · let t1' : α := Classical.choose hex
    let extras2 : Finset α := extras.erase t1'
    by_cases hex2 : extras2.Nonempty
    · -- If a second extra exists, `tx2Plus` returns `some (t1', some t2', _)`, contradiction.
      let t2' : α := Classical.choose hex2
      let extras3 : Finset α := extras2.erase t2'
      by_cases hex3 : extras3.Nonempty
      · have htx_def :
            tx2Plus (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g =
              some (t1', some t2', true) := by
          simp [tx2Plus, w, extras, hex, t1', extras2, hex2, t2', extras3, hex3]
        have hsome : some (t1', some t2', true) = some (t1, (none : Option α), false) := by
          simpa [htx_def] using htx'
        have hpair := Option.some.inj hsome
        have hsecond : (some t2', true) = ((none : Option α), false) := congrArg Prod.snd hpair
        have hnone : (some t2' : Option α) = none := congrArg Prod.fst hsecond
        cases hnone
      · have htx_def :
            tx2Plus (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g =
              some (t1', some t2', false) := by
          simp [tx2Plus, w, extras, hex, t1', extras2, hex2, t2', extras3, hex3]
        have hsome : some (t1', some t2', false) = some (t1, (none : Option α), false) := by
          simpa [htx_def] using htx'
        have hpair := Option.some.inj hsome
        have hsecond : (some t2', false) = ((none : Option α), false) := congrArg Prod.snd hpair
        have hnone : (some t2' : Option α) = none := congrArg Prod.fst hsecond
        cases hnone
    · -- No second extra: both `tx2Plus` and `tx2` pick the same first extra and stop.
      have htx_def :
          tx2Plus (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g =
            some (t1', (none : Option α), false) := by
        simp [tx2Plus, w, extras, hex, t1', extras2, hex2]
      have hsome : some (t1', (none : Option α), false) = some (t1, (none : Option α), false) := by
        simpa [htx_def] using htx'
      have hpair := Option.some.inj hsome
      have htEq1 : t1' = t1 := congrArg Prod.fst hpair
      have htx2_def :
          tx2 (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g =
            some (t1', (none : Option α)) := by
        simp [tx2, w, extras, hex, t1', extras2, hex2]
      have htx2_def' :
          tx2 (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g =
            some (t1, (none : Option α)) := by
        simpa [htEq1] using htx2_def
      simpa [tx2Realized, g] using htx2_def'
  · -- If `extras` is empty, `tx2Plus` is `none`, contradiction.
    have htx_none :
        tx2Plus (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked g = none := by
      simp [tx2Plus, w, extras, hex]
    have : False := by
      have : (none : Option (α × Option α × Bool)) = some (t1, (none : Option α), false) := by
        simpa [htx_none] using htx'
      cases this
    exact False.elim this

theorem card_filter_rtx2PlusRealized_eq_pair_some_none_false_le_two
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (r : Finset α) (t1 : α) :
    ((realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked).filter (fun gx =>
          rtx2PlusRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
              fiber hS hfree hblocked gx = (r, some (t1, (none : Option α), false)))).card ≤ 2 := by
  classical
  -- Reduce to the already-proved `tx2 = some (t1, none)` bucket bound.
  have hsub :
      ((realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
              fiber hS hfree hblocked).filter (fun gx =>
            rtx2PlusRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
                fiber hS hfree hblocked gx = (r, some (t1, (none : Option α), false))))
        ⊆
        ((realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
              fiber hS hfree hblocked).filter (fun gx =>
            rtx2Realized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
                fiber hS hfree hblocked gx = (r, some (t1, (none : Option α))))) := by
    intro gx hgx
    have hrtxP :
        rtx2PlusRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked gx = (r, some (t1, (none : Option α), false)) :=
      (Finset.mem_filter.mp hgx).2
    have hrx : rxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked gx = r := by
      have : (rtx2PlusRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked gx).1 = r := by
        simpa [hrtxP] using congrArg Prod.fst hrtxP
      simpa [rtx2PlusRealized] using this
    have htxP :
        tx2PlusRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked gx = some (t1, (none : Option α), false) := by
      have : (rtx2PlusRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked gx).2 = some (t1, (none : Option α), false) := by
        simpa [hrtxP] using congrArg Prod.snd hrtxP
      simpa [rtx2PlusRealized] using this
    have htx2 :
        tx2Realized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked gx = some (t1, (none : Option α)) :=
      tx2Realized_eq_some_none_of_tx2PlusRealized_eq_some_none_false
        (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        (fiber := fiber) hS hfree hblocked gx htxP
    have hrtx2 :
        rtx2Realized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked gx = (r, some (t1, (none : Option α))) := by
      simp [rtx2Realized, hrx, htx2]
    refine Finset.mem_filter.mpr ?_
    exact ⟨(Finset.mem_filter.mp hgx).1, hrtx2⟩
  have hcard := card_filter_rtx2Realized_eq_pair_some_none_le_two
    (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
    (fiber := fiber) hS hfree hblocked r t1
  exact (Finset.card_le_card hsub).trans hcard

theorem sunflower_contradiction_of_three_realizedGoodX_rtx2PlusRealized_some_some_false_collision
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    {r : Finset α} {t1 t2 : α}
    {gx1 gx2 gx3 :
      RealizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked}
    (hx12 : gx1.1 ≠ gx2.1) (hx13 : gx1.1 ≠ gx3.1) (hx23 : gx2.1 ≠ gx3.1)
    (h1 :
      rtx2PlusRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked gx1 =
        (r, some (t1, some t2, false)))
    (h2 :
      rtx2PlusRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked gx2 =
        (r, some (t1, some t2, false)))
    (h3 :
      rtx2PlusRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked gx3 =
        (r, some (t1, some t2, false))) :
    False := by
  classical
  -- Extract witnesses.
  let g1 :=
    toGoodX_of_realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
      fiber hS hfree hblocked gx1
  let g2 :=
    toGoodX_of_realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
      fiber hS hfree hblocked gx2
  let g3 :=
    toGoodX_of_realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
      fiber hS hfree hblocked gx3
  let w1 : BlockedUnionWitness family S gx1.1 :=
    goodXWitness (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked
      (x := gx1.1) g1.2
  let w2 : BlockedUnionWitness family S gx2.1 :=
    goodXWitness (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked
      (x := gx2.1) g2.2
  let w3 : BlockedUnionWitness family S gx3.1 :=
    goodXWitness (family := family) (S := S) (X := X) (h0 := h0) hS hfree hblocked
      (x := gx3.1) g3.2
  -- Realized elements are not in `S`.
  have hxReal1 :
      gx1.1 ∈ realizedXSet (dom := dom) fiber S X :=
    (mem_realizedGoodXSet_iff (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked).1 gx1.2 |>.1
  have hxReal2 :
      gx2.1 ∈ realizedXSet (dom := dom) fiber S X :=
    (mem_realizedGoodXSet_iff (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked).1 gx2.2 |>.1
  have hxReal3 :
      gx3.1 ∈ realizedXSet (dom := dom) fiber S X :=
    (mem_realizedGoodXSet_iff (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked).1 gx3.2 |>.1
  have hxnot1 : gx1.1 ∉ S := mem_realizedXSet_imp_not_mem_S (dom := dom) (fiber := fiber) hxReal1
  have hxnot2 : gx2.1 ∉ S := mem_realizedXSet_imp_not_mem_S (dom := dom) (fiber := fiber) hxReal2
  have hxnot3 : gx3.1 ∉ S := mem_realizedXSet_imp_not_mem_S (dom := dom) (fiber := fiber) hxReal3
  -- Each `A`-witness meets `S` in exactly `r`.
  have hAS1 : w1.A ∩ S = r := by
    have hcore :
        w1.A ∩ S = w1.core.erase gx1.1 :=
      inter_left_eq_core_erase_of_blockedUnionWitness_of_mem_core_of_not_mem_S
        (family := family) (S := S) (x := gx1.1) w1 hxnot1
    have hrx_w1 :
        rxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked gx1 = w1.core.erase gx1.1 := by
      simp [rxRealized, w1]
    calc
      w1.A ∩ S = w1.core.erase gx1.1 := hcore
      _ = rxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked gx1 := hrx_w1.symm
      _ = r := by
            have : (rtx2PlusRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
                fiber hS hfree hblocked gx1).1 = r := by
              simpa [h1] using congrArg Prod.fst h1
            simpa [rtx2PlusRealized] using this
  have hAS2 : w2.A ∩ S = r := by
    have hcore :
        w2.A ∩ S = w2.core.erase gx2.1 :=
      inter_left_eq_core_erase_of_blockedUnionWitness_of_mem_core_of_not_mem_S
        (family := family) (S := S) (x := gx2.1) w2 hxnot2
    have hrx_w2 :
        rxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked gx2 = w2.core.erase gx2.1 := by
      simp [rxRealized, w2]
    calc
      w2.A ∩ S = w2.core.erase gx2.1 := hcore
      _ = rxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked gx2 := hrx_w2.symm
      _ = r := by
            have : (rtx2PlusRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
                fiber hS hfree hblocked gx2).1 = r := by
              simpa [h2] using congrArg Prod.fst h2
            simpa [rtx2PlusRealized] using this
  have hAS3 : w3.A ∩ S = r := by
    have hcore :
        w3.A ∩ S = w3.core.erase gx3.1 :=
      inter_left_eq_core_erase_of_blockedUnionWitness_of_mem_core_of_not_mem_S
        (family := family) (S := S) (x := gx3.1) w3 hxnot3
    have hrx_w3 :
        rxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked gx3 = w3.core.erase gx3.1 := by
      simp [rxRealized, w3]
    calc
      w3.A ∩ S = w3.core.erase gx3.1 := hcore
      _ = rxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked gx3 := hrx_w3.symm
      _ = r := by
            have : (rtx2PlusRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
                fiber hS hfree hblocked gx3).1 = r := by
              simpa [h3] using congrArg Prod.fst h3
            simpa [rtx2PlusRealized] using this
  -- Extract the `tx2Plus` trace.
  have htxp1 :
      tx2PlusRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked gx1 = some (t1, some t2, false) := by
    have : (rtx2PlusRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked gx1).2 = some (t1, some t2, false) := by
      simpa [h1] using congrArg Prod.snd h1
    simpa [rtx2PlusRealized] using this
  have htxp2 :
      tx2PlusRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked gx2 = some (t1, some t2, false) := by
    have : (rtx2PlusRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked gx2).2 = some (t1, some t2, false) := by
      simpa [h2] using congrArg Prod.snd h2
    simpa [rtx2PlusRealized] using this
  have htxp3 :
      tx2PlusRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked gx3 = some (t1, some t2, false) := by
    have : (rtx2PlusRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked gx3).2 = some (t1, some t2, false) := by
      simpa [h3] using congrArg Prod.snd h3
    simpa [rtx2PlusRealized] using this
  -- Convert `tx2Plus` to `tx2` so we can reuse the `tx2` membership lemmas.
  have htx1 :
      tx2Realized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked gx1 = some (t1, some t2) := by
    exact
      tx2Realized_eq_some_of_tx2PlusRealized_eq_some_some (family := family) (dom := dom) (S := S)
        (X := X) (h0 := h0) (fiber := fiber) hS hfree hblocked gx1 htxp1
  have htx2 :
      tx2Realized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked gx2 = some (t1, some t2) := by
    exact
      tx2Realized_eq_some_of_tx2PlusRealized_eq_some_some (family := family) (dom := dom) (S := S)
        (X := X) (h0 := h0) (fiber := fiber) hS hfree hblocked gx2 htxp2
  have htx3 :
      tx2Realized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked gx3 = some (t1, some t2) := by
    exact
      tx2Realized_eq_some_of_tx2PlusRealized_eq_some_some (family := family) (dom := dom) (S := S)
        (X := X) (h0 := h0) (fiber := fiber) hS hfree hblocked gx3 htxp3
  -- Membership of `t1,t2` in each witness, and `t1,t2 ∉ insert x S`.
  have ht1A1 : t1 ∈ w1.A := by
    simpa [g1, w1] using
      mem_A_of_tx2Realized_eq_some_fst (family := family) (dom := dom) (S := S) (X := X)
        (h0 := h0) (fiber := fiber) hS hfree hblocked gx1 htx1
  have ht1A2 : t1 ∈ w2.A := by
    simpa [g2, w2] using
      mem_A_of_tx2Realized_eq_some_fst (family := family) (dom := dom) (S := S) (X := X)
        (h0 := h0) (fiber := fiber) hS hfree hblocked gx2 htx2
  have ht1A3 : t1 ∈ w3.A := by
    simpa [g3, w3] using
      mem_A_of_tx2Realized_eq_some_fst (family := family) (dom := dom) (S := S) (X := X)
        (h0 := h0) (fiber := fiber) hS hfree hblocked gx3 htx3
  have ht2A1 : t2 ∈ w1.A := by
    simpa [g1, w1] using
      mem_A_of_tx2Realized_eq_some_snd (family := family) (dom := dom) (S := S) (X := X)
        (h0 := h0) (fiber := fiber) hS hfree hblocked gx1 htx1
  have ht2A2 : t2 ∈ w2.A := by
    simpa [g2, w2] using
      mem_A_of_tx2Realized_eq_some_snd (family := family) (dom := dom) (S := S) (X := X)
        (h0 := h0) (fiber := fiber) hS hfree hblocked gx2 htx2
  have ht2A3 : t2 ∈ w3.A := by
    simpa [g3, w3] using
      mem_A_of_tx2Realized_eq_some_snd (family := family) (dom := dom) (S := S) (X := X)
        (h0 := h0) (fiber := fiber) hS hfree hblocked gx3 htx3
  have ht1NotIns1 : t1 ∉ insert gx1.1 S := by
    simpa [g1] using
      not_mem_insert_of_tx2Realized_eq_some_fst (family := family) (dom := dom) (S := S) (X := X)
        (h0 := h0) (fiber := fiber) hS hfree hblocked gx1 htx1
  have ht1NotIns2 : t1 ∉ insert gx2.1 S := by
    simpa [g2] using
      not_mem_insert_of_tx2Realized_eq_some_fst (family := family) (dom := dom) (S := S) (X := X)
        (h0 := h0) (fiber := fiber) hS hfree hblocked gx2 htx2
  have ht1NotIns3 : t1 ∉ insert gx3.1 S := by
    simpa [g3] using
      not_mem_insert_of_tx2Realized_eq_some_fst (family := family) (dom := dom) (S := S) (X := X)
        (h0 := h0) (fiber := fiber) hS hfree hblocked gx3 htx3
  have ht2NotIns1 : t2 ∉ insert gx1.1 S := by
    simpa [g1] using
      not_mem_insert_of_tx2Realized_eq_some_snd (family := family) (dom := dom) (S := S) (X := X)
        (h0 := h0) (fiber := fiber) hS hfree hblocked gx1 htx1
  have ht2NotIns2 : t2 ∉ insert gx2.1 S := by
    simpa [g2] using
      not_mem_insert_of_tx2Realized_eq_some_snd (family := family) (dom := dom) (S := S) (X := X)
        (h0 := h0) (fiber := fiber) hS hfree hblocked gx2 htx2
  have ht2NotIns3 : t2 ∉ insert gx3.1 S := by
    simpa [g3] using
      not_mem_insert_of_tx2Realized_eq_some_snd (family := family) (dom := dom) (S := S) (X := X)
        (h0 := h0) (fiber := fiber) hS hfree hblocked gx3 htx3
  -- In the `tx2Plus = some (_, some _, false)` bucket, the extra part of each witness is contained in `{t1,t2}`.
  have hsub1 : w1.A \ insert gx1.1 S ⊆ ({t1, t2} : Finset α) := by
    simpa [g1, w1] using
      A_sdiff_insert_subset_pair_of_tx2PlusRealized_eq_some_some_false (family := family) (dom := dom)
        (S := S) (X := X) (h0 := h0) (fiber := fiber) hS hfree hblocked gx1 htxp1
  have hsub2 : w2.A \ insert gx2.1 S ⊆ ({t1, t2} : Finset α) := by
    simpa [g2, w2] using
      A_sdiff_insert_subset_pair_of_tx2PlusRealized_eq_some_some_false (family := family) (dom := dom)
        (S := S) (X := X) (h0 := h0) (fiber := fiber) hS hfree hblocked gx2 htxp2
  have hsub3 : w3.A \ insert gx3.1 S ⊆ ({t1, t2} : Finset α) := by
    simpa [g3, w3] using
      A_sdiff_insert_subset_pair_of_tx2PlusRealized_eq_some_some_false (family := family) (dom := dom)
        (S := S) (X := X) (h0 := h0) (fiber := fiber) hS hfree hblocked gx3 htxp3
  -- Pairwise intersection identities: `wᵢ.A ∩ wⱼ.A = insert t1 (insert t2 r)`.
  have hA12 : w1.A ∩ w2.A = insert t1 (insert t2 r) := by
    apply Finset.Subset.antisymm
    · intro z hz
      have hz1 : z ∈ w1.A := (Finset.mem_inter.mp hz).1
      have hz2 : z ∈ w2.A := (Finset.mem_inter.mp hz).2
      by_cases hzT1 : z = t1
      · subst hzT1
        simp
      · by_cases hzT2 : z = t2
        · subst hzT2
          simp [hzT1]
        · have hzIns1 : z ∈ insert gx1.1 S := by
            by_contra hzNot
            have hzDiff : z ∈ w1.A \ insert gx1.1 S := Finset.mem_sdiff.mpr ⟨hz1, hzNot⟩
            have hzPair : z ∈ ({t1, t2} : Finset α) := hsub1 hzDiff
            have : z = t1 ∨ z = t2 := by
              simpa [Finset.mem_insert, Finset.mem_singleton] using hzPair
            rcases this with hEq | hEq
            · exact hzT1 hEq
            · exact hzT2 hEq
          have hzIns2 : z ∈ insert gx2.1 S := by
            by_contra hzNot
            have hzDiff : z ∈ w2.A \ insert gx2.1 S := Finset.mem_sdiff.mpr ⟨hz2, hzNot⟩
            have hzPair : z ∈ ({t1, t2} : Finset α) := hsub2 hzDiff
            have : z = t1 ∨ z = t2 := by
              simpa [Finset.mem_insert, Finset.mem_singleton] using hzPair
            rcases this with hEq | hEq
            · exact hzT1 hEq
            · exact hzT2 hEq
          have hzS : z ∈ S := by
            rcases Finset.mem_insert.mp hzIns1 with hzEq1 | hzS1
            · subst hzEq1
              rcases Finset.mem_insert.mp hzIns2 with hzEq2 | hzS2
              · exact False.elim (hx12 hzEq2)
              · exact False.elim (hxnot1 hzS2)
            · exact hzS1
          have hzR : z ∈ r := by
            have : z ∈ w1.A ∩ S := Finset.mem_inter.mpr ⟨hz1, hzS⟩
            simpa [hAS1] using this
          simp [hzR, hzT1, hzT2]
    · intro z hz
      rcases Finset.mem_insert.mp hz with hzEq | hz
      · subst hzEq
        exact Finset.mem_inter.mpr ⟨ht1A1, ht1A2⟩
      rcases Finset.mem_insert.mp hz with hzEq | hzR
      · subst hzEq
        exact Finset.mem_inter.mpr ⟨ht2A1, ht2A2⟩
      · have hz1 : z ∈ w1.A :=
          (Finset.mem_inter.mp (by simpa [hAS1] using hzR : z ∈ w1.A ∩ S)).1
        have hz2 : z ∈ w2.A :=
          (Finset.mem_inter.mp (by simpa [hAS2] using hzR : z ∈ w2.A ∩ S)).1
        exact Finset.mem_inter.mpr ⟨hz1, hz2⟩
  have hA13 : w1.A ∩ w3.A = insert t1 (insert t2 r) := by
    apply Finset.Subset.antisymm
    · intro z hz
      have hz1 : z ∈ w1.A := (Finset.mem_inter.mp hz).1
      have hz3 : z ∈ w3.A := (Finset.mem_inter.mp hz).2
      by_cases hzT1 : z = t1
      · subst hzT1
        simp
      · by_cases hzT2 : z = t2
        · subst hzT2
          simp [hzT1]
        · have hzIns1 : z ∈ insert gx1.1 S := by
            by_contra hzNot
            have hzDiff : z ∈ w1.A \ insert gx1.1 S := Finset.mem_sdiff.mpr ⟨hz1, hzNot⟩
            have hzPair : z ∈ ({t1, t2} : Finset α) := hsub1 hzDiff
            have : z = t1 ∨ z = t2 := by
              simpa [Finset.mem_insert, Finset.mem_singleton] using hzPair
            rcases this with hEq | hEq
            · exact hzT1 hEq
            · exact hzT2 hEq
          have hzIns3 : z ∈ insert gx3.1 S := by
            by_contra hzNot
            have hzDiff : z ∈ w3.A \ insert gx3.1 S := Finset.mem_sdiff.mpr ⟨hz3, hzNot⟩
            have hzPair : z ∈ ({t1, t2} : Finset α) := hsub3 hzDiff
            have : z = t1 ∨ z = t2 := by
              simpa [Finset.mem_insert, Finset.mem_singleton] using hzPair
            rcases this with hEq | hEq
            · exact hzT1 hEq
            · exact hzT2 hEq
          have hzS : z ∈ S := by
            rcases Finset.mem_insert.mp hzIns1 with hzEq1 | hzS1
            · subst hzEq1
              rcases Finset.mem_insert.mp hzIns3 with hzEq3 | hzS3
              · exact False.elim (hx13 hzEq3)
              · exact False.elim (hxnot1 hzS3)
            · exact hzS1
          have hzR : z ∈ r := by
            have : z ∈ w1.A ∩ S := Finset.mem_inter.mpr ⟨hz1, hzS⟩
            simpa [hAS1] using this
          simp [hzR, hzT1, hzT2]
    · intro z hz
      rcases Finset.mem_insert.mp hz with hzEq | hz
      · subst hzEq
        exact Finset.mem_inter.mpr ⟨ht1A1, ht1A3⟩
      rcases Finset.mem_insert.mp hz with hzEq | hzR
      · subst hzEq
        exact Finset.mem_inter.mpr ⟨ht2A1, ht2A3⟩
      · have hz1 : z ∈ w1.A :=
          (Finset.mem_inter.mp (by simpa [hAS1] using hzR : z ∈ w1.A ∩ S)).1
        have hz3 : z ∈ w3.A :=
          (Finset.mem_inter.mp (by simpa [hAS3] using hzR : z ∈ w3.A ∩ S)).1
        exact Finset.mem_inter.mpr ⟨hz1, hz3⟩
  have hA23 : w2.A ∩ w3.A = insert t1 (insert t2 r) := by
    apply Finset.Subset.antisymm
    · intro z hz
      have hz2 : z ∈ w2.A := (Finset.mem_inter.mp hz).1
      have hz3 : z ∈ w3.A := (Finset.mem_inter.mp hz).2
      by_cases hzT1 : z = t1
      · subst hzT1
        simp
      · by_cases hzT2 : z = t2
        · subst hzT2
          simp [hzT1]
        · have hzIns2 : z ∈ insert gx2.1 S := by
            by_contra hzNot
            have hzDiff : z ∈ w2.A \ insert gx2.1 S := Finset.mem_sdiff.mpr ⟨hz2, hzNot⟩
            have hzPair : z ∈ ({t1, t2} : Finset α) := hsub2 hzDiff
            have : z = t1 ∨ z = t2 := by
              simpa [Finset.mem_insert, Finset.mem_singleton] using hzPair
            rcases this with hEq | hEq
            · exact hzT1 hEq
            · exact hzT2 hEq
          have hzIns3 : z ∈ insert gx3.1 S := by
            by_contra hzNot
            have hzDiff : z ∈ w3.A \ insert gx3.1 S := Finset.mem_sdiff.mpr ⟨hz3, hzNot⟩
            have hzPair : z ∈ ({t1, t2} : Finset α) := hsub3 hzDiff
            have : z = t1 ∨ z = t2 := by
              simpa [Finset.mem_insert, Finset.mem_singleton] using hzPair
            rcases this with hEq | hEq
            · exact hzT1 hEq
            · exact hzT2 hEq
          have hzS : z ∈ S := by
            rcases Finset.mem_insert.mp hzIns2 with hzEq2 | hzS2
            · subst hzEq2
              rcases Finset.mem_insert.mp hzIns3 with hzEq3 | hzS3
              · exact False.elim (hx23 hzEq3)
              · exact False.elim (hxnot2 hzS3)
            · exact hzS2
          have hzR : z ∈ r := by
            have : z ∈ w2.A ∩ S := Finset.mem_inter.mpr ⟨hz2, hzS⟩
            simpa [hAS2] using this
          simp [hzR, hzT1, hzT2]
    · intro z hz
      rcases Finset.mem_insert.mp hz with hzEq | hz
      · subst hzEq
        exact Finset.mem_inter.mpr ⟨ht1A2, ht1A3⟩
      rcases Finset.mem_insert.mp hz with hzEq | hzR
      · subst hzEq
        exact Finset.mem_inter.mpr ⟨ht2A2, ht2A3⟩
      · have hz2 : z ∈ w2.A :=
          (Finset.mem_inter.mp (by simpa [hAS2] using hzR : z ∈ w2.A ∩ S)).1
        have hz3 : z ∈ w3.A :=
          (Finset.mem_inter.mp (by simpa [hAS3] using hzR : z ∈ w3.A ∩ S)).1
        exact Finset.mem_inter.mpr ⟨hz2, hz3⟩
  -- Contradiction: `{w1.A, w2.A, w3.A}` forms a 3-sunflower inside `family`.
  have hsub : ({w1.A, w2.A, w3.A} : Finset (Finset α)) ⊆ family := by
    intro T hT
    have hT' : T = w1.A ∨ T = w2.A ∨ T = w3.A := by
      simpa using (Finset.mem_insert.mp hT)
    rcases hT' with rfl | hT'
    · exact w1.hA
    rcases hT' with rfl | rfl
    · exact w2.hA
    · exact w3.hA
  have hsun : IsSunflower ({w1.A, w2.A, w3.A} : Finset (Finset α)) 3 := by
    refine ⟨?_, ?_⟩
    · -- card = 3: the three witness sets are distinct (each contains its own realized `x`).
      have hxA1 : gx1.1 ∈ w1.A := by
        have hxcore : gx1.1 ∈ w1.core :=
          mem_core_of_goodXWitness (family := family) (S := S) (X := X) (h0 := h0)
            (hS := hS) (hfree := hfree) (hblocked := hblocked) g1.2
        have hxAT : gx1.1 ∈ w1.A ∩ (S ∪ ({gx1.1} : Finset α)) := by
          have hx' := hxcore
          rw [← w1.hcoreAT] at hx'
          exact hx'
        exact (Finset.mem_inter.mp hxAT).1
      have hxA2 : gx2.1 ∈ w2.A := by
        have hxcore : gx2.1 ∈ w2.core :=
          mem_core_of_goodXWitness (family := family) (S := S) (X := X) (h0 := h0)
            (hS := hS) (hfree := hfree) (hblocked := hblocked) g2.2
        have hxAT : gx2.1 ∈ w2.A ∩ (S ∪ ({gx2.1} : Finset α)) := by
          have hx' := hxcore
          rw [← w2.hcoreAT] at hx'
          exact hx'
        exact (Finset.mem_inter.mp hxAT).1
      have hxA3 : gx3.1 ∈ w3.A := by
        have hxcore : gx3.1 ∈ w3.core :=
          mem_core_of_goodXWitness (family := family) (S := S) (X := X) (h0 := h0)
            (hS := hS) (hfree := hfree) (hblocked := hblocked) g3.2
        have hxAT : gx3.1 ∈ w3.A ∩ (S ∪ ({gx3.1} : Finset α)) := by
          have hx' := hxcore
          rw [← w3.hcoreAT] at hx'
          exact hx'
        exact (Finset.mem_inter.mp hxAT).1
      have hx1_ne_t1 : gx1.1 ≠ t1 := by
        intro hxEq; subst hxEq
        exact ht1NotIns1 (Finset.mem_insert_self _ _)
      have hx2_ne_t1 : gx2.1 ≠ t1 := by
        intro hxEq; subst hxEq
        exact ht1NotIns2 (Finset.mem_insert_self _ _)
      have hx3_ne_t1 : gx3.1 ≠ t1 := by
        intro hxEq; subst hxEq
        exact ht1NotIns3 (Finset.mem_insert_self _ _)
      have hx1_ne_t2 : gx1.1 ≠ t2 := by
        intro hxEq; subst hxEq
        exact ht2NotIns1 (Finset.mem_insert_self _ _)
      have hx2_ne_t2 : gx2.1 ≠ t2 := by
        intro hxEq; subst hxEq
        exact ht2NotIns2 (Finset.mem_insert_self _ _)
      have hx3_ne_t2 : gx3.1 ≠ t2 := by
        intro hxEq; subst hxEq
        exact ht2NotIns3 (Finset.mem_insert_self _ _)
      have hxnotIns12 : gx1.1 ∉ insert gx2.1 S := by
        intro hxIn
        rcases Finset.mem_insert.mp hxIn with hxEq | hxInS
        · exact hx12 hxEq
        · exact hxnot1 hxInS
      have hxnotIns13 : gx1.1 ∉ insert gx3.1 S := by
        intro hxIn
        rcases Finset.mem_insert.mp hxIn with hxEq | hxInS
        · exact hx13 hxEq
        · exact hxnot1 hxInS
      have hxnotIns21 : gx2.1 ∉ insert gx1.1 S := by
        intro hxIn
        rcases Finset.mem_insert.mp hxIn with hxEq | hxInS
        · exact hx12 hxEq.symm
        · exact hxnot2 hxInS
      have hxnotIns23 : gx2.1 ∉ insert gx3.1 S := by
        intro hxIn
        rcases Finset.mem_insert.mp hxIn with hxEq | hxInS
        · exact hx23 hxEq
        · exact hxnot2 hxInS
      have hxnotIns31 : gx3.1 ∉ insert gx1.1 S := by
        intro hxIn
        rcases Finset.mem_insert.mp hxIn with hxEq | hxInS
        · exact hx13 hxEq.symm
        · exact hxnot3 hxInS
      have hxnotIns32 : gx3.1 ∉ insert gx2.1 S := by
        intro hxIn
        rcases Finset.mem_insert.mp hxIn with hxEq | hxInS
        · exact hx23 hxEq.symm
        · exact hxnot3 hxInS
      have hxA1_not2 : gx1.1 ∉ w2.A := by
        intro hxIn
        have hxDiff : gx1.1 ∈ w2.A \ insert gx2.1 S := Finset.mem_sdiff.mpr ⟨hxIn, hxnotIns12⟩
        have : gx1.1 ∈ ({t1, t2} : Finset α) := hsub2 hxDiff
        have : gx1.1 = t1 ∨ gx1.1 = t2 := by
          simpa [Finset.mem_insert, Finset.mem_singleton] using this
        rcases this with hEq | hEq
        · exact hx1_ne_t1 hEq
        · exact hx1_ne_t2 hEq
      have hxA1_not3 : gx1.1 ∉ w3.A := by
        intro hxIn
        have hxDiff : gx1.1 ∈ w3.A \ insert gx3.1 S := Finset.mem_sdiff.mpr ⟨hxIn, hxnotIns13⟩
        have : gx1.1 ∈ ({t1, t2} : Finset α) := hsub3 hxDiff
        have : gx1.1 = t1 ∨ gx1.1 = t2 := by
          simpa [Finset.mem_insert, Finset.mem_singleton] using this
        rcases this with hEq | hEq
        · exact hx1_ne_t1 hEq
        · exact hx1_ne_t2 hEq
      have hxA2_not1 : gx2.1 ∉ w1.A := by
        intro hxIn
        have hxDiff : gx2.1 ∈ w1.A \ insert gx1.1 S := Finset.mem_sdiff.mpr ⟨hxIn, hxnotIns21⟩
        have : gx2.1 ∈ ({t1, t2} : Finset α) := hsub1 hxDiff
        have : gx2.1 = t1 ∨ gx2.1 = t2 := by
          simpa [Finset.mem_insert, Finset.mem_singleton] using this
        rcases this with hEq | hEq
        · exact hx2_ne_t1 hEq
        · exact hx2_ne_t2 hEq
      have hxA2_not3 : gx2.1 ∉ w3.A := by
        intro hxIn
        have hxDiff : gx2.1 ∈ w3.A \ insert gx3.1 S := Finset.mem_sdiff.mpr ⟨hxIn, hxnotIns23⟩
        have : gx2.1 ∈ ({t1, t2} : Finset α) := hsub3 hxDiff
        have : gx2.1 = t1 ∨ gx2.1 = t2 := by
          simpa [Finset.mem_insert, Finset.mem_singleton] using this
        rcases this with hEq | hEq
        · exact hx2_ne_t1 hEq
        · exact hx2_ne_t2 hEq
      have hxA3_not1 : gx3.1 ∉ w1.A := by
        intro hxIn
        have hxDiff : gx3.1 ∈ w1.A \ insert gx1.1 S := Finset.mem_sdiff.mpr ⟨hxIn, hxnotIns31⟩
        have : gx3.1 ∈ ({t1, t2} : Finset α) := hsub1 hxDiff
        have : gx3.1 = t1 ∨ gx3.1 = t2 := by
          simpa [Finset.mem_insert, Finset.mem_singleton] using this
        rcases this with hEq | hEq
        · exact hx3_ne_t1 hEq
        · exact hx3_ne_t2 hEq
      have hxA3_not2 : gx3.1 ∉ w2.A := by
        intro hxIn
        have hxDiff : gx3.1 ∈ w2.A \ insert gx2.1 S := Finset.mem_sdiff.mpr ⟨hxIn, hxnotIns32⟩
        have : gx3.1 ∈ ({t1, t2} : Finset α) := hsub2 hxDiff
        have : gx3.1 = t1 ∨ gx3.1 = t2 := by
          simpa [Finset.mem_insert, Finset.mem_singleton] using this
        rcases this with hEq | hEq
        · exact hx3_ne_t1 hEq
        · exact hx3_ne_t2 hEq
      have hA12_ne : w1.A ≠ w2.A := by
        intro hEq
        have : gx1.1 ∈ w2.A := by simpa [hEq] using hxA1
        exact hxA1_not2 this
      have hA13_ne : w1.A ≠ w3.A := by
        intro hEq
        have : gx1.1 ∈ w3.A := by simpa [hEq] using hxA1
        exact hxA1_not3 this
      have hA23_ne : w2.A ≠ w3.A := by
        intro hEq
        have : gx2.1 ∈ w3.A := by simpa [hEq] using hxA2
        exact hxA2_not3 this
      have hBnot : w2.A ∉ ({w3.A} : Finset (Finset α)) := by
        simp [hA23_ne]
      have hAnot : w1.A ∉ insert w2.A ({w3.A} : Finset (Finset α)) := by
        simp [hA12_ne, hA13_ne]
      have hcardB : (insert w2.A ({w3.A} : Finset (Finset α))).card = 2 := by
        simp [Finset.card_insert_of_notMem, hBnot]
      have hcard : (insert w1.A (insert w2.A ({w3.A} : Finset (Finset α)))).card = 3 := by
        calc
          (insert w1.A (insert w2.A ({w3.A} : Finset (Finset α)))).card =
              (insert w2.A ({w3.A} : Finset (Finset α))).card + 1 := by
                simp [Finset.card_insert_of_notMem, hAnot]
          _ = 3 := by simp [hcardB]
      simpa using hcard
    · refine ⟨insert t1 (insert t2 r), ?_⟩
      intro A B hA hB hAB
      have hA' : A = w1.A ∨ A = w2.A ∨ A = w3.A := by
        simpa using (Finset.mem_insert.mp hA)
      have hB' : B = w1.A ∨ B = w2.A ∨ B = w3.A := by
        simpa using (Finset.mem_insert.mp hB)
      rcases hA' with rfl | hA'
      · rcases hB' with rfl | hB'
        · exact False.elim (hAB rfl)
        rcases hB' with rfl | rfl
        · exact hA12
        · exact hA13
      rcases hA' with rfl | rfl
      · rcases hB' with rfl | hB'
        · simpa [Finset.inter_comm] using hA12
        rcases hB' with rfl | rfl
        · exact False.elim (hAB rfl)
        · exact hA23
      · rcases hB' with rfl | hB'
        · simpa [Finset.inter_comm] using hA13
        rcases hB' with rfl | rfl
        · simpa [Finset.inter_comm] using hA23
        · exact False.elim (hAB rfl)
  exact hfree ({w1.A, w2.A, w3.A} : Finset (Finset α)) hsub hsun

theorem card_filter_rtx2PlusRealized_eq_pair_some_some_false_le_two
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (r : Finset α) (t1 t2 : α) :
    ((realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked).filter (fun gx =>
          rtx2PlusRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
              fiber hS hfree hblocked gx = (r, some (t1, some t2, false)))).card ≤ 2 := by
  classical
  by_contra h
  have hlt : 2 < ((realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked).filter (fun gx =>
          rtx2PlusRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
              fiber hS hfree hblocked gx = (r, some (t1, some t2, false)))).card := by
    exact Nat.lt_of_not_ge h
  have h3 :
      3 ≤ ((realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked).filter (fun gx =>
          rtx2PlusRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
              fiber hS hfree hblocked gx = (r, some (t1, some t2, false)))).card :=
    Nat.succ_le_of_lt hlt
  rcases exists_three_mem_pairwise_ne_of_card_ge_three
      (F :=
        (realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
              fiber hS hfree hblocked).filter (fun gx =>
            rtx2PlusRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
                fiber hS hfree hblocked gx = (r, some (t1, some t2, false))))
      h3 with
    ⟨gx1, gx2, gx3, hgx1, hgx2, hgx3, hx12, hx13, hx23⟩
  have hx12' : gx1.1 ≠ gx2.1 := by
    intro hEq
    apply hx12
    ext
    exact hEq
  have hx13' : gx1.1 ≠ gx3.1 := by
    intro hEq
    apply hx13
    ext
    exact hEq
  have hx23' : gx2.1 ≠ gx3.1 := by
    intro hEq
    apply hx23
    ext
    exact hEq
  have h1 : rtx2PlusRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked gx1 = (r, some (t1, some t2, false)) :=
    (Finset.mem_filter.mp hgx1).2
  have h2 : rtx2PlusRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked gx2 = (r, some (t1, some t2, false)) :=
    (Finset.mem_filter.mp hgx2).2
  have h3' : rtx2PlusRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked gx3 = (r, some (t1, some t2, false)) :=
    (Finset.mem_filter.mp hgx3).2
  exact
    sunflower_contradiction_of_three_realizedGoodX_rtx2PlusRealized_some_some_false_collision
      (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
      (fiber := fiber) hS hfree hblocked hx12' hx13' hx23' h1 h2 h3'

theorem card_realizedGoodX_hasMoreTrue_le_X_card_pow_three
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α))) :
    (realizedGoodX_hasMoreTrue (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked).card ≤ X.card ^ 3 := by
  classical
  let F :=
    realizedGoodX_hasMoreTrue (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
      fiber hS hfree hblocked
  -- Use a coarse injection into `X × X × X` via `gx ↦ (x,x,x)`.
  let f :
      RealizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked →
        (α × α × α) :=
    fun gx => (gx.1, (gx.1, gx.1))
  have hf_inj :
      Function.Injective f := by
    intro gx1 gx2 hf
    have hx : gx1.1 = gx2.1 := by
      simpa [f] using congrArg Prod.fst hf
    ext
    exact hx
  have hcard_image : (F.image f).card = F.card := by
    simpa using Finset.card_image_of_injective (s := F) (f := f) hf_inj
  have himage_sub :
      F.image f ⊆ X.product (X.product X) := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨gx, hgx, rfl⟩
    have hxX : gx.1 ∈ X := by
      have hx' :=
        (mem_realizedGoodXSet_iff (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
              fiber hS hfree hblocked).1 gx.2
      -- `goodXSet` membership implies `x ∈ X`.
      exact (Finset.mem_filter.mp hx'.2).1
    refine Finset.mem_product.mpr ?_
    refine ⟨hxX, ?_⟩
    refine Finset.mem_product.mpr ?_
    exact ⟨hxX, hxX⟩
  have hcard_le :
      (F.image f).card ≤ (X.product (X.product X)).card :=
    Finset.card_le_card himage_sub
  have hprod_card : (X.product (X.product X)).card = X.card ^ 3 := by
    -- `card (X × (X × X)) = card X * (card X * card X) = card X ^ 3`.
    simp [Finset.card_product, pow_succ, pow_two, Nat.mul_assoc]
  -- Conclude.
  have : F.card ≤ X.card ^ 3 := by
    -- rewrite `F.card` as `card (F.image f)` via injectivity, then bound by the product card.
    have hle : F.card ≤ (X.product (X.product X)).card := by
      simpa [hcard_image] using hcard_le
    exact le_trans hle (le_of_eq hprod_card)
  simpa [F] using this

theorem card_filter_rtx2PlusRealized_eq_pair_some_false_le_two
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (r : Finset α) (t1 : α) (ot2 : Option α) :
    ((realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked).filter (fun gx =>
          rtx2PlusRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
              fiber hS hfree hblocked gx = (r, some (t1, ot2, false)))).card ≤ 2 := by
  classical
              cases ot2 with
  | none =>
      simpa using
        card_filter_rtx2PlusRealized_eq_pair_some_none_false_le_two
          (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          (fiber := fiber) hS hfree hblocked r t1
  | some t2 =>
      simpa using
        card_filter_rtx2PlusRealized_eq_pair_some_some_false_le_two
          (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          (fiber := fiber) hS hfree hblocked r t1 t2

/-!
Combination bound for `RealizedGoodX(S)`.

We will ultimately use the refined trace buckets to control collisions (hasMore=false), and treat the
`hasMore=true` bucket with a coarse polynomial bound (per guidance).

This lemma just packages the “sum of buckets” step into a single inequality usable by the final
multiplicity proof.
-/

theorem card_realizedGoodX_le_X_card_add_X_card_pow_three
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α))) :
    (realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked).card ≤ X.card + X.card ^ 3 := by
  classical
  let G :=
    realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
      fiber hS hfree hblocked
  let Gmore :=
    realizedGoodX_hasMoreTrue (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
      fiber hS hfree hblocked
  -- `Gmore ⊆ G`, and the complement is bounded by `X.card` since `RealizedGoodX ⊆ X`.
  have hmore_sub : Gmore ⊆ G := by
    intro gx hgx
    exact (Finset.mem_filter.mp hgx).1
  have hmore_card : Gmore.card ≤ X.card ^ 3 := by
    simpa [Gmore] using
      card_realizedGoodX_hasMoreTrue_le_X_card_pow_three
        (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        (fiber := fiber) hS hfree hblocked
  have hG_card_le_X : G.card ≤ X.card := by
    -- `G` is the attachment of a set of elements in `X`.
    have hsub : realizedGoodXSet (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked ⊆ X := by
      intro x hx
      have hx' :=
        (mem_realizedGoodXSet_iff (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
              fiber hS hfree hblocked).1 hx
      -- `goodXSet` membership implies `x ∈ X`.
      exact (Finset.mem_filter.mp hx'.2).1
    have : G.card = (realizedGoodXSet (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked).card := by
      simp [G, realizedGoodX]
    -- Use the subset bound on the underlying set.
    have hcard :
        (realizedGoodXSet (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked).card ≤ X.card :=
      Finset.card_le_card hsub
    simpa [this] using hcard
  -- Combine: `G = (G \ Gmore) ∪ Gmore`.
  have hcard_union :
      G.card ≤ (G \ Gmore).card + Gmore.card := by
    -- `Gmore ⊆ G` gives an exact partition of cards.
    simpa using
      (Finset.card_sdiff_add_card_eq_card (s := Gmore) (t := G) hmore_sub).symm.le
  have hsdiff_le : (G \ Gmore).card ≤ X.card := by
    exact (Finset.card_le_card (Finset.sdiff_subset (s := G) (t := Gmore))).trans hG_card_le_X
  calc
    G.card ≤ (G \ Gmore).card + Gmore.card := hcard_union
    _ ≤ X.card + X.card ^ 3 := by
        exact Nat.add_le_add hsdiff_le hmore_card

end RealizedGoodX

/-!
`RealizedGoodX(S)` pigeonhole setup: repeat the coarse `x ↦ rx` collision bounds, but restricted
to the realized-good subtype. This is the version intended for multiplicity bounds in the
hard-branch fiber argument.
-/

section RealizedGoodXPigeonhole

variable {α : Type*} [DecidableEq α]
variable {family : Finset (Finset α)} {dom : Finset (Finset α)}
variable {S X : Finset α} {h0 : α}

theorem image_rxRealized_subset_powerset
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α))) :
    (realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked).image
        (rxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked)
      ⊆ S.powerset := by
  classical
  intro r hr
  rcases Finset.mem_image.mp hr with ⟨gx, hgx, rfl⟩
  exact Finset.mem_powerset.mpr
    (rxRealized_subset_S (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
      fiber hS hfree hblocked gx)

theorem card_image_rxRealized_le_powerset_card
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α))) :
    ((realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked).image
        (rxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked)).card
      ≤ S.powerset.card := by
  classical
  exact Finset.card_le_card (image_rxRealized_subset_powerset (family := family) (dom := dom)
    (S := S) (X := X) (h0 := h0) fiber hS hfree hblocked)

/-- Range bound for the refined invariant `x ↦ (rxRealized, txRealized)` on `RealizedGoodX(S)`. -/
theorem image_rtxRealized_subset_powerset_product_option
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α))) :
    (realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked).image
        (rtxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked) ⊆
      S.powerset.product (optionOfFinset (α := α) (family.biUnion id)) := by
  classical
  intro rt hrt
  rcases Finset.mem_image.mp hrt with ⟨gx, hgx, rfl⟩
  refine Finset.mem_product.mpr ?_
  refine ⟨?_, ?_⟩
  · exact Finset.mem_powerset.mpr
      (rxRealized_subset_S (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked gx)
  · exact txRealized_mem_optionOfFinset_family_biUnion (family := family) (dom := dom)
      (S := S) (X := X) (h0 := h0) fiber hS hfree hblocked gx

theorem card_image_rtxRealized_le_range_card
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α))) :
    ((realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked).image
        (rtxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked)).card ≤
      S.powerset.card * (optionOfFinset (α := α) (family.biUnion id)).card := by
  classical
  have hsub :
      (realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked).image
          (rtxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked) ⊆
        S.powerset.product (optionOfFinset (α := α) (family.biUnion id)) :=
    image_rtxRealized_subset_powerset_product_option (family := family) (dom := dom) (S := S)
      (X := X) (h0 := h0) fiber hS hfree hblocked
  have hcard_le :
      ((realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked).image
            (rtxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
              fiber hS hfree hblocked)).card ≤
        (S.powerset.product (optionOfFinset (α := α) (family.biUnion id))).card :=
    Finset.card_le_card hsub
  simpa [Finset.card_product, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hcard_le

theorem biUnion_id_subset_of_subset_powerset {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α}
    (hsub : family ⊆ ground.powerset) :
    family.biUnion id ⊆ ground := by
  classical
  intro x hx
  rcases Finset.mem_biUnion.mp hx with ⟨T, hT, hxT⟩
  have hTsub : T ⊆ ground := Finset.mem_powerset.mp (hsub hT)
  exact hTsub hxT

theorem txRealized_mem_optionOfFinset_ground
    {ground : Finset α}
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (hsub : family ⊆ ground.powerset)
    (gx :
      RealizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked) :
    txRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked gx ∈ optionOfFinset (α := α) ground := by
  classical
  have hxT :
      txRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked gx ∈
        optionOfFinset (α := α) (family.biUnion id) :=
    txRealized_mem_optionOfFinset_family_biUnion (family := family) (dom := dom) (S := S)
      (X := X) (h0 := h0) fiber hS hfree hblocked gx
  have hTU : family.biUnion id ⊆ ground := biUnion_id_subset_of_subset_powerset (hsub := hsub)
  exact optionOfFinset_mono (α := α) hTU hxT

theorem image_txRealized_subset_optionOfFinset_ground
    {ground : Finset α}
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (hsub : family ⊆ ground.powerset) :
    (realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked).image
        (txRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked)
      ⊆ optionOfFinset (α := α) ground := by
  classical
  intro t ht
  rcases Finset.mem_image.mp ht with ⟨gx, hgx, rfl⟩
  exact txRealized_mem_optionOfFinset_ground (family := family) (dom := dom) (S := S) (X := X)
    (h0 := h0) (ground := ground) (fiber := fiber) hS hfree hblocked hsub gx

theorem card_image_txRealized_le_ground_succ
    {ground : Finset α}
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (hsub : family ⊆ ground.powerset) :
    ((realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked).image
        (txRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked)).card ≤ ground.card + 1 := by
  classical
  have hsubImg :
      (realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked).image
          (txRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked) ⊆
        optionOfFinset (α := α) ground :=
    image_txRealized_subset_optionOfFinset_ground (family := family) (dom := dom) (S := S)
      (X := X) (h0 := h0) (ground := ground) fiber hS hfree hblocked hsub
  have hcard :=
    Finset.card_le_card hsubImg
  exact hcard.trans (card_optionOfFinset_le_succ (α := α) ground)

theorem card_image_rtxRealized_le_powerset_mul_ground_succ
    {ground : Finset α}
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (hsub : family ⊆ ground.powerset) :
    ((realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked).image
        (rtxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked)).card ≤
      S.powerset.card * (ground.card + 1) := by
  classical
  have h1 :
      ((realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
              fiber hS hfree hblocked).image
            (rtxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
              fiber hS hfree hblocked)).card ≤
        S.powerset.card * (optionOfFinset (α := α) (family.biUnion id)).card :=
    card_image_rtxRealized_le_range_card (family := family) (dom := dom) (S := S) (X := X)
      (h0 := h0) fiber hS hfree hblocked
  have hTU : family.biUnion id ⊆ ground := biUnion_id_subset_of_subset_powerset (hsub := hsub)
  have hopt :
      (optionOfFinset (α := α) (family.biUnion id)).card ≤ ground.card + 1 := by
    have hsubOpt :
        optionOfFinset (α := α) (family.biUnion id) ⊆ optionOfFinset (α := α) ground :=
      optionOfFinset_mono (α := α) hTU
    have hcard := Finset.card_le_card hsubOpt
    exact hcard.trans (card_optionOfFinset_le_succ (α := α) ground)
  exact le_trans h1 (Nat.mul_le_mul_left _ hopt)

theorem card_image_rtxRealized_le_card_image_rxRealized_mul_ground_succ
    {ground : Finset α}
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (hsub : family ⊆ ground.powerset) :
    ((realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked).image
        (rtxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked)).card ≤
      ((realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked).image
          (rxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked)).card *
        (ground.card + 1) := by
  classical
  let G :=
    realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
      fiber hS hfree hblocked
  have hsubImg :
      G.image
          (rtxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked) ⊆
        (G.image
              (rxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
                fiber hS hfree hblocked)).product
          (optionOfFinset (α := α) ground) := by
    intro rt hrt
    rcases Finset.mem_image.mp hrt with ⟨gx, hgx, rfl⟩
    refine Finset.mem_product.mpr ?_
    refine ⟨?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨gx, hgx, rfl⟩
    · exact txRealized_mem_optionOfFinset_ground (family := family) (dom := dom) (S := S)
        (X := X) (h0 := h0) (ground := ground) (fiber := fiber) hS hfree hblocked hsub gx
  have hcard_le :
      (G.image
              (rtxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
                fiber hS hfree hblocked)).card ≤
        ((G.image
                (rxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
                  fiber hS hfree hblocked)).product
            (optionOfFinset (α := α) ground)).card :=
    Finset.card_le_card hsubImg
  -- Finish by computing the product card and bounding the option range by `ground.card + 1`.
  have hopt : (optionOfFinset (α := α) ground).card ≤ ground.card + 1 :=
    card_optionOfFinset_le_succ (α := α) ground
  have hopt' :
      ((G.image
              (rxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
                fiber hS hfree hblocked)).product
          (optionOfFinset (α := α) ground)).card ≤
        (G.image
              (rxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
                fiber hS hfree hblocked)).card *
          (ground.card + 1) := by
    -- `card_product = card * card`, then apply `hopt`.
    simpa [Finset.card_product, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      Nat.mul_le_mul_left
        (G.image
              (rxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
                fiber hS hfree hblocked)).card hopt
  exact le_trans hcard_le hopt'

theorem exists_rtxRealized_fiber_ge_div_range
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α))) :
    ∃ rt ∈ S.powerset.product (optionOfFinset (α := α) (family.biUnion id)),
      ((realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked).filter
          (fun gx =>
            rtxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
              fiber hS hfree hblocked gx = rt)).card ≥
        (realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked).card /
          (S.powerset.product (optionOfFinset (α := α) (family.biUnion id))).card := by
  classical
  let range := S.powerset.product (optionOfFinset (α := α) (family.biUnion id))
  by_cases hGX :
      (realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked).Nonempty
  · have himgNonempty :
        (((realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
              fiber hS hfree hblocked).image
            (rtxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
              fiber hS hfree hblocked)).Nonempty) := by
        rcases hGX with ⟨gx, hgx⟩
        refine ⟨rtxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked gx, ?_⟩
        exact Finset.mem_image.mpr ⟨gx, hgx, rfl⟩
    let img :=
      (realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked).image
        (rtxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked)
    let fiberFn : (Finset α × Option α) → ℕ :=
      fun rt =>
        ((realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
              fiber hS hfree hblocked).filter
            (fun gx =>
              rtxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
                fiber hS hfree hblocked gx = rt)).card
    obtain ⟨rt, hrtImg, hrtMax⟩ :=
      Finset.exists_max_image img fiberFn (by simpa [img] using himgNonempty)
    have hrtRange : rt ∈ range :=
      (image_rtxRealized_subset_powerset_product_option (family := family) (dom := dom) (S := S)
          (X := X) (h0 := h0) fiber hS hfree hblocked) hrtImg
    have hsum :
        (realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
              fiber hS hfree hblocked).card =
          ∑ rt' ∈ img, fiberFn rt' := by
      simpa [img, fiberFn] using
        (Finset.card_eq_sum_card_image
          (f := rtxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked)
          (s := realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked))
    have hsum_le :
        (∑ rt' ∈ img, fiberFn rt') ≤ img.card * fiberFn rt := by
      calc
        (∑ rt' ∈ img, fiberFn rt')
            ≤ ∑ _rt' ∈ img, fiberFn rt := by
                refine Finset.sum_le_sum ?_
                intro rt' hrt'
                exact hrtMax rt' hrt'
        _ = img.card * fiberFn rt := by
                simp
    have hcard_le :
        (realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
              fiber hS hfree hblocked).card ≤
          img.card * fiberFn rt := by
      simpa [hsum] using hsum_le
    have himg_le : img.card ≤ range.card := by
      have : img ⊆ range := by
        intro rt' hrt'
        exact (image_rtxRealized_subset_powerset_product_option (family := family) (dom := dom)
          (S := S) (X := X) (h0 := h0) fiber hS hfree hblocked) hrt'
      exact Finset.card_le_card this
    have hcard_le' :
        (realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
              fiber hS hfree hblocked).card ≤
          range.card * fiberFn rt := by
      exact le_trans hcard_le (Nat.mul_le_mul_right (fiberFn rt) himg_le)
    refine ⟨rt, hrtRange, ?_⟩
    simpa [fiberFn, range, Finset.card_product] using (Nat.div_le_of_le_mul hcard_le')
  · have hGX0 :
        realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked = ∅ := by
      simpa [Finset.not_nonempty_iff_eq_empty] using hGX
    refine ⟨(∅, none), by simp [optionOfFinset, Finset.mem_powerset], ?_⟩
    simp [hGX0]

theorem exists_rtxRealized_fiber_ge_three_of_three_mul_range_card_le
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (h3 :
      3 * (S.powerset.card * (optionOfFinset (α := α) (family.biUnion id)).card) ≤
        (realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
              fiber hS hfree hblocked).card) :
    ∃ rt ∈ S.powerset.product (optionOfFinset (α := α) (family.biUnion id)),
      ((realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked).filter
          (fun gx =>
            rtxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
              fiber hS hfree hblocked gx = rt)).card ≥ 3 := by
  classical
  let range := S.powerset.product (optionOfFinset (α := α) (family.biUnion id))
  rcases
      exists_rtxRealized_fiber_ge_div_range (family := family) (dom := dom) (S := S) (X := X)
        (h0 := h0) fiber hS hfree hblocked with
    ⟨rt, hrtRange, hrtFiber⟩
  refine ⟨rt, hrtRange, ?_⟩
  have hpos : 0 < range.card := by
    refine Finset.card_pos.mpr ?_
    refine ⟨(∅, none), ?_⟩
    simp [range, optionOfFinset, Finset.mem_powerset]
  have hdiv :
      3 ≤
        (realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
              fiber hS hfree hblocked).card / range.card := by
    have h3' :
        3 * range.card ≤
          (realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
                fiber hS hfree hblocked).card := by
      simpa [range, Finset.card_product, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h3
    exact (Nat.le_div_iff_mul_le hpos).2 h3'
  exact le_trans hdiv hrtFiber

theorem exists_rxRealized_fiber_ge_div_powerset
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α))) :
    ∃ r ∈ S.powerset,
      ((realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked).filter
          (fun gx =>
            rxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
              fiber hS hfree hblocked gx = r)).card ≥
        (realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked).card / S.powerset.card := by
  classical
  by_cases hGX :
      (realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
        fiber hS hfree hblocked).Nonempty
  · have himgNonempty :
        (((realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
              fiber hS hfree hblocked).image
            (rxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
              fiber hS hfree hblocked)).Nonempty) := by
        rcases hGX with ⟨gx, hgx⟩
        refine ⟨rxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked gx, ?_⟩
        exact Finset.mem_image.mpr ⟨gx, hgx, rfl⟩
    -- Choose an `r` in the image that maximizes the fiber size.
    let img :=
      (realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked).image
        (rxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked)
    let fiberFn : Finset α → ℕ :=
      fun r =>
        ((realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
              fiber hS hfree hblocked).filter
            (fun gx =>
              rxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
                fiber hS hfree hblocked gx = r)).card
    obtain ⟨r, hrimg, hrmax⟩ :=
      Finset.exists_max_image img fiberFn (by simpa [img] using himgNonempty)
    have hrpow : r ∈ S.powerset := by
      exact (image_rxRealized_subset_powerset (family := family) (dom := dom) (S := S) (X := X)
        (h0 := h0) fiber hS hfree hblocked) hrimg
    have hsum :
        (realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
              fiber hS hfree hblocked).card =
          ∑ r' ∈ img, fiberFn r' := by
      simpa [img, fiberFn] using
        (Finset.card_eq_sum_card_image
          (f := rxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked)
          (s := realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked))
    have hsum_le :
        (∑ r' ∈ img, fiberFn r') ≤ img.card * fiberFn r := by
      calc
        (∑ r' ∈ img, fiberFn r')
            ≤ ∑ _r' ∈ img, fiberFn r := by
                refine Finset.sum_le_sum ?_
                intro r' hr'
                exact hrmax r' hr'
        _ = img.card * fiberFn r := by
                simp
    have hcard_le :
        (realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
              fiber hS hfree hblocked).card ≤
          img.card * fiberFn r := by
      simpa [hsum] using hsum_le
    have himg_le : img.card ≤ S.powerset.card :=
      card_image_rxRealized_le_powerset_card (family := family) (dom := dom) (S := S) (X := X)
        (h0 := h0) fiber hS hfree hblocked
    have hcard_le' :
        (realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
              fiber hS hfree hblocked).card ≤
          S.powerset.card * fiberFn r := by
      exact le_trans hcard_le (Nat.mul_le_mul_right (fiberFn r) himg_le)
    refine ⟨r, hrpow, ?_⟩
    simpa [fiberFn] using (Nat.div_le_of_le_mul hcard_le')
  · -- Trivial case: `realizedGoodX` is empty.
    have hGX0 :
        realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
          fiber hS hfree hblocked = ∅ := by
      simpa [Finset.not_nonempty_iff_eq_empty] using hGX
    refine ⟨∅, by simp [Finset.mem_powerset], ?_⟩
    simp [hGX0]

theorem exists_rxRealized_fiber_ge_three_of_three_mul_powerset_card_le
    (fiber : Finset {T // T ∈ dom})
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked :
      ∀ x, x ∈ X → x ∉ S → x ≠ h0 → BlockedByTwo family (S ∪ ({x} : Finset α)))
    (h3 :
      3 * S.powerset.card ≤
        (realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
              fiber hS hfree hblocked).card) :
    ∃ r ∈ S.powerset,
      ((realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
            fiber hS hfree hblocked).filter
          (fun gx =>
            rxRealized (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
              fiber hS hfree hblocked gx = r)).card ≥ 3 := by
  classical
  rcases
      exists_rxRealized_fiber_ge_div_powerset (family := family) (dom := dom) (S := S) (X := X)
        (h0 := h0) fiber hS hfree hblocked with
    ⟨r, hrpow, hrfiber⟩
  refine ⟨r, hrpow, ?_⟩
  have hpos : 0 < S.powerset.card := by
    refine Finset.card_pos.mpr ?_
    refine ⟨(∅ : Finset α), ?_⟩
    simp [Finset.mem_powerset]
  have hdiv :
      3 ≤
        (realizedGoodX (family := family) (dom := dom) (S := S) (X := X) (h0 := h0)
              fiber hS hfree hblocked).card / S.powerset.card := by
    exact (Nat.le_div_iff_mul_le hpos).2 h3
  exact le_trans hdiv hrfiber

end RealizedGoodXPigeonhole

/-!
Bridge lemma: from a hard-branch admissible fiber (fixed realized key `k`) to realized `x`'s
relative to a minimal-card reference completion `S⋆`.

This matches the intended multiplicity strategy:
pick `S⋆` of minimal size in the hard-branch fiber, then every other completion contributes
some `x ∈ X \\ S⋆` that is realized by definition.
-/

section FiberMinCompletion

variable {α : Type*} [DecidableEq α]
variable {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h0 : α}

theorem sdiff_nonempty_of_ne_of_mem_o1aWitnessLiftDomWL
    {Sstar Ssub : Finset α}
    (hSstar : Sstar ∈ o1aWitnessLiftDomWL family h0)
    (hSsub : Ssub ∈ o1aWitnessLiftDomWL family h0)
    (hne : Ssub ≠ Sstar) :
    (Sstar \ Ssub).Nonempty := by
  classical
  -- Unpack `Sstar ∈ domWL` to get `Sstar ∈ family` and `¬ChainExtension family Sstar h0`.
  have hSstar' :
      Sstar ∈
        (o1aWitnessLiftDom family h0).filter
          (fun S => ¬ ChainExtension family S h0 ∧
            ¬ WitnessHasHSingletonCore family (liftAt S h0) h0) := by
    simpa [o1aWitnessLiftDomWL] using hSstar
  have hSstar0 : Sstar ∈ o1aWitnessLiftDom family h0 := (Finset.mem_filter.mp hSstar').1
  have hnoChain : ¬ ChainExtension family Sstar h0 :=
    (Finset.mem_filter.mp hSstar').2.1
  have hSAvoid : Sstar ∈ coreSliceAvoid family h0 := (Finset.mem_filter.mp hSstar0).1
  have hSstarFam : Sstar ∈ family := (Finset.mem_filter.mp hSAvoid).1
  have hh0nSsub : h0 ∉ Ssub := by
    -- `Ssub ∈ domWL` implies `Ssub ∈ coreSliceAvoid`, hence `h0 ∉ Ssub`.
    have hSsub' :
        Ssub ∈
          (o1aWitnessLiftDom family h0).filter
            (fun S => ¬ ChainExtension family S h0 ∧
              ¬ WitnessHasHSingletonCore family (liftAt S h0) h0) := by
      simpa [o1aWitnessLiftDomWL] using hSsub
    have hSsub0 : Ssub ∈ o1aWitnessLiftDom family h0 := (Finset.mem_filter.mp hSsub').1
    have hSAvoid' : Ssub ∈ coreSliceAvoid family h0 := (Finset.mem_filter.mp hSsub0).1
    exact (Finset.mem_filter.mp hSAvoid').2
  -- `Sstar ⊄ Ssub`: otherwise we'd have a chain extension of `Sstar`.
  have hnotSub : ¬ Sstar ⊆ Ssub := by
    intro hsub
    have hSS : Sstar ⊂ Ssub := by
      refine ssubset_iff_subset_not_subset.2 ?_
      refine ⟨hsub, ?_⟩
      intro hsub'
      have hEq : Ssub = Sstar := by
        ext x
        exact ⟨fun hx => hsub' hx, fun hx => hsub hx⟩
      exact hne hEq
    have hChain : ChainExtension family Sstar h0 := by
      refine ⟨Ssub, ?_, hSS, hh0nSsub⟩
      -- `Ssub ∈ family` from `domWL`.
      have hSsub' :
          Ssub ∈
            (o1aWitnessLiftDom family h0).filter
              (fun S => ¬ ChainExtension family S h0 ∧
                ¬ WitnessHasHSingletonCore family (liftAt S h0) h0) := by
        simpa [o1aWitnessLiftDomWL] using hSsub
      have hSsub0 : Ssub ∈ o1aWitnessLiftDom family h0 := (Finset.mem_filter.mp hSsub').1
      have hSAvoid' : Ssub ∈ coreSliceAvoid family h0 := (Finset.mem_filter.mp hSsub0).1
      exact (Finset.mem_filter.mp hSAvoid').1
    exact hnoChain hChain
  -- Extract an element in `Sstar \ Ssub`.
  rcases Finset.not_subset.mp hnotSub with ⟨x, hxSstar, hxnot⟩
  exact ⟨x, Finset.mem_sdiff.mpr ⟨hxSstar, hxnot⟩⟩

/-!
Step (1) of the “minimal-card reference completion” bridge:
given `S⋆ ∈ fiber` and the fact that every other completion `S'` has some realized
`x ∈ (S' \\ S⋆) ∩ X`, we can cover the fiber by `{S⋆}` plus the union of the per-`x`
subfibers.

We do **not** assume injectivity `completion ↦ x`; we only use the union bound:
`card (⋃_x Fiber_x) ≤ ∑_x card (Fiber_x)`.
-/

noncomputable def wlcertAdmissibleFiber_hNotMem_fiberForX
    {α : Type*} [DecidableEq α]
    {dom : Finset (Finset α)} (fiber : Finset {S // S ∈ dom})
    (Sstar : Finset α) (x : α) : Finset {S // S ∈ dom} := by
  classical
  exact fiber.filter (fun Ssub => x ∈ Ssub.1 ∧ x ∉ Sstar)

theorem card_le_one_add_sum_card_fiberForX_of_cover
    {α : Type*} [DecidableEq α]
    {dom : Finset (Finset α)} (fiber : Finset {S // S ∈ dom})
    (Sstar : {S // S ∈ dom}) (X : Finset α)
    (hSstar : Sstar ∈ fiber)
    (hcover :
      ∀ Ssub ∈ fiber, Ssub ≠ Sstar →
        ∃ x, x ∈ realizedXSet (dom := dom) fiber Sstar.1 X ∧ x ∈ Ssub.1 ∧ x ∉ Sstar.1) :
    fiber.card ≤
      1 +
        ∑ x ∈ realizedXSet (dom := dom) fiber Sstar.1 X,
          (wlcertAdmissibleFiber_hNotMem_fiberForX (dom := dom) fiber Sstar.1 x).card := by
  classical
  -- Let `R` be the set of realized `x`'s relative to the reference completion `S⋆`.
  let R : Finset α := realizedXSet (dom := dom) fiber Sstar.1 X
  let U : Finset {S // S ∈ dom} :=
    R.biUnion (fun x => wlcertAdmissibleFiber_hNotMem_fiberForX (dom := dom) fiber Sstar.1 x)
  have hsub : fiber ⊆ insert Sstar U := by
    intro Ssub hSsub
    by_cases hEq : Ssub = Sstar
    · simpa [hEq] using Finset.mem_insert_self Sstar U
    · have hx := hcover Ssub hSsub hEq
      rcases hx with ⟨x, hxR, hxSsub', hxnot⟩
      have hmemFx :
          Ssub ∈ wlcertAdmissibleFiber_hNotMem_fiberForX (dom := dom) fiber Sstar.1 x := by
        refine Finset.mem_filter.mpr ?_
        exact ⟨hSsub, hxSsub', hxnot⟩
      have hmemU : Ssub ∈ U := by
        refine Finset.mem_biUnion.mpr ?_
        refine ⟨x, ?_, hmemFx⟩
        simpa [R] using hxR
      exact Finset.mem_insert_of_mem hmemU
  have hcard1 : fiber.card ≤ (insert Sstar U).card := Finset.card_le_card hsub
  have hcard2 : (insert Sstar U).card ≤ U.card + 1 := by
    simpa [Nat.add_comm] using (Finset.card_insert_le Sstar U)
  have hcardU :
      U.card ≤
        ∑ x ∈ R,
          (wlcertAdmissibleFiber_hNotMem_fiberForX (dom := dom) fiber Sstar.1 x).card := by
    -- Union bound over the `x`-subfibers.
    simpa [U] using
      (Finset.card_biUnion_le (s := R)
        (t := fun x => wlcertAdmissibleFiber_hNotMem_fiberForX (dom := dom) fiber Sstar.1 x))
  -- Combine the inequalities.
  have :
      fiber.card ≤ (∑ x ∈ R,
          (wlcertAdmissibleFiber_hNotMem_fiberForX (dom := dom) fiber Sstar.1 x).card) + 1 := by
    exact le_trans hcard1 (le_trans hcard2 (Nat.add_le_add_right hcardU 1))
  -- Rewrite `R` back to `realizedXSet`.
  simpa [R, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this

theorem exists_minCard_mem_wlcertAdmissibleFiber_hNotMem_and_realizedX_of_ne
    (hreg : O1aUpgradeRegime family ground A0 h0)
    (k : WLcertKey α) :
    let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h0
    let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
    let kh : α := k.1
    let kA : Finset α := k.2.2.1
    let kB : Finset α := k.2.2.2.1
    let kcore : Finset α := k.2.2.2.2
    let X : Finset α := ground \ (kA ∪ kB)
    fiber.Nonempty →
      ∃ Sstar ∈ fiber,
        (∀ Ssub ∈ fiber, Ssub ≠ Sstar →
          ∃ x, x ∈ realizedXSet (dom := dom) fiber Sstar.1 X ∧ x ∈ Ssub.1 ∧ x ∉ Sstar.1) := by
  intro dom fiber kh kA kB kcore X hne
  classical
  -- Choose `S⋆` of minimal cardinality in the fiber.
  obtain ⟨Sstar, hSstar, hmin⟩ :=
    Finset.exists_min_image fiber (fun Ssub : {S // S ∈ dom} => Ssub.1.card) hne
  refine ⟨Sstar, hSstar, ?_⟩
  intro Ssub hSsub hne'
  -- From minimality: `Ssub \ Sstar` is nonempty.
  have hdiff_ne : (Ssub.1 \ Sstar.1).Nonempty := by
    by_contra h0
    have hsub : Ssub.1 ⊆ Sstar.1 := by
      intro x hx
      by_contra hxnot
      have : x ∈ Ssub.1 \ Sstar.1 := Finset.mem_sdiff.mpr ⟨hx, hxnot⟩
      exact h0 ⟨x, this⟩
    have hcard_le : Ssub.1.card ≤ Sstar.1.card := Finset.card_le_card hsub
    have hcard_ge : Sstar.1.card ≤ Ssub.1.card := hmin Ssub hSsub
    have hcard_eq : Ssub.1.card = Sstar.1.card := le_antisymm hcard_le hcard_ge
    have hEq : Ssub.1 = Sstar.1 := Finset.eq_of_subset_of_card_le hsub (by simpa [hcard_eq])
    exact hne' (Subtype.ext hEq)
  -- Choose an `x ∈ Ssub \ Sstar`.
  let x : α := Classical.choose hdiff_ne
  have hx_diff : x ∈ Ssub.1 \ Sstar.1 := Classical.choose_spec hdiff_ne
  have hxSsub : x ∈ Ssub.1 := (Finset.mem_sdiff.mp hx_diff).1
  have hxnotSstar : x ∉ Sstar.1 := (Finset.mem_sdiff.mp hx_diff).2
  -- Show `x ∈ X = ground \\ (A ∪ B)` using the fixed trace on `A ∪ B`.
  have hSstarDom : Sstar.1 ∈ o1aWitnessLiftDomWL family h0 := Sstar.2
  have hSsubDom : Ssub.1 ∈ o1aWitnessLiftDomWL family h0 := Ssub.2
  have hcert_star :
      ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
    (Finset.mem_filter.mp hSstar).2
  have hcert_sub :
      ∃ cert : WLcert family Ssub.1, WLcert.key cert = k ∧ cert.h ∉ Ssub.1 :=
    (Finset.mem_filter.mp hSsub).2
  have htr_star :=
    (wlcert_hNotMem_reduction_o1aDomWL (family := family) (ground := ground) (A0 := A0) (h0 := h0)
      hreg (k := k) (S := Sstar.1) hSstarDom hcert_star)
  have htr_sub :=
    (wlcert_hNotMem_reduction_o1aDomWL (family := family) (ground := ground) (A0 := A0) (h0 := h0)
      hreg (k := k) (S := Ssub.1) hSsubDom hcert_sub)
  have hAB_star : Sstar.1 ∩ (kA ∪ kB) = kcore.erase kh := htr_star.2.2.1
  have hAB_sub : Ssub.1 ∩ (kA ∪ kB) = kcore.erase kh := htr_sub.2.2.1
  have hx_not_mem_AB : x ∉ kA ∪ kB := by
    intro hxAB
    have hxIn_inter : x ∈ Ssub.1 ∩ (kA ∪ kB) := Finset.mem_inter.mpr ⟨hxSsub, hxAB⟩
    have hxBase : x ∈ kcore.erase kh := by simpa [hAB_sub] using hxIn_inter
    have hxIn_star_inter : x ∈ Sstar.1 ∩ (kA ∪ kB) := by simpa [hAB_star] using hxBase
    exact hxnotSstar (Finset.mem_inter.mp hxIn_star_inter).1
  have hx_ground : x ∈ ground := by
    -- `Ssub ⊆ ground` from the regime.
    have hground : family ⊆ ground.powerset := hreg.1
    have hSsubFam : Ssub.1 ∈ family := by
      -- membership in `domWL` implies membership in `family` via `coreSliceAvoid`.
      have hSA : Ssub.1 ∈ coreSliceAvoid family h0 := by
        have : Ssub.1 ∈ o1aWitnessLiftDom family h0 := (Finset.mem_filter.mp (by
          have : Ssub.1 ∈ (o1aWitnessLiftDom family h0).filter
              (fun S => ¬ ChainExtension family S h0 ∧
                ¬ WitnessHasHSingletonCore family (liftAt S h0) h0) := by
            simpa [o1aWitnessLiftDomWL] using hSsubDom
          exact this)).1
        exact (Finset.mem_filter.mp this).1
      exact (Finset.mem_filter.mp hSA).1
    have hSsub_sub : Ssub.1 ⊆ ground := Finset.mem_powerset.mp (hground hSsubFam)
    exact hSsub_sub hxSsub
  have hxX : x ∈ X := Finset.mem_sdiff.mpr ⟨hx_ground, hx_not_mem_AB⟩
  -- Finally, `x` is realized by the completion `Ssub`.
  have hxReal : x ∈ realizedXSet (dom := dom) fiber Sstar.1 X := by
    refine Finset.mem_biUnion.mpr ?_
    refine ⟨Ssub, hSsub, ?_⟩
    have : x ∈ (Ssub.1 \ Sstar.1) ∩ X := by
      exact Finset.mem_inter.mpr ⟨hx_diff, hxX⟩
    simpa using this
  exact ⟨x, hxReal, hxSsub, hxnotSstar⟩

end FiberMinCompletion

/-!
Per-`x` subfiber signature scaffold (hard-branch multiplicity).

For a fixed realized key `k` and a fixed minimal-card reference completion `S⋆` in the hard fiber,
we cover the hard fiber by `{S⋆}` plus the union of per-`x` subfibers.

The remaining missing piece for the multiplicity bound is a *polynomial* bound on each per-`x`
subfiber. The intended mechanism is:

1. For each completion `S` in the subfiber, choose a missing element `y(S) ∈ S⋆ \\ S`.
2. Use the O₁a hard-branch reduction to get `BlockedByTwo family (S ∪ {y(S)})`.
3. Extract a constant-size trace signature from a chosen blocking witness for `S ∪ {y(S)}`.
4. Prove `3`-collision on the signature forces a `3`-sunflower inside `family` (among completions),
   giving a per-bucket bound (≤ 2) and hence a polynomial bound on the subfiber.

Implementation note: the signatures below are intentionally lightweight and only depend on
`BlockedUnionWitness` (not on the `GoodX` / `RealizedGoodX` apparatus for fixed reference `S`).
-/

section PerXSubfiber

variable {α : Type*} [DecidableEq α]
variable {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h0 : α}

noncomputable def chooseMissingFromRef
    (Sstar Ssub : Finset α)
    (hSstar : Sstar ∈ o1aWitnessLiftDomWL family h0)
    (hSsub : Ssub ∈ o1aWitnessLiftDomWL family h0)
    (hne : Ssub ≠ Sstar) : α :=
  Classical.choose
    (sdiff_nonempty_of_ne_of_mem_o1aWitnessLiftDomWL
      (family := family) (h0 := h0) (Sstar := Sstar) (Ssub := Ssub) hSstar hSsub hne)

theorem chooseMissingFromRef_spec
    (Sstar Ssub : Finset α)
    (hSstar : Sstar ∈ o1aWitnessLiftDomWL family h0)
    (hSsub : Ssub ∈ o1aWitnessLiftDomWL family h0)
    (hne : Ssub ≠ Sstar) :
    chooseMissingFromRef (family := family) (h0 := h0) Sstar Ssub hSstar hSsub hne ∈
      Sstar \ Ssub := by
  classical
  simpa [chooseMissingFromRef] using
    (Classical.choose_spec
      (sdiff_nonempty_of_ne_of_mem_o1aWitnessLiftDomWL
        (family := family) (h0 := h0) (Sstar := Sstar) (Ssub := Ssub) hSstar hSsub hne))

/-!
Trace extraction from a `BlockedUnionWitness`.

This mirrors the earlier `tx2Plus` construction, but works directly from an arbitrary
`BlockedUnionWitness family S x`.
-/

noncomputable def tx2PlusOfWitness (w : BlockedUnionWitness family S x) :
    Option (α × Option α × Bool) := by
  classical
  let extras : Finset α := w.A \ insert x S
  by_cases hex : extras.Nonempty
  · let t1 : α := Classical.choose hex
    let extras2 : Finset α := extras.erase t1
    by_cases hex2 : extras2.Nonempty
    · let t2 : α := Classical.choose hex2
      let extras3 : Finset α := extras2.erase t2
      by_cases hex3 : extras3.Nonempty
      · exact some (t1, some t2, true)
      · exact some (t1, some t2, false)
    · exact some (t1, none, false)
  · exact none

theorem mem_extras_of_tx2PlusOfWitness_eq_some
    {α : Type*} [DecidableEq α] {family : Finset (Finset α)} {S : Finset α} {x : α}
    (w : BlockedUnionWitness family S x) {triple : α × Option α × Bool}
    (ht : tx2PlusOfWitness (family := family) (S := S) (x := x) w = some triple) :
    triple.1 ∈ w.A \ insert x S := by
  classical
  let extras : Finset α := w.A \ insert x S
  by_cases hex : extras.Nonempty
  · let t1 : α := Classical.choose hex
    have ht1mem : t1 ∈ extras := Classical.choose_spec hex
    let extras2 : Finset α := extras.erase t1
    by_cases hex2 : extras2.Nonempty
    · let t2 : α := Classical.choose hex2
      let extras3 : Finset α := extras2.erase t2
      by_cases hex3 : extras3.Nonempty
      · have ht_def :
            tx2PlusOfWitness (family := family) (S := S) (x := x) w =
              some (t1, some t2, true) := by
          simp [tx2PlusOfWitness, extras, hex, t1, extras2, hex2, t2, extras3, hex3]
        have hsome : some (t1, some t2, true) = some triple := by
          simpa [ht_def] using ht
        have htriple : (t1, some t2, true) = triple := Option.some.inj hsome
        have ht1 : t1 = triple.1 := by
          simpa using congrArg (fun p : α × Option α × Bool => p.1) htriple
        have : triple.1 ∈ extras := by simpa [ht1] using ht1mem
        simpa [extras] using this
      · have ht_def :
            tx2PlusOfWitness (family := family) (S := S) (x := x) w =
              some (t1, some t2, false) := by
          simp [tx2PlusOfWitness, extras, hex, t1, extras2, hex2, t2, extras3, hex3]
        have hsome : some (t1, some t2, false) = some triple := by
          simpa [ht_def] using ht
        have htriple : (t1, some t2, false) = triple := Option.some.inj hsome
        have ht1 : t1 = triple.1 := by
          simpa using congrArg (fun p : α × Option α × Bool => p.1) htriple
        have : triple.1 ∈ extras := by simpa [ht1] using ht1mem
        simpa [extras] using this
    · have ht_def :
          tx2PlusOfWitness (family := family) (S := S) (x := x) w =
            some (t1, (none : Option α), false) := by
        simp [tx2PlusOfWitness, extras, hex, t1, extras2, hex2]
      have hsome : some (t1, (none : Option α), false) = some triple := by
        simpa [ht_def] using ht
      have htriple : (t1, (none : Option α), false) = triple := Option.some.inj hsome
      have ht1 : t1 = triple.1 := by
        simpa using congrArg (fun p : α × Option α × Bool => p.1) htriple
      have : triple.1 ∈ extras := by simpa [ht1] using ht1mem
      simpa [extras] using this
  · have ht_none :
        tx2PlusOfWitness (family := family) (S := S) (x := x) w = none := by
      simp [tx2PlusOfWitness, extras, hex]
    cases (by simpa [ht_none] using ht : (none : Option (α × Option α × Bool)) = some triple)

namespace BlockedUnionWitness

variable {α : Type*} [DecidableEq α]
variable {family : Finset (Finset α)} {S : Finset α} {x : α}

def swap (w : BlockedUnionWitness family S x) : BlockedUnionWitness family S x :=
  { A := w.B
    hA := w.hB
    B := w.A
    hB := w.hA
    hneAB := w.hneAB.symm
    core := w.core
    hcoreAB := by simpa [Finset.inter_comm] using w.hcoreAB
    hcoreAT := w.hcoreBT
    hcoreBT := w.hcoreAT
    htag := by
      rcases w.htag with hx | hA | hB
      · exact Or.inl hx
      · exact Or.inr (Or.inr hA)
      · exact Or.inr (Or.inl hB) }

def normalizeA (w : BlockedUnionWitness family S x) : BlockedUnionWitness family S x :=
  if h : w.A = S then swap (family := family) (S := S) (x := x) w else w

theorem normalizeA_A_ne_S (w : BlockedUnionWitness family S x) :
    (normalizeA (family := family) (S := S) (x := x) w).A ≠ S := by
  classical
  by_cases h : w.A = S
  · -- The swapped witness has `A = w.B`, which cannot equal `S` because `w.A ≠ w.B`.
    have hwB : w.B ≠ S := by
      intro hEq
      apply w.hneAB
      -- `w.A = S` and `w.B = S` contradict `A ≠ B`.
      simpa [h, hEq]
    simpa [normalizeA, h, swap] using hwB
  · simpa [normalizeA, h] using h

end BlockedUnionWitness

noncomputable def chooseBlockedUnionWitnessNorm {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {S : Finset α} {x : α}
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked : BlockedByTwo family (S ∪ ({x} : Finset α))) :
    BlockedUnionWitness family S x :=
  BlockedUnionWitness.normalizeA (family := family) (S := S) (x := x)
    (chooseBlockedUnionWitness (family := family) (S := S) (x := x) hS hfree hblocked)

theorem chooseBlockedUnionWitnessNorm_A_ne_S {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {S : Finset α} {x : α}
    (hS : S ∈ family) (hfree : IsSunflowerFree family 3)
    (hblocked : BlockedByTwo family (S ∪ ({x} : Finset α))) :
    (chooseBlockedUnionWitnessNorm (family := family) (S := S) (x := x)
          hS hfree hblocked).A ≠ S := by
  classical
  simpa [chooseBlockedUnionWitnessNorm] using
    BlockedUnionWitness.normalizeA_A_ne_S
      (family := family) (S := S) (x := x)
      (chooseBlockedUnionWitness (family := family) (S := S) (x := x) hS hfree hblocked)

theorem A_sdiff_insert_subset_pair_of_tx2PlusOfWitness_eq_some_some_false
    {α : Type*} [DecidableEq α] {family : Finset (Finset α)} {S : Finset α} {x : α}
    (w : BlockedUnionWitness family S x) {t1 t2 : α}
    (htx : tx2PlusOfWitness (family := family) (S := S) (x := x) w = some (t1, some t2, false)) :
    w.A \ insert x S ⊆ ({t1, t2} : Finset α) := by
  classical
  -- Mirror the definition of `tx2PlusOfWitness` and extract the “no third extra” consequence.
  let extras : Finset α := w.A \ insert x S
  by_cases hex : extras.Nonempty
  · let t1' : α := Classical.choose hex
    let extras2 : Finset α := extras.erase t1'
    by_cases hex2 : extras2.Nonempty
    · let t2' : α := Classical.choose hex2
      let extras3 : Finset α := extras2.erase t2'
      by_cases hex3 : extras3.Nonempty
      · -- Contradiction: definition would return `true`.
        have htx_def :
            tx2PlusOfWitness (family := family) (S := S) (x := x) w =
              some (t1', some t2', true) := by
          simp [tx2PlusOfWitness, extras, hex, t1', extras2, hex2, t2', extras3, hex3]
        have : False := by
          have hsome : some (t1', some t2', true) = some (t1, some t2, false) := by
            simpa [htx_def] using htx
          have hpair := Option.some.inj hsome
          have hsecond : (some t2', true) = (some t2, false) := congrArg Prod.snd hpair
          have hbool : true = false := congrArg Prod.snd hsecond
          cases hbool
        exact False.elim this
      · -- The intended branch: no third extra beyond `t1',t2'`.
        have htx_def :
            tx2PlusOfWitness (family := family) (S := S) (x := x) w =
              some (t1', some t2', false) := by
          simp [tx2PlusOfWitness, extras, hex, t1', extras2, hex2, t2', extras3, hex3]
        have hsome : some (t1', some t2', false) = some (t1, some t2, false) := by
          simpa [htx_def] using htx
        have hpair := Option.some.inj hsome
        have htEq1 : t1' = t1 := congrArg Prod.fst hpair
        have htEq2 : t2' = t2 := by
          have : (some t2', false) = (some t2, false) := congrArg Prod.snd hpair
          have : some t2' = some t2 := congrArg Prod.fst this
          exact Option.some.inj this
        have hNoMore : extras3 = (∅ : Finset α) := by
          simpa [Finset.not_nonempty_iff_eq_empty] using hex3
        have hNoMore' : (extras.erase t1).erase t2 = (∅ : Finset α) := by
          simpa [extras2, extras3, htEq1, htEq2] using hNoMore
        intro z hz
        by_cases hz1 : z = t1
        · subst hz1
          simp
        · have hzErase1 : z ∈ extras.erase t1 := Finset.mem_erase.mpr ⟨hz1, by simpa [extras] using hz⟩
          by_cases hz2 : z = t2
          · subst hz2
            simp [hz1]
          · have hzErase2 : z ∈ (extras.erase t1).erase t2 := Finset.mem_erase.mpr ⟨hz2, hzErase1⟩
            have : False := by
              have : z ∈ (∅ : Finset α) := by simpa [hNoMore'] using hzErase2
              simpa using this
            exact False.elim this
    · -- Contradiction: definition would return `none` as second component.
      have htx_def :
          tx2PlusOfWitness (family := family) (S := S) (x := x) w =
            some (t1', (none : Option α), false) := by
        simp [tx2PlusOfWitness, extras, hex, t1', extras2, hex2]
      have : False := by
        have hsome : some (t1', (none : Option α), false) = some (t1, some t2, false) := by
          simpa [htx_def] using htx
        have hpair := Option.some.inj hsome
        have hsecond : ((none : Option α), false) = (some t2, false) := congrArg Prod.snd hpair
        have hnone : (none : Option α) = some t2 := congrArg Prod.fst hsecond
        cases hnone
      exact False.elim this
  · -- Contradiction: definition would return `none`.
    have htx_none :
        tx2PlusOfWitness (family := family) (S := S) (x := x) w = none := by
      simp [tx2PlusOfWitness, extras, hex]
    have : False := by
      have : (none : Option (α × Option α × Bool)) = some (t1, some t2, false) := by
        simpa [htx_none] using htx
      cases this
    exact False.elim this

theorem A_sdiff_insert_subset_singleton_of_tx2PlusOfWitness_eq_some_none_false
    {α : Type*} [DecidableEq α] {family : Finset (Finset α)} {S : Finset α} {x : α}
    (w : BlockedUnionWitness family S x) {t1 : α}
    (htx : tx2PlusOfWitness (family := family) (S := S) (x := x) w = some (t1, none, false)) :
    w.A \ insert x S ⊆ ({t1} : Finset α) := by
  classical
  let extras : Finset α := w.A \ insert x S
  by_cases hex : extras.Nonempty
  · let t1' : α := Classical.choose hex
    let extras2 : Finset α := extras.erase t1'
    by_cases hex2 : extras2.Nonempty
    · -- Contradiction: definition would return `some (t1', some t2', _)`.
      let t2' : α := Classical.choose hex2
      let extras3 : Finset α := extras2.erase t2'
      by_cases hex3 : extras3.Nonempty
      · have htx_def :
            tx2PlusOfWitness (family := family) (S := S) (x := x) w =
              some (t1', some t2', true) := by
          simp [tx2PlusOfWitness, extras, hex, t1', extras2, hex2, t2', extras3, hex3]
        have : False := by
          have hsome : some (t1', some t2', true) = some (t1, none, false) := by
            simpa [htx_def] using htx
          have hpair := Option.some.inj hsome
          have hsecond : (some t2', true) = (none, false) := congrArg Prod.snd hpair
          have hnone : some t2' = none := congrArg Prod.fst hsecond
          cases hnone
        exact False.elim this
      · have htx_def :
            tx2PlusOfWitness (family := family) (S := S) (x := x) w =
              some (t1', some t2', false) := by
          simp [tx2PlusOfWitness, extras, hex, t1', extras2, hex2, t2', extras3, hex3]
        have : False := by
          have hsome : some (t1', some t2', false) = some (t1, none, false) := by
            simpa [htx_def] using htx
          have hpair := Option.some.inj hsome
          have hsecond : (some t2', false) = (none, false) := congrArg Prod.snd hpair
          have hnone : some t2' = none := congrArg Prod.fst hsecond
          cases hnone
        exact False.elim this
    · -- Intended branch: no second extra beyond `t1'`.
      have htx_def :
          tx2PlusOfWitness (family := family) (S := S) (x := x) w =
            some (t1', (none : Option α), false) := by
        simp [tx2PlusOfWitness, extras, hex, t1', extras2, hex2]
      have hsome : some (t1', (none : Option α), false) = some (t1, none, false) := by
        simpa [htx_def] using htx
      have hpair := Option.some.inj hsome
      have htEq1 : t1' = t1 := congrArg Prod.fst hpair
      have hNoMore : extras2 = (∅ : Finset α) := by
        simpa [Finset.not_nonempty_iff_eq_empty] using hex2
      have hNoMore' : extras.erase t1 = (∅ : Finset α) := by
        simpa [extras2, htEq1] using hNoMore
      intro z hz
      by_cases hz1 : z = t1
      · subst hz1
        simp
      · have hzErase : z ∈ extras.erase t1 := Finset.mem_erase.mpr ⟨hz1, by simpa [extras] using hz⟩
        have : False := by
          have : z ∈ (∅ : Finset α) := by simpa [hNoMore'] using hzErase
          simpa using this
        exact False.elim this
  · -- Contradiction: definition would return `none`.
    have htx_none :
        tx2PlusOfWitness (family := family) (S := S) (x := x) w = none := by
      simp [tx2PlusOfWitness, extras, hex]
    have : False := by
      have : (none : Option (α × Option α × Bool)) = some (t1, none, false) := by
        simpa [htx_none] using htx
      cases this
    exact False.elim this

/-!
Per-`x` subfiber collision invariants.

In the multiplicity proof for a fixed realized key `k`, we will:
1. fix a minimal-card reference completion `S⋆` in the hard-branch fiber,
2. cover the fiber by `{S⋆}` plus per-`x` subfibers, and
3. bound each per-`x` subfiber by bucketing completions `S` using a fixed missing `y ∈ S⋆ \\ S`
   together with a blocking-witness signature for `S ∪ {y}`.

The intended “fixed anchor” for these buckets is `keyBase := kcore.erase kh`, the common trace
of all completions on `kA ∪ kB` in the hard branch.
-/

namespace PerXSubfiber

variable {α : Type*} [DecidableEq α]
variable {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h0 : α}

/-- The fixed hard-branch base for a realized key `k = (h,j,A,B,core)`. -/
def keyBase (k : WLcertKey α) : Finset α :=
  let kh : α := k.1
  let kcore : Finset α := k.2.2.2.2
  kcore.erase kh

/-- Build the normalized chosen blocking witness for `S ∪ {y}` in the hard-branch regime. -/
noncomputable def chooseBlockedUnionWitnessNorm_of_hNotMem_reduction
    (hreg : O1aUpgradeRegime family ground A0 h0)
    {k : WLcertKey α} {S : Finset α}
    (hSdom : S ∈ o1aWitnessLiftDomWL family h0)
    (hcert : ∃ cert : WLcert family S, WLcert.key cert = k ∧ cert.h ∉ S)
    {y : α} (hyX : y ∈ (ground \ (k.2.2.1 ∪ k.2.2.2.1))) (hyNot : y ∉ S) (hy0 : y ≠ h0) :
    BlockedUnionWitness family S y := by
  classical
  -- Unpack `S ∈ domWL` to get `S ∈ family`.
  have hS' :
      S ∈
        (o1aWitnessLiftDom family h0).filter
          (fun S => ¬ ChainExtension family S h0 ∧
            ¬ WitnessHasHSingletonCore family (liftAt S h0) h0) := by
    simpa [o1aWitnessLiftDomWL] using hSdom
  have hS0 : S ∈ o1aWitnessLiftDom family h0 := (Finset.mem_filter.mp hS').1
  have hSAvoid : S ∈ coreSliceAvoid family h0 := (Finset.mem_filter.mp hS0).1
  have hSfam : S ∈ family := (Finset.mem_filter.mp hSAvoid).1
  have hfree : IsSunflowerFree family 3 := hreg.2.1
  -- Use the hard-branch reduction to get `BlockedByTwo family (S ∪ {y})`.
  have htr :=
    (wlcert_hNotMem_reduction_o1aDomWL (family := family) (ground := ground) (A0 := A0) (h0 := h0)
      hreg (k := k) (S := S) hSdom hcert)
  -- Extract `BlockedByTwo` from the last conjunct.
  have hblocked : BlockedByTwo family (S ∪ ({y} : Finset α)) :=
    (htr.2.2.2.2.2 y hyX hyNot hy0).2
  exact
    chooseBlockedUnionWitnessNorm (family := family) (S := S) (x := y)
      hSfam hfree hblocked

/-!
Per-`x` plumbing helpers.

When we choose `y(S) ∈ S⋆ \\ S` inside the hard-branch fiber for a fixed key `k`, we need
to know `y(S) ∈ X := ground \\ (kA ∪ kB)` so that the hard-branch reduction can supply
`BlockedByTwo family (S ∪ {y(S)})`.
-/

theorem mem_family_of_mem_o1aWitnessLiftDomWL
    {S : Finset α} (hSdom : S ∈ o1aWitnessLiftDomWL family h0) :
    S ∈ family := by
  classical
  have hS' :
      S ∈
        (o1aWitnessLiftDom family h0).filter
          (fun S => ¬ ChainExtension family S h0 ∧
            ¬ WitnessHasHSingletonCore family (liftAt S h0) h0) := by
    simpa [o1aWitnessLiftDomWL] using hSdom
  have hS0 : S ∈ o1aWitnessLiftDom family h0 := (Finset.mem_filter.mp hS').1
  have hSAvoid : S ∈ coreSliceAvoid family h0 := (Finset.mem_filter.mp hS0).1
  exact (Finset.mem_filter.mp hSAvoid).1

theorem chooseMissingFromRef_mem_X_of_hardFiber
    (hreg : O1aUpgradeRegime family ground A0 h0)
    {k : WLcertKey α} {Sstar Ssub : Finset α}
    (hSstarDom : Sstar ∈ o1aWitnessLiftDomWL family h0)
    (hSsubDom : Ssub ∈ o1aWitnessLiftDomWL family h0)
    (hcert_star : ∃ cert : WLcert family Sstar, WLcert.key cert = k ∧ cert.h ∉ Sstar)
    (hcert_sub : ∃ cert : WLcert family Ssub, WLcert.key cert = k ∧ cert.h ∉ Ssub)
    (hne : Ssub ≠ Sstar) :
    let y : α :=
      chooseMissingFromRef (family := family) (h0 := h0) Sstar Ssub hSstarDom hSsubDom hne
    y ∈ (ground \ (k.2.2.1 ∪ k.2.2.2.1)) := by
  classical
  intro y
  have hyDiff :
      y ∈ Sstar \ Ssub :=
    chooseMissingFromRef_spec (family := family) (h0 := h0) Sstar Ssub hSstarDom hSsubDom hne
  have hySstar : y ∈ Sstar := (Finset.mem_sdiff.mp hyDiff).1
  have hyNotSsub : y ∉ Ssub := (Finset.mem_sdiff.mp hyDiff).2
  -- `y ∈ ground` since `S⋆ ⊆ ground`.
  have hSstarFam : Sstar ∈ family :=
    mem_family_of_mem_o1aWitnessLiftDomWL (family := family) (h0 := h0) hSstarDom
  have hSstarSub : Sstar ⊆ ground := by
    rcases hreg with ⟨hground, _hfree, _hmax, _hfail, _hanch⟩
    exact Finset.mem_powerset.mp (hground hSstarFam)
  have hyGround : y ∈ ground := hSstarSub hySstar
  -- Show `y ∉ kA ∪ kB` using the fixed hard-branch trace on `S⋆` and `S`.
  have htr_star :=
    wlcert_hNotMem_reduction_o1aDomWL (family := family) (ground := ground) (A0 := A0) (h0 := h0)
      hreg (k := k) (S := Sstar) hSstarDom hcert_star
  have htr_sub :=
    wlcert_hNotMem_reduction_o1aDomWL (family := family) (ground := ground) (A0 := A0) (h0 := h0)
      hreg (k := k) (S := Ssub) hSsubDom hcert_sub
  have hyNotAB : y ∉ (k.2.2.1 ∪ k.2.2.2.1) := by
    intro hyAB
    -- From `S⋆ ∩ (kA ∪ kB) = keyBase`, deduce `y ∈ keyBase`.
    have hyBase : y ∈ keyBase (k := k) := by
      have : y ∈ Sstar ∩ (k.2.2.1 ∪ k.2.2.2.1) := Finset.mem_inter.mpr ⟨hySstar, hyAB⟩
      simpa [keyBase, htr_star.2.2.1] using this
    -- From `kA ∩ S = keyBase`, deduce `y ∈ S`, contradiction.
    have hyInSsub : y ∈ Ssub := by
      have hyBase' : y ∈ (k.2.2.2.2).erase (k.1) := by
        simpa [keyBase] using hyBase
      have hEq : (k.2.2.2.2).erase (k.1) = k.2.2.1 ∩ Ssub := by
        simpa using htr_sub.1.symm
      have : y ∈ k.2.2.1 ∩ Ssub := by
        simpa [hEq] using hyBase'
      exact (Finset.mem_inter.mp this).2
    exact hyNotSsub hyInSsub
  exact Finset.mem_sdiff.mpr ⟨hyGround, hyNotAB⟩

theorem chooseMissingFromRef_ne_h0_of_hardFiber
    {Sstar Ssub : Finset α}
    (hSstarDom : Sstar ∈ o1aWitnessLiftDomWL family h0)
    (hSsubDom : Ssub ∈ o1aWitnessLiftDomWL family h0)
    (hne : Ssub ≠ Sstar) :
    let y : α :=
      chooseMissingFromRef (family := family) (h0 := h0) Sstar Ssub hSstarDom hSsubDom hne
    y ≠ h0 := by
  classical
  intro y
  have hyDiff :
      y ∈ Sstar \ Ssub :=
    chooseMissingFromRef_spec (family := family) (h0 := h0) Sstar Ssub hSstarDom hSsubDom hne
  have hySstar : y ∈ Sstar := (Finset.mem_sdiff.mp hyDiff).1
  -- `h0 ∉ S⋆` since `S⋆ ∈ coreSliceAvoid`.
  have hh0nSstar : h0 ∉ Sstar := by
    have hSstar' :
        Sstar ∈
          (o1aWitnessLiftDom family h0).filter
            (fun S => ¬ ChainExtension family S h0 ∧
              ¬ WitnessHasHSingletonCore family (liftAt S h0) h0) := by
      simpa [o1aWitnessLiftDomWL] using hSstarDom
    have hSstar0 : Sstar ∈ o1aWitnessLiftDom family h0 := (Finset.mem_filter.mp hSstar').1
    have hSAvoid : Sstar ∈ coreSliceAvoid family h0 := (Finset.mem_filter.mp hSstar0).1
    exact (Finset.mem_filter.mp hSAvoid).2
  intro hEq
  have : h0 ∈ Sstar := by
    simpa [hEq] using hySstar
  exact hh0nSstar this

/-!
Per-`x` signature plumbing (hard-branch fiber).

To bound a per-`x` subfiber, we need a deterministic way to associate to each completion `S`
in the hard-branch fiber (for a fixed realized key `k`) a missing element `y(S) ∈ S⋆ \\ S`
and the corresponding normalized blocking witness for `S ∪ {y(S)}`.

This is the shared “witness selection” that both `perXSignature` bucketing and the residue
lemmas will use.
-/

/-- Choose `y(S) ∈ S⋆ \\ S` and the normalized blocking witness for `S ∪ {y(S)}` in the hard branch. -/
noncomputable def chooseYAndWitness_of_hardFiber
    (hreg : O1aUpgradeRegime family ground A0 h0)
    {k : WLcertKey α} {Sstar Ssub : Finset α}
    (hSstarDom : Sstar ∈ o1aWitnessLiftDomWL family h0)
    (hSsubDom : Ssub ∈ o1aWitnessLiftDomWL family h0)
    (hcert_star : ∃ cert : WLcert family Sstar, WLcert.key cert = k ∧ cert.h ∉ Sstar)
    (hcert_sub : ∃ cert : WLcert family Ssub, WLcert.key cert = k ∧ cert.h ∉ Ssub)
    (hne : Ssub ≠ Sstar) :
    Σ y : α, BlockedUnionWitness family Ssub y := by
  classical
  let y : α :=
    chooseMissingFromRef (family := family) (h0 := h0) Sstar Ssub hSstarDom hSsubDom hne
  have hyX : y ∈ (ground \ (k.2.2.1 ∪ k.2.2.2.1)) := by
    simpa [y] using
      (chooseMissingFromRef_mem_X_of_hardFiber (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg (k := k) (Sstar := Sstar) (Ssub := Ssub) hSstarDom hSsubDom hcert_star hcert_sub hne)
  have hyNot : y ∉ Ssub := by
    have hyDiff :
        y ∈ Sstar \ Ssub := by
      simpa [y] using
        (chooseMissingFromRef_spec (family := family) (h0 := h0) Sstar Ssub hSstarDom hSsubDom hne)
    exact (Finset.mem_sdiff.mp hyDiff).2
  have hy0 : y ≠ h0 := by
    simpa [y] using
      (chooseMissingFromRef_ne_h0_of_hardFiber (family := family) (h0 := h0) (Sstar := Sstar) (Ssub := Ssub)
        hSstarDom hSsubDom hne)
  refine ⟨y, ?_⟩
  exact
    chooseBlockedUnionWitnessNorm_of_hNotMem_reduction
      (family := family) (ground := ground) (A0 := A0) (h0 := h0)
      hreg (k := k) (S := Ssub) hSsubDom hcert_sub hyX hyNot hy0

/-!
Per-`x` subfiber signature pieces.

We avoid forcing the full witness core to lie in `kA ∪ kB` (this is false for arbitrary chosen
blocking witnesses). Instead we use the **projected anchor**

`rAB := (core.erase y) ∩ (kA ∪ kB)`,

which automatically lies in `kA ∪ kB` and, via the hard-branch trace, lands in the fixed
`keyBase = kcore.erase kh`.
-/

/-- Projected anchor from a blocking witness: the part of `core.erase y` that lies in `kA ∪ kB`. -/
def rAB (k : WLcertKey α) (S : Finset α) (y : α) (w : BlockedUnionWitness family S y) : Finset α :=
  let kA : Finset α := k.2.2.1
  let kB : Finset α := k.2.2.2.1
  (w.core.erase y) ∩ (kA ∪ kB)

/-!
Compression of `Finset`-valued anchors to a constant-size trace.

We use the same `Option (t₁, t₂?, hasMore)` shape as the `tx2Plus` trace: record up to two elements,
plus a 1-bit tag `hasMore` indicating whether there exists a third element.
-/

noncomputable def trace2PlusOfFinset (T : Finset α) : Option (α × Option α × Bool) := by
  classical
  by_cases hT : T.Nonempty
  · let t1 : α := Classical.choose hT
    let T2 : Finset α := T.erase t1
    by_cases hT2 : T2.Nonempty
    · let t2 : α := Classical.choose hT2
      let T3 : Finset α := T2.erase t2
      by_cases hT3 : T3.Nonempty
      · exact some (t1, some t2, true)
      · exact some (t1, some t2, false)
    · exact some (t1, none, false)
  · exact none

theorem tx2PlusOfWitness_eq_trace2PlusOfFinset_extras
    {S : Finset α} {x : α} (w : BlockedUnionWitness family S x) :
    tx2PlusOfWitness (family := family) (S := S) (x := x) w =
      trace2PlusOfFinset (α := α) (w.A \ insert x S) := by
  classical
  simp [tx2PlusOfWitness, trace2PlusOfFinset]

/-!
Canonical triple key for a `Finset` with at least 3 elements.

This is used for the non-rigid (“hasMore = true”) triple-bucketing finish: we avoid the weak
predicate `{t₁,t₂,t₃} ⊆ U` and instead bucket by the *canonical* `(t₁,t₂,t₃)` obtained via
`choose/erase/choose/erase/choose`.
-/

noncomputable def tripleKeyOfFinset (T : Finset α) : Option (α × α × α) := by
  classical
  by_cases hT : T.Nonempty
  · let t1 : α := Classical.choose hT
    let T2 : Finset α := T.erase t1
    by_cases hT2 : T2.Nonempty
    · let t2 : α := Classical.choose hT2
      let T3 : Finset α := T2.erase t2
      by_cases hT3 : T3.Nonempty
      · let t3 : α := Classical.choose hT3
        exact some (t1, t2, t3)
      · exact none
    · exact none
  · exact none

noncomputable def hasFourthOfFinset (T : Finset α) (t1 t2 t3 : α) : Bool := by
  classical
  exact decide ((((T.erase t1).erase t2).erase t3).Nonempty)

noncomputable def quadKeyOfFinset (T : Finset α) : Option (α × α × α × α) :=
  match tripleKeyOfFinset (α := α) T with
  | none => none
  | some (t1, t2, t3) =>
      let R : Finset α := (((T.erase t1).erase t2).erase t3)
      if hR : R.Nonempty then
        some (t1, t2, t3, Classical.choose hR)
      else none

noncomputable def hasFifthOfFinset (T : Finset α) (t1 t2 t3 t4 : α) : Bool := by
  classical
  exact decide ((((T.erase t1).erase t2).erase t3).erase t4).Nonempty

noncomputable def trace3PlusOfFinset (T : Finset α) : Option (α × α × α × Bool) :=
  match tripleKeyOfFinset (α := α) T with
  | none => none
  | some (t1, t2, t3) => some (t1, t2, t3, hasFourthOfFinset (α := α) T t1 t2 t3)

noncomputable def trace4PlusOfFinset (T : Finset α) : Option (α × α × α × α × Bool) :=
  match quadKeyOfFinset (α := α) T with
  | none => none
  | some (t1, t2, t3, t4) => some (t1, t2, t3, t4, hasFifthOfFinset (α := α) T t1 t2 t3 t4)

noncomputable def quintKeyOfFinset (T : Finset α) : Option (α × α × α × α × α) :=
  match quadKeyOfFinset (α := α) T with
  | none => none
  | some (t1, t2, t3, t4) =>
      let R : Finset α := ((((T.erase t1).erase t2).erase t3).erase t4)
      if hR : R.Nonempty then
        some (t1, t2, t3, t4, Classical.choose hR)
      else none

noncomputable def hasSixthOfFinset (T : Finset α) (t1 t2 t3 t4 t5 : α) : Bool := by
  classical
  exact decide ((((((T.erase t1).erase t2).erase t3).erase t4).erase t5).Nonempty)

noncomputable def trace5PlusOfFinset (T : Finset α) : Option (α × α × α × α × α × Bool) :=
  match quintKeyOfFinset (α := α) T with
  | none => none
  | some (t1, t2, t3, t4, t5) =>
      some (t1, t2, t3, t4, t5, hasSixthOfFinset (α := α) T t1 t2 t3 t4 t5)

theorem subset_triple_of_hasFourth_false
    {T : Finset α} {t1 t2 t3 : α}
    (h4 : hasFourthOfFinset (α := α) T t1 t2 t3 = false) :
    T ⊆ ({t1, t2, t3} : Finset α) := by
  classical
  -- Reduce to showing there is no element outside `{t1,t2,t3}`.
  intro z hz
  by_cases hz1 : z = t1
  · subst hz1; simp
  by_cases hz2 : z = t2
  · subst hz2; simp [hz1]
  by_cases hz3 : z = t3
  · subst hz3; simp [hz1, hz2]
  -- If `z` is distinct from `t1,t2,t3`, then `z` survives all three erases.
  have hzErase1 : z ∈ T.erase t1 := Finset.mem_erase.mpr ⟨hz1, hz⟩
  have hzErase2 : z ∈ (T.erase t1).erase t2 := Finset.mem_erase.mpr ⟨hz2, hzErase1⟩
  have hzErase3 : z ∈ ((T.erase t1).erase t2).erase t3 :=
    Finset.mem_erase.mpr ⟨hz3, hzErase2⟩
  -- Contradict `hasFourth = false`.
  have hEmpty : (((T.erase t1).erase t2).erase t3) = ∅ := by
    -- `decide Nonempty = false` means the set is empty.
    have : ¬ (((T.erase t1).erase t2).erase t3).Nonempty := by
      simpa [hasFourthOfFinset] using h4
    simpa [Finset.not_nonempty_iff_eq_empty] using this
  have : False := by
    have : z ∈ (∅ : Finset α) := by simpa [hEmpty] using hzErase3
    simpa using this
  exact False.elim this

theorem mem_components_of_tripleKeyOfFinset_eq_some
    {T : Finset α} {t1 t2 t3 : α}
    (ht : tripleKeyOfFinset (α := α) T = some (t1, t2, t3)) :
    t1 ∈ T ∧ t2 ∈ T ∧ t3 ∈ T := by
  classical
  -- Unfold `tripleKeyOfFinset` and chase the `choose` witnesses.
  by_cases hT : T.Nonempty
  · let t1' : α := Classical.choose hT
    let T2 : Finset α := T.erase t1'
    by_cases hT2 : T2.Nonempty
    · let t2' : α := Classical.choose hT2
      let T3 : Finset α := T2.erase t2'
      by_cases hT3 : T3.Nonempty
      · let t3' : α := Classical.choose hT3
        have ht_def :
            tripleKeyOfFinset (α := α) T = some (t1', t2', t3') := by
          simp [tripleKeyOfFinset, hT, t1', T2, hT2, t2', T3, hT3, t3']
        have hsome : some (t1', t2', t3') = some (t1, t2, t3) := by
          simpa [ht_def] using ht
        have htriple : (t1', t2', t3') = (t1, t2, t3) :=
          Option.some.inj hsome
        have ht1 : t1' = t1 := by simpa using congrArg Prod.fst htriple
        have ht23 : (t2', t3') = (t2, t3) := by
          simpa using congrArg Prod.snd htriple
        have ht2 : t2' = t2 := by simpa using congrArg Prod.fst ht23
        have ht3 : t3' = t3 := by simpa using congrArg Prod.snd ht23
        have ht1mem : t1 ∈ T := by
          subst ht1
          exact Classical.choose_spec hT
        have ht2mem : t2 ∈ T := by
          subst ht2
          have : t2' ∈ T2 := Classical.choose_spec hT2
          exact (Finset.mem_erase.mp this).2
        have ht3mem : t3 ∈ T := by
          subst ht3
          have : t3' ∈ T3 := Classical.choose_spec hT3
          have : t3' ∈ T2 := (Finset.mem_erase.mp this).2
          exact (Finset.mem_erase.mp this).2
        exact ⟨ht1mem, ht2mem, ht3mem⟩
      · have ht_def : tripleKeyOfFinset (α := α) T = none := by
          simp [tripleKeyOfFinset, hT, t1', T2, hT2, t2', T3, hT3]
        have : (none : Option (α × α × α)) = some (t1, t2, t3) := by
          simpa [ht_def] using ht
        cases this
    · have ht_def : tripleKeyOfFinset (α := α) T = none := by
        simp [tripleKeyOfFinset, hT, t1', T2, hT2]
      have : (none : Option (α × α × α)) = some (t1, t2, t3) := by
        simpa [ht_def] using ht
      cases this
  · have ht_def : tripleKeyOfFinset (α := α) T = none := by
      simp [tripleKeyOfFinset, hT]
    have : (none : Option (α × α × α)) = some (t1, t2, t3) := by
      simpa [ht_def] using ht
    cases this

theorem eq_triple_of_trace3PlusOfFinset_eq_some_false
    {T : Finset α} {t1 t2 t3 : α}
    (ht : trace3PlusOfFinset (α := α) T = some (t1, t2, t3, false)) :
    T = ({t1, t2, t3} : Finset α) := by
  classical
  -- Unfold `trace3PlusOfFinset` to recover the underlying `tripleKey` and `hasFourth`.
  cases htk : tripleKeyOfFinset (α := α) T with
  | none =>
      have : (none : Option (α × α × α × Bool)) = some (t1, t2, t3, false) := by
        simpa [trace3PlusOfFinset, htk] using ht
      cases this
  | some t =>
      have ht' :
          some (t.1, t.2.1, t.2.2,
              hasFourthOfFinset (α := α) T t.1 t.2.1 t.2.2) =
            some (t1, t2, t3, false) := by
        simpa [trace3PlusOfFinset, htk] using ht
      have hquad :
          (t.1, t.2.1, t.2.2,
              hasFourthOfFinset (α := α) T t.1 t.2.1 t.2.2) =
            (t1, t2, t3, false) :=
        Option.some.inj ht'
      have ht1 : t.1 = t1 := by
        simpa using congrArg (fun q : α × α × α × Bool => q.1) hquad
      have ht2 : t.2.1 = t2 := by
        simpa using congrArg (fun q : α × α × α × Bool => q.2.1) hquad
      have ht3 : t.2.2 = t3 := by
        simpa using congrArg (fun q : α × α × α × Bool => q.2.2.1) hquad
      have h4 :
          hasFourthOfFinset (α := α) T t1 t2 t3 = false := by
        have h4' :
            hasFourthOfFinset (α := α) T t.1 t.2.1 t.2.2 = false := by
          simpa using congrArg (fun q : α × α × α × Bool => q.2.2.2) hquad
        simpa [ht1, ht2, ht3] using h4'
      have hsub : T ⊆ ({t1, t2, t3} : Finset α) :=
        subset_triple_of_hasFourth_false (α := α) (T := T) (t1 := t1) (t2 := t2) (t3 := t3) h4
      have hmem : t1 ∈ T ∧ t2 ∈ T ∧ t3 ∈ T := by
        have htk' : tripleKeyOfFinset (α := α) T = some (t.1, t.2.1, t.2.2) := by
          simpa [htk]
        have hmem' :=
          mem_components_of_tripleKeyOfFinset_eq_some (α := α) (T := T)
            (t1 := t.1) (t2 := t.2.1) (t3 := t.2.2) htk'
        simpa [ht1, ht2, ht3] using hmem'
      have hsup : ({t1, t2, t3} : Finset α) ⊆ T := by
        intro z hz
        rcases Finset.mem_insert.mp hz with hzEq | hz
        · subst hzEq; exact hmem.1
        rcases Finset.mem_insert.mp hz with hzEq | hz
        · subst hzEq; exact hmem.2.1
        have hzEq : z = t3 := by simpa using (Finset.mem_singleton.mp hz)
        subst hzEq
        exact hmem.2.2
      exact Finset.Subset.antisymm hsub hsup

theorem subset_quad_of_hasFifth_false
    {T : Finset α} {t1 t2 t3 t4 : α}
    (h5 : hasFifthOfFinset (α := α) T t1 t2 t3 t4 = false) :
    T ⊆ ({t1, t2, t3, t4} : Finset α) := by
  classical
  intro z hz
  by_cases hz1 : z = t1
  · subst hz1; simp
  by_cases hz2 : z = t2
  · subst hz2; simp [hz1]
  by_cases hz3 : z = t3
  · subst hz3; simp [hz1, hz2]
  by_cases hz4 : z = t4
  · subst hz4; simp [hz1, hz2, hz3]
  have hzErase1 : z ∈ T.erase t1 := Finset.mem_erase.mpr ⟨hz1, hz⟩
  have hzErase2 : z ∈ (T.erase t1).erase t2 := Finset.mem_erase.mpr ⟨hz2, hzErase1⟩
  have hzErase3 : z ∈ ((T.erase t1).erase t2).erase t3 :=
    Finset.mem_erase.mpr ⟨hz3, hzErase2⟩
  have hzErase4 : z ∈ (((T.erase t1).erase t2).erase t3).erase t4 :=
    Finset.mem_erase.mpr ⟨hz4, hzErase3⟩
  have hEmpty : ((((T.erase t1).erase t2).erase t3).erase t4) = ∅ := by
    have : ¬ ((((T.erase t1).erase t2).erase t3).erase t4).Nonempty := by
      simpa [hasFifthOfFinset] using h5
    simpa [Finset.not_nonempty_iff_eq_empty] using this
  have : False := by
    have : z ∈ (∅ : Finset α) := by simpa [hEmpty] using hzErase4
    simpa using this
  exact False.elim this

theorem mem_components_of_quadKeyOfFinset_eq_some
    {T : Finset α} {t1 t2 t3 t4 : α}
    (ht : quadKeyOfFinset (α := α) T = some (t1, t2, t3, t4)) :
    t1 ∈ T ∧ t2 ∈ T ∧ t3 ∈ T ∧ t4 ∈ T := by
  classical
  cases h3 : tripleKeyOfFinset (α := α) T with
  | none =>
      have : (none : Option (α × α × α × α)) = some (t1, t2, t3, t4) := by
        simpa [quadKeyOfFinset, h3] using ht
      cases this
  | some t =>
      let t1' : α := t.1
      let t2' : α := t.2.1
      let t3' : α := t.2.2
      let R : Finset α := (((T.erase t1').erase t2').erase t3')
      by_cases hR : R.Nonempty
      · let t4' : α := Classical.choose hR
        have ht_def : quadKeyOfFinset (α := α) T = some (t1', t2', t3', t4') := by
          simp [quadKeyOfFinset, h3, t1', t2', t3', R, hR, t4']
        have hsome : some (t1', t2', t3', t4') = some (t1, t2, t3, t4) := by
          simpa [ht_def] using ht
        have hquad : (t1', t2', t3', t4') = (t1, t2, t3, t4) := Option.some.inj hsome
        have ht1 : t1' = t1 := by simpa using congrArg (fun q : α × α × α × α => q.1) hquad
        have ht2 : t2' = t2 := by simpa using congrArg (fun q : α × α × α × α => q.2.1) hquad
        have ht3 : t3' = t3 := by simpa using congrArg (fun q : α × α × α × α => q.2.2.1) hquad
        have ht4 : t4' = t4 := by simpa using congrArg (fun q : α × α × α × α => q.2.2.2) hquad
        have hmem123 :
            t1' ∈ T ∧ t2' ∈ T ∧ t3' ∈ T := by
          have htriple : tripleKeyOfFinset (α := α) T = some (t1', t2', t3') := by
            simpa [t1', t2', t3'] using h3
          exact
            mem_components_of_tripleKeyOfFinset_eq_some (α := α) (T := T)
              (t1 := t1') (t2 := t2') (t3 := t3') htriple
        have ht4mem' : t4' ∈ T := by
          have ht4memR : t4' ∈ R := Classical.choose_spec hR
          have ht4memT2 : t4' ∈ (T.erase t1').erase t2' :=
            (Finset.mem_erase.mp ht4memR).2
          have ht4memT1 : t4' ∈ T.erase t1' :=
            (Finset.mem_erase.mp ht4memT2).2
          exact (Finset.mem_erase.mp ht4memT1).2
        refine ⟨?_, ?_, ?_, ?_⟩
        · simpa [ht1] using hmem123.1
        · simpa [ht2] using hmem123.2.1
        · simpa [ht3] using hmem123.2.2
        · simpa [ht4] using ht4mem'
      · have : (none : Option (α × α × α × α)) = some (t1, t2, t3, t4) := by
          simpa [quadKeyOfFinset, h3, t1', t2', t3', R, hR] using ht
        cases this

theorem eq_quad_of_trace4PlusOfFinset_eq_some_false
    {T : Finset α} {t1 t2 t3 t4 : α}
    (ht : trace4PlusOfFinset (α := α) T = some (t1, t2, t3, t4, false)) :
    T = ({t1, t2, t3, t4} : Finset α) := by
  classical
  cases hq : quadKeyOfFinset (α := α) T with
  | none =>
      have : (none : Option (α × α × α × α × Bool)) = some (t1, t2, t3, t4, false) := by
        simpa [trace4PlusOfFinset, hq] using ht
      cases this
  | some q =>
      have ht' :
          some (q.1, q.2.1, q.2.2.1, q.2.2.2,
              hasFifthOfFinset (α := α) T q.1 q.2.1 q.2.2.1 q.2.2.2) =
            some (t1, t2, t3, t4, false) := by
        simpa [trace4PlusOfFinset, hq] using ht
      have h5tuple :
          (q.1, q.2.1, q.2.2.1, q.2.2.2,
              hasFifthOfFinset (α := α) T q.1 q.2.1 q.2.2.1 q.2.2.2) =
            (t1, t2, t3, t4, false) :=
        Option.some.inj ht'
      have ht1 : q.1 = t1 := by
        simpa using congrArg (fun p : α × α × α × α × Bool => p.1) h5tuple
      have ht2 : q.2.1 = t2 := by
        simpa using congrArg (fun p : α × α × α × α × Bool => p.2.1) h5tuple
      have ht3 : q.2.2.1 = t3 := by
        simpa using congrArg (fun p : α × α × α × α × Bool => p.2.2.1) h5tuple
      have ht4 : q.2.2.2 = t4 := by
        simpa using congrArg (fun p : α × α × α × α × Bool => p.2.2.2.1) h5tuple
      have h5 :
          hasFifthOfFinset (α := α) T t1 t2 t3 t4 = false := by
        have h5' :
            hasFifthOfFinset (α := α) T q.1 q.2.1 q.2.2.1 q.2.2.2 = false := by
          simpa using congrArg (fun p : α × α × α × α × Bool => p.2.2.2.2) h5tuple
        simpa [ht1, ht2, ht3, ht4] using h5'
      have hsub : T ⊆ ({t1, t2, t3, t4} : Finset α) :=
        subset_quad_of_hasFifth_false (α := α) (T := T) (t1 := t1) (t2 := t2) (t3 := t3)
          (t4 := t4) h5
      have hmem : t1 ∈ T ∧ t2 ∈ T ∧ t3 ∈ T ∧ t4 ∈ T := by
        have hq' : quadKeyOfFinset (α := α) T = some (q.1, q.2.1, q.2.2.1, q.2.2.2) := by
          simpa [hq]
        have hmem' :=
          mem_components_of_quadKeyOfFinset_eq_some (α := α) (T := T)
            (t1 := q.1) (t2 := q.2.1) (t3 := q.2.2.1) (t4 := q.2.2.2) hq'
        simpa [ht1, ht2, ht3, ht4] using hmem'
      have hsup : ({t1, t2, t3, t4} : Finset α) ⊆ T := by
        intro z hz
        rcases Finset.mem_insert.mp hz with hzEq | hz
        · subst hzEq; exact hmem.1
        rcases Finset.mem_insert.mp hz with hzEq | hz
        · subst hzEq; exact hmem.2.1
        rcases Finset.mem_insert.mp hz with hzEq | hz
        · subst hzEq; exact hmem.2.2.1
        have hzEq : z = t4 := by simpa using (Finset.mem_singleton.mp hz)
        subst hzEq
        exact hmem.2.2.2
      exact Finset.Subset.antisymm hsub hsup

theorem subset_quint_of_hasSixth_false
    {T : Finset α} {t1 t2 t3 t4 t5 : α}
    (h6 : hasSixthOfFinset (α := α) T t1 t2 t3 t4 t5 = false) :
    T ⊆ ({t1, t2, t3, t4, t5} : Finset α) := by
  classical
  intro z hz
  by_cases hz1 : z = t1
  · subst hz1; simp
  by_cases hz2 : z = t2
  · subst hz2; simp [hz1]
  by_cases hz3 : z = t3
  · subst hz3; simp [hz1, hz2]
  by_cases hz4 : z = t4
  · subst hz4; simp [hz1, hz2, hz3]
  by_cases hz5 : z = t5
  · subst hz5; simp [hz1, hz2, hz3, hz4]
  have hzErase1 : z ∈ T.erase t1 := Finset.mem_erase.mpr ⟨hz1, hz⟩
  have hzErase2 : z ∈ (T.erase t1).erase t2 := Finset.mem_erase.mpr ⟨hz2, hzErase1⟩
  have hzErase3 : z ∈ ((T.erase t1).erase t2).erase t3 :=
    Finset.mem_erase.mpr ⟨hz3, hzErase2⟩
  have hzErase4 : z ∈ (((T.erase t1).erase t2).erase t3).erase t4 :=
    Finset.mem_erase.mpr ⟨hz4, hzErase3⟩
  have hzErase5 : z ∈ ((((T.erase t1).erase t2).erase t3).erase t4).erase t5 :=
    Finset.mem_erase.mpr ⟨hz5, hzErase4⟩
  have hEmpty : (((((T.erase t1).erase t2).erase t3).erase t4).erase t5) = ∅ := by
    have : ¬ (((((T.erase t1).erase t2).erase t3).erase t4).erase t5).Nonempty := by
      simpa [hasSixthOfFinset] using h6
    simpa [Finset.not_nonempty_iff_eq_empty] using this
  have : False := by
    have : z ∈ (∅ : Finset α) := by simpa [hEmpty] using hzErase5
    simpa using this
  exact False.elim this

theorem mem_components_of_quintKeyOfFinset_eq_some
    {T : Finset α} {t1 t2 t3 t4 t5 : α}
    (ht : quintKeyOfFinset (α := α) T = some (t1, t2, t3, t4, t5)) :
    t1 ∈ T ∧ t2 ∈ T ∧ t3 ∈ T ∧ t4 ∈ T ∧ t5 ∈ T := by
  classical
  cases hq : quadKeyOfFinset (α := α) T with
  | none =>
      have : (none : Option (α × α × α × α × α)) = some (t1, t2, t3, t4, t5) := by
        simpa [quintKeyOfFinset, hq] using ht
      cases this
  | some q =>
      have hq' :
          quadKeyOfFinset (α := α) T = some (q.1, q.2.1, q.2.2.1, q.2.2.2) := by
        simpa [hq]
      let q1 : α := q.1
      let q2 : α := q.2.1
      let q3 : α := q.2.2.1
      let q4 : α := q.2.2.2
      let R : Finset α := ((((T.erase q1).erase q2).erase q3).erase q4)
      by_cases hR : R.Nonempty
      · let t5' : α := Classical.choose hR
        have ht_def :
            quintKeyOfFinset (α := α) T = some (q1, q2, q3, q4, t5') := by
          simp [quintKeyOfFinset, hq, q1, q2, q3, q4, R, hR, t5']
        have hsome : some (q1, q2, q3, q4, t5') = some (t1, t2, t3, t4, t5) := by
          simpa [ht_def] using ht
        have hquint : (q1, q2, q3, q4, t5') = (t1, t2, t3, t4, t5) := Option.some.inj hsome
        have ht1 : q1 = t1 := by simpa using congrArg (fun p : α × α × α × α × α => p.1) hquint
        have ht2 : q2 = t2 := by simpa using congrArg (fun p : α × α × α × α × α => p.2.1) hquint
        have ht3 : q3 = t3 := by simpa using congrArg (fun p : α × α × α × α × α => p.2.2.1) hquint
        have ht4 : q4 = t4 := by simpa using congrArg (fun p : α × α × α × α × α => p.2.2.2.1) hquint
        have ht5 : t5' = t5 := by simpa using congrArg (fun p : α × α × α × α × α => p.2.2.2.2) hquint
        have hmem1234 :
            q1 ∈ T ∧ q2 ∈ T ∧ q3 ∈ T ∧ q4 ∈ T :=
          mem_components_of_quadKeyOfFinset_eq_some (α := α) (T := T)
            (t1 := q1) (t2 := q2) (t3 := q3) (t4 := q4) hq'
        have ht5mem' : t5' ∈ T := by
          have ht5memR : t5' ∈ R := Classical.choose_spec hR
          have ht5memT3 : t5' ∈ ((T.erase q1).erase q2).erase q3 :=
            (Finset.mem_erase.mp ht5memR).2
          have ht5memT2 : t5' ∈ (T.erase q1).erase q2 :=
            (Finset.mem_erase.mp ht5memT3).2
          have ht5memT1 : t5' ∈ T.erase q1 :=
            (Finset.mem_erase.mp ht5memT2).2
          exact (Finset.mem_erase.mp ht5memT1).2
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · simpa [ht1] using hmem1234.1
        · simpa [ht2] using hmem1234.2.1
        · simpa [ht3] using hmem1234.2.2.1
        · simpa [ht4] using hmem1234.2.2.2
        · simpa [ht5] using ht5mem'
      · have : (none : Option (α × α × α × α × α)) = some (t1, t2, t3, t4, t5) := by
          simpa [quintKeyOfFinset, hq, q1, q2, q3, q4, R, hR] using ht
        cases this

theorem eq_quint_of_trace5PlusOfFinset_eq_some_false
    {T : Finset α} {t1 t2 t3 t4 t5 : α}
    (ht : trace5PlusOfFinset (α := α) T = some (t1, t2, t3, t4, t5, false)) :
    T = ({t1, t2, t3, t4, t5} : Finset α) := by
  classical
  cases hk : quintKeyOfFinset (α := α) T with
  | none =>
      have : (none : Option (α × α × α × α × α × Bool)) =
            some (t1, t2, t3, t4, t5, false) := by
        simpa [trace5PlusOfFinset, hk] using ht
      cases this
  | some q =>
      have ht' :
          some (q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2,
              hasSixthOfFinset (α := α) T q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) =
            some (t1, t2, t3, t4, t5, false) := by
        simpa [trace5PlusOfFinset, hk] using ht
      have h6tuple :
          (q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2,
              hasSixthOfFinset (α := α) T q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) =
            (t1, t2, t3, t4, t5, false) :=
        Option.some.inj ht'
      have ht1 : q.1 = t1 := by
        simpa using congrArg (fun p : α × α × α × α × α × Bool => p.1) h6tuple
      have ht2 : q.2.1 = t2 := by
        simpa using congrArg (fun p : α × α × α × α × α × Bool => p.2.1) h6tuple
      have ht3 : q.2.2.1 = t3 := by
        simpa using congrArg (fun p : α × α × α × α × α × Bool => p.2.2.1) h6tuple
      have ht4 : q.2.2.2.1 = t4 := by
        simpa using congrArg (fun p : α × α × α × α × α × Bool => p.2.2.2.1) h6tuple
      have ht5 : q.2.2.2.2 = t5 := by
        simpa using congrArg (fun p : α × α × α × α × α × Bool => p.2.2.2.2.1) h6tuple
      have h6 :
          hasSixthOfFinset (α := α) T t1 t2 t3 t4 t5 = false := by
        have h6' :
            hasSixthOfFinset (α := α) T q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 = false := by
          simpa using congrArg (fun p : α × α × α × α × α × Bool => p.2.2.2.2.2) h6tuple
        simpa [ht1, ht2, ht3, ht4, ht5] using h6'
      have hsub : T ⊆ ({t1, t2, t3, t4, t5} : Finset α) :=
        subset_quint_of_hasSixth_false (α := α) (T := T) (t1 := t1) (t2 := t2) (t3 := t3)
          (t4 := t4) (t5 := t5) h6
      have hmem : t1 ∈ T ∧ t2 ∈ T ∧ t3 ∈ T ∧ t4 ∈ T ∧ t5 ∈ T := by
        have hk' :
            quintKeyOfFinset (α := α) T =
              some (q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2) := by
          simpa [hk]
        have hmem' :=
          mem_components_of_quintKeyOfFinset_eq_some (α := α) (T := T)
            (t1 := q.1) (t2 := q.2.1) (t3 := q.2.2.1) (t4 := q.2.2.2.1) (t5 := q.2.2.2.2) hk'
        simpa [ht1, ht2, ht3, ht4, ht5] using hmem'
      have hsup : ({t1, t2, t3, t4, t5} : Finset α) ⊆ T := by
        intro z hz
        rcases Finset.mem_insert.mp hz with hzEq | hz
        · subst hzEq; exact hmem.1
        rcases Finset.mem_insert.mp hz with hzEq | hz
        · subst hzEq; exact hmem.2.1
        rcases Finset.mem_insert.mp hz with hzEq | hz
        · subst hzEq; exact hmem.2.2.1
        rcases Finset.mem_insert.mp hz with hzEq | hz
        · subst hzEq; exact hmem.2.2.2.1
        have hzEq : z = t5 := by simpa using (Finset.mem_singleton.mp hz)
        subst hzEq
        exact hmem.2.2.2.2
      exact Finset.Subset.antisymm hsub hsup

theorem exists_sixth_of_trace5PlusOfFinset_eq_some_true
    {T : Finset α} {t1 t2 t3 t4 t5 : α}
    (ht : trace5PlusOfFinset (α := α) T = some (t1, t2, t3, t4, t5, true)) :
    ∃ t6, t6 ∈ T ∧ t6 ∉ ({t1, t2, t3, t4, t5} : Finset α) := by
  classical
  cases hk : quintKeyOfFinset (α := α) T with
  | none =>
      have : (none : Option (α × α × α × α × α × Bool)) =
            some (t1, t2, t3, t4, t5, true) := by
        simpa [trace5PlusOfFinset, hk] using ht
      cases this
  | some q =>
      have ht' :
          some (q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2,
              hasSixthOfFinset (α := α) T q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) =
            some (t1, t2, t3, t4, t5, true) := by
        simpa [trace5PlusOfFinset, hk] using ht
      have h6tuple :
          (q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2,
              hasSixthOfFinset (α := α) T q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) =
            (t1, t2, t3, t4, t5, true) :=
        Option.some.inj ht'
      have ht1 : q.1 = t1 := by
        simpa using congrArg (fun p : α × α × α × α × α × Bool => p.1) h6tuple
      have ht2 : q.2.1 = t2 := by
        simpa using congrArg (fun p : α × α × α × α × α × Bool => p.2.1) h6tuple
      have ht3 : q.2.2.1 = t3 := by
        simpa using congrArg (fun p : α × α × α × α × α × Bool => p.2.2.1) h6tuple
      have ht4 : q.2.2.2.1 = t4 := by
        simpa using congrArg (fun p : α × α × α × α × α × Bool => p.2.2.2.1) h6tuple
      have ht5 : q.2.2.2.2 = t5 := by
        simpa using congrArg (fun p : α × α × α × α × α × Bool => p.2.2.2.2.1) h6tuple
      have h6 :
          hasSixthOfFinset (α := α) T t1 t2 t3 t4 t5 = true := by
        have h6' :
            hasSixthOfFinset (α := α) T q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 = true := by
          simpa using congrArg (fun p : α × α × α × α × α × Bool => p.2.2.2.2.2) h6tuple
        simpa [ht1, ht2, ht3, ht4, ht5] using h6'
      let R : Finset α := (((((T.erase t1).erase t2).erase t3).erase t4).erase t5)
      have hR : R.Nonempty := by
        -- `hasSixth = true` means the remainder after erasing the chosen quintuple is nonempty.
        have : decide R.Nonempty = true := by
          simpa [hasSixthOfFinset, R] using h6
        exact of_decide_eq_true this
      let t6 : α := Classical.choose hR
      have ht6R : t6 ∈ R := Classical.choose_spec hR
      have ht6e5 : t6 ∈ ((((T.erase t1).erase t2).erase t3).erase t4).erase t5 := by
        simpa [R] using ht6R
      have ht6e4 : t6 ∈ (((T.erase t1).erase t2).erase t3).erase t4 := (Finset.mem_erase.mp ht6e5).2
      have ht6e3 : t6 ∈ ((T.erase t1).erase t2).erase t3 := (Finset.mem_erase.mp ht6e4).2
      have ht6e2 : t6 ∈ (T.erase t1).erase t2 := (Finset.mem_erase.mp ht6e3).2
      have ht6e1 : t6 ∈ T.erase t1 := (Finset.mem_erase.mp ht6e2).2
      have ht6T : t6 ∈ T := (Finset.mem_erase.mp ht6e1).2
      have ht6ne5 : t6 ≠ t5 := (Finset.mem_erase.mp ht6e5).1
      have ht6ne4 : t6 ≠ t4 := (Finset.mem_erase.mp ht6e4).1
      have ht6ne3 : t6 ≠ t3 := (Finset.mem_erase.mp ht6e3).1
      have ht6ne2 : t6 ≠ t2 := (Finset.mem_erase.mp ht6e2).1
      have ht6ne1 : t6 ≠ t1 := (Finset.mem_erase.mp ht6e1).1
      refine ⟨t6, ht6T, ?_⟩
      -- `t6` is distinct from each of `t1..t5`, so it is not in their 5-element finset.
      intro ht6mem
      have ht6mem' : t6 = t1 ∨ t6 = t2 ∨ t6 = t3 ∨ t6 = t4 ∨ t6 = t5 := by
        simpa using (Finset.mem_insert.mp ht6mem)
      rcases ht6mem' with ht6eq | ht6mem'
      · exact ht6ne1 ht6eq
      rcases ht6mem' with ht6eq | ht6mem'
      · exact ht6ne2 ht6eq
      rcases ht6mem' with ht6eq | ht6mem'
      · exact ht6ne3 ht6eq
      rcases ht6mem' with ht6eq | ht6eq
      · exact ht6ne4 ht6eq
      · exact ht6ne5 ht6eq

theorem trace5PlusOfFinset_ne_none_of_card_ge_five
    {T : Finset α} (hcard : 5 ≤ T.card) :
    trace5PlusOfFinset (α := α) T ≠ none := by
  classical
  intro hτ
  have hTpos : 0 < T.card := lt_of_lt_of_le (by decide : 0 < 5) hcard
  have hT : T.Nonempty := Finset.card_pos.mp hTpos
  let t1 : α := Classical.choose hT
  have ht1 : t1 ∈ T := Classical.choose_spec hT
  let T2 : Finset α := T.erase t1
  have hT2pos : 0 < T2.card := by
    have hlt : 1 < T.card := lt_of_lt_of_le (by decide : 1 < 5) hcard
    have hsub : 0 < T.card - 1 := Nat.sub_pos_of_lt hlt
    simpa [T2, Finset.card_erase_of_mem ht1] using hsub
  have hT2 : T2.Nonempty := Finset.card_pos.mp hT2pos
  let t2 : α := Classical.choose hT2
  have ht2 : t2 ∈ T2 := Classical.choose_spec hT2
  let T3 : Finset α := T2.erase t2
  have hT3pos : 0 < T3.card := by
    have hlt : 2 < T.card := lt_of_lt_of_le (by decide : 2 < 5) hcard
    have hsub : 0 < T.card - 2 := Nat.sub_pos_of_lt hlt
    simpa [T3, T2, Finset.card_erase_of_mem ht2, Finset.card_erase_of_mem ht1, Nat.sub_sub] using hsub
  have hT3 : T3.Nonempty := Finset.card_pos.mp hT3pos
  let t3 : α := Classical.choose hT3
  have ht3 : t3 ∈ T3 := Classical.choose_spec hT3
  let R4 : Finset α := T3.erase t3
  have hR4pos : 0 < R4.card := by
    have hlt : 3 < T.card := lt_of_lt_of_le (by decide : 3 < 5) hcard
    have hsub : 0 < T.card - 3 := Nat.sub_pos_of_lt hlt
    -- `R4.card = T.card - 3`.
    simpa [R4, T3, T2, Finset.card_erase_of_mem ht3, Finset.card_erase_of_mem ht2,
      Finset.card_erase_of_mem ht1, Nat.sub_sub, Nat.sub_sub] using hsub
  have hR4 : R4.Nonempty := Finset.card_pos.mp hR4pos
  let t4 : α := Classical.choose hR4
  have ht4 : t4 ∈ R4 := Classical.choose_spec hR4
  let R5 : Finset α := R4.erase t4
  have hR5pos : 0 < R5.card := by
    have hlt : 4 < T.card := lt_of_lt_of_le (by decide : 4 < 5) hcard
    have hsub : 0 < T.card - 4 := Nat.sub_pos_of_lt hlt
    -- `R5.card = T.card - 4`.
    simpa [R5, R4, T3, T2, Finset.card_erase_of_mem ht4, Finset.card_erase_of_mem ht3,
      Finset.card_erase_of_mem ht2, Finset.card_erase_of_mem ht1, Nat.sub_sub, Nat.sub_sub, Nat.sub_sub] using hsub
  have hR5 : R5.Nonempty := Finset.card_pos.mp hR5pos
  let t5 : α := Classical.choose hR5
  have htrace :
      trace5PlusOfFinset (α := α) T =
        some (t1, t2, t3, t4, t5, hasSixthOfFinset (α := α) T t1 t2 t3 t4 t5) := by
    -- unfold the key chain; all intermediate remainders are nonempty by construction
    have htriple :
        tripleKeyOfFinset (α := α) T = some (t1, t2, t3) := by
      -- `T3.Nonempty` ensures the third element exists
      simp [tripleKeyOfFinset, hT, t1, T2, hT2, t2, T3, hT3, t3]
    have hquad :
        quadKeyOfFinset (α := α) T = some (t1, t2, t3, t4) := by
      simp [quadKeyOfFinset, htriple, T2, T3, R4, hR4, t4]
    have hquint :
        quintKeyOfFinset (α := α) T = some (t1, t2, t3, t4, t5) := by
      simp [quintKeyOfFinset, hquad, T2, T3, R4, R5, hR5, t4, t5]
    simp [trace5PlusOfFinset, hquint]
  have : (some (t1, t2, t3, t4, t5, hasSixthOfFinset (α := α) T t1 t2 t3 t4 t5) :
        Option (α × α × α × α × α × Bool)) = none := by
    simpa [htrace] using hτ
  cases this

/-!
Local “sixth element” selector from `trace5PlusOfFinset`.

If `trace5PlusOfFinset T = some(t₁,…,t₅,true)` (so `|T| ≥ 6`), pick a witness `t₆ ∈ T \ {t₁,…,t₅}`.
Otherwise return `none`.

This is used to fold the one local `t₆` refinement into a bucket key, without introducing a global
`trace6Plus` ladder.
-/
noncomputable def t6OptionOfTrace5Plus (T : Finset α) : Option α := by
  classical
  match quintKeyOfFinset (α := α) T with
  | none => exact none
  | some (t1, t2, t3, t4, t5) =>
      let R : Finset α := (((((T.erase t1).erase t2).erase t3).erase t4).erase t5)
      if hR : R.Nonempty then
        exact some (Classical.choose hR)
      else exact none

theorem mem_of_t6OptionOfTrace5Plus_eq_some {T : Finset α} {t6 : α}
    (ht6 : t6OptionOfTrace5Plus (α := α) T = some t6) : t6 ∈ T := by
  classical
  cases hq : quintKeyOfFinset (α := α) T with
  | none =>
      have : (none : Option α) = some t6 := by
        simpa [t6OptionOfTrace5Plus, hq] using ht6
      cases this
  | some q =>
      rcases q with ⟨t1, t2, t3, t4, t5⟩
      let R : Finset α := (((((T.erase t1).erase t2).erase t3).erase t4).erase t5)
      by_cases hR : R.Nonempty
      · have ht6' : some (Classical.choose hR) = some t6 := by
          simpa [t6OptionOfTrace5Plus, hq, R, hR] using ht6
        have ht6eq : Classical.choose hR = t6 := Option.some.inj ht6'
        have hmemR : Classical.choose hR ∈ R := Classical.choose_spec hR
        have hmemT : Classical.choose hR ∈ T := by
          -- Peel the nested `erase`s.
          have h1 :
              Classical.choose hR ∈ ((((T.erase t1).erase t2).erase t3).erase t4) :=
            (Finset.mem_erase.mp hmemR).2
          have h2 : Classical.choose hR ∈ (((T.erase t1).erase t2).erase t3) :=
            (Finset.mem_erase.mp h1).2
          have h3 : Classical.choose hR ∈ ((T.erase t1).erase t2) :=
            (Finset.mem_erase.mp h2).2
          have h4 : Classical.choose hR ∈ (T.erase t1) :=
            (Finset.mem_erase.mp h3).2
          exact (Finset.mem_erase.mp h4).2
        simpa [ht6eq] using hmemT
      · have : (none : Option α) = some t6 := by
          simpa [t6OptionOfTrace5Plus, hq, R, hR] using ht6
        cases this

theorem t6OptionOfTrace5Plus_mem_optionOfFinset (T : Finset α) :
    t6OptionOfTrace5Plus (α := α) T ∈ optionOfFinset (α := α) T := by
  classical
  cases hopt : t6OptionOfTrace5Plus (α := α) T with
  | none =>
      -- `none` is always in `optionOfFinset T`.
      simpa [optionOfFinset, hopt] using (Finset.mem_insert_self none (T.image some))
  | some t6 =>
      have ht6mem : t6 ∈ T := mem_of_t6OptionOfTrace5Plus_eq_some (α := α) (T := T) (t6 := t6) hopt
      have : some t6 ∈ optionOfFinset (α := α) T := by
        dsimp [optionOfFinset]
        exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨t6, ht6mem, rfl⟩)
      simpa [hopt] using this

/-!
Local t₆ split for the `trace5Plus` residue case.

When `trace5PlusOfFinset U = some(t₁,…,t₅,true)` we may (locally, inside the residue lemma only)
choose a sixth element `t₆ ∈ U \ {t₁,…,t₅}` and union-bound over `t₆`.

This lemma is intentionally generic and does **not** introduce a global `trace6Plus` ladder.
-/

theorem card_le_sum_card_filter_of_exists_sixth
    {β : Type*} [DecidableEq β]
    (F : Finset β) (ground : Finset α) (U : β → Finset α)
    (hUsub : ∀ b ∈ F, U b ⊆ ground)
    {t1 t2 t3 t4 t5 : α}
    (htr :
      ∀ b ∈ F, trace5PlusOfFinset (α := α) (U b) = some (t1, t2, t3, t4, t5, true)) :
    F.card ≤
      ∑ t6 ∈ ground,
        (F.filter (fun b => t6 ∈ U b ∧ t6 ∉ ({t1, t2, t3, t4, t5} : Finset α))).card := by
  classical
  -- Every `b ∈ F` contributes to (at least) one `t6`-subbucket.
  have hcover :
      F ⊆
        ground.biUnion (fun t6 =>
          F.filter (fun b => t6 ∈ U b ∧ t6 ∉ ({t1, t2, t3, t4, t5} : Finset α))) := by
    intro b hbF
    rcases exists_sixth_of_trace5PlusOfFinset_eq_some_true (α := α) (T := U b) (t1 := t1)
        (t2 := t2) (t3 := t3) (t4 := t4) (t5 := t5) (htr b hbF) with
      ⟨t6, ht6U, ht6not⟩
    have ht6ground : t6 ∈ ground := (hUsub b hbF) ht6U
    refine Finset.mem_biUnion.mpr ?_
    refine ⟨t6, ht6ground, ?_⟩
    refine Finset.mem_filter.mpr ?_
    exact ⟨hbF, ⟨ht6U, ht6not⟩⟩
  have hcard : F.card ≤
      (ground.biUnion (fun t6 =>
          F.filter (fun b => t6 ∈ U b ∧ t6 ∉ ({t1, t2, t3, t4, t5} : Finset α)))).card :=
    Finset.card_le_card hcover
  -- Union-bound over `t6`.
  have hcardU :
      (ground.biUnion (fun t6 =>
          F.filter (fun b => t6 ∈ U b ∧ t6 ∉ ({t1, t2, t3, t4, t5} : Finset α)))).card ≤
        ∑ t6 ∈ ground,
          (F.filter (fun b => t6 ∈ U b ∧ t6 ∉ ({t1, t2, t3, t4, t5} : Finset α))).card := by
    simpa using
      (Finset.card_biUnion_le (s := ground)
        (t := fun t6 =>
          F.filter (fun b => t6 ∈ U b ∧ t6 ∉ ({t1, t2, t3, t4, t5} : Finset α))))
  exact le_trans hcard hcardU

theorem trace2PlusOfFinset_ne_some_none_true
    {T : Finset α} {t1 : α} :
    trace2PlusOfFinset (α := α) T ≠ some (t1, none, true) := by
  classical
  intro ht
  by_cases hT : T.Nonempty
  · let t1' : α := Classical.choose hT
    let T2 : Finset α := T.erase t1'
    by_cases hT2 : T2.Nonempty
    · let t2' : α := Classical.choose hT2
      let T3 : Finset α := T2.erase t2'
      by_cases hT3 : T3.Nonempty
      · have ht' :
            trace2PlusOfFinset (α := α) T = some (t1', some t2', true) := by
          simp [trace2PlusOfFinset, hT, t1', T2, hT2, t2', T3, hT3]
        have : (some (t1, none, true) : Option (α × Option α × Bool)) =
            some (t1', some t2', true) := by
          simpa [ht] using ht'.symm
        have hcontr :
            (none : Option α) = some t2' := by
          exact congrArg (fun p : α × Option α × Bool => p.2.1) (Option.some.inj this)
        cases hcontr
      · have ht' :
            trace2PlusOfFinset (α := α) T = some (t1', some t2', false) := by
          simp [trace2PlusOfFinset, hT, t1', T2, hT2, t2', T3, hT3]
        have : (some (t1, none, true) : Option (α × Option α × Bool)) =
            some (t1', some t2', false) := by
          simpa [ht] using ht'.symm
        have hcontr :
            (none : Option α) = some t2' := by
          exact congrArg (fun p : α × Option α × Bool => p.2.1) (Option.some.inj this)
        cases hcontr
    · have ht' :
          trace2PlusOfFinset (α := α) T = some (t1', none, false) := by
        simp [trace2PlusOfFinset, hT, t1', T2, hT2]
      have : (some (t1, none, true) : Option (α × Option α × Bool)) =
          some (t1', none, false) := by
        simpa [ht] using ht'.symm
      have hcontr : (true : Bool) = false := by
        exact congrArg (fun p : α × Option α × Bool => p.2.2) (Option.some.inj this)
      cases hcontr
  · have ht' : trace2PlusOfFinset (α := α) T = none := by
      simp [trace2PlusOfFinset, hT]
    have : (some (t1, none, true) : Option (α × Option α × Bool)) = none := by
      simpa [ht] using ht'.symm
    cases this

theorem trace2PlusOfFinset_eq_some_some_true_of_tripleKeyOfFinset_eq_some
    {T : Finset α} {t1 t2 t3 : α}
    (ht : tripleKeyOfFinset (α := α) T = some (t1, t2, t3)) :
    trace2PlusOfFinset (α := α) T = some (t1, some t2, true) := by
  classical
  by_cases hT : T.Nonempty
  · let t1' : α := Classical.choose hT
    let T2 : Finset α := T.erase t1'
    by_cases hT2 : T2.Nonempty
    · let t2' : α := Classical.choose hT2
      let T3 : Finset α := T2.erase t2'
      by_cases hT3 : T3.Nonempty
      · let t3' : α := Classical.choose hT3
        have ht_def :
            tripleKeyOfFinset (α := α) T = some (t1', t2', t3') := by
          simp [tripleKeyOfFinset, hT, t1', T2, hT2, t2', T3, hT3, t3']
        have hEq :
            some (t1', t2', t3') = some (t1, t2, t3) := by
          -- rewrite the LHS using `ht_def` and close by `ht`.
          simpa [ht_def] using ht
        have hEq' : (t1', t2', t3') = (t1, t2, t3) := Option.some.inj hEq
        have ht1 : t1' = t1 := by
          simpa using congrArg (fun p : α × α × α => p.1) hEq'
        have ht2 : t2' = t2 := by
          simpa using congrArg (fun p : α × α × α => p.2.1) hEq'
        have ht_trace :
            trace2PlusOfFinset (α := α) T = some (t1', some t2', true) := by
          simp [trace2PlusOfFinset, hT, t1', T2, hT2, t2', T3, hT3]
        simpa [ht1, ht2] using ht_trace
      ·
        have ht_none : tripleKeyOfFinset (α := α) T = none := by
          simp [tripleKeyOfFinset, hT, t1', T2, hT2, t2', T3, hT3]
        have : (none : Option (α × α × α)) = some (t1, t2, t3) := by
          simpa [ht] using ht_none
        cases this
    ·
      have ht_none : tripleKeyOfFinset (α := α) T = none := by
        simp [tripleKeyOfFinset, hT, t1', T2, hT2]
      have : (none : Option (α × α × α)) = some (t1, t2, t3) := by
        simpa [ht] using ht_none
      cases this
  ·
    have ht_none : tripleKeyOfFinset (α := α) T = none := by
      simp [tripleKeyOfFinset, hT]
    have : (none : Option (α × α × α)) = some (t1, t2, t3) := by
      simpa [ht] using ht_none
    cases this

theorem tripleKeyOfFinset_eq_some_of_quadKeyOfFinset_eq_some
    {T : Finset α} {t1 t2 t3 t4 : α}
    (ht : quadKeyOfFinset (α := α) T = some (t1, t2, t3, t4)) :
    tripleKeyOfFinset (α := α) T = some (t1, t2, t3) := by
  classical
  cases htr : tripleKeyOfFinset (α := α) T with
  | none =>
      have : (none : Option (α × α × α × α)) = some (t1, t2, t3, t4) := by
        simpa [quadKeyOfFinset, htr] using ht
      cases this
  | some triple =>
      let a1 : α := triple.1
      let a2 : α := triple.2.1
      let a3 : α := triple.2.2
      let R : Finset α := ((T.erase a1).erase a2).erase a3
      by_cases hR : R.Nonempty
      · let t4' : α := Classical.choose hR
        have ht_def : quadKeyOfFinset (α := α) T = some (a1, a2, a3, t4') := by
          simp [quadKeyOfFinset, htr, a1, a2, a3, R, hR, t4']
        have hEq :
            some (a1, a2, a3, t4') = some (t1, t2, t3, t4) := by
          simpa [ht_def] using ht
        have hEq' : (a1, a2, a3, t4') = (t1, t2, t3, t4) := Option.some.inj hEq
        have ha1 : a1 = t1 := by
          simpa using congrArg (fun p : α × α × α × α => p.1) hEq'
        have ha2 : a2 = t2 := by
          simpa using congrArg (fun p : α × α × α × α => p.2.1) hEq'
        have ha3 : a3 = t3 := by
          simpa using congrArg (fun p : α × α × α × α => p.2.2.1) hEq'
        have ht1 : triple.1 = t1 := by
          simpa [a1] using ha1
        have ht2 : triple.2.1 = t2 := by
          simpa [a2] using ha2
        have ht3 : triple.2.2 = t3 := by
          simpa [a3] using ha3
        refine congrArg Option.some ?_
        apply Prod.ext
        · exact ht1
        ·
          apply Prod.ext
          · exact ht2
          · exact ht3
      ·
        have ht_none : quadKeyOfFinset (α := α) T = none := by
          simp [quadKeyOfFinset, htr, a1, a2, a3, R, hR]
        have : (none : Option (α × α × α × α)) = some (t1, t2, t3, t4) := by
          simpa [ht_none] using ht
        cases this

theorem quadKeyOfFinset_eq_some_of_quintKeyOfFinset_eq_some
    {T : Finset α} {t1 t2 t3 t4 t5 : α}
    (ht : quintKeyOfFinset (α := α) T = some (t1, t2, t3, t4, t5)) :
    quadKeyOfFinset (α := α) T = some (t1, t2, t3, t4) := by
  classical
  cases hq : quadKeyOfFinset (α := α) T with
  | none =>
      have : (none : Option (α × α × α × α × α)) = some (t1, t2, t3, t4, t5) := by
        simpa [quintKeyOfFinset, hq] using ht
      cases this
  | some q =>
      let q1 : α := q.1
      let q2 : α := q.2.1
      let q3 : α := q.2.2.1
      let q4 : α := q.2.2.2
      let R : Finset α := ((((T.erase q1).erase q2).erase q3).erase q4)
      by_cases hR : R.Nonempty
      · let t5' : α := Classical.choose hR
        have ht_def :
            quintKeyOfFinset (α := α) T = some (q1, q2, q3, q4, t5') := by
          simp [quintKeyOfFinset, hq, q1, q2, q3, q4, R, hR, t5']
        have hEq :
            some (q1, q2, q3, q4, t5') = some (t1, t2, t3, t4, t5) := by
          simpa [ht_def] using ht
        have hEq' : (q1, q2, q3, q4, t5') = (t1, t2, t3, t4, t5) := Option.some.inj hEq
        have hq1 : q1 = t1 := by
          simpa using congrArg (fun p : α × α × α × α × α => p.1) hEq'
        have hq2 : q2 = t2 := by
          simpa using congrArg (fun p : α × α × α × α × α => p.2.1) hEq'
        have hq3 : q3 = t3 := by
          simpa using congrArg (fun p : α × α × α × α × α => p.2.2.1) hEq'
        have hq4 : q4 = t4 := by
          simpa using congrArg (fun p : α × α × α × α × α => p.2.2.2.1) hEq'
        have hq1' : q.1 = t1 := by
          simpa [q1] using hq1
        have hq2' : q.2.1 = t2 := by
          simpa [q2] using hq2
        have hq3' : q.2.2.1 = t3 := by
          simpa [q3] using hq3
        have hq4' : q.2.2.2 = t4 := by
          simpa [q4] using hq4
        have qEq : q = (t1, t2, t3, t4) := by
          apply Prod.ext
          · exact hq1'
          ·
            apply Prod.ext
            · exact hq2'
            ·
              apply Prod.ext
              · exact hq3'
              · exact hq4'
        simpa [qEq] using hq
      ·
        have : (none : Option (α × α × α × α × α)) = some (t1, t2, t3, t4, t5) := by
          simpa [quintKeyOfFinset, hq, q1, q2, q3, q4, R, hR] using ht
        cases this

theorem trace2PlusOfFinset_eq_some_some_true_of_trace5PlusOfFinset_eq_some
    {T : Finset α} {t1 t2 t3 t4 t5 : α} {b : Bool}
    (ht : trace5PlusOfFinset (α := α) T = some (t1, t2, t3, t4, t5, b)) :
    trace2PlusOfFinset (α := α) T = some (t1, some t2, true) := by
  classical
  -- Extract the underlying `quintKey` tuple.
  have hquint : quintKeyOfFinset (α := α) T = some (t1, t2, t3, t4, t5) := by
    cases hq : quintKeyOfFinset (α := α) T with
    | none =>
        have : (none : Option (α × α × α × α × α × Bool)) = some (t1, t2, t3, t4, t5, b) := by
          simpa [trace5PlusOfFinset, hq] using ht
        cases this
    | some q =>
        have hEq :
            some
                (q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2,
                  hasSixthOfFinset (α := α) T q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) =
              some (t1, t2, t3, t4, t5, b) := by
          simpa [trace5PlusOfFinset, hq] using ht
        have hEq' :
            (q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2,
                hasSixthOfFinset (α := α) T q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) =
              (t1, t2, t3, t4, t5, b) :=
          Option.some.inj hEq
        have hq1 : q.1 = t1 := by
          simpa using congrArg (fun p : α × α × α × α × α × Bool => p.1) hEq'
        have hq2 : q.2.1 = t2 := by
          simpa using congrArg (fun p : α × α × α × α × α × Bool => p.2.1) hEq'
        have hq3 : q.2.2.1 = t3 := by
          simpa using congrArg (fun p : α × α × α × α × α × Bool => p.2.2.1) hEq'
        have hq4 : q.2.2.2.1 = t4 := by
          simpa using congrArg (fun p : α × α × α × α × α × Bool => p.2.2.2.1) hEq'
        have hq5 : q.2.2.2.2 = t5 := by
          simpa using congrArg (fun p : α × α × α × α × α × Bool => p.2.2.2.2.1) hEq'
        have qEq : q = (t1, t2, t3, t4, t5) := by
          ext <;> simp [hq1, hq2, hq3, hq4, hq5]
        simpa [qEq] using hq
  have hquad :
      quadKeyOfFinset (α := α) T = some (t1, t2, t3, t4) :=
    quadKeyOfFinset_eq_some_of_quintKeyOfFinset_eq_some (α := α) (T := T) hquint
  have htriple :
      tripleKeyOfFinset (α := α) T = some (t1, t2, t3) :=
    tripleKeyOfFinset_eq_some_of_quadKeyOfFinset_eq_some (α := α) (T := T) hquad
  exact
    trace2PlusOfFinset_eq_some_some_true_of_tripleKeyOfFinset_eq_some (α := α) (T := T) htriple

theorem mem_left_of_trace2PlusOfFinset_eq_some
    {T : Finset α} {t1 : α} {ot2 : Option α} {b : Bool}
    (ht : trace2PlusOfFinset (α := α) T = some (t1, ot2, b)) :
    t1 ∈ T := by
  classical
  by_cases hT : T.Nonempty
  · let t1' : α := Classical.choose hT
    have ht1' : t1' ∈ T := Classical.choose_spec hT
    let T2 : Finset α := T.erase t1'
    by_cases hT2 : T2.Nonempty
    · let t2' : α := Classical.choose hT2
      let T3 : Finset α := T2.erase t2'
      by_cases hT3 : T3.Nonempty
      · have ht' :
            trace2PlusOfFinset (α := α) T = some (t1', some t2', true) := by
          simp [trace2PlusOfFinset, hT, t1', T2, hT2, t2', T3, hT3]
        have : some (t1, ot2, b) = some (t1', some t2', true) := by
          simpa [ht] using ht'
        have ht1 : t1 = t1' := congrArg Prod.fst (Option.some.inj this)
        simpa [ht1] using ht1'
      · have ht' :
            trace2PlusOfFinset (α := α) T = some (t1', some t2', false) := by
          simp [trace2PlusOfFinset, hT, t1', T2, hT2, t2', T3, hT3]
        have : some (t1, ot2, b) = some (t1', some t2', false) := by
          simpa [ht] using ht'
        have ht1 : t1 = t1' := congrArg Prod.fst (Option.some.inj this)
        simpa [ht1] using ht1'
    · have ht' :
          trace2PlusOfFinset (α := α) T = some (t1', none, false) := by
        simp [trace2PlusOfFinset, hT, t1', T2, hT2]
      have : some (t1, ot2, b) = some (t1', none, false) := by
        simpa [ht] using ht'
      have ht1 : t1 = t1' := congrArg Prod.fst (Option.some.inj this)
      simpa [ht1] using ht1'
  · have : False := by
      have : trace2PlusOfFinset (α := α) T = none := by
        simp [trace2PlusOfFinset, hT]
      have : (none : Option (α × Option α × Bool)) = some (t1, ot2, b) := by
        simpa [ht] using this
      cases this
    exact False.elim this

theorem mem_right_erase_of_trace2PlusOfFinset_eq_some_some
    {T : Finset α} {t1 t2 : α} {b : Bool}
    (ht : trace2PlusOfFinset (α := α) T = some (t1, some t2, b)) :
    t2 ∈ T.erase t1 := by
  classical
  by_cases hT : T.Nonempty
  · let t1' : α := Classical.choose hT
    let T2 : Finset α := T.erase t1'
    by_cases hT2 : T2.Nonempty
    · let t2' : α := Classical.choose hT2
      have ht2mem : t2' ∈ T2 := Classical.choose_spec hT2
      let T3 : Finset α := T2.erase t2'
      by_cases hT3 : T3.Nonempty
      · have ht' :
            trace2PlusOfFinset (α := α) T = some (t1', some t2', true) := by
          simp [trace2PlusOfFinset, hT, t1', T2, hT2, t2', T3, hT3]
        have : some (t1, some t2, b) = some (t1', some t2', true) := by
          simpa [ht] using ht'
        have ht1 : t1 = t1' := congrArg Prod.fst (Option.some.inj this)
        have ht2 :
            some t2 = some t2' := by
          -- compare second components
          exact congrArg (fun p : Option α × Bool => p.1) (congrArg Prod.snd (Option.some.inj this))
        have ht2eq : t2 = t2' := Option.some.inj ht2
        -- `t2' ∈ T.erase t1'`, and `t1=t1'`.
        simpa [T2, ht1, ht2eq] using ht2mem
      · have ht' :
            trace2PlusOfFinset (α := α) T = some (t1', some t2', false) := by
          simp [trace2PlusOfFinset, hT, t1', T2, hT2, t2', T3, hT3]
        have : some (t1, some t2, b) = some (t1', some t2', false) := by
          simpa [ht] using ht'
        have ht1 : t1 = t1' := congrArg Prod.fst (Option.some.inj this)
        have ht2 :
            some t2 = some t2' := by
          exact congrArg (fun p : Option α × Bool => p.1) (congrArg Prod.snd (Option.some.inj this))
        have ht2eq : t2 = t2' := Option.some.inj ht2
        simpa [T2, ht1, ht2eq] using ht2mem
    · have ht' :
          trace2PlusOfFinset (α := α) T = some (t1', none, false) := by
        simp [trace2PlusOfFinset, hT, t1', T2, hT2]
      have : some (t1, some t2, b) = some (t1', none, false) := by
        simpa [ht] using ht'
      have hcontr : (some t2 : Option α) = none := by
        exact congrArg (fun p : α × Option α × Bool => p.2.1) (Option.some.inj this)
      cases hcontr
  · have : False := by
      have : trace2PlusOfFinset (α := α) T = none := by
        simp [trace2PlusOfFinset, hT]
      have : (none : Option (α × Option α × Bool)) = some (t1, some t2, b) := by
        simpa [ht] using this
      cases this
    exact False.elim this

theorem mem_right_of_trace2PlusOfFinset_eq_some_some
    {T : Finset α} {t1 t2 : α} {b : Bool}
    (ht : trace2PlusOfFinset (α := α) T = some (t1, some t2, b)) :
    t2 ∈ T := by
  exact (Finset.mem_erase.mp (mem_right_erase_of_trace2PlusOfFinset_eq_some_some (α := α) ht)).2

theorem ne_left_right_of_trace2PlusOfFinset_eq_some_some
    {T : Finset α} {t1 t2 : α} {b : Bool}
    (ht : trace2PlusOfFinset (α := α) T = some (t1, some t2, b)) :
    t2 ≠ t1 := by
  exact (Finset.mem_erase.mp (mem_right_erase_of_trace2PlusOfFinset_eq_some_some (α := α) ht)).1

theorem subset_pair_of_trace2PlusOfFinset_eq_some_some_false
    {T : Finset α} {t1 t2 : α}
    (ht : trace2PlusOfFinset (α := α) T = some (t1, some t2, false)) :
    T ⊆ ({t1, t2} : Finset α) := by
  classical
  by_cases hT : T.Nonempty
  · let t1' : α := Classical.choose hT
    let T2 : Finset α := T.erase t1'
    by_cases hT2 : T2.Nonempty
    · let t2' : α := Classical.choose hT2
      let T3 : Finset α := T2.erase t2'
      by_cases hT3 : T3.Nonempty
      · -- Contradiction: definition would return `true`.
        have ht_true :
            trace2PlusOfFinset (α := α) T = some (t1', some t2', true) := by
          simp [trace2PlusOfFinset, hT, t1', T2, hT2, t2', T3, hT3]
        have : False := by
          have hsome : some (t1', some t2', true) = some (t1, some t2, false) := by
            simpa [ht_true] using ht
          have htriple : (t1', some t2', true) = (t1, some t2, false) :=
            Option.some.inj hsome
          have : (true : Bool) = false := by
            simpa using congrArg (fun p : α × Option α × Bool => p.2.2) htriple
          cases this
        exact False.elim this
      · have ht_false :
            trace2PlusOfFinset (α := α) T = some (t1', some t2', false) := by
          simp [trace2PlusOfFinset, hT, t1', T2, hT2, t2', T3, hT3]
        have hsome : some (t1', some t2', false) = some (t1, some t2, false) := by
          simpa [ht_false] using ht
        have htriple :
            (t1', some t2', false) = (t1, some t2, false) :=
          Option.some.inj hsome
        have ht1 : t1' = t1 := by
          simpa using congrArg (fun p : α × Option α × Bool => p.1) htriple
        have ht2 : t2' = t2 := by
          have h2 : (some t2' : Option α) = some t2 := by
            simpa using congrArg (fun p : α × Option α × Bool => p.2.1) htriple
          exact Option.some.inj h2
        have hT3empty : T3 = ∅ := by
          simpa [Finset.not_nonempty_iff_eq_empty] using hT3
        have hsub' : T ⊆ ({t1', t2'} : Finset α) := by
          intro z hz
          by_cases hz1 : z = t1'
          · simp [hz1]
          by_cases hz2 : z = t2'
          · simp [hz2, hz1]
          have hzT2 : z ∈ T2 := Finset.mem_erase.mpr ⟨hz1, hz⟩
          have hzT3 : z ∈ T3 := Finset.mem_erase.mpr ⟨hz2, hzT2⟩
          exact False.elim (by simpa [hT3empty] using hzT3)
        simpa [ht1, ht2] using hsub'
    · -- Contradiction: definition would return `some (t1', none, false)`.
      have ht_def :
          trace2PlusOfFinset (α := α) T = some (t1', (none : Option α), false) := by
        simp [trace2PlusOfFinset, hT, t1', T2, hT2]
      have : False := by
        have hsome :
            some (t1', (none : Option α), false) = some (t1, some t2, false) := by
          simpa [ht_def] using ht
        have htriple : (t1', (none : Option α), false) = (t1, some t2, false) :=
          Option.some.inj hsome
        have : (none : Option α) = some t2 := by
          simpa using congrArg (fun p : α × Option α × Bool => p.2.1) htriple
        cases this
      exact False.elim this
  · -- Contradiction: definition would return `none`.
    have ht_def : trace2PlusOfFinset (α := α) T = none := by
      simp [trace2PlusOfFinset, hT]
    have : False := by
      have : (none : Option (α × Option α × Bool)) = some (t1, some t2, false) := by
        simpa [ht_def] using ht
      cases this
    exact False.elim this

theorem subset_singleton_of_trace2PlusOfFinset_eq_some_none_false
    {T : Finset α} {t1 : α}
    (ht : trace2PlusOfFinset (α := α) T = some (t1, (none : Option α), false)) :
    T ⊆ ({t1} : Finset α) := by
  classical
  by_cases hT : T.Nonempty
  · let t1' : α := Classical.choose hT
    let T2 : Finset α := T.erase t1'
    by_cases hT2 : T2.Nonempty
    · -- Contradiction: definition would return `some (t1', some t2, b)`.
      let t2' : α := Classical.choose hT2
      let T3 : Finset α := T2.erase t2'
      by_cases hT3 : T3.Nonempty
      · have ht_def :
            trace2PlusOfFinset (α := α) T = some (t1', some t2', true) := by
          simp [trace2PlusOfFinset, hT, t1', T2, hT2, t2', T3, hT3]
        have : False := by
          have hsome :
              some (t1', some t2', true) = some (t1, (none : Option α), false) := by
            simpa [ht_def] using ht
          have htriple : (t1', some t2', true) = (t1, (none : Option α), false) :=
            Option.some.inj hsome
          have : (some t2' : Option α) = none := by
            simpa using congrArg (fun p : α × Option α × Bool => p.2.1) htriple
          cases this
        exact False.elim this
      · have ht_def :
            trace2PlusOfFinset (α := α) T = some (t1', some t2', false) := by
          simp [trace2PlusOfFinset, hT, t1', T2, hT2, t2', T3, hT3]
        have : False := by
          have hsome :
              some (t1', some t2', false) = some (t1, (none : Option α), false) := by
            simpa [ht_def] using ht
          have htriple : (t1', some t2', false) = (t1, (none : Option α), false) :=
            Option.some.inj hsome
          have : (some t2' : Option α) = none := by
            simpa using congrArg (fun p : α × Option α × Bool => p.2.1) htriple
          cases this
        exact False.elim this
    · have ht_def :
          trace2PlusOfFinset (α := α) T = some (t1', (none : Option α), false) := by
        simp [trace2PlusOfFinset, hT, t1', T2, hT2]
      have hsome :
          some (t1', (none : Option α), false) = some (t1, (none : Option α), false) := by
        simpa [ht_def] using ht
      have ht1 : t1' = t1 := by
        simpa using congrArg (fun p : α × Option α × Bool => p.1) (Option.some.inj hsome)
      have hT2empty : T2 = ∅ := by
        simpa [Finset.not_nonempty_iff_eq_empty] using hT2
      have hsub' : T ⊆ ({t1'} : Finset α) := by
        intro z hz
        by_cases hz1 : z = t1'
        · simp [hz1]
        · have hzT2 : z ∈ T2 := Finset.mem_erase.mpr ⟨hz1, hz⟩
          exact False.elim (by simpa [hT2empty] using hzT2)
      simpa [ht1] using hsub'
  · -- Contradiction: definition would return `none`.
    have ht_def : trace2PlusOfFinset (α := α) T = none := by
      simp [trace2PlusOfFinset, hT]
    have : False := by
      have : (none : Option (α × Option α × Bool)) = some (t1, (none : Option α), false) := by
        simpa [ht_def] using ht
      cases this
    exact False.elim this

theorem eq_empty_of_trace2PlusOfFinset_eq_none
    {T : Finset α} (ht : trace2PlusOfFinset (α := α) T = none) :
    T = (∅ : Finset α) := by
  classical
  by_cases hT : T.Nonempty
  · -- Contradiction: definition would return `some ...` in every branch.
    let t1 : α := Classical.choose hT
    let T2 : Finset α := T.erase t1
    by_cases hT2 : T2.Nonempty
    · let t2 : α := Classical.choose hT2
      let T3 : Finset α := T2.erase t2
      by_cases hT3 : T3.Nonempty
      · have ht_def :
            trace2PlusOfFinset (α := α) T = some (t1, some t2, true) := by
          simp [trace2PlusOfFinset, hT, t1, T2, hT2, t2, T3, hT3]
        have : (some (t1, some t2, true) : Option (α × Option α × Bool)) = none := by
          simpa [ht_def] using ht
        cases this
      · have ht_def :
            trace2PlusOfFinset (α := α) T = some (t1, some t2, false) := by
          simp [trace2PlusOfFinset, hT, t1, T2, hT2, t2, T3, hT3]
        have : (some (t1, some t2, false) : Option (α × Option α × Bool)) = none := by
          simpa [ht_def] using ht
        cases this
    · have ht_def :
          trace2PlusOfFinset (α := α) T = some (t1, (none : Option α), false) := by
        simp [trace2PlusOfFinset, hT, t1, T2, hT2]
      have : (some (t1, (none : Option α), false) : Option (α × Option α × Bool)) = none := by
        simpa [ht_def] using ht
      cases this
  · simpa [Finset.not_nonempty_iff_eq_empty] using hT

theorem eq_singleton_of_trace2PlusOfFinset_eq_some_none_false
    {T : Finset α} {t1 : α}
    (ht : trace2PlusOfFinset (α := α) T = some (t1, (none : Option α), false)) :
    T = ({t1} : Finset α) := by
  classical
  apply Finset.Subset.antisymm
  · exact subset_singleton_of_trace2PlusOfFinset_eq_some_none_false (α := α) ht
  ·
    -- First show `t1 ∈ T` by comparing the definition output to `ht`.
    have ht1mem : t1 ∈ T := by
      have hTne : T.Nonempty := by
        by_contra h0
        have : trace2PlusOfFinset (α := α) T = none := by
          simp [trace2PlusOfFinset, h0]
        cases (by simpa [this] using ht :
          (none : Option (α × Option α × Bool)) = some (t1, (none : Option α), false))
      let t1' : α := Classical.choose hTne
      let T2 : Finset α := T.erase t1'
      have hT2 : ¬ T2.Nonempty := by
        by_cases hT2' : T2.Nonempty
        · -- Contradiction: definition would return `some (t1', some t2, _)`.
          let t2' : α := Classical.choose hT2'
          let T3 : Finset α := T2.erase t2'
          by_cases hT3 : T3.Nonempty
          · have ht_def :
                trace2PlusOfFinset (α := α) T = some (t1', some t2', true) := by
              simp [trace2PlusOfFinset, hTne, t1', T2, hT2', t2', T3, hT3]
            have hsome :
                some (t1', some t2', true) =
                  some (t1, (none : Option α), false) := by
              simpa [ht_def] using ht
            have htriple :
                (t1', some t2', true) = (t1, (none : Option α), false) :=
              Option.some.inj hsome
            have : (some t2' : Option α) = none := by
              simpa using congrArg (fun p : α × Option α × Bool => p.2.1) htriple
            cases this
          · have ht_def :
                trace2PlusOfFinset (α := α) T = some (t1', some t2', false) := by
              simp [trace2PlusOfFinset, hTne, t1', T2, hT2', t2', T3, hT3]
            have hsome :
                some (t1', some t2', false) =
                  some (t1, (none : Option α), false) := by
              simpa [ht_def] using ht
            have htriple :
                (t1', some t2', false) = (t1, (none : Option α), false) :=
              Option.some.inj hsome
            have : (some t2' : Option α) = none := by
              simpa using congrArg (fun p : α × Option α × Bool => p.2.1) htriple
            cases this
        · exact hT2'
      have ht_def :
          trace2PlusOfFinset (α := α) T = some (t1', (none : Option α), false) := by
        simp [trace2PlusOfFinset, hTne, t1', T2, hT2]
      have hsome :
          some (t1', (none : Option α), false) = some (t1, (none : Option α), false) := by
        simpa [ht_def] using ht
      have ht1 : t1' = t1 := by
        simpa using congrArg (fun p : α × Option α × Bool => p.1) (Option.some.inj hsome)
      have ht1mem' : t1' ∈ T := Classical.choose_spec hTne
      simpa [ht1] using ht1mem'
    -- Now `z ∈ {t1}` implies `z ∈ T`.
    intro z hz
    have hzEq : z = t1 := by
      simpa using (Finset.mem_singleton.mp hz)
    simpa [hzEq] using ht1mem

theorem eq_pair_of_trace2PlusOfFinset_eq_some_some_false
    {T : Finset α} {t1 t2 : α}
    (ht : trace2PlusOfFinset (α := α) T = some (t1, some t2, false)) :
    T = ({t1, t2} : Finset α) := by
  classical
  apply Finset.Subset.antisymm
  · exact subset_pair_of_trace2PlusOfFinset_eq_some_some_false (α := α) ht
  · intro z hz
    have hz' : z = t1 ∨ z = t2 := by
      simpa [Finset.mem_insert, Finset.mem_singleton] using hz
    have htne : T.Nonempty := by
      by_contra h0
      have : trace2PlusOfFinset (α := α) T = none := by
        simp [trace2PlusOfFinset, h0]
      cases (by simpa [this] using ht : (none : Option (α × Option α × Bool)) =
        some (t1, some t2, false))
    let t1' : α := Classical.choose htne
    let T2 : Finset α := T.erase t1'
    have hT2ne : T2.Nonempty := by
      by_cases hT2 : T2.Nonempty
      · exact hT2
      · -- Contradiction: definition would return `some (t1', none, false)`.
        have ht_def :
            trace2PlusOfFinset (α := α) T = some (t1', (none : Option α), false) := by
          simp [trace2PlusOfFinset, htne, t1', T2, hT2]
        have hsome :
            some (t1', (none : Option α), false) = some (t1, some t2, false) := by
          simpa [ht_def] using ht
        have htriple :
            (t1', (none : Option α), false) = (t1, some t2, false) :=
          Option.some.inj hsome
        have : (none : Option α) = some t2 := by
          simpa using congrArg (fun p : α × Option α × Bool => p.2.1) htriple
        cases this
    let t2' : α := Classical.choose hT2ne
    let T3 : Finset α := T2.erase t2'
    have hT3 : ¬ T3.Nonempty := by
      by_cases hT3' : T3.Nonempty
      · -- Contradiction: definition would return `true`.
        have ht_def :
            trace2PlusOfFinset (α := α) T = some (t1', some t2', true) := by
          simp [trace2PlusOfFinset, htne, t1', T2, hT2ne, t2', T3, hT3']
        have hsome :
            some (t1', some t2', true) = some (t1, some t2, false) := by
          simpa [ht_def] using ht
        have htriple :
            (t1', some t2', true) = (t1, some t2, false) :=
          Option.some.inj hsome
        have : (true : Bool) = false := by
          simpa using congrArg (fun p : α × Option α × Bool => p.2.2) htriple
        cases this
      · exact hT3'
    have ht_def :
        trace2PlusOfFinset (α := α) T = some (t1', some t2', false) := by
      simp [trace2PlusOfFinset, htne, t1', T2, hT2ne, t2', T3, hT3]
    have hsome :
        some (t1', some t2', false) = some (t1, some t2, false) := by
      simpa [ht_def] using ht
    have htriple : (t1', some t2', false) = (t1, some t2, false) :=
      Option.some.inj hsome
    have ht1 : t1' = t1 := by
      simpa using congrArg (fun p : α × Option α × Bool => p.1) htriple
    have ht2 : t2' = t2 := by
      have : (some t2' : Option α) = some t2 := by
        simpa using congrArg (fun p : α × Option α × Bool => p.2.1) htriple
      exact Option.some.inj this
    -- `t1 ∈ T` and `t2 ∈ T` by construction.
    have ht1mem' : t1' ∈ T := Classical.choose_spec htne
    have ht2mem' : t2' ∈ T := by
      have : t2' ∈ T2 := Classical.choose_spec hT2ne
      exact (Finset.mem_erase.mp this).2
    have ht1mem : t1 ∈ T := by
      simpa [ht1] using ht1mem'
    have ht2mem : t2 ∈ T := by
      simpa [ht2] using ht2mem'
    rcases hz' with rfl | rfl
    · exact ht1mem
    · exact ht2mem

/-!
Exact identification of the extra part `w.A \\ insert x S` from `tx2PlusOfWitness` in the
rigid (`hasMore=false`) regimes.

These are local “shape” lemmas used in the per-`x` subfiber collision proofs.
-/

theorem eq_empty_of_tx2PlusOfWitness_eq_none
    {S : Finset α} {x : α} (w : BlockedUnionWitness family S x)
    (ht : tx2PlusOfWitness (family := family) (S := S) (x := x) w = none) :
    w.A \ insert x S = (∅ : Finset α) := by
  classical
  let extras : Finset α := w.A \ insert x S
  by_cases hex : extras.Nonempty
  · let t1 : α := Classical.choose hex
    let extras2 : Finset α := extras.erase t1
    by_cases hex2 : extras2.Nonempty
    · let t2 : α := Classical.choose hex2
      let extras3 : Finset α := extras2.erase t2
      by_cases hex3 : extras3.Nonempty
      · have ht_def :
            tx2PlusOfWitness (family := family) (S := S) (x := x) w =
              some (t1, some t2, true) := by
          simp [tx2PlusOfWitness, extras, hex, t1, extras2, hex2, t2, extras3, hex3]
        have : (some (t1, some t2, true) : Option (α × Option α × Bool)) = none := by
          simpa [ht_def] using ht
        cases this
      · have ht_def :
            tx2PlusOfWitness (family := family) (S := S) (x := x) w =
              some (t1, some t2, false) := by
          simp [tx2PlusOfWitness, extras, hex, t1, extras2, hex2, t2, extras3, hex3]
        have : (some (t1, some t2, false) : Option (α × Option α × Bool)) = none := by
          simpa [ht_def] using ht
        cases this
    · have ht_def :
          tx2PlusOfWitness (family := family) (S := S) (x := x) w =
            some (t1, (none : Option α), false) := by
        simp [tx2PlusOfWitness, extras, hex, t1, extras2, hex2]
      have : (some (t1, (none : Option α), false) : Option (α × Option α × Bool)) = none := by
        simpa [ht_def] using ht
      cases this
  · have hex0 : extras = (∅ : Finset α) := by
      simpa [Finset.not_nonempty_iff_eq_empty] using hex
    simpa [extras, hex0]

theorem eq_singleton_of_tx2PlusOfWitness_eq_some_none_false
    {S : Finset α} {x : α} (w : BlockedUnionWitness family S x) {t1 : α}
    (ht : tx2PlusOfWitness (family := family) (S := S) (x := x) w = some (t1, none, false)) :
    w.A \ insert x S = ({t1} : Finset α) := by
  classical
  let extras : Finset α := w.A \ insert x S
  -- `extras` is nonempty, else the trace would be `none`.
  have hex : extras.Nonempty := by
    by_contra h0
    have ht_def :
        tx2PlusOfWitness (family := family) (S := S) (x := x) w = none := by
      simp [tx2PlusOfWitness, extras, h0]
    cases (by simpa [ht_def] using ht :
      (none : Option (α × Option α × Bool)) = some (t1, none, false))
  let t1' : α := Classical.choose hex
  let extras2 : Finset α := extras.erase t1'
  have hex2 : ¬ extras2.Nonempty := by
    by_cases hex2' : extras2.Nonempty
    · -- Contradiction: definition would return `some (t1', some t2', _)`.
      let t2' : α := Classical.choose hex2'
      let extras3 : Finset α := extras2.erase t2'
      by_cases hex3 : extras3.Nonempty
      · have ht_def :
            tx2PlusOfWitness (family := family) (S := S) (x := x) w =
              some (t1', some t2', true) := by
          simp [tx2PlusOfWitness, extras, hex, t1', extras2, hex2', t2', extras3, hex3]
        have hsome :
            some (t1', some t2', true) = some (t1, none, false) := by
          simpa [ht_def] using ht
        have htriple : (t1', some t2', true) = (t1, none, false) :=
          Option.some.inj hsome
        have : (some t2' : Option α) = none := by
          simpa using congrArg (fun p : α × Option α × Bool => p.2.1) htriple
        cases this
      · have ht_def :
            tx2PlusOfWitness (family := family) (S := S) (x := x) w =
              some (t1', some t2', false) := by
          simp [tx2PlusOfWitness, extras, hex, t1', extras2, hex2', t2', extras3, hex3]
        have hsome :
            some (t1', some t2', false) = some (t1, none, false) := by
          simpa [ht_def] using ht
        have htriple : (t1', some t2', false) = (t1, none, false) :=
          Option.some.inj hsome
        have : (some t2' : Option α) = none := by
          simpa using congrArg (fun p : α × Option α × Bool => p.2.1) htriple
        cases this
    · exact hex2'
  have ht_def :
      tx2PlusOfWitness (family := family) (S := S) (x := x) w =
        some (t1', (none : Option α), false) := by
    simp [tx2PlusOfWitness, extras, hex, t1', extras2, hex2]
  have hsome :
      some (t1', (none : Option α), false) = some (t1, (none : Option α), false) := by
    simpa [ht_def] using ht
  have ht1 : t1' = t1 := by
    simpa using congrArg (fun p : α × Option α × Bool => p.1) (Option.some.inj hsome)
  have hNoMore : extras2 = (∅ : Finset α) := by
    simpa [Finset.not_nonempty_iff_eq_empty] using hex2
  have hNoMore' : extras.erase t1 = (∅ : Finset α) := by
    simpa [extras2, ht1] using hNoMore
  apply Finset.Subset.antisymm
  · -- `extras ⊆ {t1}` using no-more.
    intro z hz
    by_cases hz1 : z = t1
    · simp [hz1]
    · have hzErase : z ∈ extras.erase t1 := Finset.mem_erase.mpr ⟨hz1, by simpa [extras] using hz⟩
      have : False := by
        have : z ∈ (∅ : Finset α) := by simpa [hNoMore'] using hzErase
        simpa using this
      exact False.elim this
  · -- `{t1} ⊆ extras` since `t1 ∈ extras` by choice.
    intro z hz
    have hzEq : z = t1 := by simpa using (Finset.mem_singleton.mp hz)
    subst hzEq
    have ht1mem' : t1' ∈ extras := Classical.choose_spec hex
    simpa [extras, ht1] using ht1mem'

theorem eq_pair_of_tx2PlusOfWitness_eq_some_some_false
    {S : Finset α} {x : α} (w : BlockedUnionWitness family S x) {t1 t2 : α}
    (ht : tx2PlusOfWitness (family := family) (S := S) (x := x) w = some (t1, some t2, false)) :
    w.A \ insert x S = ({t1, t2} : Finset α) := by
  classical
  let extras : Finset α := w.A \ insert x S
  have hex : extras.Nonempty := by
    by_contra h0
    have ht_def :
        tx2PlusOfWitness (family := family) (S := S) (x := x) w = none := by
      simp [tx2PlusOfWitness, extras, h0]
    cases (by simpa [ht_def] using ht :
      (none : Option (α × Option α × Bool)) = some (t1, some t2, false))
  let t1' : α := Classical.choose hex
  let extras2 : Finset α := extras.erase t1'
  have hex2 : extras2.Nonempty := by
    by_cases hex2' : extras2.Nonempty
    · exact hex2'
    · have ht_def :
          tx2PlusOfWitness (family := family) (S := S) (x := x) w =
            some (t1', (none : Option α), false) := by
        simp [tx2PlusOfWitness, extras, hex, t1', extras2, hex2']
      have hsome :
          some (t1', (none : Option α), false) = some (t1, some t2, false) := by
        simpa [ht_def] using ht
      have htriple : (t1', (none : Option α), false) = (t1, some t2, false) :=
        Option.some.inj hsome
      have : (none : Option α) = some t2 := by
        simpa using congrArg (fun p : α × Option α × Bool => p.2.1) htriple
      cases this
  let t2' : α := Classical.choose hex2
  let extras3 : Finset α := extras2.erase t2'
  have hex3 : ¬ extras3.Nonempty := by
    by_cases hex3' : extras3.Nonempty
    · have ht_def :
          tx2PlusOfWitness (family := family) (S := S) (x := x) w =
            some (t1', some t2', true) := by
        simp [tx2PlusOfWitness, extras, hex, t1', extras2, hex2, t2', extras3, hex3']
      have hsome :
          some (t1', some t2', true) = some (t1, some t2, false) := by
        simpa [ht_def] using ht
      have htriple : (t1', some t2', true) = (t1, some t2, false) :=
        Option.some.inj hsome
      have : (true : Bool) = false := by
        simpa using congrArg (fun p : α × Option α × Bool => p.2.2) htriple
      cases this
    · exact hex3'
  have ht_def :
      tx2PlusOfWitness (family := family) (S := S) (x := x) w =
        some (t1', some t2', false) := by
    simp [tx2PlusOfWitness, extras, hex, t1', extras2, hex2, t2', extras3, hex3]
  have hsome :
      some (t1', some t2', false) = some (t1, some t2, false) := by
    simpa [ht_def] using ht
  have htriple : (t1', some t2', false) = (t1, some t2, false) :=
    Option.some.inj hsome
  have ht1 : t1' = t1 := by
    simpa using congrArg (fun p : α × Option α × Bool => p.1) htriple
  have ht2 : t2' = t2 := by
    have : (some t2' : Option α) = some t2 := by
      simpa using congrArg (fun p : α × Option α × Bool => p.2.1) htriple
    exact Option.some.inj this
  have hNoMore : extras3 = (∅ : Finset α) := by
    simpa [Finset.not_nonempty_iff_eq_empty] using hex3
  have hNoMore' : (extras.erase t1).erase t2 = (∅ : Finset α) := by
    simpa [extras2, extras3, ht1, ht2] using hNoMore
  apply Finset.Subset.antisymm
  · -- `extras ⊆ {t1,t2}` using no-more.
    intro z hz
    by_cases hz1 : z = t1
    · simp [hz1]
    · have hzErase1 : z ∈ extras.erase t1 := Finset.mem_erase.mpr ⟨hz1, by simpa [extras] using hz⟩
      by_cases hz2 : z = t2
      · simp [hz2, hz1]
      · have hzErase2 : z ∈ (extras.erase t1).erase t2 := Finset.mem_erase.mpr ⟨hz2, hzErase1⟩
        have : False := by
          have : z ∈ (∅ : Finset α) := by simpa [hNoMore'] using hzErase2
          simpa using this
        exact False.elim this
  · -- `{t1,t2} ⊆ extras` since `t1,t2 ∈ extras` by choice.
    intro z hz
    rcases Finset.mem_insert.mp hz with hzEq | hz
    · subst hzEq
      have ht1mem' : t1' ∈ extras := Classical.choose_spec hex
      simpa [extras, ht1] using ht1mem'
    · have hzEq : z = t2 := by simpa using (Finset.mem_singleton.mp hz)
      subst hzEq
      have ht2mem' : t2' ∈ extras2 := Classical.choose_spec hex2
      have ht2mem'' : t2' ∈ extras := by
        exact (Finset.mem_erase.mp ht2mem').2
      simpa [extras, ht2] using ht2mem''

/-!
Signature helpers.

We will bucket per-`x` completions using:
`(y, rABTrace, wTrace, coreTrace, bTrace, outsideTrace)` where
`rABTrace := trace2PlusOfFinset ((core.erase y) ∩ (kA ∪ kB))`
`wTrace := tx2PlusOfWitness w` for the chosen blocking witness `w` of `S ∪ {y}`,
`coreTrace := trace2PlusOfFinset (core.erase y)`, and
`bTrace := trace2PlusOfFinset (B \\ insert y S)`, and
`outsideTrace := trace2PlusOfFinset (S \\ (A ∪ B))`.
-/

/-- Compressed trace of the projected anchor `rAB`. -/
noncomputable def rABTrace (k : WLcertKey α) (S : Finset α) (y : α)
    (w : BlockedUnionWitness family S y) : Option (α × Option α × Bool) :=
  trace2PlusOfFinset (α := α) (rAB (family := family) (k := k) (S := S) (y := y) w)

noncomputable def bTrace (S : Finset α) (y : α) (w : BlockedUnionWitness family S y) :
    Option (α × Option α × Bool) :=
  trace2PlusOfFinset (α := α) (w.B \ insert y S)

noncomputable def outsideTrace (S : Finset α) (y : α) (w : BlockedUnionWitness family S y) :
    Option (α × Option α × Bool) :=
  trace2PlusOfFinset (α := α) (S \ (w.A ∪ w.B))

/--
Auxiliary selector for the outMore `τ=true` residue bounded-fiber step.

Given a normalized blocked-union witness `wz` for `S ∪ {z}`, try to pick a single element `u`
that is:
- preferably in the "core side" `wz.core.erase z` (Plan A), else
- from the first `tx2PlusOfWitness` extra on the A-side (Plan B, only when the core-side is empty).

We keep the result as an `Option α` to avoid defaulting when neither source is available.
The calling lemma is expected to treat the `none` branch as a separate subcase.
-/
noncomputable def uFromZWitness (S : Finset α) (z : α) (wz : BlockedUnionWitness family S z) :
    Option α := by
  classical
  by_cases hcore : (wz.core.erase z).Nonempty
  · exact some (Classical.choose hcore)
  · -- Plan B: pull the first `tx2Plus` element from the A-side extras when available.
    match tx2PlusOfWitness (family := family) (S := S) (x := z) wz with
    | none => exact none
    | some triple => exact some triple.1

/-- In any `BlockedUnionWitness` for `S ∪ {z}`, at least one witness set has an element outside `insert z S`. -/
theorem nonempty_A_sdiff_insert_or_B_sdiff_insert_of_blockedUnionWitness
    {S : Finset α} {z : α} (wz : BlockedUnionWitness family S z) :
    (wz.A \ insert z S).Nonempty ∨ (wz.B \ insert z S).Nonempty := by
  classical
  by_contra h
  have hAne : ¬ (wz.A \ insert z S).Nonempty := (not_or.mp h).1
  have hBne : ¬ (wz.B \ insert z S).Nonempty := (not_or.mp h).2
  have hAeq : wz.A \ insert z S = (∅ : Finset α) := by
    simpa [Finset.not_nonempty_iff_eq_empty] using hAne
  have hBeq : wz.B \ insert z S = (∅ : Finset α) := by
    simpa [Finset.not_nonempty_iff_eq_empty] using hBne
  have hAsub : wz.A ⊆ insert z S := by
    intro a ha
    by_contra hnot
    have : a ∈ wz.A \ insert z S := Finset.mem_sdiff.mpr ⟨ha, hnot⟩
    have : a ∈ (∅ : Finset α) := by simpa [hAeq] using this
    exact (Finset.notMem_empty a this)
  have hBsub : wz.B ⊆ insert z S := by
    intro a ha
    by_contra hnot
    have : a ∈ wz.B \ insert z S := Finset.mem_sdiff.mpr ⟨ha, hnot⟩
    have : a ∈ (∅ : Finset α) := by simpa [hBeq] using this
    exact (Finset.notMem_empty a this)
  have hAsub' : wz.A ⊆ S ∪ ({z} : Finset α) := by
    intro a ha
    have haIns : a ∈ insert z S := hAsub ha
    simpa [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using haIns
  have hBsub' : wz.B ⊆ S ∪ ({z} : Finset α) := by
    intro a ha
    have haIns : a ∈ insert z S := hBsub ha
    simpa [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using haIns
  have hAinter : wz.A ∩ (S ∪ ({z} : Finset α)) = wz.A := by
    ext a
    constructor
    · intro ha
      exact (Finset.mem_inter.mp ha).1
    · intro ha
      exact Finset.mem_inter.mpr ⟨ha, hAsub' ha⟩
  have hBinter : wz.B ∩ (S ∪ ({z} : Finset α)) = wz.B := by
    ext a
    constructor
    · intro ha
      exact (Finset.mem_inter.mp ha).1
    · intro ha
      exact Finset.mem_inter.mpr ⟨ha, hBsub' ha⟩
  have hAcore : wz.A = wz.core := by
    calc
      wz.A = wz.A ∩ (S ∪ ({z} : Finset α)) := hAinter.symm
      _ = wz.core := by simpa using wz.hcoreAT
  have hBcore : wz.B = wz.core := by
    calc
      wz.B = wz.B ∩ (S ∪ ({z} : Finset α)) := hBinter.symm
      _ = wz.core := by simpa using wz.hcoreBT
  apply wz.hneAB
  simpa [hAcore, hBcore]

/--
Choose a normalized blocked-union witness for `S ∪ {z}` in the hard-branch reduction,
and (if needed) swap it so that the A-side has some element outside `insert z S`.

This is a local selection refinement used to avoid the `uFromZWitness = none` contract gap.
-/
noncomputable def chooseBlockedUnionWitnessNormGoodU_of_hNotMem_reduction
    (hreg : O1aUpgradeRegime family ground A0 h0)
    {k : WLcertKey α} {S : Finset α}
    (hSdom : S ∈ o1aWitnessLiftDomWL family h0)
    (hcert : ∃ cert : WLcert family S, WLcert.key cert = k ∧ cert.h ∉ S)
    {z : α} (hzX : z ∈ (ground \ (k.2.2.1 ∪ k.2.2.2.1))) (hzNot : z ∉ S) (hz0 : z ≠ h0) :
    BlockedUnionWitness family S z := by
  classical
  let wz0 :=
    chooseBlockedUnionWitnessNorm_of_hNotMem_reduction
      (family := family) (ground := ground) (A0 := A0) (h0 := h0)
      hreg (k := k) (S := S) hSdom hcert (y := z) hzX hzNot hz0
  by_cases hA : (wz0.A \ insert z S).Nonempty
  · exact wz0
  · exact BlockedUnionWitness.swap (family := family) (S := S) (x := z) wz0

theorem A_sdiff_insert_nonempty_of_chooseBlockedUnionWitnessNormGoodU_of_hNotMem_reduction
    (hreg : O1aUpgradeRegime family ground A0 h0)
    {k : WLcertKey α} {S : Finset α}
    (hSdom : S ∈ o1aWitnessLiftDomWL family h0)
    (hcert : ∃ cert : WLcert family S, WLcert.key cert = k ∧ cert.h ∉ S)
    {z : α} (hzX : z ∈ (ground \ (k.2.2.1 ∪ k.2.2.2.1))) (hzNot : z ∉ S) (hz0 : z ≠ h0) :
    (((chooseBlockedUnionWitnessNormGoodU_of_hNotMem_reduction
          (family := family) (ground := ground) (A0 := A0) (h0 := h0)
          hreg (k := k) (S := S) hSdom hcert (z := z) hzX hzNot hz0).A \ insert z S).Nonempty) := by
  classical
  unfold chooseBlockedUnionWitnessNormGoodU_of_hNotMem_reduction
  set wz0 :=
    chooseBlockedUnionWitnessNorm_of_hNotMem_reduction
      (family := family) (ground := ground) (A0 := A0) (h0 := h0)
      hreg (k := k) (S := S) hSdom hcert (y := z) hzX hzNot hz0
    with hwz0
  by_cases hA : (wz0.A \ insert z S).Nonempty
  · simpa [hA]
  · have hAt : ¬ (wz0.A \ insert z S).Nonempty := hA
    have hBor :
        (wz0.B \ insert z S).Nonempty := by
      have hor :=
        nonempty_A_sdiff_insert_or_B_sdiff_insert_of_blockedUnionWitness
          (family := family) (S := S) (z := z) wz0
      rcases hor with hA' | hB'
      · exact False.elim (hAt hA')
      · exact hB'
    -- In this branch the chooser returns `swap`, so `A = wz0.B`.
    simpa [hA, BlockedUnionWitness.swap] using hBor

theorem core_erase_eq_empty_of_uFromZWitness_eq_none
    {S : Finset α} {z : α} (wz : BlockedUnionWitness family S z)
    (hu : uFromZWitness (family := family) (S := S) (z := z) wz = none) :
    wz.core.erase z = (∅ : Finset α) := by
  classical
  unfold uFromZWitness at hu
  by_cases hcore : (wz.core.erase z).Nonempty
  · -- Contradiction: the definition would return `some _`.
    simp [hcore] at hu
  · -- `¬ Nonempty` iff empty.
    simpa [Finset.not_nonempty_iff_eq_empty] using hcore

theorem tx2PlusOfWitness_eq_none_of_uFromZWitness_eq_none
    {S : Finset α} {z : α} (wz : BlockedUnionWitness family S z)
    (hu : uFromZWitness (family := family) (S := S) (z := z) wz = none) :
    tx2PlusOfWitness (family := family) (S := S) (x := z) wz = none := by
  classical
  by_cases hcore : (wz.core.erase z).Nonempty
  · -- Contradiction: `uFromZWitness` returns `some _` in the core-nonempty branch.
    have huContr : (some (Classical.choose hcore) : Option α) = none := by
      simpa [uFromZWitness, hcore] using hu
    cases huContr
  · -- In the `¬Nonempty` branch, the result is determined by `tx2PlusOfWitness`.
    cases htx : tx2PlusOfWitness (family := family) (S := S) (x := z) wz with
    | none => rfl
    | some triple =>
        -- Contradiction: the definition would return `some triple.1`.
        have huContr : (some triple.1 : Option α) = none := by
          have : uFromZWitness (family := family) (S := S) (z := z) wz = some triple.1 := by
            simp [uFromZWitness, hcore, htx]
          simpa [this] using hu
        cases huContr

theorem A_sdiff_insert_eq_empty_of_uFromZWitness_eq_none
    {S : Finset α} {z : α} (wz : BlockedUnionWitness family S z)
    (hu : uFromZWitness (family := family) (S := S) (z := z) wz = none) :
    wz.A \ insert z S = (∅ : Finset α) := by
  have htx :
      tx2PlusOfWitness (family := family) (S := S) (x := z) wz = none :=
    tx2PlusOfWitness_eq_none_of_uFromZWitness_eq_none (family := family) (S := S) (z := z) wz hu
  simpa using
    (eq_empty_of_tx2PlusOfWitness_eq_none (family := family) (S := S) (x := z) wz htx)

theorem uFromZWitness_ne_none_of_A_sdiff_insert_nonempty
    {S : Finset α} {z : α} (wz : BlockedUnionWitness family S z)
    (hA : (wz.A \ insert z S).Nonempty) :
    uFromZWitness (family := family) (S := S) (z := z) wz ≠ none := by
  classical
  intro hu
  have hAempty :
      wz.A \ insert z S = (∅ : Finset α) :=
    A_sdiff_insert_eq_empty_of_uFromZWitness_eq_none (family := family) (S := S) (z := z) wz hu
  have hnot : ¬ (wz.A \ insert z S).Nonempty :=
    (Finset.not_nonempty_iff_eq_empty).mpr hAempty
  exact hnot hA

theorem uFromZWitness_ne_none_of_chooseBlockedUnionWitnessNormGoodU_of_hNotMem_reduction
    (hreg : O1aUpgradeRegime family ground A0 h0)
    {k : WLcertKey α} {S : Finset α}
    (hSdom : S ∈ o1aWitnessLiftDomWL family h0)
    (hcert : ∃ cert : WLcert family S, WLcert.key cert = k ∧ cert.h ∉ S)
    {z : α} (hzX : z ∈ (ground \ (k.2.2.1 ∪ k.2.2.2.1))) (hzNot : z ∉ S) (hz0 : z ≠ h0) :
    uFromZWitness (family := family) (S := S) (z := z)
        (chooseBlockedUnionWitnessNormGoodU_of_hNotMem_reduction
          (family := family) (ground := ground) (A0 := A0) (h0 := h0)
          hreg (k := k) (S := S) hSdom hcert (z := z) hzX hzNot hz0) ≠ none := by
  classical
  let wz :=
    chooseBlockedUnionWitnessNormGoodU_of_hNotMem_reduction
      (family := family) (ground := ground) (A0 := A0) (h0 := h0)
      hreg (k := k) (S := S) hSdom hcert (z := z) hzX hzNot hz0
  have hA : (wz.A \ insert z S).Nonempty := by
    simpa [wz] using
      (A_sdiff_insert_nonempty_of_chooseBlockedUnionWitnessNormGoodU_of_hNotMem_reduction
        (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg (k := k) (S := S) hSdom hcert (z := z) hzX hzNot hz0)
  simpa [wz] using
    (uFromZWitness_ne_none_of_A_sdiff_insert_nonempty (family := family) (S := S) (z := z) wz hA)

theorem uFromZWitness_mem_optionOfFinset_of_A_subset_ground
    (ground : Finset α) {S : Finset α} {z : α} (wz : BlockedUnionWitness family S z)
    (hAground : wz.A ⊆ ground) :
    uFromZWitness (family := family) (S := S) (z := z) wz ∈ optionOfFinset (α := α) ground := by
  classical
  cases hu : uFromZWitness (family := family) (S := S) (z := z) wz with
  | none =>
      simp [optionOfFinset, hu]
  | some u =>
      have huA : u ∈ wz.A := by
        unfold uFromZWitness at hu
        by_cases hcore : (wz.core.erase z).Nonempty
        · have : (some (Classical.choose hcore) : Option α) = some u := by
            simpa [hcore] using hu
          have huEq : Classical.choose hcore = u := Option.some.inj this
          subst huEq
          have huMemErase : Classical.choose hcore ∈ wz.core.erase z := Classical.choose_spec hcore
          have huMemCore : Classical.choose hcore ∈ wz.core :=
            (Finset.mem_erase.mp huMemErase).2
          have huMemInter : Classical.choose hcore ∈ wz.A ∩ wz.B := by
            simpa [wz.hcoreAB.symm] using huMemCore
          exact (Finset.mem_inter.mp huMemInter).1
        · cases htx : tx2PlusOfWitness (family := family) (S := S) (x := z) wz with
          | none =>
              -- Contradiction: would force `uFromZWitness = none`.
              have : (none : Option α) = some u := by
                simpa [uFromZWitness, hcore, htx] using hu
              cases this
          | some triple =>
              have : (some triple.1 : Option α) = some u := by
                simpa [uFromZWitness, hcore, htx] using hu
              have huEq : triple.1 = u := Option.some.inj this
              subst huEq
              have huMem : triple.1 ∈ wz.A \ insert z S :=
                mem_extras_of_tx2PlusOfWitness_eq_some (family := family) (S := S) (x := z) wz
                  (triple := triple) htx
              exact (Finset.mem_sdiff.mp huMem).1
      have huG : u ∈ ground := hAground huA
      simp [optionOfFinset, hu, huG]

theorem core_eq_singleton_of_core_erase_eq_empty_of_tag_mem_core
    {S : Finset α} {z : α} (wz : BlockedUnionWitness family S z)
    (hcore : wz.core.erase z = (∅ : Finset α))
    (hz : z ∈ wz.core) :
    wz.core = ({z} : Finset α) := by
  classical
  have hsub : wz.core ⊆ ({z} : Finset α) := by
    intro a ha
    by_cases haz : a = z
    · simpa [haz]
    · have : a ∈ wz.core.erase z := Finset.mem_erase.mpr ⟨haz, ha⟩
      have : a ∈ (∅ : Finset α) := by simpa [hcore] using this
      exact False.elim (Finset.notMem_empty a this)
  have hz' : z ∈ ({z} : Finset α) := by simp
  exact Finset.Subset.antisymm hsub (by
    intro a ha
    have haz : a = z := by simpa using (Finset.mem_singleton.mp ha)
    simpa [haz] using hz)

/-- Per-`x` subfiber signature for a completion `S` and a chosen missing `y`. -/
abbrev PerXSignature (α : Type*) :=
  α × Option (α × Option α × Bool) × Option (α × Option α × Bool) ×
    Option (α × Option α × Bool) × Option (α × Option α × Bool) ×
      Option (α × Option α × Bool)

section PerXSignatureRange

variable {α : Type*} [DecidableEq α]

def boolFin : Finset Bool := ({false, true} : Finset Bool)

noncomputable instance instDecidableEqPerXSignature : DecidableEq (PerXSignature α) := by
  classical
  exact Classical.decEq _

def traceCod (ground : Finset α) : Finset (Option (α × Option α × Bool)) :=
  optionOfFinset (α := α × Option α × Bool)
    (ground.product ((optionOfFinset (α := α) ground).product boolFin))

theorem mem_traceCod_of_trace2PlusOfFinset_of_subset {T ground : Finset α}
    (hT : T ⊆ ground) :
    trace2PlusOfFinset (α := α) T ∈ traceCod (α := α) ground := by
  classical
  cases ht : trace2PlusOfFinset (α := α) T with
  | none =>
      -- `none` is always in `optionOfFinset _`.
      simp [traceCod, optionOfFinset, ht]
  | some triple =>
      rcases triple with ⟨t1, ot2, b⟩
      have htT1 : t1 ∈ T :=
        mem_left_of_trace2PlusOfFinset_eq_some (α := α) (T := T) (t1 := t1) (ot2 := ot2)
          (b := b) (by simpa [ht])
      have ht1 : t1 ∈ ground := hT htT1
      have hb : b ∈ boolFin := by simp [boolFin]
      have hot2 : ot2 ∈ optionOfFinset (α := α) ground := by
        cases ot2 with
        | none =>
            simp [optionOfFinset]
        | some t2 =>
            have htT2 : t2 ∈ T :=
              mem_right_of_trace2PlusOfFinset_eq_some_some (α := α) (T := T) (t1 := t1)
                (t2 := t2) (b := b) (by simpa [ht])
            have ht2 : t2 ∈ ground := hT htT2
            simp [optionOfFinset, ht2]
      have hPair2 :
          (ot2, b) ∈ (optionOfFinset (α := α) ground).product boolFin :=
        Finset.mem_product.mpr ⟨hot2, hb⟩
      have hPair1 :
          (t1, (ot2, b)) ∈
            ground.product ((optionOfFinset (α := α) ground).product boolFin) :=
        Finset.mem_product.mpr ⟨ht1, hPair2⟩
      have hmem :
          (t1, ot2, b) ∈
            ground.product ((optionOfFinset (α := α) ground).product boolFin) := by
        simpa using hPair1
      -- Lift to membership in `traceCod`.
      refine Finset.mem_insert_of_mem ?_
      refine Finset.mem_image.mpr ?_
      exact ⟨(t1, ot2, b), hmem, rfl⟩

theorem card_traceCod_le (ground : Finset α) :
    (traceCod (α := α) ground).card ≤ 2 * ground.card * (ground.card + 1) + 1 := by
  classical
  -- Unfold and bound by `card_optionOfFinset_le_succ`.
  have hopt : (optionOfFinset (α := α) ground).card ≤ ground.card + 1 :=
    card_optionOfFinset_le_succ (α := α) ground
  have hbool : boolFin.card = 2 := by simp [boolFin]
  have hprod :
      (ground.product
            ((optionOfFinset (α := α) ground).product boolFin)).card ≤
        ground.card * (ground.card + 1) * 2 := by
    -- `card(product) = card * card`, then apply bounds.
    have :
        (ground.product ((optionOfFinset (α := α) ground).product boolFin)).card =
          ground.card * ((optionOfFinset (α := α) ground).product boolFin).card := by
      simp [Finset.card_product, Nat.mul_assoc]
    calc
      (ground.product
            ((optionOfFinset (α := α) ground).product boolFin)).card
          = ground.card *
              ((optionOfFinset (α := α) ground).product boolFin).card := this
      _ = ground.card * ((optionOfFinset (α := α) ground).card * boolFin.card) := by
            simp [Finset.card_product, Nat.mul_assoc]
      _ ≤ ground.card * ((ground.card + 1) * boolFin.card) := by
            gcongr
      _ = ground.card * (ground.card + 1) * 2 := by
            simp [hbool, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  -- Apply `card_optionOfFinset_le_succ` to the triple product finset.
  have htrace :
      (traceCod (α := α) ground).card ≤
        (ground.product
              ((optionOfFinset (α := α) ground).product boolFin)).card + 1 := by
    simpa [traceCod] using
      (card_optionOfFinset_le_succ (α := α × Option α × Bool)
        (ground.product
          ((optionOfFinset (α := α) ground).product boolFin)))
  calc
    (traceCod (α := α) ground).card
        ≤ (ground.product
              ((optionOfFinset (α := α) ground).product boolFin)).card + 1 := htrace
    _ ≤ (ground.card * (ground.card + 1) * 2) + 1 := by
          exact Nat.add_le_add_right hprod 1
    _ = 2 * ground.card * (ground.card + 1) + 1 := by
          ring

theorem card_image_sig0_le_card_traceCod_pow_five
    {β : Type*} [DecidableEq β]
    (Fx : Finset β) (ground : Finset α) (sig0 : β → PerXSignature α)
    (hy : ∀ b ∈ Fx, (sig0 b).1 ∈ ground)
    (htr :
      ∀ b ∈ Fx,
        (sig0 b).2.1 ∈ traceCod (α := α) ground ∧
          (sig0 b).2.2.1 ∈ traceCod (α := α) ground ∧
            (sig0 b).2.2.2.1 ∈ traceCod (α := α) ground ∧
              (sig0 b).2.2.2.2.1 ∈ traceCod (α := α) ground ∧
                (sig0 b).2.2.2.2.2 ∈ traceCod (α := α) ground) :
    (Fx.image sig0).card ≤ ground.card * (traceCod (α := α) ground).card ^ 5 := by
  classical
  let sig0Image : Finset (PerXSignature α) := Fx.image sig0
  let T : Finset (Option (α × Option α × Bool)) := traceCod (α := α) ground
  let Tail : Finset
      (Option (α × Option α × Bool) ×
        Option (α × Option α × Bool) ×
          Option (α × Option α × Bool) ×
            Option (α × Option α × Bool) ×
              Option (α × Option α × Bool)) :=
    T.product (T.product (T.product (T.product T)))
  let Cod : Finset (PerXSignature α) := ground.product Tail
  have hsub : sig0Image ⊆ Cod := by
    intro σ hσ
    rcases Finset.mem_image.mp (by simpa [sig0Image] using hσ) with ⟨b, hbFx, rfl⟩
    have hyb : (sig0 b).1 ∈ ground := hy b hbFx
    have htrb := htr b hbFx
    have ht1 : (sig0 b).2.1 ∈ T := htrb.1
    have ht2 : (sig0 b).2.2.1 ∈ T := htrb.2.1
    have ht3 : (sig0 b).2.2.2.1 ∈ T := htrb.2.2.1
    have ht4 : (sig0 b).2.2.2.2.1 ∈ T := htrb.2.2.2.1
    have ht5 : (sig0 b).2.2.2.2.2 ∈ T := htrb.2.2.2.2
    -- Build membership in the nested product `Tail`.
    have htail :
        (sig0 b).2 ∈ Tail := by
      -- `Tail = T × (T × (T × (T × T)))`.
      refine Finset.mem_product.mpr ?_
      refine ⟨ht1, ?_⟩
      refine Finset.mem_product.mpr ?_
      refine ⟨ht2, ?_⟩
      refine Finset.mem_product.mpr ?_
      refine ⟨ht3, ?_⟩
      refine Finset.mem_product.mpr ?_
      exact ⟨ht4, ht5⟩
    -- Combine head and tail.
    exact Finset.mem_product.mpr ⟨hyb, htail⟩
  have hcard : sig0Image.card ≤ Cod.card := Finset.card_le_card hsub
  have hTail : Tail.card = T.card ^ 5 := by
    simp [Tail, Finset.card_product, pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have hCod : Cod.card = ground.card * T.card ^ 5 := by
    simp [Cod, Finset.card_product, hTail, Nat.mul_assoc]
  calc
    sig0Image.card ≤ Cod.card := hcard
    _ = ground.card * T.card ^ 5 := hCod
    _ = ground.card * (traceCod (α := α) ground).card ^ 5 := by simp [T]

end PerXSignatureRange

noncomputable def perXSignature (k : WLcertKey α) (S : Finset α) (y : α)
    (w : BlockedUnionWitness family S y) : PerXSignature α :=
  (y,
    rABTrace (family := family) (k := k) (S := S) (y := y) w,
    tx2PlusOfWitness (family := family) (S := S) (x := y) w,
    trace2PlusOfFinset (α := α) (w.core.erase y),
    bTrace (family := family) (S := S) (y := y) w,
    outsideTrace (family := family) (S := S) (y := y) w)

/-- Per-`x` signature for a hard-branch completion `S` using the canonical `y(S)` and normalized witness. -/
noncomputable def perXSignature_of_hardFiber
    (hreg : O1aUpgradeRegime family ground A0 h0)
    {k : WLcertKey α} {Sstar Ssub : Finset α}
    (hSstarDom : Sstar ∈ o1aWitnessLiftDomWL family h0)
    (hSsubDom : Ssub ∈ o1aWitnessLiftDomWL family h0)
    (hcert_star : ∃ cert : WLcert family Sstar, WLcert.key cert = k ∧ cert.h ∉ Sstar)
    (hcert_sub : ∃ cert : WLcert family Ssub, WLcert.key cert = k ∧ cert.h ∉ Ssub)
    (hne : Ssub ≠ Sstar) : PerXSignature α := by
  classical
  let yw :
      Σ y : α, BlockedUnionWitness family Ssub y :=
    chooseYAndWitness_of_hardFiber (family := family) (ground := ground) (A0 := A0) (h0 := h0)
      hreg (k := k) (Sstar := Sstar) (Ssub := Ssub) hSstarDom hSsubDom hcert_star hcert_sub hne
  exact perXSignature (family := family) (k := k) (S := Ssub) (y := yw.1) yw.2

/-
Bucket plumbing: partition a finite set `Fx` by a signature map `sig`.

We keep this generic and lightweight: the per-`x` proofs will instantiate it with
`sig := perXSignature_of_hardFiber …`.
-/

section BucketPlumbing

variable {β γ : Type*} [DecidableEq β] [DecidableEq γ]

noncomputable def Bucket (Fx : Finset β) (sig : β → γ) (σ : γ) : Finset β :=
  Fx.filter (fun b => sig b = σ)

theorem mem_Bucket {Fx : Finset β} {sig : β → γ} {σ : γ} {b : β} :
    b ∈ Bucket (Fx := Fx) sig σ ↔ b ∈ Fx ∧ sig b = σ := by
  simp [Bucket]

theorem Bucket_subset {Fx : Finset β} {sig : β → γ} {σ : γ} :
    Bucket (Fx := Fx) sig σ ⊆ Fx := by
  intro b hb
  exact ((mem_Bucket (Fx := Fx) (sig := sig) (σ := σ) (b := b)).1 hb).1

theorem Fx_eq_biUnion_Bucket (Fx : Finset β) (sig : β → γ) :
    Fx = (Fx.image sig).biUnion (fun σ => Bucket (Fx := Fx) sig σ) := by
  classical
  ext b
  constructor
  · intro hb
    refine Finset.mem_biUnion.mpr ?_
    refine ⟨sig b, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
    · exact Finset.mem_filter.mpr ⟨hb, rfl⟩
  · intro hb
    rcases Finset.mem_biUnion.mp hb with ⟨σ, _hσ, hbσ⟩
    exact (Finset.mem_filter.mp hbσ).1

theorem card_Fx_eq_sum_card_Bucket (Fx : Finset β) (sig : β → γ) :
    Fx.card = ∑ σ ∈ Fx.image sig, (Bucket (Fx := Fx) sig σ).card := by
  classical
  -- This is exactly `card_eq_sum_card_image` in fiber-counting form.
  simpa [Bucket] using (Finset.card_eq_sum_card_image (f := sig) (s := Fx))

end BucketPlumbing

theorem rAB_eq_A_inter_keyBase
    {k : WLcertKey α} {S : Finset α} {y : α} (w : BlockedUnionWitness family S y)
    (hAB : S ∩ (k.2.2.1 ∪ k.2.2.2.1) = keyBase (k := k))
    (hyNot : y ∉ S) :
    rAB (family := family) (k := k) (S := S) (y := y) w =
      w.A ∩ keyBase (k := k) := by
  classical
  have hAS : w.A ∩ S = w.core.erase y :=
    inter_left_eq_core_erase_of_blockedUnionWitness_of_mem_core_of_not_mem_S
      (family := family) (S := S) (x := y) w hyNot
  -- Unfold `rAB` and rewrite using the fixed trace of `S` on `kA ∪ kB`.
  ext z
  constructor
  · intro hz
    have hz' : z ∈ w.core.erase y ∧ z ∈ (k.2.2.1 ∪ k.2.2.2.1) := by
      simpa [rAB] using (Finset.mem_inter.mp hz)
    have hzAS : z ∈ w.A ∩ S := by
      simpa [hAS] using hz'.1
    have hzBase : z ∈ keyBase (k := k) := by
      have : z ∈ S ∩ (k.2.2.1 ∪ k.2.2.2.1) := by
        exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hzAS).2, hz'.2⟩
      simpa [hAB] using this
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hzAS).1, hzBase⟩
  · intro hz
    have hzA : z ∈ w.A := (Finset.mem_inter.mp hz).1
    have hzBase : z ∈ keyBase (k := k) := (Finset.mem_inter.mp hz).2
    have hzSAB : z ∈ S ∩ (k.2.2.1 ∪ k.2.2.2.1) := by
      have : z ∈ S ∩ (k.2.2.1 ∪ k.2.2.2.1) := by
        -- Use `hAB` to move from `keyBase` back to `S ∩ (kA ∪ kB)`.
        simpa [hAB] using hzBase
      exact this
    have hzS : z ∈ S := (Finset.mem_inter.mp hzSAB).1
    have hzAB : z ∈ (k.2.2.1 ∪ k.2.2.2.1) := (Finset.mem_inter.mp hzSAB).2
    have hzAS : z ∈ w.A ∩ S := Finset.mem_inter.mpr ⟨hzA, hzS⟩
    have hzCoreErase : z ∈ w.core.erase y := by
      simpa [hAS] using hzAS
    exact Finset.mem_inter.mpr ⟨hzCoreErase, hzAB⟩

theorem A_inter_keyBase_subset_pair_of_rABTrace_eq_some_some_false
    {k : WLcertKey α} {S : Finset α} {y : α} (w : BlockedUnionWitness family S y)
    (hAB : S ∩ (k.2.2.1 ∪ k.2.2.2.1) = keyBase (k := k)) (hyNot : y ∉ S)
    {t1 t2 : α}
    (ht : rABTrace (family := family) (k := k) (S := S) (y := y) w =
        some (t1, some t2, false)) :
    w.A ∩ keyBase (k := k) ⊆ ({t1, t2} : Finset α) := by
  classical
  have hsub : rAB (family := family) (k := k) (S := S) (y := y) w ⊆ ({t1, t2} : Finset α) := by
    have : trace2PlusOfFinset (α := α)
          (rAB (family := family) (k := k) (S := S) (y := y) w) =
        some (t1, some t2, false) := by
      simpa [rABTrace] using ht
    exact subset_pair_of_trace2PlusOfFinset_eq_some_some_false (α := α) this
  -- Rewrite `rAB` as `w.A ∩ keyBase`.
  simpa [rAB_eq_A_inter_keyBase (family := family) (k := k) (S := S) (y := y) w hAB hyNot] using hsub

theorem A_inter_keyBase_subset_singleton_of_rABTrace_eq_some_none_false
    {k : WLcertKey α} {S : Finset α} {y : α} (w : BlockedUnionWitness family S y)
    (hAB : S ∩ (k.2.2.1 ∪ k.2.2.2.1) = keyBase (k := k)) (hyNot : y ∉ S)
    {t1 : α}
    (ht : rABTrace (family := family) (k := k) (S := S) (y := y) w =
        some (t1, (none : Option α), false)) :
    w.A ∩ keyBase (k := k) ⊆ ({t1} : Finset α) := by
  classical
  have hsub : rAB (family := family) (k := k) (S := S) (y := y) w ⊆ ({t1} : Finset α) := by
    have : trace2PlusOfFinset (α := α)
          (rAB (family := family) (k := k) (S := S) (y := y) w) =
        some (t1, (none : Option α), false) := by
      simpa [rABTrace] using ht
    exact subset_singleton_of_trace2PlusOfFinset_eq_some_none_false (α := α) this
  simpa [rAB_eq_A_inter_keyBase (family := family) (k := k) (S := S) (y := y) w hAB hyNot] using hsub

theorem coreErase_subset_pair_of_coreTrace_eq_some_some_false
    {S : Finset α} {y : α} (w : BlockedUnionWitness family S y) {t1 t2 : α}
    (ht : trace2PlusOfFinset (α := α) (w.core.erase y) = some (t1, some t2, false)) :
    w.core.erase y ⊆ ({t1, t2} : Finset α) :=
  subset_pair_of_trace2PlusOfFinset_eq_some_some_false (α := α) ht

theorem coreErase_subset_singleton_of_coreTrace_eq_some_none_false
    {S : Finset α} {y : α} (w : BlockedUnionWitness family S y) {t1 : α}
    (ht : trace2PlusOfFinset (α := α) (w.core.erase y) =
        some (t1, (none : Option α), false)) :
    w.core.erase y ⊆ ({t1} : Finset α) :=
  subset_singleton_of_trace2PlusOfFinset_eq_some_none_false (α := α) ht

theorem B_sdiff_insert_eq_empty_of_bTrace_eq_none
    {S : Finset α} {y : α} (w : BlockedUnionWitness family S y)
    (ht : bTrace (family := family) (S := S) (y := y) w = none) :
    w.B \ insert y S = (∅ : Finset α) := by
  classical
  have : trace2PlusOfFinset (α := α) (w.B \ insert y S) = none := by
    simpa [bTrace] using ht
  exact eq_empty_of_trace2PlusOfFinset_eq_none (α := α) this

theorem B_sdiff_insert_eq_singleton_of_bTrace_eq_some_none_false
    {S : Finset α} {y : α} (w : BlockedUnionWitness family S y) {t1 : α}
    (ht : bTrace (family := family) (S := S) (y := y) w =
        some (t1, (none : Option α), false)) :
    w.B \ insert y S = ({t1} : Finset α) := by
  classical
  have : trace2PlusOfFinset (α := α) (w.B \ insert y S) =
        some (t1, (none : Option α), false) := by
    simpa [bTrace] using ht
  exact eq_singleton_of_trace2PlusOfFinset_eq_some_none_false (α := α) this

theorem B_sdiff_insert_eq_pair_of_bTrace_eq_some_some_false
    {S : Finset α} {y : α} (w : BlockedUnionWitness family S y) {t1 t2 : α}
    (ht : bTrace (family := family) (S := S) (y := y) w =
        some (t1, (some t2 : Option α), false)) :
    w.B \ insert y S = ({t1, t2} : Finset α) := by
  classical
  have : trace2PlusOfFinset (α := α) (w.B \ insert y S) =
        some (t1, some t2, false) := by
    simpa [bTrace] using ht
  exact eq_pair_of_trace2PlusOfFinset_eq_some_some_false (α := α) this

theorem S_sdiff_union_eq_empty_of_outsideTrace_eq_none
    {S : Finset α} {y : α} (w : BlockedUnionWitness family S y)
    (ht : outsideTrace (family := family) (S := S) (y := y) w = none) :
    S \ (w.A ∪ w.B) = (∅ : Finset α) := by
  classical
  have : trace2PlusOfFinset (α := α) (S \ (w.A ∪ w.B)) = none := by
    simpa [outsideTrace] using ht
  exact eq_empty_of_trace2PlusOfFinset_eq_none (α := α) this

theorem S_sdiff_union_eq_singleton_of_outsideTrace_eq_some_none_false
    {S : Finset α} {y : α} (w : BlockedUnionWitness family S y) {t1 : α}
    (ht : outsideTrace (family := family) (S := S) (y := y) w =
        some (t1, (none : Option α), false)) :
    S \ (w.A ∪ w.B) = ({t1} : Finset α) := by
  classical
  have : trace2PlusOfFinset (α := α) (S \ (w.A ∪ w.B)) =
        some (t1, (none : Option α), false) := by
    simpa [outsideTrace] using ht
  exact eq_singleton_of_trace2PlusOfFinset_eq_some_none_false (α := α) this

theorem S_sdiff_union_eq_pair_of_outsideTrace_eq_some_some_false
    {S : Finset α} {y : α} (w : BlockedUnionWitness family S y) {t1 t2 : α}
    (ht : outsideTrace (family := family) (S := S) (y := y) w =
        some (t1, (some t2 : Option α), false)) :
    S \ (w.A ∪ w.B) = ({t1, t2} : Finset α) := by
  classical
  have : trace2PlusOfFinset (α := α) (S \ (w.A ∪ w.B)) =
        some (t1, some t2, false) := by
    simpa [outsideTrace] using ht
  exact eq_pair_of_trace2PlusOfFinset_eq_some_some_false (α := α) this

theorem mem_left_of_mem_core {S : Finset α} {y : α} (w : BlockedUnionWitness family S y)
    (hy : y ∈ w.core) :
    y ∈ w.A := by
  classical
  have hyAT : y ∈ w.A ∩ (S ∪ ({y} : Finset α)) := by
    -- rewrite membership along `w.hcoreAT` in reverse
    have hy' : y ∈ w.core := hy
    have hy'' := hy'
    rw [← w.hcoreAT] at hy''
    exact hy''
  exact (Finset.mem_inter.mp hyAT).1

theorem mem_right_of_mem_core {S : Finset α} {y : α} (w : BlockedUnionWitness family S y)
    (hy : y ∈ w.core) :
    y ∈ w.B := by
  classical
  have hyBT : y ∈ w.B ∩ (S ∪ ({y} : Finset α)) := by
    have hy' : y ∈ w.core := hy
    have hy'' := hy'
    rw [← w.hcoreBT] at hy''
    exact hy''
  exact (Finset.mem_inter.mp hyBT).1

theorem B_eq_S_of_not_mem_core_of_A_ne_S {S : Finset α} {y : α} (w : BlockedUnionWitness family S y)
    (hAne : w.A ≠ S) (hy : y ∉ w.core) :
    w.B = S := by
  rcases w.htag with hy' | hAeq | hBeq
  · exact False.elim (hy hy')
  · exact False.elim (hAne hAeq)
  · exact hBeq

theorem A_eq_core_union_sdiff_insert {S : Finset α} {y : α} (w : BlockedUnionWitness family S y) :
    w.A = w.core ∪ (w.A \ insert y S) := by
  classical
  -- Decompose `w.A` into the part inside `insert y S` (which is exactly `core`) and the rest.
  have hdecomp : w.A = (w.A ∩ insert y S) ∪ (w.A \ insert y S) := by
    ext z
    constructor
    · intro hz
      by_cases hzT : z ∈ insert y S
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hz, hzT⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hz, hzT⟩))
    · intro hz
      rcases Finset.mem_union.mp hz with hz | hz
      · exact (Finset.mem_inter.mp hz).1
      · exact (Finset.mem_sdiff.mp hz).1
  -- Rewrite `w.A ∩ insert y S` using the witness core equality.
  have hcore : w.A ∩ insert y S = w.core := by
    simpa [Finset.union_singleton] using w.hcoreAT
  calc
    w.A = (w.A ∩ insert y S) ∪ (w.A \ insert y S) := hdecomp
    _ = w.core ∪ (w.A \ insert y S) := by simpa [hcore]

theorem B_eq_core_union_sdiff_insert {S : Finset α} {y : α} (w : BlockedUnionWitness family S y) :
    w.B = w.core ∪ (w.B \ insert y S) := by
  classical
  have hdecomp : w.B = (w.B ∩ insert y S) ∪ (w.B \ insert y S) := by
    ext z
    constructor
    · intro hz
      by_cases hzT : z ∈ insert y S
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hz, hzT⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hz, hzT⟩))
    · intro hz
      rcases Finset.mem_union.mp hz with hz | hz
      · exact (Finset.mem_inter.mp hz).1
      · exact (Finset.mem_sdiff.mp hz).1
  have hcore : w.B ∩ insert y S = w.core := by
    simpa [Finset.union_singleton] using w.hcoreBT
  calc
    w.B = (w.B ∩ insert y S) ∪ (w.B \ insert y S) := hdecomp
    _ = w.core ∪ (w.B \ insert y S) := by simpa [hcore]

theorem S_eq_coreErase_union_sdiff_union_of_blockedUnionWitness
    {S : Finset α} {y : α} (w : BlockedUnionWitness family S y) (hyNot : y ∉ S) :
    S = (w.core.erase y) ∪ (S \ (w.A ∪ w.B)) := by
  classical
  -- First, identify `S ∩ (w.A ∪ w.B)` as `w.core.erase y`.
  have hAS : w.A ∩ S = w.core.erase y :=
    inter_left_eq_core_erase_of_blockedUnionWitness_of_mem_core_of_not_mem_S
      (family := family) (S := S) (x := y) w hyNot
  have hBS : w.B ∩ S = w.core.erase y :=
    inter_right_eq_core_erase_of_blockedUnionWitness_of_mem_core_of_not_mem_S
      (family := family) (S := S) (x := y) w hyNot
  have hSAB : S ∩ (w.A ∪ w.B) = w.core.erase y := by
    ext z
    constructor
    · intro hz
      have hzS : z ∈ S := (Finset.mem_inter.mp hz).1
      have hzAB : z ∈ w.A ∪ w.B := (Finset.mem_inter.mp hz).2
      rcases Finset.mem_union.mp hzAB with hzA | hzB
      · have : z ∈ w.A ∩ S := Finset.mem_inter.mpr ⟨hzA, hzS⟩
        simpa [hAS] using this
      · have : z ∈ w.B ∩ S := Finset.mem_inter.mpr ⟨hzB, hzS⟩
        simpa [hBS] using this
    · intro hz
      have hzCore : z ∈ w.core := (Finset.mem_erase.mp hz).2
      have hzS : z ∈ S :=
        core_erase_subset_S_of_blockedUnionWitness (family := family) (S := S)
          (x := y) w hz
      -- `z ∈ core` implies `z ∈ A ∩ B`, hence `z ∈ A ∪ B`.
      have hzAB' : z ∈ w.A ∩ w.B := by
        have hz' : z ∈ w.core := hzCore
        -- rewrite along `w.hcoreAB : A ∩ B = core`
        have hz'' := hz'
        rw [← w.hcoreAB] at hz''
        exact hz''
      have hzAB : z ∈ w.A ∪ w.B := by
        exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mp hzAB').1)
      exact Finset.mem_inter.mpr ⟨hzS, hzAB⟩
  -- Decompose `S` into the part inside `w.A ∪ w.B` and its complement.
  have hdecomp : S = (S ∩ (w.A ∪ w.B)) ∪ (S \ (w.A ∪ w.B)) := by
    ext z
    constructor
    · intro hz
      by_cases hzAB : z ∈ w.A ∪ w.B
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hz, hzAB⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hz, hzAB⟩))
    · intro hz
      rcases Finset.mem_union.mp hz with hz | hz
      · exact (Finset.mem_inter.mp hz).1
      · exact (Finset.mem_sdiff.mp hz).1
  -- Substitute `S ∩ (A ∪ B) = core.erase y`.
  calc
    S = (S ∩ (w.A ∪ w.B)) ∪ (S \ (w.A ∪ w.B)) := hdecomp
    _ = (w.core.erase y) ∪ (S \ (w.A ∪ w.B)) := by simpa [hSAB]

theorem eq_of_coreTrace_eq_of_outsideTrace_eq_of_rigid
    {S1 S2 : Finset α} {y : α}
    (w1 : BlockedUnionWitness family S1 y) (w2 : BlockedUnionWitness family S2 y)
    (hy1 : y ∉ S1) (hy2 : y ∉ S2)
    (hcore : trace2PlusOfFinset (α := α) (w1.core.erase y) =
        trace2PlusOfFinset (α := α) (w2.core.erase y))
    (hout : outsideTrace (family := family) (S := S1) (y := y) w1 =
        outsideTrace (family := family) (S := S2) (y := y) w2) :
    -- Rigid regime: neither trace reports a “third element”.
    (∀ t1 ot2, trace2PlusOfFinset (α := α) (w1.core.erase y) ≠ some (t1, ot2, true)) →
    (∀ t1 ot2, outsideTrace (family := family) (S := S1) (y := y) w1 ≠ some (t1, ot2, true)) →
    S1 = S2 := by
  classical
  intro hcoreNoMore houtNoMore
  -- Decode `core.erase y` exactly from the common trace (rigid cases only).
  have hcore1 : w1.core.erase y = w2.core.erase y := by
    -- Case split on the common trace value.
    cases ht : trace2PlusOfFinset (α := α) (w1.core.erase y) with
    | none =>
        have ht2 : trace2PlusOfFinset (α := α) (w2.core.erase y) = none := by
          simpa [ht] using hcore.symm
        have h1 : w1.core.erase y = (∅ : Finset α) :=
          eq_empty_of_trace2PlusOfFinset_eq_none (α := α) ht
        have h2 : w2.core.erase y = (∅ : Finset α) :=
          eq_empty_of_trace2PlusOfFinset_eq_none (α := α) ht2
        simpa [h1, h2]
    | some triple =>
        cases' triple with t1 triple2
        cases' triple2 with ot2 b
        cases b with
        | false =>
            -- Rigid: decode as singleton or pair.
            have ht2 : trace2PlusOfFinset (α := α) (w2.core.erase y) = some (t1, ot2, false) := by
              simpa [ht] using hcore.symm
            cases ot2 with
            | none =>
                have h1 :
                    w1.core.erase y = ({t1} : Finset α) :=
                  eq_singleton_of_trace2PlusOfFinset_eq_some_none_false (α := α) ht
                have h2 :
                    w2.core.erase y = ({t1} : Finset α) :=
                  eq_singleton_of_trace2PlusOfFinset_eq_some_none_false (α := α) ht2
                simpa [h1, h2]
            | some t2 =>
                have h1 :
                    w1.core.erase y = ({t1, t2} : Finset α) :=
                  eq_pair_of_trace2PlusOfFinset_eq_some_some_false (α := α) (by simpa [ht])
                have h2 :
                    w2.core.erase y = ({t1, t2} : Finset α) :=
                  eq_pair_of_trace2PlusOfFinset_eq_some_some_false (α := α) (by simpa [ht2])
                simpa [h1, h2]
        | true =>
            exfalso
            exact (hcoreNoMore t1 ot2) ht
  -- Decode `S \ (A ∪ B)` exactly from the common outside trace (rigid cases only).
  have hout1 : S1 \ (w1.A ∪ w1.B) = S2 \ (w2.A ∪ w2.B) := by
    cases ht : outsideTrace (family := family) (S := S1) (y := y) w1 with
    | none =>
        have ht2 : outsideTrace (family := family) (S := S2) (y := y) w2 = none := by
          simpa [ht] using hout.symm
        have h1 : S1 \ (w1.A ∪ w1.B) = (∅ : Finset α) :=
          S_sdiff_union_eq_empty_of_outsideTrace_eq_none (family := family) (S := S1) (y := y) w1 ht
        have h2 : S2 \ (w2.A ∪ w2.B) = (∅ : Finset α) :=
          S_sdiff_union_eq_empty_of_outsideTrace_eq_none (family := family) (S := S2) (y := y) w2 ht2
        simpa [h1, h2]
    | some triple =>
        cases' triple with t1 triple2
        cases' triple2 with ot2 b
        cases b with
        | false =>
            have ht2 : outsideTrace (family := family) (S := S2) (y := y) w2 = some (t1, ot2, false) := by
              simpa [ht] using hout.symm
            cases ot2 with
            | none =>
                have h1 : S1 \ (w1.A ∪ w1.B) = ({t1} : Finset α) :=
                  S_sdiff_union_eq_singleton_of_outsideTrace_eq_some_none_false
                    (family := family) (S := S1) (y := y) w1 (by simpa [ht])
                have h2 : S2 \ (w2.A ∪ w2.B) = ({t1} : Finset α) :=
                  S_sdiff_union_eq_singleton_of_outsideTrace_eq_some_none_false
                    (family := family) (S := S2) (y := y) w2 (by simpa [ht2])
                simpa [h1, h2]
            | some t2 =>
                have h1 : S1 \ (w1.A ∪ w1.B) = ({t1, t2} : Finset α) :=
                  S_sdiff_union_eq_pair_of_outsideTrace_eq_some_some_false
                    (family := family) (S := S1) (y := y) w1 (by simpa [ht])
                have h2 : S2 \ (w2.A ∪ w2.B) = ({t1, t2} : Finset α) :=
                  S_sdiff_union_eq_pair_of_outsideTrace_eq_some_some_false
                    (family := family) (S := S2) (y := y) w2 (by simpa [ht2])
                simpa [h1, h2]
        | true =>
            exfalso
            exact (houtNoMore t1 ot2) (by simpa [ht])
  -- Finally, reconstruct `S` from the two rigid pieces.
  have hS1 :
      S1 = (w1.core.erase y) ∪ (S1 \ (w1.A ∪ w1.B)) :=
    S_eq_coreErase_union_sdiff_union_of_blockedUnionWitness
      (family := family) (S := S1) (y := y) w1 hy1
  have hS2 :
      S2 = (w2.core.erase y) ∪ (S2 \ (w2.A ∪ w2.B)) :=
    S_eq_coreErase_union_sdiff_union_of_blockedUnionWitness
      (family := family) (S := S2) (y := y) w2 hy2
  -- Substitute the two equal components.
  calc
    S1 = (w1.core.erase y) ∪ (S1 \ (w1.A ∪ w1.B)) := hS1
    _ = (w2.core.erase y) ∪ (S2 \ (w2.A ∪ w2.B)) := by simpa [hcore1, hout1]
    _ = S2 := hS2.symm

theorem eq_of_perXSignature_eq_of_rigid
    {k : WLcertKey α} {S1 S2 : Finset α} {y : α}
    (w1 : BlockedUnionWitness family S1 y) (w2 : BlockedUnionWitness family S2 y)
    (hy1 : y ∉ S1) (hy2 : y ∉ S2)
    (hsig :
      perXSignature (family := family) (k := k) (S := S1) (y := y) w1 =
        perXSignature (family := family) (k := k) (S := S2) (y := y) w2)
    (hcoreNoMore :
      ∀ t1 ot2, trace2PlusOfFinset (α := α) (w1.core.erase y) ≠ some (t1, ot2, true))
    (houtNoMore :
      ∀ t1 ot2, outsideTrace (family := family) (S := S1) (y := y) w1 ≠ some (t1, ot2, true)) :
    S1 = S2 := by
  classical
  have hcore :
      trace2PlusOfFinset (α := α) (w1.core.erase y) =
        trace2PlusOfFinset (α := α) (w2.core.erase y) :=
    congrArg (fun sig : PerXSignature α => sig.2.2.2.1) hsig
  have hout :
      outsideTrace (family := family) (S := S1) (y := y) w1 =
        outsideTrace (family := family) (S := S2) (y := y) w2 :=
    congrArg (fun sig : PerXSignature α => sig.2.2.2.2.2) hsig
  exact
    eq_of_coreTrace_eq_of_outsideTrace_eq_of_rigid
      (family := family) (S1 := S1) (S2 := S2) (y := y) w1 w2 hy1 hy2 hcore hout
      hcoreNoMore houtNoMore

/--
Rigid determinism, lifted to the canonical hard-fiber signature:
if two hard-fiber completions have the same `perXSignature_of_hardFiber` and the
`coreTrace`/`outsideTrace` components are rigid (no “third element”), then the completions
are equal.

This is the lemma used to show rigid signature buckets have card ≤ 1.
-/
theorem eq_of_perXSignature_of_hardFiber_eq_of_rigid
    (hreg : O1aUpgradeRegime family ground A0 h0)
    {k : WLcertKey α} {Sstar S1 S2 : Finset α}
    (hSstarDom : Sstar ∈ o1aWitnessLiftDomWL family h0)
    (hS1Dom : S1 ∈ o1aWitnessLiftDomWL family h0)
    (hS2Dom : S2 ∈ o1aWitnessLiftDomWL family h0)
    (hcert_star : ∃ cert : WLcert family Sstar, WLcert.key cert = k ∧ cert.h ∉ Sstar)
    (hcert1 : ∃ cert : WLcert family S1, WLcert.key cert = k ∧ cert.h ∉ S1)
    (hcert2 : ∃ cert : WLcert family S2, WLcert.key cert = k ∧ cert.h ∉ S2)
    (hne1 : S1 ≠ Sstar) (hne2 : S2 ≠ Sstar)
    (hsig :
      perXSignature_of_hardFiber (family := family) (ground := ground) (A0 := A0) (h0 := h0)
          hreg (k := k) (Sstar := Sstar) (Ssub := S1) hSstarDom hS1Dom hcert_star hcert1 hne1 =
        perXSignature_of_hardFiber (family := family) (ground := ground) (A0 := A0) (h0 := h0)
          hreg (k := k) (Sstar := Sstar) (Ssub := S2) hSstarDom hS2Dom hcert_star hcert2 hne2)
    (hcoreNoMore :
      ∀ t1 ot2,
        (perXSignature_of_hardFiber (family := family) (ground := ground) (A0 := A0) (h0 := h0)
              hreg (k := k) (Sstar := Sstar) (Ssub := S1) hSstarDom hS1Dom hcert_star hcert1 hne1).2.2.2.1 ≠
          some (t1, ot2, true))
    (houtNoMore :
      ∀ t1 ot2,
        (perXSignature_of_hardFiber (family := family) (ground := ground) (A0 := A0) (h0 := h0)
              hreg (k := k) (Sstar := Sstar) (Ssub := S1) hSstarDom hS1Dom hcert_star hcert1 hne1).2.2.2.2.2 ≠
          some (t1, ot2, true)) :
    S1 = S2 := by
  classical
  -- Unfold the canonical `y/witness` selections.
  let yw1 :
      Σ y : α, BlockedUnionWitness family S1 y :=
    chooseYAndWitness_of_hardFiber (family := family) (ground := ground) (A0 := A0) (h0 := h0)
      hreg (k := k) (Sstar := Sstar) (Ssub := S1) hSstarDom hS1Dom hcert_star hcert1 hne1
  let yw2 :
      Σ y : α, BlockedUnionWitness family S2 y :=
    chooseYAndWitness_of_hardFiber (family := family) (ground := ground) (A0 := A0) (h0 := h0)
      hreg (k := k) (Sstar := Sstar) (Ssub := S2) hSstarDom hS2Dom hcert_star hcert2 hne2
  -- Rewrite the signature equality into an equality of `perXSignature` terms.
  have hsig' :
      perXSignature (family := family) (k := k) (S := S1) (y := yw1.1) yw1.2 =
        perXSignature (family := family) (k := k) (S := S2) (y := yw2.1) yw2.2 := by
    simpa [perXSignature_of_hardFiber, yw1, yw2] using hsig
  -- Extract the common `y` from the first coordinate of the signature.
  have hy : yw1.1 = yw2.1 := by
    simpa using congrArg (fun sig : PerXSignature α => sig.1) hsig'
  have hy' : yw2.1 = yw1.1 := hy.symm
  -- Rebuild the second witness at `y := yw1.1` by reusing the same data and rewriting along `hy`.
  have hcoreAT2 : yw2.2.A ∩ (S2 ∪ ({yw1.1} : Finset α)) = yw2.2.core := by
    simpa [hy] using yw2.2.hcoreAT
  have hcoreBT2 : yw2.2.B ∩ (S2 ∪ ({yw1.1} : Finset α)) = yw2.2.core := by
    simpa [hy] using yw2.2.hcoreBT
  have htag2 : yw1.1 ∈ yw2.2.core ∨ yw2.2.A = S2 ∨ yw2.2.B = S2 := by
    simpa [hy] using yw2.2.htag
  let w2' : BlockedUnionWitness family S2 yw1.1 :=
    { A := yw2.2.A
      hA := yw2.2.hA
      B := yw2.2.B
      hB := yw2.2.hB
      hneAB := yw2.2.hneAB
      core := yw2.2.core
      hcoreAB := yw2.2.hcoreAB
      hcoreAT := hcoreAT2
      hcoreBT := hcoreBT2
      htag := htag2 }
  -- Extract the coreTrace/outsideTrace equalities from the signature equality.
  have hcoreTr :
      trace2PlusOfFinset (α := α) (yw1.2.core.erase yw1.1) =
        trace2PlusOfFinset (α := α) (yw2.2.core.erase yw2.1) :=
    congrArg (fun sig : PerXSignature α => sig.2.2.2.1) hsig'
  have houtTr :
      outsideTrace (family := family) (S := S1) (y := yw1.1) yw1.2 =
        outsideTrace (family := family) (S := S2) (y := yw2.1) yw2.2 :=
    congrArg (fun sig : PerXSignature α => sig.2.2.2.2.2) hsig'
  have hcoreEq :
      trace2PlusOfFinset (α := α) (yw1.2.core.erase yw1.1) =
        trace2PlusOfFinset (α := α) (w2'.core.erase yw1.1) := by
    -- Rewrite `yw2.1` into `yw1.1` and `w2'.core` into `yw2.2.core`.
    simpa [w2', hy'] using hcoreTr
  have houtEq :
      outsideTrace (family := family) (S := S1) (y := yw1.1) yw1.2 =
        outsideTrace (family := family) (S := S2) (y := yw1.1) w2' := by
    -- `outsideTrace` ignores `y`; only `S` and the witness sets matter.
    simpa [outsideTrace, w2', hy'] using houtTr
  -- Now both witnesses are over the same `y := yw1.1`.
  have hy1not : yw1.1 ∉ S1 := by
    have hyDiff : yw1.1 ∈ Sstar \ S1 := by
      simpa [yw1, chooseYAndWitness_of_hardFiber] using
        (chooseMissingFromRef_spec (family := family) (h0 := h0) Sstar S1 hSstarDom hS1Dom hne1)
    exact (Finset.mem_sdiff.mp hyDiff).2
  have hy2not : yw1.1 ∉ S2 := by
    have hyDiff : yw2.1 ∈ Sstar \ S2 := by
      simpa [yw2, chooseYAndWitness_of_hardFiber] using
        (chooseMissingFromRef_spec (family := family) (h0 := h0) Sstar S2 hSstarDom hS2Dom hne2)
    have hy2not' : yw2.1 ∉ S2 := (Finset.mem_sdiff.mp hyDiff).2
    simpa [hy'] using hy2not'
  -- Convert the rigid hypotheses to the forms needed by `eq_of_perXSignature_eq_of_rigid`.
  have hcoreNoMore' :
      ∀ t1 ot2,
        trace2PlusOfFinset (α := α) (yw1.2.core.erase yw1.1) ≠ some (t1, ot2, true) := by
    intro t1 ot2
    simpa [perXSignature_of_hardFiber, yw1, perXSignature] using hcoreNoMore t1 ot2
  have houtNoMore' :
      ∀ t1 ot2,
        outsideTrace (family := family) (S := S1) (y := yw1.1) yw1.2 ≠ some (t1, ot2, true) := by
    intro t1 ot2
    simpa [perXSignature_of_hardFiber, yw1, perXSignature, outsideTrace] using houtNoMore t1 ot2
  -- Apply rigid determinism using only the coreTrace/outsideTrace equalities.
  exact
    eq_of_coreTrace_eq_of_outsideTrace_eq_of_rigid
      (family := family) (S1 := S1) (S2 := S2) (y := yw1.1) yw1.2 w2'
      hy1not hy2not hcoreEq houtEq hcoreNoMore' houtNoMore'

theorem B_ne_S_of_mem_core_of_not_mem_S {S : Finset α} {y : α} (w : BlockedUnionWitness family S y)
    (hyNot : y ∉ S) (hyCore : y ∈ w.core) :
    w.B ≠ S := by
  intro hEq
  have hyB : y ∈ w.B := mem_right_of_mem_core (family := family) (S := S) (y := y) w hyCore
  have : y ∈ S := by simpa [hEq] using hyB
  exact hyNot this

theorem rAB_subset_keyBase_of_hNotMem_reduction
    (hreg : O1aUpgradeRegime family ground A0 h0)
    {k : WLcertKey α} {S : Finset α}
    (hSdom : S ∈ o1aWitnessLiftDomWL family h0)
    (hcert : ∃ cert : WLcert family S, WLcert.key cert = k ∧ cert.h ∉ S)
    {y : α} (hyX : y ∈ (ground \ (k.2.2.1 ∪ k.2.2.2.1))) (hyNot : y ∉ S) (hy0 : y ≠ h0) :
    let w : BlockedUnionWitness family S y :=
      chooseBlockedUnionWitnessNorm_of_hNotMem_reduction (family := family) (ground := ground)
        (A0 := A0) (h0 := h0) hreg (k := k) (S := S) hSdom hcert hyX hyNot hy0
    rAB (family := family) (k := k) (S := S) (y := y) w ⊆ keyBase (k := k) := by
  classical
  intro w
  -- The hard-branch trace pins down `S ∩ (kA ∪ kB)`.
  have htr :=
    (wlcert_hNotMem_reduction_o1aDomWL (family := family) (ground := ground) (A0 := A0) (h0 := h0)
      hreg (k := k) (S := S) hSdom hcert)
  have hAB : S ∩ (k.2.2.1 ∪ k.2.2.2.1) = (k.2.2.2.2).erase (k.1) := htr.2.2.1
  -- Unfold the projected anchor and rewrite into `S ∩ (kA ∪ kB)`.
  intro z hz
  have hz' : z ∈ (w.core.erase y) ∧ z ∈ (k.2.2.1 ∪ k.2.2.2.1) := by
    simpa [rAB] using (Finset.mem_inter.mp hz)
  have hz_core : z ∈ w.core.erase y := hz'.1
  have hzS : z ∈ S := core_erase_subset_S_of_blockedUnionWitness (family := family) (S := S)
      (x := y) w hz_core
  have hzAB : z ∈ k.2.2.1 ∪ k.2.2.2.1 := hz'.2
  have : z ∈ S ∩ (k.2.2.1 ∪ k.2.2.2.1) := Finset.mem_inter.mpr ⟨hzS, hzAB⟩
  -- Conclude using the fixed trace equality.
  simpa [keyBase, hAB] using this

/-!
Per-`x` subfiber bucket plumbing (hard branch).

We will use the generic `Bucket` API instantiated with the canonical per-`x` signature
`perXSignature_of_hardFiber` to bound each per-`x` subfiber in the hard-branch multiplicity proof.

At this layer we only record the two structural facts that are reused many times:
1. every completion `Ssub` in a per-`x` subfiber is distinct from the reference completion `S⋆`;
2. rigid signature buckets have cardinality `≤ 1` by the rigid determinism lemma.
-/

section PerXBucket

variable {k : WLcertKey α}
variable {dom : Finset (Finset α)}
variable {fiber : Finset {S // S ∈ dom}}
variable {Sstar : {S // S ∈ dom}} {x : α}

theorem ne_Sstar_of_mem_fiberForX {Ssub : {S // S ∈ dom}}
    (hSsub :
      Ssub ∈ wlcertAdmissibleFiber_hNotMem_fiberForX (dom := dom) fiber Sstar.1 x) :
    Ssub ≠ Sstar := by
  classical
  -- `x ∈ Ssub` but `x ∉ S⋆` by definition of the per-`x` subfiber.
  have hxSsub : x ∈ Ssub.1 := (Finset.mem_filter.mp hSsub).2.1
  have hxnot : x ∉ Sstar.1 := (Finset.mem_filter.mp hSsub).2.2
  intro hEq
  have : x ∈ Sstar.1 := by simpa [hEq] using hxSsub
  exact hxnot this

theorem ne_Sstar_val_of_mem_fiberForX {Ssub : {S // S ∈ dom}}
    (hSsub :
      Ssub ∈ wlcertAdmissibleFiber_hNotMem_fiberForX (dom := dom) fiber Sstar.1 x) :
    Ssub.1 ≠ Sstar.1 := by
  intro hEq
  exact ne_Sstar_of_mem_fiberForX (Sstar := Sstar) (x := x) (Ssub := Ssub) hSsub
    (Subtype.ext hEq)

end PerXBucket

/-!
Rigid bucket bound inside a per-`x` subfiber.

This is the first “plug-in” lemma for the per-`x` bucket sum:
inside a fixed signature bucket `Bucket(σ)`, if the `coreTrace` and `outsideTrace` components
are rigid (`hasMore = false`), then the bucket has cardinality `≤ 1` by rigid determinism.
-/

section PerXBucketBounds

variable {α : Type*} [DecidableEq α]
variable {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h0 : α}

-- `Bucket`/`Finset.filter` over the per-`x` signature requires decidable equality on signatures.
noncomputable local instance : DecidableEq (PerXSignature α) := by
  classical
  exact Classical.decEq _

theorem card_Bucket_perXSignature_of_hardFiber_le_one_of_rigid
    (hreg : O1aUpgradeRegime family ground A0 h0)
    {k : WLcertKey α}
    {Sstar : {S // S ∈ o1aWitnessLiftDomWL family h0}}
    {x : α}
    (hSstar :
      Sstar ∈ wlcertAdmissibleFiber_hNotMem (family := family) (o1aWitnessLiftDomWL family h0) k)
    (σ : PerXSignature α)
    (hcoreNoMore : ∀ t1 ot2, σ.2.2.2.1 ≠ some (t1, ot2, true))
    (houtNoMore : ∀ t1 ot2, σ.2.2.2.2.2 ≠ some (t1, ot2, true)) :
    let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h0
    let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
    let Fx0 :
        Finset {S // S ∈ dom} :=
      wlcertAdmissibleFiber_hNotMem_fiberForX (dom := dom) fiber Sstar.1 x
    let sig : {Ssub // Ssub ∈ Fx0} → PerXSignature α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      perXSignature_of_hardFiber (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1) Sstar.2 b.1.2 hcert_star hcert_sub hne
    (Bucket (Fx := Fx0.attach) sig σ).card ≤ 1 := by
  classical
  intro dom fiber Fx0 sig
  -- Show the bucket is a subsingleton by rigid determinism.
  refine Finset.card_le_one.2 ?_
  intro b1 hb1 b2 hb2
  have hb1sig : sig b1 = σ := (Finset.mem_filter.mp hb1).2
  have hb2sig : sig b2 = σ := (Finset.mem_filter.mp hb2).2
  have hsig : sig b1 = sig b2 := by simpa [hb1sig, hb2sig]
  -- Extract the hard-fiber certificates for `S⋆` and the two completions.
  have hcert_star :
      ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
    (Finset.mem_filter.mp hSstar).2
  have hb1Fiber : b1.1 ∈ fiber := (Finset.mem_filter.mp b1.2).1
  have hb2Fiber : b2.1 ∈ fiber := (Finset.mem_filter.mp b2.2).1
  have hcert1 :
      ∃ cert : WLcert family b1.1.1, WLcert.key cert = k ∧ cert.h ∉ b1.1.1 :=
    (Finset.mem_filter.mp hb1Fiber).2
  have hcert2 :
      ∃ cert : WLcert family b2.1.1, WLcert.key cert = k ∧ cert.h ∉ b2.1.1 :=
    (Finset.mem_filter.mp hb2Fiber).2
  have hne1 : b1.1.1 ≠ Sstar.1 :=
    ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
      (Ssub := b1.1) b1.2
  have hne2 : b2.1.1 ≠ Sstar.1 :=
    ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
      (Ssub := b2.1) b2.2
  -- Apply rigid determinism for the canonical hard-fiber signature.
  have hEqSets :
      b1.1.1 = b2.1.1 := by
    have hsig' :
        perXSignature_of_hardFiber (family := family) (ground := ground) (A0 := A0) (h0 := h0)
            hreg (k := k) (Sstar := Sstar.1) (Ssub := b1.1.1) Sstar.2 b1.1.2 hcert_star hcert1 hne1 =
          perXSignature_of_hardFiber (family := family) (ground := ground) (A0 := A0) (h0 := h0)
            hreg (k := k) (Sstar := Sstar.1) (Ssub := b2.1.1) Sstar.2 b2.1.2 hcert_star hcert2 hne2 := by
      simpa [sig, hcert_star] using hsig
    have hcoreNoMore1 :
        ∀ t1 ot2,
          (perXSignature_of_hardFiber (family := family) (ground := ground) (A0 := A0) (h0 := h0)
                hreg (k := k) (Sstar := Sstar.1) (Ssub := b1.1.1) Sstar.2 b1.1.2 hcert_star hcert1
                hne1).2.2.2.1 ≠ some (t1, ot2, true) := by
      intro t1 ot2
      simpa [hb1sig, sig, hcert_star] using hcoreNoMore t1 ot2
    have houtNoMore1 :
        ∀ t1 ot2,
          (perXSignature_of_hardFiber (family := family) (ground := ground) (A0 := A0) (h0 := h0)
                hreg (k := k) (Sstar := Sstar.1) (Ssub := b1.1.1) Sstar.2 b1.1.2 hcert_star hcert1
                hne1).2.2.2.2.2 ≠ some (t1, ot2, true) := by
      intro t1 ot2
      simpa [hb1sig, sig, hcert_star, perXSignature, outsideTrace] using houtNoMore t1 ot2
    exact
      eq_of_perXSignature_of_hardFiber_eq_of_rigid (family := family) (ground := ground) (A0 := A0)
        (h0 := h0) hreg (k := k) (Sstar := Sstar.1) (S1 := b1.1.1) (S2 := b2.1.1)
        (hSstarDom := Sstar.2) (hS1Dom := b1.1.2) (hS2Dom := b2.1.2) hcert_star hcert1 hcert2 hne1 hne2
        hsig' hcoreNoMore1 houtNoMore1
  -- Conclude equality in the attached bucket.
  have hEq1 : b1.1 = b2.1 := Subtype.ext hEqSets
  exact Subtype.ext hEq1

/-!
Local `t₆` split inside a fixed per-`x` signature bucket (outMore residue helper).

This is purely “wiring”: we package the generic `card_le_sum_card_filter_of_exists_sixth` lemma
at the exact plug-in point we will use in the per-`x` bucket ledger:
inside a fixed `Bucket(σ)` over `sig := perXSignature_of_hardFiber`, we may union-bound the
`|Uout| ≥ 6` residue case by a single local `t₆` split.

No constant cap is proved here yet; this lemma is just the decomposition step.
-/

theorem card_Bucket_trace5Plus_Uout_le_sum_t6
    (hreg : O1aUpgradeRegime family ground A0 h0)
    {k : WLcertKey α}
    {Sstar : {S // S ∈ o1aWitnessLiftDomWL family h0}}
    {x : α}
    (hSstar :
      Sstar ∈ wlcertAdmissibleFiber_hNotMem (family := family) (o1aWitnessLiftDomWL family h0) k)
    (σ : PerXSignature α)
    {t1 t2 t3 t4 t5 : α} :
    let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h0
    let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
    let Fx0 :
        Finset {S // S ∈ dom} :=
      wlcertAdmissibleFiber_hNotMem_fiberForX (dom := dom) fiber Sstar.1 x
    let sig : {Ssub // Ssub ∈ Fx0} → PerXSignature α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      perXSignature_of_hardFiber (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1) Sstar.2 b.1.2 hcert_star hcert_sub hne
    let Uout : {Ssub // Ssub ∈ Fx0} → Finset α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      let yw :
          Σ y : α, BlockedUnionWitness family b.1.1 y :=
        chooseYAndWitness_of_hardFiber
          (family := family) (ground := ground) (A0 := A0) (h0 := h0)
          hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
          Sstar.2 b.1.2 hcert_star hcert_sub hne
      b.1.1 \ (yw.2.A ∪ yw.2.B)
    let Bσ : Finset {Ssub // Ssub ∈ Fx0} := Bucket (Fx := Fx0.attach) sig σ
    let Fτ : Finset {Ssub // Ssub ∈ Fx0} := by
      classical
      exact
        Bσ.filter (fun b =>
          trace5PlusOfFinset (α := α) (Uout b) = some (t1, t2, t3, t4, t5, true))
    Fτ.card ≤
      ∑ t6 ∈ ground,
        (Fτ.filter (fun b =>
          t6 ∈ Uout b ∧ t6 ∉ ({t1, t2, t3, t4, t5} : Finset α))).card := by
  classical
  intro dom fiber Fx0 sig Uout Bσ Fτ
  -- Reduce the goal by unfolding the `let`-binding for `Fτ`.
  -- (We prove the statement for `Bσ.filter …` directly, and `simpa` eliminates the `let`.)
  have hmain :
      (Bσ.filter (fun b =>
          trace5PlusOfFinset (α := α) (Uout b) = some (t1, t2, t3, t4, t5, true))).card ≤
        ∑ t6 ∈ ground,
          ((Bσ.filter (fun b =>
              trace5PlusOfFinset (α := α) (Uout b) = some (t1, t2, t3, t4, t5, true))).filter
            (fun b => t6 ∈ Uout b ∧ t6 ∉ ({t1, t2, t3, t4, t5} : Finset α))).card := by
    -- Use the generic local `t₆` split lemma.
    refine
      card_le_sum_card_filter_of_exists_sixth (α := α)
        (F :=
          Bσ.filter (fun b =>
            trace5PlusOfFinset (α := α) (Uout b) = some (t1, t2, t3, t4, t5, true)))
        (ground := ground) (U := Uout) ?hUsub ?htr
    · intro b hbF
      -- `Uout b ⊆ b.1.1 ⊆ ground`.
      have hbDom : b.1.1 ∈ dom := b.1.2
      have hSfam : b.1.1 ∈ family :=
        mem_family_of_mem_o1aWitnessLiftDomWL (family := family) (h0 := h0) (S := b.1.1) hbDom
      have hSsub : b.1.1 ⊆ ground := Finset.mem_powerset.mp (hreg.1 hSfam)
      intro z hzU
      have hzS : z ∈ b.1.1 := (Finset.mem_sdiff.mp hzU).1
      exact hSsub hzS
    · intro b hbF
      exact (Finset.mem_filter.mp hbF).2
  -- Finish by rewriting `Fτ` away.
  simpa [Fτ] using hmain

/--
Extended per-`x` outMore signature:
fold the `trace5Plus` quintuple and a single local sixth witness `t₆` into the bucket key.

This is a wiring move: it avoids paying an external `n^5 · n` factor in the ledger by
absorbing `(τ,t₆?)` into the number of signature values.
-/
abbrev PerXSignatureOutMore (α : Type*) :=
  PerXSignature α × Option (α × α × α × α × α × Bool) × Option α

-- `Finset.image`/`Finset.filter` over the extended signature uses decidable equality.
noncomputable local instance : DecidableEq (PerXSignatureOutMore α) := by
  classical
  exact Classical.decEq _

/-!
`τ=true` signature-image bound for the extended outMore signature.

When `trace5PlusOfFinset (Uout b) = some(t1,t2,t3,t4,t5,true)`, the first two coordinates
`(t1,t2)` are already pinned by the `outsideTrace` component of `sig0 b`, because
`outsideTrace = trace2PlusOfFinset (Uout b)` and the `trace5Plus`/`trace2Plus` heads are
compatible.

Thus, in the `τ=true` regime the only remaining freedom in the `trace5Plus` quintuple is
`(t3,t4,t5)`, giving an `n^3` contribution (and the `t6` option contributes `≤ n+1`).
-/
theorem card_image_sigOut_filter_trace5Plus_true_le
    {β : Type*} [DecidableEq β]
    (Fx : Finset β) (ground : Finset α)
    (sig0 : β → PerXSignature α) (Uout : β → Finset α)
    (hUsub : ∀ b ∈ Fx, Uout b ⊆ ground)
    (hout :
      ∀ b ∈ Fx,
        (sig0 b).2.2.2.2.2 = trace2PlusOfFinset (α := α) (Uout b)) :
    let sigOut : β → PerXSignatureOutMore α := fun b =>
      (sig0 b,
        trace5PlusOfFinset (α := α) (Uout b),
        t6OptionOfTrace5Plus (α := α) (Uout b))
    let sig0Image : Finset (PerXSignature α) := Fx.image sig0
    let sigOutImage : Finset (PerXSignatureOutMore α) := Fx.image sigOut
    let TauTrue : Finset (PerXSignatureOutMore α) :=
      by
        classical
        exact sigOutImage.filter (fun σOut =>
          match σOut.2.1 with
          | some (t1, t2, t3, t4, t5, true) => True
          | _ => False)
    TauTrue.card ≤ sig0Image.card * (ground.card ^ 3) * (ground.card + 1) := by
  classical
  intro sigOut sig0Image sigOutImage TauTrue
  -- Codomain finsets for the injection argument.
  let Trip : Finset (α × (α × α)) := ground.product (ground.product ground)
  let T6 : Finset (Option α) := optionOfFinset (α := α) ground
  let Cod :
      Finset (PerXSignature α × (Option (α × (α × α)) × Option α)) :=
    sig0Image.product ((Trip.image some).product T6)
  -- The injection records: the full `PerXSignature`, the tail triple `(t3,t4,t5)` (as `some`),
  -- and the local `t6` option. The head pair `(t1,t2)` is recovered from `outsideTrace`.
  let h :
      PerXSignatureOutMore α →
        PerXSignature α × (Option (α × (α × α)) × Option α) :=
    fun σOut =>
      match σOut.2.1 with
      | some (t1, t2, t3, t4, t5, true) =>
          (σOut.1, (some (t3, (t4, t5)), σOut.2.2))
      | _ =>
          (σOut.1, (none, σOut.2.2))
  -- Extract the `trace5Plus` quintuple from membership in `TauTrue`.
  have exists_quint_of_mem_TauTrue :
      ∀ {σOut : PerXSignatureOutMore α},
        σOut ∈ TauTrue →
          ∃ t1 t2 t3 t4 t5 : α, σOut.2.1 = some (t1, t2, t3, t4, t5, true) := by
    intro σOut hmem
    have hmem' :
        σOut ∈ sigOutImage ∧
          (match σOut.2.1 with
            | some (t1, t2, t3, t4, t5, true) => True
            | _ => False) := by
      simpa [TauTrue] using hmem
    have hpred :
        (match σOut.2.1 with
          | some (t1, t2, t3, t4, t5, true) => True
          | _ => False) := hmem'.2
    cases hτ : σOut.2.1 with
    | none =>
        exfalso
        exact (by simpa [hτ] using hpred)
    | some q =>
        rcases q with ⟨t1, t2, t3, t4, t5, b⟩
        cases b with
        | false =>
            exfalso
            exact (by simpa [hτ] using hpred)
        | true =>
            refine ⟨t1, t2, t3, t4, t5, ?_⟩
            simpa [hτ]
  -- Helper: in the actual `sigOut` image, `outsideTrace` matches the `trace5Plus` head pair.
  have hout_head :
      ∀ {σOut : PerXSignatureOutMore α} {t1 t2 t3 t4 t5 : α},
        σOut ∈ sigOutImage →
        σOut.2.1 = some (t1, t2, t3, t4, t5, true) →
        σOut.1.2.2.2.2.2 = some (t1, some t2, true) := by
    intro σOut t1 t2 t3 t4 t5 hmem hτ
    rcases Finset.mem_image.mp hmem with ⟨b, hbFx, hbEq⟩
    -- Rewrite `σOut` as `sigOut b`.
    have hσ1 : (sigOut b).1 = σOut.1 := congrArg (fun s : PerXSignatureOutMore α => s.1) hbEq
    have hστ : (sigOut b).2.1 = σOut.2.1 :=
      congrArg (fun s : PerXSignatureOutMore α => s.2.1) hbEq
    have hτ' :
        trace5PlusOfFinset (α := α) (Uout b) =
          some (t1, t2, t3, t4, t5, true) := by
      -- `(sigOut b).2.1` is `trace5Plus(Uout b)`.
      have : trace5PlusOfFinset (α := α) (Uout b) = σOut.2.1 := by
        simpa [sigOut] using hστ
      simpa [hτ] using this
    have h2 :
        trace2PlusOfFinset (α := α) (Uout b) =
          some (t1, some t2, true) :=
      trace2PlusOfFinset_eq_some_some_true_of_trace5PlusOfFinset_eq_some (α := α) (T := Uout b)
        (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) (t5 := t5) (b := true) hτ'
    have hout' :
        (sigOut b).1.2.2.2.2.2 = trace2PlusOfFinset (α := α) (Uout b) := by
      -- `(sigOut b).1 = sig0 b`, and `hout` tells us how the `outsideTrace` component is computed.
      have : (sig0 b).2.2.2.2.2 = trace2PlusOfFinset (α := α) (Uout b) := hout b hbFx
      simpa [sigOut] using this
    -- Transport along `hbEq` to get the statement for `σOut`.
    -- First rewrite the LHS via `hσ1`, then chain with `h2`.
    have : σOut.1.2.2.2.2.2 = trace2PlusOfFinset (α := α) (Uout b) := by
      -- `hout'` gives the equality for `(sigOut b).1`; rewrite to `σOut.1`.
      simpa [hσ1] using hout'
    exact this.trans h2
  -- `h` is injective on the `τ=true` filtered image.
  have hinj : Set.InjOn h (↑TauTrue : Set (PerXSignatureOutMore α)) := by
    intro σ1 hσ1 σ2 hσ2 hEq
    have hσ1Fin : σ1 ∈ TauTrue := by simpa using hσ1
    have hσ2Fin : σ2 ∈ TauTrue := by simpa using hσ2
    have hσ1' :
        σ1 ∈ sigOutImage ∧
          (match σ1.2.1 with
            | some (t1, t2, t3, t4, t5, true) => True
            | _ => False) := by
      simpa [TauTrue] using hσ1Fin
    have hσ2' :
        σ2 ∈ sigOutImage ∧
          (match σ2.2.1 with
            | some (t1, t2, t3, t4, t5, true) => True
            | _ => False) := by
      simpa [TauTrue] using hσ2Fin
    have hmem1 : σ1 ∈ sigOutImage := hσ1'.1
    have hmem2 : σ2 ∈ sigOutImage := hσ2'.1
    rcases exists_quint_of_mem_TauTrue (σOut := σ1) hσ1Fin with ⟨t1a, t2a, t3a, t4a, t5a, hτ1⟩
    rcases exists_quint_of_mem_TauTrue (σOut := σ2) hσ2Fin with ⟨t1b, t2b, t3b, t4b, t5b, hτ2⟩
    -- Expand `h σi` under the `τ=true` hypotheses.
    have hEq' :
        (σ1.1, (some (t3a, (t4a, t5a)), σ1.2.2)) =
          (σ2.1, (some (t3b, (t4b, t5b)), σ2.2.2)) := by
      simpa [h, hτ1, hτ2] using hEq
    have hSigEq : σ1.1 = σ2.1 := congrArg (fun t => t.1) hEq'
    have hSnd :
        (some (t3a, (t4a, t5a)), σ1.2.2) =
          (some (t3b, (t4b, t5b)), σ2.2.2) := congrArg (fun t => t.2) hEq'
    have ht345 :
        (t3a, (t4a, t5a)) = (t3b, (t4b, t5b)) := by
      exact Option.some.inj (congrArg (fun p => p.1) hSnd)
    have ht3 : t3a = t3b := by simpa using congrArg (fun p => p.1) ht345
    have ht45 : (t4a, t5a) = (t4b, t5b) := by simpa using congrArg (fun p => p.2) ht345
    have ht4 : t4a = t4b := by simpa using congrArg (fun p => p.1) ht45
    have ht5 : t5a = t5b := by simpa using congrArg (fun p => p.2) ht45
    have ht6 : σ1.2.2 = σ2.2.2 := congrArg (fun p => p.2) hSnd
    -- Recover the head pair `(t1,t2)` from `outsideTrace` using membership in the image.
    have hHead1 :
        σ1.1.2.2.2.2.2 = some (t1a, some t2a, true) :=
      hout_head (σOut := σ1) (t1 := t1a) (t2 := t2a) (t3 := t3a) (t4 := t4a) (t5 := t5a)
        hmem1 hτ1
    have hHead2 :
        σ2.1.2.2.2.2.2 = some (t1b, some t2b, true) :=
      hout_head (σOut := σ2) (t1 := t1b) (t2 := t2b) (t3 := t3b) (t4 := t4b) (t5 := t5b)
        hmem2 hτ2
    have hHeadEq :
        some (t1a, some t2a, true) = some (t1b, some t2b, true) := by
      -- Use `hSigEq` to equate the `outsideTrace` components.
      have houtEq :
          σ1.1.2.2.2.2.2 = σ2.1.2.2.2.2.2 :=
        congrArg (fun s : PerXSignature α => s.2.2.2.2.2) hSigEq
      -- Chain the three equalities.
      calc
        some (t1a, some t2a, true) = σ1.1.2.2.2.2.2 := by simpa [hHead1]
        _ = σ2.1.2.2.2.2.2 := houtEq
        _ = some (t1b, some t2b, true) := hHead2
    have hHead' :
        (t1a, some t2a, true) = (t1b, some t2b, true) :=
      Option.some.inj hHeadEq
    have ht1 : t1a = t1b := by
      simpa using congrArg (fun p : α × Option α × Bool => p.1) hHead'
    have ht2s : some t2a = some t2b := by
      simpa using congrArg (fun p : α × Option α × Bool => p.2.1) hHead'
    have ht2 : t2a = t2b := Option.some.inj ht2s
    -- Now the full `trace5Plus` components agree.
    have hτeq : σ1.2.1 = σ2.2.1 := by
      -- Rewrite both sides to the same tuple.
      -- `σ1.2.1` is `some(t1a,t2a,t3a,t4a,t5a,true)` and similarly for `σ2`.
      -- Use the derived equalities to align them.
      simpa [hτ1, hτ2, ht1, ht2, ht3, ht4, ht5]
    -- Conclude by extensionality on the product structure.
    apply Prod.ext
    · exact hSigEq
    ·
      apply Prod.ext
      · exact hτeq
      · exact ht6
  -- Use injectivity to identify `TauTrue` with its image under `h`.
  have hcard_eq : (TauTrue.image h).card = TauTrue.card :=
    (Finset.card_image_iff (s := TauTrue) (f := h)).2 hinj
  have hsub : TauTrue.image h ⊆ Cod := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨σOut, hσOut, rfl⟩
    have hσOut' :
        σOut ∈ sigOutImage ∧
          (match σOut.2.1 with
            | some (t1, t2, t3, t4, t5, true) => True
            | _ => False) := by
      simpa [TauTrue] using hσOut
    have hmem : σOut ∈ sigOutImage := hσOut'.1
    rcases exists_quint_of_mem_TauTrue (σOut := σOut) hσOut with ⟨t1, t2, t3, t4, t5, hτ⟩
    -- Unpack `σOut` as `sigOut b` to get membership facts in `ground`.
    rcases Finset.mem_image.mp hmem with ⟨b, hbFx, hbEq⟩
    have hσ0 : sig0 b = σOut.1 := by
      have := congrArg (fun s : PerXSignatureOutMore α => s.1) hbEq
      simpa [sigOut] using this
    have hτb : trace5PlusOfFinset (α := α) (Uout b) = some (t1, t2, t3, t4, t5, true) := by
      have := congrArg (fun s : PerXSignatureOutMore α => s.2.1) hbEq
      have : trace5PlusOfFinset (α := α) (Uout b) = σOut.2.1 := by
        simpa [sigOut] using this
      simpa [hτ] using this
    -- Extract membership `t3,t4,t5 ∈ Uout b` from the underlying quint key.
    have hquint : quintKeyOfFinset (α := α) (Uout b) = some (t1, t2, t3, t4, t5) := by
      cases hq : quintKeyOfFinset (α := α) (Uout b) with
      | none =>
          have : (none : Option (α × α × α × α × α × Bool)) = some (t1, t2, t3, t4, t5, true) := by
            simpa [trace5PlusOfFinset, hq] using hτb
          cases this
      | some q =>
          have hEq :
              some
                  (q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2,
                    hasSixthOfFinset (α := α) (Uout b) q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) =
                some (t1, t2, t3, t4, t5, true) := by
            simpa [trace5PlusOfFinset, hq] using hτb
          have hEq' :
              (q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2,
                  hasSixthOfFinset (α := α) (Uout b) q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) =
                (t1, t2, t3, t4, t5, true) :=
            Option.some.inj hEq
          have hq1 : q.1 = t1 := by
            simpa using congrArg (fun p : α × α × α × α × α × Bool => p.1) hEq'
          have hq2 : q.2.1 = t2 := by
            simpa using congrArg (fun p : α × α × α × α × α × Bool => p.2.1) hEq'
          have hq3 : q.2.2.1 = t3 := by
            simpa using congrArg (fun p : α × α × α × α × α × Bool => p.2.2.1) hEq'
          have hq4 : q.2.2.2.1 = t4 := by
            simpa using congrArg (fun p : α × α × α × α × α × Bool => p.2.2.2.1) hEq'
          have hq5 : q.2.2.2.2 = t5 := by
            simpa using congrArg (fun p : α × α × α × α × α × Bool => p.2.2.2.2.1) hEq'
          have qEq : q = (t1, t2, t3, t4, t5) := by
            ext <;> simp [hq1, hq2, hq3, hq4, hq5]
          simpa [qEq] using hq
    have htMem :
        t1 ∈ Uout b ∧ t2 ∈ Uout b ∧ t3 ∈ Uout b ∧ t4 ∈ Uout b ∧ t5 ∈ Uout b :=
      mem_components_of_quintKeyOfFinset_eq_some (α := α) (T := Uout b) (t1 := t1) (t2 := t2)
        (t3 := t3) (t4 := t4) (t5 := t5) hquint
    have ht3G : t3 ∈ ground := (hUsub b hbFx) htMem.2.2.1
    have ht4G : t4 ∈ ground := (hUsub b hbFx) htMem.2.2.2.1
    have ht5G : t5 ∈ ground := (hUsub b hbFx) htMem.2.2.2.2
    -- `t6OptionOfTrace5Plus` always lands in `optionOfFinset ground`.
    have ht6mem : σOut.2.2 ∈ T6 := by
      -- Rewrite `σOut.2.2` using `hbEq`.
      have hσ2 : (sigOut b).2.2 = σOut.2.2 :=
        congrArg (fun s : PerXSignatureOutMore α => s.2.2) hbEq
      have hσ2' : t6OptionOfTrace5Plus (α := α) (Uout b) = σOut.2.2 := by
        simpa [sigOut] using hσ2
      -- It suffices to show membership in `optionOfFinset (Uout b)`, then use monotonicity.
      have ht6Uout : t6OptionOfTrace5Plus (α := α) (Uout b) ∈ optionOfFinset (α := α) (Uout b) :=
        t6OptionOfTrace5Plus_mem_optionOfFinset (α := α) (T := Uout b)
      have hmono : optionOfFinset (α := α) (Uout b) ⊆ optionOfFinset (α := α) ground :=
        optionOfFinset_mono (α := α) (hUsub b hbFx)
      have : t6OptionOfTrace5Plus (α := α) (Uout b) ∈ optionOfFinset (α := α) ground :=
        hmono ht6Uout
      simpa [hσ2'] using this
    -- Now show `h σOut ∈ Cod`.
    have hs0Mem : σOut.1 ∈ sig0Image := by
      refine Finset.mem_image.mpr ?_
      exact ⟨b, hbFx, hσ0⟩
    have hTripMem : (t3, (t4, t5)) ∈ Trip := by
      refine Finset.mem_product.mpr ?_
      refine ⟨ht3G, ?_⟩
      refine Finset.mem_product.mpr ?_
      exact ⟨ht4G, ht5G⟩
    have hTripSome : some (t3, (t4, t5)) ∈ Trip.image some := by
      refine Finset.mem_image.mpr ?_
      exact ⟨(t3, (t4, t5)), hTripMem, rfl⟩
    have hPairMem :
        (some (t3, (t4, t5)), σOut.2.2) ∈ (Trip.image some).product T6 := by
      exact Finset.mem_product.mpr ⟨hTripSome, ht6mem⟩
    have : (σOut.1, (some (t3, (t4, t5)), σOut.2.2)) ∈ Cod := by
      exact Finset.mem_product.mpr ⟨hs0Mem, hPairMem⟩
    simpa [h, hτ] using this
  have hcard_le : TauTrue.card ≤ Cod.card := by
    have himg_le : (TauTrue.image h).card ≤ Cod.card :=
      Finset.card_le_card hsub
    -- Rewrite `TauTrue.card` via the injective image.
    simpa [hcard_eq] using himg_le
  -- Bound `Cod.card` by `sig0Image.card * n^3 * (n+1)`.
  have hCod :
      Cod.card ≤ sig0Image.card * (ground.card ^ 3) * (ground.card + 1) := by
    have hT6 : T6.card ≤ ground.card + 1 := card_optionOfFinset_le_succ (α := α) ground
    have hTrip : Trip.card = ground.card ^ 3 := by
      -- `Trip = ground × (ground × ground)`.
      simp [Trip, Finset.card_product, pow_succ, pow_two, Nat.mul_assoc, Nat.mul_left_comm,
        Nat.mul_comm]
    have hTripSome : (Trip.image some).card = Trip.card := by
      simpa using (Finset.card_image_of_injective (s := Trip) (f := some) (fun _ _ h => by cases h; rfl))
    have hC2 :
        ((Trip.image some).product T6).card ≤ (ground.card ^ 3) * (ground.card + 1) := by
      -- `card(product) = card * card`, then apply the bounds.
      have :
          ((Trip.image some).product T6).card =
            (Trip.image some).card * T6.card := by
        simpa using (Finset.card_product (s := (Trip.image some)) (t := T6))
      calc
        ((Trip.image some).product T6).card
            = (Trip.image some).card * T6.card := this
        _ ≤ (Trip.image some).card * (ground.card + 1) := Nat.mul_le_mul_left _ hT6
        _ = Trip.card * (ground.card + 1) := by simp [hTripSome]
        _ = (ground.card ^ 3) * (ground.card + 1) := by simp [hTrip]
    have hCodEq :
        Cod.card = sig0Image.card * ((Trip.image some).product T6).card := by
      simpa [Cod, Finset.card_product]
    calc
      Cod.card = sig0Image.card * ((Trip.image some).product T6).card := hCodEq
      _ ≤ sig0Image.card * ((ground.card ^ 3) * (ground.card + 1)) := Nat.mul_le_mul_left _ hC2
      _ = sig0Image.card * (ground.card ^ 3) * (ground.card + 1) := by
            simp [Nat.mul_assoc]
  exact le_trans hcard_le hCod

/-!
`τ≠true` signature-image bound for the extended outMore signature.

When `σOut.2.1 ≠ some(_,_,_,_,_,true)`, we have either:
* `σOut.2.1 = none` (so the `trace5Plus` component carries no freedom), or
* `σOut.2.1 = some(t1,t2,t3,t4,t5,false)`, and then the head pair `(t1,t2)` is pinned by the
  `outsideTrace` component of `σOut.1` (compatibility of `trace5Plus`/`trace2Plus` heads).

Thus the only freedom in the `τ=false` case is the tail triple `(t3,t4,t5)`, giving an `n^3`
contribution; the `τ=none` case adds only a `+1`.
-/
theorem card_image_sigOut_filter_trace5Plus_notTrue_le
    {β : Type*} [DecidableEq β]
    (Fx : Finset β) (ground : Finset α)
    (sig0 : β → PerXSignature α) (Uout : β → Finset α)
    (hUsub : ∀ b ∈ Fx, Uout b ⊆ ground)
    (hout :
      ∀ b ∈ Fx,
        (sig0 b).2.2.2.2.2 = trace2PlusOfFinset (α := α) (Uout b)) :
    let sigOut : β → PerXSignatureOutMore α := fun b =>
      (sig0 b,
        trace5PlusOfFinset (α := α) (Uout b),
        t6OptionOfTrace5Plus (α := α) (Uout b))
    let sig0Image : Finset (PerXSignature α) := Fx.image sig0
    let sigOutImage : Finset (PerXSignatureOutMore α) := Fx.image sigOut
    let TauNotTrue : Finset (PerXSignatureOutMore α) :=
      by
        classical
        exact sigOutImage.filter (fun σOut =>
          match σOut.2.1 with
          | some (_t1, _t2, _t3, _t4, _t5, true) => False
          | _ => True)
    TauNotTrue.card ≤ sig0Image.card * ((ground.card ^ 3) + 1) := by
  classical
  intro sigOut sig0Image sigOutImage TauNotTrue
  -- Codomain finsets for the injection.
  let Trip : Finset (α × (α × α)) := ground.product (ground.product ground)
  let Tail : Finset (Option (α × (α × α))) := optionOfFinset (α := α × (α × α)) Trip
  let Cod : Finset (PerXSignature α × Option (α × (α × α))) := sig0Image.product Tail
  -- Record only the tail triple `(t3,t4,t5)` when `τ=false`; `τ=none` contributes `none`.
  let h :
      PerXSignatureOutMore α → PerXSignature α × Option (α × (α × α)) :=
    fun σOut =>
      match σOut.2.1 with
      | some (t1, t2, t3, t4, t5, false) => (σOut.1, some (t3, (t4, t5)))
      | _ => (σOut.1, none)
  -- Helper: in the actual `sigOut` image, `outsideTrace` matches the `trace5Plus` head pair.
  have hout_head_false :
      ∀ {σOut : PerXSignatureOutMore α} {t1 t2 t3 t4 t5 : α},
        σOut ∈ sigOutImage →
        σOut.2.1 = some (t1, t2, t3, t4, t5, false) →
        σOut.1.2.2.2.2.2 = some (t1, some t2, true) := by
    intro σOut t1 t2 t3 t4 t5 hmem hτ
    rcases Finset.mem_image.mp hmem with ⟨b, hbFx, hbEq⟩
    have hσ1 : (sigOut b).1 = σOut.1 := congrArg (fun s : PerXSignatureOutMore α => s.1) hbEq
    have hστ : (sigOut b).2.1 = σOut.2.1 :=
      congrArg (fun s : PerXSignatureOutMore α => s.2.1) hbEq
    have hτ' :
        trace5PlusOfFinset (α := α) (Uout b) =
          some (t1, t2, t3, t4, t5, false) := by
      have : trace5PlusOfFinset (α := α) (Uout b) = σOut.2.1 := by
        simpa [sigOut] using hστ
      simpa [hτ] using this
    have h2 :
        trace2PlusOfFinset (α := α) (Uout b) = some (t1, some t2, true) :=
      trace2PlusOfFinset_eq_some_some_true_of_trace5PlusOfFinset_eq_some (α := α) (T := Uout b)
        (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) (t5 := t5) (b := false) hτ'
    have hout' :
        (sigOut b).1.2.2.2.2.2 = trace2PlusOfFinset (α := α) (Uout b) := by
      have : (sig0 b).2.2.2.2.2 = trace2PlusOfFinset (α := α) (Uout b) := hout b hbFx
      simpa [sigOut] using this
    have : σOut.1.2.2.2.2.2 = trace2PlusOfFinset (α := α) (Uout b) := by
      simpa [hσ1] using hout'
    exact this.trans h2
  -- In `sigOutImage`, `t6OptionOfTrace5Plus` is `none` when `τ` is not `true`.
  have ht6_none_of_mem_TauNotTrue :
      ∀ {σOut : PerXSignatureOutMore α},
        σOut ∈ TauNotTrue → σOut.2.2 = none := by
    intro σOut hmem
    have hmem' :
        σOut ∈ sigOutImage ∧
          (match σOut.2.1 with
            | some (_t1, _t2, _t3, _t4, _t5, true) => False
            | _ => True) := by
      simpa [TauNotTrue] using hmem
    rcases Finset.mem_image.mp hmem'.1 with ⟨b, hbFx, hbEq⟩
    have hσ2 : (sigOut b).2.2 = σOut.2.2 :=
      congrArg (fun s : PerXSignatureOutMore α => s.2.2) hbEq
    have hστ : (sigOut b).2.1 = σOut.2.1 :=
      congrArg (fun s : PerXSignatureOutMore α => s.2.1) hbEq
    have hτb : trace5PlusOfFinset (α := α) (Uout b) = σOut.2.1 := by
      simpa [sigOut] using hστ
    -- Case split on `σOut.2.1`: it is either `none` or `some(...,false)`.
    cases hτ : σOut.2.1 with
    | none =>
        have : t6OptionOfTrace5Plus (α := α) (Uout b) = none := by
          -- `trace5Plus = none` forces `quintKey = none`, hence `t6Option = none`.
          -- Unfold and close by case splitting on `quintKeyOfFinset`.
          cases hq : quintKeyOfFinset (α := α) (Uout b) with
          | none =>
              simp [t6OptionOfTrace5Plus, hq]
          | some q =>
              -- If `quintKey` exists, then `trace5Plus` would be `some _`, contradicting `hτb`.
              have hτnone : trace5PlusOfFinset (α := α) (Uout b) = none := by
                simpa [hτ] using hτb
              have : False := by
                have hcontr :
                    (some
                          (q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2,
                            hasSixthOfFinset (α := α) (Uout b) q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) :
                        Option (α × α × α × α × α × Bool)) =
                      none := by
                  simpa [trace5PlusOfFinset, hq] using hτnone
                cases hcontr
              exact False.elim this
        have ht6 : t6OptionOfTrace5Plus (α := α) (Uout b) = σOut.2.2 := by
          simpa [sigOut, hτ] using congrArg (fun s : PerXSignatureOutMore α => s.2.2) hbEq
        simpa [ht6] using this
    | some sext =>
        rcases sext with ⟨t1, t2, t3, t4, t5, b6⟩
        cases b6 with
        | true =>
            -- `τ=true` is excluded by membership in `TauNotTrue`.
            exfalso
            exact (by simpa [hτ] using hmem'.2)
        | false =>
            have ht6opt :
                t6OptionOfTrace5Plus (α := α) (Uout b) = none := by
              -- From `trace5Plus = some(_,_,_,_,_,false)`, extract `quintKey` and `hasSixth=false`.
              have hτ' :
                  trace5PlusOfFinset (α := α) (Uout b) =
                    some (t1, t2, t3, t4, t5, false) := by
                simpa [hτ, hτb]
              cases hq : quintKeyOfFinset (α := α) (Uout b) with
              | none =>
                  have : (none : Option (α × α × α × α × α × Bool)) =
                        some (t1, t2, t3, t4, t5, false) := by
                    simpa [trace5PlusOfFinset, hq] using hτ'
                  cases this
              | some q =>
                  have hEq :
                      some
                          (q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2,
                            hasSixthOfFinset (α := α) (Uout b) q.1 q.2.1 q.2.2.1 q.2.2.2.1
                              q.2.2.2.2) =
                        some (t1, t2, t3, t4, t5, false) := by
                    simpa [trace5PlusOfFinset, hq] using hτ'
                  have h6tuple :
                      (q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2,
                          hasSixthOfFinset (α := α) (Uout b) q.1 q.2.1 q.2.2.1 q.2.2.2.1
                            q.2.2.2.2) =
                        (t1, t2, t3, t4, t5, false) :=
                    Option.some.inj hEq
                  have ht1 : q.1 = t1 := by
                    simpa using congrArg (fun p : α × α × α × α × α × Bool => p.1) h6tuple
                  have ht2 : q.2.1 = t2 := by
                    simpa using congrArg (fun p : α × α × α × α × α × Bool => p.2.1) h6tuple
                  have ht3 : q.2.2.1 = t3 := by
                    simpa using congrArg (fun p : α × α × α × α × α × Bool => p.2.2.1) h6tuple
                  have ht4 : q.2.2.2.1 = t4 := by
                    simpa using congrArg (fun p : α × α × α × α × α × Bool => p.2.2.2.1) h6tuple
                  have ht5 : q.2.2.2.2 = t5 := by
                    simpa using congrArg (fun p : α × α × α × α × α × Bool => p.2.2.2.2.1) h6tuple
                  have h6 :
                      hasSixthOfFinset (α := α) (Uout b) t1 t2 t3 t4 t5 = false := by
                    have h6' :
                        hasSixthOfFinset (α := α) (Uout b) q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 =
                          false := by
                      simpa using congrArg (fun p : α × α × α × α × α × Bool => p.2.2.2.2.2) h6tuple
                    simpa [ht1, ht2, ht3, ht4, ht5] using h6'
                  -- Now unfold `t6OptionOfTrace5Plus` and use `h6` to show `R.Nonempty` is false.
                  have hR :
                      ¬ ((((((Uout b).erase t1).erase t2).erase t3).erase t4).erase t5).Nonempty := by
                    have hRbool :
                        decide
                            ((((((Uout b).erase t1).erase t2).erase t3).erase t4).erase t5).Nonempty =
                          false := by
                      simpa [hasSixthOfFinset] using h6
                    intro hRne
                    have hRtrue :
                        decide
                            ((((((Uout b).erase t1).erase t2).erase t3).erase t4).erase t5).Nonempty =
                          true := by
                      simp [hRne]
                    have : (true : Bool) = false := by
                      simpa [hRtrue] using hRbool
                    cases this
                  -- Close by unfolding the `if` in `t6OptionOfTrace5Plus`.
                  have hq' : quintKeyOfFinset (α := α) (Uout b) = some (t1, t2, t3, t4, t5) := by
                    have hqEq : q = (t1, t2, t3, t4, t5) := by
                      ext <;> simp [ht1, ht2, ht3, ht4, ht5]
                    simpa [hqEq] using hq
                  -- Unfold with the computed quintKey; the remainder is not nonempty.
                  simp [t6OptionOfTrace5Plus, hq', hR]
            have ht6 : t6OptionOfTrace5Plus (α := α) (Uout b) = σOut.2.2 := by
              simpa [sigOut, hτ] using congrArg (fun s : PerXSignatureOutMore α => s.2.2) hbEq
            simpa [ht6] using ht6opt
  -- `h` is injective on `TauNotTrue`.
  have hf : ∀ σOut : PerXSignatureOutMore α, (h σOut).1 = σOut.1 := by
    intro σOut
    cases hτ : σOut.2.1 with
    | none =>
        simp [h, hτ]
    | some sext =>
        rcases sext with ⟨_t1, _t2, _t3, _t4, _t5, b⟩
        cases b <;> simp [h, hτ]
  have hinj : Set.InjOn h (↑TauNotTrue : Set (PerXSignatureOutMore α)) := by
    intro σ1 hσ1 σ2 hσ2 hEq
    have hσ1Fin : σ1 ∈ TauNotTrue := by simpa using hσ1
    have hσ2Fin : σ2 ∈ TauNotTrue := by simpa using hσ2
    have hσ1' :
        σ1 ∈ sigOutImage ∧
          (match σ1.2.1 with
            | some (_t1, _t2, _t3, _t4, _t5, true) => False
            | _ => True) := by
      simpa [TauNotTrue] using hσ1Fin
    have hσ2' :
        σ2 ∈ sigOutImage ∧
          (match σ2.2.1 with
            | some (_t1, _t2, _t3, _t4, _t5, true) => False
            | _ => True) := by
      simpa [TauNotTrue] using hσ2Fin
    have hmem1 : σ1 ∈ sigOutImage := hσ1'.1
    have hmem2 : σ2 ∈ sigOutImage := hσ2'.1
    have hSigEq : σ1.1 = σ2.1 := by
      have : (h σ1).1 = (h σ2).1 := congrArg (fun p => p.1) hEq
      simpa [hf σ1, hf σ2] using this
    have hTailEq : (h σ1).2 = (h σ2).2 := congrArg (fun p => p.2) hEq
    cases hτ1 : σ1.2.1 with
    | none =>
        -- Then `h σ1` has tail `none`, hence so does `h σ2`.
        have hTail1 : (h σ1).2 = none := by simp [h, hτ1]
        have hTail2 : (h σ2).2 = none := by simpa [hTail1] using hTailEq.symm
        -- So `σ2.2.1` cannot be `some(_,_,_,_,_,false)`; it must be `none`.
        cases hτ2 : σ2.2.1 with
        | none =>
            -- Conclude by extensionality; `t6Option` is forced to be `none` on `TauNotTrue`.
            have ht6_1 : σ1.2.2 = none := ht6_none_of_mem_TauNotTrue hσ1Fin
            have ht6_2 : σ2.2.2 = none := ht6_none_of_mem_TauNotTrue hσ2Fin
            apply Prod.ext
            · exact hSigEq
            ·
              apply Prod.ext
              · simpa [hτ1, hτ2]
              · simpa [ht6_1, ht6_2]
        | some sext2 =>
            rcases sext2 with ⟨t1, t2, t3, t4, t5, b2⟩
            cases b2 with
            | true =>
                -- Excluded by `TauNotTrue`.
                exfalso
                exact (by simpa [hτ2] using hσ2'.2)
            | false =>
                -- But then `(h σ2).2` would be `some _`, contradiction.
                have : (h σ2).2 = some (t3, (t4, t5)) := by simp [h, hτ2]
                simpa [this] using hTail2
    | some sext1 =>
        rcases sext1 with ⟨t1a, t2a, t3a, t4a, t5a, b1⟩
        cases b1 with
        | true =>
            exfalso
            exact (by simpa [hτ1] using hσ1'.2)
        | false =>
            have hTail1 : (h σ1).2 = some (t3a, (t4a, t5a)) := by
              simp [h, hτ1]
            have hTail2 : (h σ2).2 = some (t3a, (t4a, t5a)) := by
              simpa [hTail1] using hTailEq.symm
            -- Hence `σ2.2.1` must also be `some(_,_,_,_,_,false)`.
            cases hτ2 : σ2.2.1 with
            | none =>
                have : (h σ2).2 = none := by simp [h, hτ2]
                simpa [this] using hTail2
            | some sext2 =>
                rcases sext2 with ⟨t1b, t2b, t3b, t4b, t5b, b2⟩
                cases b2 with
                | true =>
                    exfalso
                    exact (by simpa [hτ2] using hσ2'.2)
                | false =>
                    -- Tail triple equality gives `t3,t4,t5` equal.
                    have htTail :
                        some (t3b, (t4b, t5b)) = some (t3a, (t4a, t5a)) := by
                      -- `h σ2` tail is `some(t3b,(t4b,t5b))`.
                      have : (h σ2).2 = some (t3b, (t4b, t5b)) := by simp [h, hτ2]
                      simpa [this] using hTail2
                    have ht3 : t3b = t3a := by
                      simpa using congrArg (fun p : α × (α × α) => p.1) (Option.some.inj htTail)
                    have ht4 : t4b = t4a := by
                      simpa using
                        congrArg (fun p : α × (α × α) => p.2.1) (Option.some.inj htTail)
                    have ht5 : t5b = t5a := by
                      simpa using
                        congrArg (fun p : α × (α × α) => p.2.2) (Option.some.inj htTail)
                    -- Head pair is pinned by `outsideTrace`, hence by `σ1.1 = σ2.1`.
                    have htHead1 :
                        σ1.1.2.2.2.2.2 = some (t1a, some t2a, true) :=
                      hout_head_false (σOut := σ1) (t1 := t1a) (t2 := t2a) (t3 := t3a) (t4 := t4a)
                        (t5 := t5a) hmem1 (by simpa [hτ1])
                    have htHead2 :
                        σ2.1.2.2.2.2.2 = some (t1b, some t2b, true) :=
                      hout_head_false (σOut := σ2) (t1 := t1b) (t2 := t2b) (t3 := t3b) (t4 := t4b)
                        (t5 := t5b) hmem2 (by simpa [hτ2])
                    -- Extract `t1a = t1b` and `t2a = t2b` from the equality of `outsideTrace`.
                    have ht1 : t1a = t1b := by
                      have hOutEq : σ1.1.2.2.2.2.2 = σ2.1.2.2.2.2.2 := by
                        simpa using congrArg (fun s : PerXSignature α => s.2.2.2.2.2) hSigEq
                      have hHeadEq : some (t1a, some t2a, true) = some (t1b, some t2b, true) := by
                        simpa [htHead1, htHead2] using hOutEq
                      simpa using
                        congrArg (fun p : α × Option α × Bool => p.1) (Option.some.inj hHeadEq)
                    have ht2 : t2a = t2b := by
                      have hOutEq : σ1.1.2.2.2.2.2 = σ2.1.2.2.2.2.2 := by
                        simpa using congrArg (fun s : PerXSignature α => s.2.2.2.2.2) hSigEq
                      have hHeadEq : some (t1a, some t2a, true) = some (t1b, some t2b, true) := by
                        simpa [htHead1, htHead2] using hOutEq
                      have ht2s : (some t2a : Option α) = some t2b :=
                        congrArg (fun p : α × Option α × Bool => p.2.1) (Option.some.inj hHeadEq)
                      exact Option.some.inj ht2s
                    have hτeq : σ1.2.1 = σ2.2.1 := by
                      simpa [hτ1, hτ2, ht1, ht2, ht3, ht4, ht5]
                    have ht6_1 : σ1.2.2 = none := ht6_none_of_mem_TauNotTrue hσ1Fin
                    have ht6_2 : σ2.2.2 = none := ht6_none_of_mem_TauNotTrue hσ2Fin
                    apply Prod.ext
                    · exact hSigEq
                    ·
                      apply Prod.ext
                      · exact hτeq
                      · simpa [ht6_1, ht6_2]
  -- Use injectivity to identify `TauNotTrue` with its image under `h`.
  have hcard_eq : (TauNotTrue.image h).card = TauNotTrue.card :=
    (Finset.card_image_iff (s := TauNotTrue) (f := h)).2 hinj
  have hsub : TauNotTrue.image h ⊆ Cod := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨σOut, hσOut, rfl⟩
    have hσOut' :
        σOut ∈ sigOutImage ∧
          (match σOut.2.1 with
            | some (_t1, _t2, _t3, _t4, _t5, true) => False
            | _ => True) := by
      simpa [TauNotTrue] using hσOut
    have hmem : σOut ∈ sigOutImage := hσOut'.1
    -- Unpack `σOut` as `sigOut b`.
    rcases Finset.mem_image.mp hmem with ⟨b, hbFx, hbEq⟩
    have hσ0 : sig0 b = σOut.1 := by
      simpa [sigOut] using congrArg (fun s : PerXSignatureOutMore α => s.1) hbEq
    have hs0Mem : σOut.1 ∈ sig0Image := by
      refine Finset.mem_image.mpr ?_
      exact ⟨b, hbFx, hσ0⟩
    -- Tail membership: either `none`, or `some(t3,(t4,t5)) ∈ optionOfFinset Trip`.
    cases hτ : σOut.2.1 with
    | none =>
        have hTail : (h σOut).2 = none := by simp [h, hτ]
        have hTailMem : (none : Option (α × (α × α))) ∈ Tail := by
          simp [Tail, optionOfFinset]
        have : (σOut.1, (none : Option (α × (α × α)))) ∈ Cod :=
          Finset.mem_product.mpr ⟨hs0Mem, hTailMem⟩
        simpa [h, hτ] using this
    | some sext =>
        rcases sext with ⟨t1, t2, t3, t4, t5, b6⟩
        cases b6 with
        | true =>
            exfalso
            exact (by simpa [hτ] using hσOut'.2)
        | false =>
            -- `t3,t4,t5 ∈ ground` since `Uout b ⊆ ground` and `Uout b = {t1..t5}`.
            have hτb :
                trace5PlusOfFinset (α := α) (Uout b) =
                  some (t1, t2, t3, t4, t5, false) := by
              have : trace5PlusOfFinset (α := α) (Uout b) = σOut.2.1 := by
                simpa [sigOut] using congrArg (fun s : PerXSignatureOutMore α => s.2.1) hbEq
              simpa [hτ] using this
            have hUeq : Uout b = ({t1, t2, t3, t4, t5} : Finset α) :=
              eq_quint_of_trace5PlusOfFinset_eq_some_false (α := α) (T := Uout b) (t1 := t1)
                (t2 := t2) (t3 := t3) (t4 := t4) (t5 := t5) hτb
            have ht3G : t3 ∈ ground := (hUsub b hbFx) (by simpa [hUeq] using
              (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self t3
                ({t4, t5} : Finset α)))))
            have ht4G : t4 ∈ ground := (hUsub b hbFx) (by simpa [hUeq] using
              (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
                (Finset.mem_insert_self t4 ({t5} : Finset α))))))
            have ht5G : t5 ∈ ground := (hUsub b hbFx) (by simpa [hUeq] using
              (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
                (Finset.mem_insert_of_mem (Finset.mem_singleton_self t5))))))
            have hTripMem : (t3, (t4, t5)) ∈ Trip := by
              refine Finset.mem_product.mpr ?_
              refine ⟨ht3G, ?_⟩
              refine Finset.mem_product.mpr ?_
              exact ⟨ht4G, ht5G⟩
            have hTailMem : some (t3, (t4, t5)) ∈ Tail := by
              refine Finset.mem_insert_of_mem ?_
              refine Finset.mem_image.mpr ?_
              exact ⟨(t3, (t4, t5)), hTripMem, rfl⟩
            have : (σOut.1, some (t3, (t4, t5))) ∈ Cod :=
              Finset.mem_product.mpr ⟨hs0Mem, hTailMem⟩
            simpa [h, hτ] using this
  have hcard_le : TauNotTrue.card ≤ Cod.card := by
    have himg_le : (TauNotTrue.image h).card ≤ Cod.card :=
      Finset.card_le_card hsub
    simpa [hcard_eq] using himg_le
  -- Bound `Cod.card` by `sig0Image.card * (n^3 + 1)`.
  have hCod :
      Cod.card ≤ sig0Image.card * ((ground.card ^ 3) + 1) := by
    have hTail : Tail.card ≤ (ground.card ^ 3) + 1 := by
      have hTrip : Trip.card = ground.card ^ 3 := by
        simp [Trip, Finset.card_product, pow_succ, pow_two, Nat.mul_assoc, Nat.mul_left_comm,
          Nat.mul_comm]
      have hTail' : Tail.card ≤ Trip.card + 1 :=
        card_optionOfFinset_le_succ (α := α × (α × α)) Trip
      simpa [hTrip, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hTail'
    have hCodEq : Cod.card = sig0Image.card * Tail.card := by
      simpa [Cod, Finset.card_product]
    calc
      Cod.card = sig0Image.card * Tail.card := hCodEq
      _ ≤ sig0Image.card * ((ground.card ^ 3) + 1) := Nat.mul_le_mul_left _ hTail
  exact le_trans hcard_le hCod

theorem card_Fx_eq_sum_card_Bucket_perXSignatureOutMore_of_hardFiber
    (hreg : O1aUpgradeRegime family ground A0 h0)
    {k : WLcertKey α}
    {Sstar : {S // S ∈ o1aWitnessLiftDomWL family h0}}
    {x : α}
    (hSstar :
      Sstar ∈ wlcertAdmissibleFiber_hNotMem (family := family) (o1aWitnessLiftDomWL family h0) k) :
    let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h0
    let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
    let Fx0 :
        Finset {S // S ∈ dom} :=
      wlcertAdmissibleFiber_hNotMem_fiberForX (dom := dom) fiber Sstar.1 x
    let sig0 : {Ssub // Ssub ∈ Fx0} → PerXSignature α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      perXSignature_of_hardFiber (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1) Sstar.2 b.1.2 hcert_star hcert_sub hne
    let Uout : {Ssub // Ssub ∈ Fx0} → Finset α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      let yw :
          Σ y : α, BlockedUnionWitness family b.1.1 y :=
        chooseYAndWitness_of_hardFiber
          (family := family) (ground := ground) (A0 := A0) (h0 := h0)
          hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
          Sstar.2 b.1.2 hcert_star hcert_sub hne
      b.1.1 \ (yw.2.A ∪ yw.2.B)
    let sigOut : {Ssub // Ssub ∈ Fx0} → PerXSignatureOutMore α := fun b =>
      (sig0 b,
        trace5PlusOfFinset (α := α) (Uout b),
        t6OptionOfTrace5Plus (α := α) (Uout b))
    Fx0.card = ∑ σ ∈ Fx0.attach.image sigOut, (Bucket (Fx := Fx0.attach) sigOut σ).card := by
  classical
  intro dom fiber Fx0 sig0 Uout sigOut
  -- Generic bucket-sum formula on `Fx0.attach` for the extended signature `sigOut`.
  have hsum :
      Fx0.attach.card = ∑ σ ∈ Fx0.attach.image sigOut, (Bucket (Fx := Fx0.attach) sigOut σ).card :=
    card_Fx_eq_sum_card_Bucket (Fx := Fx0.attach) sigOut
  simpa using hsum

theorem card_image_perXSignature_of_hardFiber_le_card_traceCod_pow_five
    (hreg : O1aUpgradeRegime family ground A0 h0)
    {k : WLcertKey α}
    {Sstar : {S // S ∈ o1aWitnessLiftDomWL family h0}}
    {x : α}
    (hSstar :
      Sstar ∈ wlcertAdmissibleFiber_hNotMem (family := family) (o1aWitnessLiftDomWL family h0) k) :
    let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h0
    let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
    let Fx0 :
        Finset {S // S ∈ dom} :=
      wlcertAdmissibleFiber_hNotMem_fiberForX (dom := dom) fiber Sstar.1 x
    let sig0 : {Ssub // Ssub ∈ Fx0} → PerXSignature α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      perXSignature_of_hardFiber (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1) Sstar.2 b.1.2 hcert_star hcert_sub hne
    (Fx0.attach.image sig0).card ≤ ground.card * (traceCod (α := α) ground).card ^ 5 := by
  classical
  intro dom fiber Fx0 sig0
  -- Apply the generic signature-range bound once we show the head `y` lies in `ground`
  -- and each trace component lives in `traceCod ground`.
  refine
    card_image_sig0_le_card_traceCod_pow_five (α := α) (Fx := Fx0.attach) (ground := ground)
      (sig0 := sig0) ?_ ?_
  · intro b hbFx
    -- Relate the `y` component of `sig0 b` to the canonical `chooseMissingFromRef`.
    have hcert_star :
        ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
      (Finset.mem_filter.mp hSstar).2
    have hbFiber : b.1 ∈ fiber := (Finset.mem_filter.mp b.2).1
    have hcert_sub :
        ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
      (Finset.mem_filter.mp hbFiber).2
    have hne : b.1.1 ≠ Sstar.1 :=
      PerXSubfiber.ne_Sstar_val_of_mem_fiberForX
        (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
        (Ssub := b.1) b.2
    let yCh : α :=
      chooseMissingFromRef (family := family) (h0 := h0) Sstar.1 b.1.1 Sstar.2 b.1.2 hne
    have hyChSig0 : (sig0 b).1 = yCh := by
      simp [sig0, perXSignature_of_hardFiber, perXSignature, chooseYAndWitness_of_hardFiber, yCh]
    have hyX' :
        yCh ∈ (ground \ (k.2.2.1 ∪ k.2.2.2.1)) := by
      simpa [yCh] using
        (chooseMissingFromRef_mem_X_of_hardFiber (family := family) (ground := ground) (A0 := A0)
          (h0 := h0) hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
          Sstar.2 b.1.2 hcert_star hcert_sub hne)
    have hyGround : yCh ∈ ground := (Finset.mem_sdiff.mp hyX').1
    simpa [hyChSig0] using hyGround
  · intro b hbFx
    -- Unpack the canonical `y` and normalized witness used in `sig0 b`.
    have hcert_star :
        ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
      (Finset.mem_filter.mp hSstar).2
    have hbFiber : b.1 ∈ fiber := (Finset.mem_filter.mp b.2).1
    have hcert_sub :
        ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
      (Finset.mem_filter.mp hbFiber).2
    have hne : b.1.1 ≠ Sstar.1 :=
      PerXSubfiber.ne_Sstar_val_of_mem_fiberForX
        (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
        (Ssub := b.1) b.2
    let yw :
        Σ y : α, BlockedUnionWitness family b.1.1 y :=
      chooseYAndWitness_of_hardFiber
        (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
        Sstar.2 b.1.2 hcert_star hcert_sub hne
    have hyw :
        chooseYAndWitness_of_hardFiber
            (family := family) (ground := ground) (A0 := A0) (h0 := h0)
            hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
            Sstar.2 b.1.2 hcert_star hcert_sub hne = yw := by
      rfl
    -- Subset facts: `S ⊆ ground` and `A,B ⊆ ground` since `family ⊆ ground.powerset`.
    have hSfam : b.1.1 ∈ family :=
      mem_family_of_mem_o1aWitnessLiftDomWL (family := family) (h0 := h0) (S := b.1.1) b.1.2
    have hSsub : b.1.1 ⊆ ground := Finset.mem_powerset.mp (hreg.1 hSfam)
    have hAsub : yw.2.A ⊆ ground := Finset.mem_powerset.mp (hreg.1 yw.2.hA)
    have hBsub : yw.2.B ⊆ ground := Finset.mem_powerset.mp (hreg.1 yw.2.hB)
    have hcoreSubA : yw.2.core ⊆ yw.2.A := by
      intro a ha
      have : a ∈ yw.2.A ∩ yw.2.B := by simpa [yw.2.hcoreAB] using ha
      exact (Finset.mem_inter.mp this).1
    have hcoreEraseSub : yw.2.core.erase yw.1 ⊆ ground := by
      intro a ha
      have haCore : a ∈ yw.2.core := (Finset.mem_erase.mp ha).2
      have haA : a ∈ yw.2.A := hcoreSubA haCore
      exact hAsub haA
    have hrABSub :
        rAB (family := family) (k := k) (S := b.1.1) (y := yw.1) yw.2 ⊆ ground := by
      intro a ha
      have haCoreErase :
          a ∈ yw.2.core.erase yw.1 := by
        -- Avoid `simp` rewriting membership into nested `And`/`Or`; unpack `rAB` as an intersection.
        have ha' :
            a ∈ (yw.2.core.erase yw.1) ∩ (k.2.2.1 ∪ k.2.2.2.1) := by
          simpa [rAB] using ha
        exact (Finset.mem_inter.mp ha').1
      exact hcoreEraseSub haCoreErase
    have hExtrasSub : yw.2.A \ insert yw.1 b.1.1 ⊆ ground := by
      intro a ha
      have haA : a ∈ yw.2.A := (Finset.mem_sdiff.mp ha).1
      exact hAsub haA
    have hBExtrasSub : yw.2.B \ insert yw.1 b.1.1 ⊆ ground := by
      intro a ha
      have haB : a ∈ yw.2.B := (Finset.mem_sdiff.mp ha).1
      exact hBsub haB
    have hOutsideSub : b.1.1 \ (yw.2.A ∪ yw.2.B) ⊆ ground := by
      intro a ha
      have haS : a ∈ b.1.1 := (Finset.mem_sdiff.mp ha).1
      exact hSsub haS
    -- Now show each trace component lies in `traceCod ground` via subset witnesses.
    have ht1 :
        trace2PlusOfFinset (α := α)
            (rAB (family := family) (k := k) (S := b.1.1) (y := yw.1) yw.2) ∈
          traceCod (α := α) ground :=
      mem_traceCod_of_trace2PlusOfFinset_of_subset (α := α) (ground := ground) hrABSub
    have ht2 :
        trace2PlusOfFinset (α := α) (yw.2.A \ insert yw.1 b.1.1) ∈ traceCod (α := α) ground :=
      mem_traceCod_of_trace2PlusOfFinset_of_subset (α := α) (ground := ground) hExtrasSub
    have ht3 :
        trace2PlusOfFinset (α := α) (yw.2.core.erase yw.1) ∈ traceCod (α := α) ground :=
      mem_traceCod_of_trace2PlusOfFinset_of_subset (α := α) (ground := ground) hcoreEraseSub
    have ht4 :
        trace2PlusOfFinset (α := α) (yw.2.B \ insert yw.1 b.1.1) ∈ traceCod (α := α) ground :=
      mem_traceCod_of_trace2PlusOfFinset_of_subset (α := α) (ground := ground) hBExtrasSub
    have ht5 :
        trace2PlusOfFinset (α := α) (b.1.1 \ (yw.2.A ∪ yw.2.B)) ∈ traceCod (α := α) ground :=
      mem_traceCod_of_trace2PlusOfFinset_of_subset (α := α) (ground := ground) hOutsideSub
    -- Transport these to the corresponding components of `sig0 b`.
    refine ⟨?_, ?_⟩
    ·
      simpa [sig0, perXSignature_of_hardFiber, perXSignature, rABTrace, hyw] using ht1
    refine ⟨?_, ?_⟩
    ·
      simpa [sig0, perXSignature_of_hardFiber, perXSignature, hyw,
        tx2PlusOfWitness_eq_trace2PlusOfFinset_extras] using ht2
    refine ⟨?_, ?_⟩
    ·
      simpa [sig0, perXSignature_of_hardFiber, perXSignature, hyw] using ht3
    refine ⟨?_, ?_⟩
    ·
      simpa [sig0, perXSignature_of_hardFiber, perXSignature, bTrace, hyw] using ht4
    ·
      simpa [sig0, perXSignature_of_hardFiber, perXSignature, outsideTrace, hyw] using ht5

/-
Per-`x` bucket caps for the extended outMore signature.

We start with the easy “|Uout| = 5” case: when `trace5Plus(Uout) = some(t1..t5,false)`,
the outside part `Uout` is **exactly** `{t1..t5}`. If, additionally, the core trace is rigid
(`coreTrace.hasMore = false`), then the completion is uniquely determined by the decomposition
`S = coreErase ∪ Uout`, so the bucket has card ≤ 1.

This lemma is a small, self-contained building block for the outMore per-`x` ledger.
-/

theorem eq_keyBase_union_X_erase_of_X_sdiff_eq_singleton
    (hreg : O1aUpgradeRegime family ground A0 h0)
    {k : WLcertKey α} {S : Finset α}
    (hSdom : S ∈ o1aWitnessLiftDomWL family h0)
    (hcert : ∃ cert : WLcert family S, WLcert.key cert = k ∧ cert.h ∉ S)
    {y : α}
    (hXsdiff : (ground \ (k.2.2.1 ∪ k.2.2.2.1)) \ S = ({y} : Finset α)) :
    let X : Finset α := ground \ (k.2.2.1 ∪ k.2.2.2.1)
    S = PerXSubfiber.keyBase (α := α) (k := k) ∪ (X.erase y) := by
  classical
  intro X
  -- Hard-branch reduction facts for `S`.
  have htr :=
    (wlcert_hNotMem_reduction_o1aDomWL (family := family) (ground := ground) (A0 := A0) (h0 := h0)
      hreg (k := k) (S := S) hSdom hcert)
  have hSoutSub : S \ (k.2.2.1 ∪ k.2.2.2.1) ⊆ X := by simpa [X] using htr.2.2.2.1
  have hSdecomp : S = PerXSubfiber.keyBase (α := α) (k := k) ∪ (S \ (k.2.2.1 ∪ k.2.2.2.1)) := by
    simpa [PerXSubfiber.keyBase] using htr.2.2.2.2.1
  -- From `X \\ S = {y}`, we get `y ∈ X` and `y ∉ S`.
  have hyMem : y ∈ X \ S := by
    -- Rewrite first so simp doesn't expand `mem_sdiff` too early.
    rw [hXsdiff]
    simpa using (Finset.mem_singleton_self y)
  have hyX : y ∈ X := (Finset.mem_sdiff.mp hyMem).1
  have hyNot : y ∉ S := (Finset.mem_sdiff.mp hyMem).2
  -- Identify the outside part `S \\ (kA ∪ kB)` with `X.erase y`.
  have hSub1 : S \ (k.2.2.1 ∪ k.2.2.2.1) ⊆ X.erase y := by
    intro z hz
    have hzX : z ∈ X := hSoutSub hz
    have hzS : z ∈ S := (Finset.mem_sdiff.mp hz).1
    have hzNe : z ≠ y := by
      intro hzy
      subst hzy
      exact hyNot hzS
    exact Finset.mem_erase.mpr ⟨hzNe, hzX⟩
  have hSub2 : X.erase y ⊆ S \ (k.2.2.1 ∪ k.2.2.2.1) := by
    intro z hz
    have hzNe : z ≠ y := (Finset.mem_erase.mp hz).1
    have hzX : z ∈ X := (Finset.mem_erase.mp hz).2
    have hzS : z ∈ S := by
      by_contra hzS
      have hzXS : z ∈ X \ S := Finset.mem_sdiff.mpr ⟨hzX, hzS⟩
      have : z ∈ ({y} : Finset α) := by
        -- Rewrite the singleton goal back to `X \\ S` (no `simp` on membership) and close by `hzXS`.
        rw [← hXsdiff]
        simpa [X] using hzXS
      exact hzNe (by simpa using (Finset.mem_singleton.mp this))
    have hzNotAB : z ∉ (k.2.2.1 ∪ k.2.2.2.1) := (Finset.mem_sdiff.mp hzX).2
    exact Finset.mem_sdiff.mpr ⟨hzS, hzNotAB⟩
  have hEqOut : S \ (k.2.2.1 ∪ k.2.2.2.1) = X.erase y :=
    Finset.Subset.antisymm hSub1 hSub2
  -- Substitute into the reduction decomposition.
  simpa [hEqOut] using hSdecomp

theorem eq_keyBase_union_X_erase_erase_of_X_sdiff_eq_pair
    (hreg : O1aUpgradeRegime family ground A0 h0)
    {k : WLcertKey α} {S : Finset α}
    (hSdom : S ∈ o1aWitnessLiftDomWL family h0)
    (hcert : ∃ cert : WLcert family S, WLcert.key cert = k ∧ cert.h ∉ S)
    {y1 y2 : α}
    (hXsdiff : (ground \ (k.2.2.1 ∪ k.2.2.2.1)) \ S = ({y1, y2} : Finset α)) :
    let X : Finset α := ground \ (k.2.2.1 ∪ k.2.2.2.1)
    S = PerXSubfiber.keyBase (α := α) (k := k) ∪ ((X.erase y1).erase y2) := by
  classical
  intro X
  -- Hard-branch reduction facts for `S`.
  have htr :=
    (wlcert_hNotMem_reduction_o1aDomWL (family := family) (ground := ground) (A0 := A0) (h0 := h0)
      hreg (k := k) (S := S) hSdom hcert)
  have hSoutSub : S \ (k.2.2.1 ∪ k.2.2.2.1) ⊆ X := by simpa [X] using htr.2.2.2.1
  have hSdecomp : S = PerXSubfiber.keyBase (α := α) (k := k) ∪ (S \ (k.2.2.1 ∪ k.2.2.2.1)) := by
    simpa [PerXSubfiber.keyBase] using htr.2.2.2.2.1
  -- From `X \\ S = {y1,y2}`, both `y1` and `y2` lie in `X \\ S`.
  have hy1Mem : y1 ∈ X \ S := by
    rw [hXsdiff]
    simpa using (Finset.mem_insert_self y1 ({y2} : Finset α))
  have hy2Mem : y2 ∈ X \ S := by
    rw [hXsdiff]
    by_cases hEq : y2 = y1
    · subst hEq
      simpa using (Finset.mem_insert_self y1 ({y2} : Finset α))
    · have : y2 ∈ ({y2} : Finset α) := by simpa using (Finset.mem_singleton_self y2)
      simpa using (Finset.mem_insert_of_mem this)
  have hy1X : y1 ∈ X := (Finset.mem_sdiff.mp hy1Mem).1
  have hy1Not : y1 ∉ S := (Finset.mem_sdiff.mp hy1Mem).2
  have hy2X : y2 ∈ X := (Finset.mem_sdiff.mp hy2Mem).1
  have hy2Not : y2 ∉ S := (Finset.mem_sdiff.mp hy2Mem).2
  -- Identify the outside part `S \\ (kA ∪ kB)` with `X.erase y1.erase y2`.
  have hSub1 : S \ (k.2.2.1 ∪ k.2.2.2.1) ⊆ (X.erase y1).erase y2 := by
    intro z hz
    have hzX : z ∈ X := hSoutSub hz
    have hzS : z ∈ S := (Finset.mem_sdiff.mp hz).1
    have hzNe1 : z ≠ y1 := by
      intro hzy
      subst hzy
      exact hy1Not hzS
    have hzNe2 : z ≠ y2 := by
      intro hzy
      subst hzy
      exact hy2Not hzS
    refine Finset.mem_erase.mpr ?_
    refine ⟨hzNe2, ?_⟩
    exact Finset.mem_erase.mpr ⟨hzNe1, hzX⟩
  have hSub2 : (X.erase y1).erase y2 ⊆ S \ (k.2.2.1 ∪ k.2.2.2.1) := by
    intro z hz
    have hzNe2 : z ≠ y2 := (Finset.mem_erase.mp hz).1
    have hzX1 : z ∈ X.erase y1 := (Finset.mem_erase.mp hz).2
    have hzNe1 : z ≠ y1 := (Finset.mem_erase.mp hzX1).1
    have hzX : z ∈ X := (Finset.mem_erase.mp hzX1).2
    have hzS : z ∈ S := by
      by_contra hzS
      have hzXS : z ∈ X \ S := Finset.mem_sdiff.mpr ⟨hzX, hzS⟩
      have : z ∈ ({y1, y2} : Finset α) := by
        -- Rewrite the goal back to `X \\ S` and close by `hzXS`.
        rw [← hXsdiff]
        simpa [X] using hzXS
      -- Contradict membership in `{y1,y2}` using `z ≠ y1` and `z ≠ y2`.
      have : z = y1 ∨ z = y2 := by
        simpa using (Finset.mem_insert.mp this)
      rcases this with hEq | hEq
      · exact hzNe1 hEq
      · exact hzNe2 hEq
    have hzNotAB : z ∉ (k.2.2.1 ∪ k.2.2.2.1) := (Finset.mem_sdiff.mp hzX).2
    exact Finset.mem_sdiff.mpr ⟨hzS, hzNotAB⟩
  have hEqOut : S \ (k.2.2.1 ∪ k.2.2.2.1) = (X.erase y1).erase y2 :=
    Finset.Subset.antisymm hSub1 hSub2
  simpa [hEqOut] using hSdecomp

theorem eq_keyBase_union_X_erase_erase_erase_of_X_sdiff_eq_triple
    (hreg : O1aUpgradeRegime family ground A0 h0)
    {k : WLcertKey α} {S : Finset α}
    (hSdom : S ∈ o1aWitnessLiftDomWL family h0)
    (hcert : ∃ cert : WLcert family S, WLcert.key cert = k ∧ cert.h ∉ S)
    {y1 y2 y3 : α}
    (hXsdiff : (ground \ (k.2.2.1 ∪ k.2.2.2.1)) \ S = ({y1, y2, y3} : Finset α)) :
    let X : Finset α := ground \ (k.2.2.1 ∪ k.2.2.2.1)
    S = PerXSubfiber.keyBase (α := α) (k := k) ∪ (((X.erase y1).erase y2).erase y3) := by
  classical
  intro X
  -- Hard-branch reduction facts for `S`.
  have htr :=
    (wlcert_hNotMem_reduction_o1aDomWL (family := family) (ground := ground) (A0 := A0) (h0 := h0)
      hreg (k := k) (S := S) hSdom hcert)
  have hSoutSub : S \ (k.2.2.1 ∪ k.2.2.2.1) ⊆ X := by simpa [X] using htr.2.2.2.1
  have hSdecomp : S = PerXSubfiber.keyBase (α := α) (k := k) ∪ (S \ (k.2.2.1 ∪ k.2.2.2.1)) := by
    simpa [PerXSubfiber.keyBase] using htr.2.2.2.2.1
  -- From `X \\ S = {y1,y2,y3}`, each `yi` lies in `X \\ S`.
  have hy1Mem : y1 ∈ X \ S := by
    rw [hXsdiff]
    simpa using (Finset.mem_insert_self y1 ({y2, y3} : Finset α))
  have hy2Mem : y2 ∈ X \ S := by
    rw [hXsdiff]
    by_cases hEq : y2 = y1
    · subst hEq
      simpa using (Finset.mem_insert_self y1 ({y2, y3} : Finset α))
    · have : y2 ∈ ({y2, y3} : Finset α) := by
        simpa using (Finset.mem_insert_self y2 ({y3} : Finset α))
      simpa using (Finset.mem_insert_of_mem this)
  have hy3Mem : y3 ∈ X \ S := by
    rw [hXsdiff]
    by_cases hEq3 : y3 = y1
    · subst hEq3
      simpa using (Finset.mem_insert_self y1 ({y2, y3} : Finset α))
    · have : y3 ∈ ({y2, y3} : Finset α) := by
        by_cases hEq32 : y3 = y2
        · subst hEq32
          simpa using (Finset.mem_insert_self y2 ({y3} : Finset α))
        · have : y3 ∈ ({y3} : Finset α) := by simpa using (Finset.mem_singleton_self y3)
          simpa using (Finset.mem_insert_of_mem this)
      simpa using (Finset.mem_insert_of_mem this)
  have hy1X : y1 ∈ X := (Finset.mem_sdiff.mp hy1Mem).1
  have hy1Not : y1 ∉ S := (Finset.mem_sdiff.mp hy1Mem).2
  have hy2X : y2 ∈ X := (Finset.mem_sdiff.mp hy2Mem).1
  have hy2Not : y2 ∉ S := (Finset.mem_sdiff.mp hy2Mem).2
  have hy3X : y3 ∈ X := (Finset.mem_sdiff.mp hy3Mem).1
  have hy3Not : y3 ∉ S := (Finset.mem_sdiff.mp hy3Mem).2
  -- Identify the outside part `S \\ (kA ∪ kB)` with `X.erase y1.erase y2.erase y3`.
  have hSub1 : S \ (k.2.2.1 ∪ k.2.2.2.1) ⊆ ((X.erase y1).erase y2).erase y3 := by
    intro z hz
    have hzX : z ∈ X := hSoutSub hz
    have hzS : z ∈ S := (Finset.mem_sdiff.mp hz).1
    have hzNe1 : z ≠ y1 := by
      intro hzy
      subst hzy
      exact hy1Not hzS
    have hzNe2 : z ≠ y2 := by
      intro hzy
      subst hzy
      exact hy2Not hzS
    have hzNe3 : z ≠ y3 := by
      intro hzy
      subst hzy
      exact hy3Not hzS
    refine Finset.mem_erase.mpr ?_
    refine ⟨hzNe3, ?_⟩
    refine Finset.mem_erase.mpr ?_
    refine ⟨hzNe2, ?_⟩
    exact Finset.mem_erase.mpr ⟨hzNe1, hzX⟩
  have hSub2 : ((X.erase y1).erase y2).erase y3 ⊆ S \ (k.2.2.1 ∪ k.2.2.2.1) := by
    intro z hz
    have hzNe3 : z ≠ y3 := (Finset.mem_erase.mp hz).1
    have hz12 : z ∈ (X.erase y1).erase y2 := (Finset.mem_erase.mp hz).2
    have hzNe2 : z ≠ y2 := (Finset.mem_erase.mp hz12).1
    have hz1 : z ∈ X.erase y1 := (Finset.mem_erase.mp hz12).2
    have hzNe1 : z ≠ y1 := (Finset.mem_erase.mp hz1).1
    have hzX : z ∈ X := (Finset.mem_erase.mp hz1).2
    have hzS : z ∈ S := by
      by_contra hzS
      have hzXS : z ∈ X \ S := Finset.mem_sdiff.mpr ⟨hzX, hzS⟩
      have : z ∈ ({y1, y2, y3} : Finset α) := by
        rw [← hXsdiff]
        simpa [X] using hzXS
      have : z = y1 ∨ z = y2 ∨ z = y3 := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using this
      rcases this with rfl | h'
      · exact hzNe1 rfl
      rcases h' with rfl | rfl
      · exact hzNe2 rfl
      · exact hzNe3 rfl
    have hzNotAB : z ∉ (k.2.2.1 ∪ k.2.2.2.1) := (Finset.mem_sdiff.mp hzX).2
    exact Finset.mem_sdiff.mpr ⟨hzS, hzNotAB⟩
  have hEqOut : S \ (k.2.2.1 ∪ k.2.2.2.1) = ((X.erase y1).erase y2).erase y3 :=
    Finset.Subset.antisymm hSub1 hSub2
  simpa [hEqOut] using hSdecomp

theorem eq_keyBase_union_X_erase_erase_erase_erase_of_X_sdiff_eq_quad
    (hreg : O1aUpgradeRegime family ground A0 h0)
    {k : WLcertKey α} {S : Finset α}
    (hSdom : S ∈ o1aWitnessLiftDomWL family h0)
    (hcert : ∃ cert : WLcert family S, WLcert.key cert = k ∧ cert.h ∉ S)
    {y1 y2 y3 y4 : α}
    (hXsdiff : (ground \ (k.2.2.1 ∪ k.2.2.2.1)) \ S = ({y1, y2, y3, y4} : Finset α)) :
    let X : Finset α := ground \ (k.2.2.1 ∪ k.2.2.2.1)
    S = PerXSubfiber.keyBase (α := α) (k := k) ∪ ((((X.erase y1).erase y2).erase y3).erase y4) := by
  classical
  intro X
  have htr :=
    (wlcert_hNotMem_reduction_o1aDomWL (family := family) (ground := ground) (A0 := A0) (h0 := h0)
      hreg (k := k) (S := S) hSdom hcert)
  have hSoutSub : S \ (k.2.2.1 ∪ k.2.2.2.1) ⊆ X := by simpa [X] using htr.2.2.2.1
  have hSdecomp : S = PerXSubfiber.keyBase (α := α) (k := k) ∪ (S \ (k.2.2.1 ∪ k.2.2.2.1)) := by
    simpa [PerXSubfiber.keyBase] using htr.2.2.2.2.1
  have hy1Mem : y1 ∈ X \ S := by
    rw [hXsdiff]
    simpa using (Finset.mem_insert_self y1 ({y2, y3, y4} : Finset α))
  have hy2Mem : y2 ∈ X \ S := by
    rw [hXsdiff]
    by_cases hEq : y2 = y1
    · subst hEq
      simpa using (Finset.mem_insert_self y1 ({y2, y3, y4} : Finset α))
    · have : y2 ∈ ({y2, y3, y4} : Finset α) := by
        simpa using (Finset.mem_insert_self y2 ({y3, y4} : Finset α))
      simpa using (Finset.mem_insert_of_mem this)
  have hy3Mem : y3 ∈ X \ S := by
    rw [hXsdiff]
    by_cases hEq3 : y3 = y1
    · subst hEq3
      simpa using (Finset.mem_insert_self y1 ({y2, y3, y4} : Finset α))
    · have : y3 ∈ ({y2, y3, y4} : Finset α) := by
        by_cases hEq32 : y3 = y2
        · subst hEq32
          simpa using (Finset.mem_insert_self y2 ({y3, y4} : Finset α))
        · have : y3 ∈ ({y3, y4} : Finset α) := by
            simpa using (Finset.mem_insert_self y3 ({y4} : Finset α))
          simpa using (Finset.mem_insert_of_mem this)
      simpa using (Finset.mem_insert_of_mem this)
  have hy4Mem : y4 ∈ X \ S := by
    rw [hXsdiff]
    simp
  have hy1X : y1 ∈ X := (Finset.mem_sdiff.mp hy1Mem).1
  have hy1Not : y1 ∉ S := (Finset.mem_sdiff.mp hy1Mem).2
  have hy2X : y2 ∈ X := (Finset.mem_sdiff.mp hy2Mem).1
  have hy2Not : y2 ∉ S := (Finset.mem_sdiff.mp hy2Mem).2
  have hy3X : y3 ∈ X := (Finset.mem_sdiff.mp hy3Mem).1
  have hy3Not : y3 ∉ S := (Finset.mem_sdiff.mp hy3Mem).2
  have hy4X : y4 ∈ X := (Finset.mem_sdiff.mp hy4Mem).1
  have hy4Not : y4 ∉ S := (Finset.mem_sdiff.mp hy4Mem).2
  have hSub1 : S \ (k.2.2.1 ∪ k.2.2.2.1) ⊆ (((X.erase y1).erase y2).erase y3).erase y4 := by
    intro z hz
    have hzX : z ∈ X := hSoutSub hz
    have hzS : z ∈ S := (Finset.mem_sdiff.mp hz).1
    have hzNe1 : z ≠ y1 := by
      intro hzy
      subst hzy
      exact hy1Not hzS
    have hzNe2 : z ≠ y2 := by
      intro hzy
      subst hzy
      exact hy2Not hzS
    have hzNe3 : z ≠ y3 := by
      intro hzy
      subst hzy
      exact hy3Not hzS
    have hzNe4 : z ≠ y4 := by
      intro hzy
      subst hzy
      exact hy4Not hzS
    refine Finset.mem_erase.mpr ?_
    refine ⟨hzNe4, ?_⟩
    refine Finset.mem_erase.mpr ?_
    refine ⟨hzNe3, ?_⟩
    refine Finset.mem_erase.mpr ?_
    refine ⟨hzNe2, ?_⟩
    exact Finset.mem_erase.mpr ⟨hzNe1, hzX⟩
  have hSub2 : (((X.erase y1).erase y2).erase y3).erase y4 ⊆ S \ (k.2.2.1 ∪ k.2.2.2.1) := by
    intro z hz
    have hzNe4 : z ≠ y4 := (Finset.mem_erase.mp hz).1
    have hz123 : z ∈ ((X.erase y1).erase y2).erase y3 := (Finset.mem_erase.mp hz).2
    have hzNe3 : z ≠ y3 := (Finset.mem_erase.mp hz123).1
    have hz12 : z ∈ (X.erase y1).erase y2 := (Finset.mem_erase.mp hz123).2
    have hzNe2 : z ≠ y2 := (Finset.mem_erase.mp hz12).1
    have hz1 : z ∈ X.erase y1 := (Finset.mem_erase.mp hz12).2
    have hzNe1 : z ≠ y1 := (Finset.mem_erase.mp hz1).1
    have hzX : z ∈ X := (Finset.mem_erase.mp hz1).2
    have hzS : z ∈ S := by
      by_contra hzS
      have hzXS : z ∈ X \ S := Finset.mem_sdiff.mpr ⟨hzX, hzS⟩
      have : z ∈ ({y1, y2, y3, y4} : Finset α) := by
        rw [← hXsdiff]
        simpa [X] using hzXS
      have : z = y1 ∨ z = y2 ∨ z = y3 ∨ z = y4 := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using this
      rcases this with rfl | h'
      · exact hzNe1 rfl
      rcases h' with rfl | h'
      · exact hzNe2 rfl
      rcases h' with rfl | rfl
      · exact hzNe3 rfl
      · exact hzNe4 rfl
    have hzNotAB : z ∉ (k.2.2.1 ∪ k.2.2.2.1) := (Finset.mem_sdiff.mp hzX).2
    exact Finset.mem_sdiff.mpr ⟨hzS, hzNotAB⟩
  have hEqOut : S \ (k.2.2.1 ∪ k.2.2.2.1) = (((X.erase y1).erase y2).erase y3).erase y4 :=
    Finset.Subset.antisymm hSub1 hSub2
  simpa [hEqOut] using hSdecomp

theorem eq_keyBase_union_Xerase_h0_erase_erase_erase_erase_of_Xerase_h0_sdiff_eq_quad
    (hreg : O1aUpgradeRegime family ground A0 h0)
    {k : WLcertKey α} {S : Finset α}
    (hSdom : S ∈ o1aWitnessLiftDomWL family h0)
    (hcert : ∃ cert : WLcert family S, WLcert.key cert = k ∧ cert.h ∉ S)
    {y1 y2 y3 y4 : α}
    (hXsdiff :
      ((ground \ (k.2.2.1 ∪ k.2.2.2.1)).erase h0) \ S = ({y1, y2, y3, y4} : Finset α)) :
    let X : Finset α := ground \ (k.2.2.1 ∪ k.2.2.2.1)
    S =
      PerXSubfiber.keyBase (α := α) (k := k) ∪
        (((((X.erase h0).erase y1).erase y2).erase y3).erase y4) := by
  classical
  intro X
  -- `h0 ∉ S` since `S ∈ domWL ⊆ coreSliceAvoid`.
  have hS0 : S ∈ o1aWitnessLiftDom family h0 := (Finset.mem_filter.mp hSdom).1
  have hSAvoid : S ∈ coreSliceAvoid family h0 := (Finset.mem_filter.mp hS0).1
  have hh0 : h0 ∉ S := (Finset.mem_filter.mp hSAvoid).2
  -- Hard-branch reduction facts for `S`.
  have htr :=
    (wlcert_hNotMem_reduction_o1aDomWL (family := family) (ground := ground) (A0 := A0) (h0 := h0)
      hreg (k := k) (S := S) hSdom hcert)
  have hSoutSub : S \ (k.2.2.1 ∪ k.2.2.2.1) ⊆ X := by simpa [X] using htr.2.2.2.1
  have hSoutSub' : S \ (k.2.2.1 ∪ k.2.2.2.1) ⊆ X.erase h0 := by
    intro z hz
    have hzX : z ∈ X := hSoutSub hz
    have hzS : z ∈ S := (Finset.mem_sdiff.mp hz).1
    have hzNe : z ≠ h0 := by
      intro hzy
      subst hzy
      exact hh0 hzS
    exact Finset.mem_erase.mpr ⟨hzNe, hzX⟩
  have hSdecomp :
      S =
        PerXSubfiber.keyBase (α := α) (k := k) ∪ (S \ (k.2.2.1 ∪ k.2.2.2.1)) := by
    simpa [PerXSubfiber.keyBase] using htr.2.2.2.2.1
  -- Rewrite the hypothesis in terms of `X`.
  have hXsdiff' : (X.erase h0) \ S = ({y1, y2, y3, y4} : Finset α) := by
    simpa [X] using hXsdiff
  -- Membership facts for the missing elements.
  have hy1Mem : y1 ∈ (X.erase h0) \ S := by
    rw [hXsdiff']
    simpa using (Finset.mem_insert_self y1 ({y2, y3, y4} : Finset α))
  have hy2Mem : y2 ∈ (X.erase h0) \ S := by
    rw [hXsdiff']
    by_cases hEq : y2 = y1
    · subst hEq
      simpa using (Finset.mem_insert_self y1 ({y2, y3, y4} : Finset α))
    · have : y2 ∈ ({y2, y3, y4} : Finset α) := by
        simpa using (Finset.mem_insert_self y2 ({y3, y4} : Finset α))
      simpa using (Finset.mem_insert_of_mem this)
  have hy3Mem : y3 ∈ (X.erase h0) \ S := by
    rw [hXsdiff']
    by_cases hEq3 : y3 = y1
    · subst hEq3
      simpa using (Finset.mem_insert_self y1 ({y2, y3, y4} : Finset α))
    · have : y3 ∈ ({y2, y3, y4} : Finset α) := by
        by_cases hEq32 : y3 = y2
        · subst hEq32
          simpa using (Finset.mem_insert_self y2 ({y3, y4} : Finset α))
        · have : y3 ∈ ({y3, y4} : Finset α) := by
            simpa using (Finset.mem_insert_self y3 ({y4} : Finset α))
          simpa using (Finset.mem_insert_of_mem this)
      simpa using (Finset.mem_insert_of_mem this)
  have hy4Mem : y4 ∈ (X.erase h0) \ S := by
    rw [hXsdiff']
    simp
  have hy1X : y1 ∈ X.erase h0 := (Finset.mem_sdiff.mp hy1Mem).1
  have hy1Not : y1 ∉ S := (Finset.mem_sdiff.mp hy1Mem).2
  have hy2X : y2 ∈ X.erase h0 := (Finset.mem_sdiff.mp hy2Mem).1
  have hy2Not : y2 ∉ S := (Finset.mem_sdiff.mp hy2Mem).2
  have hy3X : y3 ∈ X.erase h0 := (Finset.mem_sdiff.mp hy3Mem).1
  have hy3Not : y3 ∉ S := (Finset.mem_sdiff.mp hy3Mem).2
  have hy4X : y4 ∈ X.erase h0 := (Finset.mem_sdiff.mp hy4Mem).1
  have hy4Not : y4 ∉ S := (Finset.mem_sdiff.mp hy4Mem).2
  -- Identify the outside part `S \\ (kA ∪ kB)` with `X.erase h0.erase y1.erase y2.erase y3.erase y4`.
  have hSub1 :
      S \ (k.2.2.1 ∪ k.2.2.2.1) ⊆ (((((X.erase h0).erase y1).erase y2).erase y3).erase y4) := by
    intro z hz
    have hzX : z ∈ X.erase h0 := hSoutSub' hz
    have hzS : z ∈ S := (Finset.mem_sdiff.mp hz).1
    have hzNe1 : z ≠ y1 := by
      intro hzy
      subst hzy
      exact hy1Not hzS
    have hzNe2 : z ≠ y2 := by
      intro hzy
      subst hzy
      exact hy2Not hzS
    have hzNe3 : z ≠ y3 := by
      intro hzy
      subst hzy
      exact hy3Not hzS
    have hzNe4 : z ≠ y4 := by
      intro hzy
      subst hzy
      exact hy4Not hzS
    refine Finset.mem_erase.mpr ?_
    refine ⟨hzNe4, ?_⟩
    refine Finset.mem_erase.mpr ?_
    refine ⟨hzNe3, ?_⟩
    refine Finset.mem_erase.mpr ?_
    refine ⟨hzNe2, ?_⟩
    refine Finset.mem_erase.mpr ?_
    refine ⟨hzNe1, ?_⟩
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hzX).1, (Finset.mem_erase.mp hzX).2⟩
  have hSub2 :
      (((((X.erase h0).erase y1).erase y2).erase y3).erase y4) ⊆ S \ (k.2.2.1 ∪ k.2.2.2.1) := by
    intro z hz
    have hzNe4 : z ≠ y4 := (Finset.mem_erase.mp hz).1
    have hz123h : z ∈ ((((X.erase h0).erase y1).erase y2).erase y3) := (Finset.mem_erase.mp hz).2
    have hzNe3 : z ≠ y3 := (Finset.mem_erase.mp hz123h).1
    have hz12h : z ∈ (((X.erase h0).erase y1).erase y2) := (Finset.mem_erase.mp hz123h).2
    have hzNe2 : z ≠ y2 := (Finset.mem_erase.mp hz12h).1
    have hz1h : z ∈ (X.erase h0).erase y1 := (Finset.mem_erase.mp hz12h).2
    have hzNe1 : z ≠ y1 := (Finset.mem_erase.mp hz1h).1
    have hzXh : z ∈ X.erase h0 := (Finset.mem_erase.mp hz1h).2
    have hzX : z ∈ X := (Finset.mem_erase.mp hzXh).2
    have hzS : z ∈ S := by
      by_contra hzS
      have hzXS : z ∈ (X.erase h0) \ S := Finset.mem_sdiff.mpr ⟨hzXh, hzS⟩
      have : z ∈ ({y1, y2, y3, y4} : Finset α) := by
        rw [← hXsdiff']
        simpa using hzXS
      have : z = y1 ∨ z = y2 ∨ z = y3 ∨ z = y4 := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using this
      rcases this with rfl | h'
      · exact hzNe1 rfl
      rcases h' with rfl | h'
      · exact hzNe2 rfl
      rcases h' with rfl | rfl
      · exact hzNe3 rfl
      · exact hzNe4 rfl
    have hzNotAB : z ∉ (k.2.2.1 ∪ k.2.2.2.1) := (Finset.mem_sdiff.mp hzX).2
    exact Finset.mem_sdiff.mpr ⟨hzS, hzNotAB⟩
  have hEqOut :
      S \ (k.2.2.1 ∪ k.2.2.2.1) =
        (((((X.erase h0).erase y1).erase y2).erase y3).erase y4) :=
    Finset.Subset.antisymm hSub1 hSub2
  simpa [hEqOut] using hSdecomp

theorem card_Bucket_perXSignatureOutMore_le_one_of_trace5Plus_Uout_eq_some_false
    (hreg : O1aUpgradeRegime family ground A0 h0)
    {k : WLcertKey α}
    {Sstar : {S // S ∈ o1aWitnessLiftDomWL family h0}}
    {x : α}
    (hSstar :
      Sstar ∈ wlcertAdmissibleFiber_hNotMem (family := family) (o1aWitnessLiftDomWL family h0) k)
    (σOut : PerXSignatureOutMore α)
    {t1 t2 t3 t4 t5 : α}
    (hτ : σOut.2.1 = some (t1, t2, t3, t4, t5, false))
    (hcoreNoMore : ∀ u1 ot2, σOut.1.2.2.2.1 ≠ some (u1, ot2, true)) :
    let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h0
    let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
    let Fx0 :
        Finset {S // S ∈ dom} :=
      wlcertAdmissibleFiber_hNotMem_fiberForX (dom := dom) fiber Sstar.1 x
    let sig0 : {Ssub // Ssub ∈ Fx0} → PerXSignature α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      perXSignature_of_hardFiber (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1) Sstar.2 b.1.2 hcert_star hcert_sub hne
    let Uout : {Ssub // Ssub ∈ Fx0} → Finset α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      let yw :
          Σ y : α, BlockedUnionWitness family b.1.1 y :=
        chooseYAndWitness_of_hardFiber
          (family := family) (ground := ground) (A0 := A0) (h0 := h0)
          hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
          Sstar.2 b.1.2 hcert_star hcert_sub hne
      b.1.1 \ (yw.2.A ∪ yw.2.B)
    let sigOut : {Ssub // Ssub ∈ Fx0} → PerXSignatureOutMore α := fun b =>
      (sig0 b,
        trace5PlusOfFinset (α := α) (Uout b),
        t6OptionOfTrace5Plus (α := α) (Uout b))
    (Bucket (Fx := Fx0.attach) sigOut σOut).card ≤ 1 := by
  classical
  intro dom fiber Fx0 sig0 Uout sigOut
  refine Finset.card_le_one.2 ?_
  intro b1 hb1 b2 hb2
  have hb1sig : sigOut b1 = σOut := (Finset.mem_filter.mp hb1).2
  have hb2sig : sigOut b2 = σOut := (Finset.mem_filter.mp hb2).2
  -- Decode the shared `trace5Plus(Uout)` value.
  have hb1τ : trace5PlusOfFinset (α := α) (Uout b1) = some (t1, t2, t3, t4, t5, false) := by
    have : (sigOut b1).2.1 = σOut.2.1 := by simpa [hb1sig]
    -- `(sigOut b).2.1` is `trace5Plus(Uout b)` by definition.
    simpa [sigOut, hτ] using this
  have hb2τ : trace5PlusOfFinset (α := α) (Uout b2) = some (t1, t2, t3, t4, t5, false) := by
    have : (sigOut b2).2.1 = σOut.2.1 := by simpa [hb2sig]
    simpa [sigOut, hτ] using this
  have hU1 : Uout b1 = ({t1, t2, t3, t4, t5} : Finset α) :=
    eq_quint_of_trace5PlusOfFinset_eq_some_false (α := α) hb1τ
  have hU2 : Uout b2 = ({t1, t2, t3, t4, t5} : Finset α) :=
    eq_quint_of_trace5PlusOfFinset_eq_some_false (α := α) hb2τ
  have hUeq : Uout b1 = Uout b2 := by simpa [hU1, hU2]
  -- Reconstruct the canonical `y` and witnesses for `b1` and `b2`.
  have hcert_star :
      ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
    (Finset.mem_filter.mp hSstar).2
  have hb1Fiber : b1.1 ∈ fiber := (Finset.mem_filter.mp b1.2).1
  have hb2Fiber : b2.1 ∈ fiber := (Finset.mem_filter.mp b2.2).1
  have hcert1 :
      ∃ cert : WLcert family b1.1.1, WLcert.key cert = k ∧ cert.h ∉ b1.1.1 :=
    (Finset.mem_filter.mp hb1Fiber).2
  have hcert2 :
      ∃ cert : WLcert family b2.1.1, WLcert.key cert = k ∧ cert.h ∉ b2.1.1 :=
    (Finset.mem_filter.mp hb2Fiber).2
  have hne1 : b1.1.1 ≠ Sstar.1 :=
    ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
      (Ssub := b1.1) b1.2
  have hne2 : b2.1.1 ≠ Sstar.1 :=
    ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
      (Ssub := b2.1) b2.2
  let yw1 :
      Σ y : α, BlockedUnionWitness family b1.1.1 y :=
    chooseYAndWitness_of_hardFiber
      (family := family) (ground := ground) (A0 := A0) (h0 := h0)
      hreg (k := k) (Sstar := Sstar.1) (Ssub := b1.1.1)
      Sstar.2 b1.1.2 hcert_star hcert1 hne1
  let yw2 :
      Σ y : α, BlockedUnionWitness family b2.1.1 y :=
    chooseYAndWitness_of_hardFiber
      (family := family) (ground := ground) (A0 := A0) (h0 := h0)
      hreg (k := k) (Sstar := Sstar.1) (Ssub := b2.1.1)
      Sstar.2 b2.1.2 hcert_star hcert2 hne2
  -- The bucket fixes the full `PerXSignature`, hence the chosen missing `y` is the same.
  have hyEq : yw1.1 = yw2.1 := by
    -- Compare the `y` component of the hard-fiber signature.
    have hsig0 :
        sig0 b1 = sig0 b2 := by
      -- `sigOut` equality gives equality of the first component `sig0`.
      have : (sigOut b1).1 = (sigOut b2).1 := by
        have : sigOut b1 = sigOut b2 := by simpa [hb1sig, hb2sig]
        exact congrArg (fun s : PerXSignatureOutMore α => s.1) this
      simpa [sigOut] using this
    -- Unfold `sig0` to expose the chosen `y`.
    have hy1 :
        (sig0 b1).1 = yw1.1 := by
      simp [sig0, perXSignature_of_hardFiber, perXSignature, yw1]
    have hy2 :
        (sig0 b2).1 = yw2.1 := by
      simp [sig0, perXSignature_of_hardFiber, perXSignature, yw2]
    -- Conclude.
    simpa [hy1, hy2] using congrArg (fun s : PerXSignature α => s.1) hsig0
  -- Decode `core.erase y` from the rigid `coreTrace` component of `σOut.1`.
  have hcoreEq : yw1.2.core.erase yw1.1 = yw2.2.core.erase yw2.1 := by
    -- The core trace component is fixed by the bucket and has `hasMore = false`.
    have hct1 :
        trace2PlusOfFinset (α := α) (yw1.2.core.erase yw1.1) = σOut.1.2.2.2.1 := by
      -- From `sigOut b1 = σOut`.
      have : (sigOut b1).1.2.2.2.1 = σOut.1.2.2.2.1 := by simpa [hb1sig]
      -- Unfold `sig0` for `b1`.
      simpa [sigOut, sig0, perXSignature_of_hardFiber, perXSignature, yw1] using this
    have hct2 :
        trace2PlusOfFinset (α := α) (yw2.2.core.erase yw2.1) = σOut.1.2.2.2.1 := by
      have : (sigOut b2).1.2.2.2.1 = σOut.1.2.2.2.1 := by simpa [hb2sig]
      simpa [sigOut, sig0, perXSignature_of_hardFiber, perXSignature, yw2] using this
    -- Case split on the trace value.
    cases ht : σOut.1.2.2.2.1 with
    | none =>
        have h1 : yw1.2.core.erase yw1.1 = (∅ : Finset α) :=
          eq_empty_of_trace2PlusOfFinset_eq_none (α := α) (by simpa [ht] using hct1)
        have h2 : yw2.2.core.erase yw2.1 = (∅ : Finset α) :=
          eq_empty_of_trace2PlusOfFinset_eq_none (α := α) (by simpa [ht] using hct2)
        simpa [h1, h2]
    | some triple =>
        rcases triple with ⟨u1, ou2, b⟩
        cases b with
        | true =>
            -- Forbidden by `hcoreNoMore`.
            have : False := by
              exact hcoreNoMore u1 ou2 ht
            exact False.elim this
        | false =>
            cases ou2 with
            | none =>
                have h1 :
                    yw1.2.core.erase yw1.1 = ({u1} : Finset α) :=
                  eq_singleton_of_trace2PlusOfFinset_eq_some_none_false (α := α)
                    (by simpa [ht] using hct1)
                have h2 :
                    yw2.2.core.erase yw2.1 = ({u1} : Finset α) :=
                  eq_singleton_of_trace2PlusOfFinset_eq_some_none_false (α := α)
                    (by simpa [ht] using hct2)
                simpa [h1, h2]
            | some u2 =>
                have h1 :
                    yw1.2.core.erase yw1.1 = ({u1, u2} : Finset α) :=
                  eq_pair_of_trace2PlusOfFinset_eq_some_some_false (α := α)
                    (by simpa [ht] using hct1)
                have h2 :
                    yw2.2.core.erase yw2.1 = ({u1, u2} : Finset α) :=
                  eq_pair_of_trace2PlusOfFinset_eq_some_some_false (α := α)
                    (by simpa [ht] using hct2)
                simpa [h1, h2]
  -- Now reconstruct `S` from `core.erase y` and `Uout`.
  have hyNot1 : yw1.1 ∉ b1.1.1 := by
    -- This is baked into the witness selection `chooseYAndWitness_of_hardFiber`.
    -- Unfold and use `chooseMissingFromRef_spec`.
    have hyDiff :
        yw1.1 ∈ Sstar.1 \ b1.1.1 := by
      simpa [yw1, chooseYAndWitness_of_hardFiber] using
        (chooseMissingFromRef_spec (family := family) (h0 := h0) Sstar.1 b1.1.1
          Sstar.2 b1.1.2 hne1)
    exact (Finset.mem_sdiff.mp hyDiff).2
  have hyNot2 : yw2.1 ∉ b2.1.1 := by
    have hyDiff :
        yw2.1 ∈ Sstar.1 \ b2.1.1 := by
      simpa [yw2, chooseYAndWitness_of_hardFiber] using
        (chooseMissingFromRef_spec (family := family) (h0 := h0) Sstar.1 b2.1.1
          Sstar.2 b2.1.2 hne2)
    exact (Finset.mem_sdiff.mp hyDiff).2
  have hS1 :
      b1.1.1 = (yw1.2.core.erase yw1.1) ∪ Uout b1 :=
    S_eq_coreErase_union_sdiff_union_of_blockedUnionWitness (family := family) (S := b1.1.1)
      (y := yw1.1) yw1.2 hyNot1
  have hS2 :
      b2.1.1 = (yw2.2.core.erase yw2.1) ∪ Uout b2 :=
    S_eq_coreErase_union_sdiff_union_of_blockedUnionWitness (family := family) (S := b2.1.1)
      (y := yw2.1) yw2.2 hyNot2
  have hEqSets : b1.1.1 = b2.1.1 := by
    -- Replace the core and outside parts by their common values.
    calc
      b1.1.1 = (yw1.2.core.erase yw1.1) ∪ Uout b1 := hS1
      _ = (yw2.2.core.erase yw2.1) ∪ Uout b2 := by simpa [hcoreEq, hUeq]
      _ = b2.1.1 := by simpa [hS2]
  -- Conclude equality in the attached bucket.
  have hEq1 : b1.1 = b2.1 := Subtype.ext hEqSets
  exact Subtype.ext hEq1

/--
If `trace5Plus(Uout) = none` (so `|Uout| < 5`) and the core trace is rigid,
then an outMore bucket has a cheap polynomial cap.

This is purely a wiring lemma: we do **not** try to collapse the bucket to a
singleton; we only need a uniform `O(n^2)` bound to keep the per-`x` ledger safe.
-/
theorem card_Bucket_perXSignatureOutMore_le_mul_succ_mul_succ_of_trace5Plus_Uout_eq_none
    (hreg : O1aUpgradeRegime family ground A0 h0)
    {k : WLcertKey α}
    {Sstar : {S // S ∈ o1aWitnessLiftDomWL family h0}}
    {x : α}
    (hSstar :
      Sstar ∈ wlcertAdmissibleFiber_hNotMem (family := family) (o1aWitnessLiftDomWL family h0) k)
    (σOut : PerXSignatureOutMore α)
    (hτ : σOut.2.1 = none)
    (hcoreNoMore : ∀ u1 ot2, σOut.1.2.2.2.1 ≠ some (u1, ot2, true)) :
    let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h0
    let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
    let Fx0 :
        Finset {S // S ∈ dom} :=
      wlcertAdmissibleFiber_hNotMem_fiberForX (dom := dom) fiber Sstar.1 x
    let sig0 : {Ssub // Ssub ∈ Fx0} → PerXSignature α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      perXSignature_of_hardFiber (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1) Sstar.2 b.1.2 hcert_star hcert_sub hne
    let Uout : {Ssub // Ssub ∈ Fx0} → Finset α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      let yw :
          Σ y : α, BlockedUnionWitness family b.1.1 y :=
        chooseYAndWitness_of_hardFiber
          (family := family) (ground := ground) (A0 := A0) (h0 := h0)
          hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
          Sstar.2 b.1.2 hcert_star hcert_sub hne
      b.1.1 \ (yw.2.A ∪ yw.2.B)
    let sigOut : {Ssub // Ssub ∈ Fx0} → PerXSignatureOutMore α := fun b =>
      (sig0 b,
        trace5PlusOfFinset (α := α) (Uout b),
        t6OptionOfTrace5Plus (α := α) (Uout b))
    (Bucket (Fx := Fx0.attach) sigOut σOut).card ≤
      (ground.card + 1) * (ground.card + 1) := by
  classical
  intro dom fiber Fx0 sig0 Uout sigOut
  let B : Finset {Ssub // Ssub ∈ Fx0} := Bucket (Fx := Fx0.attach) sigOut σOut
  let T : Finset (Option α) := optionOfFinset (α := α) ground
  -- Record (up to two) extra outside elements beyond the fixed `outsideTrace` pair.
  let f : {Ssub // Ssub ∈ Fx0} → Option α × Option α := fun b =>
    match σOut.1.2.2.2.2.2 with
    | none => (none, none)
    | some (t1, none, false) => (none, none)
    | some (t1, none, true) => (none, none)
    | some (t1, some t2, false) => (none, none)
    | some (t1, some t2, true) =>
        match trace2PlusOfFinset (α := α) (((Uout b).erase t1).erase t2) with
        | none => (none, none)
        | some (u1, ou2, _b) => (some u1, ou2)
  -- Bound fibers of `f` on the bucket by showing `f` is injective on `B`.
  have hfiber :
      ∀ p ∈ B.image f, (B.filter (fun b => f b = p)).card ≤ 1 := by
    intro p hp
    refine Finset.card_le_one.2 ?_
    intro b1 hb1 b2 hb2
    have hb1B : b1 ∈ B := (Finset.mem_filter.mp hb1).1
    have hb2B : b2 ∈ B := (Finset.mem_filter.mp hb2).1
    have hb1f : f b1 = p := (Finset.mem_filter.mp hb1).2
    have hb2f : f b2 = p := (Finset.mem_filter.mp hb2).2
    have hfEq : f b1 = f b2 := by simpa [hb2f] using hb1f
    have hb1sig : sigOut b1 = σOut := (Finset.mem_filter.mp hb1B).2
    have hb2sig : sigOut b2 = σOut := (Finset.mem_filter.mp hb2B).2
    -- Reconstruct the canonical `y` and witnesses for `b1` and `b2`.
    have hcert_star :
        ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
      (Finset.mem_filter.mp hSstar).2
    have hb1Fiber : b1.1 ∈ fiber := (Finset.mem_filter.mp b1.2).1
    have hb2Fiber : b2.1 ∈ fiber := (Finset.mem_filter.mp b2.2).1
    have hcert1 :
        ∃ cert : WLcert family b1.1.1, WLcert.key cert = k ∧ cert.h ∉ b1.1.1 :=
      (Finset.mem_filter.mp hb1Fiber).2
    have hcert2 :
        ∃ cert : WLcert family b2.1.1, WLcert.key cert = k ∧ cert.h ∉ b2.1.1 :=
      (Finset.mem_filter.mp hb2Fiber).2
    have hne1 : b1.1.1 ≠ Sstar.1 :=
      ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
        (Ssub := b1.1) b1.2
    have hne2 : b2.1.1 ≠ Sstar.1 :=
      ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
        (Ssub := b2.1) b2.2
    let yw1 :
        Σ y : α, BlockedUnionWitness family b1.1.1 y :=
      chooseYAndWitness_of_hardFiber
        (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg (k := k) (Sstar := Sstar.1) (Ssub := b1.1.1)
        Sstar.2 b1.1.2 hcert_star hcert1 hne1
    let yw2 :
        Σ y : α, BlockedUnionWitness family b2.1.1 y :=
      chooseYAndWitness_of_hardFiber
        (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg (k := k) (Sstar := Sstar.1) (Ssub := b2.1.1)
        Sstar.2 b2.1.2 hcert_star hcert2 hne2
    -- The bucket fixes the full `PerXSignature`, hence the chosen missing `y` is the same.
    have hyEq : yw1.1 = yw2.1 := by
      have hsig0 : sig0 b1 = sig0 b2 := by
        have : (sigOut b1).1 = (sigOut b2).1 := by
          have : sigOut b1 = sigOut b2 := by simpa [hb1sig, hb2sig]
          exact congrArg (fun s : PerXSignatureOutMore α => s.1) this
        simpa [sigOut] using this
      have hy1 : (sig0 b1).1 = yw1.1 := by
        simp [sig0, perXSignature_of_hardFiber, perXSignature, yw1]
      have hy2 : (sig0 b2).1 = yw2.1 := by
        simp [sig0, perXSignature_of_hardFiber, perXSignature, yw2]
      simpa [hy1, hy2] using congrArg (fun s : PerXSignature α => s.1) hsig0
    -- Decode `core.erase y` from the rigid `coreTrace` component of `σOut.1`.
    have hcoreEq : yw1.2.core.erase yw1.1 = yw2.2.core.erase yw2.1 := by
      have hct1 :
          trace2PlusOfFinset (α := α) (yw1.2.core.erase yw1.1) = σOut.1.2.2.2.1 := by
        have : (sigOut b1).1.2.2.2.1 = σOut.1.2.2.2.1 := by simpa [hb1sig]
        simpa [sigOut, sig0, perXSignature_of_hardFiber, perXSignature, yw1] using this
      have hct2 :
          trace2PlusOfFinset (α := α) (yw2.2.core.erase yw2.1) = σOut.1.2.2.2.1 := by
        have : (sigOut b2).1.2.2.2.1 = σOut.1.2.2.2.1 := by simpa [hb2sig]
        simpa [sigOut, sig0, perXSignature_of_hardFiber, perXSignature, yw2] using this
      cases ht : σOut.1.2.2.2.1 with
      | none =>
          have h1 : yw1.2.core.erase yw1.1 = (∅ : Finset α) :=
            eq_empty_of_trace2PlusOfFinset_eq_none (α := α) (by simpa [ht] using hct1)
          have h2 : yw2.2.core.erase yw2.1 = (∅ : Finset α) :=
            eq_empty_of_trace2PlusOfFinset_eq_none (α := α) (by simpa [ht] using hct2)
          rw [h1, h2]
      | some triple =>
          rcases triple with ⟨u1, ou2, b⟩
          cases b with
          | true =>
              have : False := by
                exact hcoreNoMore u1 ou2 ht
              exact False.elim this
          | false =>
              cases ou2 with
              | none =>
                  have h1 :
                      yw1.2.core.erase yw1.1 = ({u1} : Finset α) :=
                    eq_singleton_of_trace2PlusOfFinset_eq_some_none_false (α := α)
                      (by simpa [ht] using hct1)
                  have h2 :
                      yw2.2.core.erase yw2.1 = ({u1} : Finset α) :=
                    eq_singleton_of_trace2PlusOfFinset_eq_some_none_false (α := α)
                      (by simpa [ht] using hct2)
                  rw [h1, h2]
              | some u2 =>
                  have h1 :
                      yw1.2.core.erase yw1.1 = ({u1, u2} : Finset α) :=
                    eq_pair_of_trace2PlusOfFinset_eq_some_some_false (α := α)
                      (by simpa [ht] using hct1)
                  have h2 :
                      yw2.2.core.erase yw2.1 = ({u1, u2} : Finset α) :=
                    eq_pair_of_trace2PlusOfFinset_eq_some_some_false (α := α)
                      (by simpa [ht] using hct2)
                  rw [h1, h2]
    -- `y ∉ S` is baked into `chooseYAndWitness_of_hardFiber`.
    have hyNot1 : yw1.1 ∉ b1.1.1 := by
      have hyDiff : yw1.1 ∈ Sstar.1 \ b1.1.1 := by
        simpa [yw1, chooseYAndWitness_of_hardFiber] using
          (chooseMissingFromRef_spec (family := family) (h0 := h0) Sstar.1 b1.1.1
            Sstar.2 b1.1.2 hne1)
      exact (Finset.mem_sdiff.mp hyDiff).2
    have hyNot2 : yw2.1 ∉ b2.1.1 := by
      have hyDiff : yw2.1 ∈ Sstar.1 \ b2.1.1 := by
        simpa [yw2, chooseYAndWitness_of_hardFiber] using
          (chooseMissingFromRef_spec (family := family) (h0 := h0) Sstar.1 b2.1.1
            Sstar.2 b2.1.2 hne2)
      exact (Finset.mem_sdiff.mp hyDiff).2
    -- Decode `Uout` from the fixed `outsideTrace` plus the `f`-value.
    have hUeq : Uout b1 = Uout b2 := by
      cases hout : σOut.1.2.2.2.2.2 with
      | none =>
          have hout1 : outsideTrace (family := family) (S := b1.1.1) (y := yw1.1) yw1.2 = none := by
              have : (sigOut b1).1.2.2.2.2.2 = σOut.1.2.2.2.2.2 := by simpa [hb1sig]
              simpa [sigOut, sig0, perXSignature_of_hardFiber, perXSignature, outsideTrace, yw1, hout] using this
          have hout2 : outsideTrace (family := family) (S := b2.1.1) (y := yw2.1) yw2.2 = none := by
              have : (sigOut b2).1.2.2.2.2.2 = σOut.1.2.2.2.2.2 := by simpa [hb2sig]
              simpa [sigOut, sig0, perXSignature_of_hardFiber, perXSignature, outsideTrace, yw2, hout] using this
          have h1 : Uout b1 = (∅ : Finset α) := by
            -- `Uout b = S \ (A ∪ B)` by definition.
            simpa [Uout, yw1] using
              (S_sdiff_union_eq_empty_of_outsideTrace_eq_none (family := family) (S := b1.1.1)
                (y := yw1.1) yw1.2 hout1)
          have h2 : Uout b2 = (∅ : Finset α) := by
            simpa [Uout, yw2] using
              (S_sdiff_union_eq_empty_of_outsideTrace_eq_none (family := family) (S := b2.1.1)
                (y := yw2.1) yw2.2 hout2)
          rw [h1, h2]
        | some triple =>
            rcases triple with ⟨t1, ot2, bMore⟩
            cases bMore with
            | true =>
                -- Here `ot2 = some t2` by definition of `trace2PlusOfFinset`.
                cases ot2 with
                | none =>
                    -- Impossible: `trace2Plus` never returns `some(_,none,true)`.
                    have hout1 : outsideTrace (family := family) (S := b1.1.1) (y := yw1.1) yw1.2 =
                        some (t1, none, true) := by
                      have : (sigOut b1).1.2.2.2.2.2 = σOut.1.2.2.2.2.2 := by simpa [hb1sig]
                      simpa [sigOut, sig0, perXSignature_of_hardFiber, perXSignature, outsideTrace, yw1, hout] using this
                    have htU1 :
                        trace2PlusOfFinset (α := α) (Uout b1) = some (t1, none, true) := by
                      simpa [outsideTrace, Uout, yw1] using hout1
                    have : False :=
                      (trace2PlusOfFinset_ne_some_none_true (α := α) (T := Uout b1) (t1 := t1)) htU1
                    exact False.elim this
                | some t2 =>
                    -- In this branch `f` records exactly the remainder after erasing `t1,t2`.
                    have hout1 :
                        outsideTrace (family := family) (S := b1.1.1) (y := yw1.1) yw1.2 =
                          some (t1, some t2, true) := by
                      have : (sigOut b1).1.2.2.2.2.2 = σOut.1.2.2.2.2.2 := by simpa [hb1sig]
                      simpa [sigOut, sig0, perXSignature_of_hardFiber, perXSignature, outsideTrace, yw1, hout] using this
                    have hout2 :
                        outsideTrace (family := family) (S := b2.1.1) (y := yw2.1) yw2.2 =
                          some (t1, some t2, true) := by
                      have : (sigOut b2).1.2.2.2.2.2 = σOut.1.2.2.2.2.2 := by simpa [hb2sig]
                      simpa [sigOut, sig0, perXSignature_of_hardFiber, perXSignature, outsideTrace, yw2, hout] using this
                    -- Convert `outsideTrace` to a `trace2Plus` statement on `Uout`.
                    have htU1 :
                        trace2PlusOfFinset (α := α) (Uout b1) =
                          some (t1, some t2, true) := by
                      simpa [outsideTrace, Uout, yw1] using hout1
                    have htU2 :
                        trace2PlusOfFinset (α := α) (Uout b2) =
                          some (t1, some t2, true) := by
                      simpa [outsideTrace, Uout, yw2] using hout2
                    have ht1mem1 : t1 ∈ Uout b1 :=
                      mem_left_of_trace2PlusOfFinset_eq_some (α := α) htU1
                    have ht2mem1 : t2 ∈ Uout b1 :=
                      mem_right_of_trace2PlusOfFinset_eq_some_some (α := α) htU1
                    have ht1mem2 : t1 ∈ Uout b2 :=
                      mem_left_of_trace2PlusOfFinset_eq_some (α := α) htU2
                    have ht2mem2 : t2 ∈ Uout b2 :=
                      mem_right_of_trace2PlusOfFinset_eq_some_some (α := α) htU2
                    -- `trace5Plus(Uout)=none` on the bucket.
                    have hbτ1 : trace5PlusOfFinset (α := α) (Uout b1) = none := by
                      have : (sigOut b1).2.1 = σOut.2.1 := by simpa [hb1sig]
                      simpa [sigOut, hτ] using this
                    have hbτ2 : trace5PlusOfFinset (α := α) (Uout b2) = none := by
                      have : (sigOut b2).2.1 = σOut.2.1 := by simpa [hb2sig]
                      simpa [sigOut, hτ] using this
                    -- Identify the remainder sets from the `f`-equality, ruling out the `bb=true` leakage using `trace5Plus=none`.
                    set R1 : Finset α := (((Uout b1).erase t1).erase t2)
                    set R2 : Finset α := (((Uout b2).erase t1).erase t2)
                    have hR : R1 = R2 := by
                      -- Split on the trace of `R1`.
                      cases htr1 : trace2PlusOfFinset (α := α) R1 with
                      | none =>
                          have hf1' : f b1 = (none, none) := by
                            simp [f, hout, htr1, R1]
                          have hf2' : f b2 = (none, none) := by
                            simpa [hfEq] using hf1'
                          cases htr2 : trace2PlusOfFinset (α := α) R2 with
                          | none =>
                              have h1 : R1 = (∅ : Finset α) :=
                                eq_empty_of_trace2PlusOfFinset_eq_none (α := α) htr1
                              have h2 : R2 = (∅ : Finset α) :=
                                eq_empty_of_trace2PlusOfFinset_eq_none (α := α) htr2
                              simpa [h1, h2]
                          | some tr2 =>
                              rcases tr2 with ⟨u1, ou2, bb2⟩
                              have : f b2 ≠ (none, none) := by
                                simp [f, hout, htr2, R2]
                              exact False.elim (this hf2')
                      | some tr1 =>
                          rcases tr1 with ⟨u1, ou2, bb1⟩
                          have hf1' : f b1 = (some u1, ou2) := by
                            simp [f, hout, htr1, R1]
                          have hf2' : f b2 = (some u1, ou2) := by
                            simpa [hfEq] using hf1'
                          cases htr2 : trace2PlusOfFinset (α := α) R2 with
                          | none =>
                              have : f b2 = (none, none) := by
                                simp [f, hout, htr2, R2]
                              exact False.elim (by simpa [this] using hf2')
                          | some tr2 =>
                              rcases tr2 with ⟨u1', ou2', bb2⟩
                              have hf2_from_tr2 : f b2 = (some u1', ou2') := by
                                simp [f, hout, htr2, R2]
                              have hpair : (some u1', ou2') = (some u1, ou2) := by
                                simpa [hf2_from_tr2] using hf2'
                              have hu1eq : u1' = u1 :=
                                Option.some.inj (congrArg Prod.fst hpair)
                              have hou2eq : ou2' = ou2 := congrArg Prod.snd hpair
                              subst u1'
                              subst ou2'
                              -- Eliminate `bb=true` for `R1` using `trace5Plus(Uout)=none`.
                              cases bb1 with
                              | true =>
                                  cases ou2 with
                                  | none =>
                                      have : False :=
                                        (trace2PlusOfFinset_ne_some_none_true (α := α) (T := R1) (t1 := u1))
                                          htr1
                                      exact False.elim this
                                  | some u2 =>
                                      -- Extract a third element from `R1` using the `bb=true` witness.
                                      have hR3 : (((R1.erase u1).erase u2).Nonempty) := by
                                        -- Unfold `trace2PlusOfFinset` to get the third-stage nonempty witness.
                                        classical
                                        -- We mimic the by_cases structure of `trace2PlusOfFinset`.
                                        by_cases hR1 : R1.Nonempty
                                        · let t1' : α := Classical.choose hR1
                                          let R1' : Finset α := R1.erase t1'
                                          by_cases hR1' : R1'.Nonempty
                                          · let t2' : α := Classical.choose hR1'
                                            let R1'' : Finset α := R1'.erase t2'
                                            by_cases hR1'' : R1''.Nonempty
                                            · have ht' :
                                                  trace2PlusOfFinset (α := α) R1 =
                                                    some (t1', some t2', true) := by
                                                  simp [trace2PlusOfFinset, hR1, t1', R1', hR1', t2', R1'', hR1'']
                                              have :
                                                  some (u1, some u2, true) =
                                                    some (t1', some t2', true) := by
                                                simpa [htr1] using ht'
                                              have hu1 : u1 = t1' := congrArg Prod.fst (Option.some.inj this)
                                              have hu2 :
                                                  some u2 = some t2' := by
                                                exact congrArg (fun p : Option α × Bool => p.1)
                                                  (congrArg Prod.snd (Option.some.inj this))
                                              have hu2' : u2 = t2' := Option.some.inj hu2
                                              simpa [R1', R1'', hu1, hu2'] using hR1''
                                            · have ht' :
                                                  trace2PlusOfFinset (α := α) R1 =
                                                    some (t1', some t2', false) := by
                                                  simp [trace2PlusOfFinset, hR1, t1', R1', hR1', t2', R1'', hR1'']
                                              have :
                                                  (some (u1, some u2, true) : Option (α × Option α × Bool)) =
                                                    some (t1', some t2', false) := by
                                                simpa [htr1] using ht'
                                              have hcontr : (true : Bool) = false :=
                                                congrArg (fun p : α × Option α × Bool => p.2.2) (Option.some.inj this)
                                              cases hcontr
                                          · have ht' :
                                                trace2PlusOfFinset (α := α) R1 =
                                                  some (t1', none, false) := by
                                                simp [trace2PlusOfFinset, hR1, t1', R1', hR1']
                                            have :
                                                (some (u1, some u2, true) : Option (α × Option α × Bool)) =
                                                  some (t1', none, false) := by
                                              simpa [htr1] using ht'
                                            have hcontr : (some u2 : Option α) = none :=
                                              congrArg (fun p : α × Option α × Bool => p.2.1) (Option.some.inj this)
                                            cases hcontr
                                        · have ht' : trace2PlusOfFinset (α := α) R1 = none := by
                                            simp [trace2PlusOfFinset, hR1]
                                          have :
                                              (none : Option (α × Option α × Bool)) = some (u1, some u2, true) := by
                                            simpa [htr1] using ht'.symm
                                          cases this
                                      let u3 : α := Classical.choose hR3
                                      have hu3mem : u3 ∈ ((R1.erase u1).erase u2) :=
                                        Classical.choose_spec hR3
                                      have hu3ne_u2 : u3 ≠ u2 := (Finset.mem_erase.mp hu3mem).1
                                      have hu3mem' : u3 ∈ (R1.erase u1) := (Finset.mem_erase.mp hu3mem).2
                                      have hu3ne_u1 : u3 ≠ u1 := (Finset.mem_erase.mp hu3mem').1
                                      have hu3R1 : u3 ∈ R1 := (Finset.mem_erase.mp hu3mem').2
                                      -- Show `5 ≤ (Uout b1).card` using five distinct elements.
                                      have hu1R1 : u1 ∈ R1 :=
                                        mem_left_of_trace2PlusOfFinset_eq_some (α := α) htr1
                                      have hu2R1 : u2 ∈ R1 :=
                                        mem_right_of_trace2PlusOfFinset_eq_some_some (α := α)
                                          htr1
                                      have hu2ne_u1 : u2 ≠ u1 :=
                                        ne_left_right_of_trace2PlusOfFinset_eq_some_some (α := α) htr1
                                      have ht2ne_t1 : t2 ≠ t1 :=
                                        ne_left_right_of_trace2PlusOfFinset_eq_some_some (α := α) htU1
                                      -- Elements from `R1` are not `t1` or `t2` by construction.
                                      have hu1ne_t2 : u1 ≠ t2 := (Finset.mem_erase.mp hu1R1).1
                                      have hu1inE1 : u1 ∈ (Uout b1).erase t1 := (Finset.mem_erase.mp hu1R1).2
                                      have hu1ne_t1 : u1 ≠ t1 := (Finset.mem_erase.mp hu1inE1).1
                                      have hu2ne_t2 : u2 ≠ t2 := (Finset.mem_erase.mp hu2R1).1
                                      have hu2inE1 : u2 ∈ (Uout b1).erase t1 := (Finset.mem_erase.mp hu2R1).2
                                      have hu2ne_t1 : u2 ≠ t1 := (Finset.mem_erase.mp hu2inE1).1
                                      have hu3ne_t2 : u3 ≠ t2 := (Finset.mem_erase.mp hu3R1).1
                                      have hu3inE1 : u3 ∈ (Uout b1).erase t1 := (Finset.mem_erase.mp hu3R1).2
                                      have hu3ne_t1 : u3 ≠ t1 := (Finset.mem_erase.mp hu3inE1).1
                                      have hu1U : u1 ∈ Uout b1 := (Finset.mem_erase.mp hu1inE1).2
                                      have hu2U : u2 ∈ Uout b1 := (Finset.mem_erase.mp hu2inE1).2
                                      have hu3U : u3 ∈ Uout b1 := (Finset.mem_erase.mp hu3inE1).2
                                      have hsub5 :
                                          ({t1, t2, u1, u2, u3} : Finset α) ⊆ Uout b1 := by
                                        intro z hz
                                        simp [Finset.mem_insert, Finset.mem_singleton] at hz
                                        rcases hz with rfl | rfl | rfl | rfl | rfl
                                        · exact ht1mem1
                                        · exact ht2mem1
                                        · exact hu1U
                                        · exact hu2U
                                        · exact hu3U
                                      have hcard5' :
                                          ({t1, t2, u1, u2, u3} : Finset α).card = 5 := by
                                        classical
                                        -- Compute the cardinality directly from the `Finset` notation order.
                                        have hu2not : u2 ∉ ({u3} : Finset α) := by
                                          simp [Finset.mem_singleton, hu3ne_u2.symm]
                                        have hu1not : u1 ∉ insert u2 ({u3} : Finset α) := by
                                          simp [Finset.mem_insert, Finset.mem_singleton, hu2ne_u1.symm, hu3ne_u1.symm]
                                        have ht2not : t2 ∉ insert u1 (insert u2 ({u3} : Finset α)) := by
                                          simp [Finset.mem_insert, Finset.mem_singleton, hu1ne_t2.symm, hu2ne_t2.symm, hu3ne_t2.symm]
                                        have ht1not : t1 ∉ insert t2 (insert u1 (insert u2 ({u3} : Finset α))) := by
                                          simp [Finset.mem_insert, Finset.mem_singleton, ht2ne_t1.symm, hu1ne_t1.symm, hu2ne_t1.symm, hu3ne_t1.symm]
                                        simp [Finset.card_insert_of_notMem, hu2not, hu1not, ht2not, ht1not]
                                      have hcard5 :
                                          5 ≤ (Uout b1).card := by
                                        have := Finset.card_le_card hsub5
                                        simpa [hcard5'] using this
                                      have : False :=
                                        (trace5PlusOfFinset_ne_none_of_card_ge_five (α := α) (T := Uout b1) hcard5) hbτ1
                                      exact False.elim this
                              | false =>
                                  -- Symmetric elimination for `R2`.
                                  cases bb2 with
                                  | true =>
                                      have : False := by
                                        -- reuse the same argument on `b2`
                                        cases ou2 with
                                        | none =>
                                            exact
                                              (trace2PlusOfFinset_ne_some_none_true (α := α) (T := R2) (t1 := u1))
                                                htr2
                                        | some u2 =>
                                            -- By symmetry: `bb2=true` forces `|Uout b2|≥5`, contradicting `hbτ2`.
                                            -- We reuse the same skeleton by rewriting indices.
                                            have hR3 : (((R2.erase u1).erase u2).Nonempty) := by
                                              classical
                                              by_cases hR2 : R2.Nonempty
                                              · let t1' : α := Classical.choose hR2
                                                let R2' : Finset α := R2.erase t1'
                                                by_cases hR2' : R2'.Nonempty
                                                · let t2' : α := Classical.choose hR2'
                                                  let R2'' : Finset α := R2'.erase t2'
                                                  by_cases hR2'' : R2''.Nonempty
                                                  · have ht' :
                                                        trace2PlusOfFinset (α := α) R2 =
                                                          some (t1', some t2', true) := by
                                                        simp [trace2PlusOfFinset, hR2, t1', R2', hR2', t2', R2'', hR2'']
                                                    have :
                                                        some (u1, some u2, true) =
                                                          some (t1', some t2', true) := by
                                                      simpa [htr2] using ht'
                                                    have hu1 : u1 = t1' := congrArg Prod.fst (Option.some.inj this)
                                                    have hu2 :
                                                        some u2 = some t2' := by
                                                      exact congrArg (fun p : Option α × Bool => p.1)
                                                        (congrArg Prod.snd (Option.some.inj this))
                                                    have hu2' : u2 = t2' := Option.some.inj hu2
                                                    simpa [R2', R2'', hu1, hu2'] using hR2''
                                                  · have ht' :
                                                        trace2PlusOfFinset (α := α) R2 =
                                                          some (t1', some t2', false) := by
                                                        simp [trace2PlusOfFinset, hR2, t1', R2', hR2', t2', R2'', hR2'']
                                                    have :
                                                        (some (u1, some u2, true) : Option (α × Option α × Bool)) =
                                                          some (t1', some t2', false) := by
                                                      simpa [htr2] using ht'
                                                    have hcontr : (true : Bool) = false :=
                                                      congrArg (fun p : α × Option α × Bool => p.2.2) (Option.some.inj this)
                                                    cases hcontr
                                                · have ht' :
                                                      trace2PlusOfFinset (α := α) R2 =
                                                        some (t1', none, false) := by
                                                      simp [trace2PlusOfFinset, hR2, t1', R2', hR2']
                                                  have :
                                                      (some (u1, some u2, true) : Option (α × Option α × Bool)) =
                                                        some (t1', none, false) := by
                                                    simpa [htr2] using ht'
                                                  have hcontr : (some u2 : Option α) = none :=
                                                    congrArg (fun p : α × Option α × Bool => p.2.1) (Option.some.inj this)
                                                  cases hcontr
                                              · have ht' : trace2PlusOfFinset (α := α) R2 = none := by
                                                  simp [trace2PlusOfFinset, hR2]
                                                have :
                                                    (none : Option (α × Option α × Bool)) = some (u1, some u2, true) := by
                                                  simpa [htr2] using ht'.symm
                                                cases this
                                            let u3 : α := Classical.choose hR3
                                            have hu3mem : u3 ∈ ((R2.erase u1).erase u2) :=
                                              Classical.choose_spec hR3
                                            have hu3mem' : u3 ∈ (R2.erase u1) := (Finset.mem_erase.mp hu3mem).2
                                            have hu3R2 : u3 ∈ R2 := (Finset.mem_erase.mp hu3mem').2
                                            have ht2ne_t1 : t2 ≠ t1 :=
                                              ne_left_right_of_trace2PlusOfFinset_eq_some_some (α := α) htU2
                                            have ht2not : t2 ∉ ({t1} : Finset α) := by
                                              simpa [Finset.mem_singleton] using ht2ne_t1
                                            have hu1R2 : u1 ∈ R2 :=
                                              mem_left_of_trace2PlusOfFinset_eq_some (α := α) htr2
                                            have hu2R2 : u2 ∈ R2 :=
                                              mem_right_of_trace2PlusOfFinset_eq_some_some (α := α) htr2
                                            have hu2ne_u1 : u2 ≠ u1 :=
                                              ne_left_right_of_trace2PlusOfFinset_eq_some_some (α := α) htr2
                                            have hu3ne_u2 : u3 ≠ u2 := (Finset.mem_erase.mp hu3mem).1
                                            have hu3ne_u1 : u3 ≠ u1 := (Finset.mem_erase.mp hu3mem').1
                                            have hu1ne_t2 : u1 ≠ t2 := (Finset.mem_erase.mp hu1R2).1
                                            have hu1inE1 : u1 ∈ (Uout b2).erase t1 := (Finset.mem_erase.mp hu1R2).2
                                            have hu1ne_t1 : u1 ≠ t1 := (Finset.mem_erase.mp hu1inE1).1
                                            have hu2ne_t2 : u2 ≠ t2 := (Finset.mem_erase.mp hu2R2).1
                                            have hu2inE1 : u2 ∈ (Uout b2).erase t1 := (Finset.mem_erase.mp hu2R2).2
                                            have hu2ne_t1 : u2 ≠ t1 := (Finset.mem_erase.mp hu2inE1).1
                                            have hu3ne_t2 : u3 ≠ t2 := (Finset.mem_erase.mp hu3R2).1
                                            have hu3inE1 : u3 ∈ (Uout b2).erase t1 := (Finset.mem_erase.mp hu3R2).2
                                            have hu3ne_t1 : u3 ≠ t1 := (Finset.mem_erase.mp hu3inE1).1
                                            have hu1U : u1 ∈ Uout b2 := (Finset.mem_erase.mp hu1inE1).2
                                            have hu2U : u2 ∈ Uout b2 := (Finset.mem_erase.mp hu2inE1).2
                                            have hu3U : u3 ∈ Uout b2 := (Finset.mem_erase.mp hu3inE1).2
                                            have hsub5 :
                                                ({t1, t2, u1, u2, u3} : Finset α) ⊆ Uout b2 := by
                                              intro z hz
                                              simp [Finset.mem_insert, Finset.mem_singleton] at hz
                                              rcases hz with rfl | rfl | rfl | rfl | rfl
                                              · exact ht1mem2
                                              · exact ht2mem2
                                              · exact hu1U
                                              · exact hu2U
                                              · exact hu3U
                                            have hcard5' :
                                                ({t1, t2, u1, u2, u3} : Finset α).card = 5 := by
                                              classical
                                              -- Compute the cardinality directly from the `Finset` notation order.
                                              have hu2not : u2 ∉ ({u3} : Finset α) := by
                                                simp [Finset.mem_singleton, hu3ne_u2.symm]
                                              have hu1not : u1 ∉ insert u2 ({u3} : Finset α) := by
                                                simp [Finset.mem_insert, Finset.mem_singleton, hu2ne_u1.symm, hu3ne_u1.symm]
                                              have ht2not : t2 ∉ insert u1 (insert u2 ({u3} : Finset α)) := by
                                                simp [Finset.mem_insert, Finset.mem_singleton, hu1ne_t2.symm, hu2ne_t2.symm, hu3ne_t2.symm]
                                              have ht1not :
                                                  t1 ∉ insert t2 (insert u1 (insert u2 ({u3} : Finset α))) := by
                                                simp [Finset.mem_insert, Finset.mem_singleton, ht2ne_t1.symm, hu1ne_t1.symm, hu2ne_t1.symm, hu3ne_t1.symm]
                                              simp [Finset.card_insert_of_notMem, hu2not, hu1not, ht2not, ht1not]
                                            have hcard5 :
                                                5 ≤ (Uout b2).card := by
                                              have := Finset.card_le_card hsub5
                                              simpa [hcard5'] using this
                                            exact
                                              (trace5PlusOfFinset_ne_none_of_card_ge_five (α := α) (T := Uout b2) hcard5) hbτ2
                                      exact False.elim this
                                  | false =>
                                      -- Both traces have `bb=false`, so decode the remainder uniquely from `(u1, ou2)`.
                                      cases ou2 with
                                      | none =>
                                          have h1 : R1 = ({u1} : Finset α) :=
                                            eq_singleton_of_trace2PlusOfFinset_eq_some_none_false (α := α)
                                              htr1
                                          have h2 : R2 = ({u1} : Finset α) :=
                                            eq_singleton_of_trace2PlusOfFinset_eq_some_none_false (α := α)
                                              htr2
                                          simpa [h1, h2]
                                      | some u2 =>
                                          have h1 : R1 = ({u1, u2} : Finset α) :=
                                            eq_pair_of_trace2PlusOfFinset_eq_some_some_false (α := α)
                                              htr1
                                          have h2 : R2 = ({u1, u2} : Finset α) :=
                                            eq_pair_of_trace2PlusOfFinset_eq_some_some_false (α := α)
                                              htr2
                                          simpa [h1, h2]
                    -- Reassemble `Uout` from `{t1,t2}` and the remainder.
                    have hU1 : Uout b1 = ({t1, t2} : Finset α) ∪ R1 := by
                      ext z
                      constructor
                      · intro hz
                        by_cases hz1 : z = t1
                        · subst hz1; simp
                        by_cases hz2 : z = t2
                        · subst hz2; simp [hz1]
                        have hzE1 : z ∈ (Uout b1).erase t1 := Finset.mem_erase.mpr ⟨hz1, hz⟩
                        have hzE2 : z ∈ ((Uout b1).erase t1).erase t2 := Finset.mem_erase.mpr ⟨hz2, hzE1⟩
                        exact Finset.mem_union.mpr (Or.inr (by simpa [R1] using hzE2))
                      · intro hz
                        rcases Finset.mem_union.mp hz with hz | hz
                        · rcases Finset.mem_insert.mp hz with hzEq | hz
                          · subst hzEq
                            exact ht1mem1
                          · have hzEq : z = t2 := by simpa using (Finset.mem_singleton.mp hz)
                            subst hzEq
                            exact ht2mem1
                        · exact (Finset.mem_erase.mp (Finset.mem_erase.mp (by simpa [R1] using hz)).2).2
                    have hU2 : Uout b2 = ({t1, t2} : Finset α) ∪ R2 := by
                      ext z
                      constructor
                      · intro hz
                        by_cases hz1 : z = t1
                        · subst hz1; simp
                        by_cases hz2 : z = t2
                        · subst hz2; simp [hz1]
                        have hzE1 : z ∈ (Uout b2).erase t1 := Finset.mem_erase.mpr ⟨hz1, hz⟩
                        have hzE2 : z ∈ ((Uout b2).erase t1).erase t2 := Finset.mem_erase.mpr ⟨hz2, hzE1⟩
                        exact Finset.mem_union.mpr (Or.inr (by simpa [R2] using hzE2))
                      · intro hz
                        rcases Finset.mem_union.mp hz with hz | hz
                        · rcases Finset.mem_insert.mp hz with hzEq | hz
                          · subst hzEq
                            exact ht1mem2
                          · have hzEq : z = t2 := by simpa using (Finset.mem_singleton.mp hz)
                            subst hzEq
                            exact ht2mem2
                        · exact (Finset.mem_erase.mp (Finset.mem_erase.mp (by simpa [R2] using hz)).2).2
                    -- Avoid `simp` here: it can hit max recursion depth on the large local context.
                    have hUR :
                        ({t1, t2} : Finset α) ∪ R1 =
                          ({t1, t2} : Finset α) ∪ R2 :=
                      congrArg (fun s => ({t1, t2} : Finset α) ∪ s) hR
                    exact hU1.trans (hUR.trans hU2.symm)
            | false =>
                -- `outsideTrace.hasMore = false`: decode `Uout` exactly.
                cases ot2 with
                | none =>
                    have hout1 : outsideTrace (family := family) (S := b1.1.1) (y := yw1.1) yw1.2 =
                        some (t1, none, false) := by
                      have : (sigOut b1).1.2.2.2.2.2 = σOut.1.2.2.2.2.2 := by simpa [hb1sig]
                      simpa [sigOut, sig0, perXSignature_of_hardFiber, perXSignature, outsideTrace, yw1, hout] using this
                    have hout2 : outsideTrace (family := family) (S := b2.1.1) (y := yw2.1) yw2.2 =
                        some (t1, none, false) := by
                      have : (sigOut b2).1.2.2.2.2.2 = σOut.1.2.2.2.2.2 := by simpa [hb2sig]
                      simpa [sigOut, sig0, perXSignature_of_hardFiber, perXSignature, outsideTrace, yw2, hout] using this
                    have h1 : Uout b1 = ({t1} : Finset α) := by
                      simpa [Uout, yw1] using
                        (S_sdiff_union_eq_singleton_of_outsideTrace_eq_some_none_false (family := family)
                          (S := b1.1.1) (y := yw1.1) yw1.2 (t1 := t1) hout1)
                    have h2 : Uout b2 = ({t1} : Finset α) := by
                      simpa [Uout, yw2] using
                        (S_sdiff_union_eq_singleton_of_outsideTrace_eq_some_none_false (family := family)
                          (S := b2.1.1) (y := yw2.1) yw2.2 (t1 := t1) hout2)
                    simpa [h1, h2]
                | some t2 =>
                    have hout1 : outsideTrace (family := family) (S := b1.1.1) (y := yw1.1) yw1.2 =
                        some (t1, some t2, false) := by
                      have : (sigOut b1).1.2.2.2.2.2 = σOut.1.2.2.2.2.2 := by simpa [hb1sig]
                      simpa [sigOut, sig0, perXSignature_of_hardFiber, perXSignature, outsideTrace, yw1, hout] using this
                    have hout2 : outsideTrace (family := family) (S := b2.1.1) (y := yw2.1) yw2.2 =
                        some (t1, some t2, false) := by
                      have : (sigOut b2).1.2.2.2.2.2 = σOut.1.2.2.2.2.2 := by simpa [hb2sig]
                      simpa [sigOut, sig0, perXSignature_of_hardFiber, perXSignature, outsideTrace, yw2, hout] using this
                    have h1 : Uout b1 = ({t1, t2} : Finset α) := by
                      simpa [Uout, yw1] using
                        (S_sdiff_union_eq_pair_of_outsideTrace_eq_some_some_false (family := family)
                          (S := b1.1.1) (y := yw1.1) yw1.2 (t1 := t1) (t2 := t2) hout1)
                    have h2 : Uout b2 = ({t1, t2} : Finset α) := by
                      simpa [Uout, yw2] using
                        (S_sdiff_union_eq_pair_of_outsideTrace_eq_some_some_false (family := family)
                          (S := b2.1.1) (y := yw2.1) yw2.2 (t1 := t1) (t2 := t2) hout2)
                    rw [h1, h2]
    -- Now reconstruct `S` from the common `core.erase y` and `Uout`.
    have hS1 : b1.1.1 = (yw1.2.core.erase yw1.1) ∪ Uout b1 :=
      S_eq_coreErase_union_sdiff_union_of_blockedUnionWitness (family := family) (S := b1.1.1)
        (y := yw1.1) yw1.2 hyNot1
    have hS2 : b2.1.1 = (yw2.2.core.erase yw2.1) ∪ Uout b2 :=
      S_eq_coreErase_union_sdiff_union_of_blockedUnionWitness (family := family) (S := b2.1.1)
        (y := yw2.1) yw2.2 hyNot2
    have hEqSets : b1.1.1 = b2.1.1 := by
      calc
        b1.1.1 = (yw1.2.core.erase yw1.1) ∪ Uout b1 := hS1
        _ = (yw2.2.core.erase yw2.1) ∪ Uout b2 := by simpa [hcoreEq, hUeq]
        _ = b2.1.1 := by simpa [hS2]
    have hEq1 : b1.1 = b2.1 := Subtype.ext hEqSets
    exact Subtype.ext hEq1
  -- Expand `B.card` as a sum of fiber cards over the image of `f`.
  have hsum :
      B.card =
        ∑ p ∈ B.image f,
          (B.filter (fun b => f b = p)).card := by
    simpa [Nat.card_eq_fintype_card] using
      (Finset.card_eq_sum_card_image (f := f) (s := B))
  have hcard_le_img : B.card ≤ (B.image f).card := by
    -- Bound each fiber by `1`.
    calc
      B.card =
          ∑ p ∈ B.image f,
            (B.filter (fun b => f b = p)).card := hsum
      _ ≤ ∑ _p ∈ B.image f, 1 := by
            refine Finset.sum_le_sum ?_
            intro p hp
            exact hfiber p hp
      _ = (B.image f).card := by
            simp
  -- Bound the image size by `(n+1)^2`.
  have him_sub : B.image f ⊆ T.product T := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨b, hbB, rfl⟩
    have hUsub : Uout b ⊆ ground := by
      have hbDom : b.1.1 ∈ dom := b.1.2
      have hSfam : b.1.1 ∈ family :=
        mem_family_of_mem_o1aWitnessLiftDomWL (family := family) (h0 := h0) (S := b.1.1) hbDom
      have hSsub : b.1.1 ⊆ ground := Finset.mem_powerset.mp (hreg.1 hSfam)
      intro z hz
      have hzS : z ∈ b.1.1 := (Finset.mem_sdiff.mp hz).1
      exact hSsub hzS
    have ho1 : (f b).1 ∈ T := by
      -- Case split on the fixed `outsideTrace` component and the remainder trace.
      cases hOut : σOut.1.2.2.2.2.2 with
      | none =>
          refine (mem_optionOfFinset_iff (α := α) (T := ground) (o := (f b).1)).2 (Or.inl ?_)
          simp [f, hOut]
      | some triple =>
          rcases triple with ⟨t1, ot2, bMore⟩
          cases bMore with
          | false =>
              cases ot2 <;>
                refine (mem_optionOfFinset_iff (α := α) (T := ground) (o := (f b).1)).2 (Or.inl ?_) <;>
                simp [f, hOut]
          | true =>
              cases ot2 with
              | none =>
                  refine (mem_optionOfFinset_iff (α := α) (T := ground) (o := (f b).1)).2 (Or.inl ?_)
                  simp [f, hOut]
              | some t2 =>
                  set R : Finset α := (((Uout b).erase t1).erase t2)
                  cases hR : trace2PlusOfFinset (α := α) R with
                  | none =>
                      refine (mem_optionOfFinset_iff (α := α) (T := ground) (o := (f b).1)).2 (Or.inl ?_)
                      simp [f, hOut, hR, R]
                  | some tr =>
                      rcases tr with ⟨u1, ou2, bb⟩
                      have hR' : trace2PlusOfFinset (α := α) R = some (u1, ou2, bb) := by
                        simpa [hR] using hR
                      have hu1R : u1 ∈ R :=
                        mem_left_of_trace2PlusOfFinset_eq_some (α := α) hR'
                      have hu1E2 : u1 ∈ ((Uout b).erase t1).erase t2 := by
                        simpa [R] using hu1R
                      have hu1E1 : u1 ∈ (Uout b).erase t1 := (Finset.mem_erase.mp hu1E2).2
                      have hu1U : u1 ∈ Uout b := (Finset.mem_erase.mp hu1E1).2
                      have hu1G : u1 ∈ ground := hUsub hu1U
                      refine
                        (mem_optionOfFinset_iff (α := α) (T := ground) (o := (f b).1)).2
                          (Or.inr ⟨u1, hu1G, ?_⟩)
                      simp [f, hOut, hR, R]
    have ho2 : (f b).2 ∈ T := by
      cases hOut : σOut.1.2.2.2.2.2 with
      | none =>
          refine (mem_optionOfFinset_iff (α := α) (T := ground) (o := (f b).2)).2 (Or.inl ?_)
          simp [f, hOut]
      | some triple =>
          rcases triple with ⟨t1, ot2, bMore⟩
          cases bMore with
          | false =>
              cases ot2 <;>
                refine (mem_optionOfFinset_iff (α := α) (T := ground) (o := (f b).2)).2 (Or.inl ?_) <;>
                simp [f, hOut]
          | true =>
              cases ot2 with
              | none =>
                  refine (mem_optionOfFinset_iff (α := α) (T := ground) (o := (f b).2)).2 (Or.inl ?_)
                  simp [f, hOut]
              | some t2 =>
                  set R : Finset α := (((Uout b).erase t1).erase t2)
                  cases hR : trace2PlusOfFinset (α := α) R with
                  | none =>
                      refine (mem_optionOfFinset_iff (α := α) (T := ground) (o := (f b).2)).2 (Or.inl ?_)
                      simp [f, hOut, hR, R]
                  | some tr =>
                      rcases tr with ⟨u1, ou2, bb⟩
                      cases ou2 with
                      | none =>
                          refine (mem_optionOfFinset_iff (α := α) (T := ground) (o := (f b).2)).2 (Or.inl ?_)
                          simp [f, hOut, hR, R]
                      | some u2 =>
                          have hR' : trace2PlusOfFinset (α := α) R = some (u1, some u2, bb) := by
                            exact hR
                          have hu2R : u2 ∈ R :=
                            mem_right_of_trace2PlusOfFinset_eq_some_some (α := α) hR'
                          have hu2E2 : u2 ∈ ((Uout b).erase t1).erase t2 := by
                            change u2 ∈ R
                            exact hu2R
                          have hu2E1 : u2 ∈ (Uout b).erase t1 := (Finset.mem_erase.mp hu2E2).2
                          have hu2U : u2 ∈ Uout b := (Finset.mem_erase.mp hu2E1).2
                          have hu2G : u2 ∈ ground := hUsub hu2U
                          refine
                            (mem_optionOfFinset_iff (α := α) (T := ground) (o := (f b).2)).2
                              (Or.inr ⟨u2, hu2G, ?_⟩)
                          simp [f, hOut, hR, R]
    exact Finset.mem_product.mpr ⟨ho1, ho2⟩
  have hTcard : T.card ≤ ground.card + 1 := card_optionOfFinset_le_succ (α := α) ground
  have himg : (B.image f).card ≤ (T.product T).card := Finset.card_le_card him_sub
  calc
    B.card ≤ (B.image f).card := hcard_le_img
    _ ≤ (T.product T).card := himg
    _ = T.card * T.card := by simp
    _ ≤ (ground.card + 1) * (ground.card + 1) :=
      Nat.mul_le_mul hTcard hTcard

theorem card_Bucket_perXSignatureOutMore_filter_X_sdiff_eq_singleton_le_one
    (hreg : O1aUpgradeRegime family ground A0 h0)
    {k : WLcertKey α}
    {Sstar : {S // S ∈ o1aWitnessLiftDomWL family h0}}
    {x : α}
    (hSstar :
      Sstar ∈ wlcertAdmissibleFiber_hNotMem (family := family) (o1aWitnessLiftDomWL family h0) k)
    (σOut : PerXSignatureOutMore α) :
    let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h0
    let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
    let Fx0 :
        Finset {S // S ∈ dom} :=
      wlcertAdmissibleFiber_hNotMem_fiberForX (dom := dom) fiber Sstar.1 x
    let sig0 : {Ssub // Ssub ∈ Fx0} → PerXSignature α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      perXSignature_of_hardFiber (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1) Sstar.2 b.1.2 hcert_star hcert_sub hne
    let Uout : {Ssub // Ssub ∈ Fx0} → Finset α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      let yw :
          Σ y : α, BlockedUnionWitness family b.1.1 y :=
        chooseYAndWitness_of_hardFiber
          (family := family) (ground := ground) (A0 := A0) (h0 := h0)
          hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
          Sstar.2 b.1.2 hcert_star hcert_sub hne
      b.1.1 \ (yw.2.A ∪ yw.2.B)
    let sigOut : {Ssub // Ssub ∈ Fx0} → PerXSignatureOutMore α := fun b =>
      (sig0 b,
        trace5PlusOfFinset (α := α) (Uout b),
        t6OptionOfTrace5Plus (α := α) (Uout b))
    let X : Finset α := ground \ (k.2.2.1 ∪ k.2.2.2.1)
    let y : α := σOut.1.1
    let B : Finset {Ssub // Ssub ∈ Fx0} := Bucket (Fx := Fx0.attach) sigOut σOut
    (B.filter (fun b => X \ b.1.1 = ({y} : Finset α))).card ≤ 1 := by
  classical
  intro dom fiber Fx0 sig0 Uout sigOut X y B
  refine Finset.card_le_one.2 ?_
  intro b1 hb1 b2 hb2
  have hb1B : b1 ∈ B := (Finset.mem_filter.mp hb1).1
  have hb2B : b2 ∈ B := (Finset.mem_filter.mp hb2).1
  have hb1X : X \ b1.1.1 = ({y} : Finset α) := (Finset.mem_filter.mp hb1).2
  have hb2X : X \ b2.1.1 = ({y} : Finset α) := (Finset.mem_filter.mp hb2).2
  -- Extract the hNotMem certificate for each completion (since `Fx0 ⊆ fiber`).
  have hb1Fiber : b1.1 ∈ fiber := (Finset.mem_filter.mp b1.2).1
  have hb2Fiber : b2.1 ∈ fiber := (Finset.mem_filter.mp b2.2).1
  have hcert1 :
      ∃ cert : WLcert family b1.1.1, WLcert.key cert = k ∧ cert.h ∉ b1.1.1 :=
    (Finset.mem_filter.mp hb1Fiber).2
  have hcert2 :
      ∃ cert : WLcert family b2.1.1, WLcert.key cert = k ∧ cert.h ∉ b2.1.1 :=
    (Finset.mem_filter.mp hb2Fiber).2
  -- Use the sharp collapse lemma `X \\ S = {y} → S = keyBase ∪ X.erase y`.
  have hS1 :
      b1.1.1 = PerXSubfiber.keyBase (α := α) (k := k) ∪ (X.erase y) := by
    -- Rewrite `X` back to the unfolded definition expected by the helper lemma.
    simpa [X] using
      (eq_keyBase_union_X_erase_of_X_sdiff_eq_singleton (family := family) (ground := ground)
        (A0 := A0) (h0 := h0) hreg (k := k) (S := b1.1.1) b1.1.2 hcert1 (y := y) (by simpa [X] using hb1X))
  have hS2 :
      b2.1.1 = PerXSubfiber.keyBase (α := α) (k := k) ∪ (X.erase y) := by
    simpa [X] using
      (eq_keyBase_union_X_erase_of_X_sdiff_eq_singleton (family := family) (ground := ground)
        (A0 := A0) (h0 := h0) hreg (k := k) (S := b2.1.1) b2.1.2 hcert2 (y := y) (by simpa [X] using hb2X))
  have hEqSets : b1.1.1 = b2.1.1 := by simpa [hS1, hS2]
  -- Conclude equality in the nested subtype.
  have hEq1 : b1.1 = b2.1 := Subtype.ext hEqSets
  exact Subtype.ext hEq1

theorem card_Bucket_perXSignatureOutMore_filter_X_sdiff_eq_pair_le_one
    (hreg : O1aUpgradeRegime family ground A0 h0)
    {k : WLcertKey α}
    {Sstar : {S // S ∈ o1aWitnessLiftDomWL family h0}}
    {x : α}
    (hSstar :
      Sstar ∈ wlcertAdmissibleFiber_hNotMem (family := family) (o1aWitnessLiftDomWL family h0) k)
    (σOut : PerXSignatureOutMore α)
    {y1 y2 : α} :
    let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h0
    let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
    let Fx0 :
        Finset {S // S ∈ dom} :=
      wlcertAdmissibleFiber_hNotMem_fiberForX (dom := dom) fiber Sstar.1 x
    let sig0 : {Ssub // Ssub ∈ Fx0} → PerXSignature α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      perXSignature_of_hardFiber (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1) Sstar.2 b.1.2 hcert_star hcert_sub hne
    let Uout : {Ssub // Ssub ∈ Fx0} → Finset α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      let yw :
          Σ y : α, BlockedUnionWitness family b.1.1 y :=
        chooseYAndWitness_of_hardFiber
          (family := family) (ground := ground) (A0 := A0) (h0 := h0)
          hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
          Sstar.2 b.1.2 hcert_star hcert_sub hne
      b.1.1 \ (yw.2.A ∪ yw.2.B)
    let sigOut : {Ssub // Ssub ∈ Fx0} → PerXSignatureOutMore α := fun b =>
      (sig0 b,
        trace5PlusOfFinset (α := α) (Uout b),
        t6OptionOfTrace5Plus (α := α) (Uout b))
    let X : Finset α := ground \ (k.2.2.1 ∪ k.2.2.2.1)
    let B : Finset {Ssub // Ssub ∈ Fx0} := Bucket (Fx := Fx0.attach) sigOut σOut
    (B.filter (fun b => X \ b.1.1 = ({y1, y2} : Finset α))).card ≤ 1 := by
  classical
  intro dom fiber Fx0 sig0 Uout sigOut X B
  refine Finset.card_le_one.2 ?_
  intro b1 hb1 b2 hb2
  have hb1B : b1 ∈ B := (Finset.mem_filter.mp hb1).1
  have hb2B : b2 ∈ B := (Finset.mem_filter.mp hb2).1
  have hb1X : X \ b1.1.1 = ({y1, y2} : Finset α) := (Finset.mem_filter.mp hb1).2
  have hb2X : X \ b2.1.1 = ({y1, y2} : Finset α) := (Finset.mem_filter.mp hb2).2
  -- Extract the hNotMem certificate for each completion (since `Fx0 ⊆ fiber`).
  have hb1Fiber : b1.1 ∈ fiber := (Finset.mem_filter.mp b1.2).1
  have hb2Fiber : b2.1 ∈ fiber := (Finset.mem_filter.mp b2.2).1
  have hcert1 :
      ∃ cert : WLcert family b1.1.1, WLcert.key cert = k ∧ cert.h ∉ b1.1.1 :=
    (Finset.mem_filter.mp hb1Fiber).2
  have hcert2 :
      ∃ cert : WLcert family b2.1.1, WLcert.key cert = k ∧ cert.h ∉ b2.1.1 :=
    (Finset.mem_filter.mp hb2Fiber).2
  -- Use the sharp collapse lemma `X \\ S = {y1,y2} → S = keyBase ∪ X.erase y1.erase y2`.
  have hS1 :
      b1.1.1 =
        PerXSubfiber.keyBase (α := α) (k := k) ∪ ((X.erase y1).erase y2) := by
    simpa [X] using
      (eq_keyBase_union_X_erase_erase_of_X_sdiff_eq_pair (family := family) (ground := ground)
        (A0 := A0) (h0 := h0) hreg (k := k) (S := b1.1.1) b1.1.2 hcert1 (y1 := y1) (y2 := y2)
        (by simpa [X] using hb1X))
  have hS2 :
      b2.1.1 =
        PerXSubfiber.keyBase (α := α) (k := k) ∪ ((X.erase y1).erase y2) := by
    simpa [X] using
      (eq_keyBase_union_X_erase_erase_of_X_sdiff_eq_pair (family := family) (ground := ground)
        (A0 := A0) (h0 := h0) hreg (k := k) (S := b2.1.1) b2.1.2 hcert2 (y1 := y1) (y2 := y2)
        (by simpa [X] using hb2X))
  have hEqSets : b1.1.1 = b2.1.1 := by simpa [hS1, hS2]
  -- Conclude equality in the nested subtype.
  have hEq1 : b1.1 = b2.1 := Subtype.ext hEqSets
  exact Subtype.ext hEq1

theorem card_Bucket_perXSignatureOutMore_filter_X_sdiff_eq_triple_le_one
    (hreg : O1aUpgradeRegime family ground A0 h0)
    {k : WLcertKey α}
    {Sstar : {S // S ∈ o1aWitnessLiftDomWL family h0}}
    {x : α}
    (hSstar :
      Sstar ∈ wlcertAdmissibleFiber_hNotMem (family := family) (o1aWitnessLiftDomWL family h0) k)
    (σOut : PerXSignatureOutMore α)
    {y1 y2 y3 : α} :
    let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h0
    let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
    let Fx0 :
        Finset {S // S ∈ dom} :=
      wlcertAdmissibleFiber_hNotMem_fiberForX (dom := dom) fiber Sstar.1 x
    let sig0 : {Ssub // Ssub ∈ Fx0} → PerXSignature α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      perXSignature_of_hardFiber (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1) Sstar.2 b.1.2 hcert_star hcert_sub hne
    let Uout : {Ssub // Ssub ∈ Fx0} → Finset α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      let yw :
          Σ y : α, BlockedUnionWitness family b.1.1 y :=
        chooseYAndWitness_of_hardFiber
          (family := family) (ground := ground) (A0 := A0) (h0 := h0)
          hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
          Sstar.2 b.1.2 hcert_star hcert_sub hne
      b.1.1 \ (yw.2.A ∪ yw.2.B)
    let sigOut : {Ssub // Ssub ∈ Fx0} → PerXSignatureOutMore α := fun b =>
      (sig0 b,
        trace5PlusOfFinset (α := α) (Uout b),
        t6OptionOfTrace5Plus (α := α) (Uout b))
    let X : Finset α := ground \ (k.2.2.1 ∪ k.2.2.2.1)
    let B : Finset {Ssub // Ssub ∈ Fx0} := Bucket (Fx := Fx0.attach) sigOut σOut
    (B.filter (fun b => X \ b.1.1 = ({y1, y2, y3} : Finset α))).card ≤ 1 := by
  classical
  intro dom fiber Fx0 sig0 Uout sigOut X B
  refine Finset.card_le_one.2 ?_
  intro b1 hb1 b2 hb2
  have hb1B : b1 ∈ B := (Finset.mem_filter.mp hb1).1
  have hb2B : b2 ∈ B := (Finset.mem_filter.mp hb2).1
  have hb1X : X \ b1.1.1 = ({y1, y2, y3} : Finset α) := (Finset.mem_filter.mp hb1).2
  have hb2X : X \ b2.1.1 = ({y1, y2, y3} : Finset α) := (Finset.mem_filter.mp hb2).2
  -- Extract the hNotMem certificate for each completion (since `Fx0 ⊆ fiber`).
  have hb1Fiber : b1.1 ∈ fiber := (Finset.mem_filter.mp b1.2).1
  have hb2Fiber : b2.1 ∈ fiber := (Finset.mem_filter.mp b2.2).1
  have hcert1 :
      ∃ cert : WLcert family b1.1.1, WLcert.key cert = k ∧ cert.h ∉ b1.1.1 :=
    (Finset.mem_filter.mp hb1Fiber).2
  have hcert2 :
      ∃ cert : WLcert family b2.1.1, WLcert.key cert = k ∧ cert.h ∉ b2.1.1 :=
    (Finset.mem_filter.mp hb2Fiber).2
  -- Use the sharp triple-collapse lemma `X \\ S = {y1,y2,y3} → S = keyBase ∪ X.erase y1.erase y2.erase y3`.
  have hS1 :
      b1.1.1 =
        PerXSubfiber.keyBase (α := α) (k := k) ∪ (((X.erase y1).erase y2).erase y3) := by
    simpa [X] using
      (eq_keyBase_union_X_erase_erase_erase_of_X_sdiff_eq_triple (family := family)
        (ground := ground) (A0 := A0) (h0 := h0) hreg (k := k) (S := b1.1.1) b1.1.2 hcert1
        (y1 := y1) (y2 := y2) (y3 := y3) (by simpa [X] using hb1X))
  have hS2 :
      b2.1.1 =
        PerXSubfiber.keyBase (α := α) (k := k) ∪ (((X.erase y1).erase y2).erase y3) := by
    simpa [X] using
      (eq_keyBase_union_X_erase_erase_erase_of_X_sdiff_eq_triple (family := family)
        (ground := ground) (A0 := A0) (h0 := h0) hreg (k := k) (S := b2.1.1) b2.1.2 hcert2
        (y1 := y1) (y2 := y2) (y3 := y3) (by simpa [X] using hb2X))
  have hEqSets : b1.1.1 = b2.1.1 := by simpa [hS1, hS2]
  have hEq1 : b1.1 = b2.1 := Subtype.ext hEqSets
  exact Subtype.ext hEq1

theorem card_Bucket_perXSignatureOutMore_filter_X_sdiff_eq_quad_le_one
    (hreg : O1aUpgradeRegime family ground A0 h0)
    {k : WLcertKey α}
    {Sstar : {S // S ∈ o1aWitnessLiftDomWL family h0}}
    {x : α}
    (hSstar :
      Sstar ∈ wlcertAdmissibleFiber_hNotMem (family := family) (o1aWitnessLiftDomWL family h0) k)
    (σOut : PerXSignatureOutMore α)
    {y1 y2 y3 y4 : α} :
    let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h0
    let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
    let Fx0 :
        Finset {S // S ∈ dom} :=
      wlcertAdmissibleFiber_hNotMem_fiberForX (dom := dom) fiber Sstar.1 x
    let sig0 : {Ssub // Ssub ∈ Fx0} → PerXSignature α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      perXSignature_of_hardFiber (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1) Sstar.2 b.1.2 hcert_star hcert_sub hne
    let Uout : {Ssub // Ssub ∈ Fx0} → Finset α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      let yw :
          Σ y : α, BlockedUnionWitness family b.1.1 y :=
        chooseYAndWitness_of_hardFiber
          (family := family) (ground := ground) (A0 := A0) (h0 := h0)
          hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
          Sstar.2 b.1.2 hcert_star hcert_sub hne
      b.1.1 \ (yw.2.A ∪ yw.2.B)
    let sigOut : {Ssub // Ssub ∈ Fx0} → PerXSignatureOutMore α := fun b =>
      (sig0 b,
        trace5PlusOfFinset (α := α) (Uout b),
        t6OptionOfTrace5Plus (α := α) (Uout b))
    let X : Finset α := ground \ (k.2.2.1 ∪ k.2.2.2.1)
    let B : Finset {Ssub // Ssub ∈ Fx0} := Bucket (Fx := Fx0.attach) sigOut σOut
    (B.filter (fun b => X \ b.1.1 = ({y1, y2, y3, y4} : Finset α))).card ≤ 1 := by
  classical
  intro dom fiber Fx0 sig0 Uout sigOut X B
  refine Finset.card_le_one.2 ?_
  intro b1 hb1 b2 hb2
  have hb1X : X \ b1.1.1 = ({y1, y2, y3, y4} : Finset α) := (Finset.mem_filter.mp hb1).2
  have hb2X : X \ b2.1.1 = ({y1, y2, y3, y4} : Finset α) := (Finset.mem_filter.mp hb2).2
  have hb1Fiber : b1.1 ∈ fiber := (Finset.mem_filter.mp b1.2).1
  have hb2Fiber : b2.1 ∈ fiber := (Finset.mem_filter.mp b2.2).1
  have hcert1 :
      ∃ cert : WLcert family b1.1.1, WLcert.key cert = k ∧ cert.h ∉ b1.1.1 :=
    (Finset.mem_filter.mp hb1Fiber).2
  have hcert2 :
      ∃ cert : WLcert family b2.1.1, WLcert.key cert = k ∧ cert.h ∉ b2.1.1 :=
    (Finset.mem_filter.mp hb2Fiber).2
  have hS1 :
      b1.1.1 =
        PerXSubfiber.keyBase (α := α) (k := k) ∪ ((((X.erase y1).erase y2).erase y3).erase y4) := by
    simpa [X] using
      (eq_keyBase_union_X_erase_erase_erase_erase_of_X_sdiff_eq_quad (family := family)
        (ground := ground) (A0 := A0) (h0 := h0) hreg (k := k) (S := b1.1.1) b1.1.2 hcert1
        (y1 := y1) (y2 := y2) (y3 := y3) (y4 := y4) (by simpa [X] using hb1X))
  have hS2 :
      b2.1.1 =
        PerXSubfiber.keyBase (α := α) (k := k) ∪ ((((X.erase y1).erase y2).erase y3).erase y4) := by
    simpa [X] using
      (eq_keyBase_union_X_erase_erase_erase_erase_of_X_sdiff_eq_quad (family := family)
        (ground := ground) (A0 := A0) (h0 := h0) hreg (k := k) (S := b2.1.1) b2.1.2 hcert2
        (y1 := y1) (y2 := y2) (y3 := y3) (y4 := y4) (by simpa [X] using hb2X))
  have hEqSets : b1.1.1 = b2.1.1 := by simpa [hS1, hS2]
  have hEq1 : b1.1 = b2.1 := Subtype.ext hEqSets
  exact Subtype.ext hEq1

theorem card_Bucket_perXSignatureOutMore_filter_Xerase_h0_sdiff_eq_quad_le_one
    (hreg : O1aUpgradeRegime family ground A0 h0)
    {k : WLcertKey α}
    {Sstar : {S // S ∈ o1aWitnessLiftDomWL family h0}}
    {x : α}
    (hSstar :
      Sstar ∈ wlcertAdmissibleFiber_hNotMem (family := family) (o1aWitnessLiftDomWL family h0) k)
    (σOut : PerXSignatureOutMore α)
    {y1 y2 y3 y4 : α} :
    let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h0
    let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
    let Fx0 :
        Finset {S // S ∈ dom} :=
      wlcertAdmissibleFiber_hNotMem_fiberForX (dom := dom) fiber Sstar.1 x
    let sig0 : {Ssub // Ssub ∈ Fx0} → PerXSignature α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      perXSignature_of_hardFiber (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1) Sstar.2 b.1.2 hcert_star hcert_sub hne
    let Uout : {Ssub // Ssub ∈ Fx0} → Finset α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      let yw :
          Σ y : α, BlockedUnionWitness family b.1.1 y :=
        chooseYAndWitness_of_hardFiber
          (family := family) (ground := ground) (A0 := A0) (h0 := h0)
          hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
          Sstar.2 b.1.2 hcert_star hcert_sub hne
      b.1.1 \ (yw.2.A ∪ yw.2.B)
    let sigOut : {Ssub // Ssub ∈ Fx0} → PerXSignatureOutMore α := fun b =>
      (sig0 b,
        trace5PlusOfFinset (α := α) (Uout b),
        t6OptionOfTrace5Plus (α := α) (Uout b))
    let X : Finset α := ground \ (k.2.2.1 ∪ k.2.2.2.1)
    let B : Finset {Ssub // Ssub ∈ Fx0} := Bucket (Fx := Fx0.attach) sigOut σOut
    (B.filter (fun b => (X.erase h0) \ b.1.1 = ({y1, y2, y3, y4} : Finset α))).card ≤ 1 := by
  classical
  intro dom fiber Fx0 sig0 Uout sigOut X B
  refine Finset.card_le_one.2 ?_
  intro b1 hb1 b2 hb2
  have hb1X : (X.erase h0) \ b1.1.1 = ({y1, y2, y3, y4} : Finset α) := (Finset.mem_filter.mp hb1).2
  have hb2X : (X.erase h0) \ b2.1.1 = ({y1, y2, y3, y4} : Finset α) := (Finset.mem_filter.mp hb2).2
  have hb1Fiber : b1.1 ∈ fiber := (Finset.mem_filter.mp b1.2).1
  have hb2Fiber : b2.1 ∈ fiber := (Finset.mem_filter.mp b2.2).1
  have hcert1 :
      ∃ cert : WLcert family b1.1.1, WLcert.key cert = k ∧ cert.h ∉ b1.1.1 :=
    (Finset.mem_filter.mp hb1Fiber).2
  have hcert2 :
      ∃ cert : WLcert family b2.1.1, WLcert.key cert = k ∧ cert.h ∉ b2.1.1 :=
    (Finset.mem_filter.mp hb2Fiber).2
  have hS1 :
      b1.1.1 =
        PerXSubfiber.keyBase (α := α) (k := k) ∪
          (((((X.erase h0).erase y1).erase y2).erase y3).erase y4) := by
    simpa [X] using
      (eq_keyBase_union_Xerase_h0_erase_erase_erase_erase_of_Xerase_h0_sdiff_eq_quad
        (family := family) (ground := ground) (A0 := A0) (h0 := h0) hreg (k := k) (S := b1.1.1)
        b1.1.2 hcert1 (y1 := y1) (y2 := y2) (y3 := y3) (y4 := y4)
        (by simpa [X] using hb1X))
  have hS2 :
      b2.1.1 =
        PerXSubfiber.keyBase (α := α) (k := k) ∪
          (((((X.erase h0).erase y1).erase y2).erase y3).erase y4) := by
    simpa [X] using
      (eq_keyBase_union_Xerase_h0_erase_erase_erase_erase_of_Xerase_h0_sdiff_eq_quad
        (family := family) (ground := ground) (A0 := A0) (h0 := h0) hreg (k := k) (S := b2.1.1)
        b2.1.2 hcert2 (y1 := y1) (y2 := y2) (y3 := y3) (y4 := y4)
        (by simpa [X] using hb2X))
  have hEqSets : b1.1.1 = b2.1.1 := by simpa [hS1, hS2]
  have hEq1 : b1.1 = b2.1 := Subtype.ext hEqSets
  exact Subtype.ext hEq1

/-!
OutMore τ=true residue helper (|Uout| ≥ 6):

We will bound completions in a fixed `Bucket(σOut)` by splitting on the size of the missing set
`X \\ S` inside the “free region” `X := ground \\ (kA ∪ kB)`:

- If `X \\ S = {y}` or `{y,h0}`, we collapse to `S = keyBase ∪ X.erase …` (card ≤ 1).
- Otherwise, we choose a canonical `z ∈ (X \\ S) \\ {y,h0}` and use the one-step blocked extension
  witness for `S ∪ {z}` to build a bounded-fiber map.

This lemma is a *wiring* step: it sets up the canonical `z` selection that all later bounds will use.
-/

theorem mem_pair_of_erase_erase_eq_empty_of_mem
    {X S : Finset α} {y0 h0 : α}
    (hy : y0 ∈ X \ S)
    (hZ : (((X \ S).erase y0).erase h0) = (∅ : Finset α)) :
    X \ S = ({y0} : Finset α) ∨ X \ S = ({y0, h0} : Finset α) := by
  classical
  -- Every element of `X \\ S` is either `y` or `h0`.
  have hSub : X \ S ⊆ ({y0, h0} : Finset α) := by
    intro z hz
    by_cases hzy : z = y0
    · subst z
      exact Finset.mem_insert_self y0 ({h0} : Finset α)
    · -- If `z ≠ y`, show `z = h0` by contradiction using `hZ`.
      have hzErase : z ∈ (X \ S).erase y0 := by
        exact Finset.mem_erase.mpr ⟨hzy, hz⟩
      by_cases hzh0 : z = h0
      · subst hzh0
        exact Finset.mem_insert_of_mem (by simpa using (Finset.mem_singleton_self h0))
      · have hzErase2 : z ∈ ((X \ S).erase y0).erase h0 := by
          exact Finset.mem_erase.mpr ⟨hzh0, hzErase⟩
        -- But the double-erase is empty.
        have : z ∈ (∅ : Finset α) := by simpa [hZ] using hzErase2
        exact False.elim (Finset.notMem_empty z this)
  -- Since `y ∈ X \\ S`, the set is either `{y}` or `{y,h0}`.
  have hyMem : y0 ∈ X \ S := hy
  by_cases hh0 : h0 ∈ X \ S
  · right
    ext z
    constructor
    · intro hz
      have : z ∈ ({y0, h0} : Finset α) := hSub hz
      exact this
    · intro hz
      -- membership in `{y,h0}` gives `z=y` or `z=h0`, both in `X\\S`.
      rcases Finset.mem_insert.mp hz with hzEq | hz'
      · subst z
        exact hyMem
      · have hzEq : z = h0 := by simpa using (Finset.mem_singleton.mp hz')
        subst hzEq
        exact hh0
  · left
    -- If `h0 ∉ X \\ S`, then `X \\ S = {y}`.
    ext z
    constructor
    · intro hz
      have : z ∈ ({y0, h0} : Finset α) := hSub hz
      rcases Finset.mem_insert.mp this with hzEq | hz'
      · subst z
        exact Finset.mem_singleton_self y0
      · have hzEq : z = h0 := by simpa using (Finset.mem_singleton.mp hz')
        subst hzEq
        exfalso
        exact hh0 hz
    · intro hz
      have hzEq : z = y0 := by simpa using (Finset.mem_singleton.mp hz)
      subst z
      exact hyMem

theorem X_sdiff_eq_singleton_or_pair_of_Z_eq_empty
    {k : WLcertKey α} {S : Finset α}
    (hSdom : S ∈ o1aWitnessLiftDomWL family h0)
    (hcert : ∃ cert : WLcert family S, WLcert.key cert = k ∧ cert.h ∉ S)
    {y0 : α}
    (hyX : y0 ∈ (ground \ (k.2.2.1 ∪ k.2.2.2.1)))
    (hyNot : y0 ∉ S)
    (hZ : ((((ground \ (k.2.2.1 ∪ k.2.2.2.1)) \ S).erase y0).erase h0) = (∅ : Finset α)) :
    let X : Finset α := ground \ (k.2.2.1 ∪ k.2.2.2.1)
    X \ S = ({y0} : Finset α) ∨ X \ S = ({y0, h0} : Finset α) := by
  classical
  intro X
  have hy : y0 ∈ X \ S := by
    exact Finset.mem_sdiff.mpr ⟨hyX, hyNot⟩
  simpa [X] using
    (mem_pair_of_erase_erase_eq_empty_of_mem (α := α) (X := X) (S := S) (y0 := y0) (h0 := h0) hy hZ)

/-!
Canonical `z` choice for the outMore τ=true bounded-fiber step.

Given a completion `S` and the fixed missing element `y`, define
`Z := ((X \\ S).erase y).erase h0`. If `Z` is nonempty, pick `z ∈ Z`;
otherwise return `none` and treat it as a small-missing case (`X \\ S = {y}` or `{y,h0}`).
-/

noncomputable def zChoice (X S : Finset α) (y0 h0 : α) : Option α := by
  classical
  let Z : Finset α := (((X \ S).erase y0).erase h0)
  by_cases hZ : Z.Nonempty
  · exact some (Classical.choose hZ)
  · exact none

/-!
Second missing element chooser for the outMore `τ=true` bounded-fiber step.

This is lemma-local infrastructure: after `zChoice` picks `z ∈ ((X \\ S) \\ {y0,h0})`,
we optionally pick a second missing `u ∈ ((X \\ S) \\ {y0,h0,z})`.
-/

noncomputable def uChoice (X S : Finset α) (y0 h0 z : α) : Option α := by
  classical
  let Z2 : Finset α := ((((X \ S).erase y0).erase h0).erase z)
  by_cases hZ2 : Z2.Nonempty
  · exact some (Classical.choose hZ2)
  · exact none

/-!
`uGoodChoice` is lemma-local infrastructure for the outMore `τ=true` bounded-fiber seam.

Given `Z2 := ((((X \\ S).erase y0).erase h0).erase z)`, it tries to pick a missing element
`u ∈ Z2` together with a proof that there is **no further missing element** beyond `y0,h0,z,u`,
i.e. `Z2.erase u = ∅`.

Callers must separately show the `none` branch is empty (or already collapses) in their context.
-/
noncomputable def uGoodChoice (X S : Finset α) (y0 h0 z : α) :
    Option {u : α //
      u ∈ ((((X \ S).erase y0).erase h0).erase z) ∧
      (((((X \ S).erase y0).erase h0).erase z).erase u = (∅ : Finset α))} := by
  classical
  let Z2 : Finset α := ((((X \ S).erase y0).erase h0).erase z)
  by_cases hZ2 : Z2.Nonempty
  · let u : α := Classical.choose hZ2
    have hu : u ∈ Z2 := Classical.choose_spec hZ2
    by_cases hE : Z2.erase u = (∅ : Finset α)
    · exact some ⟨u, hu, hE⟩
    · exact none
  · exact none

/-!
`uPairGoodChoice` is lemma-local infrastructure for the outMore `τ=true` bounded-fiber seam.

Given `Z2 := ((((X \\ S).erase y0).erase h0).erase z)`, it tries to pick two **distinct**
missing elements `u v ∈ Z2` together with a proof that there is **no further missing element**
beyond `y0,h0,z,u,v`, i.e. `Z2.erase u.erase v = ∅`.

Callers must separately show the `none` branch is empty (or already collapses) in their context.
-/
noncomputable def uPairGoodChoice (X S : Finset α) (y0 h0 z : α) :
    Option {uv : α × α //
      uv.1 ∈ ((((X \ S).erase y0).erase h0).erase z) ∧
        uv.2 ∈ ((((X \ S).erase y0).erase h0).erase z) ∧
          uv.1 ≠ uv.2 ∧
            (((((X \ S).erase y0).erase h0).erase z).erase uv.1).erase uv.2 = (∅ : Finset α)} :=
  by
    classical
    let Z2 : Finset α := ((((X \ S).erase y0).erase h0).erase z)
    by_cases hZ2 : Z2.Nonempty
    · let u : α := Classical.choose hZ2
      have hu : u ∈ Z2 := Classical.choose_spec hZ2
      let Z2u : Finset α := Z2.erase u
      by_cases hZ2u : Z2u.Nonempty
      · let v : α := Classical.choose hZ2u
        have hvZ2u : v ∈ Z2u := Classical.choose_spec hZ2u
        have hv : v ∈ Z2 := (Finset.mem_erase.mp hvZ2u).2
        have hvne : v ≠ u := (Finset.mem_erase.mp hvZ2u).1
        by_cases hE : Z2u.erase v = (∅ : Finset α)
        · exact some
            ⟨(u, v), by
              refine ⟨?_, ?_, ?_, ?_⟩
              · simpa [Z2] using hu
              · simpa [Z2] using hv
              · exact hvne.symm
              · simpa [Z2, Z2u] using hE⟩
        · exact none
      · exact none
    · exact none

theorem exists_two_mem_Z2_of_uGoodChoice_eq_none_of_Z2_nonempty
    {X S : Finset α} {y0 h0 z : α}
    (hZ2 : ((((X \ S).erase y0).erase h0).erase z).Nonempty)
    (hUG : uGoodChoice (α := α) X S y0 h0 z = none) :
    ∃ u v,
      u ∈ ((((X \ S).erase y0).erase h0).erase z) ∧
        v ∈ ((((X \ S).erase y0).erase h0).erase z) ∧ u ≠ v := by
  classical
  -- Shorthand for the triple-erase set.
  let Z2 : Finset α := ((((X \ S).erase y0).erase h0).erase z)
  have hZ2' : Z2.Nonempty := by simpa [Z2] using hZ2
  -- In the nonempty branch, `uGoodChoice` picks `u := choose Z2` and returns `none`
  -- iff the `erase` test fails, i.e. `Z2.erase u` is nonempty.
  have hEraseNe : (Z2.erase (Classical.choose hZ2')).Nonempty := by
    have hEraseNotEmpty : Z2.erase (Classical.choose hZ2') ≠ (∅ : Finset α) := by
      -- Unfold `uGoodChoice` and simplify the outer `by_cases` using `hZ2'`.
      -- The remaining `if` is on `Z2.erase (choose hZ2') = ∅`.
      have hUG' : uGoodChoice (α := α) X S y0 h0 z = none := hUG
      -- Reduce the definition; in the `erase = ∅` branch the result is `some _`, contradiction.
      unfold uGoodChoice at hUG'
      -- `simp` discharges the outer `by_cases` and exposes the inner `by_cases` as an `if`.
      -- We then read off that the `erase = ∅` condition cannot hold.
      simp [Z2, hZ2'] at hUG'
      -- After `simp`, the goal is exactly the negation of the `erase = ∅` test.
      exact hUG'
    exact Finset.nonempty_iff_ne_empty.2 hEraseNotEmpty
  -- Extract two distinct elements from `Z2`: the chosen element and one from the nonempty erase.
  let u : α := Classical.choose hZ2'
  let v : α := Classical.choose hEraseNe
  have hu : u ∈ Z2 := Classical.choose_spec hZ2'
  have hvErase : v ∈ Z2.erase u := Classical.choose_spec hEraseNe
  have hv : v ∈ Z2 := (Finset.mem_erase.mp hvErase).2
  have hvne : v ≠ u := (Finset.mem_erase.mp hvErase).1
  refine ⟨u, v, ?_, ?_, ?_⟩
  · simpa [Z2] using hu
  · simpa [Z2] using hv
  · exact hvne.symm

theorem uChoice_eq_none_iff
    {X S : Finset α} {y0 h0 z : α} :
    uChoice (α := α) X S y0 h0 z = none ↔
      ((((X \ S).erase y0).erase h0).erase z) = (∅ : Finset α) := by
  classical
  unfold uChoice
  by_cases hZ : (((((X \ S).erase y0).erase h0).erase z) : Finset α).Nonempty
  · have hNe : (((((X \ S).erase y0).erase h0).erase z) : Finset α) ≠ (∅ : Finset α) :=
      hZ.ne_empty
    simp [hZ, hNe]
  · have : (((((X \ S).erase y0).erase h0).erase z) : Finset α) = (∅ : Finset α) := by
      simpa [Finset.not_nonempty_iff_eq_empty] using hZ
    simp [hZ, this]

theorem uChoice_eq_none_imp
    {X S : Finset α} {y0 h0 z : α} :
    uChoice (α := α) X S y0 h0 z = none →
      ((((X \ S).erase y0).erase h0).erase z) = (∅ : Finset α) := by
  intro hu
  exact (uChoice_eq_none_iff (α := α) (X := X) (S := S) (y0 := y0) (h0 := h0) (z := z)).1 hu

theorem uChoice_eq_some_mem
    {X S : Finset α} {y0 h0 z u : α}
    (hu : uChoice (α := α) X S y0 h0 z = some u) :
    u ∈ ((((X \ S).erase y0).erase h0).erase z) := by
  classical
  unfold uChoice at hu
  by_cases hZ : (((((X \ S).erase y0).erase h0).erase z) : Finset α).Nonempty
  · have huEq : Classical.choose hZ = u := by
      simpa [hZ] using hu
    have huMem' :
        Classical.choose hZ ∈ ((((X \ S).erase y0).erase h0).erase z) :=
      Classical.choose_spec hZ
    simpa [huEq] using huMem'
  · simp [hZ] at hu

theorem uChoice_mem_X_sdiff
    {X S : Finset α} {y0 h0 z u : α}
    (hu : uChoice (α := α) X S y0 h0 z = some u) :
    u ∈ X \ S := by
  classical
  have huMem : u ∈ ((((X \ S).erase y0).erase h0).erase z) :=
    uChoice_eq_some_mem (α := α) (X := X) (S := S) (y0 := y0) (h0 := h0) (z := z) (u := u) hu
  -- Membership in the triple-erase implies membership in `X \\ S`.
  have huErase2 : u ∈ ((X \ S).erase y0).erase h0 := (Finset.mem_erase.mp huMem).2
  have huErase1 : u ∈ (X \ S).erase y0 := (Finset.mem_erase.mp huErase2).2
  exact (Finset.mem_erase.mp huErase1).2

theorem zChoice_eq_none_iff
    {X S : Finset α} {y0 h0 : α} :
    zChoice (α := α) X S y0 h0 = none ↔
      (((X \ S).erase y0).erase h0) = (∅ : Finset α) := by
  classical
  unfold zChoice
  by_cases hZ : ((((X \ S).erase y0).erase h0) : Finset α).Nonempty
  · have hNe : ((((X \ S).erase y0).erase h0) : Finset α) ≠ (∅ : Finset α) := hZ.ne_empty
    simp [hZ, hNe]
  · have : ((((X \ S).erase y0).erase h0) : Finset α) = (∅ : Finset α) := by
      simpa [Finset.not_nonempty_iff_eq_empty] using hZ
    simp [hZ, this]

theorem zChoice_eq_none_imp
    {X S : Finset α} {y0 h0 : α} :
    zChoice (α := α) X S y0 h0 = none →
      (((X \ S).erase y0).erase h0) = (∅ : Finset α) := by
  intro hzNone
  exact (zChoice_eq_none_iff (α := α) (X := X) (S := S) (y0 := y0) (h0 := h0)).1 hzNone

theorem zChoice_eq_some_mem
    {X S : Finset α} {y0 h0 z : α}
    (hz : zChoice (α := α) X S y0 h0 = some z) :
    z ∈ ((X \ S).erase y0).erase h0 := by
  classical
  unfold zChoice at hz
  by_cases hZ : ((((X \ S).erase y0).erase h0) : Finset α).Nonempty
  · -- In the `Nonempty` branch, `z` is the chosen element.
    have hzEq : Classical.choose hZ = z := by
      simpa [hZ] using hz
    have hzMem' : Classical.choose hZ ∈ ((X \ S).erase y0).erase h0 := Classical.choose_spec hZ
    simpa [hzEq] using hzMem'
  · -- Impossible: `zChoice = none`.
    simp [hZ] at hz

theorem zChoice_mem_X_sdiff
    {X S : Finset α} {y0 h0 z : α}
    (hz : zChoice (α := α) X S y0 h0 = some z) :
    z ∈ X \ S := by
  classical
  have hzMem : z ∈ ((X \ S).erase y0).erase h0 :=
    zChoice_eq_some_mem (α := α) (X := X) (S := S) (y0 := y0) (h0 := h0) (z := z) hz
  -- Membership in the double-erase implies membership in `X \\ S`.
  have hzErase1 : z ∈ (X \ S).erase y0 := (Finset.mem_erase.mp hzMem).2
  exact (Finset.mem_erase.mp hzErase1).2

theorem X_sdiff_eq_pair_or_triple_of_uChoice_eq_none
    {X S : Finset α} {y0 h0 z : α}
    (hy : y0 ∈ X \ S)
    (hz : zChoice (α := α) X S y0 h0 = some z)
    (hu : uChoice (α := α) X S y0 h0 z = none) :
    X \ S = ({y0, z} : Finset α) ∨ X \ S = ({y0, h0, z} : Finset α) := by
  classical
  have hzXS : z ∈ X \ S := zChoice_mem_X_sdiff (α := α) (X := X) (S := S) hz
  have hZ2 :
      ((((X \ S).erase y0).erase h0).erase z) = (∅ : Finset α) :=
    (uChoice_eq_none_iff (α := α) (X := X) (S := S) (y0 := y0) (h0 := h0) (z := z)).1 hu
  have hSub : X \ S ⊆ ({y0, h0, z} : Finset α) := by
    intro a ha
    by_cases hay : a = y0
    · subst a
      exact Finset.mem_insert_self y0 ({h0, z} : Finset α)
    by_cases hah : a = h0
    · subst a
      exact Finset.mem_insert_of_mem (by simpa using (Finset.mem_insert_self h0 ({z} : Finset α)))
    by_cases haz : a = z
    · subst a
      exact Finset.mem_insert_of_mem (by simpa using (Finset.mem_insert_of_mem (Finset.mem_singleton_self z)))
    -- Otherwise `a ∈ ((((X\\S).erase y0).erase h0).erase z)`, contradicting emptiness.
    have haZ1 : a ∈ (X \ S).erase y0 := Finset.mem_erase.mpr ⟨hay, ha⟩
    have haZ2 : a ∈ ((X \ S).erase y0).erase h0 := Finset.mem_erase.mpr ⟨hah, haZ1⟩
    have haZ3 : a ∈ (((X \ S).erase y0).erase h0).erase z := Finset.mem_erase.mpr ⟨haz, haZ2⟩
    have : a ∈ (∅ : Finset α) := by simpa [hZ2] using haZ3
    exact False.elim (Finset.notMem_empty a this)
  by_cases hh : h0 ∈ X \ S
  · right
    -- In this branch, all three of `y0,h0,z` lie in `X\\S`.
    refine Finset.Subset.antisymm ?_ ?_
    · exact hSub
    · intro a ha
      -- Membership in `{y0,h0,z}` gives `a=y0 ∨ a=h0 ∨ a=z`.
      have : a = y0 ∨ a = h0 ∨ a = z := by
        simpa using (Finset.mem_insert.mp ha)
      rcases this with rfl | rfl | rfl
      · exact hy
      · exact hh
      · exact hzXS
  · left
    -- If `h0 ∉ X\\S`, then `X\\S ⊆ {y0,z}` and both `y0,z` lie in it.
    have hSub' : X \ S ⊆ ({y0, z} : Finset α) := by
      intro a ha
      have ha' : a ∈ ({y0, h0, z} : Finset α) := hSub ha
      rcases Finset.mem_insert.mp ha' with haEq | ha'
      · subst a
        exact Finset.mem_insert_self y0 ({z} : Finset α)
      have : a = h0 ∨ a = z := by
        simpa using (Finset.mem_insert.mp ha')
      rcases this with rfl | rfl
      · exfalso
        exact hh ha
      · exact Finset.mem_insert_of_mem (by simpa using (Finset.mem_singleton_self z))
    refine Finset.Subset.antisymm ?_ ?_
    · exact hSub'
    · intro a ha
      rcases Finset.mem_insert.mp ha with haEq | ha'
      · subst a
        exact hy
      have haEq : a = z := by simpa using (Finset.mem_singleton.mp ha')
      subst a
      exact hzXS

theorem X_sdiff_eq_triple_or_quad_of_uChoice_eq_some_of_erase_u_eq_empty
    {X S : Finset α} {y0 h0 z u : α}
    (hy : y0 ∈ X \ S)
    (hz : zChoice (α := α) X S y0 h0 = some z)
    (hu : uChoice (α := α) X S y0 h0 z = some u)
    (hZ3 :
      ((((((X \ S).erase y0).erase h0).erase z).erase u) = (∅ : Finset α))) :
    X \ S = ({y0, z, u} : Finset α) ∨ X \ S = ({y0, h0, z, u} : Finset α) := by
  classical
  have hzXS : z ∈ X \ S := zChoice_mem_X_sdiff (α := α) (X := X) (S := S) hz
  have huXS : u ∈ X \ S := uChoice_mem_X_sdiff (α := α) (X := X) (S := S) hu
  have hSub : X \ S ⊆ ({y0, h0, z, u} : Finset α) := by
    intro a ha
    by_cases hay : a = y0
    · subst a
      exact Finset.mem_insert_self y0 ({h0, z, u} : Finset α)
    by_cases hah : a = h0
    · subst a
      exact Finset.mem_insert_of_mem (by
        simpa using (Finset.mem_insert_self h0 ({z, u} : Finset α)))
    by_cases haz : a = z
    · subst a
      exact Finset.mem_insert_of_mem (by
        simpa using (Finset.mem_insert_of_mem (Finset.mem_insert_self z ({u} : Finset α))))
    by_cases hau : a = u
    · subst a
      exact Finset.mem_insert_of_mem (by
        simpa using
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self u))))
    -- Otherwise `a ∈ ((((((X\\S).erase y0).erase h0).erase z).erase u)`, contradicting emptiness.
    have haZ1 : a ∈ (X \ S).erase y0 := Finset.mem_erase.mpr ⟨hay, ha⟩
    have haZ2 : a ∈ ((X \ S).erase y0).erase h0 := Finset.mem_erase.mpr ⟨hah, haZ1⟩
    have haZ3 : a ∈ (((X \ S).erase y0).erase h0).erase z := Finset.mem_erase.mpr ⟨haz, haZ2⟩
    have haZ4 :
        a ∈ (((((X \ S).erase y0).erase h0).erase z).erase u) := Finset.mem_erase.mpr ⟨hau, haZ3⟩
    have : a ∈ (∅ : Finset α) := by simpa [hZ3] using haZ4
    exact False.elim (Finset.notMem_empty a this)
  by_cases hh : h0 ∈ X \ S
  · right
    refine Finset.Subset.antisymm ?_ ?_
    · exact hSub
    · intro a ha
      have : a = y0 ∨ a = h0 ∨ a = z ∨ a = u := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using ha
      rcases this with rfl | rfl | rfl | rfl
      · exact hy
      · exact hh
      · exact hzXS
      · exact huXS
  · left
    have hSub' : X \ S ⊆ ({y0, z, u} : Finset α) := by
      intro a ha
      have ha' : a ∈ ({y0, h0, z, u} : Finset α) := hSub ha
      rcases Finset.mem_insert.mp ha' with haEq | ha'
      · subst a
        exact Finset.mem_insert_self y0 ({z, u} : Finset α)
      have : a = h0 ∨ a = z ∨ a = u := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using ha'
      rcases this with rfl | rfl | rfl
      · exfalso
        exact hh ha
      · exact Finset.mem_insert_of_mem (by simpa using (Finset.mem_insert_self z ({u} : Finset α)))
      · exact Finset.mem_insert_of_mem (by
        simpa using (Finset.mem_insert_of_mem (Finset.mem_singleton_self u)))
    refine Finset.Subset.antisymm ?_ ?_
    · exact hSub'
    · intro a ha
      rcases Finset.mem_insert.mp ha with haEq | ha'
      · subst a
        exact hy
      rcases Finset.mem_insert.mp ha' with haEq | ha'
      · subst a
        exact hzXS
      have haEq : a = u := by simpa using (Finset.mem_singleton.mp ha')
      subst a
      exact huXS

theorem X_sdiff_eq_triple_or_quad_of_mem_of_erase_u_eq_empty
    {X S : Finset α} {y0 h0 z u : α}
    (hy : y0 ∈ X \ S)
    (hz : zChoice (α := α) X S y0 h0 = some z)
    (huMem : u ∈ ((((X \ S).erase y0).erase h0).erase z))
    (hZ3 :
      ((((((X \ S).erase y0).erase h0).erase z).erase u) = (∅ : Finset α))) :
    X \ S = ({y0, z, u} : Finset α) ∨ X \ S = ({y0, h0, z, u} : Finset α) := by
  classical
  have hzXS : z ∈ X \ S := zChoice_mem_X_sdiff (α := α) (X := X) (S := S) hz
  -- Membership in the triple-erase implies membership in `X \\ S`.
  have huErase2 : u ∈ ((X \ S).erase y0).erase h0 := (Finset.mem_erase.mp huMem).2
  have huErase1 : u ∈ (X \ S).erase y0 := (Finset.mem_erase.mp huErase2).2
  have huXS : u ∈ X \ S := (Finset.mem_erase.mp huErase1).2
  have hSub : X \ S ⊆ ({y0, h0, z, u} : Finset α) := by
    intro a ha
    by_cases hay : a = y0
    · subst a
      exact Finset.mem_insert_self y0 ({h0, z, u} : Finset α)
    by_cases hah : a = h0
    · subst a
      exact Finset.mem_insert_of_mem (by
        simpa using (Finset.mem_insert_self h0 ({z, u} : Finset α)))
    by_cases haz : a = z
    · subst a
      exact Finset.mem_insert_of_mem (by
        simpa using (Finset.mem_insert_of_mem (Finset.mem_insert_self z ({u} : Finset α))))
    by_cases hau : a = u
    · subst a
      exact Finset.mem_insert_of_mem (by
        simpa using
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self u))))
    -- Otherwise `a ∈ ((((((X\\S).erase y0).erase h0).erase z).erase u)`, contradicting emptiness.
    have haZ1 : a ∈ (X \ S).erase y0 := Finset.mem_erase.mpr ⟨hay, ha⟩
    have haZ2 : a ∈ ((X \ S).erase y0).erase h0 := Finset.mem_erase.mpr ⟨hah, haZ1⟩
    have haZ3 : a ∈ (((X \ S).erase y0).erase h0).erase z := Finset.mem_erase.mpr ⟨haz, haZ2⟩
    have haZ4 :
        a ∈ (((((X \ S).erase y0).erase h0).erase z).erase u) := Finset.mem_erase.mpr ⟨hau, haZ3⟩
    have : a ∈ (∅ : Finset α) := by simpa [hZ3] using haZ4
    exact False.elim (Finset.notMem_empty a this)
  by_cases hh : h0 ∈ X \ S
  · right
    refine Finset.Subset.antisymm ?_ ?_
    · exact hSub
    · intro a ha
      have : a = y0 ∨ a = h0 ∨ a = z ∨ a = u := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using ha
      rcases this with rfl | rfl | rfl | rfl
      · exact hy
      · exact hh
      · exact hzXS
      · exact huXS
  · left
    have hSub' : X \ S ⊆ ({y0, z, u} : Finset α) := by
      intro a ha
      have ha' : a ∈ ({y0, h0, z, u} : Finset α) := hSub ha
      rcases Finset.mem_insert.mp ha' with haEq | ha'
      · subst a
        exact Finset.mem_insert_self y0 ({z, u} : Finset α)
      have : a = h0 ∨ a = z ∨ a = u := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using ha'
      rcases this with rfl | rfl | rfl
      · exfalso
        exact hh ha
      · exact Finset.mem_insert_of_mem (by simpa using (Finset.mem_insert_self z ({u} : Finset α)))
      · exact Finset.mem_insert_of_mem (by
        simpa using (Finset.mem_insert_of_mem (Finset.mem_singleton_self u)))
    refine Finset.Subset.antisymm ?_ ?_
    · exact hSub'
    · intro a ha
      rcases Finset.mem_insert.mp ha with haEq | ha'
      · subst a
        exact hy
      rcases Finset.mem_insert.mp ha' with haEq | ha'
      · subst a
        exact hzXS
      have haEq : a = u := by simpa using (Finset.mem_singleton.mp ha')
      subst a
      exact huXS

theorem Xerase_h0_sdiff_eq_quad_of_mem_of_erase_u_erase_v_eq_empty
    {X S : Finset α} {y0 h0 z u v : α}
    (hy : y0 ∈ X \ S)
    (hyNe : y0 ≠ h0)
    (hz : zChoice (α := α) X S y0 h0 = some z)
    (huMem : u ∈ ((((X \ S).erase y0).erase h0).erase z))
    (hvMem : v ∈ (((((X \ S).erase y0).erase h0).erase z).erase u))
    (hZ4 :
      (((((((X \ S).erase y0).erase h0).erase z).erase u).erase v) = (∅ : Finset α))) :
    (X.erase h0) \ S = ({y0, z, u, v} : Finset α) := by
  classical
  have hzMem : z ∈ ((X \ S).erase y0).erase h0 :=
    zChoice_eq_some_mem (α := α) (X := X) (S := S) (y0 := y0) (h0 := h0) (z := z) hz
  have hzXS : z ∈ X \ S :=
    zChoice_mem_X_sdiff (α := α) (X := X) (S := S) (y0 := y0) (h0 := h0) (z := z) hz
  -- Membership in the triple-erase implies membership in `X \\ S`.
  have huErase2 : u ∈ ((X \ S).erase y0).erase h0 := (Finset.mem_erase.mp huMem).2
  have huErase1 : u ∈ (X \ S).erase y0 := (Finset.mem_erase.mp huErase2).2
  have huXS : u ∈ X \ S := (Finset.mem_erase.mp huErase1).2
  have hvErase3 : v ∈ ((((X \ S).erase y0).erase h0).erase z) := (Finset.mem_erase.mp hvMem).2
  have hvErase2 : v ∈ ((X \ S).erase y0).erase h0 := (Finset.mem_erase.mp hvErase3).2
  have hvErase1 : v ∈ (X \ S).erase y0 := (Finset.mem_erase.mp hvErase2).2
  have hvXS : v ∈ X \ S := (Finset.mem_erase.mp hvErase1).2
  have hzNe : z ≠ h0 := (Finset.mem_erase.mp hzMem).1
  have huNe : u ≠ h0 := (Finset.mem_erase.mp huErase2).1
  have hvNe : v ≠ h0 := (Finset.mem_erase.mp hvErase2).1
  have hSub : (X.erase h0) \ S ⊆ ({y0, z, u, v} : Finset α) := by
    intro a ha
    have haXh : a ∈ X.erase h0 := (Finset.mem_sdiff.mp ha).1
    have haNotS : a ∉ S := (Finset.mem_sdiff.mp ha).2
    have haX : a ∈ X := (Finset.mem_erase.mp haXh).2
    have haNeH0 : a ≠ h0 := (Finset.mem_erase.mp haXh).1
    have haXS : a ∈ X \ S := Finset.mem_sdiff.mpr ⟨haX, haNotS⟩
    by_cases hay : a = y0
    · subst a
      exact Finset.mem_insert_self y0 ({z, u, v} : Finset α)
    by_cases haz : a = z
    · subst a
      exact Finset.mem_insert_of_mem (by
        simpa using (Finset.mem_insert_self z ({u, v} : Finset α)))
    by_cases hau : a = u
    · subst a
      exact Finset.mem_insert_of_mem (by
        simpa using (Finset.mem_insert_of_mem (Finset.mem_insert_self u ({v} : Finset α))))
    by_cases hav : a = v
    · subst a
      exact Finset.mem_insert_of_mem (by
        simpa using
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self v))))
    -- Otherwise `a` lies in the erased set, contradicting emptiness.
    have haZ1 : a ∈ (X \ S).erase y0 := Finset.mem_erase.mpr ⟨hay, haXS⟩
    have haZ2 : a ∈ ((X \ S).erase y0).erase h0 := Finset.mem_erase.mpr ⟨haNeH0, haZ1⟩
    have haZ3 : a ∈ (((X \ S).erase y0).erase h0).erase z := Finset.mem_erase.mpr ⟨haz, haZ2⟩
    have haZ4 : a ∈ ((((X \ S).erase y0).erase h0).erase z).erase u :=
      Finset.mem_erase.mpr ⟨hau, haZ3⟩
    have haZ5 :
        a ∈ ((((((X \ S).erase y0).erase h0).erase z).erase u).erase v) :=
      Finset.mem_erase.mpr ⟨hav, haZ4⟩
    have : a ∈ (∅ : Finset α) := by simpa [hZ4] using haZ5
    exact False.elim (Finset.notMem_empty a this)
  have hSub' : ({y0, z, u, v} : Finset α) ⊆ (X.erase h0) \ S := by
    intro a ha
    have : a = y0 ∨ a = z ∨ a = u ∨ a = v := by
      simpa [Finset.mem_insert, Finset.mem_singleton] using ha
    rcases this with haY | h'
    · subst a
      have hyX : y0 ∈ X := (Finset.mem_sdiff.mp hy).1
      have hyNot : y0 ∉ S := (Finset.mem_sdiff.mp hy).2
      have hyXh : y0 ∈ X.erase h0 := Finset.mem_erase.mpr ⟨hyNe, hyX⟩
      exact Finset.mem_sdiff.mpr ⟨hyXh, hyNot⟩
    rcases h' with haZ | h'
    · subst a
      have hzX : z ∈ X := (Finset.mem_sdiff.mp hzXS).1
      have hzNot : z ∉ S := (Finset.mem_sdiff.mp hzXS).2
      have hzXh : z ∈ X.erase h0 := Finset.mem_erase.mpr ⟨hzNe, hzX⟩
      exact Finset.mem_sdiff.mpr ⟨hzXh, hzNot⟩
    rcases h' with haU | haV
    · subst a
      have huX : u ∈ X := (Finset.mem_sdiff.mp huXS).1
      have huNot : u ∉ S := (Finset.mem_sdiff.mp huXS).2
      have huXh : u ∈ X.erase h0 := Finset.mem_erase.mpr ⟨huNe, huX⟩
      exact Finset.mem_sdiff.mpr ⟨huXh, huNot⟩
    · subst a
      have hvX : v ∈ X := (Finset.mem_sdiff.mp hvXS).1
      have hvNot : v ∉ S := (Finset.mem_sdiff.mp hvXS).2
      have hvXh : v ∈ X.erase h0 := Finset.mem_erase.mpr ⟨hvNe, hvX⟩
      exact Finset.mem_sdiff.mpr ⟨hvXh, hvNot⟩
  exact Finset.Subset.antisymm hSub hSub'

theorem zChoice_ne_y0
    {X S : Finset α} {y0 h0 z : α}
    (hz : zChoice (α := α) X S y0 h0 = some z) :
    z ≠ y0 := by
  classical
  have hzMem : z ∈ ((X \ S).erase y0).erase h0 :=
    zChoice_eq_some_mem (α := α) (X := X) (S := S) (y0 := y0) (h0 := h0) (z := z) hz
  have hzErase1 : z ∈ (X \ S).erase y0 := (Finset.mem_erase.mp hzMem).2
  exact (Finset.mem_erase.mp hzErase1).1

theorem zChoice_ne_h0
    {X S : Finset α} {y0 h0 z : α}
    (hz : zChoice (α := α) X S y0 h0 = some z) :
    z ≠ h0 := by
  classical
  have hzMem : z ∈ ((X \ S).erase y0).erase h0 :=
    zChoice_eq_some_mem (α := α) (X := X) (S := S) (y0 := y0) (h0 := h0) (z := z) hz
  exact (Finset.mem_erase.mp hzMem).1

theorem exists_z_of_zChoice_ne_none
    {X S : Finset α} {y0 h0 : α}
    (hz : zChoice (α := α) X S y0 h0 ≠ none) :
    ∃ z, zChoice (α := α) X S y0 h0 = some z := by
  classical
  cases hzChoice : zChoice (α := α) X S y0 h0 with
  | none =>
      exact False.elim (hz hzChoice)
  | some z =>
      exact ⟨z, by simpa [hzChoice]⟩

/-!
OutMore `τ=true` bucket cap (work in progress).

In a fixed outMore bucket `Bucket(σOut)` for the extended signature
`PerXSignatureOutMore := (perXSignature_of_hardFiber, trace5Plus(Uout), t6Option)`,
we split on the canonical `zChoice`:

* `zChoice = none`: this forces `X \\ S = {y}` or `{y,h0}` and collapses by the sharp
  singleton/pair missing-set lemmas (`card ≤ 1`).
* `zChoice = some z`: we build the normalized one-step blocking witness for `S ∪ {z}`
  (via `wlcert_hNotMem_reduction_o1aDomWL`) and map completions to `(z, uFromZWitness)`.

The bounded-fiber proof for the `(z,u)` map is the remaining main lemma.
-/

theorem card_Bucket_perXSignatureOutMore_le_of_trace5Plus_true
    (hreg : O1aUpgradeRegime family ground A0 h0)
    {k : WLcertKey α}
    {Sstar : {S // S ∈ o1aWitnessLiftDomWL family h0}}
    {x : α}
    (hSstar :
      Sstar ∈ wlcertAdmissibleFiber_hNotMem (family := family) (o1aWitnessLiftDomWL family h0) k)
    (σOut : PerXSignatureOutMore α)
    {t1 t2 t3 t4 t5 : α}
    (hτ : σOut.2.1 = some (t1, t2, t3, t4, t5, true)) :
    let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h0
    let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
    let Fx0 :
        Finset {S // S ∈ dom} :=
      wlcertAdmissibleFiber_hNotMem_fiberForX (dom := dom) fiber Sstar.1 x
    let sig0 : {Ssub // Ssub ∈ Fx0} → PerXSignature α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      perXSignature_of_hardFiber (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1) Sstar.2 b.1.2 hcert_star hcert_sub hne
    let Uout : {Ssub // Ssub ∈ Fx0} → Finset α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      let yw :
          Σ y : α, BlockedUnionWitness family b.1.1 y :=
        chooseYAndWitness_of_hardFiber
          (family := family) (ground := ground) (A0 := A0) (h0 := h0)
          hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
          Sstar.2 b.1.2 hcert_star hcert_sub hne
      b.1.1 \ (yw.2.A ∪ yw.2.B)
    let sigOut : {Ssub // Ssub ∈ Fx0} → PerXSignatureOutMore α := fun b =>
      (sig0 b,
        trace5PlusOfFinset (α := α) (Uout b),
        t6OptionOfTrace5Plus (α := α) (Uout b))
    let X : Finset α := ground \ (k.2.2.1 ∪ k.2.2.2.1)
    let y : α := σOut.1.1
    let B : Finset {Ssub // Ssub ∈ Fx0} := Bucket (Fx := Fx0.attach) sigOut σOut
    (B.filter (fun b => zChoice (α := α) X b.1.1 y h0 = none)).card ≤ 2 := by
  classical
  intro dom fiber Fx0 sig0 Uout sigOut X y B
  -- Split the `zChoice = none` branch into the sharp singleton/pair missing-set cases.
  -- This is a loose cap (≤2) that will be refined later if needed.
  have hsub :
      B.filter (fun b => zChoice (α := α) X b.1.1 y h0 = none) ⊆
        (B.filter (fun b => X \ b.1.1 = ({y} : Finset α))) ∪
          (B.filter (fun b => X \ b.1.1 = ({y, h0} : Finset α))) := by
    intro b hb
    have hbB : b ∈ B := (Finset.mem_filter.mp hb).1
    have hzNone : zChoice (α := α) X b.1.1 y h0 = none := (Finset.mem_filter.mp hb).2
    have hZ :
        (((X \ b.1.1).erase y).erase h0) = (∅ : Finset α) :=
      (zChoice_eq_none_iff (α := α) (X := X) (S := b.1.1) (y0 := y) (h0 := h0)).1 hzNone
    -- Show `y ∈ X \\ b` and `y ∉ b` from the bucket's fixed `PerXSignature`.
    have hbFiber : b.1 ∈ fiber := (Finset.mem_filter.mp b.2).1
    have hcert_sub :
        ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
      (Finset.mem_filter.mp hbFiber).2
    -- First, relate the bucket-fixed `y = σOut.1.1` to the hard-fiber chosen missing element.
    have hbSig : sigOut b = σOut := (Finset.mem_filter.mp hbB).2
    have hySig : (sig0 b).1 = y := by
      -- Compare the `y` component of `sig0` via `sigOut b = σOut`.
      have : (sigOut b).1.1 = σOut.1.1 := by simpa [hbSig]
      simpa [sigOut] using this
    have hcert_star :
        ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
      (Finset.mem_filter.mp hSstar).2
    have hne : b.1.1 ≠ Sstar.1 :=
      PerXSubfiber.ne_Sstar_val_of_mem_fiberForX
        (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
        (Ssub := b.1) b.2
    let yCh : α :=
      chooseMissingFromRef (family := family) (h0 := h0) Sstar.1 b.1.1 Sstar.2 b.1.2 hne
    have hyChSig0 : (sig0 b).1 = yCh := by
      -- Unfold the signature definition to expose the chosen missing element.
      simp [sig0, perXSignature_of_hardFiber, perXSignature, chooseYAndWitness_of_hardFiber, yCh]
    have hyEq : yCh = y := by simpa [hyChSig0] using hySig
    have hyXCh : yCh ∈ X := by
      have hyX' :
          yCh ∈ (ground \ (k.2.2.1 ∪ k.2.2.2.1)) := by
        simpa [yCh] using
          (chooseMissingFromRef_mem_X_of_hardFiber (family := family) (ground := ground) (A0 := A0)
            (h0 := h0) hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
            Sstar.2 b.1.2 hcert_star hcert_sub hne)
      simpa [X] using hyX'
    have hyNotCh : yCh ∉ b.1.1 := by
      have hyDiff :
          yCh ∈ Sstar.1 \ b.1.1 := by
        simpa [yCh] using
          (chooseMissingFromRef_spec (family := family) (h0 := h0) Sstar.1 b.1.1
            Sstar.2 b.1.2 hne)
      exact (Finset.mem_sdiff.mp hyDiff).2
    have hyX : y ∈ X := by simpa [hyEq] using hyXCh
    have hyNot : y ∉ b.1.1 := by simpa [hyEq] using hyNotCh
    have hXs :
        X \ b.1.1 = ({y} : Finset α) ∨ X \ b.1.1 = ({y, h0} : Finset α) := by
      -- Use the helper lemma for the empty double-erase.
      have hbDom : b.1.1 ∈ o1aWitnessLiftDomWL family h0 := b.1.2
      exact
        X_sdiff_eq_singleton_or_pair_of_Z_eq_empty (family := family) (ground := ground) (h0 := h0)
          (k := k) (S := b.1.1) hbDom hcert_sub (y0 := y) (by simpa [X] using hyX)
          hyNot (by simpa [X] using hZ)
    rcases hXs with hXs | hXs
    · have : b ∈ B.filter (fun b => X \ b.1.1 = ({y} : Finset α)) :=
        Finset.mem_filter.mpr ⟨hbB, hXs⟩
      exact Finset.mem_union.mpr (Or.inl this)
    · have : b ∈ B.filter (fun b => X \ b.1.1 = ({y, h0} : Finset α)) :=
        Finset.mem_filter.mpr ⟨hbB, hXs⟩
      exact Finset.mem_union.mpr (Or.inr this)
  -- Now bound by the sum of the singleton/pair caps.
  have hcard1 :
      (B.filter (fun b => X \ b.1.1 = ({y} : Finset α))).card ≤ 1 :=
    card_Bucket_perXSignatureOutMore_filter_X_sdiff_eq_singleton_le_one
      (family := family) (ground := ground) (A0 := A0) (h0 := h0) hreg (k := k) (Sstar := Sstar)
      (x := x) hSstar σOut
  have hcard2 :
      (B.filter (fun b => X \ b.1.1 = ({y, h0} : Finset α))).card ≤ 1 :=
    card_Bucket_perXSignatureOutMore_filter_X_sdiff_eq_pair_le_one
      (family := family) (ground := ground) (A0 := A0) (h0 := h0) hreg (k := k) (Sstar := Sstar)
      (x := x) hSstar σOut (y1 := y) (y2 := h0)
  -- Use `card_le_of_subset` and `card_union_le` to get the final `≤ 2`.
  have hcard_sub :
      (B.filter (fun b => zChoice (α := α) X b.1.1 y h0 = none)).card ≤
        ((B.filter (fun b => X \ b.1.1 = ({y} : Finset α))) ∪
            (B.filter (fun b => X \ b.1.1 = ({y, h0} : Finset α)))).card := by
    exact Finset.card_le_card hsub
  have hcard_union :
      (((B.filter (fun b => X \ b.1.1 = ({y} : Finset α))) ∪
            (B.filter (fun b => X \ b.1.1 = ({y, h0} : Finset α)))).card) ≤ 2 := by
    -- crude: `card(union) ≤ card + card ≤ 1+1`.
    have := Finset.card_union_le (B.filter (fun b => X \ b.1.1 = ({y} : Finset α)))
        (B.filter (fun b => X \ b.1.1 = ({y, h0} : Finset α)))
    -- `card_union_le` gives `≤ card + card`.
    have hsum :
        ((B.filter (fun b => X \ b.1.1 = ({y} : Finset α))) ∪
              (B.filter (fun b => X \ b.1.1 = ({y, h0} : Finset α)))).card ≤
          (B.filter (fun b => X \ b.1.1 = ({y} : Finset α))).card +
            (B.filter (fun b => X \ b.1.1 = ({y, h0} : Finset α))).card := by
      simpa using this
    calc
      (((B.filter (fun b => X \ b.1.1 = ({y} : Finset α))) ∪
              (B.filter (fun b => X \ b.1.1 = ({y, h0} : Finset α)))).card)
          ≤ (B.filter (fun b => X \ b.1.1 = ({y} : Finset α))).card +
              (B.filter (fun b => X \ b.1.1 = ({y, h0} : Finset α))).card := hsum
      _ ≤ 1 + 1 := by exact Nat.add_le_add hcard1 hcard2
      _ = 2 := by simp
  exact le_trans hcard_sub hcard_union

/-!
OutMore τ=true bucket cap (zChoice ≠ none branch): wiring + ledger.

This lemma packages the *counting* part of the bounded-fiber strategy:
map completions in a fixed `Bucket(σOut)` to `(z, uFromZWitness)` and count via
`card_eq_sum_card_image`.

It intentionally leaves the fiber cap (`≤ 2`) as an assumption; the next lemma
will discharge it using residue-local blocked-extension constraints.
-/

private noncomputable def bucketPairOfZChoice
    {dom : Finset (Finset α)}
    {Fx0 : Finset {S // S ∈ dom}}
    (X : Finset α) (y h0 : α) (b : {Ssub // Ssub ∈ Fx0}) : α × Option α :=
  if hz : zChoice (α := α) X b.1.1 y h0 ≠ none then
    let ex : ∃ z, zChoice (α := α) X b.1.1 y h0 = some z :=
      exists_z_of_zChoice_ne_none (α := α) (X := X) (S := b.1.1) (y0 := y) (h0 := h0) hz
    let z : α := Classical.choose ex
    (z, (uGoodChoice (α := α) X b.1.1 y h0 z).map (fun hu => hu.1))
  else
    (h0, none)

private theorem bucketPairOfZChoice_eq_dif
    {dom : Finset (Finset α)}
    {Fx0 : Finset {S // S ∈ dom}}
    (X : Finset α) (y h0 : α) (b : {Ssub // Ssub ∈ Fx0}) :
    bucketPairOfZChoice (X := X) (y := y) (h0 := h0) b =
      if hz : zChoice (α := α) X b.1.1 y h0 ≠ none then
        let ex : ∃ z, zChoice (α := α) X b.1.1 y h0 = some z :=
          exists_z_of_zChoice_ne_none (α := α) (X := X) (S := b.1.1) (y0 := y) (h0 := h0) hz
        let z : α := Classical.choose ex
        (z, (uGoodChoice (α := α) X b.1.1 y h0 z).map (fun hu => hu.1))
      else
        (h0, none) := by
  rfl

set_option maxHeartbeats 5000000 in
-- Needed for this lemma because the `g` / `himg_sub` proof unfolds a large witness-selection term
-- (the `...GoodU...` chooser), which can exceed the default heartbeat budget during `whnf`.
theorem card_Bucket_perXSignatureOutMore_filter_zChoice_ne_none_le_two_mul_n_mul_succ_of_fiber_le_two
    (hreg : O1aUpgradeRegime family ground A0 h0)
    {k : WLcertKey α}
    {Sstar : {S // S ∈ o1aWitnessLiftDomWL family h0}}
    {x : α}
    (hSstar :
      Sstar ∈ wlcertAdmissibleFiber_hNotMem (family := family) (o1aWitnessLiftDomWL family h0) k)
    (σOut : PerXSignatureOutMore α) :
    let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h0
    let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
    let Fx0 :
        Finset {S // S ∈ dom} :=
      wlcertAdmissibleFiber_hNotMem_fiberForX (dom := dom) fiber Sstar.1 x
    let Uout : {Ssub // Ssub ∈ Fx0} → Finset α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      let yw :
          Σ y : α, BlockedUnionWitness family b.1.1 y :=
        chooseYAndWitness_of_hardFiber
          (family := family) (ground := ground) (A0 := A0) (h0 := h0)
          hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
          Sstar.2 b.1.2 hcert_star hcert_sub hne
      b.1.1 \ (yw.2.A ∪ yw.2.B)
    let sig0 : {Ssub // Ssub ∈ Fx0} → PerXSignature α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      perXSignature_of_hardFiber (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1) Sstar.2 b.1.2 hcert_star hcert_sub hne
    let sigOut : {Ssub // Ssub ∈ Fx0} → PerXSignatureOutMore α := fun b =>
      (sig0 b,
        trace5PlusOfFinset (α := α) (Uout b),
        t6OptionOfTrace5Plus (α := α) (Uout b))
    let X : Finset α := ground \ (k.2.2.1 ∪ k.2.2.2.1)
    let y : α := σOut.1.1
    let B : Finset {Ssub // Ssub ∈ Fx0} := Bucket (Fx := Fx0.attach) sigOut σOut
    let Bsome : Finset {Ssub // Ssub ∈ Fx0} :=
      B.filter (fun b => zChoice (α := α) X b.1.1 y h0 ≠ none)
    let g : {Ssub // Ssub ∈ Fx0} → α × Option α := by
      classical
      exact fun b => bucketPairOfZChoice (X := X) (y := y) (h0 := h0) b
    (∀ p ∈ Bsome.image g, (Bsome.filter (fun b => g b = p)).card ≤ 2) →
      Bsome.card ≤ 2 * ground.card * (ground.card + 1) := by
  classical
  intro dom fiber Fx0 Uout sig0 sigOut X y B Bsome g hFib
  have hXsub : X ⊆ ground := by
    intro a ha
    exact (Finset.mem_sdiff.mp ha).1
  have hgdef :
      ∀ b,
        g b =
          bucketPairOfZChoice (X := X) (y := y) (h0 := h0) b := by
    intro b
    rfl
  -- Expand `Bsome.card` as a sum of fibers over the image of `g`.
  have hsum :
      Bsome.card =
        ∑ p ∈ Bsome.image g, (Bsome.filter (fun b => g b = p)).card := by
    exact Finset.card_eq_sum_card_image (f := g) (s := Bsome)
  -- Bound each fiber by `2`.
  have hsum_le :
      (∑ p ∈ Bsome.image g, (Bsome.filter (fun b => g b = p)).card) ≤
        ∑ _p ∈ Bsome.image g, 2 := by
    refine Finset.sum_le_sum ?_
    intro p hp
    exact hFib p hp
  -- Collapse the constant sum.
  have hconst :
      (∑ _p ∈ Bsome.image g, 2) = 2 * (Bsome.image g).card := by
    calc
      (∑ _p ∈ Bsome.image g, 2) = (Bsome.image g).card * 2 := by
        simpa using Finset.sum_const_nat (s := Bsome.image g) 2
      _ = 2 * (Bsome.image g).card := by
        exact Nat.mul_comm _ _
  -- Bound the image size by `|ground| * (|ground|+1)` using `optionOfFinset`.
  have himg_sub :
      Bsome.image g ⊆ (ground.product (optionOfFinset (α := α) ground)) := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨b, hbBsome, rfl⟩
    have hbz : zChoice (α := α) X b.1.1 y h0 ≠ none := (Finset.mem_filter.mp hbBsome).2
    -- Use the same `Classical.choose` witness as in the definition of `g`.
    let ex : ∃ z, zChoice (α := α) X b.1.1 y h0 = some z :=
      exists_z_of_zChoice_ne_none (α := α) (X := X) (S := b.1.1) (y0 := y) (h0 := h0) hbz
    let z : α := Classical.choose ex
    have hzEq : zChoice (α := α) X b.1.1 y h0 = some z := Classical.choose_spec ex
    have hzXS : z ∈ X \ b.1.1 := zChoice_mem_X_sdiff (α := α) (X := X) (S := b.1.1) hzEq
    have hzX : z ∈ X := (Finset.mem_sdiff.mp hzXS).1
    have hzG : z ∈ ground := by
      exact hXsub hzX
    have huG :
        ((uGoodChoice (α := α) X b.1.1 y h0 z).map (fun hu => hu.1)) ∈
          optionOfFinset (α := α) ground := by
      have hnoneOpt :
          (none : Option α) ∈ optionOfFinset (α := α) ground :=
        (mem_optionOfFinset_iff (α := α) (T := ground) (o := (none : Option α))).2
          (Or.inl rfl)
      -- Either `none`, or `some u` with `u ∈ X ⊆ ground`.
      cases huEq : uGoodChoice (α := α) X b.1.1 y h0 z with
      | none =>
          simpa [huEq] using hnoneOpt
      | some hu =>
          -- Extract `u ∈ X \\ b` from membership in the triple-erase.
          have huMem : hu.1 ∈ ((((X \ b.1.1).erase y).erase h0).erase z) := hu.2.1
          have huErase2 : hu.1 ∈ ((X \ b.1.1).erase y).erase h0 := (Finset.mem_erase.mp huMem).2
          have huErase1 : hu.1 ∈ (X \ b.1.1).erase y := (Finset.mem_erase.mp huErase2).2
          have huXS : hu.1 ∈ X \ b.1.1 := (Finset.mem_erase.mp huErase1).2
          have huX : hu.1 ∈ X := (Finset.mem_sdiff.mp huXS).1
          have huGnd : hu.1 ∈ ground := hXsub huX
          have hmem :
              (some hu.1 : Option α) ∈ optionOfFinset (α := α) ground :=
            (mem_optionOfFinset_iff (α := α) (T := ground) (o := (some hu.1 : Option α))).2
              (Or.inr ⟨hu.1, huGnd, rfl⟩)
          simpa [huEq] using hmem
    -- Assemble membership in the product finset.
    have hPair : (z, (uGoodChoice (α := α) X b.1.1 y h0 z).map (fun hu => hu.1)) ∈
        ground.product (optionOfFinset (α := α) ground) := by
      exact Finset.mem_product.mpr ⟨hzG, huG⟩
    -- Close by transporting along the concrete branch identity for `g b`.
    have hgb :
        g b = (z, (uGoodChoice (α := α) X b.1.1 y h0 z).map (fun hu => hu.1)) := by
      rw [hgdef b]
      rw [bucketPairOfZChoice_eq_dif (X := X) (y := y) (h0 := h0) (b := b)]
      rw [dif_pos hbz]
    exact hgb ▸ hPair
  have himg_card :
      (Bsome.image g).card ≤ ground.card * (ground.card + 1) := by
    have hle :
        (Bsome.image g).card ≤ (ground.product (optionOfFinset (α := α) ground)).card :=
      Finset.card_le_card himg_sub
    -- `card (ground × optionOfFinset ground) = card ground * card(optionOfFinset ground)`.
    have hprod :
        (ground.product (optionOfFinset (α := α) ground)).card =
          ground.card * (optionOfFinset (α := α) ground).card := by
      exact Finset.card_product ground (optionOfFinset (α := α) ground)
    have hopt :
        (optionOfFinset (α := α) ground).card ≤ ground.card + 1 :=
      card_optionOfFinset_le_succ (α := α) ground
    calc
      (Bsome.image g).card
          ≤ (ground.product (optionOfFinset (α := α) ground)).card := hle
      _ = ground.card * (optionOfFinset (α := α) ground).card := hprod
      _ ≤ ground.card * (ground.card + 1) := by
            exact Nat.mul_le_mul_left ground.card hopt
  -- Combine everything.
  calc
    Bsome.card
        = ∑ p ∈ Bsome.image g, (Bsome.filter (fun b => g b = p)).card := hsum
    _ ≤ ∑ _p ∈ Bsome.image g, 2 := hsum_le
    _ = 2 * (Bsome.image g).card := hconst
    _ ≤ 2 * (ground.card * (ground.card + 1)) := by
      exact Nat.mul_le_mul_left 2 himg_card
    _ = 2 * ground.card * (ground.card + 1) := by
      simp [Nat.mul_assoc]

/-!
OutMore τ=true bucket cap (zChoice ≠ none branch): one extra missing coordinate.

This is a lemma-local refinement of the counting map used in
`card_Bucket_perXSignatureOutMore_filter_zChoice_ne_none_le_two_mul_n_mul_succ_of_fiber_le_two`.

Instead of `g : Bsome → α × Option α`, we use
`g₂ : Bsome → α × Option α × Option α` to separate the `uGoodChoice = none` bad-none branch
by recording **two** missing elements from the triple-erase set when available.

Ledger: `|im g₂| ≤ |ground| * (|ground|+1)^2`.

This lemma packages only the counting part; the fiber caps remain to be discharged separately.
-/

theorem g2_coords_mem_ground_optionOfFinset_of_filter_zChoice_ne_none
    {α : Type*} [DecidableEq α]
    {dom : Finset (Finset α)}
    {Fx0 : Finset {S // S ∈ dom}}
    (ground X : Finset α) (y h0 : α)
    (Bsome : Finset {Ssub // Ssub ∈ Fx0})
    (hXsub : X ⊆ ground)
    (hbz : ∀ b ∈ Bsome, zChoice (α := α) X b.1.1 y h0 ≠ none) :
    ∀ b ∈ Bsome,
      (match zChoice (α := α) X b.1.1 y h0 with
        | some z =>
            match uGoodChoice (α := α) X b.1.1 y h0 z with
            | some hu => (z, some hu.1, none)
            | none =>
                match uPairGoodChoice (α := α) X b.1.1 y h0 z with
                | some huv => (z, some huv.1.1, some huv.1.2)
                | none => (z, none, none)
        | none => (h0, none, none)).1 ∈ ground ∧
      (match zChoice (α := α) X b.1.1 y h0 with
        | some z =>
            match uGoodChoice (α := α) X b.1.1 y h0 z with
            | some hu => (z, some hu.1, none)
            | none =>
                match uPairGoodChoice (α := α) X b.1.1 y h0 z with
                | some huv => (z, some huv.1.1, some huv.1.2)
                | none => (z, none, none)
        | none => (h0, none, none)).2.1 ∈ optionOfFinset (α := α) ground ∧
      (match zChoice (α := α) X b.1.1 y h0 with
        | some z =>
            match uGoodChoice (α := α) X b.1.1 y h0 z with
            | some hu => (z, some hu.1, none)
            | none =>
                match uPairGoodChoice (α := α) X b.1.1 y h0 z with
                | some huv => (z, some huv.1.1, some huv.1.2)
                | none => (z, none, none)
        | none => (h0, none, none)).2.2 ∈ optionOfFinset (α := α) ground := by
  intro b hbBsome
  let g2b : α × Option α × Option α :=
    match zChoice (α := α) X b.1.1 y h0 with
    | some z =>
        match uGoodChoice (α := α) X b.1.1 y h0 z with
        | some hu => (z, some hu.1, none)
        | none =>
            match uPairGoodChoice (α := α) X b.1.1 y h0 z with
            | some huv => (z, some huv.1.1, some huv.1.2)
            | none => (z, none, none)
    | none => (h0, none, none)
  change g2b.1 ∈ ground ∧
      g2b.2.1 ∈ optionOfFinset (α := α) ground ∧
      g2b.2.2 ∈ optionOfFinset (α := α) ground
  have hbz' : zChoice (α := α) X b.1.1 y h0 ≠ none := hbz b hbBsome
  cases hzEq : zChoice (α := α) X b.1.1 y h0 with
  | none =>
      exact (hbz' hzEq).elim
  | some z =>
      have hzXS : z ∈ X \ b.1.1 :=
        zChoice_mem_X_sdiff (α := α) (X := X) (S := b.1.1) hzEq
      have hzX : z ∈ X := (Finset.mem_sdiff.mp hzXS).1
      have hzG : z ∈ ground := hXsub hzX
      cases hUGb : uGoodChoice (α := α) X b.1.1 y h0 z with
      | some hu =>
          have huMem : hu.1 ∈ ((((X \ b.1.1).erase y).erase h0).erase z) := hu.2.1
          have huErase2 : hu.1 ∈ ((X \ b.1.1).erase y).erase h0 := (Finset.mem_erase.mp huMem).2
          have huErase1 : hu.1 ∈ (X \ b.1.1).erase y := (Finset.mem_erase.mp huErase2).2
          have huXS : hu.1 ∈ X \ b.1.1 := (Finset.mem_erase.mp huErase1).2
          have huX : hu.1 ∈ X := (Finset.mem_sdiff.mp huXS).1
          have huGnd : hu.1 ∈ ground := hXsub huX
          have hsome :
              (some hu.1 : Option α) ∈ optionOfFinset (α := α) ground :=
            (mem_optionOfFinset_iff (α := α) (T := ground) (o := (some hu.1 : Option α))).2
              (Or.inr ⟨hu.1, huGnd, rfl⟩)
          have hnone :
              (none : Option α) ∈ optionOfFinset (α := α) ground :=
            (mem_optionOfFinset_iff (α := α) (T := ground) (o := (none : Option α))).2 (Or.inl rfl)
          have hg2bEq : g2b = (z, (some hu.1 : Option α), (none : Option α)) := by
            simp only [g2b, hzEq, hUGb]
          refine ⟨?_, ?_, ?_⟩
          · rw [hg2bEq]
            exact hzG
          · rw [hg2bEq]
            exact hsome
          · rw [hg2bEq]
            exact hnone
      | none =>
          cases huvEq : uPairGoodChoice (α := α) X b.1.1 y h0 z with
          | some huv =>
              let Z2 : Finset α := ((((X \ b.1.1).erase y).erase h0).erase z)
              let u : α := huv.1.1
              let v : α := huv.1.2
              have huMem : u ∈ Z2 := by
                simpa [Z2, u] using huv.2.1
              have hvMem : v ∈ Z2 := by
                simpa [Z2, v] using huv.2.2.1
              have huXS : u ∈ X \ b.1.1 := by
                have huErase2 : u ∈ ((X \ b.1.1).erase y).erase h0 :=
                  (Finset.mem_erase.mp huMem).2
                have huErase1 : u ∈ (X \ b.1.1).erase y := (Finset.mem_erase.mp huErase2).2
                exact (Finset.mem_erase.mp huErase1).2
              have hvXS : v ∈ X \ b.1.1 := by
                have hvErase2 : v ∈ ((X \ b.1.1).erase y).erase h0 :=
                  (Finset.mem_erase.mp hvMem).2
                have hvErase1 : v ∈ (X \ b.1.1).erase y := (Finset.mem_erase.mp hvErase2).2
                exact (Finset.mem_erase.mp hvErase1).2
              have huX : u ∈ X := (Finset.mem_sdiff.mp huXS).1
              have hvX : v ∈ X := (Finset.mem_sdiff.mp hvXS).1
              have huGnd : u ∈ ground := hXsub huX
              have hvGnd : v ∈ ground := hXsub hvX
              have hsomeu :
                  (some u : Option α) ∈ optionOfFinset (α := α) ground :=
                (mem_optionOfFinset_iff (α := α) (T := ground) (o := (some u : Option α))).2
                  (Or.inr ⟨u, huGnd, rfl⟩)
              have hsomev :
                  (some v : Option α) ∈ optionOfFinset (α := α) ground :=
                (mem_optionOfFinset_iff (α := α) (T := ground) (o := (some v : Option α))).2
                  (Or.inr ⟨v, hvGnd, rfl⟩)
              have hg2bEq : g2b = (z, (some u : Option α), (some v : Option α)) := by
                simp only [g2b, hzEq, hUGb, huvEq, u, v]
              refine ⟨?_, ?_, ?_⟩
              · rw [hg2bEq]
                exact hzG
              · rw [hg2bEq]
                exact hsomeu
              · rw [hg2bEq]
                exact hsomev
          | none =>
              have hnone :
                  (none : Option α) ∈ optionOfFinset (α := α) ground :=
                (mem_optionOfFinset_iff (α := α) (T := ground) (o := (none : Option α))).2
                  (Or.inl rfl)
              have hg2bEq : g2b = (z, (none : Option α), (none : Option α)) := by
                simp only [g2b, hzEq, hUGb, huvEq]
              refine ⟨?_, ?_, ?_⟩
              · rw [hg2bEq]
                exact hzG
              · rw [hg2bEq]
                exact hnone
              · rw [hg2bEq]
                exact hnone

set_option maxHeartbeats 5000000 in
theorem card_Bucket_perXSignatureOutMore_filter_zChoice_ne_none_le_two_mul_n_mul_succ_mul_succ_of_fiber_le_two
    (hreg : O1aUpgradeRegime family ground A0 h0)
    {k : WLcertKey α}
    {Sstar : {S // S ∈ o1aWitnessLiftDomWL family h0}}
    {x : α}
    (hSstar :
      Sstar ∈ wlcertAdmissibleFiber_hNotMem (family := family) (o1aWitnessLiftDomWL family h0) k)
    (σOut : PerXSignatureOutMore α) :
    let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h0
    let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
    let Fx0 :
        Finset {S // S ∈ dom} :=
      wlcertAdmissibleFiber_hNotMem_fiberForX (dom := dom) fiber Sstar.1 x
    let Uout : {Ssub // Ssub ∈ Fx0} → Finset α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      let yw :
          Σ y : α, BlockedUnionWitness family b.1.1 y :=
        chooseYAndWitness_of_hardFiber
          (family := family) (ground := ground) (A0 := A0) (h0 := h0)
          hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
          Sstar.2 b.1.2 hcert_star hcert_sub hne
      b.1.1 \ (yw.2.A ∪ yw.2.B)
    let sig0 : {Ssub // Ssub ∈ Fx0} → PerXSignature α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      perXSignature_of_hardFiber (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1) Sstar.2 b.1.2 hcert_star hcert_sub hne
    let sigOut : {Ssub // Ssub ∈ Fx0} → PerXSignatureOutMore α := fun b =>
      (sig0 b,
        trace5PlusOfFinset (α := α) (Uout b),
        t6OptionOfTrace5Plus (α := α) (Uout b))
    let X : Finset α := ground \ (k.2.2.1 ∪ k.2.2.2.1)
    let y : α := σOut.1.1
    let B : Finset {Ssub // Ssub ∈ Fx0} := Bucket (Fx := Fx0.attach) sigOut σOut
    let Bsome : Finset {Ssub // Ssub ∈ Fx0} :=
      B.filter (fun b => zChoice (α := α) X b.1.1 y h0 ≠ none)
    let g2 : {Ssub // Ssub ∈ Fx0} → α × Option α × Option α := by
      classical
      exact fun b =>
        match zChoice (α := α) X b.1.1 y h0 with
        | some z =>
            match uGoodChoice (α := α) X b.1.1 y h0 z with
            | some hu => (z, some hu.1, none)
            | none =>
                match uPairGoodChoice (α := α) X b.1.1 y h0 z with
                | some huv => (z, some huv.1.1, some huv.1.2)
                | none => (z, none, none)
        | none => (h0, none, none)
    (∀ p ∈ Bsome.image g2, (Bsome.filter (fun b => g2 b = p)).card ≤ 2) →
      Bsome.card ≤ 2 * ground.card * (ground.card + 1) * (ground.card + 1) := by
  classical
  intro dom fiber Fx0 Uout sig0 sigOut X y B Bsome g2 hFib
  -- Expand `Bsome.card` as a sum of fibers over the image of `g₂`.
  have hsum :
      Bsome.card =
        ∑ p ∈ Bsome.image g2, (Bsome.filter (fun b => g2 b = p)).card := by
    exact Finset.card_eq_sum_card_image (f := g2) (s := Bsome)
  -- Bound each fiber by `2`.
  have hsum_le :
      (∑ p ∈ Bsome.image g2, (Bsome.filter (fun b => g2 b = p)).card) ≤
        ∑ _p ∈ Bsome.image g2, 2 := by
    refine Finset.sum_le_sum ?_
    intro p hp
    exact hFib p hp
  -- Collapse the constant sum.
  have hconst :
      (∑ _p ∈ Bsome.image g2, 2) = 2 * (Bsome.image g2).card := by
    simp [Nat.mul_comm]
  have hXsub : X ⊆ ground := by
    intro a ha
    exact (Finset.mem_sdiff.mp ha).1
  have hbz_all : ∀ b ∈ Bsome, zChoice (α := α) X b.1.1 y h0 ≠ none := by
    intro b hbBsome
    exact (Finset.mem_filter.mp hbBsome).2
  -- Image-size ledger: `im g₂ ⊆ ground × optionOfFinset ground × optionOfFinset ground`.
  have hcoords_g2 :
      ∀ b ∈ Bsome,
        (g2 b).1 ∈ ground ∧
          (g2 b).2.1 ∈ optionOfFinset (α := α) ground ∧
          (g2 b).2.2 ∈ optionOfFinset (α := α) ground := by
    intro b hbBsome
    have hnoneOpt : (none : Option α) ∈ optionOfFinset (α := α) ground :=
      (mem_optionOfFinset_iff (α := α) (T := ground) (o := (none : Option α))).2
        (Or.inl rfl)
    have hsomeOpt :
        ∀ t : α, t ∈ ground → (some t : Option α) ∈ optionOfFinset (α := α) ground := by
      intro t ht
      exact
        (mem_optionOfFinset_iff (α := α) (T := ground) (o := (some t : Option α))).2
          (Or.inr ⟨t, ht, rfl⟩)
    have hbz : zChoice (α := α) X b.1.1 y h0 ≠ none := hbz_all b hbBsome
    cases hzEq : zChoice (α := α) X b.1.1 y h0 with
    | none =>
        exact (hbz hzEq).elim
    | some z =>
        have hzXS : z ∈ X \ b.1.1 := zChoice_mem_X_sdiff (α := α) (X := X) (S := b.1.1) hzEq
        have hzX : z ∈ X := (Finset.mem_sdiff.mp hzXS).1
        have hzG : z ∈ ground := hXsub hzX
        have hmem_Xsdiff_of_mem_tail :
            ∀ t : α, t ∈ ((((X \ b.1.1).erase y).erase h0).erase z) → t ∈ X \ b.1.1 := by
          intro t ht
          have ht2 : t ∈ ((X \ b.1.1).erase y).erase h0 := (Finset.mem_erase.mp ht).2
          have ht1 : t ∈ (X \ b.1.1).erase y := (Finset.mem_erase.mp ht2).2
          exact (Finset.mem_erase.mp ht1).2
        cases hUGb : uGoodChoice (α := α) X b.1.1 y h0 z with
        | some hu =>
            have huMem : hu.1 ∈ ((((X \ b.1.1).erase y).erase h0).erase z) := hu.2.1
            have huXS : hu.1 ∈ X \ b.1.1 := hmem_Xsdiff_of_mem_tail hu.1 huMem
            have huX : hu.1 ∈ X := (Finset.mem_sdiff.mp huXS).1
            have huGnd : hu.1 ∈ ground := hXsub huX
            have hg2 : g2 b = (z, (some hu.1 : Option α), (none : Option α)) := by
              simp only [g2, hzEq, hUGb]
            refine ⟨?_, ?_, ?_⟩
            · rw [hg2]
              exact hzG
            · rw [hg2]
              exact hsomeOpt hu.1 huGnd
            · rw [hg2]
              exact hnoneOpt
        | none =>
            cases huvEq : uPairGoodChoice (α := α) X b.1.1 y h0 z with
            | some huv =>
                let Z2 : Finset α := ((((X \ b.1.1).erase y).erase h0).erase z)
                let u : α := huv.1.1
                let v : α := huv.1.2
                have huMem : u ∈ Z2 := by
                  simpa [Z2, u] using huv.2.1
                have hvMem : v ∈ Z2 := by
                  simpa [Z2, v] using huv.2.2.1
                have huXS : u ∈ X \ b.1.1 := by
                  have huMem' : u ∈ ((((X \ b.1.1).erase y).erase h0).erase z) := by
                    simpa [Z2] using huMem
                  exact hmem_Xsdiff_of_mem_tail u huMem'
                have hvXS : v ∈ X \ b.1.1 := by
                  have hvMem' : v ∈ ((((X \ b.1.1).erase y).erase h0).erase z) := by
                    simpa [Z2] using hvMem
                  exact hmem_Xsdiff_of_mem_tail v hvMem'
                have huX : u ∈ X := (Finset.mem_sdiff.mp huXS).1
                have hvX : v ∈ X := (Finset.mem_sdiff.mp hvXS).1
                have huGnd : u ∈ ground := hXsub huX
                have hvGnd : v ∈ ground := hXsub hvX
                have hg2 : g2 b = (z, (some u : Option α), (some v : Option α)) := by
                  simp only [g2, hzEq, hUGb, huvEq, u, v]
                refine ⟨?_, ?_, ?_⟩
                · rw [hg2]
                  exact hzG
                · rw [hg2]
                  exact hsomeOpt u huGnd
                · rw [hg2]
                  exact hsomeOpt v hvGnd
            | none =>
                have hg2 : g2 b = (z, (none : Option α), (none : Option α)) := by
                  simp only [g2, hzEq, hUGb, huvEq]
                refine ⟨?_, ?_, ?_⟩
                · rw [hg2]
                  exact hzG
                · rw [hg2]
                  exact hnoneOpt
                · rw [hg2]
                  exact hnoneOpt
  let Cod2 : Finset (α × (Option α × Option α)) :=
    ground.product
      ((optionOfFinset (α := α) ground).product (optionOfFinset (α := α) ground))
  have hmem_g2 :
      ∀ b ∈ Bsome,
        g2 b ∈ Cod2 := by
    intro b hbBsome
    rcases hcoords_g2 b hbBsome with ⟨hzG, huOpt, hvOpt⟩
    exact Finset.mem_product.mpr ⟨hzG, Finset.mem_product.mpr ⟨huOpt, hvOpt⟩⟩
  have himg_sub :
      Bsome.image g2 ⊆ Cod2 := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨b, hbBsome, rfl⟩
    exact hmem_g2 b hbBsome
  have himg_card :
      (Bsome.image g2).card ≤ ground.card * (ground.card + 1) * (ground.card + 1) := by
    have hle :
        (Bsome.image g2).card ≤ Cod2.card :=
      Finset.card_le_card himg_sub
    have hprod1 :
        Cod2.card =
          ground.card *
            ((optionOfFinset (α := α) ground).product (optionOfFinset (α := α) ground)).card := by
      simp [Cod2, Finset.card_product]
    have hprod2 :
        ((optionOfFinset (α := α) ground).product (optionOfFinset (α := α) ground)).card =
          (optionOfFinset (α := α) ground).card * (optionOfFinset (α := α) ground).card := by
      exact Finset.card_product (optionOfFinset (α := α) ground) (optionOfFinset (α := α) ground)
    have hopt :
        (optionOfFinset (α := α) ground).card ≤ ground.card + 1 :=
      card_optionOfFinset_le_succ (α := α) ground
    calc
      (Bsome.image g2).card
          ≤ Cod2.card := hle
      _ = ground.card *
            ((optionOfFinset (α := α) ground).product (optionOfFinset (α := α) ground)).card :=
          hprod1
      _ = ground.card *
            ((optionOfFinset (α := α) ground).card * (optionOfFinset (α := α) ground).card) := by
          rw [hprod2]
      _ ≤ ground.card * ((ground.card + 1) * (ground.card + 1)) := by
          exact Nat.mul_le_mul_left ground.card (Nat.mul_le_mul hopt hopt)
      _ = ground.card * (ground.card + 1) * (ground.card + 1) := by
          simp [Nat.mul_assoc]
  -- Combine everything.
  calc
    Bsome.card
        = ∑ p ∈ Bsome.image g2, (Bsome.filter (fun b => g2 b = p)).card := hsum
    _ ≤ ∑ _p ∈ Bsome.image g2, 2 := hsum_le
    _ = 2 * (Bsome.image g2).card := hconst
    _ ≤ 2 * (ground.card * (ground.card + 1) * (ground.card + 1)) := by
          exact Nat.mul_le_mul_left 2 himg_card
    _ = 2 * ground.card * (ground.card + 1) * (ground.card + 1) := by
          simp [Nat.mul_assoc]

/-!
OutMore τ=true, `zChoice ≠ none` bounded-fiber cap: provenance split.

We keep the existing counting lemma in terms of `g : Bsome → α × Option α`. To avoid paying any
new image-size ledger factor, we only use the Bool provenance tag *internally*:

`prov(b) := (wz.core.erase z).Nonempty`, where `wz` is the same normalized z-witness used in `g`.

The goal is to bound each `g`-fiber by splitting it into the disjoint union of two provenance
subfibers (core-erase vs tx2Plus branch).
-/

theorem card_filter_g_le_two_of_card_filter_prov_le_one
    {β : Type*} [DecidableEq β]
    {α : Type*} [DecidableEq α]
    (Bsome : Finset β) (g : β → α × Option α) (prov : β → Bool)
    (htrue : ∀ p : α × Option α,
      (Bsome.filter (fun b => g b = p ∧ prov b = true)).card ≤ 1)
    (hfalse : ∀ p : α × Option α,
      (Bsome.filter (fun b => g b = p ∧ prov b = false)).card ≤ 1) :
    ∀ p : α × Option α, (Bsome.filter (fun b => g b = p)).card ≤ 2 := by
  classical
  intro p
  -- Split the `g`-fiber by the Bool provenance value.
  let F : Finset β := Bsome.filter (fun b => g b = p)
  have hsub :
      F ⊆
        (Bsome.filter (fun b => g b = p ∧ prov b = true)) ∪
          (Bsome.filter (fun b => g b = p ∧ prov b = false)) := by
    intro b hbF
    have hbB : b ∈ Bsome := (Finset.mem_filter.mp hbF).1
    have hgb : g b = p := (Finset.mem_filter.mp hbF).2
    by_cases hp : prov b = true
    · refine Finset.mem_union.mpr (Or.inl ?_)
      exact Finset.mem_filter.mpr ⟨hbB, ⟨hgb, hp⟩⟩
    · have hp' : prov b = false := by
        cases hprov : prov b <;> simp [hprov] at hp ⊢
      refine Finset.mem_union.mpr (Or.inr ?_)
      exact Finset.mem_filter.mpr ⟨hbB, ⟨hgb, hp'⟩⟩
  have hcardF :
      F.card ≤
        ((Bsome.filter (fun b => g b = p ∧ prov b = true)) ∪
            (Bsome.filter (fun b => g b = p ∧ prov b = false))).card :=
    Finset.card_le_card hsub
  have hcardU :
      ((Bsome.filter (fun b => g b = p ∧ prov b = true)) ∪
            (Bsome.filter (fun b => g b = p ∧ prov b = false))).card ≤ 2 := by
    have hsum :
        ((Bsome.filter (fun b => g b = p ∧ prov b = true)) ∪
              (Bsome.filter (fun b => g b = p ∧ prov b = false))).card ≤
          (Bsome.filter (fun b => g b = p ∧ prov b = true)).card +
            (Bsome.filter (fun b => g b = p ∧ prov b = false)).card := by
      simpa using
        (Finset.card_union_le
          (Bsome.filter (fun b => g b = p ∧ prov b = true))
          (Bsome.filter (fun b => g b = p ∧ prov b = false)))
    calc
      ((Bsome.filter (fun b => g b = p ∧ prov b = true)) ∪
              (Bsome.filter (fun b => g b = p ∧ prov b = false))).card
          ≤ (Bsome.filter (fun b => g b = p ∧ prov b = true)).card +
              (Bsome.filter (fun b => g b = p ∧ prov b = false)).card := hsum
      _ ≤ 1 + 1 := by
            exact Nat.add_le_add (htrue p) (hfalse p)
      _ = 2 := by simp
  exact le_trans (le_trans hcardF hcardU) (le_of_eq rfl)

/-!
Helper for the `zChoice ≠ none` bounded-fiber cap:
for a fixed `z`, the `g`-fiber at `(z, none)` has card ≤ 2 by collapsing `X \\ S` to a
pair `{y,z}` or triple `{y,h0,z}` (no "no-extra-common-elements" reasoning).
-/

theorem card_Bsome_filter_g_eq_mk_z_none_le_two
    (hreg : O1aUpgradeRegime family ground A0 h0)
    {k : WLcertKey α}
    {Sstar : {S // S ∈ o1aWitnessLiftDomWL family h0}}
    {x : α}
    (hSstar :
      Sstar ∈ wlcertAdmissibleFiber_hNotMem (family := family) (o1aWitnessLiftDomWL family h0) k)
    (σOut : PerXSignatureOutMore α)
    (z : α) :
    let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h0
    let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
    let Fx0 :
        Finset {S // S ∈ dom} :=
      wlcertAdmissibleFiber_hNotMem_fiberForX (dom := dom) fiber Sstar.1 x
    let Uout : {Ssub // Ssub ∈ Fx0} → Finset α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      let yw :
          Σ y : α, BlockedUnionWitness family b.1.1 y :=
        chooseYAndWitness_of_hardFiber
          (family := family) (ground := ground) (A0 := A0) (h0 := h0)
          hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
          Sstar.2 b.1.2 hcert_star hcert_sub hne
      b.1.1 \ (yw.2.A ∪ yw.2.B)
    let sig0 : {Ssub // Ssub ∈ Fx0} → PerXSignature α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      perXSignature_of_hardFiber (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1) Sstar.2 b.1.2 hcert_star hcert_sub hne
    let sigOut : {Ssub // Ssub ∈ Fx0} → PerXSignatureOutMore α := fun b =>
      (sig0 b,
        trace5PlusOfFinset (α := α) (Uout b),
        t6OptionOfTrace5Plus (α := α) (Uout b))
    let X : Finset α := ground \ (k.2.2.1 ∪ k.2.2.2.1)
    let y : α := σOut.1.1
    let B : Finset {Ssub // Ssub ∈ Fx0} := Bucket (Fx := Fx0.attach) sigOut σOut
    let Bsome : Finset {Ssub // Ssub ∈ Fx0} :=
      B.filter (fun b => zChoice (α := α) X b.1.1 y h0 ≠ none)
    let g : {Ssub // Ssub ∈ Fx0} → α × Option α := by
      classical
      exact fun b =>
        if hz : zChoice (α := α) X b.1.1 y h0 ≠ none then
          let ex : ∃ z, zChoice (α := α) X b.1.1 y h0 = some z :=
            exists_z_of_zChoice_ne_none (α := α) (X := X) (S := b.1.1) (y0 := y) (h0 := h0) hz
          let z : α := Classical.choose ex
          (z, uChoice (α := α) X b.1.1 y h0 z)
        else (h0, none)
    (Bsome.filter (fun b => g b = (z, none))).card ≤ 2 := by
  classical
  intro dom fiber Fx0 Uout sig0 sigOut X y B Bsome g
  -- Every `b` in the fiber satisfies the pair/triple missing-set collapse.
  have hsub :
      (Bsome.filter (fun b => g b = (z, none))) ⊆
        (B.filter (fun b => X \ b.1.1 = ({y, z} : Finset α))) ∪
          (B.filter (fun b => X \ b.1.1 = ({y, h0, z} : Finset α))) := by
    intro b hb
    have hbBsome : b ∈ Bsome := (Finset.mem_filter.mp hb).1
    have hbB : b ∈ B := (Finset.mem_filter.mp hbBsome).1
    have hbzChoice : zChoice (α := α) X b.1.1 y h0 ≠ none := (Finset.mem_filter.mp hbBsome).2
    have hgb : g b = (z, none) := (Finset.mem_filter.mp hb).2
    -- Unfold `g` at `b` and extract the `zChoice = some z` witness.
    have hzEq : zChoice (α := α) X b.1.1 y h0 = some z := by
      -- Use the same `Classical.choose` witness as in `g`.
      let ex : ∃ z0, zChoice (α := α) X b.1.1 y h0 = some z0 :=
        exists_z_of_zChoice_ne_none (α := α) (X := X) (S := b.1.1) (y0 := y) (h0 := h0) hbzChoice
      have : g b = (Classical.choose ex, uChoice (α := α) X b.1.1 y h0 (Classical.choose ex)) := by
        simp [g, hbzChoice]
      have hzEq' : Classical.choose ex = z := by
        have := congrArg Prod.fst (this.symm.trans hgb)
        simpa using this
      -- Rewrite the chosen witness to the fixed `z`.
      have hzSpec : zChoice (α := α) X b.1.1 y h0 = some (Classical.choose ex) :=
        Classical.choose_spec ex
      simpa [hzEq'] using hzSpec
    have huNone : uChoice (α := α) X b.1.1 y h0 z = none := by
      -- Second component of `g b = (z, none)`.
      let ex : ∃ z0, zChoice (α := α) X b.1.1 y h0 = some z0 :=
        exists_z_of_zChoice_ne_none (α := α) (X := X) (S := b.1.1) (y0 := y) (h0 := h0) hbzChoice
      have : g b = (Classical.choose ex, uChoice (α := α) X b.1.1 y h0 (Classical.choose ex)) := by
        simp [g, hbzChoice]
      have hzEq' : Classical.choose ex = z := by
        have := congrArg Prod.fst (this.symm.trans hgb)
        simpa using this
      have huEq : uChoice (α := α) X b.1.1 y h0 (Classical.choose ex) = none := by
        have := congrArg Prod.snd (this.symm.trans hgb)
        simpa using this
      simpa [hzEq'] using huEq
    -- Show `y ∈ X \\ b` using the bucket-fixed signature.
    have hbSig : sigOut b = σOut := (Finset.mem_filter.mp hbB).2
    have hSig11 : (sigOut b).1.1 = σOut.1.1 :=
      congrArg (fun t : PerXSignatureOutMore α => t.1.1) hbSig
    have hySig : (sig0 b).1 = y := by
      simpa [sigOut, y] using hSig11
    have hbFiber : b.1 ∈ fiber := (Finset.mem_filter.mp b.2).1
    have hcert_sub :
        ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
      (Finset.mem_filter.mp hbFiber).2
    have hcert_star :
        ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
      (Finset.mem_filter.mp hSstar).2
    have hne : b.1.1 ≠ Sstar.1 :=
      PerXSubfiber.ne_Sstar_val_of_mem_fiberForX
        (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
        (Ssub := b.1) b.2
    let yCh : α :=
      chooseMissingFromRef (family := family) (h0 := h0) Sstar.1 b.1.1 Sstar.2 b.1.2 hne
    have hyChSig0 : (sig0 b).1 = yCh := by
      simp [sig0, perXSignature_of_hardFiber, perXSignature, chooseYAndWitness_of_hardFiber, yCh]
    have hyEq : yCh = y := by simpa [hyChSig0] using hySig
    have hyXCh : yCh ∈ X := by
      have hyX' :
          yCh ∈ (ground \ (k.2.2.1 ∪ k.2.2.2.1)) := by
        simpa [yCh] using
          (chooseMissingFromRef_mem_X_of_hardFiber (family := family) (ground := ground) (A0 := A0)
            (h0 := h0) hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
            Sstar.2 b.1.2 hcert_star hcert_sub hne)
      simpa [X] using hyX'
    have hyNotCh : yCh ∉ b.1.1 := by
      have hyDiff :
          yCh ∈ Sstar.1 \ b.1.1 := by
        simpa [yCh] using
          (chooseMissingFromRef_spec (family := family) (h0 := h0) Sstar.1 b.1.1
            Sstar.2 b.1.2 hne)
      exact (Finset.mem_sdiff.mp hyDiff).2
    have hy : y ∈ X \ b.1.1 := by
      have : yCh ∈ X \ b.1.1 := Finset.mem_sdiff.mpr ⟨hyXCh, hyNotCh⟩
      simpa [hyEq] using this
    -- Apply the pair/triple collapse lemma.
    have hXcase :
        X \ b.1.1 = ({y, z} : Finset α) ∨ X \ b.1.1 = ({y, h0, z} : Finset α) :=
      X_sdiff_eq_pair_or_triple_of_uChoice_eq_none (α := α) (X := X) (S := b.1.1)
        (y0 := y) (h0 := h0) (z := z) hy hzEq huNone
    rcases hXcase with hPair | hTrip
    · refine Finset.mem_union.mpr (Or.inl ?_)
      exact Finset.mem_filter.mpr ⟨hbB, hPair⟩
    · refine Finset.mem_union.mpr (Or.inr ?_)
      exact Finset.mem_filter.mpr ⟨hbB, hTrip⟩
  have hcard_sub :
      (Bsome.filter (fun b => g b = (z, none))).card ≤
        ((B.filter (fun b => X \ b.1.1 = ({y, z} : Finset α))) ∪
              (B.filter (fun b => X \ b.1.1 = ({y, h0, z} : Finset α)))).card :=
    Finset.card_le_card hsub
  -- Each side of the union has card ≤ 1 by the sharp missing-set bucket caps.
  have hcard1 :
      (B.filter (fun b => X \ b.1.1 = ({y, z} : Finset α))).card ≤ 1 := by
    simpa [X] using
      (card_Bucket_perXSignatureOutMore_filter_X_sdiff_eq_pair_le_one (family := family)
        (ground := ground) (A0 := A0) (h0 := h0) hreg (k := k) (Sstar := Sstar) (x := x)
        hSstar (σOut := σOut) (y1 := y) (y2 := z))
  have hcard2 :
      (B.filter (fun b => X \ b.1.1 = ({y, h0, z} : Finset α))).card ≤ 1 := by
    simpa [X] using
      (card_Bucket_perXSignatureOutMore_filter_X_sdiff_eq_triple_le_one (family := family)
        (ground := ground) (A0 := A0) (h0 := h0) hreg (k := k) (Sstar := Sstar) (x := x)
        hSstar (σOut := σOut) (y1 := y) (y2 := h0) (y3 := z))
  have hcard_union :
      ((B.filter (fun b => X \ b.1.1 = ({y, z} : Finset α))) ∪
            (B.filter (fun b => X \ b.1.1 = ({y, h0, z} : Finset α)))).card ≤ 2 := by
    have hsum :
        ((B.filter (fun b => X \ b.1.1 = ({y, z} : Finset α))) ∪
              (B.filter (fun b => X \ b.1.1 = ({y, h0, z} : Finset α)))).card ≤
          (B.filter (fun b => X \ b.1.1 = ({y, z} : Finset α))).card +
            (B.filter (fun b => X \ b.1.1 = ({y, h0, z} : Finset α))).card := by
      simpa using
        (Finset.card_union_le
          (B.filter (fun b => X \ b.1.1 = ({y, z} : Finset α)))
          (B.filter (fun b => X \ b.1.1 = ({y, h0, z} : Finset α))))
    calc
      ((B.filter (fun b => X \ b.1.1 = ({y, z} : Finset α))) ∪
              (B.filter (fun b => X \ b.1.1 = ({y, h0, z} : Finset α)))).card
          ≤ (B.filter (fun b => X \ b.1.1 = ({y, z} : Finset α))).card +
              (B.filter (fun b => X \ b.1.1 = ({y, h0, z} : Finset α))).card := hsum
      _ ≤ 1 + 1 := Nat.add_le_add hcard1 hcard2
      _ = 2 := by simp
  exact le_trans hcard_sub hcard_union

/-!
τ=true outMore-specialized `(z, none)` fiber cap for the `uGoodChoice`-based map
`g b := (z, (uGoodChoice …).map (·.1))`.

This is the missing seam: for τ=true buckets we must control the `uGoodChoice = none`
case. We split it into:
- good-none: `Z2 = ∅`, which collapses to the existing pair/triple missing-set buckets.
- bad-none: `Z2.Nonempty` but `Z2.erase (choose _) ≠ ∅`, which must be killed locally.

The bad-none branch is intentionally time-boxed; if it does not collapse quickly from
existing hard-fiber one-step blocked-extension facts + existing collapse/cap lemmas,
we hard stop and re-plan (no new intersection-control machinery).
-/
theorem card_Bsome_filter_g_eq_mk_z_none_le_two_tauTrue_uGoodChoice_of_Z2_empty_on_fiber
    (hreg : O1aUpgradeRegime family ground A0 h0)
    {k : WLcertKey α}
    {Sstar : {S // S ∈ o1aWitnessLiftDomWL family h0}}
    {x : α}
    (hSstar :
      Sstar ∈ wlcertAdmissibleFiber_hNotMem (family := family) (o1aWitnessLiftDomWL family h0) k)
    (σOut : PerXSignatureOutMore α)
    (z : α) :
    let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h0
    let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
    let Fx0 :
        Finset {S // S ∈ dom} :=
      wlcertAdmissibleFiber_hNotMem_fiberForX (dom := dom) fiber Sstar.1 x
    let Uout : {Ssub // Ssub ∈ Fx0} → Finset α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      let yw :
          Σ y : α, BlockedUnionWitness family b.1.1 y :=
        chooseYAndWitness_of_hardFiber
          (family := family) (ground := ground) (A0 := A0) (h0 := h0)
          hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
          Sstar.2 b.1.2 hcert_star hcert_sub hne
      b.1.1 \ (yw.2.A ∪ yw.2.B)
    let sig0 : {Ssub // Ssub ∈ Fx0} → PerXSignature α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      perXSignature_of_hardFiber (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1) Sstar.2 b.1.2 hcert_star hcert_sub hne
    let sigOut : {Ssub // Ssub ∈ Fx0} → PerXSignatureOutMore α := fun b =>
      (sig0 b,
        trace5PlusOfFinset (α := α) (Uout b),
        t6OptionOfTrace5Plus (α := α) (Uout b))
    let X : Finset α := ground \ (k.2.2.1 ∪ k.2.2.2.1)
    let y : α := σOut.1.1
    let B : Finset {Ssub // Ssub ∈ Fx0} := Bucket (Fx := Fx0.attach) sigOut σOut
    let Bsome : Finset {Ssub // Ssub ∈ Fx0} :=
      B.filter (fun b => zChoice (α := α) X b.1.1 y h0 ≠ none)
    let g : {Ssub // Ssub ∈ Fx0} → α × Option α := by
      classical
      exact fun b =>
        if hz : zChoice (α := α) X b.1.1 y h0 ≠ none then
          let ex : ∃ z0, zChoice (α := α) X b.1.1 y h0 = some z0 :=
            exists_z_of_zChoice_ne_none (α := α) (X := X) (S := b.1.1) (y0 := y) (h0 := h0) hz
          let z0 : α := Classical.choose ex
          (z0, (uGoodChoice (α := α) X b.1.1 y h0 z0).map (fun hu => hu.1))
        else (h0, none)
    (∀ b ∈ (Bsome.filter (fun b => g b = (z, none))),
        ((((X \ b.1.1).erase y).erase h0).erase z) = (∅ : Finset α)) →
      (Bsome.filter (fun b => g b = (z, none))).card ≤ 2 := by
  classical
  intro dom fiber Fx0 Uout sig0 sigOut X y B Bsome g hZ2Empty
  have hsub :
      (Bsome.filter (fun b => g b = (z, none))) ⊆
        (B.filter (fun b => X \ b.1.1 = ({y, z} : Finset α))) ∪
          (B.filter (fun b => X \ b.1.1 = ({y, h0, z} : Finset α))) := by
    intro b hb
    have hbBsome : b ∈ Bsome := (Finset.mem_filter.mp hb).1
    have hbB : b ∈ B := (Finset.mem_filter.mp hbBsome).1
    have hbzChoice : zChoice (α := α) X b.1.1 y h0 ≠ none := (Finset.mem_filter.mp hbBsome).2
    have hgb : g b = (z, none) := (Finset.mem_filter.mp hb).2
    -- Extract `zChoice = some z` from `g b = (z, none)`.
    have hzEq : zChoice (α := α) X b.1.1 y h0 = some z := by
      let ex : ∃ z0, zChoice (α := α) X b.1.1 y h0 = some z0 :=
        exists_z_of_zChoice_ne_none (α := α) (X := X) (S := b.1.1) (y0 := y) (h0 := h0) hbzChoice
      have hg :
          g b =
            (Classical.choose ex,
              (uGoodChoice (α := α) X b.1.1 y h0 (Classical.choose ex)).map (fun hu => hu.1)) := by
        simp [g, hbzChoice]
      have hzEq' : Classical.choose ex = z := by
        have := congrArg Prod.fst (hg.symm.trans hgb)
        simpa using this
      have hzSpec : zChoice (α := α) X b.1.1 y h0 = some (Classical.choose ex) :=
        Classical.choose_spec ex
      simpa [hzEq'] using hzSpec
    -- Use the local `Z2 = ∅` hypothesis to get `uChoice = none`.
    have hZ2 : ((((X \ b.1.1).erase y).erase h0).erase z) = (∅ : Finset α) :=
      hZ2Empty b hb
    have huNone : uChoice (α := α) X b.1.1 y h0 z = none := by
      exact (uChoice_eq_none_iff (α := α) (X := X) (S := b.1.1) (y0 := y) (h0 := h0) (z := z)).2 hZ2
    -- Show `y ∈ X \\ b` using the bucket-fixed signature (same as in the `uChoice`-based lemma).
    have hbSig : sigOut b = σOut := (Finset.mem_filter.mp hbB).2
    have hSig11 : (sigOut b).1.1 = σOut.1.1 :=
      congrArg (fun t : PerXSignatureOutMore α => t.1.1) hbSig
    have hySig : (sig0 b).1 = y := by
      simpa [sigOut, y] using hSig11
    have hbFiber : b.1 ∈ fiber := (Finset.mem_filter.mp b.2).1
    have hcert_sub :
        ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
      (Finset.mem_filter.mp hbFiber).2
    have hcert_star :
        ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
      (Finset.mem_filter.mp hSstar).2
    have hne : b.1.1 ≠ Sstar.1 :=
      ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
        (Ssub := b.1) b.2
    let yCh : α :=
      chooseMissingFromRef (family := family) (h0 := h0) Sstar.1 b.1.1 Sstar.2 b.1.2 hne
    have hyChSig0 : (sig0 b).1 = yCh := by
      simp [sig0, perXSignature_of_hardFiber, perXSignature, chooseYAndWitness_of_hardFiber, yCh]
    have hyEq : yCh = y := by simpa [hyChSig0] using hySig
    have hyXCh : yCh ∈ X := by
      have hyX' :
          yCh ∈ (ground \ (k.2.2.1 ∪ k.2.2.2.1)) := by
        simpa [yCh] using
          (chooseMissingFromRef_mem_X_of_hardFiber (family := family) (ground := ground) (A0 := A0)
            (h0 := h0) hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
            Sstar.2 b.1.2 hcert_star hcert_sub hne)
      simpa [X] using hyX'
    have hyNotCh : yCh ∉ b.1.1 := by
      have hyDiff :
          yCh ∈ Sstar.1 \ b.1.1 := by
        simpa [yCh] using
          (chooseMissingFromRef_spec (family := family) (h0 := h0) Sstar.1 b.1.1
            Sstar.2 b.1.2 hne)
      exact (Finset.mem_sdiff.mp hyDiff).2
    have hy : y ∈ X \ b.1.1 := by
      have : yCh ∈ X \ b.1.1 := Finset.mem_sdiff.mpr ⟨hyXCh, hyNotCh⟩
      simpa [hyEq] using this
    have hXcase :
        X \ b.1.1 = ({y, z} : Finset α) ∨ X \ b.1.1 = ({y, h0, z} : Finset α) :=
      X_sdiff_eq_pair_or_triple_of_uChoice_eq_none (α := α) (X := X) (S := b.1.1)
        (y0 := y) (h0 := h0) (z := z) hy hzEq huNone
    rcases hXcase with hPair | hTrip
    · refine Finset.mem_union.mpr (Or.inl ?_)
      exact Finset.mem_filter.mpr ⟨hbB, hPair⟩
    · refine Finset.mem_union.mpr (Or.inr ?_)
      exact Finset.mem_filter.mpr ⟨hbB, hTrip⟩
  have hcard_sub :
      (Bsome.filter (fun b => g b = (z, none))).card ≤
        ((B.filter (fun b => X \ b.1.1 = ({y, z} : Finset α))) ∪
              (B.filter (fun b => X \ b.1.1 = ({y, h0, z} : Finset α)))).card :=
    Finset.card_le_card hsub
  have hcard1 :
      (B.filter (fun b => X \ b.1.1 = ({y, z} : Finset α))).card ≤ 1 := by
    simpa [X] using
      (card_Bucket_perXSignatureOutMore_filter_X_sdiff_eq_pair_le_one (family := family)
        (ground := ground) (A0 := A0) (h0 := h0) hreg (k := k) (Sstar := Sstar) (x := x)
        hSstar (σOut := σOut) (y1 := y) (y2 := z))
  have hcard2 :
      (B.filter (fun b => X \ b.1.1 = ({y, h0, z} : Finset α))).card ≤ 1 := by
    simpa [X] using
      (card_Bucket_perXSignatureOutMore_filter_X_sdiff_eq_triple_le_one (family := family)
        (ground := ground) (A0 := A0) (h0 := h0) hreg (k := k) (Sstar := Sstar) (x := x)
        hSstar (σOut := σOut) (y1 := y) (y2 := h0) (y3 := z))
  have hcard_union :
      ((B.filter (fun b => X \ b.1.1 = ({y, z} : Finset α))) ∪
            (B.filter (fun b => X \ b.1.1 = ({y, h0, z} : Finset α)))).card ≤ 2 := by
    have hsum :
        ((B.filter (fun b => X \ b.1.1 = ({y, z} : Finset α))) ∪
              (B.filter (fun b => X \ b.1.1 = ({y, h0, z} : Finset α)))).card ≤
          (B.filter (fun b => X \ b.1.1 = ({y, z} : Finset α))).card +
            (B.filter (fun b => X \ b.1.1 = ({y, h0, z} : Finset α))).card := by
      simpa using
        (Finset.card_union_le
          (B.filter (fun b => X \ b.1.1 = ({y, z} : Finset α)))
          (B.filter (fun b => X \ b.1.1 = ({y, h0, z} : Finset α))))
    calc
      ((B.filter (fun b => X \ b.1.1 = ({y, z} : Finset α))) ∪
              (B.filter (fun b => X \ b.1.1 = ({y, h0, z} : Finset α)))).card
          ≤ (B.filter (fun b => X \ b.1.1 = ({y, z} : Finset α))).card +
              (B.filter (fun b => X \ b.1.1 = ({y, h0, z} : Finset α))).card := hsum
      _ ≤ 1 + 1 := Nat.add_le_add hcard1 hcard2
      _ = 2 := by simp
  exact le_trans hcard_sub hcard_union
  /- TODO (contract gap): τ=true outMore `(z, none)` fiber cap for the `uGoodChoice`-based map.
  Currently stuck on the bad-none branch (`uGoodChoice = none` with `Z2.Nonempty`), see the
  failed goal at `SunflowerLean/Obstruction.lean:12357`.

  Hard stop per cone: we need an explicit new local lever or a selector tweak that forces the
  triple/quad collapse by construction; no “no extra common elements” framework.
  -/

/-!
`g₂`-based fiber caps for the `zChoice ≠ none` outMore counting map.

This is the lemma-local refinement used by
`card_Bucket_perXSignatureOutMore_filter_zChoice_ne_none_le_two_mul_n_mul_succ_mul_succ_of_fiber_le_two`:

`g₂ b := (z, uOpt, vOpt)` where `uOpt` comes from `uGoodChoice` and `vOpt` (when present) comes from
`uPairGoodChoice`.

The key new ingredient is the quad-only collapse after erasing `h0`:
`(X.erase h0) \\ S = {y,z,u,v}` for the `(z, some u, some v)` fibers.
-/

theorem card_Bsome_filter_g2_eq_mk_z_some_some_le_one
    (hreg : O1aUpgradeRegime family ground A0 h0)
    {k : WLcertKey α}
    {Sstar : {S // S ∈ o1aWitnessLiftDomWL family h0}}
    {x : α}
    (hSstar :
      Sstar ∈ wlcertAdmissibleFiber_hNotMem (family := family) (o1aWitnessLiftDomWL family h0) k)
    (σOut : PerXSignatureOutMore α)
    (z u v : α) :
    let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h0
    let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
    let Fx0 :
        Finset {S // S ∈ dom} :=
      wlcertAdmissibleFiber_hNotMem_fiberForX (dom := dom) fiber Sstar.1 x
    let Uout : {Ssub // Ssub ∈ Fx0} → Finset α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      let yw :
          Σ y : α, BlockedUnionWitness family b.1.1 y :=
        chooseYAndWitness_of_hardFiber
          (family := family) (ground := ground) (A0 := A0) (h0 := h0)
          hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
          Sstar.2 b.1.2 hcert_star hcert_sub hne
      b.1.1 \ (yw.2.A ∪ yw.2.B)
    let sig0 : {Ssub // Ssub ∈ Fx0} → PerXSignature α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      perXSignature_of_hardFiber (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1) Sstar.2 b.1.2 hcert_star hcert_sub hne
    let sigOut : {Ssub // Ssub ∈ Fx0} → PerXSignatureOutMore α := fun b =>
      (sig0 b,
        trace5PlusOfFinset (α := α) (Uout b),
        t6OptionOfTrace5Plus (α := α) (Uout b))
    let X : Finset α := ground \ (k.2.2.1 ∪ k.2.2.2.1)
    let y : α := σOut.1.1
    let B : Finset {Ssub // Ssub ∈ Fx0} := Bucket (Fx := Fx0.attach) sigOut σOut
    let Bsome : Finset {Ssub // Ssub ∈ Fx0} :=
      B.filter (fun b => zChoice (α := α) X b.1.1 y h0 ≠ none)
    let g2 : {Ssub // Ssub ∈ Fx0} → α × Option α × Option α := by
      classical
      exact fun b =>
        match zChoice (α := α) X b.1.1 y h0 with
        | some z0 =>
            match uGoodChoice (α := α) X b.1.1 y h0 z0 with
            | some hu => (z0, some hu.1, none)
            | none =>
                match uPairGoodChoice (α := α) X b.1.1 y h0 z0 with
                | some huv => (z0, some huv.1.1, some huv.1.2)
                | none => (z0, none, none)
        | none => (h0, none, none)
    (Bsome.filter (fun b => g2 b = (z, (some u : Option α), (some v : Option α)))).card ≤ 1 := by
  classical
  intro dom fiber Fx0 Uout sig0 sigOut X y B Bsome g2
  -- Reduce to the sharp erased-`h0` quad missing-set bucket.
  have hsub :
      (Bsome.filter (fun b => g2 b = (z, (some u : Option α), (some v : Option α)))) ⊆
        (B.filter (fun b => (X.erase h0) \ b.1.1 = ({y, z, u, v} : Finset α))) := by
    intro b hb
    have hbBsome : b ∈ Bsome := (Finset.mem_filter.mp hb).1
    have hbB : b ∈ B := (Finset.mem_filter.mp hbBsome).1
    have hbzChoice : zChoice (α := α) X b.1.1 y h0 ≠ none := (Finset.mem_filter.mp hbBsome).2
    have hgb : g2 b = (z, (some u : Option α), (some v : Option α)) := (Finset.mem_filter.mp hb).2
    -- Show `y ∈ X \\ b` using the bucket-fixed signature (same pattern as other fiber lemmas).
    have hbFiber : b.1 ∈ fiber := (Finset.mem_filter.mp b.2).1
    have hcert_sub :
        ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
      (Finset.mem_filter.mp hbFiber).2
    have hcert_star :
        ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
      (Finset.mem_filter.mp hSstar).2
    have hne : b.1.1 ≠ Sstar.1 :=
      ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
        (Ssub := b.1) b.2
    let yCh : α :=
      chooseMissingFromRef (family := family) (h0 := h0) Sstar.1 b.1.1 Sstar.2 b.1.2 hne
    have hbSig : sigOut b = σOut := (Finset.mem_filter.mp hbB).2
    have hSig11 : (sigOut b).1.1 = σOut.1.1 :=
      congrArg (fun t : PerXSignatureOutMore α => t.1.1) hbSig
    have hySig : (sig0 b).1 = y := by
      simpa [sigOut, y] using hSig11
    have hyChSig0 : (sig0 b).1 = yCh := by
      unfold yCh
      simp only [sig0, perXSignature_of_hardFiber, perXSignature, chooseYAndWitness_of_hardFiber]
    have hyEq : yCh = y := hyChSig0.symm.trans hySig
    have hyXCh : yCh ∈ X := by
      have hyX' :
          yCh ∈ (ground \ (k.2.2.1 ∪ k.2.2.2.1)) := by
        simpa [yCh] using
          (chooseMissingFromRef_mem_X_of_hardFiber (family := family) (ground := ground) (A0 := A0)
            (h0 := h0) hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
            Sstar.2 b.1.2 hcert_star hcert_sub hne)
      simpa [X] using hyX'
    have hyNotCh : yCh ∉ b.1.1 := by
      have hyDiff :
          yCh ∈ Sstar.1 \ b.1.1 := by
        simpa [yCh] using
          (chooseMissingFromRef_spec (family := family) (h0 := h0) Sstar.1 b.1.1
            Sstar.2 b.1.2 hne)
      exact (Finset.mem_sdiff.mp hyDiff).2
    have hy : y ∈ X \ b.1.1 := by
      have : yCh ∈ X \ b.1.1 := Finset.mem_sdiff.mpr ⟨hyXCh, hyNotCh⟩
      simpa [hyEq] using this
    have hyNe : y ≠ h0 := by
      -- `yCh ∈ Sstar \\ b`, so `yCh ∈ Sstar`; but `h0 ∉ Sstar` since `Sstar ∈ coreSliceAvoid`.
      have hSstarDom : Sstar.1 ∈ o1aWitnessLiftDom family h0 := (Finset.mem_filter.mp Sstar.2).1
      have hSstarAvoid : h0 ∉ Sstar.1 := by
        have hSstarAvoid' : Sstar.1 ∈ coreSliceAvoid family h0 :=
          (Finset.mem_filter.mp hSstarDom).1
        exact (Finset.mem_filter.mp hSstarAvoid').2
      have hyMemSstar : yCh ∈ Sstar.1 := by
        have hyDiff :
            yCh ∈ Sstar.1 \ b.1.1 := by
          simpa [yCh] using
            (chooseMissingFromRef_spec (family := family) (h0 := h0) Sstar.1 b.1.1
              Sstar.2 b.1.2 hne)
        exact (Finset.mem_sdiff.mp hyDiff).1
      have : yCh ≠ h0 := by
        intro hEq
        have : h0 ∈ Sstar.1 := by
          simpa [hEq] using hyMemSstar
        exact hSstarAvoid this
      simpa [hyEq] using this
    -- Extract `zChoice = some z` and the `uPairGoodChoice` witness from `g₂ b = (z, some u, some v)`.
    cases hzOpt : zChoice (α := α) X b.1.1 y h0 with
    | none =>
        cases hbzChoice (by simp [hzOpt])
    | some z0 =>
        have hzEq0 : z0 = z := by
          have hfst1 : (g2 b).1 = z0 := by
            -- Expand `g₂ b` using `hzOpt`; the first coordinate is `z0` in every inner branch.
            cases hUG : uGoodChoice (α := α) X b.1.1 y h0 z0 with
            | some hu =>
                simp [g2, hzOpt, hUG]
            | none =>
                cases hUV : uPairGoodChoice (α := α) X b.1.1 y h0 z0 with
                | some huv =>
                    simp [g2, hzOpt, hUG, hUV]
                | none =>
                    simp [g2, hzOpt, hUG, hUV]
          have hfst2 : (g2 b).1 = z := by
            simpa using congrArg (fun t : α × Option α × Option α => t.1) hgb
          exact hfst1.symm.trans hfst2
        have hzEq : zChoice (α := α) X b.1.1 y h0 = some z := by
          simpa [hzEq0] using hzOpt
        -- Now force `uGoodChoice = none` and `uPairGoodChoice = some _`.
        cases hUGb : uGoodChoice (α := α) X b.1.1 y h0 z with
        | some hu =>
            -- `g₂ b` would have third coordinate `none`, contradiction.
            have : g2 b = (z, (some hu.1 : Option α), (none : Option α)) := by
              simp [g2, hzEq, hUGb]
            have := congrArg (fun t : α × Option α × Option α => t.2.2) (this.symm.trans hgb)
            simp at this
        | none =>
            cases huvEq : uPairGoodChoice (α := α) X b.1.1 y h0 z with
            | none =>
                -- `g₂ b` would be `(z, none, none)`, contradiction with `hgb`.
                have : g2 b = (z, (none : Option α), (none : Option α)) := by
                  simp [g2, hzEq, hUGb, huvEq]
                have := congrArg (fun t : α × Option α × Option α => t.2.1) (this.symm.trans hgb)
                simp at this
            | some huv =>
                -- Extract the membership facts and the empty-erase chain.
                have hg2' :
                    g2 b = (z, (some huv.1.1 : Option α), (some huv.1.2 : Option α)) := by
                  simp [g2, hzEq, hUGb, huvEq]
                let u0 : α := huv.1.1
                let v0 : α := huv.1.2
                have huEq : u0 = u := by
                  have := congrArg (fun t : α × Option α × Option α => t.2.1) (hg2'.symm.trans hgb)
                  simpa [u0] using this
                have hvEq : v0 = v := by
                  have := congrArg (fun t : α × Option α × Option α => t.2.2) (hg2'.symm.trans hgb)
                  simpa [v0] using this
                let Z2 : Finset α := ((((X \ b.1.1).erase y).erase h0).erase z)
                have huMem : u0 ∈ Z2 := by simpa [Z2, u0] using huv.2.1
                have hvMemZ2 : v0 ∈ Z2 := by simpa [Z2, v0] using huv.2.2.1
                have hvMem : v0 ∈ Z2.erase u0 := by
                  exact Finset.mem_erase.mpr ⟨huv.2.2.2.1.symm, hvMemZ2⟩
                have hZ4 : (Z2.erase u0).erase v0 = (∅ : Finset α) := by
                  simpa [Z2, u0, v0] using huv.2.2.2.2
                have hXs :
                    (X.erase h0) \ b.1.1 = ({y, z, u, v} : Finset α) := by
                  have hXs0 :
                      (X.erase h0) \ b.1.1 = ({y, z, u0, v0} : Finset α) :=
                    Xerase_h0_sdiff_eq_quad_of_mem_of_erase_u_erase_v_eq_empty (α := α)
                      (X := X) (S := b.1.1) (y0 := y) (h0 := h0) (z := z) (u := u0) (v := v0)
                      hy hyNe hzEq huMem hvMem hZ4
                  simpa [u0, v0, huEq, hvEq] using hXs0
                exact Finset.mem_filter.mpr ⟨hbB, hXs⟩
  have hcard_sub :
      (Bsome.filter (fun b => g2 b = (z, (some u : Option α), (some v : Option α)))).card ≤
        (B.filter (fun b => (X.erase h0) \ b.1.1 = ({y, z, u, v} : Finset α))).card :=
    Finset.card_le_card hsub
  have hcap :
      (B.filter (fun b => (X.erase h0) \ b.1.1 = ({y, z, u, v} : Finset α))).card ≤ 1 := by
    simpa [X] using
      (card_Bucket_perXSignatureOutMore_filter_Xerase_h0_sdiff_eq_quad_le_one (family := family)
        (ground := ground) (A0 := A0) (h0 := h0) hreg (k := k) (Sstar := Sstar) (x := x) hSstar
        (σOut := σOut) (y1 := y) (y2 := z) (y3 := u) (y4 := v))
  exact le_trans hcard_sub hcap

theorem card_Bsome_filter_g2_eq_mk_z_some_none_le_two
    (hreg : O1aUpgradeRegime family ground A0 h0)
    {k : WLcertKey α}
    {Sstar : {S // S ∈ o1aWitnessLiftDomWL family h0}}
    {x : α}
    (hSstar :
      Sstar ∈ wlcertAdmissibleFiber_hNotMem (family := family) (o1aWitnessLiftDomWL family h0) k)
    (σOut : PerXSignatureOutMore α)
    (z u : α) :
    let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h0
    let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
    let Fx0 :
        Finset {S // S ∈ dom} :=
      wlcertAdmissibleFiber_hNotMem_fiberForX (dom := dom) fiber Sstar.1 x
    let Uout : {Ssub // Ssub ∈ Fx0} → Finset α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      let yw :
          Σ y : α, BlockedUnionWitness family b.1.1 y :=
        chooseYAndWitness_of_hardFiber
          (family := family) (ground := ground) (A0 := A0) (h0 := h0)
          hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
          Sstar.2 b.1.2 hcert_star hcert_sub hne
      b.1.1 \ (yw.2.A ∪ yw.2.B)
    let sig0 : {Ssub // Ssub ∈ Fx0} → PerXSignature α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      perXSignature_of_hardFiber (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1) Sstar.2 b.1.2 hcert_star hcert_sub hne
    let sigOut : {Ssub // Ssub ∈ Fx0} → PerXSignatureOutMore α := fun b =>
      (sig0 b,
        trace5PlusOfFinset (α := α) (Uout b),
        t6OptionOfTrace5Plus (α := α) (Uout b))
    let X : Finset α := ground \ (k.2.2.1 ∪ k.2.2.2.1)
    let y : α := σOut.1.1
    let B : Finset {Ssub // Ssub ∈ Fx0} := Bucket (Fx := Fx0.attach) sigOut σOut
    let Bsome : Finset {Ssub // Ssub ∈ Fx0} :=
      B.filter (fun b => zChoice (α := α) X b.1.1 y h0 ≠ none)
    let g2 : {Ssub // Ssub ∈ Fx0} → α × Option α × Option α := by
      classical
      exact fun b =>
        match zChoice (α := α) X b.1.1 y h0 with
        | some z0 =>
            match uGoodChoice (α := α) X b.1.1 y h0 z0 with
            | some hu => (z0, some hu.1, none)
            | none =>
                match uPairGoodChoice (α := α) X b.1.1 y h0 z0 with
                | some huv => (z0, some huv.1.1, some huv.1.2)
                | none => (z0, none, none)
        | none => (h0, none, none)
    (Bsome.filter (fun b => g2 b = (z, (some u : Option α), (none : Option α)))).card ≤ 2 := by
  classical
  intro dom fiber Fx0 Uout sig0 sigOut X y B Bsome g2
  -- Reduce to the triple/quad missing-set buckets (no further missing beyond `u`).
  have hsub :
      (Bsome.filter (fun b => g2 b = (z, (some u : Option α), (none : Option α)))) ⊆
        (B.filter (fun b => X \ b.1.1 = ({y, z, u} : Finset α))) ∪
          (B.filter (fun b => X \ b.1.1 = ({y, h0, z, u} : Finset α))) := by
    intro b hb
    have hbBsome : b ∈ Bsome := (Finset.mem_filter.mp hb).1
    have hbB : b ∈ B := (Finset.mem_filter.mp hbBsome).1
    have hbzChoice : zChoice (α := α) X b.1.1 y h0 ≠ none := (Finset.mem_filter.mp hbBsome).2
    have hgb : g2 b = (z, (some u : Option α), (none : Option α)) := (Finset.mem_filter.mp hb).2
    -- Show `y ∈ X \\ b` using the bucket-fixed signature.
    have hbFiber : b.1 ∈ fiber := (Finset.mem_filter.mp b.2).1
    have hcert_sub :
        ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
      (Finset.mem_filter.mp hbFiber).2
    have hcert_star :
        ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
      (Finset.mem_filter.mp hSstar).2
    have hne : b.1.1 ≠ Sstar.1 :=
      ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
        (Ssub := b.1) b.2
    let yCh : α :=
      chooseMissingFromRef (family := family) (h0 := h0) Sstar.1 b.1.1 Sstar.2 b.1.2 hne
    have hbSig : sigOut b = σOut := (Finset.mem_filter.mp hbB).2
    have hSig11 : (sigOut b).1.1 = σOut.1.1 :=
      congrArg (fun t : PerXSignatureOutMore α => t.1.1) hbSig
    have hySig : (sig0 b).1 = y := by
      simpa [sigOut, y] using hSig11
    have hyChSig0 : (sig0 b).1 = yCh := by
      unfold yCh
      simp only [sig0, perXSignature_of_hardFiber, perXSignature, chooseYAndWitness_of_hardFiber]
    have hyEq : yCh = y := hyChSig0.symm.trans hySig
    have hyXCh : yCh ∈ X := by
      have hyX' :
          yCh ∈ (ground \ (k.2.2.1 ∪ k.2.2.2.1)) := by
        simpa [yCh] using
          (chooseMissingFromRef_mem_X_of_hardFiber (family := family) (ground := ground) (A0 := A0)
            (h0 := h0) hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
            Sstar.2 b.1.2 hcert_star hcert_sub hne)
      simpa [X] using hyX'
    have hyNotCh : yCh ∉ b.1.1 := by
      have hyDiff :
          yCh ∈ Sstar.1 \ b.1.1 := by
        simpa [yCh] using
          (chooseMissingFromRef_spec (family := family) (h0 := h0) Sstar.1 b.1.1
            Sstar.2 b.1.2 hne)
      exact (Finset.mem_sdiff.mp hyDiff).2
    have hy : y ∈ X \ b.1.1 := by
      have : yCh ∈ X \ b.1.1 := Finset.mem_sdiff.mpr ⟨hyXCh, hyNotCh⟩
      simpa [hyEq] using this
    -- Extract `zChoice = some z` and the `uGoodChoice` witness from `g₂ b = (z, some u, none)`.
    cases hzOpt : zChoice (α := α) X b.1.1 y h0 with
    | none =>
        cases hbzChoice (by simp [hzOpt])
    | some z0 =>
        have hzEq0 : z0 = z := by
          have hfst1 : (g2 b).1 = z0 := by
            cases hUG : uGoodChoice (α := α) X b.1.1 y h0 z0 with
            | some hu =>
                simp [g2, hzOpt, hUG]
            | none =>
                cases hUV : uPairGoodChoice (α := α) X b.1.1 y h0 z0 with
                | some huv =>
                    simp [g2, hzOpt, hUG, hUV]
                | none =>
                    simp [g2, hzOpt, hUG, hUV]
          have hfst2 : (g2 b).1 = z := by
            simpa using congrArg (fun t : α × Option α × Option α => t.1) hgb
          exact hfst1.symm.trans hfst2
        have hzEq : zChoice (α := α) X b.1.1 y h0 = some z := by
          simpa [hzEq0] using hzOpt
        cases hUGb : uGoodChoice (α := α) X b.1.1 y h0 z with
        | none =>
            -- Split on `uPairGoodChoice`; either way we contradict `g₂ b = (z, some u, none)`.
            cases huvEq : uPairGoodChoice (α := α) X b.1.1 y h0 z with
            | some huv =>
                have : g2 b = (z, (some huv.1.1 : Option α), (some huv.1.2 : Option α)) := by
                  simp [g2, hzEq, hUGb, huvEq]
                have :=
                  congrArg (fun t : α × Option α × Option α => t.2.2) (this.symm.trans hgb)
                simp at this
            | none =>
                have : g2 b = (z, (none : Option α), (none : Option α)) := by
                  simp [g2, hzEq, hUGb, huvEq]
                have :=
                  congrArg (fun t : α × Option α × Option α => t.2.1) (this.symm.trans hgb)
                simp at this
        | some hu =>
            -- Extract `u = hu.1` and the singleton-erase proof from `hu`.
            have hg2' : g2 b = (z, (some hu.1 : Option α), (none : Option α)) := by
              simp [g2, hzEq, hUGb]
            have huEq : hu.1 = u := by
              have := congrArg (fun t : α × Option α × Option α => t.2.1) (hg2'.symm.trans hgb)
              simpa using this
            let Z2 : Finset α := ((((X \ b.1.1).erase y).erase h0).erase z)
            have huMem : hu.1 ∈ Z2 := by simpa [Z2] using hu.2.1
            have hZ3 : Z2.erase hu.1 = (∅ : Finset α) := by simpa [Z2] using hu.2.2
            have hXs :
                X \ b.1.1 = ({y, z, u} : Finset α) ∨ X \ b.1.1 = ({y, h0, z, u} : Finset α) := by
              have hXs0 :
                  X \ b.1.1 = ({y, z, hu.1} : Finset α) ∨
                    X \ b.1.1 = ({y, h0, z, hu.1} : Finset α) :=
                X_sdiff_eq_triple_or_quad_of_mem_of_erase_u_eq_empty (α := α)
                  (X := X) (S := b.1.1) (y0 := y) (h0 := h0) (z := z) (u := hu.1)
                  hy hzEq huMem hZ3
              simpa [huEq] using hXs0
            rcases hXs with hTrip | hQuad
            · refine Finset.mem_union.mpr (Or.inl ?_)
              exact Finset.mem_filter.mpr ⟨hbB, hTrip⟩
            · refine Finset.mem_union.mpr (Or.inr ?_)
              exact Finset.mem_filter.mpr ⟨hbB, hQuad⟩
  have hcard_sub :
      (Bsome.filter (fun b => g2 b = (z, (some u : Option α), (none : Option α)))).card ≤
        ((B.filter (fun b => X \ b.1.1 = ({y, z, u} : Finset α))) ∪
              (B.filter (fun b => X \ b.1.1 = ({y, h0, z, u} : Finset α)))).card :=
    Finset.card_le_card hsub
  have hcard1 :
      (B.filter (fun b => X \ b.1.1 = ({y, z, u} : Finset α))).card ≤ 1 := by
    simpa [X] using
      (card_Bucket_perXSignatureOutMore_filter_X_sdiff_eq_triple_le_one (family := family)
        (ground := ground) (A0 := A0) (h0 := h0) hreg (k := k) (Sstar := Sstar) (x := x)
        hSstar (σOut := σOut) (y1 := y) (y2 := z) (y3 := u))
  have hcard2 :
      (B.filter (fun b => X \ b.1.1 = ({y, h0, z, u} : Finset α))).card ≤ 1 := by
    simpa [X] using
      (card_Bucket_perXSignatureOutMore_filter_X_sdiff_eq_quad_le_one (family := family)
        (ground := ground) (A0 := A0) (h0 := h0) hreg (k := k) (Sstar := Sstar) (x := x)
        hSstar (σOut := σOut) (y1 := y) (y2 := h0) (y3 := z) (y4 := u))
  have hcard_union :
      ((B.filter (fun b => X \ b.1.1 = ({y, z, u} : Finset α))) ∪
            (B.filter (fun b => X \ b.1.1 = ({y, h0, z, u} : Finset α)))).card ≤ 2 := by
    have hsum :
        ((B.filter (fun b => X \ b.1.1 = ({y, z, u} : Finset α))) ∪
              (B.filter (fun b => X \ b.1.1 = ({y, h0, z, u} : Finset α)))).card ≤
          (B.filter (fun b => X \ b.1.1 = ({y, z, u} : Finset α))).card +
            (B.filter (fun b => X \ b.1.1 = ({y, h0, z, u} : Finset α))).card := by
      simpa using
        (Finset.card_union_le
          (B.filter (fun b => X \ b.1.1 = ({y, z, u} : Finset α)))
          (B.filter (fun b => X \ b.1.1 = ({y, h0, z, u} : Finset α))))
    calc
      ((B.filter (fun b => X \ b.1.1 = ({y, z, u} : Finset α))) ∪
              (B.filter (fun b => X \ b.1.1 = ({y, h0, z, u} : Finset α)))).card
          ≤ (B.filter (fun b => X \ b.1.1 = ({y, z, u} : Finset α))).card +
              (B.filter (fun b => X \ b.1.1 = ({y, h0, z, u} : Finset α))).card := hsum
      _ ≤ 1 + 1 := Nat.add_le_add hcard1 hcard2
      _ = 2 := by simp
  exact le_trans hcard_sub hcard_union

theorem card_Bsome_filter_g2_eq_mk_z_none_none_Z2_empty_le_two
    (hreg : O1aUpgradeRegime family ground A0 h0)
    {k : WLcertKey α}
    {Sstar : {S // S ∈ o1aWitnessLiftDomWL family h0}}
    {x : α}
    (hSstar :
      Sstar ∈ wlcertAdmissibleFiber_hNotMem (family := family) (o1aWitnessLiftDomWL family h0) k)
    (σOut : PerXSignatureOutMore α)
    (z : α) :
    let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h0
    let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
    let Fx0 :
        Finset {S // S ∈ dom} :=
      wlcertAdmissibleFiber_hNotMem_fiberForX (dom := dom) fiber Sstar.1 x
    let Uout : {Ssub // Ssub ∈ Fx0} → Finset α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      let yw :
          Σ y : α, BlockedUnionWitness family b.1.1 y :=
        chooseYAndWitness_of_hardFiber
          (family := family) (ground := ground) (A0 := A0) (h0 := h0)
          hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
          Sstar.2 b.1.2 hcert_star hcert_sub hne
      b.1.1 \ (yw.2.A ∪ yw.2.B)
    let sig0 : {Ssub // Ssub ∈ Fx0} → PerXSignature α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      perXSignature_of_hardFiber (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1) Sstar.2 b.1.2 hcert_star hcert_sub hne
    let sigOut : {Ssub // Ssub ∈ Fx0} → PerXSignatureOutMore α := fun b =>
      (sig0 b,
        trace5PlusOfFinset (α := α) (Uout b),
        t6OptionOfTrace5Plus (α := α) (Uout b))
    let X : Finset α := ground \ (k.2.2.1 ∪ k.2.2.2.1)
    let y : α := σOut.1.1
    let B : Finset {Ssub // Ssub ∈ Fx0} := Bucket (Fx := Fx0.attach) sigOut σOut
    let Bsome : Finset {Ssub // Ssub ∈ Fx0} :=
      B.filter (fun b => zChoice (α := α) X b.1.1 y h0 ≠ none)
    let g2 : {Ssub // Ssub ∈ Fx0} → α × Option α × Option α := by
      classical
      exact fun b =>
        match zChoice (α := α) X b.1.1 y h0 with
        | some z0 =>
            match uGoodChoice (α := α) X b.1.1 y h0 z0 with
            | some hu => (z0, some hu.1, none)
            | none =>
                match uPairGoodChoice (α := α) X b.1.1 y h0 z0 with
                | some huv => (z0, some huv.1.1, some huv.1.2)
                | none => (z0, none, none)
        | none => (h0, none, none)
    (Bsome.filter (fun b =>
          g2 b = (z, (none : Option α), (none : Option α)) ∧
            ((((X \ b.1.1).erase y).erase h0).erase z) = (∅ : Finset α))).card ≤ 2 := by
  classical
  intro dom fiber Fx0 Uout sig0 sigOut X y B Bsome g2
  -- Reduce to the sharp pair/triple missing-set buckets.
  have hsub :
      (Bsome.filter (fun b =>
            g2 b = (z, (none : Option α), (none : Option α)) ∧
              ((((X \ b.1.1).erase y).erase h0).erase z) = (∅ : Finset α))) ⊆
        (B.filter (fun b => X \ b.1.1 = ({y, z} : Finset α))) ∪
          (B.filter (fun b => X \ b.1.1 = ({y, h0, z} : Finset α))) := by
    intro b hb
    have hbBsome : b ∈ Bsome := (Finset.mem_filter.mp hb).1
    have hbB : b ∈ B := (Finset.mem_filter.mp hbBsome).1
    have hbzChoice : zChoice (α := α) X b.1.1 y h0 ≠ none := (Finset.mem_filter.mp hbBsome).2
    have hgb : g2 b = (z, (none : Option α), (none : Option α)) := (Finset.mem_filter.mp hb).2.1
    have hZ2 : ((((X \ b.1.1).erase y).erase h0).erase z) = (∅ : Finset α) :=
      (Finset.mem_filter.mp hb).2.2
    have huNone : uChoice (α := α) X b.1.1 y h0 z = none := by
      exact (uChoice_eq_none_iff (α := α) (X := X) (S := b.1.1) (y0 := y) (h0 := h0) (z := z)).2 hZ2
    -- Show `y ∈ X \\ b` using the bucket-fixed signature (same pattern as other fiber lemmas).
    have hbFiber : b.1 ∈ fiber := (Finset.mem_filter.mp b.2).1
    have hcert_sub :
        ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
      (Finset.mem_filter.mp hbFiber).2
    have hcert_star :
        ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
      (Finset.mem_filter.mp hSstar).2
    have hne : b.1.1 ≠ Sstar.1 :=
      ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
        (Ssub := b.1) b.2
    let yCh : α :=
      chooseMissingFromRef (family := family) (h0 := h0) Sstar.1 b.1.1 Sstar.2 b.1.2 hne
    have hbSig : sigOut b = σOut := (Finset.mem_filter.mp hbB).2
    have hSig11 : (sigOut b).1.1 = σOut.1.1 :=
      congrArg (fun t : PerXSignatureOutMore α => t.1.1) hbSig
    have hySig : (sig0 b).1 = y := by
      simpa [sigOut, y] using hSig11
    have hyChSig0 : (sig0 b).1 = yCh := by
      unfold yCh
      simp only [sig0, perXSignature_of_hardFiber, perXSignature, chooseYAndWitness_of_hardFiber]
    have hyEq : yCh = y := hyChSig0.symm.trans hySig
    have hyXCh : yCh ∈ X := by
      have hyX' :
          yCh ∈ (ground \ (k.2.2.1 ∪ k.2.2.2.1)) := by
        simpa [yCh] using
          (chooseMissingFromRef_mem_X_of_hardFiber (family := family) (ground := ground) (A0 := A0)
            (h0 := h0) hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
            Sstar.2 b.1.2 hcert_star hcert_sub hne)
      simpa [X] using hyX'
    have hyNotCh : yCh ∉ b.1.1 := by
      have hyDiff :
          yCh ∈ Sstar.1 \ b.1.1 := by
        simpa [yCh] using
          (chooseMissingFromRef_spec (family := family) (h0 := h0) Sstar.1 b.1.1
            Sstar.2 b.1.2 hne)
      exact (Finset.mem_sdiff.mp hyDiff).2
    have hy : y ∈ X \ b.1.1 := by
      have : yCh ∈ X \ b.1.1 := Finset.mem_sdiff.mpr ⟨hyXCh, hyNotCh⟩
      simpa [hyEq] using this
    -- Extract `zChoice = some z` from `g₂ b = (z, none, none)`.
    cases hzOpt : zChoice (α := α) X b.1.1 y h0 with
    | none =>
        cases hbzChoice (by simp [hzOpt])
    | some z0 =>
        have hzEq0 : z0 = z := by
          have hfst1 : (g2 b).1 = z0 := by
            cases hUG : uGoodChoice (α := α) X b.1.1 y h0 z0 with
            | some hu =>
                simp [g2, hzOpt, hUG]
            | none =>
                cases hUV : uPairGoodChoice (α := α) X b.1.1 y h0 z0 with
                | some huv =>
                    simp [g2, hzOpt, hUG, hUV]
                | none =>
                    simp [g2, hzOpt, hUG, hUV]
          have hfst2 : (g2 b).1 = z := by
            simpa using congrArg (fun t : α × Option α × Option α => t.1) hgb
          exact hfst1.symm.trans hfst2
        have hzEq : zChoice (α := α) X b.1.1 y h0 = some z := by
          simpa [hzEq0] using hzOpt
        have hXcase :
            X \ b.1.1 = ({y, z} : Finset α) ∨ X \ b.1.1 = ({y, h0, z} : Finset α) :=
          X_sdiff_eq_pair_or_triple_of_uChoice_eq_none (α := α) (X := X) (S := b.1.1)
            (y0 := y) (h0 := h0) (z := z) hy hzEq huNone
        rcases hXcase with hPair | hTrip
        · refine Finset.mem_union.mpr (Or.inl ?_)
          exact Finset.mem_filter.mpr ⟨hbB, hPair⟩
        · refine Finset.mem_union.mpr (Or.inr ?_)
          exact Finset.mem_filter.mpr ⟨hbB, hTrip⟩
  have hcard_sub :
      (Bsome.filter (fun b =>
            g2 b = (z, (none : Option α), (none : Option α)) ∧
              ((((X \ b.1.1).erase y).erase h0).erase z) = (∅ : Finset α))).card ≤
        ((B.filter (fun b => X \ b.1.1 = ({y, z} : Finset α))) ∪
              (B.filter (fun b => X \ b.1.1 = ({y, h0, z} : Finset α)))).card :=
    Finset.card_le_card hsub
  have hcard1 :
      (B.filter (fun b => X \ b.1.1 = ({y, z} : Finset α))).card ≤ 1 := by
    simpa [X] using
      (card_Bucket_perXSignatureOutMore_filter_X_sdiff_eq_pair_le_one (family := family)
        (ground := ground) (A0 := A0) (h0 := h0) hreg (k := k) (Sstar := Sstar) (x := x)
        hSstar (σOut := σOut) (y1 := y) (y2 := z))
  have hcard2 :
      (B.filter (fun b => X \ b.1.1 = ({y, h0, z} : Finset α))).card ≤ 1 := by
    simpa [X] using
      (card_Bucket_perXSignatureOutMore_filter_X_sdiff_eq_triple_le_one (family := family)
        (ground := ground) (A0 := A0) (h0 := h0) hreg (k := k) (Sstar := Sstar) (x := x)
        hSstar (σOut := σOut) (y1 := y) (y2 := h0) (y3 := z))
  have hcard_union :
      ((B.filter (fun b => X \ b.1.1 = ({y, z} : Finset α))) ∪
            (B.filter (fun b => X \ b.1.1 = ({y, h0, z} : Finset α)))).card ≤ 2 := by
    have hsum :
        ((B.filter (fun b => X \ b.1.1 = ({y, z} : Finset α))) ∪
              (B.filter (fun b => X \ b.1.1 = ({y, h0, z} : Finset α)))).card ≤
          (B.filter (fun b => X \ b.1.1 = ({y, z} : Finset α))).card +
            (B.filter (fun b => X \ b.1.1 = ({y, h0, z} : Finset α))).card := by
      simpa using
        (Finset.card_union_le
          (B.filter (fun b => X \ b.1.1 = ({y, z} : Finset α)))
          (B.filter (fun b => X \ b.1.1 = ({y, h0, z} : Finset α))))
    calc
      ((B.filter (fun b => X \ b.1.1 = ({y, z} : Finset α))) ∪
              (B.filter (fun b => X \ b.1.1 = ({y, h0, z} : Finset α)))).card
          ≤ (B.filter (fun b => X \ b.1.1 = ({y, z} : Finset α))).card +
              (B.filter (fun b => X \ b.1.1 = ({y, h0, z} : Finset α))).card := hsum
      _ ≤ 1 + 1 := Nat.add_le_add hcard1 hcard2
      _ = 2 := by simp
  exact le_trans hcard_sub hcard_union

/-!
Residual isolation for the remaining outMore contract gap (bad-none).

We currently have sharp fiber caps for all `g₂`-values **except** the case
`g₂ b = (z, none, none)` with a nonempty triple-erase set
`Z2 := ((((X \\ S).erase y).erase h0).erase z)`.

Rather than thrashing on that seam, we isolate it as a named residual finset
`BadNone` and prove a clean split bound:

`Bsome.card ≤ 2 * n * (n+1)^2 + BadNone.card`.

The later contract-gap obligation is to show `BadNone.card = 0` (or otherwise
bound it) under the intended regime.
-/

set_option maxHeartbeats 1000000 in
theorem card_Bucket_perXSignatureOutMore_filter_zChoice_ne_none_le_two_mul_n_mul_succ_mul_succ_add_badNone
    (hreg : O1aUpgradeRegime family ground A0 h0)
    {k : WLcertKey α}
    {Sstar : {S // S ∈ o1aWitnessLiftDomWL family h0}}
    {x : α}
    (hSstar :
      Sstar ∈ wlcertAdmissibleFiber_hNotMem (family := family) (o1aWitnessLiftDomWL family h0) k)
    (σOut : PerXSignatureOutMore α) :
    let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h0
    let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
    let Fx0 :
        Finset {S // S ∈ dom} :=
      wlcertAdmissibleFiber_hNotMem_fiberForX (dom := dom) fiber Sstar.1 x
    let Uout : {Ssub // Ssub ∈ Fx0} → Finset α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      let yw :
          Σ y : α, BlockedUnionWitness family b.1.1 y :=
        chooseYAndWitness_of_hardFiber
          (family := family) (ground := ground) (A0 := A0) (h0 := h0)
          hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
          Sstar.2 b.1.2 hcert_star hcert_sub hne
      b.1.1 \ (yw.2.A ∪ yw.2.B)
    let sig0 : {Ssub // Ssub ∈ Fx0} → PerXSignature α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      perXSignature_of_hardFiber (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1) Sstar.2 b.1.2 hcert_star hcert_sub hne
    let sigOut : {Ssub // Ssub ∈ Fx0} → PerXSignatureOutMore α := fun b =>
      (sig0 b,
        trace5PlusOfFinset (α := α) (Uout b),
        t6OptionOfTrace5Plus (α := α) (Uout b))
    let X : Finset α := ground \ (k.2.2.1 ∪ k.2.2.2.1)
    let y : α := σOut.1.1
    let B : Finset {Ssub // Ssub ∈ Fx0} := Bucket (Fx := Fx0.attach) sigOut σOut
    let Bsome : Finset {Ssub // Ssub ∈ Fx0} :=
      B.filter (fun b => zChoice (α := α) X b.1.1 y h0 ≠ none)
    let g2 : {Ssub // Ssub ∈ Fx0} → α × Option α × Option α := by
      classical
      exact fun b =>
        match zChoice (α := α) X b.1.1 y h0 with
        | some z =>
            match uGoodChoice (α := α) X b.1.1 y h0 z with
            | some hu => (z, some hu.1, none)
            | none =>
                match uPairGoodChoice (α := α) X b.1.1 y h0 z with
                | some huv => (z, some huv.1.1, some huv.1.2)
                | none => (z, none, none)
        | none => (h0, none, none)
    let BadNone : Finset {Ssub // Ssub ∈ Fx0} :=
      Bsome.filter (fun b =>
        (g2 b).2.1 = none ∧ (g2 b).2.2 = none ∧
          ((((X \ b.1.1).erase y).erase h0).erase (g2 b).1).Nonempty)
    Bsome.card ≤ 2 * ground.card * (ground.card + 1) * (ground.card + 1) + BadNone.card := by
  classical
  intro dom fiber Fx0 Uout sig0 sigOut X y B Bsome g2 BadNone
  -- Predicate defining the residual (bad-none) subbucket.
  let PBad : {Ssub // Ssub ∈ Fx0} → Prop := fun b =>
    (g2 b).2.1 = none ∧ (g2 b).2.2 = none ∧
      ((((X \ b.1.1).erase y).erase h0).erase (g2 b).1).Nonempty
  have hBad : BadNone = Bsome.filter PBad := by
    rfl
  let Good : Finset {Ssub // Ssub ∈ Fx0} := Bsome.filter (fun b => ¬ PBad b)
  have hUnion : Good ∪ BadNone = Bsome := by
    ext b
    by_cases hb : PBad b <;> simp [Good, hBad, hb]
  have hDisj : Disjoint Good BadNone := by
    refine Finset.disjoint_left.2 ?_
    intro b hbG hbB
    have hP : PBad b := (Finset.mem_filter.mp (by simpa [hBad] using hbB)).2
    have hnP : ¬ PBad b := (Finset.mem_filter.mp hbG).2
    exact hnP hP
  have hcard_split : Bsome.card = Good.card + BadNone.card := by
    have hcardU : (Good ∪ BadNone).card = Good.card + BadNone.card :=
      Finset.card_union_of_disjoint hDisj
    simpa [hUnion] using hcardU
  -- Bound the good part by the standard `g₂` image-size ledger and the existing fiber caps.
  have hGood :
      Good.card ≤ 2 * ground.card * (ground.card + 1) * (ground.card + 1) := by
    -- Fiber decomposition over the image of `g₂` on `Good`.
    have hsum :
        Good.card =
          ∑ p ∈ Good.image g2, (Good.filter (fun b => g2 b = p)).card := by
      simpa using (Finset.card_eq_sum_card_image (f := g2) (s := Good))
    -- Fiber cap: all fibers inside `Good` have card ≤ 2.
    have hFib :
        ∀ p ∈ Good.image g2, (Good.filter (fun b => g2 b = p)).card ≤ 2 := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨b, hbGood, rfl⟩
      have hbBsome : b ∈ Bsome := (Finset.mem_filter.mp hbGood).1
      -- Case split on the shape of `g₂ b`.
      rcases hg2 : g2 b with ⟨z0, ou0, ov0⟩
      cases ou0 with
      | none =>
          cases ov0 with
          | none =>
              -- Here `g₂ b = (z0, none, none)`; in `Good`, this forces the triple-erase set to be empty.
              have hnotBad : ¬ PBad b := (Finset.mem_filter.mp hbGood).2
              have hZ2empty :
                  ((((X \ b.1.1).erase y).erase h0).erase z0) = (∅ : Finset α) := by
                -- If the triple-erase were nonempty, we'd be in `BadNone`.
                have : ¬ ((((X \ b.1.1).erase y).erase h0).erase z0).Nonempty := by
                  intro hne
                  apply hnotBad
                  -- Assemble `PBad b` explicitly from `hg2`.
                  have h1 : (g2 b).2.1 = (none : Option α) := by
                    simpa using congrArg (fun t : α × Option α × Option α => t.2.1) hg2
                  have h2 : (g2 b).2.2 = (none : Option α) := by
                    simpa using congrArg (fun t : α × Option α × Option α => t.2.2) hg2
                  have hz : (g2 b).1 = z0 := by
                    simpa using congrArg (fun t : α × Option α × Option α => t.1) hg2
                  have hne' :
                      ((((X \ b.1.1).erase y).erase h0).erase (g2 b).1).Nonempty := by
                    simpa [hz] using hne
                  exact ⟨h1, h2, hne'⟩
                -- Convert `¬Nonempty` to `= ∅`.
                by_contra hne
                exact this ((Finset.nonempty_iff_ne_empty).2 hne)
              -- Reduce to the `Z2 = ∅` fiber cap lemma on `Bsome`.
              have hsub :
                  (Good.filter (fun b => g2 b = (z0, (none : Option α), (none : Option α)))) ⊆
                    (Bsome.filter (fun b =>
                        g2 b = (z0, (none : Option α), (none : Option α)) ∧
                          ((((X \ b.1.1).erase y).erase h0).erase z0) = (∅ : Finset α))) := by
                intro b' hb'
                have hb'Good : b' ∈ Good := (Finset.mem_filter.mp hb').1
                have hb'Bsome : b' ∈ Bsome := (Finset.mem_filter.mp hb'Good).1
                have hb'g2 : g2 b' = (z0, (none : Option α), (none : Option α)) :=
                  (Finset.mem_filter.mp hb').2
                -- As above: in `Good`, `Z2` must be empty.
                have hnotBad' : ¬ PBad b' := (Finset.mem_filter.mp hb'Good).2
                have hZ2empty' :
                    ((((X \ b'.1.1).erase y).erase h0).erase z0) = (∅ : Finset α) := by
                  have : ¬ ((((X \ b'.1.1).erase y).erase h0).erase z0).Nonempty := by
                    intro hne
                    apply hnotBad'
                    -- `g₂ b'` has both options `none`.
                    have hopt :
                        (g2 b').2.1 = (none : Option α) ∧ (g2 b').2.2 = (none : Option α) := by
                      -- read from `hb'g2`
                      have h1 :
                          (g2 b').2.1 = (none : Option α) := by
                        simpa using congrArg (fun t : α × Option α × Option α => t.2.1) hb'g2
                      have h2 :
                          (g2 b').2.2 = (none : Option α) := by
                        simpa using congrArg (fun t : α × Option α × Option α => t.2.2) hb'g2
                      exact ⟨h1, h2⟩
                    -- and `g₂ b'` has first coordinate `z0`
                    have hz' : (g2 b').1 = z0 := by
                      simpa using congrArg (fun t : α × Option α × Option α => t.1) hb'g2
                    -- assemble `PBad b'`
                    -- (rewrite the `erase (g2 b').1` with `z0` using `hz'`)
                    have hne' :
                        ((((X \ b'.1.1).erase y).erase h0).erase (g2 b').1).Nonempty := by
                      simpa [hz'] using hne
                    exact ⟨hopt.1, hopt.2, hne'⟩
                  by_contra hne'
                  exact this ((Finset.nonempty_iff_ne_empty).2 hne')
                exact
                  Finset.mem_filter.mpr ⟨hb'Bsome, And.intro hb'g2 hZ2empty'⟩
              have hcard_sub :
                  (Good.filter (fun b => g2 b = (z0, (none : Option α), (none : Option α)))).card ≤
                    (Bsome.filter (fun b =>
                        g2 b = (z0, (none : Option α), (none : Option α)) ∧
                          ((((X \ b.1.1).erase y).erase h0).erase z0) = (∅ : Finset α))).card :=
                Finset.card_le_card hsub
              -- Apply the existing cap (≤2) and then `≤` by transitivity.
              have hcap :
                  (Bsome.filter (fun b =>
                        g2 b = (z0, (none : Option α), (none : Option α)) ∧
                          ((((X \ b.1.1).erase y).erase h0).erase z0) = (∅ : Finset α))).card ≤ 2 :=
                card_Bsome_filter_g2_eq_mk_z_none_none_Z2_empty_le_two
                  (family := family) (ground := ground) (A0 := A0) (h0 := h0)
                  hreg (k := k) (Sstar := Sstar) (x := x) hSstar σOut z0
              exact le_trans hcard_sub hcap
          | some v0 =>
              -- Impossible: `g₂ b` can't have `uOpt = none` and `vOpt = some _` by definition.
              -- But we can bound the fiber by `2` trivially.
              have hEmptyCard :
                  (Good.filter (fun b => g2 b = (z0, (none : Option α), (some v0 : Option α)))).card = 0 := by
                apply (Finset.card_eq_zero).2
                -- Show the filter is empty: `g₂` never produces the shape `(z0, none, some v0)`.
                apply Finset.filter_eq_empty_iff.2
                intro b' hb' hg
                -- Unfold `g₂ b'` by cases; in all cases we contradict the `none/some` mismatch.
                cases hz : zChoice (α := α) X b'.1.1 y h0 with
                | none =>
                    have : (none : Option α) = (some v0 : Option α) := by
                      simpa [g2, hz] using
                        congrArg (fun t : α × Option α × Option α => t.2.2) hg
                    cases this
                | some z =>
                    cases hUG : uGoodChoice (α := α) X b'.1.1 y h0 z with
                    | some hu =>
                        have : (none : Option α) = (some v0 : Option α) := by
                          simpa [g2, hz, hUG] using
                            congrArg (fun t : α × Option α × Option α => t.2.2) hg
                        cases this
                    | none =>
                        cases hUV : uPairGoodChoice (α := α) X b'.1.1 y h0 z with
                        | some huv =>
                            have : (some huv.1.1 : Option α) = (none : Option α) := by
                              simpa [g2, hz, hUG, hUV] using
                                congrArg (fun t : α × Option α × Option α => t.2.1) hg
                            cases this
                        | none =>
                            have : (none : Option α) = (some v0 : Option α) := by
                              simpa [g2, hz, hUG, hUV] using
                                congrArg (fun t : α × Option α × Option α => t.2.2) hg
                            cases this
              -- Now `0 ≤ 2` gives the desired fiber cap.
              have : (Good.filter (fun b => g2 b = (z0, (none : Option α), (some v0 : Option α)))).card ≤ 2 := by
                rw [hEmptyCard]
                exact Nat.zero_le 2
              exact this
      | some u0 =>
          cases ov0 with
          | none =>
              -- Apply the `(z, some u, none)` cap (≤2) via subset.
              have hsub :
                  (Good.filter (fun b => g2 b = (z0, (some u0 : Option α), (none : Option α)))) ⊆
                    (Bsome.filter (fun b => g2 b = (z0, (some u0 : Option α), (none : Option α)))) := by
                intro b' hb'
                have hb'Good : b' ∈ Good := (Finset.mem_filter.mp hb').1
                have hb'Bsome : b' ∈ Bsome := (Finset.mem_filter.mp hb'Good).1
                exact Finset.mem_filter.mpr ⟨hb'Bsome, (Finset.mem_filter.mp hb').2⟩
              have hcard_sub :
                  (Good.filter (fun b => g2 b = (z0, (some u0 : Option α), (none : Option α)))).card ≤
                    (Bsome.filter (fun b => g2 b = (z0, (some u0 : Option α), (none : Option α)))).card :=
                Finset.card_le_card hsub
              have hcap :
                  (Bsome.filter (fun b => g2 b = (z0, (some u0 : Option α), (none : Option α)))).card ≤ 2 :=
                card_Bsome_filter_g2_eq_mk_z_some_none_le_two
                  (family := family) (ground := ground) (A0 := A0) (h0 := h0)
                  hreg (k := k) (Sstar := Sstar) (x := x) hSstar σOut z0 u0
              exact le_trans hcard_sub hcap
          | some v0 =>
              -- Apply the `(z, some u, some v)` cap (≤1 ≤2) via subset.
              have hsub :
                  (Good.filter (fun b => g2 b = (z0, (some u0 : Option α), (some v0 : Option α)))) ⊆
                    (Bsome.filter (fun b => g2 b = (z0, (some u0 : Option α), (some v0 : Option α)))) := by
                intro b' hb'
                have hb'Good : b' ∈ Good := (Finset.mem_filter.mp hb').1
                have hb'Bsome : b' ∈ Bsome := (Finset.mem_filter.mp hb'Good).1
                exact Finset.mem_filter.mpr ⟨hb'Bsome, (Finset.mem_filter.mp hb').2⟩
              have hcard_sub :
                  (Good.filter (fun b => g2 b = (z0, (some u0 : Option α), (some v0 : Option α)))).card ≤
                    (Bsome.filter (fun b => g2 b = (z0, (some u0 : Option α), (some v0 : Option α)))).card :=
                Finset.card_le_card hsub
              have hcap1 :
                  (Bsome.filter (fun b => g2 b = (z0, (some u0 : Option α), (some v0 : Option α)))).card ≤ 1 :=
                card_Bsome_filter_g2_eq_mk_z_some_some_le_one
                  (family := family) (ground := ground) (A0 := A0) (h0 := h0)
                  hreg (k := k) (Sstar := Sstar) (x := x) hSstar σOut z0 u0 v0
              have hcap : (Bsome.filter (fun b => g2 b = (z0, (some u0 : Option α), (some v0 : Option α)))).card ≤ 2 :=
                le_trans hcap1 (by decide)
              exact le_trans hcard_sub hcap
    -- Now sum over fibers and apply the image-size ledger.
    have hsum_le :
        (∑ p ∈ Good.image g2, (Good.filter (fun b => g2 b = p)).card) ≤
          ∑ _p ∈ Good.image g2, 2 := by
      refine Finset.sum_le_sum ?_
      intro p hp
      exact hFib p hp
    have hconst :
        (∑ _p ∈ Good.image g2, 2) = 2 * (Good.image g2).card := by
      simp [Nat.mul_comm]
    let Cod2 : Finset (α × (Option α × Option α)) :=
      ground.product
        ((optionOfFinset (α := α) ground).product (optionOfFinset (α := α) ground))
    have hXsub : X ⊆ ground := by
      intro a ha
      exact (Finset.mem_sdiff.mp ha).1
    have hnoneOpt :
        (none : Option α) ∈ optionOfFinset (α := α) ground :=
      (mem_optionOfFinset_iff (α := α) (T := ground) (o := (none : Option α))).2 (Or.inl rfl)
    have hsomeOpt :
        ∀ t : α, t ∈ ground → (some t : Option α) ∈ optionOfFinset (α := α) ground := by
      intro t ht
      exact
        (mem_optionOfFinset_iff (α := α) (T := ground) (o := (some t : Option α))).2
          (Or.inr ⟨t, ht, rfl⟩)
    -- Bound the image size by the product ledger.
    have himg_sub :
        Good.image g2 ⊆ Cod2 := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨b, hbGood, rfl⟩
      have hbBsome : b ∈ Bsome := (Finset.mem_filter.mp hbGood).1
      have hbz : zChoice (α := α) X b.1.1 y h0 ≠ none := (Finset.mem_filter.mp hbBsome).2
      cases hzOpt : zChoice (α := α) X b.1.1 y h0 with
      | none =>
          cases hbz (by simp [hzOpt])
      | some z0 =>
          have hzEq : zChoice (α := α) X b.1.1 y h0 = some z0 := hzOpt
          have hzXS : z0 ∈ X \ b.1.1 := zChoice_mem_X_sdiff (α := α) (X := X) (S := b.1.1) hzEq
          have hzX : z0 ∈ X := (Finset.mem_sdiff.mp hzXS).1
          have hzG : z0 ∈ ground := hXsub hzX
          -- Show both option components lie in `optionOfFinset ground`.
          cases hUG : uGoodChoice (α := α) X b.1.1 y h0 z0 with
          | some hu =>
              have huMem : hu.1 ∈ ((((X \ b.1.1).erase y).erase h0).erase z0) := hu.2.1
              have huErase2 : hu.1 ∈ ((X \ b.1.1).erase y).erase h0 := (Finset.mem_erase.mp huMem).2
              have huErase1 : hu.1 ∈ (X \ b.1.1).erase y := (Finset.mem_erase.mp huErase2).2
              have huXS : hu.1 ∈ X \ b.1.1 := (Finset.mem_erase.mp huErase1).2
              have huX : hu.1 ∈ X := (Finset.mem_sdiff.mp huXS).1
              have huGnd : hu.1 ∈ ground := hXsub huX
              have hsome :
                  (some hu.1 : Option α) ∈ optionOfFinset (α := α) ground :=
                hsomeOpt hu.1 huGnd
              have hpair :
                  (some hu.1, (none : Option α)) ∈
                    (optionOfFinset (α := α) ground).product (optionOfFinset (α := α) ground) :=
                Finset.mem_product.mpr ⟨hsome, hnoneOpt⟩
              have hmem :
                  (z0, (some hu.1 : Option α), (none : Option α)) ∈
                    Cod2 :=
                (Finset.mem_product (s := ground)
                  (t :=
                    (optionOfFinset (α := α) ground).product (optionOfFinset (α := α) ground))).2
                  ⟨hzG, hpair⟩
              have hg2 : g2 b = (z0, (some hu.1 : Option α), (none : Option α)) := by
                simp [g2, hzOpt, hUG]
              exact hg2 ▸ hmem
          | none =>
              cases hUV : uPairGoodChoice (α := α) X b.1.1 y h0 z0 with
              | some huv =>
                  let Z2 : Finset α := ((((X \ b.1.1).erase y).erase h0).erase z0)
                  let u : α := huv.1.1
                  let v : α := huv.1.2
                  have huMem : u ∈ Z2 := by
                    simpa [Z2, u] using huv.2.1
                  have hvMem : v ∈ Z2 := by
                    simpa [Z2, v] using huv.2.2.1
                  have huXS : u ∈ X \ b.1.1 := by
                    have huErase2 : u ∈ ((X \ b.1.1).erase y).erase h0 :=
                      (Finset.mem_erase.mp huMem).2
                    have huErase1 : u ∈ (X \ b.1.1).erase y := (Finset.mem_erase.mp huErase2).2
                    exact (Finset.mem_erase.mp huErase1).2
                  have hvXS : v ∈ X \ b.1.1 := by
                    have hvErase2 : v ∈ ((X \ b.1.1).erase y).erase h0 :=
                      (Finset.mem_erase.mp hvMem).2
                    have hvErase1 : v ∈ (X \ b.1.1).erase y := (Finset.mem_erase.mp hvErase2).2
                    exact (Finset.mem_erase.mp hvErase1).2
                  have huX : u ∈ X := (Finset.mem_sdiff.mp huXS).1
                  have hvX : v ∈ X := (Finset.mem_sdiff.mp hvXS).1
                  have huGnd : u ∈ ground := hXsub huX
                  have hvGnd : v ∈ ground := hXsub hvX
                  have hsomeu :
                      (some u : Option α) ∈ optionOfFinset (α := α) ground :=
                    hsomeOpt u huGnd
                  have hsomev :
                      (some v : Option α) ∈ optionOfFinset (α := α) ground :=
                    hsomeOpt v hvGnd
                  have hpair :
                      (some u, (some v : Option α)) ∈
                        (optionOfFinset (α := α) ground).product (optionOfFinset (α := α) ground) :=
                    Finset.mem_product.mpr ⟨hsomeu, hsomev⟩
                  have hmem :
                      (z0, (some u : Option α), (some v : Option α)) ∈
                        Cod2 :=
                    (Finset.mem_product (s := ground)
                      (t :=
                        (optionOfFinset (α := α) ground).product
                          (optionOfFinset (α := α) ground))).2
                      ⟨hzG, hpair⟩
                  have hg2 : g2 b = (z0, (some u : Option α), (some v : Option α)) := by
                    simp [g2, hzOpt, hUG, hUV, u, v]
                  exact hg2 ▸ hmem
              | none =>
                  have hpair :
                      ((none : Option α), (none : Option α)) ∈
                        (optionOfFinset (α := α) ground).product (optionOfFinset (α := α) ground) :=
                    Finset.mem_product.mpr ⟨hnoneOpt, hnoneOpt⟩
                  have hmem :
                      (z0, (none : Option α), (none : Option α)) ∈
                        Cod2 :=
                    (Finset.mem_product (s := ground)
                      (t :=
                        (optionOfFinset (α := α) ground).product
                          (optionOfFinset (α := α) ground))).2
                      ⟨hzG, hpair⟩
                  have hg2 : g2 b = (z0, (none : Option α), (none : Option α)) := by
                    simp [g2, hzOpt, hUG, hUV]
                  exact hg2 ▸ hmem
    have himg_card :
        (Good.image g2).card ≤ ground.card * (ground.card + 1) * (ground.card + 1) := by
      have hle :
          (Good.image g2).card ≤ Cod2.card :=
        Finset.card_le_card himg_sub
      have hprod :
          Cod2.card =
            ground.card *
              ((optionOfFinset (α := α) ground).product (optionOfFinset (α := α) ground)).card := by
        simp [Cod2, Finset.card_product]
      have hprod2 :
          ((optionOfFinset (α := α) ground).product (optionOfFinset (α := α) ground)).card =
            (optionOfFinset (α := α) ground).card * (optionOfFinset (α := α) ground).card := by
        exact Finset.card_product (optionOfFinset (α := α) ground) (optionOfFinset (α := α) ground)
      have hopt :
          (optionOfFinset (α := α) ground).card ≤ ground.card + 1 :=
        card_optionOfFinset_le_succ (α := α) ground
      calc
        (Good.image g2).card
            ≤ Cod2.card := hle
        _ = ground.card *
              ((optionOfFinset (α := α) ground).product (optionOfFinset (α := α) ground)).card := hprod
        _ = ground.card *
              ((optionOfFinset (α := α) ground).card * (optionOfFinset (α := α) ground).card) := by
              rw [hprod2]
        _ ≤ ground.card * ((ground.card + 1) * (ground.card + 1)) := by
              -- bound each `optionOfFinset` factor by `ground.card + 1`.
              have : (optionOfFinset (α := α) ground).card * (optionOfFinset (α := α) ground).card ≤
                  (ground.card + 1) * (ground.card + 1) :=
                Nat.mul_le_mul hopt hopt
              exact Nat.mul_le_mul_left ground.card this
        _ = ground.card * (ground.card + 1) * (ground.card + 1) := by
              simp [Nat.mul_assoc]
    -- Combine everything for the good part.
    calc
      Good.card
          = ∑ p ∈ Good.image g2, (Good.filter (fun b => g2 b = p)).card := hsum
      _ ≤ ∑ _p ∈ Good.image g2, 2 := hsum_le
      _ = 2 * (Good.image g2).card := hconst
      _ ≤ 2 * (ground.card * (ground.card + 1) * (ground.card + 1)) := by
            exact Nat.mul_le_mul_left 2 himg_card
      _ = 2 * ground.card * (ground.card + 1) * (ground.card + 1) := by
            simp [Nat.mul_assoc]
  -- Final split bound.
  calc
    Bsome.card
        = Good.card + BadNone.card := hcard_split
    _ ≤ 2 * ground.card * (ground.card + 1) * (ground.card + 1) + BadNone.card := by
          exact Nat.add_le_add_right hGood _

set_option maxHeartbeats 1000000 in
theorem card_Bucket_perXSignatureOutMore_filter_zChoice_ne_none_le_two_mul_n_mul_succ_mul_succ_of_badNone_empty
    (hreg : O1aUpgradeRegime family ground A0 h0)
    {k : WLcertKey α}
    {Sstar : {S // S ∈ o1aWitnessLiftDomWL family h0}}
    {x : α}
    (hSstar :
      Sstar ∈ wlcertAdmissibleFiber_hNotMem (family := family) (o1aWitnessLiftDomWL family h0) k)
    (σOut : PerXSignatureOutMore α) :
    let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h0
    let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
    let Fx0 :
        Finset {S // S ∈ dom} :=
      wlcertAdmissibleFiber_hNotMem_fiberForX (dom := dom) fiber Sstar.1 x
    let Uout : {Ssub // Ssub ∈ Fx0} → Finset α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      let yw :
          Σ y : α, BlockedUnionWitness family b.1.1 y :=
        chooseYAndWitness_of_hardFiber
          (family := family) (ground := ground) (A0 := A0) (h0 := h0)
          hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
          Sstar.2 b.1.2 hcert_star hcert_sub hne
      b.1.1 \ (yw.2.A ∪ yw.2.B)
    let sig0 : {Ssub // Ssub ∈ Fx0} → PerXSignature α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      perXSignature_of_hardFiber (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1) Sstar.2 b.1.2 hcert_star hcert_sub hne
    let sigOut : {Ssub // Ssub ∈ Fx0} → PerXSignatureOutMore α := fun b =>
      (sig0 b,
        trace5PlusOfFinset (α := α) (Uout b),
        t6OptionOfTrace5Plus (α := α) (Uout b))
    let X : Finset α := ground \ (k.2.2.1 ∪ k.2.2.2.1)
    let y : α := σOut.1.1
    let B : Finset {Ssub // Ssub ∈ Fx0} := Bucket (Fx := Fx0.attach) sigOut σOut
    let Bsome : Finset {Ssub // Ssub ∈ Fx0} :=
      B.filter (fun b => zChoice (α := α) X b.1.1 y h0 ≠ none)
    let g2 : {Ssub // Ssub ∈ Fx0} → α × Option α × Option α := by
      classical
      exact fun b =>
        match zChoice (α := α) X b.1.1 y h0 with
        | some z =>
            match uGoodChoice (α := α) X b.1.1 y h0 z with
            | some hu => (z, some hu.1, none)
            | none =>
                match uPairGoodChoice (α := α) X b.1.1 y h0 z with
                | some huv => (z, some huv.1.1, some huv.1.2)
                | none => (z, none, none)
        | none => (h0, none, none)
    let BadNone : Finset {Ssub // Ssub ∈ Fx0} :=
      Bsome.filter (fun b =>
        (g2 b).2.1 = none ∧ (g2 b).2.2 = none ∧
          ((((X \ b.1.1).erase y).erase h0).erase (g2 b).1).Nonempty)
    BadNone.card = 0 →
      Bsome.card ≤ 2 * ground.card * (ground.card + 1) * (ground.card + 1) := by
  classical
  intro dom fiber Fx0 Uout sig0 sigOut X y B Bsome g2 BadNone hBad0
  have h :=
    card_Bucket_perXSignatureOutMore_filter_zChoice_ne_none_le_two_mul_n_mul_succ_mul_succ_add_badNone
      (family := family) (ground := ground) (A0 := A0) (h0 := h0)
      hreg (k := k) (Sstar := Sstar) (x := x) hSstar σOut
  have h' :
      Bsome.card ≤ 2 * ground.card * (ground.card + 1) * (ground.card + 1) + BadNone.card := by
    simpa using h
  simpa [hBad0] using h'

/-!
Combine the `zChoice = none` and `zChoice ≠ none` bounds inside a fixed outMore bucket.

This packages the current best cap for `Bucket(σOut)` in the `τ=true` regime:
the `zChoice = none` part is `≤ 2`, and the `zChoice ≠ none` part is bounded by the
`g₂`-ledger plus the isolated residual `BadNone.card`.
-/

set_option maxHeartbeats 1000000 in
-- Needed: this lemma shares the large outMore telescope and can exceed the default heartbeat budget.
theorem card_Bucket_perXSignatureOutMore_le_two_add_two_mul_n_mul_succ_mul_succ_add_badNone_of_trace5Plus_true
    (hreg : O1aUpgradeRegime family ground A0 h0)
    {k : WLcertKey α}
    {Sstar : {S // S ∈ o1aWitnessLiftDomWL family h0}}
    {x : α}
    (hSstar :
      Sstar ∈ wlcertAdmissibleFiber_hNotMem (family := family) (o1aWitnessLiftDomWL family h0) k)
    (σOut : PerXSignatureOutMore α)
    {t1 t2 t3 t4 t5 : α}
    (hτ : σOut.2.1 = some (t1, t2, t3, t4, t5, true)) :
    let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h0
    let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
    let Fx0 :
        Finset {S // S ∈ dom} :=
      wlcertAdmissibleFiber_hNotMem_fiberForX (dom := dom) fiber Sstar.1 x
    let Uout : {Ssub // Ssub ∈ Fx0} → Finset α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      let yw :
          Σ y : α, BlockedUnionWitness family b.1.1 y :=
        chooseYAndWitness_of_hardFiber
          (family := family) (ground := ground) (A0 := A0) (h0 := h0)
          hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
          Sstar.2 b.1.2 hcert_star hcert_sub hne
      b.1.1 \ (yw.2.A ∪ yw.2.B)
    let sig0 : {Ssub // Ssub ∈ Fx0} → PerXSignature α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      perXSignature_of_hardFiber (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1) Sstar.2 b.1.2 hcert_star hcert_sub hne
    let sigOut : {Ssub // Ssub ∈ Fx0} → PerXSignatureOutMore α := fun b =>
      (sig0 b,
        trace5PlusOfFinset (α := α) (Uout b),
        t6OptionOfTrace5Plus (α := α) (Uout b))
    let X : Finset α := ground \ (k.2.2.1 ∪ k.2.2.2.1)
    let y : α := σOut.1.1
    let B : Finset {Ssub // Ssub ∈ Fx0} := Bucket (Fx := Fx0.attach) sigOut σOut
    let Bsome : Finset {Ssub // Ssub ∈ Fx0} :=
      B.filter (fun b => zChoice (α := α) X b.1.1 y h0 ≠ none)
    let g2 : {Ssub // Ssub ∈ Fx0} → α × Option α × Option α := by
      classical
      exact fun b =>
        match zChoice (α := α) X b.1.1 y h0 with
        | some z =>
            match uGoodChoice (α := α) X b.1.1 y h0 z with
            | some hu => (z, some hu.1, none)
            | none =>
                match uPairGoodChoice (α := α) X b.1.1 y h0 z with
                | some huv => (z, some huv.1.1, some huv.1.2)
                | none => (z, none, none)
        | none => (h0, none, none)
    let BadNone : Finset {Ssub // Ssub ∈ Fx0} :=
      Bsome.filter (fun b =>
        (g2 b).2.1 = none ∧ (g2 b).2.2 = none ∧
          ((((X \ b.1.1).erase y).erase h0).erase (g2 b).1).Nonempty)
    B.card ≤ 2 + 2 * ground.card * (ground.card + 1) * (ground.card + 1) + BadNone.card := by
  classical
  intro dom fiber Fx0 Uout sig0 sigOut X y B Bsome g2 BadNone
  -- `zChoice = none` part.
  let Bnone : Finset {Ssub // Ssub ∈ Fx0} :=
    B.filter (fun b => zChoice (α := α) X b.1.1 y h0 = none)
  have hBnone : Bnone.card ≤ 2 := by
    have h :=
      card_Bucket_perXSignatureOutMore_le_of_trace5Plus_true
        (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg (k := k) (Sstar := Sstar) (x := x) hSstar σOut hτ
    simpa [Bnone] using h
  -- `zChoice ≠ none` part (with the isolated residual).
  have hBsome :
      Bsome.card ≤ 2 * ground.card * (ground.card + 1) * (ground.card + 1) + BadNone.card := by
    have h :=
      card_Bucket_perXSignatureOutMore_filter_zChoice_ne_none_le_two_mul_n_mul_succ_mul_succ_add_badNone
        (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg (k := k) (Sstar := Sstar) (x := x) hSstar σOut
    simpa using h
  -- Partition `B` into the disjoint union of `Bnone` and `Bsome`.
  have hUnion : Bnone ∪ Bsome = B := by
    ext b
    by_cases hb : zChoice (α := α) X b.1.1 y h0 = none
    · simp [Bnone, Bsome, hb]
    · have hb' : zChoice (α := α) X b.1.1 y h0 ≠ none := by exact hb
      simp [Bnone, Bsome, hb, hb']
  have hDisj : Disjoint Bnone Bsome := by
    refine Finset.disjoint_left.2 ?_
    intro b hbN hbS
    have hzN : zChoice (α := α) X b.1.1 y h0 = none := (Finset.mem_filter.mp hbN).2
    have hzS : zChoice (α := α) X b.1.1 y h0 ≠ none := (Finset.mem_filter.mp hbS).2
    exact hzS hzN
  have hcard_split : B.card = Bnone.card + Bsome.card := by
    have hcardU : (Bnone ∪ Bsome).card = Bnone.card + Bsome.card :=
      Finset.card_union_of_disjoint hDisj
    simpa [hUnion] using hcardU
  -- Final bound.
  calc
    B.card = Bnone.card + Bsome.card := hcard_split
    _ ≤ 2 + (2 * ground.card * (ground.card + 1) * (ground.card + 1) + BadNone.card) := by
          exact Nat.add_le_add hBnone hBsome
    _ = 2 + 2 * ground.card * (ground.card + 1) * (ground.card + 1) + BadNone.card := by
          -- Associate to reassociate `2 + (A + B)` into `(2 + A) + B`.
          exact
            (Nat.add_assoc 2 (2 * ground.card * (ground.card + 1) * (ground.card + 1)) BadNone.card).symm

/-!
Aggregate residual seam: `BadNone`.

`BadNone` is the isolated contract-gap subbucket inside a `τ=true` outMore signature bucket.
We keep it as the **only** residual seam by aggregating its cardinalities as a Nat sum.

These definitions are wiring-only: they do not introduce any new structural assumptions.
-/

noncomputable def BadNoneOf_perXSignatureOutMore
    {α : Type*} [DecidableEq α]
    {dom : Finset (Finset α)} (Fx0 : Finset {S // S ∈ dom})
    (sigOut : {Ssub // Ssub ∈ Fx0} → PerXSignatureOutMore α)
    (σOut : PerXSignatureOutMore α) (X : Finset α) (h0 : α) :
    Finset {Ssub // Ssub ∈ Fx0} := by
  classical
  let y : α := σOut.1.1
  let B : Finset {Ssub // Ssub ∈ Fx0} := Bucket (Fx := Fx0.attach) sigOut σOut
  let Bsome : Finset {Ssub // Ssub ∈ Fx0} :=
    B.filter (fun b => zChoice (α := α) X b.1.1 y h0 ≠ none)
  let g2 : {Ssub // Ssub ∈ Fx0} → α × Option α × Option α := by
    classical
    exact fun b =>
      match zChoice (α := α) X b.1.1 y h0 with
      | some z =>
          match uGoodChoice (α := α) X b.1.1 y h0 z with
          | some hu => (z, some hu.1, none)
          | none =>
              match uPairGoodChoice (α := α) X b.1.1 y h0 z with
              | some huv => (z, some huv.1.1, some huv.1.2)
              | none => (z, none, none)
      | none => (h0, none, none)
  exact
    Bsome.filter (fun b =>
      (g2 b).2.1 = none ∧ (g2 b).2.2 = none ∧
        ((((X \ b.1.1).erase y).erase h0).erase (g2 b).1).Nonempty)

theorem BadNone_card_eq_BadNoneOf_card
    {α : Type*} [DecidableEq α]
    {dom : Finset (Finset α)} (Fx0 : Finset {S // S ∈ dom})
    (sigOut : {Ssub // Ssub ∈ Fx0} → PerXSignatureOutMore α)
    (σOut : PerXSignatureOutMore α) (X : Finset α) (h0 : α) :
    (let y : α := σOut.1.1
     let B : Finset {Ssub // Ssub ∈ Fx0} := Bucket (Fx := Fx0.attach) sigOut σOut
     let Bsome : Finset {Ssub // Ssub ∈ Fx0} :=
       B.filter (fun b => zChoice (α := α) X b.1.1 y h0 ≠ none)
     let g2 : {Ssub // Ssub ∈ Fx0} → α × Option α × Option α := by
       classical
       exact fun b =>
         match zChoice (α := α) X b.1.1 y h0 with
         | some z =>
             match uGoodChoice (α := α) X b.1.1 y h0 z with
             | some hu => (z, some hu.1, none)
             | none =>
                 match uPairGoodChoice (α := α) X b.1.1 y h0 z with
                 | some huv => (z, some huv.1.1, some huv.1.2)
                 | none => (z, none, none)
         | none => (h0, none, none)
     let BadNone :=
       Bsome.filter (fun b =>
         (g2 b).2.1 = none ∧ (g2 b).2.2 = none ∧
           ((((X \ b.1.1).erase y).erase h0).erase (g2 b).1).Nonempty)
     BadNone.card)
      =
      (BadNoneOf_perXSignatureOutMore (Fx0 := Fx0) sigOut σOut X h0).card := by
  rfl

set_option maxHeartbeats 2000000 in
-- Re-export the `τ=true` bucket bound with `BadNoneOf` on the RHS to keep downstream elaboration light.
theorem card_Bucket_perXSignatureOutMore_le_two_add_two_mul_n_mul_succ_mul_succ_add_badNoneOf_of_trace5Plus_true
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h0 : α}
    (hreg : O1aUpgradeRegime family ground A0 h0)
    {k : WLcertKey α}
    {Sstar : {S // S ∈ o1aWitnessLiftDomWL family h0}}
    {x : α}
    (hSstar :
      Sstar ∈ wlcertAdmissibleFiber_hNotMem (family := family) (o1aWitnessLiftDomWL family h0) k)
    (σOut : PerXSignatureOutMore α)
    {t1 t2 t3 t4 t5 : α}
    (hτ : σOut.2.1 = some (t1, t2, t3, t4, t5, true)) :
    let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h0
    let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
    let Fx0 :
        Finset {S // S ∈ dom} :=
      wlcertAdmissibleFiber_hNotMem_fiberForX (dom := dom) fiber Sstar.1 x
    let Uout : {Ssub // Ssub ∈ Fx0} → Finset α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      let yw :
          Σ y : α, BlockedUnionWitness family b.1.1 y :=
        chooseYAndWitness_of_hardFiber
          (family := family) (ground := ground) (A0 := A0) (h0 := h0)
          hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
          Sstar.2 b.1.2 hcert_star hcert_sub hne
      b.1.1 \ (yw.2.A ∪ yw.2.B)
    let sig0 : {Ssub // Ssub ∈ Fx0} → PerXSignature α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      perXSignature_of_hardFiber (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1) Sstar.2 b.1.2 hcert_star hcert_sub hne
    let sigOut : {Ssub // Ssub ∈ Fx0} → PerXSignatureOutMore α := fun b =>
      (sig0 b,
        trace5PlusOfFinset (α := α) (Uout b),
        t6OptionOfTrace5Plus (α := α) (Uout b))
    let X : Finset α := ground \ (k.2.2.1 ∪ k.2.2.2.1)
    let y : α := σOut.1.1
    let B : Finset {Ssub // Ssub ∈ Fx0} := Bucket (Fx := Fx0.attach) sigOut σOut
    let Bsome : Finset {Ssub // Ssub ∈ Fx0} :=
      B.filter (fun b => zChoice (α := α) X b.1.1 y h0 ≠ none)
    let g2 : {Ssub // Ssub ∈ Fx0} → α × Option α × Option α := by
      classical
      exact fun b =>
        match zChoice (α := α) X b.1.1 y h0 with
        | some z =>
            match uGoodChoice (α := α) X b.1.1 y h0 z with
            | some hu => (z, some hu.1, none)
            | none =>
                match uPairGoodChoice (α := α) X b.1.1 y h0 z with
                | some huv => (z, some huv.1.1, some huv.1.2)
                | none => (z, none, none)
        | none => (h0, none, none)
    let BadNone :=
      Bsome.filter (fun b =>
        (g2 b).2.1 = none ∧ (g2 b).2.2 = none ∧
          ((((X \ b.1.1).erase y).erase h0).erase (g2 b).1).Nonempty)
    (Bucket (Fx := Fx0.attach) sigOut σOut).card ≤
      2 + 2 * ground.card * (ground.card + 1) * (ground.card + 1) + BadNone.card := by
  classical
  exact
    card_Bucket_perXSignatureOutMore_le_two_add_two_mul_n_mul_succ_mul_succ_add_badNone_of_trace5Plus_true
      (family := family) (ground := ground) (A0 := A0) (h0 := h0)
      hreg (k := k) (Sstar := Sstar) (x := x) hSstar σOut
      (hτ := hτ)

noncomputable def BadNoneAgg_perXSignatureOutMore
    {α : Type*} [DecidableEq α]
    {dom : Finset (Finset α)} (Fx0 : Finset {S // S ∈ dom})
    (sigOut : {Ssub // Ssub ∈ Fx0} → PerXSignatureOutMore α)
    (X : Finset α) (h0 : α) : ℕ := by
  classical
  let sigOutImage : Finset (PerXSignatureOutMore α) := Fx0.attach.image sigOut
  let TauTrue : Finset (PerXSignatureOutMore α) :=
    sigOutImage.filter (fun σOut =>
      match σOut.2.1 with
      | some (_t1, _t2, _t3, _t4, _t5, true) => True
      | _ => False)
  exact
    ∑ σOut ∈ TauTrue,
      (BadNoneOf_perXSignatureOutMore (Fx0 := Fx0) sigOut σOut X h0).card

theorem BadNoneAgg_perXSignatureOutMore_eq_zero_iff
    {α : Type*} [DecidableEq α]
    {dom : Finset (Finset α)} (Fx0 : Finset {S // S ∈ dom})
    (sigOut : {Ssub // Ssub ∈ Fx0} → PerXSignatureOutMore α)
    (X : Finset α) (h0 : α) :
    let sigOutImage : Finset (PerXSignatureOutMore α) := Fx0.attach.image sigOut
    let TauTrue : Finset (PerXSignatureOutMore α) :=
      by
        classical
        exact
          sigOutImage.filter (fun σOut =>
            match σOut.2.1 with
            | some (_t1, _t2, _t3, _t4, _t5, true) => True
            | _ => False)
    BadNoneAgg_perXSignatureOutMore (Fx0 := Fx0) sigOut X h0 = 0 ↔
      ∀ σOut ∈ TauTrue,
        (BadNoneOf_perXSignatureOutMore (Fx0 := Fx0) sigOut σOut X h0).card = 0 := by
  classical
  intro sigOutImage TauTrue
  -- Expand the aggregate and use `Nat`-sum zero iff all terms are zero.
  simp [BadNoneAgg_perXSignatureOutMore, sigOutImage, TauTrue]

theorem BadNoneAgg_perXSignatureOutMore_eq_zero_imp
    {α : Type*} [DecidableEq α]
    {dom : Finset (Finset α)} (Fx0 : Finset {S // S ∈ dom})
    (sigOut : {Ssub // Ssub ∈ Fx0} → PerXSignatureOutMore α)
    (X : Finset α) (h0 : α) :
    let sigOutImage : Finset (PerXSignatureOutMore α) := Fx0.attach.image sigOut
    let TauTrue : Finset (PerXSignatureOutMore α) :=
      by
        classical
        exact
          sigOutImage.filter (fun σOut =>
            match σOut.2.1 with
            | some (_t1, _t2, _t3, _t4, _t5, true) => True
            | _ => False)
    BadNoneAgg_perXSignatureOutMore (Fx0 := Fx0) sigOut X h0 = 0 →
      ∀ σOut ∈ TauTrue,
        (BadNoneOf_perXSignatureOutMore (Fx0 := Fx0) sigOut σOut X h0).card = 0 := by
  classical
  intro sigOutImage TauTrue hAgg0
  have hIff :
      BadNoneAgg_perXSignatureOutMore (Fx0 := Fx0) sigOut X h0 = 0 ↔
        ∀ σOut ∈ TauTrue,
          (BadNoneOf_perXSignatureOutMore (Fx0 := Fx0) sigOut σOut X h0).card = 0 := by
    simpa [sigOutImage, TauTrue] using
      (BadNoneAgg_perXSignatureOutMore_eq_zero_iff (Fx0 := Fx0) sigOut X h0)
  exact hIff.mp hAgg0

theorem BadNoneAgg_perXSignatureOutMore_eq_zero_of_pointwise
    {α : Type*} [DecidableEq α]
    {dom : Finset (Finset α)} (Fx0 : Finset {S // S ∈ dom})
    (sigOut : {Ssub // Ssub ∈ Fx0} → PerXSignatureOutMore α)
    (X : Finset α) (h0 : α) :
    let sigOutImage : Finset (PerXSignatureOutMore α) := Fx0.attach.image sigOut
    let TauTrue : Finset (PerXSignatureOutMore α) :=
      by
        classical
        exact
          sigOutImage.filter (fun σOut =>
            match σOut.2.1 with
            | some (_t1, _t2, _t3, _t4, _t5, true) => True
            | _ => False)
    (∀ σOut ∈ TauTrue,
      (BadNoneOf_perXSignatureOutMore (Fx0 := Fx0) sigOut σOut X h0).card = 0) →
      BadNoneAgg_perXSignatureOutMore (Fx0 := Fx0) sigOut X h0 = 0 := by
  classical
  intro sigOutImage TauTrue hPointwise
  have hIff :
      BadNoneAgg_perXSignatureOutMore (Fx0 := Fx0) sigOut X h0 = 0 ↔
        ∀ σOut ∈ TauTrue,
          (BadNoneOf_perXSignatureOutMore (Fx0 := Fx0) sigOut σOut X h0).card = 0 := by
    simpa [sigOutImage, TauTrue] using
      (BadNoneAgg_perXSignatureOutMore_eq_zero_iff (Fx0 := Fx0) sigOut X h0)
  exact hIff.mpr hPointwise

/-!
Additional seam: `τ≠true ∧ coreTrace.hasMore=true`.

The `τ`-split and `coreTrace` are not coupled by the current contracts, so the existing
`τ≠true` bucket caps only apply on the `coreTrace.hasMore=false` slice. We keep a *single*
exposed seam knob by aggregating the uncovered mass as a Nat sum and adding it to the
existing `BadNoneAgg` seam.
-/

noncomputable def CoreMore_perXSignatureOutMore
    {α : Type*} (σOut : PerXSignatureOutMore α) : Prop :=
  ∃ u1 ot2, σOut.1.2.2.2.1 = some (u1, ot2, true)

noncomputable def BadCoreNotTrueAgg_perXSignatureOutMore
    {α : Type*} [DecidableEq α]
    {dom : Finset (Finset α)} (Fx0 : Finset {S // S ∈ dom})
    (sigOut : {Ssub // Ssub ∈ Fx0} → PerXSignatureOutMore α) : ℕ := by
  classical
  let sigOutImage : Finset (PerXSignatureOutMore α) := Fx0.attach.image sigOut
  let TauNotTrue : Finset (PerXSignatureOutMore α) :=
    sigOutImage.filter (fun σOut =>
      match σOut.2.1 with
      | some (_t1, _t2, _t3, _t4, _t5, true) => False
      | _ => True)
  let TauNotTrueCoreMore : Finset (PerXSignatureOutMore α) :=
    TauNotTrue.filter (fun σOut =>
      CoreMore_perXSignatureOutMore (α := α) σOut)
  exact ∑ σOut ∈ TauNotTrueCoreMore, (Bucket (Fx := Fx0.attach) sigOut σOut).card

noncomputable def BadAgg_perXSignatureOutMore
    {α : Type*} [DecidableEq α]
    {dom : Finset (Finset α)} (Fx0 : Finset {S // S ∈ dom})
    (sigOut : {Ssub // Ssub ∈ Fx0} → PerXSignatureOutMore α)
    (X : Finset α) (h0 : α) : ℕ :=
  BadNoneAgg_perXSignatureOutMore (Fx0 := Fx0) sigOut X h0 +
    BadCoreNotTrueAgg_perXSignatureOutMore (Fx0 := Fx0) sigOut

theorem BadAgg_perXSignatureOutMore_eq_zero_imp
    {α : Type*} [DecidableEq α]
    {dom : Finset (Finset α)} (Fx0 : Finset {S // S ∈ dom})
    (sigOut : {Ssub // Ssub ∈ Fx0} → PerXSignatureOutMore α)
    (X : Finset α) (h0 : α) :
    BadAgg_perXSignatureOutMore (Fx0 := Fx0) sigOut X h0 = 0 →
      BadNoneAgg_perXSignatureOutMore (Fx0 := Fx0) sigOut X h0 = 0 ∧
        BadCoreNotTrueAgg_perXSignatureOutMore (Fx0 := Fx0) sigOut = 0 := by
  intro h
  have h' :
      BadNoneAgg_perXSignatureOutMore (Fx0 := Fx0) sigOut X h0 +
          BadCoreNotTrueAgg_perXSignatureOutMore (Fx0 := Fx0) sigOut = 0 := by
    simpa [BadAgg_perXSignatureOutMore] using h
  simpa using (Nat.add_eq_zero_iff.mp h')

/-!
Local sum-wiring helper.

We will repeatedly use the pattern:
if `f x ≤ C + g x` on a finset, then `∑ f ≤ card * C + ∑ g`.

This is purely arithmetic wiring; it does not depend on any sunflower-specific structure.
-/

theorem sum_le_card_mul_add_sum {β : Type*} (s : Finset β) (C : ℕ) (f g : β → ℕ)
    (hfg : ∀ b ∈ s, f b ≤ C + g b) :
    (∑ b ∈ s, f b) ≤ s.card * C + (∑ b ∈ s, g b) := by
  classical
  -- Pointwise bound the sum by `∑ (C + g b)`.
  have hsum : (∑ b ∈ s, f b) ≤ ∑ b ∈ s, (C + g b) := by
    refine Finset.sum_le_sum ?_
    intro b hb
    exact hfg b hb
  -- Rewrite the RHS using distributivity.
  -- `∑ (C + g b) = ∑ C + ∑ g b = card * C + ∑ g b`.
  refine le_trans hsum ?_
  have hsum_const : (∑ _b ∈ s, C) = s.card * C := by
    simpa [Nat.mul_comm] using (Finset.sum_const_nat (s := s) C)
  have hrewrite :
      (∑ b ∈ s, (C + g b)) = s.card * C + (∑ b ∈ s, g b) := by
    calc
      (∑ b ∈ s, (C + g b))
          = (∑ b ∈ s, C) + (∑ b ∈ s, g b) := by
              simp [Finset.sum_add_distrib]
      _ = s.card * C + (∑ b ∈ s, g b) := by
            rw [hsum_const]
  exact le_of_eq hrewrite

/-!
Global seam knob across per-`x` subfibers.

When we cover a hard-branch fiber by `{S⋆}` plus a sum over `x ∈ realizedXSet`, we expose a single
residual seam per `x` (currently `BadAgg_perXSignatureOutMore`). We aggregate these per-`x` seams
as a Nat sum. Downstream, we assume **only** that this aggregate is `0`, and derive the pointwise
seam-vanishing facts mechanically.
-/

noncomputable def BadAggAgg_over_realizedXSet
    {α : Type*} [DecidableEq α]
    {dom : Finset (Finset α)} (fiber : Finset {S // S ∈ dom})
    (Sstar : {S // S ∈ dom}) (X : Finset α) (bad : α → ℕ) : ℕ :=
  ∑ x ∈ realizedXSet (dom := dom) fiber Sstar.1 X, bad x

theorem BadAggAgg_over_realizedXSet_eq_zero_imp
    {α : Type*} [DecidableEq α]
    {dom : Finset (Finset α)} (fiber : Finset {S // S ∈ dom})
    (Sstar : {S // S ∈ dom}) (X : Finset α) (bad : α → ℕ) :
    BadAggAgg_over_realizedXSet (fiber := fiber) (Sstar := Sstar) X bad = 0 →
      ∀ x ∈ realizedXSet (dom := dom) fiber Sstar.1 X, bad x = 0 := by
  classical
  intro hsum
  -- `Nat` sum-zero iff all terms are zero (nonnegativity is automatic).
  have h :=
    (Finset.sum_eq_zero_iff_of_nonneg
        (s := realizedXSet (dom := dom) fiber Sstar.1 X)
        (f := fun x => bad x) (by
          intro _ _; exact Nat.zero_le _)).1 (by
          simpa [BadAggAgg_over_realizedXSet] using hsum)
  simpa using h

/--
Wiring lemma for the outMore bucket sum: split signature values into `τ=true` vs `τ≠true`
and keep `BadNone` as the single aggregated residual seam.

This is *purely* a decomposition lemma: the caller supplies the per-bucket caps in the two
regimes, and we return the corresponding bound on `Fx0.card`.
-/
theorem card_Fx0_le_tauTrue_mul_add_tauNotTrue_mul_add_badNoneAgg
    {α : Type*} [DecidableEq α]
    {dom : Finset (Finset α)} (Fx0 : Finset {S // S ∈ dom})
    (sigOut : {Ssub // Ssub ∈ Fx0} → PerXSignatureOutMore α)
    (X : Finset α) (h0 : α) (C capNotTrue : ℕ)
    (hTauTrue :
      let sigOutImage : Finset (PerXSignatureOutMore α) := Fx0.attach.image sigOut
      let TauTrue : Finset (PerXSignatureOutMore α) :=
        by
          classical
          exact
            sigOutImage.filter (fun σOut =>
              match σOut.2.1 with
              | some (_t1, _t2, _t3, _t4, _t5, true) => True
              | _ => False)
      ∀ σOut ∈ TauTrue,
        (Bucket (Fx := Fx0.attach) sigOut σOut).card ≤
          C + (BadNoneOf_perXSignatureOutMore (Fx0 := Fx0) sigOut σOut X h0).card)
    (hTauNotTrue :
      let sigOutImage : Finset (PerXSignatureOutMore α) := Fx0.attach.image sigOut
      let TauNotTrue : Finset (PerXSignatureOutMore α) :=
        by
          classical
          exact
            sigOutImage.filter (fun σOut =>
              match σOut.2.1 with
              | some (_t1, _t2, _t3, _t4, _t5, true) => False
              | _ => True)
      ∀ σOut ∈ TauNotTrue, (Bucket (Fx := Fx0.attach) sigOut σOut).card ≤ capNotTrue) :
    let sigOutImage : Finset (PerXSignatureOutMore α) := Fx0.attach.image sigOut
    let TauTrue : Finset (PerXSignatureOutMore α) :=
      by
        classical
        exact
          sigOutImage.filter (fun σOut =>
            match σOut.2.1 with
            | some (_t1, _t2, _t3, _t4, _t5, true) => True
            | _ => False)
    let TauNotTrue : Finset (PerXSignatureOutMore α) :=
      by
        classical
        exact
          sigOutImage.filter (fun σOut =>
            match σOut.2.1 with
            | some (_t1, _t2, _t3, _t4, _t5, true) => False
            | _ => True)
    Fx0.card ≤ TauTrue.card * C + TauNotTrue.card * capNotTrue +
      BadNoneAgg_perXSignatureOutMore (Fx0 := Fx0) sigOut X h0 := by
  classical
  intro sigOutImage TauTrue TauNotTrue
  -- Specialize the caller-supplied caps (they are stated under `let`-bindings).
  have hTauTrue' :
      ∀ σOut ∈ TauTrue,
        (Bucket (Fx := Fx0.attach) sigOut σOut).card ≤
          C + (BadNoneOf_perXSignatureOutMore (Fx0 := Fx0) sigOut σOut X h0).card := by
    classical
    simpa [sigOutImage, TauTrue] using hTauTrue
  have hTauNotTrue' :
      ∀ σOut ∈ TauNotTrue, (Bucket (Fx := Fx0.attach) sigOut σOut).card ≤ capNotTrue := by
    classical
    simpa [sigOutImage, TauNotTrue] using hTauNotTrue
  -- Bucket-sum formula on `Fx0.attach`.
  have hsum :
      Fx0.card =
        (∑ σOut ∈ sigOutImage, (Bucket (Fx := Fx0.attach) sigOut σOut).card) := by
    have hsum' :
        Fx0.attach.card =
          (∑ σOut ∈ sigOutImage, (Bucket (Fx := Fx0.attach) sigOut σOut).card) :=
      card_Fx_eq_sum_card_Bucket (Fx := Fx0.attach) sigOut
    simpa using hsum'
  -- `TauTrue` and `TauNotTrue` are complementary filters of `sigOutImage`.
  let pTau : PerXSignatureOutMore α → Prop := fun σOut =>
    match σOut.2.1 with
    | some (_t1, _t2, _t3, _t4, _t5, true) => True
    | _ => False
  have hTauTrueDef : TauTrue = sigOutImage.filter pTau := by
    ext σOut
    simp [TauTrue, pTau]
  have hTauNotTrueDef : TauNotTrue = sigOutImage.filter (fun σOut => ¬ pTau σOut) := by
    ext σOut
    cases hτ : σOut.2.1 with
    | none =>
        simp [TauNotTrue, pTau, hτ]
    | some sext =>
        rcases sext with ⟨t1, t2, t3, t4, t5, b⟩
        cases b <;> simp [TauNotTrue, pTau, hτ]
  have hdisj : Disjoint TauTrue TauNotTrue := by
    rw [hTauTrueDef, hTauNotTrueDef]
    exact Finset.disjoint_filter_filter_neg _ _ pTau
  have hunion : TauTrue ∪ TauNotTrue = sigOutImage := by
    rw [hTauTrueDef, hTauNotTrueDef]
    simpa using (Finset.filter_union_filter_neg_eq (s := sigOutImage) (p := pTau))
  -- Rewrite the bucket sum via the disjoint union.
  have hsum_split :
      (∑ σOut ∈ sigOutImage, (Bucket (Fx := Fx0.attach) sigOut σOut).card) =
        (∑ σOut ∈ TauTrue, (Bucket (Fx := Fx0.attach) sigOut σOut).card) +
          (∑ σOut ∈ TauNotTrue, (Bucket (Fx := Fx0.attach) sigOut σOut).card) := by
    -- First split over the disjoint union, then rewrite the union to `sigOutImage`.
    have hsumU :
        (∑ σOut ∈ TauTrue ∪ TauNotTrue,
            (Bucket (Fx := Fx0.attach) sigOut σOut).card) =
          (∑ σOut ∈ TauTrue, (Bucket (Fx := Fx0.attach) sigOut σOut).card) +
            (∑ σOut ∈ TauNotTrue, (Bucket (Fx := Fx0.attach) sigOut σOut).card) :=
      -- Be explicit about the summand to avoid leaving any metavariables unresolved.
      Finset.sum_union hdisj (f := fun σOut => (Bucket (Fx := Fx0.attach) sigOut σOut).card)
    -- Rewrite `TauTrue ∪ TauNotTrue` to `sigOutImage`.
    simpa [hunion] using hsumU
  -- Bound the `τ=true` sum by `card * C + BadNoneAgg`.
  have hTrueSum :
      (∑ σOut ∈ TauTrue, (Bucket (Fx := Fx0.attach) sigOut σOut).card) ≤
        TauTrue.card * C +
          BadNoneAgg_perXSignatureOutMore (Fx0 := Fx0) sigOut X h0 := by
    -- First, apply the generic `∑ f ≤ card*C + ∑ g` wiring lemma.
    have hle :
        (∑ σOut ∈ TauTrue, (Bucket (Fx := Fx0.attach) sigOut σOut).card) ≤
          TauTrue.card * C +
            ∑ σOut ∈ TauTrue,
              (BadNoneOf_perXSignatureOutMore (Fx0 := Fx0) sigOut σOut X h0).card :=
      sum_le_card_mul_add_sum (s := TauTrue) (C := C)
        (f := fun σOut => (Bucket (Fx := Fx0.attach) sigOut σOut).card)
        (g := fun σOut =>
          (BadNoneOf_perXSignatureOutMore (Fx0 := Fx0) sigOut σOut X h0).card) (by
            intro σOut hσ
            -- Discharge the hypothesis using the caller-supplied cap.
            exact hTauTrue' σOut hσ)
    -- Replace the `∑ BadNoneOf.card` term by `BadNoneAgg`.
    have hAgg :
        (∑ σOut ∈ TauTrue,
            (BadNoneOf_perXSignatureOutMore (Fx0 := Fx0) sigOut σOut X h0).card) =
          BadNoneAgg_perXSignatureOutMore (Fx0 := Fx0) sigOut X h0 := by
      -- `BadNoneAgg` is *defined* as this sum over the same `TauTrue`.
      simp [BadNoneAgg_perXSignatureOutMore, sigOutImage, TauTrue]
    -- Conclude after rewriting.
    simpa [hAgg, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hle
  -- Bound the `τ≠true` sum by `card * capNotTrue`.
  have hNotTrueSum :
      (∑ σOut ∈ TauNotTrue, (Bucket (Fx := Fx0.attach) sigOut σOut).card) ≤
        TauNotTrue.card * capNotTrue := by
    have hle :
        (∑ σOut ∈ TauNotTrue, (Bucket (Fx := Fx0.attach) sigOut σOut).card) ≤
          ∑ σOut ∈ TauNotTrue, capNotTrue := by
      refine Finset.sum_le_sum ?_
      intro σOut hσ
      exact hTauNotTrue' σOut hσ
    simpa [Finset.sum_const_nat, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hle
  -- Combine everything.
  have hmain :
      Fx0.card ≤ TauTrue.card * C + TauNotTrue.card * capNotTrue +
        BadNoneAgg_perXSignatureOutMore (Fx0 := Fx0) sigOut X h0 := by
    -- Start from `Fx0.card = sum buckets` and use the split + bounds.
    calc
      Fx0.card =
          (∑ σOut ∈ sigOutImage, (Bucket (Fx := Fx0.attach) sigOut σOut).card) := hsum
      _ = (∑ σOut ∈ TauTrue, (Bucket (Fx := Fx0.attach) sigOut σOut).card) +
            (∑ σOut ∈ TauNotTrue, (Bucket (Fx := Fx0.attach) sigOut σOut).card) := hsum_split
      _ ≤ (TauTrue.card * C + BadNoneAgg_perXSignatureOutMore (Fx0 := Fx0) sigOut X h0) +
            (TauNotTrue.card * capNotTrue) := by
              exact Nat.add_le_add hTrueSum hNotTrueSum
      _ = TauTrue.card * C + TauNotTrue.card * capNotTrue +
            BadNoneAgg_perXSignatureOutMore (Fx0 := Fx0) sigOut X h0 := by
              -- Reassociate/commute into the desired `A + B + seam` order.
              -- Avoid `simp` with AC lemmas (heartbeat-expensive); do targeted rewrites.
              rw [Nat.add_assoc]
              rw [Nat.add_comm (BadNoneAgg_perXSignatureOutMore (Fx0 := Fx0) sigOut X h0)
                (TauNotTrue.card * capNotTrue)]
              -- `A + (B + seam) = (A + B) + seam`
              rw [(Nat.add_assoc (TauTrue.card * C) (TauNotTrue.card * capNotTrue)
                (BadNoneAgg_perXSignatureOutMore (Fx0 := Fx0) sigOut X h0)).symm]
  exact hmain

/--
Variant of `card_Fx0_le_tauTrue_mul_add_tauNotTrue_mul_add_badNoneAgg` that keeps a *single*
seam knob while avoiding any coupling assumption between `τ` and `coreTrace`.

We split `τ≠true` signatures into a rigid slice (where `coreTrace.hasMore=false`, so the
existing `τ≠true` bucket caps apply) and an uncovered slice (where `coreTrace.hasMore=true`),
whose total mass is aggregated into `BadCoreNotTrueAgg_perXSignatureOutMore` and folded into
`BadAgg_perXSignatureOutMore`.
-/
theorem card_Fx0_le_tauTrue_mul_add_tauNotTrueRigid_mul_add_badAgg
    {α : Type*} [DecidableEq α]
    {dom : Finset (Finset α)} (Fx0 : Finset {S // S ∈ dom})
    (sigOut : {Ssub // Ssub ∈ Fx0} → PerXSignatureOutMore α)
    (X : Finset α) (h0 : α) (C capNotTrue : ℕ)
    (hTauTrue :
      let sigOutImage : Finset (PerXSignatureOutMore α) := Fx0.attach.image sigOut
      let TauTrue : Finset (PerXSignatureOutMore α) :=
        by
          classical
          exact
            sigOutImage.filter (fun σOut =>
              match σOut.2.1 with
              | some (_t1, _t2, _t3, _t4, _t5, true) => True
              | _ => False)
      ∀ σOut ∈ TauTrue,
        (Bucket (Fx := Fx0.attach) sigOut σOut).card ≤
          C + (BadNoneOf_perXSignatureOutMore (Fx0 := Fx0) sigOut σOut X h0).card)
    (hTauNotTrueRigid :
      let sigOutImage : Finset (PerXSignatureOutMore α) := Fx0.attach.image sigOut
      let TauNotTrue : Finset (PerXSignatureOutMore α) :=
        by
          classical
          exact
            sigOutImage.filter (fun σOut =>
              match σOut.2.1 with
              | some (_t1, _t2, _t3, _t4, _t5, true) => False
              | _ => True)
      let TauNotTrueRigid : Finset (PerXSignatureOutMore α) :=
        by
          classical
          exact
            TauNotTrue.filter (fun σOut =>
              ¬ CoreMore_perXSignatureOutMore (α := α) σOut)
      ∀ σOut ∈ TauNotTrueRigid, (Bucket (Fx := Fx0.attach) sigOut σOut).card ≤ capNotTrue) :
    let sigOutImage : Finset (PerXSignatureOutMore α) := Fx0.attach.image sigOut
    let TauTrue : Finset (PerXSignatureOutMore α) :=
      by
        classical
        exact
          sigOutImage.filter (fun σOut =>
            match σOut.2.1 with
            | some (_t1, _t2, _t3, _t4, _t5, true) => True
            | _ => False)
    let TauNotTrue : Finset (PerXSignatureOutMore α) :=
      by
        classical
        exact
          sigOutImage.filter (fun σOut =>
            match σOut.2.1 with
            | some (_t1, _t2, _t3, _t4, _t5, true) => False
            | _ => True)
    let TauNotTrueCoreMore : Finset (PerXSignatureOutMore α) :=
      by
        classical
        exact
          TauNotTrue.filter (fun σOut =>
            CoreMore_perXSignatureOutMore (α := α) σOut)
    let TauNotTrueRigid : Finset (PerXSignatureOutMore α) :=
      by
        classical
        exact
          TauNotTrue.filter (fun σOut =>
            ¬ CoreMore_perXSignatureOutMore (α := α) σOut)
    Fx0.card ≤ TauTrue.card * C + TauNotTrueRigid.card * capNotTrue +
      BadAgg_perXSignatureOutMore (Fx0 := Fx0) sigOut X h0 := by
  classical
  intro sigOutImage TauTrue TauNotTrue TauNotTrueCoreMore TauNotTrueRigid
  -- Specialize the caller-supplied caps (they are stated under `let`-bindings).
  have hTauTrue' :
      ∀ σOut ∈ TauTrue,
        (Bucket (Fx := Fx0.attach) sigOut σOut).card ≤
          C + (BadNoneOf_perXSignatureOutMore (Fx0 := Fx0) sigOut σOut X h0).card := by
    classical
    simpa [sigOutImage, TauTrue] using hTauTrue
  have hTauNotTrueRigid' :
      ∀ σOut ∈ TauNotTrueRigid, (Bucket (Fx := Fx0.attach) sigOut σOut).card ≤ capNotTrue := by
    classical
    simpa [sigOutImage, TauNotTrue, TauNotTrueRigid] using hTauNotTrueRigid
  -- Bucket-sum formula on `Fx0.attach`.
  have hsum :
      Fx0.card =
        (∑ σOut ∈ sigOutImage, (Bucket (Fx := Fx0.attach) sigOut σOut).card) := by
    have hsum' :
        Fx0.attach.card =
          (∑ σOut ∈ sigOutImage, (Bucket (Fx := Fx0.attach) sigOut σOut).card) :=
      card_Fx_eq_sum_card_Bucket (Fx := Fx0.attach) sigOut
    simpa using hsum'
  -- `TauTrue` and `TauNotTrue` form a disjoint union equal to `sigOutImage`.
  have hdisjTrueNot : Disjoint TauTrue TauNotTrue := by
    refine Finset.disjoint_left.2 ?_
    intro σOut hT hN
    have hTp : (match σOut.2.1 with
        | some (_t1, _t2, _t3, _t4, _t5, true) => True
        | _ => False) := (Finset.mem_filter.mp hT).2
    have hNp : (match σOut.2.1 with
        | some (_t1, _t2, _t3, _t4, _t5, true) => False
        | _ => True) := (Finset.mem_filter.mp hN).2
    cases hτ : σOut.2.1 with
    | none =>
        simpa [hτ] using hTp
    | some sext =>
        rcases sext with ⟨t1, t2, t3, t4, t5, b⟩
        cases b <;> simp [hτ] at hTp hNp
  have hunionTrueNot : TauTrue ∪ TauNotTrue = sigOutImage := by
    ext σOut
    constructor
    · intro hmem
      exact (Finset.mem_union.mp hmem).elim (fun h => (Finset.mem_filter.mp h).1)
        (fun h => (Finset.mem_filter.mp h).1)
    · intro hmem
      cases hτ : σOut.2.1 with
      | none =>
          have hN : σOut ∈ TauNotTrue := by
            refine Finset.mem_filter.mpr ?_
            refine ⟨hmem, ?_⟩
            simp [hτ]
          exact Finset.mem_union.mpr (Or.inr hN)
      | some sext =>
          rcases sext with ⟨t1, t2, t3, t4, t5, b⟩
          cases b with
          | false =>
              have hN : σOut ∈ TauNotTrue := by
                refine Finset.mem_filter.mpr ?_
                refine ⟨hmem, ?_⟩
                simp [hτ]
              exact Finset.mem_union.mpr (Or.inr hN)
          | true =>
              have hT : σOut ∈ TauTrue := by
                refine Finset.mem_filter.mpr ?_
                refine ⟨hmem, ?_⟩
                simp [hτ]
              exact Finset.mem_union.mpr (Or.inl hT)
  -- Split `TauNotTrue` into the uncovered `CoreMore` slice and the rigid slice.
  have hdisjCoreRigid : Disjoint TauNotTrueCoreMore TauNotTrueRigid := by
    refine Finset.disjoint_left.2 ?_
    intro σOut hC hR
    have hCore : CoreMore_perXSignatureOutMore (α := α) σOut :=
      (Finset.mem_filter.mp hC).2
    have hNoCore : ¬ CoreMore_perXSignatureOutMore (α := α) σOut :=
      (Finset.mem_filter.mp hR).2
    exact hNoCore hCore
  have hunionCoreRigid : TauNotTrueCoreMore ∪ TauNotTrueRigid = TauNotTrue := by
    ext σOut
    constructor
    · intro hmem
      exact (Finset.mem_union.mp hmem).elim (fun h => (Finset.mem_filter.mp h).1)
        (fun h => (Finset.mem_filter.mp h).1)
    · intro hmem
      by_cases hCore : CoreMore_perXSignatureOutMore (α := α) σOut
      · have hC : σOut ∈ TauNotTrueCoreMore := by
          refine Finset.mem_filter.mpr ?_
          exact ⟨hmem, hCore⟩
        exact Finset.mem_union.mpr (Or.inl hC)
      · have hR : σOut ∈ TauNotTrueRigid := by
          refine Finset.mem_filter.mpr ?_
          exact ⟨hmem, hCore⟩
        exact Finset.mem_union.mpr (Or.inr hR)
  -- Rewrite the bucket sum via the disjoint unions.
  have hsum_split_true :
      (∑ σOut ∈ sigOutImage, (Bucket (Fx := Fx0.attach) sigOut σOut).card) =
        (∑ σOut ∈ TauTrue, (Bucket (Fx := Fx0.attach) sigOut σOut).card) +
          (∑ σOut ∈ TauNotTrue, (Bucket (Fx := Fx0.attach) sigOut σOut).card) := by
    have hsumU :
        (∑ σOut ∈ TauTrue ∪ TauNotTrue,
            (Bucket (Fx := Fx0.attach) sigOut σOut).card) =
          (∑ σOut ∈ TauTrue, (Bucket (Fx := Fx0.attach) sigOut σOut).card) +
            (∑ σOut ∈ TauNotTrue, (Bucket (Fx := Fx0.attach) sigOut σOut).card) :=
      Finset.sum_union hdisjTrueNot (f := fun σOut => (Bucket (Fx := Fx0.attach) sigOut σOut).card)
    simpa [hunionTrueNot] using hsumU
  have hsum_split_core :
      (∑ σOut ∈ TauNotTrue, (Bucket (Fx := Fx0.attach) sigOut σOut).card) =
        (∑ σOut ∈ TauNotTrueCoreMore, (Bucket (Fx := Fx0.attach) sigOut σOut).card) +
          (∑ σOut ∈ TauNotTrueRigid, (Bucket (Fx := Fx0.attach) sigOut σOut).card) := by
    have hsumU :
        (∑ σOut ∈ TauNotTrueCoreMore ∪ TauNotTrueRigid,
            (Bucket (Fx := Fx0.attach) sigOut σOut).card) =
          (∑ σOut ∈ TauNotTrueCoreMore, (Bucket (Fx := Fx0.attach) sigOut σOut).card) +
            (∑ σOut ∈ TauNotTrueRigid, (Bucket (Fx := Fx0.attach) sigOut σOut).card) :=
      Finset.sum_union hdisjCoreRigid
        (f := fun σOut => (Bucket (Fx := Fx0.attach) sigOut σOut).card)
    simpa [hunionCoreRigid] using hsumU
  -- Bound the `τ=true` sum by `card * C + BadNoneAgg`.
  have hTrueSum :
      (∑ σOut ∈ TauTrue, (Bucket (Fx := Fx0.attach) sigOut σOut).card) ≤
        TauTrue.card * C +
          BadNoneAgg_perXSignatureOutMore (Fx0 := Fx0) sigOut X h0 := by
    have hle :
        (∑ σOut ∈ TauTrue, (Bucket (Fx := Fx0.attach) sigOut σOut).card) ≤
          TauTrue.card * C +
            ∑ σOut ∈ TauTrue,
              (BadNoneOf_perXSignatureOutMore (Fx0 := Fx0) sigOut σOut X h0).card :=
      sum_le_card_mul_add_sum (s := TauTrue) (C := C)
        (f := fun σOut => (Bucket (Fx := Fx0.attach) sigOut σOut).card)
        (g := fun σOut =>
          (BadNoneOf_perXSignatureOutMore (Fx0 := Fx0) sigOut σOut X h0).card) (by
            intro σOut hσ
            exact hTauTrue' σOut hσ)
    have hAgg :
        (∑ σOut ∈ TauTrue,
            (BadNoneOf_perXSignatureOutMore (Fx0 := Fx0) sigOut σOut X h0).card) =
          BadNoneAgg_perXSignatureOutMore (Fx0 := Fx0) sigOut X h0 := by
      simp [BadNoneAgg_perXSignatureOutMore, sigOutImage, TauTrue]
    simpa [hAgg, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hle
  -- Bound the rigid `τ≠true` sum by `card * capNotTrue`.
  have hRigidSum :
      (∑ σOut ∈ TauNotTrueRigid, (Bucket (Fx := Fx0.attach) sigOut σOut).card) ≤
        TauNotTrueRigid.card * capNotTrue := by
    have hle :
        (∑ σOut ∈ TauNotTrueRigid, (Bucket (Fx := Fx0.attach) sigOut σOut).card) ≤
          ∑ σOut ∈ TauNotTrueRigid, capNotTrue := by
      refine Finset.sum_le_sum ?_
      intro σOut hσ
      exact hTauNotTrueRigid' σOut hσ
    simpa [Finset.sum_const_nat, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hle
  -- Replace the uncovered `CoreMore` slice by its aggregate seam.
  have hCoreAgg :
      (∑ σOut ∈ TauNotTrueCoreMore, (Bucket (Fx := Fx0.attach) sigOut σOut).card) =
        BadCoreNotTrueAgg_perXSignatureOutMore (Fx0 := Fx0) sigOut := by
    simp [BadCoreNotTrueAgg_perXSignatureOutMore, sigOutImage, TauNotTrue, TauNotTrueCoreMore]
  -- Combine.
  have hmain :
      Fx0.card ≤ TauTrue.card * C + TauNotTrueRigid.card * capNotTrue +
        BadAgg_perXSignatureOutMore (Fx0 := Fx0) sigOut X h0 := by
    have hsum_all :
        Fx0.card =
          (∑ σOut ∈ TauTrue, (Bucket (Fx := Fx0.attach) sigOut σOut).card) +
            (∑ σOut ∈ TauNotTrueCoreMore, (Bucket (Fx := Fx0.attach) sigOut σOut).card) +
              (∑ σOut ∈ TauNotTrueRigid, (Bucket (Fx := Fx0.attach) sigOut σOut).card) := by
      calc
        Fx0.card =
            (∑ σOut ∈ sigOutImage, (Bucket (Fx := Fx0.attach) sigOut σOut).card) := hsum
        _ = (∑ σOut ∈ TauTrue, (Bucket (Fx := Fx0.attach) sigOut σOut).card) +
              (∑ σOut ∈ TauNotTrue, (Bucket (Fx := Fx0.attach) sigOut σOut).card) := hsum_split_true
        _ = (∑ σOut ∈ TauTrue, (Bucket (Fx := Fx0.attach) sigOut σOut).card) +
              ((∑ σOut ∈ TauNotTrueCoreMore, (Bucket (Fx := Fx0.attach) sigOut σOut).card) +
                (∑ σOut ∈ TauNotTrueRigid, (Bucket (Fx := Fx0.attach) sigOut σOut).card)) := by
              rw [hsum_split_core]
        _ = (∑ σOut ∈ TauTrue, (Bucket (Fx := Fx0.attach) sigOut σOut).card) +
              (∑ σOut ∈ TauNotTrueCoreMore, (Bucket (Fx := Fx0.attach) sigOut σOut).card) +
                (∑ σOut ∈ TauNotTrueRigid, (Bucket (Fx := Fx0.attach) sigOut σOut).card) := by
              exact (Nat.add_assoc _ _ _).symm
    -- Apply the three bounds and rewrite the seams.
    calc
      Fx0.card =
          (∑ σOut ∈ TauTrue, (Bucket (Fx := Fx0.attach) sigOut σOut).card) +
            (∑ σOut ∈ TauNotTrueCoreMore, (Bucket (Fx := Fx0.attach) sigOut σOut).card) +
              (∑ σOut ∈ TauNotTrueRigid, (Bucket (Fx := Fx0.attach) sigOut σOut).card) := hsum_all
      _ ≤ (TauTrue.card * C + BadNoneAgg_perXSignatureOutMore (Fx0 := Fx0) sigOut X h0) +
            (BadCoreNotTrueAgg_perXSignatureOutMore (Fx0 := Fx0) sigOut) +
              (TauNotTrueRigid.card * capNotTrue) := by
            exact Nat.add_le_add (Nat.add_le_add hTrueSum (le_of_eq hCoreAgg)) hRigidSum
      _ = TauTrue.card * C + TauNotTrueRigid.card * capNotTrue +
            BadAgg_perXSignatureOutMore (Fx0 := Fx0) sigOut X h0 := by
            -- Reassociate and fold the seam terms into `BadAgg`.
            -- `BadAgg = BadNoneAgg + BadCoreNotTrueAgg`.
            -- Avoid `simp` with commutativity/associativity lemmas (heartbeat-expensive).
            rw [BadAgg_perXSignatureOutMore]
            -- Normalize LHS: `((A + B) + C) + D` into `A + D + (B + C)`.
            rw [Nat.add_assoc (TauTrue.card * C + BadNoneAgg_perXSignatureOutMore (Fx0 := Fx0) sigOut X h0)
              (BadCoreNotTrueAgg_perXSignatureOutMore (Fx0 := Fx0) sigOut)
              (TauNotTrueRigid.card * capNotTrue)]
            rw [Nat.add_assoc (TauTrue.card * C)
              (BadNoneAgg_perXSignatureOutMore (Fx0 := Fx0) sigOut X h0)
              (BadCoreNotTrueAgg_perXSignatureOutMore (Fx0 := Fx0) sigOut +
                TauNotTrueRigid.card * capNotTrue)]
            rw [(Nat.add_assoc (BadNoneAgg_perXSignatureOutMore (Fx0 := Fx0) sigOut X h0)
              (BadCoreNotTrueAgg_perXSignatureOutMore (Fx0 := Fx0) sigOut)
              (TauNotTrueRigid.card * capNotTrue)).symm]
            rw [Nat.add_comm (BadNoneAgg_perXSignatureOutMore (Fx0 := Fx0) sigOut X h0 +
              BadCoreNotTrueAgg_perXSignatureOutMore (Fx0 := Fx0) sigOut)
              (TauNotTrueRigid.card * capNotTrue)]
            -- Finish by associativity on the outer `A`.
            rw [(Nat.add_assoc (TauTrue.card * C) (TauNotTrueRigid.card * capNotTrue)
              (BadNoneAgg_perXSignatureOutMore (Fx0 := Fx0) sigOut X h0 +
                BadCoreNotTrueAgg_perXSignatureOutMore (Fx0 := Fx0) sigOut)).symm]
  exact hmain

/-- Corollary: under `BadAgg = 0`, the seam disappears from the outMore bucket wiring bound. -/
theorem card_Fx0_le_tauTrue_mul_add_tauNotTrueRigid_mul_of_badAgg_eq_zero
    {α : Type*} [DecidableEq α]
    {dom : Finset (Finset α)} (Fx0 : Finset {S // S ∈ dom})
    (sigOut : {Ssub // Ssub ∈ Fx0} → PerXSignatureOutMore α)
    (X : Finset α) (h0 : α) (C capNotTrue : ℕ)
    (hTauTrue :
      let sigOutImage : Finset (PerXSignatureOutMore α) := Fx0.attach.image sigOut
      let TauTrue : Finset (PerXSignatureOutMore α) :=
        by
          classical
          exact
            sigOutImage.filter (fun σOut =>
              match σOut.2.1 with
              | some (_t1, _t2, _t3, _t4, _t5, true) => True
              | _ => False)
      ∀ σOut ∈ TauTrue,
        (Bucket (Fx := Fx0.attach) sigOut σOut).card ≤
          C + (BadNoneOf_perXSignatureOutMore (Fx0 := Fx0) sigOut σOut X h0).card)
    (hTauNotTrueRigid :
      let sigOutImage : Finset (PerXSignatureOutMore α) := Fx0.attach.image sigOut
      let TauNotTrue : Finset (PerXSignatureOutMore α) :=
        by
          classical
          exact
            sigOutImage.filter (fun σOut =>
              match σOut.2.1 with
              | some (_t1, _t2, _t3, _t4, _t5, true) => False
              | _ => True)
      let TauNotTrueRigid : Finset (PerXSignatureOutMore α) :=
        by
          classical
          exact
            TauNotTrue.filter (fun σOut =>
              ¬ CoreMore_perXSignatureOutMore (α := α) σOut)
      ∀ σOut ∈ TauNotTrueRigid, (Bucket (Fx := Fx0.attach) sigOut σOut).card ≤ capNotTrue)
    (hBad :
      BadAgg_perXSignatureOutMore (Fx0 := Fx0) sigOut X h0 = 0) :
    let sigOutImage : Finset (PerXSignatureOutMore α) := Fx0.attach.image sigOut
    let TauTrue : Finset (PerXSignatureOutMore α) :=
      by
        classical
        exact
          sigOutImage.filter (fun σOut =>
            match σOut.2.1 with
            | some (_t1, _t2, _t3, _t4, _t5, true) => True
            | _ => False)
    let TauNotTrue : Finset (PerXSignatureOutMore α) :=
      by
        classical
        exact
          sigOutImage.filter (fun σOut =>
            match σOut.2.1 with
            | some (_t1, _t2, _t3, _t4, _t5, true) => False
            | _ => True)
    let TauNotTrueCoreMore : Finset (PerXSignatureOutMore α) :=
      by
        classical
        exact
          TauNotTrue.filter (fun σOut =>
            CoreMore_perXSignatureOutMore (α := α) σOut)
    let TauNotTrueRigid : Finset (PerXSignatureOutMore α) :=
      by
        classical
        exact
          TauNotTrue.filter (fun σOut =>
            ¬ CoreMore_perXSignatureOutMore (α := α) σOut)
    Fx0.card ≤ TauTrue.card * C + TauNotTrueRigid.card * capNotTrue := by
  classical
  intro sigOutImage TauTrue TauNotTrue TauNotTrueCoreMore TauNotTrueRigid
  have h :=
    card_Fx0_le_tauTrue_mul_add_tauNotTrueRigid_mul_add_badAgg
      (Fx0 := Fx0) (sigOut := sigOut) (X := X) (h0 := h0) (C := C) (capNotTrue := capNotTrue)
      hTauTrue hTauNotTrueRigid
  have h' :
      Fx0.card ≤ TauTrue.card * C + TauNotTrueRigid.card * capNotTrue + 0 := by
    simpa [sigOutImage, TauTrue, TauNotTrue, TauNotTrueCoreMore, TauNotTrueRigid, hBad] using h
  simpa using h'

/- theorem card_Bsome_filter_g_eq_mk_z_none_le_two_tauTrue_uGoodChoice
    (hreg : O1aUpgradeRegime family ground A0 h0)
    {k : WLcertKey α}
    {Sstar : {S // S ∈ o1aWitnessLiftDomWL family h0}}
    {x : α}
    (hSstar :
      Sstar ∈ wlcertAdmissibleFiber_hNotMem (family := family) (o1aWitnessLiftDomWL family h0) k)
    (σOut : PerXSignatureOutMore α)
    {t1 t2 t3 t4 t5 : α}
    (hτ : σOut.2.1 = some (t1, t2, t3, t4, t5, true))
    (z : α) :
    let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h0
    let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
    let Fx0 :
        Finset {S // S ∈ dom} :=
      wlcertAdmissibleFiber_hNotMem_fiberForX (dom := dom) fiber Sstar.1 x
    let Uout : {Ssub // Ssub ∈ Fx0} → Finset α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      let yw :
          Σ y : α, BlockedUnionWitness family b.1.1 y :=
        chooseYAndWitness_of_hardFiber
          (family := family) (ground := ground) (A0 := A0) (h0 := h0)
          hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
          Sstar.2 b.1.2 hcert_star hcert_sub hne
      b.1.1 \ (yw.2.A ∪ yw.2.B)
    let sig0 : {Ssub // Ssub ∈ Fx0} → PerXSignature α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      perXSignature_of_hardFiber (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1) Sstar.2 b.1.2 hcert_star hcert_sub hne
    let sigOut : {Ssub // Ssub ∈ Fx0} → PerXSignatureOutMore α := fun b =>
      (sig0 b,
        trace5PlusOfFinset (α := α) (Uout b),
        t6OptionOfTrace5Plus (α := α) (Uout b))
    let X : Finset α := ground \ (k.2.2.1 ∪ k.2.2.2.1)
    let y : α := σOut.1.1
    let B : Finset {Ssub // Ssub ∈ Fx0} := Bucket (Fx := Fx0.attach) sigOut σOut
    let Bsome : Finset {Ssub // Ssub ∈ Fx0} :=
      B.filter (fun b => zChoice (α := α) X b.1.1 y h0 ≠ none)
    let g : {Ssub // Ssub ∈ Fx0} → α × Option α := by
      classical
      exact fun b =>
        if hz : zChoice (α := α) X b.1.1 y h0 ≠ none then
          let ex : ∃ z0, zChoice (α := α) X b.1.1 y h0 = some z0 :=
            exists_z_of_zChoice_ne_none (α := α) (X := X) (S := b.1.1) (y0 := y) (h0 := h0) hz
          let z0 : α := Classical.choose ex
          (z0, (uGoodChoice (α := α) X b.1.1 y h0 z0).map (fun hu => hu.1))
        else (h0, none)
    (Bsome.filter (fun b => g b = (z, none))).card ≤ 2 := by
  classical
  intro dom fiber Fx0 Uout sig0 sigOut X y B Bsome g
  have hsub :
      (Bsome.filter (fun b => g b = (z, none))) ⊆
        (B.filter (fun b => X \ b.1.1 = ({y, z} : Finset α))) ∪
          (B.filter (fun b => X \ b.1.1 = ({y, h0, z} : Finset α))) := by
    intro b hb
    have hbBsome : b ∈ Bsome := (Finset.mem_filter.mp hb).1
    have hbB : b ∈ B := (Finset.mem_filter.mp hbBsome).1
    have hbzChoice : zChoice (α := α) X b.1.1 y h0 ≠ none := (Finset.mem_filter.mp hbBsome).2
    have hgb : g b = (z, none) := (Finset.mem_filter.mp hb).2
    -- Extract `zChoice = some z` from the definition of `g`.
    have hzEq : zChoice (α := α) X b.1.1 y h0 = some z := by
      let ex : ∃ z0, zChoice (α := α) X b.1.1 y h0 = some z0 :=
        exists_z_of_zChoice_ne_none (α := α) (X := X) (S := b.1.1) (y0 := y) (h0 := h0) hbzChoice
      have hg :
          g b =
            (Classical.choose ex,
              (uGoodChoice (α := α) X b.1.1 y h0 (Classical.choose ex)).map (fun hu => hu.1)) := by
        simp [g, hbzChoice, ex]
      have hzEq' : Classical.choose ex = z := by
        have := congrArg Prod.fst (hg.symm.trans hgb)
        simpa using this
      have hzSpec : zChoice (α := α) X b.1.1 y h0 = some (Classical.choose ex) :=
        Classical.choose_spec ex
      simpa [hzEq'] using hzSpec
    -- Extract `uGoodChoice.map = none` from the second component.
    have huMap :
        (uGoodChoice (α := α) X b.1.1 y h0 z).map (fun hu => hu.1) = none := by
      let ex : ∃ z0, zChoice (α := α) X b.1.1 y h0 = some z0 :=
        exists_z_of_zChoice_ne_none (α := α) (X := X) (S := b.1.1) (y0 := y) (h0 := h0) hbzChoice
      have hg :
          g b =
            (Classical.choose ex,
              (uGoodChoice (α := α) X b.1.1 y h0 (Classical.choose ex)).map (fun hu => hu.1)) := by
        simp [g, hbzChoice, ex]
      have hzEq' : Classical.choose ex = z := by
        have := congrArg Prod.fst (hg.symm.trans hgb)
        simpa using this
      have huMap0 :
          (uGoodChoice (α := α) X b.1.1 y h0 (Classical.choose ex)).map (fun hu => hu.1) = none := by
        have := congrArg Prod.snd (hg.symm.trans hgb)
        simpa using this
      -- Rewrite the last argument from `Classical.choose ex` to `z`.
      have huMap1 := huMap0
      rw [hzEq'] at huMap1
      exact huMap1
    have hUG : uGoodChoice (α := α) X b.1.1 y h0 z = none := by
      cases hUG : uGoodChoice (α := α) X b.1.1 y h0 z with
      | none => rfl
      | some hu =>
          -- Impossible: `map` of `some` is `some`.
          simp [hUG] at huMap
    -- Show `y ∈ X \\ b` using the bucket-fixed signature (same as in the `some u` lemma).
    have hbSig : sigOut b = σOut := (Finset.mem_filter.mp hbB).2
    have hySig : (sig0 b).1 = y := by
      have : (sigOut b).1.1 = σOut.1.1 := by simpa [hbSig]
      simpa [sigOut] using this
    have hbFiber : b.1 ∈ fiber := (Finset.mem_filter.mp b.2).1
    have hcert_sub :
        ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
      (Finset.mem_filter.mp hbFiber).2
    have hcert_star :
        ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
      (Finset.mem_filter.mp hSstar).2
    have hne : b.1.1 ≠ Sstar.1 :=
      ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
        (Ssub := b.1) b.2
    let yCh : α :=
      chooseMissingFromRef (family := family) (h0 := h0) Sstar.1 b.1.1 Sstar.2 b.1.2 hne
    have hyChSig0 : (sig0 b).1 = yCh := by
      simp [sig0, perXSignature_of_hardFiber, perXSignature, chooseYAndWitness_of_hardFiber, yCh]
    have hyEq : yCh = y := by simpa [hyChSig0] using hySig
    have hyXCh : yCh ∈ X := by
      have hyX' :
          yCh ∈ (ground \ (k.2.2.1 ∪ k.2.2.2.1)) := by
        simpa [yCh] using
          (chooseMissingFromRef_mem_X_of_hardFiber (family := family) (ground := ground) (A0 := A0)
            (h0 := h0) hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
            Sstar.2 b.1.2 hcert_star hcert_sub hne)
      simpa [X] using hyX'
    have hyNotCh : yCh ∉ b.1.1 := by
      have hyDiff :
          yCh ∈ Sstar.1 \ b.1.1 := by
        simpa [yCh] using
          (chooseMissingFromRef_spec (family := family) (h0 := h0) Sstar.1 b.1.1
            Sstar.2 b.1.2 hne)
      exact (Finset.mem_sdiff.mp hyDiff).2
    have hy : y ∈ X \ b.1.1 := by
      have : yCh ∈ X \ b.1.1 := Finset.mem_sdiff.mpr ⟨hyXCh, hyNotCh⟩
      simpa [hyEq] using this
    -- Split `uGoodChoice = none` into good-none (`Z2 = ∅`) vs bad-none (`Z2.Nonempty` but not singleton).
    let Z2 : Finset α := ((((X \ b.1.1).erase y).erase h0).erase z)
    by_cases hZ2 : Z2 = (∅ : Finset α)
    · -- good-none: collapse via the existing pair/triple missing-set lemma.
      have huNone : uChoice (α := α) X b.1.1 y h0 z = none := by
        exact (uChoice_eq_none_iff (α := α) (X := X) (S := b.1.1) (y0 := y) (h0 := h0) (z := z)).2 hZ2
      have hXcase :
          X \ b.1.1 = ({y, z} : Finset α) ∨ X \ b.1.1 = ({y, h0, z} : Finset α) :=
        X_sdiff_eq_pair_or_triple_of_uChoice_eq_none (α := α) (X := X) (S := b.1.1)
          (y0 := y) (h0 := h0) (z := z) hy hzEq huNone
      rcases hXcase with hPair | hTrip
      · refine Finset.mem_union.mpr (Or.inl ?_)
        exact Finset.mem_filter.mpr ⟨hbB, hPair⟩
      · refine Finset.mem_union.mpr (Or.inr ?_)
        exact Finset.mem_filter.mpr ⟨hbB, hTrip⟩
    · -- bad-none: `Z2` is nonempty but `uGoodChoice` failed to certify singleton.
      have hZ2ne : Z2.Nonempty := by
        classical
        exact Finset.nonempty_iff_ne_empty.2 hZ2
      -- Time-boxed attempt: kill this branch using only existing hard-fiber one-step blocked-extension facts.
      -- If this doesn't collapse quickly, hard stop and re-plan.
      have : False := by
        -- TODO: show this subbucket is empty (contract gap if not).
        exact ?_
      exact False.elim this
  have hcard_sub :
      (Bsome.filter (fun b => g b = (z, none))).card ≤
        ((B.filter (fun b => X \ b.1.1 = ({y, z} : Finset α))) ∪
              (B.filter (fun b => X \ b.1.1 = ({y, h0, z} : Finset α)))).card :=
    Finset.card_le_card hsub
  have hcard1 :
      (B.filter (fun b => X \ b.1.1 = ({y, z} : Finset α))).card ≤ 1 := by
    simpa [X] using
      (card_Bucket_perXSignatureOutMore_filter_X_sdiff_eq_pair_le_one (family := family)
        (ground := ground) (A0 := A0) (h0 := h0) hreg (k := k) (Sstar := Sstar) (x := x)
        hSstar (σOut := σOut) (y1 := y) (y2 := z))
  have hcard2 :
      (B.filter (fun b => X \ b.1.1 = ({y, h0, z} : Finset α))).card ≤ 1 := by
    simpa [X] using
      (card_Bucket_perXSignatureOutMore_filter_X_sdiff_eq_triple_le_one (family := family)
        (ground := ground) (A0 := A0) (h0 := h0) hreg (k := k) (Sstar := Sstar) (x := x)
        hSstar (σOut := σOut) (y1 := y) (y2 := h0) (y3 := z))
  have hcard_union :
      ((B.filter (fun b => X \ b.1.1 = ({y, z} : Finset α))) ∪
            (B.filter (fun b => X \ b.1.1 = ({y, h0, z} : Finset α)))).card ≤ 2 := by
    have hsum :
        ((B.filter (fun b => X \ b.1.1 = ({y, z} : Finset α))) ∪
              (B.filter (fun b => X \ b.1.1 = ({y, h0, z} : Finset α)))).card ≤
          (B.filter (fun b => X \ b.1.1 = ({y, z} : Finset α))).card +
            (B.filter (fun b => X \ b.1.1 = ({y, h0, z} : Finset α))).card := by
      simpa using
        (Finset.card_union_le (B.filter (fun b => X \ b.1.1 = ({y, z} : Finset α)))
          (B.filter (fun b => X \ b.1.1 = ({y, h0, z} : Finset α))))
    calc
      ((B.filter (fun b => X \ b.1.1 = ({y, z} : Finset α))) ∪
              (B.filter (fun b => X \ b.1.1 = ({y, h0, z} : Finset α)))).card
          ≤ (B.filter (fun b => X \ b.1.1 = ({y, z} : Finset α))).card +
              (B.filter (fun b => X \ b.1.1 = ({y, h0, z} : Finset α))).card := hsum
      _ ≤ 1 + 1 := Nat.add_le_add hcard1 hcard2
      _ = 2 := by simp
  exact le_trans hcard_sub hcard_union
-/


/-!
Helper for the `zChoice ≠ none` bounded-fiber cap:
for a fixed `z` and `u`, the `g`-fiber at `(z, some u)` has card ≤ 2 *provided*
we can show there is **no third missing element** beyond `y,h0,z,u`.

This isolates the exact “no further missing” obligation that must be discharged
in the `uChoice = some u` branch.
-/

theorem card_Bsome_filter_g_eq_mk_z_some_u_le_two
    (hreg : O1aUpgradeRegime family ground A0 h0)
    {k : WLcertKey α}
    {Sstar : {S // S ∈ o1aWitnessLiftDomWL family h0}}
    {x : α}
    (hSstar :
      Sstar ∈ wlcertAdmissibleFiber_hNotMem (family := family) (o1aWitnessLiftDomWL family h0) k)
    (σOut : PerXSignatureOutMore α)
    (z u : α) :
    let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h0
    let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
    let Fx0 :
        Finset {S // S ∈ dom} :=
      wlcertAdmissibleFiber_hNotMem_fiberForX (dom := dom) fiber Sstar.1 x
    let Uout : {Ssub // Ssub ∈ Fx0} → Finset α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      let yw :
          Σ y : α, BlockedUnionWitness family b.1.1 y :=
        chooseYAndWitness_of_hardFiber
          (family := family) (ground := ground) (A0 := A0) (h0 := h0)
          hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
          Sstar.2 b.1.2 hcert_star hcert_sub hne
      b.1.1 \ (yw.2.A ∪ yw.2.B)
    let sig0 : {Ssub // Ssub ∈ Fx0} → PerXSignature α := fun b =>
      let hcert_star :
          ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hSstar).2
      have hbFiber : b.1 ∈ fiber := by
        classical
        exact (Finset.mem_filter.mp b.2).1
      have hcert_sub :
          ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
        by
          classical
          exact (Finset.mem_filter.mp hbFiber).2
      have hne : b.1.1 ≠ Sstar.1 :=
        ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      perXSignature_of_hardFiber (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1) Sstar.2 b.1.2 hcert_star hcert_sub hne
    let sigOut : {Ssub // Ssub ∈ Fx0} → PerXSignatureOutMore α := fun b =>
      (sig0 b,
        trace5PlusOfFinset (α := α) (Uout b),
        t6OptionOfTrace5Plus (α := α) (Uout b))
    let X : Finset α := ground \ (k.2.2.1 ∪ k.2.2.2.1)
    let y : α := σOut.1.1
    let B : Finset {Ssub // Ssub ∈ Fx0} := Bucket (Fx := Fx0.attach) sigOut σOut
    let Bsome : Finset {Ssub // Ssub ∈ Fx0} :=
      B.filter (fun b => zChoice (α := α) X b.1.1 y h0 ≠ none)
    let g : {Ssub // Ssub ∈ Fx0} → α × Option α := by
      classical
      exact fun b =>
        if hz : zChoice (α := α) X b.1.1 y h0 ≠ none then
          let ex : ∃ z, zChoice (α := α) X b.1.1 y h0 = some z :=
            exists_z_of_zChoice_ne_none (α := α) (X := X) (S := b.1.1) (y0 := y) (h0 := h0) hz
          let z : α := Classical.choose ex
          (z, (uGoodChoice (α := α) X b.1.1 y h0 z).map (fun hu => hu.1))
        else (h0, none)
    (Bsome.filter (fun b => g b = (z, some u))).card ≤ 2 := by
  classical
  intro dom fiber Fx0 Uout sig0 sigOut X y B Bsome g
  -- Reduce to the triple/quad missing-set buckets.
  have hsub :
      (Bsome.filter (fun b => g b = (z, some u))) ⊆
        (B.filter (fun b => X \ b.1.1 = ({y, z, u} : Finset α))) ∪
          (B.filter (fun b => X \ b.1.1 = ({y, h0, z, u} : Finset α))) := by
    intro b hb
    have hbBsome : b ∈ Bsome := (Finset.mem_filter.mp hb).1
    have hbB : b ∈ B := (Finset.mem_filter.mp hbBsome).1
    have hbzChoice : zChoice (α := α) X b.1.1 y h0 ≠ none := (Finset.mem_filter.mp hbBsome).2
    have hgb : g b = (z, some u) := (Finset.mem_filter.mp hb).2
    -- Extract `zChoice = some z` from the definition of `g`.
    have hzEq : zChoice (α := α) X b.1.1 y h0 = some z := by
      let ex : ∃ z0, zChoice (α := α) X b.1.1 y h0 = some z0 :=
        exists_z_of_zChoice_ne_none (α := α) (X := X) (S := b.1.1) (y0 := y) (h0 := h0) hbzChoice
      have : g b =
          (Classical.choose ex,
            (uGoodChoice (α := α) X b.1.1 y h0 (Classical.choose ex)).map (fun hu => hu.1)) := by
        simp [g, hbzChoice]
      have hzEq' : Classical.choose ex = z := by
        have := congrArg Prod.fst (this.symm.trans hgb)
        simpa using this
      have hzSpec : zChoice (α := α) X b.1.1 y h0 = some (Classical.choose ex) :=
        Classical.choose_spec ex
      simpa [hzEq'] using hzSpec
    -- Extract the `uGoodChoice` witness from the second component.
    have huMap :
        (uGoodChoice (α := α) X b.1.1 y h0 z).map (fun hu => hu.1) = some u := by
      -- Use the same `Classical.choose` witness as in `g`, then rewrite it to the fixed `z`.
      let ex : ∃ z0, zChoice (α := α) X b.1.1 y h0 = some z0 :=
        exists_z_of_zChoice_ne_none (α := α) (X := X) (S := b.1.1) (y0 := y) (h0 := h0) hbzChoice
      have hg :
          g b =
            (Classical.choose ex,
              (uGoodChoice (α := α) X b.1.1 y h0 (Classical.choose ex)).map (fun hu => hu.1)) := by
        simp [g, hbzChoice]
      have hzEq' : Classical.choose ex = z := by
        have := congrArg Prod.fst (hg.symm.trans hgb)
        simpa using this
      have huMap0 :
          (uGoodChoice (α := α) X b.1.1 y h0 (Classical.choose ex)).map (fun hu => hu.1) = some u := by
        have := congrArg Prod.snd (hg.symm.trans hgb)
        simpa using this
      -- Rewrite the last argument from `Classical.choose ex` to the fixed `z`.
      have huMap1 := huMap0
      rw [hzEq'] at huMap1
      exact huMap1
    have huSome :
        ∃ hu, uGoodChoice (α := α) X b.1.1 y h0 z = some hu ∧ hu.1 = u := by
      classical
      cases hUG : uGoodChoice (α := α) X b.1.1 y h0 z with
      | none =>
          -- Impossible: the second component of `g b = (z, some u)` is `some u`.
          simp [hUG] at huMap
      | some hu =>
          have : (some hu.1 : Option α) = some u := by
            simpa [hUG] using huMap
          exact ⟨hu, rfl, Option.some.inj this⟩
    rcases huSome with ⟨hu, hhu, hu1Eq⟩
    have huMem : u ∈ ((((X \ b.1.1).erase y).erase h0).erase z) := by
      simpa [hu1Eq] using hu.2.1
    have hZ3 :
        ((((((X \ b.1.1).erase y).erase h0).erase z).erase u) = (∅ : Finset α)) := by
      simpa [hu1Eq] using hu.2.2
    -- Recover `y ∈ X \\ b` from the bucket-fixed signature.
    have hbSig : sigOut b = σOut := (Finset.mem_filter.mp hbB).2
    have hSig11 : (sigOut b).1.1 = σOut.1.1 :=
      congrArg (fun t => t.1.1) hbSig
    have hySig : (sig0 b).1 = y := by
      simpa [sigOut, y] using hSig11
    have hbFiber : b.1 ∈ fiber := (Finset.mem_filter.mp b.2).1
    have hcert_sub :
        ∃ cert : WLcert family b.1.1, WLcert.key cert = k ∧ cert.h ∉ b.1.1 :=
      (Finset.mem_filter.mp hbFiber).2
    have hcert_star :
        ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
      (Finset.mem_filter.mp hSstar).2
    have hne : b.1.1 ≠ Sstar.1 :=
      ne_Sstar_val_of_mem_fiberForX (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
        (Ssub := b.1) b.2
    let yCh : α :=
      chooseMissingFromRef (family := family) (h0 := h0) Sstar.1 b.1.1 Sstar.2 b.1.2 hne
    have hyChSig0 : (sig0 b).1 = yCh := by
      unfold yCh
      simp only [sig0, perXSignature_of_hardFiber, perXSignature, chooseYAndWitness_of_hardFiber]
    have hyEq : yCh = y := hyChSig0.symm.trans hySig
    have hyXCh : yCh ∈ X := by
      have hyX' :
          yCh ∈ (ground \ (k.2.2.1 ∪ k.2.2.2.1)) := by
        simpa [yCh] using
          (chooseMissingFromRef_mem_X_of_hardFiber (family := family) (ground := ground) (A0 := A0)
            (h0 := h0) hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
            Sstar.2 b.1.2 hcert_star hcert_sub hne)
      simpa [X] using hyX'
    have hyNotCh : yCh ∉ b.1.1 := by
      have hyDiff :
          yCh ∈ Sstar.1 \ b.1.1 := by
        simpa [yCh] using
          (chooseMissingFromRef_spec (family := family) (h0 := h0) Sstar.1 b.1.1
            Sstar.2 b.1.2 hne)
      exact (Finset.mem_sdiff.mp hyDiff).2
    have hy : y ∈ X \ b.1.1 := by
      have : yCh ∈ X \ b.1.1 := Finset.mem_sdiff.mpr ⟨hyXCh, hyNotCh⟩
      simpa [hyEq] using this
    -- Apply the triple/quad collapse lemma using the `uGoodChoice` witness.
    have hXcase :
        X \ b.1.1 = ({y, z, u} : Finset α) ∨ X \ b.1.1 = ({y, h0, z, u} : Finset α) :=
      X_sdiff_eq_triple_or_quad_of_mem_of_erase_u_eq_empty (α := α)
        (X := X) (S := b.1.1) (y0 := y) (h0 := h0) (z := z) (u := u)
        hy hzEq huMem hZ3
    rcases hXcase with hTrip | hQuad
    · refine Finset.mem_union.mpr (Or.inl ?_)
      exact Finset.mem_filter.mpr ⟨hbB, hTrip⟩
    · refine Finset.mem_union.mpr (Or.inr ?_)
      exact Finset.mem_filter.mpr ⟨hbB, hQuad⟩
  have hcard_sub :
      (Bsome.filter (fun b => g b = (z, some u))).card ≤
        ((B.filter (fun b => X \ b.1.1 = ({y, z, u} : Finset α))) ∪
            (B.filter (fun b => X \ b.1.1 = ({y, h0, z, u} : Finset α)))).card :=
    Finset.card_le_card hsub
  have hcard1 :
      (B.filter (fun b => X \ b.1.1 = ({y, z, u} : Finset α))).card ≤ 1 := by
    simpa [X] using
      (card_Bucket_perXSignatureOutMore_filter_X_sdiff_eq_triple_le_one (family := family)
        (ground := ground) (A0 := A0) (h0 := h0) hreg (k := k) (Sstar := Sstar) (x := x)
        hSstar (σOut := σOut) (y1 := y) (y2 := z) (y3 := u))
  have hcard2 :
      (B.filter (fun b => X \ b.1.1 = ({y, h0, z, u} : Finset α))).card ≤ 1 := by
    simpa [X] using
      (card_Bucket_perXSignatureOutMore_filter_X_sdiff_eq_quad_le_one (family := family)
        (ground := ground) (A0 := A0) (h0 := h0) hreg (k := k) (Sstar := Sstar) (x := x)
        hSstar (σOut := σOut) (y1 := y) (y2 := h0) (y3 := z) (y4 := u))
  have hcard_union :
      ((B.filter (fun b => X \ b.1.1 = ({y, z, u} : Finset α))) ∪
            (B.filter (fun b => X \ b.1.1 = ({y, h0, z, u} : Finset α)))).card ≤ 2 := by
    have hsum :
        ((B.filter (fun b => X \ b.1.1 = ({y, z, u} : Finset α))) ∪
              (B.filter (fun b => X \ b.1.1 = ({y, h0, z, u} : Finset α)))).card ≤
          (B.filter (fun b => X \ b.1.1 = ({y, z, u} : Finset α))).card +
            (B.filter (fun b => X \ b.1.1 = ({y, h0, z, u} : Finset α))).card := by
      simpa using
        (Finset.card_union_le (B.filter (fun b => X \ b.1.1 = ({y, z, u} : Finset α)))
          (B.filter (fun b => X \ b.1.1 = ({y, h0, z, u} : Finset α))))
    calc
      ((B.filter (fun b => X \ b.1.1 = ({y, z, u} : Finset α))) ∪
              (B.filter (fun b => X \ b.1.1 = ({y, h0, z, u} : Finset α)))).card
          ≤ (B.filter (fun b => X \ b.1.1 = ({y, z, u} : Finset α))).card +
              (B.filter (fun b => X \ b.1.1 = ({y, h0, z, u} : Finset α))).card := hsum
      _ ≤ 1 + 1 := Nat.add_le_add hcard1 hcard2
      _ = 2 := by simp
  exact le_trans hcard_sub hcard_union

end PerXBucketBounds

end PerXSubfiber

end PerXSubfiber
end SunflowerLean
