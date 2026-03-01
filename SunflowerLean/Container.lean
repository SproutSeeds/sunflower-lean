import SunflowerLean.Balance

namespace SunflowerLean

/-- Container collection covers all k-sunflower-free families on a ground set. -/
def IsContainerCollection {α : Type*} [DecidableEq α]
    (containers : Finset (Finset (Finset α))) (ground : Finset α) (k : ℕ) : Prop :=
  ∀ (family : Finset (Finset α)),
    IsSunflowerFree family k →
    IsOnGround family ground →
    ∃ C ∈ containers, family ⊆ C

/-- NAT-safe density-gap style conjecture (ratio-free). -/
def ContainerDensityGapConjectureNat {α : Type*} [DecidableEq α] : Prop :=
  ∀ (ground : Finset α),
    ∃ (containers : Finset (Finset (Finset α))) (gap : ℕ),
      0 < gap ∧
      IsContainerCollection containers ground 3 ∧
      ∀ C ∈ containers, C.card * 2 ^ gap ≤ 2 ^ ground.card

/-- Unpacks the bounded-container consequence of the conjecture at a fixed ground set. -/
theorem container_density_gap_consequence {α : Type*} [DecidableEq α]
    (ground : Finset α) :
    ContainerDensityGapConjectureNat (α := α) →
    ∃ (containers : Finset (Finset (Finset α))) (gap : ℕ),
      0 < gap ∧
      IsContainerCollection containers ground 3 ∧
      ∀ C ∈ containers, C.card * 2 ^ gap ≤ 2 ^ ground.card := by
  intro h
  exact h ground

/-- Obstruction witness: the current `ContainerDensityGapConjectureNat` shape
is false on a one-point ground set (`Fin 1`). On this ground, the full
power-set family has size `2`, so any covering container must have cardinality
at least `2`; with `gap > 0`, the bound `C.card * 2^gap ≤ 2^|ground| = 2`
cannot hold. -/
theorem not_container_density_gap_conjecture_nat_fin1 :
    ¬ ContainerDensityGapConjectureNat (α := Fin 1) := by
  intro hconj
  let ground : Finset (Fin 1) := Finset.univ
  rcases container_density_gap_consequence (α := Fin 1) ground hconj with
    ⟨containers, gap, hgap_pos, hcover, hbound⟩
  let fullFam : Finset (Finset (Fin 1)) := Finset.univ
  have hfull_on_ground : IsOnGround fullFam ground := by
    intro S _hS
    exact Finset.subset_univ S
  have hfull_sf_free : IsSunflowerFree fullFam 3 := by
    intro sub hsub hsun
    have hle : sub.card ≤ fullFam.card := Finset.card_le_card hsub
    have hfull_card : fullFam.card = 2 := by
      simp [fullFam]
    rcases hsun with ⟨hcard, _⟩
    have : ¬ (3 ≤ 2) := by decide
    exact this (by simpa [hcard, hfull_card] using hle)
  rcases hcover fullFam hfull_sf_free hfull_on_ground with ⟨C, hCmem, hfull_sub_C⟩
  have hfull_card : fullFam.card = 2 := by
    simp [fullFam]
  have hC_ge2 : 2 ≤ C.card := by
    have hle : fullFam.card ≤ C.card := Finset.card_le_card hfull_sub_C
    simpa [hfull_card] using hle
  have hgap_ge1 : 1 ≤ gap := Nat.succ_le_of_lt hgap_pos
  have hpow_ge2 : 2 ≤ 2 ^ gap := by
    calc
      2 = 2 ^ 1 := by simp
      _ ≤ 2 ^ gap := Nat.pow_le_pow_right (by decide) hgap_ge1
  have hCbound : C.card * 2 ^ gap ≤ 2 ^ ground.card := hbound C hCmem
  have hground_pow : 2 ^ ground.card = 2 := by
    simp [ground]
  have hmul_ge4 : 4 ≤ C.card * 2 ^ gap := by
    have hmul_ge : 2 * 2 ≤ C.card * 2 ^ gap :=
      Nat.mul_le_mul hC_ge2 hpow_ge2
    simpa using hmul_ge
  have h4_le_2 : 4 ≤ 2 := by
    calc
      4 ≤ C.card * 2 ^ gap := hmul_ge4
      _ ≤ 2 ^ ground.card := hCbound
      _ = 2 := hground_pow
  exact (by decide : ¬ (4 ≤ 2)) h4_le_2

end SunflowerLean
