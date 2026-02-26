import SunflowerLean.BalanceCore

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

end SunflowerLean
