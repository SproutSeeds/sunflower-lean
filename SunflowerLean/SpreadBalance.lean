import SunflowerLean.Balance
import SunflowerLean.Spread

namespace SunflowerLean

/-- Spread families give a coordinate-degree upper bound at every element. -/
theorem spread_implies_coordDegree_upper {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (r : ℕ) (i : α) :
    IsRSpread family r →
    coordDegree family i * r ≤ family.card := by
  intro hspread
  simpa [coordDegree, Nat.mul_comm] using spread_singleton family r hspread i

/-- Bridge: if spread fails, reuse the heavy-subset witness from `Spread`. -/
theorem non_spread_implies_heavy_subset_bridge {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (r : ℕ) :
    r > 0 →
    family.Nonempty →
    ¬ IsRSpread family r →
    ∃ Z : Finset α, (family.filter (fun S => Z ⊆ S)).card * r ^ Z.card > family.card := by
  intro hr hne hnot
  exact not_spread_implies_heavy_subset family r hr hne hnot

end SunflowerLean
