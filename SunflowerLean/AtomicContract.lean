import SunflowerLean.Erdos367
import SunflowerLean.ErdosProblem20

/-!
# Atomic Contract Completion Schema

Cross-route contract wiring used by the relief-aligned gateboard:
- Problem 367 transfer route (`LargeTwoFullPartRarity_transfer_sharpened`)
- Problem 857 split guarded-frequency packager route
- Problem 20 rank-5/6 unifier route
-/

/-- Problem-367 route leaf as a reusable contract type. -/
def Problem367TransferSharpenedContract : Prop :=
  ∀ {Cexact Clegacy : ℕ},
    Cexact ≤ Clegacy →
    (∀ n T : ℕ, n ≥ 1 → T ≥ 1 →
      (Finset.Icc 1 n |>.filter (fun m => Nat.twoFullPartExactOnce m > T)).card
        ≤ Cexact * n / T) →
    ∀ n T : ℕ, n ≥ 1 → T ≥ 1 →
      (Finset.Icc 1 n |>.filter (fun m => Nat.twoFullPart m > T)).card
        ≤ Clegacy * n / T

/-- Problem-857 route leaf as a reusable contract type. -/
def Problem857SplitNoFreqContract : Prop :=
  ∀ {α : Type} [DecidableEq α],
    NoLowFreqGuarded (α := α) →
    NoHighFreqGuarded (α := α) →
    LowCaseCountingBoundSmallGuarded (α := α) ∧
      LowCaseUniformDecompositionHypGuarded (α := α) ∧
      HighCaseCountingBoundSmallGuarded (α := α) ∧
      HighCaseUniformDecompositionHypGuarded (α := α)

/-- Problem-20 route leaf as a reusable contract type. -/
def Problem20Rank56UnifierContract : Prop :=
  UniformBoundF5Global → UniformBoundF6Global → UniformBoundRGlobalUnifier_5_6

/-- Master atomic map node across the three active route leaves. -/
def AtomicContractCompletionSchema : Prop :=
  Problem367TransferSharpenedContract ∧
    Problem857SplitNoFreqContract ∧
    Problem20Rank56UnifierContract

/-- Generic closure theorem: route-level components assemble the master schema. -/
theorem atomic_contract_completion_schema_of_components
    (h367 : Problem367TransferSharpenedContract)
    (h857 : Problem857SplitNoFreqContract)
    (h20 : Problem20Rank56UnifierContract) :
    AtomicContractCompletionSchema :=
  ⟨h367, h857, h20⟩

/-- Schema projection: recover the Problem 367 transfer route. -/
theorem largeTwoFullPartRarity_transfer_sharpened_of_atomic_schema
    (h : AtomicContractCompletionSchema) :
    Problem367TransferSharpenedContract :=
  h.1

/-- Schema projection: recover the Problem 857 split guarded-frequency
packager route. -/
theorem guarded_lane_bounds_of_split_noFreqGuarded_contract_of_atomic_schema
    (h : AtomicContractCompletionSchema) :
    Problem857SplitNoFreqContract :=
  h.2.1

/-- Schema projection: recover the Problem 20 rank-5/6 unifier route
contract. -/
theorem uniform_bound_r_global_unifier_5_6_contract_of_atomic_schema
    (h : AtomicContractCompletionSchema) :
    Problem20Rank56UnifierContract :=
  h.2.2

/-- Problem 367 instantiation from the master schema. -/
theorem problem367_route_of_atomic_schema
    (h : AtomicContractCompletionSchema) :
    Problem367TransferSharpenedContract :=
  largeTwoFullPartRarity_transfer_sharpened_of_atomic_schema h

/-- Problem 857 instantiation from the master schema. -/
theorem problem857_route_of_atomic_schema
    (h : AtomicContractCompletionSchema)
    {α : Type} [DecidableEq α]
    (hlow : NoLowFreqGuarded (α := α))
    (hhigh : NoHighFreqGuarded (α := α)) :
    LowCaseCountingBoundSmallGuarded (α := α) ∧
      LowCaseUniformDecompositionHypGuarded (α := α) ∧
      HighCaseCountingBoundSmallGuarded (α := α) ∧
      HighCaseUniformDecompositionHypGuarded (α := α) := by
  exact (guarded_lane_bounds_of_split_noFreqGuarded_contract_of_atomic_schema h)
    hlow hhigh

/-- Problem 20 instantiation from the master schema. -/
theorem problem20_route_of_atomic_schema
    (h : AtomicContractCompletionSchema)
    (h5 : UniformBoundF5Global)
    (h6 : UniformBoundF6Global) :
    UniformBoundRGlobalUnifier_5_6 := by
  exact (uniform_bound_r_global_unifier_5_6_contract_of_atomic_schema h) h5 h6

/-- Canonical Problem-367 contract from the existing route theorem. -/
theorem problem367_transfer_sharpened_contract :
    Problem367TransferSharpenedContract := by
  intro Cexact Clegacy hC hbound
  exact LargeTwoFullPartRarity_transfer_sharpened hC hbound

/-- Canonical bridge from existing route theorems to the master schema. -/
theorem atomic_contract_completion_schema_of_existing_routes :
    AtomicContractCompletionSchema := by
  refine atomic_contract_completion_schema_of_components
    problem367_transfer_sharpened_contract
    (fun {α : Type} [DecidableEq α] =>
      guarded_lane_bounds_of_split_noFreqGuarded (α := α))
    ?_
  intro h5 h6
  exact uniform_bound_r_global_unifier_5_6_of_f5_f6 h5 h6
