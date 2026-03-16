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

/-- Minimal admissible window for the reformulated container route. -/
def ContainerAdmissibleGround {α : Type*} [DecidableEq α]
    (ground : Finset α) : Prop :=
  2 ≤ ground.card

@[simp] theorem containerAdmissibleGround_iff_card_ge_two
    {α : Type*} [DecidableEq α] (ground : Finset α) :
    ContainerAdmissibleGround ground ↔ 2 ≤ ground.card := Iff.rfl

theorem containerAdmissibleGround_pos
    {α : Type*} [DecidableEq α] {ground : Finset α}
    (hground : ContainerAdmissibleGround ground) :
    0 < ground.card := by
  exact lt_of_lt_of_le (by decide : 0 < 2) hground

/-- Obstruction-aware reformulation:
require a nontrivial ground (`2 ≤ |ground|`) to avoid the known `Fin 1`
counterexample while keeping the same Nat-only container-gap shape. -/
def ContainerDensityGapConjectureNatReformulated {α : Type*} [DecidableEq α] : Prop :=
  ∀ (ground : Finset α), ContainerAdmissibleGround ground →
    ∃ (containers : Finset (Finset (Finset α))) (gap : ℕ),
      0 < gap ∧
      IsContainerCollection containers ground 3 ∧
      ∀ C ∈ containers, C.card * 2 ^ gap ≤ 2 ^ ground.card

/-- Route leaf alias (v2 scope name) for strict scanner compatibility. -/
def ContainerDensityGapConjectureNat_reformulated {α : Type*} [DecidableEq α] : Prop :=
  ContainerDensityGapConjectureNatReformulated (α := α)

/-- v2 admissibility window: require at least three ground elements. -/
def ContainerAdmissibleGroundV2 {α : Type*} [DecidableEq α]
    (ground : Finset α) : Prop :=
  3 ≤ ground.card

@[simp] theorem containerAdmissibleGroundV2_iff_card_ge_three
    {α : Type*} [DecidableEq α] (ground : Finset α) :
    ContainerAdmissibleGroundV2 ground ↔ 3 ≤ ground.card := Iff.rfl

/-- v2 reformulation route: same Nat-only gap shape, but with the stricter
admissibility guard `3 ≤ |ground|`. -/
def ContainerDensityGapConjectureNatReformulatedV2 {α : Type*} [DecidableEq α] : Prop :=
  ∀ (ground : Finset α), ContainerAdmissibleGroundV2 ground →
    ∃ (containers : Finset (Finset (Finset α))) (gap : ℕ),
      0 < gap ∧
      IsContainerCollection containers ground 3 ∧
      ∀ C ∈ containers, C.card * 2 ^ gap ≤ 2 ^ ground.card

/-- Route-facing alias for the v2 reformulated container leaf. -/
def ContainerDensityGapConjectureNat_reformulated_v2 {α : Type*} [DecidableEq α] : Prop :=
  ContainerDensityGapConjectureNatReformulatedV2 (α := α)

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

/-- Unpacks the bounded-container consequence of the reformulated conjecture
at a fixed nontrivial ground set. -/
theorem container_density_gap_reformulated_consequence {α : Type*} [DecidableEq α]
    (ground : Finset α) (hground : ContainerAdmissibleGround ground) :
    ContainerDensityGapConjectureNatReformulated (α := α) →
    ∃ (containers : Finset (Finset (Finset α))) (gap : ℕ),
      0 < gap ∧
      IsContainerCollection containers ground 3 ∧
      ∀ C ∈ containers, C.card * 2 ^ gap ≤ 2 ^ ground.card := by
  intro h
  exact h ground hground

/-- Compatibility variant exposing the same consequence with a raw cardinality
bound hypothesis. -/
theorem container_density_gap_reformulated_consequence_of_card_ge_two
    {α : Type*} [DecidableEq α] (ground : Finset α) (hground : 2 ≤ ground.card) :
    ContainerDensityGapConjectureNatReformulated (α := α) →
    ∃ (containers : Finset (Finset (Finset α))) (gap : ℕ),
      0 < gap ∧
      IsContainerCollection containers ground 3 ∧
      ∀ C ∈ containers, C.card * 2 ^ gap ≤ 2 ^ ground.card := by
  intro h
  exact container_density_gap_reformulated_consequence ground hground h

/-- Unpacks the bounded-container consequence of the v2 reformulated
conjecture at a fixed admissible ground set (`3 ≤ |ground|`). -/
theorem container_density_gap_reformulated_v2_consequence {α : Type*} [DecidableEq α]
    (ground : Finset α) (hground : ContainerAdmissibleGroundV2 ground) :
    ContainerDensityGapConjectureNatReformulatedV2 (α := α) →
    ∃ (containers : Finset (Finset (Finset α))) (gap : ℕ),
      0 < gap ∧
      IsContainerCollection containers ground 3 ∧
      ∀ C ∈ containers, C.card * 2 ^ gap ≤ 2 ^ ground.card := by
  intro h
  exact h ground hground

/-- The one-point universe sits outside the admissible reformulated window. -/
theorem not_containerAdmissibleGround_fin1_univ :
    ¬ ContainerAdmissibleGround (Finset.univ : Finset (Fin 1)) := by
  simp [ContainerAdmissibleGround]

/-- In v2, the two-point universe is excluded by admissibility. -/
theorem not_containerAdmissibleGroundV2_fin2_univ :
    ¬ ContainerAdmissibleGroundV2 (Finset.univ : Finset (Fin 2)) := by
  simp [ContainerAdmissibleGroundV2]

/-- A concrete cardinality window strong enough to support a gap-1 container
witness at fixed ground. -/
def ContainerHalfDensityCap {α : Type*} [DecidableEq α]
    (ground : Finset α) : Prop :=
  ∀ (family : Finset (Finset α)),
    IsSunflowerFree family 3 →
    IsOnGround family ground →
    family.card * 2 ≤ 2 ^ ground.card

/-- Micro-lemma: a per-family half-card bound implies `ContainerHalfDensityCap`.
This is a reusable reducer for v2 lane attempts. -/
theorem container_halfDensityCap_of_half_card_bound {α : Type*} [DecidableEq α]
    (ground : Finset α)
    (hbound : ∀ (family : Finset (Finset α)),
      IsSunflowerFree family 3 →
      IsOnGround family ground →
      family.card ≤ (2 ^ ground.card) / 2) :
    ContainerHalfDensityCap ground := by
  intro family hsf hOn
  have hcard : family.card ≤ (2 ^ ground.card) / 2 := hbound family hsf hOn
  have hmul : 2 * family.card ≤ 2 * ((2 ^ ground.card) / 2) :=
    Nat.mul_le_mul_left 2 hcard
  have hdiv : 2 * ((2 ^ ground.card) / 2) ≤ 2 ^ ground.card := by
    have hdiv' : ((2 ^ ground.card) / 2) * 2 ≤ 2 ^ ground.card :=
      Nat.div_mul_le_self (2 ^ ground.card) 2
    simpa [Nat.mul_comm] using hdiv'
  have hfinal : 2 * family.card ≤ 2 ^ ground.card := le_trans hmul hdiv
  simpa [Nat.mul_comm] using hfinal

/-- Concrete cardinality-bound family for v2-admissible grounds: every
3-sunflower-free on-ground family has cardinality at most half the full
powerset size. -/
def ContainerAdmissibleGroundV2HalfCardBoundFamily (α : Type*) [DecidableEq α] : Prop :=
  ∀ (ground : Finset α), ContainerAdmissibleGroundV2 ground →
    ∀ (family : Finset (Finset α)),
      IsSunflowerFree family 3 →
      IsOnGround family ground →
      family.card ≤ (2 ^ ground.card) / 2

/-- If every sunflower-free family on `ground` satisfies the half-density cap,
we get an explicit gap-1 container witness by taking the filtered powerset-of-powerset
family. -/
theorem container_gap1_witness_of_halfDensityCap {α : Type*} [DecidableEq α]
    (ground : Finset α) (hcap : ContainerHalfDensityCap ground) :
    ∃ (containers : Finset (Finset (Finset α))) (gap : ℕ),
      0 < gap ∧
      IsContainerCollection containers ground 3 ∧
      ∀ C ∈ containers, C.card * 2 ^ gap ≤ 2 ^ ground.card := by
  refine ⟨(ground.powerset.powerset).filter
      (fun C => C.card * 2 ≤ 2 ^ ground.card), 1, by decide, ?_, ?_⟩
  · intro family hsf hOn
    refine ⟨family, ?_, Finset.Subset.rfl⟩
    refine Finset.mem_filter.mpr ⟨?_, hcap family hsf hOn⟩
    refine Finset.mem_powerset.mpr ?_
    intro S hS
    exact Finset.mem_powerset.mpr (hOn S hS)
  · intro C hC
    have hcapC : C.card * 2 ≤ 2 ^ ground.card := (Finset.mem_filter.mp hC).2
    simpa using hcapC

/-- Reusable local-input bundle for invoking container consequence-shaped
closures on a fixed admissible ground. -/
def ContainerReformulatedConsequenceInputs {α : Type*} [DecidableEq α]
    (ground : Finset α) : Prop :=
  ContainerAdmissibleGround ground ∧
  ContainerHalfDensityCap ground

/-- Bundle reducer: the local reformulated input package is sufficient to
construct an explicit gap-1 container consequence witness. -/
theorem container_gap1_witness_of_reformulated_inputs
    {α : Type*} [DecidableEq α] (ground : Finset α)
    (hinputs : ContainerReformulatedConsequenceInputs ground) :
    ∃ (containers : Finset (Finset (Finset α))) (gap : ℕ),
      0 < gap ∧
      IsContainerCollection containers ground 3 ∧
      ∀ C ∈ containers, C.card * 2 ^ gap ≤ 2 ^ ground.card := by
  rcases hinputs with ⟨_hground, hcap⟩
  exact container_gap1_witness_of_halfDensityCap ground hcap

/-- Skeleton bridge: if each admissible ground comes equipped with the local
reformulated input bundle, then the reformulated container leaf follows. -/
theorem container_density_gap_reformulated_of_inputs_bundle
    {α : Type*} [DecidableEq α]
    (hinputs :
      ∀ ground : Finset α, ContainerAdmissibleGround ground →
        ContainerReformulatedConsequenceInputs ground) :
    ContainerDensityGapConjectureNatReformulated (α := α) := by
  intro ground hground
  exact container_gap1_witness_of_reformulated_inputs ground (hinputs ground hground)

/-- Convenience bridge: a per-ground half-density cap on admissible grounds
immediately packages into the reformulated leaf skeleton. -/
theorem container_density_gap_reformulated_of_halfDensityCap
    {α : Type*} [DecidableEq α]
    (hcap :
      ∀ ground : Finset α, ContainerAdmissibleGround ground →
        ContainerHalfDensityCap ground) :
    ContainerDensityGapConjectureNatReformulated (α := α) := by
  refine container_density_gap_reformulated_of_inputs_bundle ?_
  intro ground hground
  exact ⟨hground, hcap ground hground⟩

/-- Route-facing strict-leaf skeleton in alias form. -/
theorem container_density_gap_reformulated_leaf_of_halfDensityCap
    {α : Type*} [DecidableEq α]
    (hcap :
      ∀ ground : Finset α, ContainerAdmissibleGround ground →
        ContainerHalfDensityCap ground) :
    ContainerDensityGapConjectureNat_reformulated (α := α) := by
  exact container_density_gap_reformulated_of_halfDensityCap hcap

/-- v2 bridge: if every v2-admissible ground (`3 ≤ |ground|`) has the
half-density cap, then the v2 reformulated container leaf follows. -/
theorem container_density_gap_reformulated_v2_of_halfDensityCap
    {α : Type*} [DecidableEq α]
    (hcap :
      ∀ ground : Finset α, ContainerAdmissibleGroundV2 ground →
        ContainerHalfDensityCap ground) :
    ContainerDensityGapConjectureNatReformulatedV2 (α := α) := by
  intro ground hground
  exact container_gap1_witness_of_halfDensityCap ground (hcap ground hground)

/-- Route-facing v2 strict-leaf skeleton in alias form. -/
theorem container_density_gap_reformulated_v2_leaf_of_halfDensityCap
    {α : Type*} [DecidableEq α]
    (hcap :
      ∀ ground : Finset α, ContainerAdmissibleGroundV2 ground →
        ContainerHalfDensityCap ground) :
    ContainerDensityGapConjectureNat_reformulated_v2 (α := α) := by
  exact container_density_gap_reformulated_v2_of_halfDensityCap hcap

/-- Candidate strict-lane kernel for the v2 container route on a fixed ambient
type. Every v2-admissible ground (`3 ≤ |ground|`) satisfies the half-density
cap. -/
def ContainerV2HalfDensityCapLane (α : Type*) [DecidableEq α] : Prop :=
  ∀ (ground : Finset α),
    ContainerAdmissibleGroundV2 ground →
      ContainerHalfDensityCap ground

/-- Bridge from the v2 strict-lane kernel to the v2 reformulated leaf. -/
theorem container_density_gap_reformulated_v2_of_halfDensityCap_lane
    {α : Type*} [DecidableEq α]
    (hlane : ContainerV2HalfDensityCapLane α) :
    ContainerDensityGapConjectureNatReformulatedV2 (α := α) := by
  exact container_density_gap_reformulated_v2_of_halfDensityCap
    (hcap := hlane)

/-- Route-facing specialized bridge from the v2 strict-lane kernel. -/
theorem container_density_gap_reformulated_v2_leaf_of_halfDensityCap_lane
    {α : Type*} [DecidableEq α]
    (hlane : ContainerV2HalfDensityCapLane α) :
    ContainerDensityGapConjectureNat_reformulated_v2 (α := α) := by
  exact container_density_gap_reformulated_v2_of_halfDensityCap_lane hlane

/-- Forward compatibility bridge: the concrete v2 admissible-ground bound
family feeds directly into the reusable half-card reducer. -/
theorem container_halfDensityCapLane_of_admissibleGroundV2_half_card_bound_family
    {α : Type*} [DecidableEq α]
    (hbound : ContainerAdmissibleGroundV2HalfCardBoundFamily α) :
    ContainerV2HalfDensityCapLane α := by
  intro ground hground
  exact container_halfDensityCap_of_half_card_bound ground (hbound ground hground)

/-- Reverse extractor: any v2 half-density-cap lane yields the same concrete
half-card cardinality bound family by dividing the cap inequality by `2`. -/
theorem container_admissibleGroundV2_half_card_bound_family_of_halfDensityCapLane
    {α : Type*} [DecidableEq α]
    (hlane : ContainerV2HalfDensityCapLane α) :
    ContainerAdmissibleGroundV2HalfCardBoundFamily α := by
  intro ground hground family hsf hOn
  have hcap : family.card * 2 ≤ 2 ^ ground.card := hlane ground hground family hsf hOn
  exact (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2 (by simpa [Nat.mul_comm] using hcap)

/-- Interface equivalence: the v2 half-density-cap lane is exactly the same
assumption content as the admissible-ground v2 half-card bound family. -/
theorem container_halfDensityCapLane_iff_admissibleGroundV2_half_card_bound_family
    {α : Type*} [DecidableEq α] :
    ContainerV2HalfDensityCapLane α ↔
      ContainerAdmissibleGroundV2HalfCardBoundFamily α := by
  constructor
  · intro hlane
    exact container_admissibleGroundV2_half_card_bound_family_of_halfDensityCapLane hlane
  · intro hbound
    exact container_halfDensityCapLane_of_admissibleGroundV2_half_card_bound_family hbound

/-- Route bridge: the concrete v2 admissible-ground cardinality-bound family
is sufficient for the v2 reformulated container leaf. -/
theorem container_density_gap_reformulated_v2_of_admissibleGroundV2_half_card_bound_family
    {α : Type*} [DecidableEq α]
    (hbound : ContainerAdmissibleGroundV2HalfCardBoundFamily α) :
    ContainerDensityGapConjectureNatReformulatedV2 (α := α) := by
  exact container_density_gap_reformulated_v2_of_halfDensityCap_lane
    (container_halfDensityCapLane_of_admissibleGroundV2_half_card_bound_family hbound)

/-- Route-facing alias form of the concrete v2 cardinality-bound family
bridge. -/
theorem container_density_gap_reformulated_v2_leaf_of_admissibleGroundV2_half_card_bound_family
    {α : Type*} [DecidableEq α]
    (hbound : ContainerAdmissibleGroundV2HalfCardBoundFamily α) :
    ContainerDensityGapConjectureNat_reformulated_v2 (α := α) := by
  exact container_density_gap_reformulated_v2_of_admissibleGroundV2_half_card_bound_family hbound

/-- The half-density cap fails on `Fin 2` (ground = univ), witnessed by the
known 3-sunflower-free family of size 3. -/
theorem not_containerHalfDensityCap_fin2_univ :
    ¬ ContainerHalfDensityCap (ground := (Finset.univ : Finset (Fin 2))) := by
  intro hcap
  have hOn : IsOnGround witness_2_3 (Finset.univ : Finset (Fin 2)) := by
    intro S _hS
    exact Finset.subset_univ S
  have hbound : witness_2_3.card * 2 ≤ 2 ^ (Finset.univ : Finset (Fin 2)).card :=
    hcap witness_2_3 witness_2_3_sf_free hOn
  have hbad : 6 ≤ 4 := by
    have hbad := hbound
    simp [witness_2_3_card] at hbad
  exact (by decide : ¬ (6 ≤ 4)) hbad

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
    have hle' := hle
    simp [hcard, hfull_card] at hle'
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

/-- Even with the admissibility guard `2 ≤ |ground|`, the current reformulated
container leaf fails on `Fin 2` (`ground = univ`), witnessed by `witness_2_3`. -/
theorem not_container_density_gap_conjecture_nat_reformulated_fin2 :
    ¬ ContainerDensityGapConjectureNat_reformulated (α := Fin 2) := by
  intro hconj
  let ground : Finset (Fin 2) := Finset.univ
  have hground : ContainerAdmissibleGround ground := by
    simp [ContainerAdmissibleGround, ground]
  rcases container_density_gap_reformulated_consequence
      (α := Fin 2) ground hground hconj with
    ⟨containers, gap, hgap_pos, hcover, hbound⟩
  have hOn : IsOnGround witness_2_3 ground := by
    intro S _hS
    exact Finset.subset_univ S
  rcases hcover witness_2_3 witness_2_3_sf_free hOn with ⟨C, hCmem, hwit_sub_C⟩
  have hC_ge3 : 3 ≤ C.card := by
    have hle : witness_2_3.card ≤ C.card := Finset.card_le_card hwit_sub_C
    rw [witness_2_3_card] at hle
    exact hle
  have hgap_ge1 : 1 ≤ gap := Nat.succ_le_of_lt hgap_pos
  have hpow_ge2 : 2 ≤ 2 ^ gap := by
    calc
      2 = 2 ^ 1 := by simp
      _ ≤ 2 ^ gap := Nat.pow_le_pow_right (by decide) hgap_ge1
  have hCbound : C.card * 2 ^ gap ≤ 2 ^ ground.card := hbound C hCmem
  have hground_pow : 2 ^ ground.card = 4 := by
    simp [ground]
  have hmul_ge6 : 6 ≤ C.card * 2 ^ gap := by
    have hmul_ge : 3 * 2 ≤ C.card * 2 ^ gap :=
      Nat.mul_le_mul hC_ge3 hpow_ge2
    simpa using hmul_ge
  have h6_le_4 : 6 ≤ 4 := by
    calc
      6 ≤ C.card * 2 ^ gap := hmul_ge6
      _ ≤ 2 ^ ground.card := hCbound
      _ = 4 := hground_pow
  exact (by decide : ¬ (6 ≤ 4)) h6_le_4

end SunflowerLean
