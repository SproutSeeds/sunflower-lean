import SunflowerLean.Obstruction

namespace SunflowerLean
open scoped BigOperators

def O1aNearUpgradeRegime {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (A : ℕ) (s : ℕ) (h : α) : Prop :=
  family ⊆ ground.powerset ∧
  IsSunflowerFree family 3 ∧
  (∀ T ⊆ ground, T ∉ family → ¬ IsSunflowerFree (insert T family) 3) ∧
  hiFail family ground A ∧
  nearMaxPairsAnchoredAt family ground s h

/--
Cleanup target (statement-only):
in the intended O₁a upgrade regime, the maximum pair co-degree should be at least `2`.

This would eliminate the residual bucket `ObstructionThinMaxCoDegree` (v2),
and remove the need for the `2 ≤ maxCoDegree` gate in the non-thin upgrade leaf.
-/
def two_le_maxCoDegree_of_O1aUpgradeRegime : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (A : ℕ) (h : α),
      O1aUpgradeRegime family ground A h → 2 ≤ maxCoDegree family ground

/-!
Router target (statement-only):
upgrade exact-max anchoring to near-max anchoring (Nat slack) under the O₁a upgrade regime,
or explicitly route to the current residual bucket.

We keep this as a separate statement so that later proofs of `coreHitsNnear` don't implicitly assume
we are in the near-max anchored subcase.
-/
def o1a_exact_to_near_or_residual (s : ℕ) : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (A : ℕ) (h : α),
      O1aUpgradeRegime family ground A h →
      nearMaxPairsAnchoredAt family ground s h ∨ ResidualV4 family ground A

/-! Operational target: `s = 1`. Keep the router parameterized and expose a convenient alias. -/
universe u'
def o1a_exact_to_near_s1_or_residual : Prop :=
  o1a_exact_to_near_or_residual.{u'} 1

/-!
Next chokepoint target (statement-only):
in the non-singleton witness-core branch, the witness core should hit `Nmax(h)`.

We keep this theorem-shaped at the regime level (no raw `A,B,core` threading):
the proof can unpack the witness internally.
-/
def coreHitsNmax_of_O1aUpgradeRegime : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (A0 : ℕ) (h : α) (S : Finset α),
      O1aUpgradeRegime family ground A0 h →
      2 ≤ maxCoDegree family ground →
      S ∈ family →
      h ∉ S →
      WitnessHasHNonSingletonCore family (liftAt S h) h →
      ∃ j, j ∈ S ∧ j ∈ Nmax family ground h

/-!
Near-max replacement for the `coreHitsNmax` chokepoint.

The intended use is: fix a small slack (start with `s = 1`) and prove this statement under the
near-max upgrade regime, then route the exact-max failure case into `ResidualV4`
only as a staging step.
-/
def coreHitsNnear_of_O1aNearUpgradeRegime (s : ℕ) : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (A0 : ℕ) (h : α) (S : Finset α),
      O1aNearUpgradeRegime family ground A0 s h →
      2 ≤ maxCoDegree family ground →
      S ∈ family →
      h ∉ S →
      WitnessHasHNonSingletonCore family (liftAt S h) h →
      ∃ j, j ∈ S ∧ j ∈ Nnear family ground s h

/-! Operational target: `s = 1`. Keep the theorem parameterized and expose a convenient alias. -/
universe u
def coreHitsNnear_s1 : Prop :=
  coreHitsNnear_of_O1aNearUpgradeRegime.{u} 1

/-! Second attempt target: `s = 2` (widen slack before introducing a new residual bucket). -/
def coreHitsNnear_s2 : Prop :=
  coreHitsNnear_of_O1aNearUpgradeRegime.{u} 2

/-!
Option 2 (witness-lift) leaf router (statement-only):
for `S` in the `h=0` slice, if `liftAt S h ∉ family` (so maximality forces a block),
then either we are in the chain-case, or we only have singleton-core witnesses,
or we can build a witness-lift certificate.

This is intentionally local (per `S`): residual buckets are introduced only after time-boxed
failures, and only when they help the global dependency graph.
-/
def o1a_witnessLift_router_v0 : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (A0 : ℕ) (h : α) (S : Finset α),
      O1aUpgradeRegime family ground A0 h →
      S ∈ family →
      h ∉ S →
      liftAt S h ∉ family →
      ChainExtension family S h ∨
        WitnessHasHSingletonCore family (liftAt S h) h ∨
        Nonempty (WLcert family S)

theorem o1a_witnessLift_router_v0_proof : o1a_witnessLift_router_v0 := by
  intro α _decEq family ground A0 h S hreg hS hhnS hliftNot
  classical
  rcases hreg with ⟨hground, hfree, hmax, _hfail, hanch⟩
  have hhground : h ∈ ground := hanch.1
  have hSsub : S ⊆ ground := Finset.mem_powerset.mp (hground hS)
  have hliftSub : liftAt S h ⊆ ground := by
    intro x hx
    have hx' : x ∈ S ∪ ({h} : Finset α) := by
      simpa [liftAt] using hx
    rcases Finset.mem_union.mp hx' with hxS | hxh
    · exact hSsub hxS
    · have : x = h := by simpa using (Finset.mem_singleton.mp hxh)
      exact this ▸ hhground
  have hnot : ¬ IsSunflowerFree (insert (liftAt S h) family) 3 :=
    hmax (liftAt S h) hliftSub hliftNot
  have hblocked : BlockedByTwo family (liftAt S h) :=
    blockedByTwo_of_not_sunflowerFree_insert (family := family) (T := liftAt S h)
      hfree hliftNot hnot
  have hrouter :=
    blockedByTwoFrom_contains_h_or_chainExtension (family := family) (S := S) (h := h)
      hS hhnS hfree hblocked
  rcases hrouter with hHasH | hChain
  · have hsplit := witnessHasH_cases_core (family := family) (T := liftAt S h) (h := h) hHasH
    rcases hsplit with hSing | hNonSing
    · exact Or.inr (Or.inl hSing)
    · exact Or.inr (Or.inr (exists_WLcert_of_WitnessHasHNonSingletonCore
        (family := family) (S := S) (h := h) hNonSing))
  · exact Or.inl hChain

theorem exists_WLcert_of_O1aUpgradeRegime_of_not_chain_of_not_singleton {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h : α} {S : Finset α}
    (hreg : O1aUpgradeRegime family ground A0 h)
    (hS : S ∈ family) (hhnS : h ∉ S) (hliftNot : liftAt S h ∉ family)
    (hnoChain : ¬ ChainExtension family S h)
    (hnoSing : ¬ WitnessHasHSingletonCore family (liftAt S h) h) :
    Nonempty (WLcert family S) := by
  classical
  have hrouter :=
    o1a_witnessLift_router_v0_proof
        (family := family) (ground := ground) (A0 := A0) (h := h) (S := S)
        hreg hS hhnS hliftNot
  rcases hrouter with hChain | hSing | hCert
  · exact False.elim (hnoChain hChain)
  · exact False.elim (hnoSing hSing)
  · exact hCert

theorem wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h : α}
    (hreg : O1aUpgradeRegime family ground A0 h) :
    ∀ S ∈ o1aWitnessLiftDomWL family h, Nonempty (WLcert family S) := by
  intro S hS
  classical
  have hS' :
      S ∈
        (o1aWitnessLiftDom family h).filter
          (fun S => ¬ ChainExtension family S h ∧
            ¬ WitnessHasHSingletonCore family (liftAt S h) h) := by
    simpa [o1aWitnessLiftDomWL] using hS
  have hS0 : S ∈ o1aWitnessLiftDom family h :=
    (Finset.mem_filter.mp hS').1
  have hno : ¬ ChainExtension family S h ∧
      ¬ WitnessHasHSingletonCore family (liftAt S h) h :=
    (Finset.mem_filter.mp hS').2
  have hSAvoid : S ∈ coreSliceAvoid family h :=
    (Finset.mem_filter.mp hS0).1
  have hSfam : S ∈ family := (Finset.mem_filter.mp hSAvoid).1
  have hhnS : h ∉ S := (Finset.mem_filter.mp hSAvoid).2
  have hliftNot : liftAt S h ∉ family := (Finset.mem_filter.mp hS0).2
  exact
    exists_WLcert_of_O1aUpgradeRegime_of_not_chain_of_not_singleton
      (family := family) (ground := ground) (A0 := A0) (h := h) (S := S)
      hreg hSfam hhnS hliftNot hno.1 hno.2

/-!
Arithmetic helper for the final multiplicity combination step.

We keep this intentionally coarse: the multiplicity proof will bound a hard-branch fiber by
`2 * (# buckets)` plus a polynomial overhead term (`≤ n^3`), and then absorb everything into
`n^20` (or, if needed, `n^25`) using the inequality below.
-/

theorem two_mul_add_pow_three_le_pow_twenty {n a : ℕ}
    (hn : 2 ≤ n) (ha : a ≤ n ^ 18) :
    2 * a + n ^ 3 ≤ n ^ 20 := by
  have hnpos : 0 < n := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hn
  have hpow3_le_pow18 : n ^ 3 ≤ n ^ 18 :=
    Nat.pow_le_pow_right hnpos (by decide : (3 : ℕ) ≤ 18)
  have h1 : 2 * a + n ^ 3 ≤ 2 * (n ^ 18) + n ^ 3 :=
    Nat.add_le_add_right (Nat.mul_le_mul_left 2 ha) (n ^ 3)
  have h2 : 2 * (n ^ 18) + n ^ 3 ≤ 3 * (n ^ 18) := by
    have : 2 * (n ^ 18) + n ^ 3 ≤ 2 * (n ^ 18) + (n ^ 18) :=
      Nat.add_le_add_left hpow3_le_pow18 (2 * (n ^ 18))
    simpa [Nat.mul_add, Nat.add_mul, Nat.succ_mul, Nat.mul_succ, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm] using this
  have h3 : 3 * (n ^ 18) ≤ n ^ 20 := by
    have h3le : 3 ≤ n ^ 2 := by
      -- `n^2 = n*n ≥ 4 ≥ 3` for `n ≥ 2`.
      have h4le : (4 : ℕ) ≤ n ^ 2 := by
        simpa [pow_two] using (Nat.mul_le_mul hn hn)
      exact le_trans (by decide : (3 : ℕ) ≤ 4) h4le
    have : 3 * (n ^ 18) ≤ (n ^ 2) * (n ^ 18) := Nat.mul_le_mul_right (n ^ 18) h3le
    -- Rewrite `(n^2) * (n^18)` as `n^(2+18) = n^20`.
    -- Use `n^(2+18) = n^2 * n^18`.
    have hpow : (n ^ 2) * (n ^ 18) = n ^ 20 := by
      simpa using (Nat.pow_add n 2 18).symm
    -- Conclude after rewriting the RHS.
    simpa [hpow] using this
  exact le_trans (le_trans h1 h2) h3

/-!
Next O₁a / Option-2 targets (statement-only).

These are the remaining “counting” steps needed to turn certificates into a remainder bound:
1) a (choice-free) multiplicity bound on admissible keys;
2) an upper bound on the number of realized keys;
3) combine via `card_le_card_image_mul_of_fiber_le`.
-/

/--
Base per-`x` seam value for a fixed key `k` and reference completion `S⋆` in the
hard `h ∉ S` branch.
-/
noncomputable def badAggBasePerX_of_hNotMemFiberForKey
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h0 : α}
    (hreg : O1aUpgradeRegime family ground A0 h0)
    (k : WLcertKey α)
    (Sstar : {S // S ∈ o1aWitnessLiftDomWL family h0})
    (hSstar :
      Sstar ∈ wlcertAdmissibleFiber_hNotMem
        (family := family) (o1aWitnessLiftDomWL family h0) k)
    (x : α) : ℕ := by
  classical
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
      PerXSubfiber.ne_Sstar_val_of_mem_fiberForX
        (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
        (Ssub := b.1) b.2
    let yw :
        Σ y : α, BlockedUnionWitness family b.1.1 y :=
      PerXSubfiber.chooseYAndWitness_of_hardFiber
        (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
        Sstar.2 b.1.2 hcert_star hcert_sub hne
    b.1.1 \ (yw.2.A ∪ yw.2.B)
  let sig0 : {Ssub // Ssub ∈ Fx0} → PerXSubfiber.PerXSignature α := fun b =>
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
      PerXSubfiber.ne_Sstar_val_of_mem_fiberForX
        (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
        (Ssub := b.1) b.2
    PerXSubfiber.perXSignature_of_hardFiber
      (family := family) (ground := ground) (A0 := A0) (h0 := h0)
      hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1) Sstar.2 b.1.2 hcert_star hcert_sub hne
  let sigOut : {Ssub // Ssub ∈ Fx0} → PerXSubfiber.PerXSignatureOutMore α := fun b =>
    (sig0 b,
      PerXSubfiber.trace5PlusOfFinset (α := α) (Uout b),
      PerXSubfiber.t6OptionOfTrace5Plus (α := α) (Uout b))
  let X : Finset α := ground \ (k.2.2.1 ∪ k.2.2.2.1)
  exact PerXSubfiber.BadAgg_perXSignatureOutMore (Fx0 := Fx0) sigOut X h0

/--
Per-`x` overflow term for the terminal weighted arithmetic squeeze.

This remains local to the fixed `(family, ground, A0, h0, k, S⋆, x)` context:
`weighted - ground.card^18`.
-/
noncomputable def badSig0OverflowPerX_of_hNotMemFiberForKey
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h0 : α}
    (hreg : O1aUpgradeRegime family ground A0 h0)
    (k : WLcertKey α)
    (Sstar : {S // S ∈ o1aWitnessLiftDomWL family h0})
    (hSstar :
      Sstar ∈ wlcertAdmissibleFiber_hNotMem
        (family := family) (o1aWitnessLiftDomWL family h0) k)
    (x : α) : ℕ := by
  classical
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
      PerXSubfiber.ne_Sstar_val_of_mem_fiberForX
        (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
        (Ssub := b.1) b.2
    let yw :
        Σ y : α, BlockedUnionWitness family b.1.1 y :=
      PerXSubfiber.chooseYAndWitness_of_hardFiber
        (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
        Sstar.2 b.1.2 hcert_star hcert_sub hne
    b.1.1 \ (yw.2.A ∪ yw.2.B)
  let sig0 : {Ssub // Ssub ∈ Fx0} → PerXSubfiber.PerXSignature α := fun b =>
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
      PerXSubfiber.ne_Sstar_val_of_mem_fiberForX
        (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
        (Ssub := b.1) b.2
    PerXSubfiber.perXSignature_of_hardFiber
      (family := family) (ground := ground) (A0 := A0) (h0 := h0)
      hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1) Sstar.2 b.1.2 hcert_star hcert_sub hne
  let sigOut : {Ssub // Ssub ∈ Fx0} → PerXSubfiber.PerXSignatureOutMore α := fun b =>
    (sig0 b,
      PerXSubfiber.trace5PlusOfFinset (α := α) (Uout b),
      PerXSubfiber.t6OptionOfTrace5Plus (α := α) (Uout b))
  let sig0Image : Finset (PerXSubfiber.PerXSignature α) := Fx0.attach.image sig0
  let Ctau : ℕ := 2 + 2 * ground.card * (ground.card + 1) * (ground.card + 1)
  let capNotTrue : ℕ := (ground.card + 1) * (ground.card + 1)
  let n : ℕ := ground.card
  let weighted : ℕ :=
    (sig0Image.card * (n ^ 3) * (n + 1)) * Ctau +
      (sig0Image.card * ((n ^ 3) + 1)) * capNotTrue
  exact weighted - n ^ 18

/--
Combined per-`x` seam term (single knob): base outMore seam + sig0-overflow.

This is the value aggregated by `KeyBadAggZeroAt`.
-/
noncomputable def badAggPerX_of_hNotMemFiberForKey
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h0 : α}
    (hreg : O1aUpgradeRegime family ground A0 h0)
    (k : WLcertKey α)
    (Sstar : {S // S ∈ o1aWitnessLiftDomWL family h0})
    (hSstar :
      Sstar ∈ wlcertAdmissibleFiber_hNotMem
        (family := family) (o1aWitnessLiftDomWL family h0) k)
    (x : α) : ℕ :=
  badAggBasePerX_of_hNotMemFiberForKey
    (family := family) (ground := ground) (A0 := A0) (h0 := h0)
    hreg k Sstar hSstar x +
    badSig0OverflowPerX_of_hNotMemFiberForKey
      (family := family) (ground := ground) (A0 := A0) (h0 := h0)
      hreg k Sstar hSstar x

theorem badAggPerX_eq_zero_imp
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h0 : α}
    (hreg : O1aUpgradeRegime family ground A0 h0)
    (k : WLcertKey α)
    (Sstar : {S // S ∈ o1aWitnessLiftDomWL family h0})
    (hSstar :
      Sstar ∈ wlcertAdmissibleFiber_hNotMem
        (family := family) (o1aWitnessLiftDomWL family h0) k)
    (x : α) :
    badAggPerX_of_hNotMemFiberForKey
        (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg k Sstar hSstar x = 0 →
      badAggBasePerX_of_hNotMemFiberForKey
          (family := family) (ground := ground) (A0 := A0) (h0 := h0)
          hreg k Sstar hSstar x = 0 ∧
        badSig0OverflowPerX_of_hNotMemFiberForKey
            (family := family) (ground := ground) (A0 := A0) (h0 := h0)
            hreg k Sstar hSstar x = 0 := by
  intro h
  have h' :
      badAggBasePerX_of_hNotMemFiberForKey
          (family := family) (ground := ground) (A0 := A0) (h0 := h0)
          hreg k Sstar hSstar x +
        badSig0OverflowPerX_of_hNotMemFiberForKey
            (family := family) (ground := ground) (A0 := A0) (h0 := h0)
            hreg k Sstar hSstar x = 0 := by
    simpa [badAggPerX_of_hNotMemFiberForKey] using h
  simpa using (Nat.add_eq_zero_iff.mp h')

/--
Single scalar seam knob for one key `k` and one chosen reference completion `S⋆`.

This keeps the assumption local and auditable: aggregate seam over the exact
`realizedXSet` index used by the cover lemma.
-/
def KeyBadAggZeroAt
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h0 : α}
    (hreg : O1aUpgradeRegime family ground A0 h0)
    (k : WLcertKey α)
    (Sstar : {S // S ∈ o1aWitnessLiftDomWL family h0})
    (hSstar :
      Sstar ∈ wlcertAdmissibleFiber_hNotMem
        (family := family) (o1aWitnessLiftDomWL family h0) k) : Prop :=
  let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h0
  let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
  let X : Finset α := ground \ (k.2.2.1 ∪ k.2.2.2.1)
  PerXSubfiber.BadAggAgg_over_realizedXSet
      (fiber := fiber) (Sstar := Sstar) X
      (bad := fun x =>
        badAggPerX_of_hNotMemFiberForKey
          (family := family) (ground := ground) (A0 := A0) (h0 := h0)
          hreg k Sstar hSstar x) = 0

theorem badAggPerX_eq_zero_on_realizedX_of_KeyBadAggZeroAt
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h0 : α}
    (hreg : O1aUpgradeRegime family ground A0 h0)
    (k : WLcertKey α)
    (Sstar : {S // S ∈ o1aWitnessLiftDomWL family h0})
    (hSstar :
      Sstar ∈ wlcertAdmissibleFiber_hNotMem
        (family := family) (o1aWitnessLiftDomWL family h0) k)
    (hKnob : KeyBadAggZeroAt
      (family := family) (ground := ground) (A0 := A0) (h0 := h0)
      hreg k Sstar hSstar) :
    let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h0
    let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
    let X : Finset α := ground \ (k.2.2.1 ∪ k.2.2.2.1)
    ∀ x ∈ realizedXSet (dom := dom) fiber Sstar.1 X,
      badAggPerX_of_hNotMemFiberForKey
        (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg k Sstar hSstar x = 0 := by
  intro dom fiber X
  have hPointwise :=
    PerXSubfiber.BadAggAgg_over_realizedXSet_eq_zero_imp
      (dom := dom) (fiber := fiber) (Sstar := Sstar) (X := X)
      (bad := fun x =>
        badAggPerX_of_hNotMemFiberForKey
          (family := family) (ground := ground) (A0 := A0) (h0 := h0)
          hreg k Sstar hSstar x)
      (by simpa [KeyBadAggZeroAt, dom, fiber, X] using hKnob)
  simpa using hPointwise

/--
Conditional local per-key multiplicity target.

Given one fixed `S⋆` in the hard fiber for key `k`, its cover property, and the
single seam knob `KeyBadAggZeroAt`, conclude the choice-free key multiplicity bound.
-/
def o1a_wlcert_choiceFree_multiplicity_pow20_local_target : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (A0 : ℕ) (h0 : α)
    (hreg : O1aUpgradeRegime family ground A0 h0),
      let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h0
      ∀ k : WLcertKey α,
        let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
        let X : Finset α := ground \ (k.2.2.1 ∪ k.2.2.2.1)
        ∀ Sstar : {S // S ∈ dom}, ∀ hSstar : Sstar ∈ fiber,
          let hSstarCanonical :
              Sstar ∈ wlcertAdmissibleFiber_hNotMem (family := family) dom k := by
                simpa [fiber] using hSstar
          (∀ Ssub ∈ fiber, Ssub ≠ Sstar →
            ∃ x,
              x ∈ realizedXSet (dom := dom) fiber Sstar.1 X ∧
              x ∈ Ssub.1 ∧ x ∉ Sstar.1) →
          KeyBadAggZeroAt
            (family := family) (ground := ground) (A0 := A0) (h0 := h0)
            hreg k Sstar hSstarCanonical →
          (wlcertAdmissibleFiber (family := family) dom k).card ≤ ground.card ^ 20

/--
Reduction helper for the local `n^20` multiplicity goal.

This isolates the purely combinatorial lifting step:
if each realized per-`x` hard subfiber has cardinality `≤ n^18`, then
the full admissible fiber is bounded by `n^20`.
-/
theorem wlcertAdmissibleFiber_card_le_pow20_of_cover_and_perX_pow18
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h0 : α}
    (hreg : O1aUpgradeRegime family ground A0 h0)
    (k : WLcertKey α)
    (Sstar : {S // S ∈ o1aWitnessLiftDomWL family h0})
    (hSstar :
      Sstar ∈ wlcertAdmissibleFiber_hNotMem
        (family := family) (o1aWitnessLiftDomWL family h0) k)
    (hCover :
      let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h0
      let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
      let X : Finset α := ground \ (k.2.2.1 ∪ k.2.2.2.1)
      ∀ Ssub ∈ fiber, Ssub ≠ Sstar →
        ∃ x, x ∈ realizedXSet (dom := dom) fiber Sstar.1 X ∧ x ∈ Ssub.1 ∧ x ∉ Sstar.1)
    (hPerX :
      let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h0
      let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
      let X : Finset α := ground \ (k.2.2.1 ∪ k.2.2.2.1)
      ∀ x ∈ realizedXSet (dom := dom) fiber Sstar.1 X,
        (wlcertAdmissibleFiber_hNotMem_fiberForX (dom := dom) fiber Sstar.1 x).card ≤
          ground.card ^ 18) :
    let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h0
    (wlcertAdmissibleFiber (family := family) dom k).card ≤ ground.card ^ 20 := by
  classical
  intro dom
  let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
  let X : Finset α := ground \ (k.2.2.1 ∪ k.2.2.2.1)
  let R : Finset α := realizedXSet (dom := dom) fiber Sstar.1 X
  have hSstarFiber : Sstar ∈ fiber := by
    simpa [dom, fiber] using hSstar
  have hCover' :
      ∀ Ssub ∈ fiber, Ssub ≠ Sstar →
        ∃ x, x ∈ R ∧ x ∈ Ssub.1 ∧ x ∉ Sstar.1 := by
    simpa [dom, fiber, X, R] using hCover
  have hPerX' :
      ∀ x ∈ R,
        (wlcertAdmissibleFiber_hNotMem_fiberForX (dom := dom) fiber Sstar.1 x).card ≤
          ground.card ^ 18 := by
    simpa [dom, fiber, X, R] using hPerX
  have hHard :
      fiber.card ≤
        1 +
          ∑ x ∈ R, (wlcertAdmissibleFiber_hNotMem_fiberForX (dom := dom) fiber Sstar.1 x).card := by
    simpa [R] using
      (card_le_one_add_sum_card_fiberForX_of_cover
        (dom := dom) (fiber := fiber) (Sstar := Sstar) (X := X) hSstarFiber hCover')
  have hSumLe :
      (∑ x ∈ R, (wlcertAdmissibleFiber_hNotMem_fiberForX (dom := dom) fiber Sstar.1 x).card) ≤
        R.card * ground.card ^ 18 := by
    have hsum :
        (∑ x ∈ R, (wlcertAdmissibleFiber_hNotMem_fiberForX (dom := dom) fiber Sstar.1 x).card) ≤
          ∑ _x ∈ R, ground.card ^ 18 := by
      refine Finset.sum_le_sum ?_
      intro x hx
      exact hPerX' x hx
    simpa [Finset.sum_const_nat, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsum
  have hRsub : R ⊆ X := by
    intro x hx
    exact mem_realizedXSet_imp_mem_X (dom := dom) (fiber := fiber) (S := Sstar.1) (X := X) hx
  have hXsub : X ⊆ ground := by
    intro x hx
    exact (Finset.mem_sdiff.mp hx).1
  have hRcardLe : R.card ≤ ground.card := by
    exact le_trans (Finset.card_le_card hRsub) (Finset.card_le_card hXsub)
  have hSumLePow19 :
      (∑ x ∈ R, (wlcertAdmissibleFiber_hNotMem_fiberForX (dom := dom) fiber Sstar.1 x).card) ≤
        ground.card ^ 19 := by
    have hMul :
        R.card * ground.card ^ 18 ≤ ground.card * ground.card ^ 18 :=
      Nat.mul_le_mul_right (ground.card ^ 18) hRcardLe
    have hpow19 : ground.card * ground.card ^ 18 = ground.card ^ 19 := by
      simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    exact le_trans hSumLe (by simpa [hpow19] using hMul)
  have hHardLe : fiber.card ≤ 1 + ground.card ^ 19 := by
    exact le_trans hHard (Nat.add_le_add_left hSumLePow19 1)
  have hdomFam : ∀ S ∈ dom, S ∈ family := by
    intro S hS
    exact PerXSubfiber.mem_family_of_mem_o1aWitnessLiftDomWL
      (family := family) (h0 := h0) (S := S) hS
  have hHM :
      (wlcertAdmissibleFiber_hMem (family := family) dom k).card ≤ 2 :=
    wlcertAdmissibleFiber_hMem_card_le_two (family := family) dom k hdomFam hreg.2.1
  have hAdmLe :
      (wlcertAdmissibleFiber (family := family) dom k).card ≤
        (wlcertAdmissibleFiber_hMem (family := family) dom k).card + fiber.card := by
    have hEq :
        wlcertAdmissibleFiber (family := family) dom k =
          (wlcertAdmissibleFiber_hMem (family := family) dom k) ∪ fiber := by
      calc
        wlcertAdmissibleFiber (family := family) dom k =
            (wlcertAdmissibleFiber_hMem (family := family) dom k) ∪
              (wlcertAdmissibleFiber_hNotMem (family := family) dom k) :=
          wlcertAdmissibleFiber_eq_hMem_union_hNotMem (family := family) dom k
        _ = (wlcertAdmissibleFiber_hMem (family := family) dom k) ∪ fiber := by
          simp [fiber]
    have hUnion :
        ((wlcertAdmissibleFiber_hMem (family := family) dom k) ∪ fiber).card ≤
          (wlcertAdmissibleFiber_hMem (family := family) dom k).card + fiber.card :=
      Finset.card_union_le _ _
    simpa [hEq] using hUnion
  have hAdmLeThree :
      (wlcertAdmissibleFiber (family := family) dom k).card ≤ 3 + ground.card ^ 19 := by
    calc
      (wlcertAdmissibleFiber (family := family) dom k).card
          ≤ (wlcertAdmissibleFiber_hMem (family := family) dom k).card + fiber.card := hAdmLe
      _ ≤ 2 + fiber.card := Nat.add_le_add_right hHM _
      _ ≤ 2 + (1 + ground.card ^ 19) := Nat.add_le_add_left hHardLe 2
      _ = 3 + ground.card ^ 19 := by omega
  have hTwoLeGround : 2 ≤ ground.card := by
    have hcertStar :
        ∃ cert : WLcert family Sstar.1, WLcert.key cert = k ∧ cert.h ∉ Sstar.1 :=
      (Finset.mem_filter.mp hSstarFiber).2
    rcases hcertStar with ⟨cert, _hkey, _hhNot⟩
    have hAsub : cert.A ⊆ ground := Finset.mem_powerset.mp (hreg.1 cert.hmemA.1)
    have hhGround : cert.h ∈ ground := hAsub cert.hmemA.2
    have hjAB : cert.j ∈ cert.A ∩ cert.B := by
      simpa [cert.hcoreAB] using cert.hjcore.1
    have hjGround : cert.j ∈ ground := hAsub (Finset.mem_inter.mp hjAB).1
    have hneq : cert.h ≠ cert.j := wlcert_h_ne_j cert
    have hOneLt : 1 < ground.card :=
      (Finset.one_lt_card).2 ⟨cert.h, hhGround, cert.j, hjGround, hneq⟩
    exact Nat.succ_le_of_lt hOneLt
  have hpos : 0 < ground.card := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hTwoLeGround
  have hThreeLePow19 : 3 ≤ ground.card ^ 19 := by
    have hpow2_le_pow19 : ground.card ^ 2 ≤ ground.card ^ 19 :=
      Nat.pow_le_pow_right hpos (by decide : (2 : ℕ) ≤ 19)
    have h4le : 4 ≤ ground.card ^ 2 := by
      simpa [pow_two] using (Nat.mul_le_mul hTwoLeGround hTwoLeGround)
    exact le_trans (by decide : (3 : ℕ) ≤ 4) (le_trans h4le hpow2_le_pow19)
  have hThreePlusLeDouble :
      3 + ground.card ^ 19 ≤ ground.card ^ 19 + ground.card ^ 19 :=
    Nat.add_le_add_right hThreeLePow19 (ground.card ^ 19)
  have hDoubleLePow20 : ground.card ^ 19 + ground.card ^ 19 ≤ ground.card ^ 20 := by
    have hMul : 2 * ground.card ^ 19 ≤ ground.card * ground.card ^ 19 :=
      Nat.mul_le_mul_right (ground.card ^ 19) hTwoLeGround
    have hMul' : ground.card ^ 19 + ground.card ^ 19 ≤ ground.card * ground.card ^ 19 := by
      simpa [two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hMul
    have hpow20 : ground.card * ground.card ^ 19 = ground.card ^ 20 := by
      simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    exact hMul'.trans (by simpa [hpow20])
  have hThreePlusLePow20 : 3 + ground.card ^ 19 ≤ ground.card ^ 20 :=
    le_trans hThreePlusLeDouble hDoubleLePow20
  exact le_trans hAdmLeThree hThreePlusLePow20

/--
Per-key composition step: if every per-`x` hard subfiber is bounded whenever the
fully instantiated seam vanishes at `x`, then `KeyBadAggZeroAt` yields the full
`n^20` key multiplicity bound.
-/
theorem wlcertAdmissibleFiber_card_le_pow20_of_cover_and_KeyBadAggZeroAt_and_perX_badEqZero
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h0 : α}
    (hreg : O1aUpgradeRegime family ground A0 h0)
    (k : WLcertKey α)
    (Sstar : {S // S ∈ o1aWitnessLiftDomWL family h0})
    (hSstar :
      Sstar ∈ wlcertAdmissibleFiber_hNotMem
        (family := family) (o1aWitnessLiftDomWL family h0) k)
    (hCover :
      let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h0
      let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
      let X : Finset α := ground \ (k.2.2.1 ∪ k.2.2.2.1)
      ∀ Ssub ∈ fiber, Ssub ≠ Sstar →
        ∃ x, x ∈ realizedXSet (dom := dom) fiber Sstar.1 X ∧ x ∈ Ssub.1 ∧ x ∉ Sstar.1)
    (hKnob : KeyBadAggZeroAt
      (family := family) (ground := ground) (A0 := A0) (h0 := h0)
      hreg k Sstar hSstar)
    (hPerXBadEqZero :
      ∀ x,
        badAggPerX_of_hNotMemFiberForKey
          (family := family) (ground := ground) (A0 := A0) (h0 := h0)
          hreg k Sstar hSstar x = 0 →
          (wlcertAdmissibleFiber_hNotMem_fiberForX
            (dom := o1aWitnessLiftDomWL family h0)
            (wlcertAdmissibleFiber_hNotMem
              (family := family) (o1aWitnessLiftDomWL family h0) k)
            Sstar.1 x).card ≤
            ground.card ^ 18) :
    (wlcertAdmissibleFiber
      (family := family) (o1aWitnessLiftDomWL family h0) k).card ≤
      ground.card ^ 20 := by
  let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h0
  let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
  let X : Finset α := ground \ (k.2.2.1 ∪ k.2.2.2.1)
  have hBadPerX :
      ∀ x ∈ realizedXSet (dom := dom) fiber Sstar.1 X,
        badAggPerX_of_hNotMemFiberForKey
          (family := family) (ground := ground) (A0 := A0) (h0 := h0)
          hreg k Sstar hSstar x = 0 := by
    simpa [dom, fiber, X] using
      (badAggPerX_eq_zero_on_realizedX_of_KeyBadAggZeroAt
        (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg k Sstar hSstar hKnob)
  have hPerX :
      ∀ x ∈ realizedXSet (dom := dom) fiber Sstar.1 X,
        (wlcertAdmissibleFiber_hNotMem_fiberForX (dom := dom) fiber Sstar.1 x).card ≤
          ground.card ^ 18 := by
    intro x hx
    exact hPerXBadEqZero x (hBadPerX x hx)
  simpa [dom] using
    (wlcertAdmissibleFiber_card_le_pow20_of_cover_and_perX_pow18
      (family := family) (ground := ground) (A0 := A0) (h0 := h0)
      hreg k Sstar hSstar
      (by simpa [dom, fiber, X] using hCover)
      (by simpa [dom, fiber, X] using hPerX))

/--
Global per-`x` bad-zero cap interface: under fully instantiated seam-zero at `x`,
the hard subfiber over `x` is bounded by `ground.card ^ 18`.
-/
def o1a_wlcert_choiceFree_perX_badEqZero_cap_target : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (A0 : ℕ) (h0 : α)
    (hreg : O1aUpgradeRegime family ground A0 h0)
    (k : WLcertKey α)
    (Sstar : {S // S ∈ o1aWitnessLiftDomWL family h0})
    (hSstar :
      Sstar ∈ wlcertAdmissibleFiber_hNotMem
        (family := family) (o1aWitnessLiftDomWL family h0) k)
    (x : α),
      badAggPerX_of_hNotMemFiberForKey
        (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg k Sstar hSstar x = 0 →
        (wlcertAdmissibleFiber_hNotMem_fiberForX
          (dom := o1aWitnessLiftDomWL family h0)
          (wlcertAdmissibleFiber_hNotMem
            (family := family) (o1aWitnessLiftDomWL family h0) k)
          Sstar.1 x).card ≤
          ground.card ^ 18

theorem badAggPerX_parts_eq_zero_of_badAggPerX_eq_zero
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h0 : α}
    (hreg : O1aUpgradeRegime family ground A0 h0)
    (k : WLcertKey α)
    (Sstar : {S // S ∈ o1aWitnessLiftDomWL family h0})
    (hSstar :
      Sstar ∈ wlcertAdmissibleFiber_hNotMem
        (family := family) (o1aWitnessLiftDomWL family h0) k)
    (x : α)
    (hBad :
      badAggPerX_of_hNotMemFiberForKey
        (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg k Sstar hSstar x = 0) :
    badAggBasePerX_of_hNotMemFiberForKey
        (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg k Sstar hSstar x = 0 ∧
      badSig0OverflowPerX_of_hNotMemFiberForKey
          (family := family) (ground := ground) (A0 := A0) (h0 := h0)
          hreg k Sstar hSstar x = 0 := by
  exact badAggPerX_eq_zero_imp
    (family := family) (ground := ground) (A0 := A0) (h0 := h0)
    hreg k Sstar hSstar x hBad

theorem badAggBasePerX_eq_zero_of_badAggPerX_eq_zero
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h0 : α}
    (hreg : O1aUpgradeRegime family ground A0 h0)
    (k : WLcertKey α)
    (Sstar : {S // S ∈ o1aWitnessLiftDomWL family h0})
    (hSstar :
      Sstar ∈ wlcertAdmissibleFiber_hNotMem
        (family := family) (o1aWitnessLiftDomWL family h0) k)
    (x : α)
    (hBad :
      badAggPerX_of_hNotMemFiberForKey
        (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg k Sstar hSstar x = 0) :
    badAggBasePerX_of_hNotMemFiberForKey
        (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg k Sstar hSstar x = 0 := by
  exact (badAggPerX_parts_eq_zero_of_badAggPerX_eq_zero
    (family := family) (ground := ground) (A0 := A0) (h0 := h0)
    hreg k Sstar hSstar x hBad).1

theorem badSig0OverflowPerX_eq_zero_of_badAggPerX_eq_zero
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h0 : α}
    (hreg : O1aUpgradeRegime family ground A0 h0)
    (k : WLcertKey α)
    (Sstar : {S // S ∈ o1aWitnessLiftDomWL family h0})
    (hSstar :
      Sstar ∈ wlcertAdmissibleFiber_hNotMem
        (family := family) (o1aWitnessLiftDomWL family h0) k)
    (x : α)
    (hBad :
      badAggPerX_of_hNotMemFiberForKey
        (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg k Sstar hSstar x = 0) :
    badSig0OverflowPerX_of_hNotMemFiberForKey
        (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg k Sstar hSstar x = 0 := by
  exact (badAggPerX_parts_eq_zero_of_badAggPerX_eq_zero
    (family := family) (ground := ground) (A0 := A0) (h0 := h0)
    hreg k Sstar hSstar x hBad).2

theorem one_le_capNotTrue_sq (n : ℕ) :
    1 ≤ (n + 1) * (n + 1) := by
  have hsucc : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hmul : 1 * 1 ≤ (n + 1) * (n + 1) :=
    Nat.mul_le_mul hsucc hsucc
  simpa using hmul

open Classical in
theorem tauNotTrueRigid_card_le_tauNotTrue_card
    {α : Type*} [DecidableEq α]
    (TauNotTrue : Finset (PerXSubfiber.PerXSignatureOutMore α)) :
    (TauNotTrue.filter
      (fun σOut => ¬ PerXSubfiber.CoreMore_perXSignatureOutMore (α := α) σOut)).card ≤
      TauNotTrue.card := by
  exact Finset.card_filter_le _ _

theorem tauNotTrueRigid_none_case_bucket_card_le_capNotTrue_realized
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (A0 : ℕ) (h0 : α)
    (hreg : O1aUpgradeRegime family ground A0 h0)
    (k : WLcertKey α)
    (Sstar : {S // S ∈ o1aWitnessLiftDomWL family h0})
    (x : α)
    (hSstar :
      Sstar ∈ wlcertAdmissibleFiber_hNotMem
        (family := family) (o1aWitnessLiftDomWL family h0) k)
    (σOut : PerXSubfiber.PerXSignatureOutMore α)
    (hτ : σOut.2.1 = none)
    (hcoreNoMore : ∀ u1 ot2, σOut.1.2.2.2.1 ≠ some (u1, ot2, true)) :
    let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h0
    let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
    let Fx0 : Finset {S // S ∈ dom} :=
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
        PerXSubfiber.ne_Sstar_val_of_mem_fiberForX
          (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      let yw :
          Σ y : α, BlockedUnionWitness family b.1.1 y :=
        PerXSubfiber.chooseYAndWitness_of_hardFiber
          (family := family) (ground := ground) (A0 := A0) (h0 := h0)
          hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
          Sstar.2 b.1.2 hcert_star hcert_sub hne
      b.1.1 \ (yw.2.A ∪ yw.2.B)
    let sig0 : {Ssub // Ssub ∈ Fx0} → PerXSubfiber.PerXSignature α := fun b =>
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
        PerXSubfiber.ne_Sstar_val_of_mem_fiberForX
          (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      PerXSubfiber.perXSignature_of_hardFiber
        (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
        Sstar.2 b.1.2 hcert_star hcert_sub hne
    let sigOut : {Ssub // Ssub ∈ Fx0} → PerXSubfiber.PerXSignatureOutMore α := fun b =>
      (sig0 b,
        PerXSubfiber.trace5PlusOfFinset (α := α) (Uout b),
        PerXSubfiber.t6OptionOfTrace5Plus (α := α) (Uout b))
    (@PerXSubfiber.Bucket
        {Ssub // Ssub ∈ Fx0}
        (PerXSubfiber.PerXSignatureOutMore α)
        PerXSubfiber.instDecidableEqPerXSignatureOutMore
        Fx0.attach
        sigOut
        σOut).card ≤ (ground.card + 1) * (ground.card + 1) := by
  intro dom fiber Fx0 Uout sig0 sigOut
  letI : DecidableEq (PerXSubfiber.PerXSignatureOutMore α) :=
    PerXSubfiber.instDecidableEqPerXSignatureOutMore
  exact
    PerXSubfiber.card_Bucket_perXSignatureOutMore_le_mul_succ_mul_succ_of_trace5Plus_Uout_eq_none
      (family := family) (ground := ground) (A0 := A0) (h0 := h0)
      hreg (k := k) (Sstar := Sstar) (x := x) hSstar σOut
      (hτ := hτ) hcoreNoMore

theorem tauNotTrueRigid_some_false_case_bucket_card_le_capNotTrue_realized
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (A0 : ℕ) (h0 : α)
    (hreg : O1aUpgradeRegime family ground A0 h0)
    (k : WLcertKey α)
    (Sstar : {S // S ∈ o1aWitnessLiftDomWL family h0})
    (x : α)
    (hSstar :
      Sstar ∈ wlcertAdmissibleFiber_hNotMem
        (family := family) (o1aWitnessLiftDomWL family h0) k)
    (σOut : PerXSubfiber.PerXSignatureOutMore α)
    (hτFalse : ∃ t1 t2 t3 t4 t5, σOut.2.1 = some (t1, t2, t3, t4, t5, false))
    (hcoreNoMore : ∀ u1 ot2, σOut.1.2.2.2.1 ≠ some (u1, ot2, true)) :
    let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h0
    let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
    let Fx0 : Finset {S // S ∈ dom} :=
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
        PerXSubfiber.ne_Sstar_val_of_mem_fiberForX
          (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      let yw :
          Σ y : α, BlockedUnionWitness family b.1.1 y :=
        PerXSubfiber.chooseYAndWitness_of_hardFiber
          (family := family) (ground := ground) (A0 := A0) (h0 := h0)
          hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
          Sstar.2 b.1.2 hcert_star hcert_sub hne
      b.1.1 \ (yw.2.A ∪ yw.2.B)
    let sig0 : {Ssub // Ssub ∈ Fx0} → PerXSubfiber.PerXSignature α := fun b =>
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
        PerXSubfiber.ne_Sstar_val_of_mem_fiberForX
          (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
          (Ssub := b.1) b.2
      PerXSubfiber.perXSignature_of_hardFiber
        (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
        Sstar.2 b.1.2 hcert_star hcert_sub hne
    let sigOut : {Ssub // Ssub ∈ Fx0} → PerXSubfiber.PerXSignatureOutMore α := fun b =>
      (sig0 b,
        PerXSubfiber.trace5PlusOfFinset (α := α) (Uout b),
        PerXSubfiber.t6OptionOfTrace5Plus (α := α) (Uout b))
    (@PerXSubfiber.Bucket
        {Ssub // Ssub ∈ Fx0}
        (PerXSubfiber.PerXSignatureOutMore α)
        PerXSubfiber.instDecidableEqPerXSignatureOutMore
        Fx0.attach
        sigOut
        σOut).card ≤ (ground.card + 1) * (ground.card + 1) := by
  intro dom fiber Fx0 Uout sig0 sigOut
  letI : DecidableEq (PerXSubfiber.PerXSignatureOutMore α) :=
    PerXSubfiber.instDecidableEqPerXSignatureOutMore
  rcases hτFalse with ⟨t1, t2, t3, t4, t5, hτ⟩
  have hBfalse :
      (@PerXSubfiber.Bucket
          {Ssub // Ssub ∈ Fx0}
          (PerXSubfiber.PerXSignatureOutMore α)
          PerXSubfiber.instDecidableEqPerXSignatureOutMore
          Fx0.attach
          sigOut
          σOut).card ≤ 1 := by
    exact
      PerXSubfiber.card_Bucket_perXSignatureOutMore_le_one_of_trace5Plus_Uout_eq_some_false
        (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg (k := k) (Sstar := Sstar) (x := x) hSstar σOut
        (hτ := hτ) hcoreNoMore
  have hOneLe : 1 ≤ (ground.card + 1) * (ground.card + 1) := by
    simpa using one_le_capNotTrue_sq ground.card
  exact le_trans hBfalse hOneLe

theorem tauTrue_some_false_case_elim
    {α : Type*} [DecidableEq α]
    (σOut : PerXSubfiber.PerXSignatureOutMore α)
    (hτpred :
      (match σOut.2.1 with
        | some (_t1, _t2, _t3, _t4, _t5, true) => True
        | _ => False))
    (t1 t2 t3 t4 t5 : α)
    (hτ : σOut.2.1 = some (t1, t2, t3, t4, t5, false)) : False := by
  simpa [hτ] using hτpred

theorem tauTrue_const_add_badNone_eq_Ctau_add_badNone
    {α : Type*}
    (ground : Finset α)
    (Ctau badNone : ℕ)
    (hCtau : Ctau = 2 + 2 * ground.card * (ground.card + 1) * (ground.card + 1)) :
    2 + 2 * ground.card * (ground.card + 1) * (ground.card + 1) + badNone =
      Ctau + badNone := by
  rw [hCtau]

theorem tauTrue_bucket_card_le_Ctau_add_badNone_of_transport
    {α : Type*}
    (ground : Finset α)
    (Ctau bucketCard badNoneRaw badNoneCanon : ℕ)
    (hB :
      bucketCard ≤
        2 + 2 * ground.card * (ground.card + 1) * (ground.card + 1) + badNoneRaw)
    (hCtau : Ctau = 2 + 2 * ground.card * (ground.card + 1) * (ground.card + 1))
    (hBnone : badNoneRaw = badNoneCanon) :
    bucketCard ≤ Ctau + badNoneCanon := by
  rw [← hCtau, hBnone] at hB
  exact hB

set_option maxHeartbeats 20000000 in
/--
Concrete realization of the per-`x` cap interface.

Under fully instantiated per-`x` seam-zero, the hard subfiber over `x` is bounded
by `ground.card ^ 18`.
-/
-- SORRY-GATED: 324-line proof body preserved in git (8e138d9); needs sub-lemma extraction
theorem o1a_wlcert_choiceFree_perX_badEqZero_cap_target_realized :
    o1a_wlcert_choiceFree_perX_badEqZero_cap_target.{u} := by
  intro α _ family ground A0 h0 hreg k Sstar hSstar x hBad
  classical
  letI : DecidableEq (PerXSubfiber.PerXSignatureOutMore α) :=
    PerXSubfiber.instDecidableEqPerXSignatureOutMore
  let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h0
  let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
  let Fx0 : Finset {S // S ∈ dom} :=
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
      PerXSubfiber.ne_Sstar_val_of_mem_fiberForX
        (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
        (Ssub := b.1) b.2
    let yw :
        Σ y : α, BlockedUnionWitness family b.1.1 y :=
      PerXSubfiber.chooseYAndWitness_of_hardFiber
        (family := family) (ground := ground) (A0 := A0) (h0 := h0)
        hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
        Sstar.2 b.1.2 hcert_star hcert_sub hne
    b.1.1 \ (yw.2.A ∪ yw.2.B)
  let sig0 : {Ssub // Ssub ∈ Fx0} → PerXSubfiber.PerXSignature α := fun b =>
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
      PerXSubfiber.ne_Sstar_val_of_mem_fiberForX
        (dom := dom) (fiber := fiber) (Sstar := Sstar) (x := x)
        (Ssub := b.1) b.2
    PerXSubfiber.perXSignature_of_hardFiber
      (family := family) (ground := ground) (A0 := A0) (h0 := h0)
      hreg (k := k) (Sstar := Sstar.1) (Ssub := b.1.1)
      Sstar.2 b.1.2 hcert_star hcert_sub hne
  let sigOut : {Ssub // Ssub ∈ Fx0} → PerXSubfiber.PerXSignatureOutMore α := fun b =>
    (sig0 b,
      PerXSubfiber.trace5PlusOfFinset (α := α) (Uout b),
      PerXSubfiber.t6OptionOfTrace5Plus (α := α) (Uout b))
  let X : Finset α := ground \ (k.2.2.1 ∪ k.2.2.2.1)
  have _h1 :
      badAggBasePerX_of_hNotMemFiberForKey
          (family := family) (ground := ground) (A0 := A0) (h0 := h0)
          hreg k Sstar hSstar x = 0 ∧
        badSig0OverflowPerX_of_hNotMemFiberForKey
            (family := family) (ground := ground) (A0 := A0) (h0 := h0)
            hreg k Sstar hSstar x = 0 := by
    exact badAggPerX_parts_eq_zero_of_badAggPerX_eq_zero
      (family := family) (ground := ground) (A0 := A0) (h0 := h0)
      hreg k Sstar hSstar x hBad
  have _h2 :
      PerXSubfiber.BadAgg_perXSignatureOutMore (Fx0 := Fx0) sigOut X h0 = 0 := by
    exact badAggBasePerX_eq_zero_of_badAggPerX_eq_zero
      (family := family) (ground := ground) (A0 := A0) (h0 := h0)
      hreg k Sstar hSstar x hBad
  have _h3 :
      ((let n : ℕ := ground.card
        let sig0Image : Finset (PerXSubfiber.PerXSignature α) := Fx0.attach.image sig0
        let Ctau : ℕ := 2 + 2 * n * (n + 1) * (n + 1)
        let capNotTrue : ℕ := (n + 1) * (n + 1)
        let weighted : ℕ :=
          (sig0Image.card * (n ^ 3) * (n + 1)) * Ctau +
            (sig0Image.card * ((n ^ 3) + 1)) * capNotTrue
        weighted - n ^ 18) = 0) := by
    exact badSig0OverflowPerX_eq_zero_of_badAggPerX_eq_zero
      (family := family) (ground := ground) (A0 := A0) (h0 := h0)
      hreg k Sstar hSstar x hBad
  let Ctau : ℕ := 2 + 2 * ground.card * (ground.card + 1) * (ground.card + 1)
  let capNotTrue : ℕ := (ground.card + 1) * (ground.card + 1)
  have hCtau : Ctau = 2 + 2 * ground.card * (ground.card + 1) * (ground.card + 1) := by
    rfl
  have _h4 : 1 ≤ capNotTrue := by
    simpa [capNotTrue] using one_le_capNotTrue_sq ground.card
  have _h5 :
      ∀ (TauNotTrue : Finset (PerXSubfiber.PerXSignatureOutMore α)),
        (TauNotTrue.filter
          (fun σOut => ¬ PerXSubfiber.CoreMore_perXSignatureOutMore (α := α) σOut)).card ≤
        TauNotTrue.card :=
    tauNotTrueRigid_card_le_tauNotTrue_card (α := α)
  have _h6 :=
    tauNotTrueRigid_none_case_bucket_card_le_capNotTrue_realized
      (α := α) (family := family) (ground := ground) (A0 := A0) (h0 := h0)
      hreg (k := k) (Sstar := Sstar) (x := x) hSstar
  have _h7 :=
    tauNotTrueRigid_some_false_case_bucket_card_le_capNotTrue_realized
      (α := α) (family := family) (ground := ground) (A0 := A0) (h0 := h0)
      hreg (k := k) (Sstar := Sstar) (x := x) hSstar
  have _h8 := tauTrue_some_false_case_elim (α := α)
  have _h9 : ∀ badNone : ℕ,
      2 + 2 * ground.card * (ground.card + 1) * (ground.card + 1) + badNone =
      Ctau + badNone := by
    intro badNone
    exact tauTrue_const_add_badNone_eq_Ctau_add_badNone
      (ground := ground) (Ctau := Ctau) (badNone := badNone) hCtau
  have _h10 :=
    tauTrue_bucket_card_le_Ctau_add_badNone_of_transport
      (α := α) (ground := ground)
  have hTauNotTrueRigid :
      let sigOutImage : Finset (PerXSubfiber.PerXSignatureOutMore α) := Fx0.attach.image sigOut
      let TauNotTrue : Finset (PerXSubfiber.PerXSignatureOutMore α) :=
        by
          classical
          exact
            sigOutImage.filter (fun σOut =>
              match σOut.2.1 with
              | some (_t1, _t2, _t3, _t4, _t5, true) => False
              | _ => True)
      let TauNotTrueRigid : Finset (PerXSubfiber.PerXSignatureOutMore α) :=
        by
          classical
          exact
            TauNotTrue.filter (fun σOut =>
              ¬ PerXSubfiber.CoreMore_perXSignatureOutMore (α := α) σOut)
      ∀ σOut ∈ TauNotTrueRigid,
        (PerXSubfiber.Bucket (Fx := Fx0.attach) sigOut σOut).card ≤ capNotTrue := by
    intro sigOutImage TauNotTrue TauNotTrueRigid σOut hσOut
    have hσNotTrue : σOut ∈ TauNotTrue := (Finset.mem_filter.mp hσOut).1
    have hNoCore : ¬ PerXSubfiber.CoreMore_perXSignatureOutMore (α := α) σOut :=
      (Finset.mem_filter.mp hσOut).2
    have hτpred :
        (match σOut.2.1 with
          | some (_t1, _t2, _t3, _t4, _t5, true) => False
          | _ => True) := (Finset.mem_filter.mp hσNotTrue).2
    have hcoreNoMore : ∀ u1 ot2, σOut.1.2.2.2.1 ≠ some (u1, ot2, true) := by
      intro u1 ot2 hEq
      exact hNoCore ⟨u1, ot2, hEq⟩
    cases hτ : σOut.2.1 with
    | none =>
        have h := _h6 σOut hτ hcoreNoMore
        simpa [capNotTrue, dom, fiber, Fx0, Uout, sig0, sigOut] using h
    | some sext =>
        rcases sext with ⟨t1, t2, t3, t4, t5, b⟩
        cases b with
        | true =>
            exact False.elim (by simpa [hτ] using hτpred)
        | false =>
            have h := _h7 σOut ⟨t1, t2, t3, t4, t5, hτ⟩ hcoreNoMore
            simpa [capNotTrue, dom, fiber, Fx0, Uout, sig0, sigOut] using h
  have hTauTrue :
      let sigOutImage : Finset (PerXSubfiber.PerXSignatureOutMore α) := Fx0.attach.image sigOut
      let TauTrue : Finset (PerXSubfiber.PerXSignatureOutMore α) :=
        by
          classical
          exact
            sigOutImage.filter (fun σOut =>
              match σOut.2.1 with
              | some (_t1, _t2, _t3, _t4, _t5, true) => True
              | _ => False)
      ∀ σOut ∈ TauTrue,
        (PerXSubfiber.Bucket (Fx := Fx0.attach) sigOut σOut).card ≤
          Ctau + (PerXSubfiber.BadNoneOf_perXSignatureOutMore (Fx0 := Fx0) sigOut σOut X h0).card := by
    intro sigOutImage TauTrue σOut hσOut
    have hτpred :
        (match σOut.2.1 with
          | some (_t1, _t2, _t3, _t4, _t5, true) => True
          | _ => False) := (Finset.mem_filter.mp hσOut).2
    cases hτ : σOut.2.1 with
    | none =>
        exact False.elim (by simpa [hτ] using hτpred)
    | some sext =>
        rcases sext with ⟨t1, t2, t3, t4, t5, b⟩
        cases b with
        | false =>
            exact False.elim (by simpa [hτ] using hτpred)
        | true =>
            have hB :=
              PerXSubfiber.card_Bucket_perXSignatureOutMore_le_two_add_two_mul_n_mul_succ_mul_succ_add_badNoneOf_of_trace5Plus_true
                (family := family) (ground := ground) (A0 := A0) (h0 := h0)
                hreg (k := k) (Sstar := Sstar) (x := x) hSstar σOut
                (hτ := hτ)
            have hBadNoneEq :
                (let y : α := σOut.1.1
                 let B : Finset {Ssub // Ssub ∈ Fx0} := PerXSubfiber.Bucket (Fx := Fx0.attach) sigOut σOut
                 let Bsome : Finset {Ssub // Ssub ∈ Fx0} :=
                   B.filter (fun b => PerXSubfiber.zChoice (α := α) X b.1.1 y h0 ≠ none)
                 let g2 : {Ssub // Ssub ∈ Fx0} → α × Option α × Option α := by
                   classical
                   exact fun b =>
                     match PerXSubfiber.zChoice (α := α) X b.1.1 y h0 with
                     | some z =>
                         match PerXSubfiber.uGoodChoice (α := α) X b.1.1 y h0 z with
                         | some hu => (z, some hu.1, none)
                         | none =>
                             match PerXSubfiber.uPairGoodChoice (α := α) X b.1.1 y h0 z with
                             | some huv => (z, some huv.1.1, some huv.1.2)
                             | none => (z, none, none)
                     | none => (h0, none, none)
                 let BadNone :=
                   Bsome.filter (fun b =>
                     (g2 b).2.1 = none ∧ (g2 b).2.2 = none ∧
                       ((((X \ b.1.1).erase y).erase h0).erase (g2 b).1).Nonempty)
                 BadNone.card) =
                  (PerXSubfiber.BadNoneOf_perXSignatureOutMore (Fx0 := Fx0) sigOut σOut X h0).card := by
              let badNoneRawSet : Finset {Ssub // Ssub ∈ Fx0} :=
                (let y : α := σOut.1.1
                 let B : Finset {Ssub // Ssub ∈ Fx0} := PerXSubfiber.Bucket (Fx := Fx0.attach) sigOut σOut
                 let Bsome : Finset {Ssub // Ssub ∈ Fx0} :=
                   B.filter (fun b => PerXSubfiber.zChoice (α := α) X b.1.1 y h0 ≠ none)
                 let g2 : {Ssub // Ssub ∈ Fx0} → α × Option α × Option α := by
                   classical
                   exact fun b =>
                     match PerXSubfiber.zChoice (α := α) X b.1.1 y h0 with
                     | some z =>
                         match PerXSubfiber.uGoodChoice (α := α) X b.1.1 y h0 z with
                         | some hu => (z, some hu.1, none)
                         | none =>
                             match PerXSubfiber.uPairGoodChoice (α := α) X b.1.1 y h0 z with
                             | some huv => (z, some huv.1.1, some huv.1.2)
                             | none => (z, none, none)
                     | none => (h0, none, none)
                 Bsome.filter (fun b =>
                   (g2 b).2.1 = none ∧ (g2 b).2.2 = none ∧
                     ((((X \ b.1.1).erase y).erase h0).erase (g2 b).1).Nonempty))
              let badNoneCanonSet : Finset {Ssub // Ssub ∈ Fx0} :=
                PerXSubfiber.BadNoneOf_perXSignatureOutMore (Fx0 := Fx0) sigOut σOut X h0
              suffices h : badNoneRawSet = badNoneCanonSet by
                exact congrArg Finset.card h
              ext b
              simp only [badNoneRawSet, badNoneCanonSet, PerXSubfiber.BadNoneOf_perXSignatureOutMore,
                Finset.mem_filter, PerXSubfiber.mem_Bucket, Finset.mem_attach, true_and,
                Finset.Nonempty, Finset.mem_erase, Finset.mem_sdiff, ne_eq]
              cases hzc : PerXSubfiber.zChoice X (↑↑b) σOut.1.1 h0 with
              | none =>
                  simp_all
              | some z =>
                  cases hug : PerXSubfiber.uGoodChoice X (↑↑b) σOut.1.1 h0 z with
                  | some hu =>
                      simp_all
                  | none =>
                      cases hup : PerXSubfiber.uPairGoodChoice X (↑↑b) σOut.1.1 h0 z with
                      | some huv =>
                          simp_all
                      | none =>
                          simp_all
            exact
              _h10 Ctau
                ((PerXSubfiber.Bucket (Fx := Fx0.attach) sigOut σOut).card)
                (let y : α := σOut.1.1
                 let B : Finset {Ssub // Ssub ∈ Fx0} := PerXSubfiber.Bucket (Fx := Fx0.attach) sigOut σOut
                 let Bsome : Finset {Ssub // Ssub ∈ Fx0} :=
                   B.filter (fun b => PerXSubfiber.zChoice (α := α) X b.1.1 y h0 ≠ none)
                 let g2 : {Ssub // Ssub ∈ Fx0} → α × Option α × Option α := by
                   classical
                   exact fun b =>
                     match PerXSubfiber.zChoice (α := α) X b.1.1 y h0 with
                     | some z =>
                         match PerXSubfiber.uGoodChoice (α := α) X b.1.1 y h0 z with
                         | some hu => (z, some hu.1, none)
                         | none =>
                             match PerXSubfiber.uPairGoodChoice (α := α) X b.1.1 y h0 z with
                             | some huv => (z, some huv.1.1, some huv.1.2)
                             | none => (z, none, none)
                     | none => (h0, none, none)
                 let BadNone :=
                   Bsome.filter (fun b =>
                     (g2 b).2.1 = none ∧ (g2 b).2.2 = none ∧
                       ((((X \ b.1.1).erase y).erase h0).erase (g2 b).1).Nonempty)
                 BadNone.card)
                ((PerXSubfiber.BadNoneOf_perXSignatureOutMore (Fx0 := Fx0) sigOut σOut X h0).card)
                hB hCtau hBadNoneEq
  have hMain :=
    PerXSubfiber.card_Fx0_le_tauTrue_mul_add_tauNotTrueRigid_mul_of_badAgg_eq_zero
      (Fx0 := Fx0) (sigOut := sigOut) (X := X) (h0 := h0)
      (C := Ctau) (capNotTrue := capNotTrue)
      hTauTrue hTauNotTrueRigid _h2
  let sigOutImage : Finset (PerXSubfiber.PerXSignatureOutMore α) :=
    by
      classical
      exact
        @Finset.image
          {Ssub // Ssub ∈ Fx0}
          (PerXSubfiber.PerXSignatureOutMore α)
          PerXSubfiber.instDecidableEqPerXSignatureOutMore
          sigOut Fx0.attach
  let TauTrue : Finset (PerXSubfiber.PerXSignatureOutMore α) :=
    by
      classical
      exact
        sigOutImage.filter (fun σOut =>
          match σOut.2.1 with
          | some (_t1, _t2, _t3, _t4, _t5, true) => True
          | _ => False)
  let TauNotTrue : Finset (PerXSubfiber.PerXSignatureOutMore α) :=
    by
      classical
      exact
        sigOutImage.filter (fun σOut =>
          match σOut.2.1 with
          | some (_t1, _t2, _t3, _t4, _t5, true) => False
          | _ => True)
  let TauNotTrueCoreMore : Finset (PerXSubfiber.PerXSignatureOutMore α) :=
    by
      classical
      exact TauNotTrue.filter (fun σOut => PerXSubfiber.CoreMore_perXSignatureOutMore (α := α) σOut)
  let TauNotTrueRigid : Finset (PerXSubfiber.PerXSignatureOutMore α) :=
    by
      classical
      exact TauNotTrue.filter (fun σOut => ¬ PerXSubfiber.CoreMore_perXSignatureOutMore (α := α) σOut)
  let sig0Image : Finset (PerXSubfiber.PerXSignature α) := Fx0.attach.image sig0
  have hMain' :
      Fx0.card ≤ TauTrue.card * Ctau + TauNotTrueRigid.card * capNotTrue := by
    simpa [sigOutImage, TauTrue, TauNotTrue, TauNotTrueCoreMore, TauNotTrueRigid] using hMain
  have hUsub : ∀ b ∈ Fx0.attach, Uout b ⊆ ground := by
    intro b _hb
    have hSfam : b.1.1 ∈ family :=
      PerXSubfiber.mem_family_of_mem_o1aWitnessLiftDomWL
        (family := family) (h0 := h0) (S := b.1.1) b.1.2
    have hSsub : b.1.1 ⊆ ground := Finset.mem_powerset.mp (hreg.1 hSfam)
    intro z hz
    have hzS : z ∈ b.1.1 := by
      simpa [Uout] using (Finset.mem_sdiff.mp hz).1
    exact hSsub hzS
  have hout :
      ∀ b ∈ Fx0.attach,
        (sig0 b).2.2.2.2.2 = PerXSubfiber.trace2PlusOfFinset (α := α) (Uout b) := by
    intro b _hb
    simp [sig0, Uout, PerXSubfiber.perXSignature_of_hardFiber, PerXSubfiber.perXSignature,
      PerXSubfiber.outsideTrace]
  have hTauTrueCard :
      TauTrue.card ≤ sig0Image.card * (ground.card ^ 3) * (ground.card + 1) := by
    have h :=
      PerXSubfiber.card_image_sigOut_filter_trace5Plus_true_le
        (Fx := Fx0.attach) (ground := ground) (sig0 := sig0) (Uout := Uout)
        hUsub hout
    simpa [sigOutImage, TauTrue, sig0Image, sigOut] using h
  have hTauNotTrueCard :
      TauNotTrue.card ≤ sig0Image.card * ((ground.card ^ 3) + 1) := by
    have h :=
      PerXSubfiber.card_image_sigOut_filter_trace5Plus_notTrue_le
        (Fx := Fx0.attach) (ground := ground) (sig0 := sig0) (Uout := Uout)
        hUsub hout
    simpa [sigOutImage, TauNotTrue, sig0Image, sigOut] using h
  have hTauNotTrueRigidLeTauNotTrue : TauNotTrueRigid.card ≤ TauNotTrue.card := by
    simpa [TauNotTrueRigid] using (_h5 TauNotTrue)
  have hTauNotTrueRigidCard :
      TauNotTrueRigid.card ≤ sig0Image.card * ((ground.card ^ 3) + 1) := by
    exact le_trans hTauNotTrueRigidLeTauNotTrue hTauNotTrueCard
  let n : ℕ := ground.card
  let weighted : ℕ :=
    (sig0Image.card * (n ^ 3) * (n + 1)) * Ctau +
      (sig0Image.card * ((n ^ 3) + 1)) * capNotTrue
  have hStep :
      TauTrue.card * Ctau + TauNotTrueRigid.card * capNotTrue ≤ weighted := by
    have hStep0 :
        TauTrue.card * Ctau + TauNotTrueRigid.card * capNotTrue ≤
          (sig0Image.card * (n ^ 3) * (n + 1)) * Ctau +
            (sig0Image.card * ((n ^ 3) + 1)) * capNotTrue := by
      exact Nat.add_le_add
        (Nat.mul_le_mul_right Ctau hTauTrueCard)
        (Nat.mul_le_mul_right capNotTrue hTauNotTrueRigidCard)
    simpa [weighted] using hStep0
  have hWeightedLe18 : weighted ≤ n ^ 18 := by
    have hSubZero : weighted - n ^ 18 = 0 := by
      change badSig0OverflowPerX_of_hNotMemFiberForKey
          (family := family) (ground := ground) (A0 := A0) (h0 := h0)
          hreg k Sstar hSstar x = 0
      exact _h1.2
    exact (Nat.sub_eq_zero_iff_le.mp hSubZero)
  have hWeighted :
      TauTrue.card * Ctau + TauNotTrueRigid.card * capNotTrue ≤ ground.card ^ 18 := by
    have hTmp :
        TauTrue.card * Ctau + TauNotTrueRigid.card * capNotTrue ≤ n ^ 18 :=
      le_trans hStep hWeightedLe18
    simpa [n] using hTmp
  exact le_trans hMain' hWeighted

end SunflowerLean
