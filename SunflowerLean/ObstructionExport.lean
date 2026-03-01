import SunflowerLean.ObstructionWiring

namespace SunflowerLean
open scoped BigOperators

theorem o1a_wlcert_choiceFree_multiplicity_pow20_local_forFixedContext_of_perX_badEqZero
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (A0 : ℕ) (h0 : α)
    (hreg : O1aUpgradeRegime family ground A0 h0)
    (hPerXBadEqZero :
      ∀ (k : WLcertKey α)
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
              ground.card ^ 18) :
    let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h0
    ∀ k : WLcertKey α,
      ∀ Sstar : {S // S ∈ dom},
      ∀ hSstar :
          Sstar ∈ wlcertAdmissibleFiber_hNotMem (family := family) dom k,
        (let fiber : Finset {S // S ∈ dom} :=
            wlcertAdmissibleFiber_hNotMem (family := family) dom k
         let X : Finset α := ground \ (k.2.2.1 ∪ k.2.2.2.1)
         ∀ Ssub ∈ fiber, Ssub ≠ Sstar →
            ∃ x,
              x ∈ realizedXSet (dom := dom) fiber Sstar.1 X ∧ x ∈ Ssub.1 ∧ x ∉ Sstar.1) →
        KeyBadAggZeroAt
          (family := family) (ground := ground) (A0 := A0) (h0 := h0)
          hreg k Sstar hSstar →
        (wlcertAdmissibleFiber (family := family) dom k).card ≤ ground.card ^ 20 := by
  intro dom k Sstar hSstar hCover hKnob
  exact
    (wlcertAdmissibleFiber_card_le_pow20_of_cover_and_KeyBadAggZeroAt_and_perX_badEqZero
      (family := family) (ground := ground) (A0 := A0) (h0 := h0)
      hreg k Sstar hSstar
      (by simpa [dom] using hCover)
      hKnob
      (fun x hBad => hPerXBadEqZero k Sstar hSstar x hBad))

/--
Bridge from the global per-`x` bad-zero cap interface to the local multiplicity target.
-/
theorem o1a_wlcert_choiceFree_multiplicity_pow20_local_target_of_perX_badEqZero_cap
    (hPerXCap : o1a_wlcert_choiceFree_perX_badEqZero_cap_target.{u}) :
    o1a_wlcert_choiceFree_multiplicity_pow20_local_target.{u} := by
  intro α _ family ground A0 h0 hreg
  simpa [o1a_wlcert_choiceFree_multiplicity_pow20_local_target] using
    (o1a_wlcert_choiceFree_multiplicity_pow20_local_forFixedContext_of_perX_badEqZero
      (family := family) (ground := ground) (A0 := A0) (h0 := h0)
      hreg
      (fun k Sstar hSstar x hBad =>
        hPerXCap
          (family := family) (ground := ground) (A0 := A0) (h0 := h0)
          hreg k Sstar hSstar x hBad))

/--
Concrete end-to-end local multiplicity closure from the realized per-`x` cap theorem.
-/
theorem o1a_wlcert_choiceFree_multiplicity_pow20_local_target_realized :
    o1a_wlcert_choiceFree_multiplicity_pow20_local_target.{u} := by
  exact
    o1a_wlcert_choiceFree_multiplicity_pow20_local_target_of_perX_badEqZero_cap
      o1a_wlcert_choiceFree_perX_badEqZero_cap_target_realized

/--
Conditional wrapper target in the final API shape.

For each realized key `k`, assume that a nonempty hard fiber admits some
reference completion `S⋆` with cover property and seam knob `KeyBadAggZeroAt`.
Then all key multiplicities satisfy the `n^20` bound.
-/
def o1a_wlcert_choiceFree_multiplicity_pow20_target_of_KeyBadAggZeroAt : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (A0 : ℕ) (h0 : α),
    (hreg : O1aUpgradeRegime family ground A0 h0) →
      let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h0
      let hdom : ∀ S ∈ dom, Nonempty (WLcert family S) :=
        wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
          (family := family) (ground := ground) (A0 := A0) (h := h0) hreg
      let keyImage := dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)
      (∀ k : WLcertKey α, k ∈ keyImage →
        let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
        fiber.Nonempty →
          ∃ Sstar : {S // S ∈ dom}, ∃ hSstar : Sstar ∈ fiber,
            let hSstarCanonical :
                Sstar ∈ wlcertAdmissibleFiber_hNotMem (family := family) dom k := by
                  simpa [fiber] using hSstar
            (∀ Ssub ∈ fiber, Ssub ≠ Sstar →
                ∃ x,
                x ∈ realizedXSet
                  (dom := dom) fiber Sstar.1 (ground \ (k.2.2.1 ∪ k.2.2.2.1)) ∧
                x ∈ Ssub.1 ∧ x ∉ Sstar.1) ∧
            KeyBadAggZeroAt
              (family := family) (ground := ground) (A0 := A0) (h0 := h0)
              hreg k Sstar hSstarCanonical) →
      ∀ k : WLcertKey α, k ∈ keyImage →
        (wlcertAdmissibleFiber (family := family) dom k).card ≤ (ground.card) ^ 20

theorem o1a_wlcert_choiceFree_multiplicity_pow20_target_of_KeyBadAggZeroAt_of_local
    (hLocal : o1a_wlcert_choiceFree_multiplicity_pow20_local_target.{u}) :
    o1a_wlcert_choiceFree_multiplicity_pow20_target_of_KeyBadAggZeroAt.{u} := by
  intro α _ family ground A0 h0 hreg
  have hLocalAt :
      ∀ k : WLcertKey α,
        let fiber : Finset {S // S ∈ o1aWitnessLiftDomWL family h0} :=
          wlcertAdmissibleFiber_hNotMem
            (family := family) (o1aWitnessLiftDomWL family h0) k
        let X : Finset α := ground \ (k.2.2.1 ∪ k.2.2.2.1)
        ∀ Sstar : {S // S ∈ o1aWitnessLiftDomWL family h0},
          ∀ hSstar : Sstar ∈ fiber,
            let hSstarCanonical :
                Sstar ∈ wlcertAdmissibleFiber_hNotMem
                  (family := family) (o1aWitnessLiftDomWL family h0) k := by
                    simpa [fiber] using hSstar
            (∀ Ssub ∈ fiber, Ssub ≠ Sstar →
              ∃ x,
                x ∈ realizedXSet
                  (dom := o1aWitnessLiftDomWL family h0) fiber Sstar.1 X ∧
                x ∈ Ssub.1 ∧ x ∉ Sstar.1) →
            KeyBadAggZeroAt
              (family := family) (ground := ground) (A0 := A0) (h0 := h0)
              hreg k Sstar hSstarCanonical →
            (wlcertAdmissibleFiber
              (family := family) (o1aWitnessLiftDomWL family h0) k).card ≤
              ground.card ^ 20 := by
    simpa [o1a_wlcert_choiceFree_multiplicity_pow20_local_target] using
      (hLocal (family := family) (ground := ground) (A0 := A0) (h0 := h0) hreg)
  intro dom hdom keyImage hAssume
  intro k hk
  let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
  by_cases hFiber : fiber.Nonempty
  · rcases hAssume k hk hFiber with ⟨Sstar, hSstar, hData⟩
    have hData' :
        (∀ Ssub ∈ fiber, Ssub ≠ Sstar →
            ∃ x,
              x ∈ realizedXSet
                (dom := dom) fiber Sstar.1 (ground \ (k.2.2.1 ∪ k.2.2.2.1)) ∧
              x ∈ Ssub.1 ∧ x ∉ Sstar.1) ∧
          KeyBadAggZeroAt
            (family := family) (ground := ground) (A0 := A0) (h0 := h0)
            hreg k Sstar (by simpa [fiber] using hSstar) := by
      simpa [fiber] using hData
    rcases hData' with ⟨hCover, hKnob⟩
    have hBound :
        (wlcertAdmissibleFiber (family := family) dom k).card ≤ ground.card ^ 20 := by
      simpa [dom, fiber] using hLocalAt k Sstar hSstar hCover hKnob
    simpa using hBound
  · have hFiberEmpty : fiber = ∅ := Finset.not_nonempty_iff_eq_empty.mp hFiber
    have hdomFam : ∀ S ∈ dom, S ∈ family := by
      intro S hS
      exact PerXSubfiber.mem_family_of_mem_o1aWitnessLiftDomWL
        (family := family) (h0 := h0) (S := S) hS
    have hHM :
        (wlcertAdmissibleFiber_hMem (family := family) dom k).card ≤ 2 :=
      wlcertAdmissibleFiber_hMem_card_le_two (family := family) dom k hdomFam hreg.2.1
    have hAdmEq :
        wlcertAdmissibleFiber (family := family) dom k =
          wlcertAdmissibleFiber_hMem (family := family) dom k := by
      calc
        wlcertAdmissibleFiber (family := family) dom k =
            (wlcertAdmissibleFiber_hMem (family := family) dom k) ∪
              (wlcertAdmissibleFiber_hNotMem (family := family) dom k) :=
          wlcertAdmissibleFiber_eq_hMem_union_hNotMem (family := family) dom k
        _ = wlcertAdmissibleFiber_hMem (family := family) dom k ∪ fiber := by
          simp [fiber]
        _ = wlcertAdmissibleFiber_hMem (family := family) dom k := by
          simp [hFiberEmpty]
    have hAdmLeTwo :
        (wlcertAdmissibleFiber (family := family) dom k).card ≤ 2 := by
      simpa [hAdmEq] using hHM
    have hTwoLeGround : 2 ≤ ground.card := by
      rcases Finset.mem_image.mp hk with ⟨Ssub, _hSsub, _hKeyEq⟩
      let cert : WLcert family Ssub.1 := Classical.choice (hdom Ssub.1 Ssub.2)
      have hAsub : cert.A ⊆ ground := Finset.mem_powerset.mp (hreg.1 cert.hmemA.1)
      have hhGround : cert.h ∈ ground := hAsub cert.hmemA.2
      have hjAB : cert.j ∈ cert.A ∩ cert.B := by
        simpa [cert.hcoreAB] using cert.hjcore.1
      have hjGround : cert.j ∈ ground := hAsub (Finset.mem_inter.mp hjAB).1
      have hneq : cert.h ≠ cert.j := wlcert_h_ne_j cert
      have hOneLt : 1 < ground.card :=
        (Finset.one_lt_card).2 ⟨cert.h, hhGround, cert.j, hjGround, hneq⟩
      exact Nat.succ_le_of_lt hOneLt
    have hGroundLePow20 : ground.card ≤ ground.card ^ 20 := by
      have hpos : 0 < ground.card := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hTwoLeGround
      have hpow : ground.card ^ 1 ≤ ground.card ^ 20 :=
        Nat.pow_le_pow_right hpos (by decide : (1 : ℕ) ≤ 20)
      simpa using hpow
    have hTwoLePow20 : 2 ≤ ground.card ^ 20 := le_trans hTwoLeGround hGroundLePow20
    exact le_trans hAdmLeTwo hTwoLePow20

/--
Thin end-to-end lift from the per-`x` bad-zero cap interface to the wrapper target.
-/
theorem o1a_wlcert_choiceFree_multiplicity_pow20_target_of_KeyBadAggZeroAt_of_perX_badEqZero_cap
    (hPerXCap : o1a_wlcert_choiceFree_perX_badEqZero_cap_target.{u}) :
    o1a_wlcert_choiceFree_multiplicity_pow20_target_of_KeyBadAggZeroAt.{u} := by
  exact
    o1a_wlcert_choiceFree_multiplicity_pow20_target_of_KeyBadAggZeroAt_of_local
      (o1a_wlcert_choiceFree_multiplicity_pow20_local_target_of_perX_badEqZero_cap
        hPerXCap)

/--
Concrete end-to-end wrapper closure from the realized per-`x` cap theorem.
-/
theorem o1a_wlcert_choiceFree_multiplicity_pow20_target_of_KeyBadAggZeroAt_realized :
    o1a_wlcert_choiceFree_multiplicity_pow20_target_of_KeyBadAggZeroAt.{u} := by
  exact
    o1a_wlcert_choiceFree_multiplicity_pow20_target_of_KeyBadAggZeroAt_of_perX_badEqZero_cap
      o1a_wlcert_choiceFree_perX_badEqZero_cap_target_realized

def o1a_wlcert_choiceFree_multiplicity_pow20_target : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (A0 : ℕ) (h : α),
    (hreg : O1aUpgradeRegime family ground A0 h) →
      let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h
      let hdom : ∀ S ∈ dom, Nonempty (WLcert family S) :=
        wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
          (family := family) (ground := ground) (A0 := A0) (h := h) hreg
      let keyImage := dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)
      ∀ k : WLcertKey α, k ∈ keyImage →
        (wlcertAdmissibleFiber (family := family) dom k).card ≤ (ground.card) ^ 20

def o1a_wlcert_multiplicity_pow20_target : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (A0 : ℕ) (h : α)
    (hreg : O1aUpgradeRegime family ground A0 h),
      let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h
      let hdom : ∀ S ∈ dom, Nonempty (WLcert family S) :=
        wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
          (family := family) (ground := ground) (A0 := A0) (h := h) hreg
      let keyImage := dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)
      ∀ k : WLcertKey α, k ∈ keyImage →
        (wlcertKeyFiber (family := family) dom hdom k).card ≤ (ground.card) ^ 20

/--
Thin closure bridge: a choice-free admissible-fiber `n^20` bound implies
the key-fiber `n^20` bound by monotonicity (`wlcertKeyFiber ⊆ wlcertAdmissibleFiber`).
-/
theorem o1a_wlcert_multiplicity_pow20_target_of_choiceFree
    (hChoice :
      o1a_wlcert_choiceFree_multiplicity_pow20_target.{u}) :
    o1a_wlcert_multiplicity_pow20_target.{u} := by
  intro α _ family ground A0 h hreg
  intro dom hdom keyImage k hk
  have hChoiceAt :
      ∀ k : WLcertKey α, k ∈ keyImage →
        (wlcertAdmissibleFiber (family := family) dom k).card ≤ (ground.card) ^ 20 := by
    simpa [o1a_wlcert_choiceFree_multiplicity_pow20_target, dom, hdom, keyImage] using
      (hChoice (family := family) (ground := ground) (A0 := A0) (h := h) (hreg := hreg))
  have hsub :=
    wlcertKeyFiber_subset_admissibleFiber
      (family := family) (dom := dom) (hdom := hdom) (k := k)
  exact (Finset.card_le_card hsub).trans (hChoiceAt k hk)

def o1a_wlcert_key_image_bound_target (B : ℕ → ℕ) : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (ground : Finset α) (A0 : ℕ) (h : α)
    (hreg : O1aUpgradeRegime family ground A0 h),
      let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h
      let hdom : ∀ S ∈ dom, Nonempty (WLcert family S) :=
        wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
          (family := family) (ground := ground) (A0 := A0) (h := h) hreg
      (dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)).card ≤
        B ground.card * (coreSliceContains family h).card ^ 2

theorem card_o1aWitnessLiftDomWL_le_card_keyImage_mul_pow20 {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h : α}
    (hreg : O1aUpgradeRegime family ground A0 h)
    (hMult :
      let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h
      let hdom : ∀ S ∈ dom, Nonempty (WLcert family S) :=
        wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
          (family := family) (ground := ground) (A0 := A0) (h := h) hreg
      let keyImage := dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)
      ∀ k : WLcertKey α, k ∈ keyImage →
        (wlcertAdmissibleFiber (family := family) dom k).card ≤ (ground.card) ^ 20) :
    (o1aWitnessLiftDomWL family h).card ≤
      ((o1aWitnessLiftDomWL family h).attach.image
          (wlcertKeyOnDom
            (family := family)
            (o1aWitnessLiftDomWL family h)
            (wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
              (family := family) (ground := ground) (A0 := A0) (h := h) hreg))).card *
        (ground.card ^ 20) := by
  classical
  let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h
  let hdom : ∀ S ∈ dom, Nonempty (WLcert family S) :=
    wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
      (family := family) (ground := ground) (A0 := A0) (h := h) hreg
  let keyImage := dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)
  have hK :
      ∀ k : WLcertKey α,
        (wlcertKeyFiber (family := family) dom hdom k).card ≤ ground.card ^ 20 := by
    intro k
    by_cases hk : k ∈ keyImage
    · have hsub :=
        wlcertKeyFiber_subset_admissibleFiber (family := family) dom hdom k
      have hcard_sub : (wlcertKeyFiber (family := family) dom hdom k).card ≤
          (wlcertAdmissibleFiber (family := family) dom k).card :=
        Finset.card_le_card hsub
      exact hcard_sub.trans (hMult k hk)
    · have hempty : (wlcertKeyFiber (family := family) dom hdom k) = ∅ := by
        ext Ssub
        constructor
        · intro hSsub
          have hEq : wlcertKeyOnDom (family := family) dom hdom Ssub = k :=
            (Finset.mem_filter.mp hSsub).2
          have hk' : k ∈ keyImage := by
            refine Finset.mem_image.mpr ?_
            exact ⟨Ssub, (Finset.mem_filter.mp hSsub).1, hEq⟩
          exact False.elim (hk hk')
        · intro hSsub
          exact False.elim (Finset.notMem_empty Ssub hSsub)
      simp [hempty]
  have hcard := card_le_card_image_mul_of_fiber_le (family := family) dom hdom (ground.card ^ 20) hK
  simpa [dom, hdom] using hcard

theorem card_o1aWitnessLiftDomWL_le_card_keyImage_mul_pow20_of_wlcert_multiplicity.{u}
    {α : Type u} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h : α}
    (hreg : O1aUpgradeRegime family ground A0 h)
    (hMultKey : o1a_wlcert_multiplicity_pow20_target.{u}) :
    (o1aWitnessLiftDomWL family h).card ≤
      ((o1aWitnessLiftDomWL family h).attach.image
          (wlcertKeyOnDom
            (family := family)
            (o1aWitnessLiftDomWL family h)
            (wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
              (family := family) (ground := ground) (A0 := A0) (h := h) hreg))).card *
        (ground.card ^ 20) := by
  classical
  let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h
  let hdom : ∀ S ∈ dom, Nonempty (WLcert family S) :=
    wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
      (family := family) (ground := ground) (A0 := A0) (h := h) hreg
  let keyImage := dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)
  have hKall :
      ∀ k : WLcertKey α, k ∈ keyImage →
        (wlcertKeyFiber (family := family) dom hdom k).card ≤ ground.card ^ 20 := by
    simpa [o1a_wlcert_multiplicity_pow20_target, dom, hdom, keyImage] using
      (hMultKey (family := family) (ground := ground) (A0 := A0) (h := h) hreg)
  have hK :
      ∀ k : WLcertKey α,
        (wlcertKeyFiber (family := family) dom hdom k).card ≤ ground.card ^ 20 := by
    intro k
    by_cases hk : k ∈ keyImage
    · exact hKall k hk
    · have hempty : (wlcertKeyFiber (family := family) dom hdom k) = ∅ := by
        ext Ssub
        constructor
        · intro hSsub
          have hEq : wlcertKeyOnDom (family := family) dom hdom Ssub = k :=
            (Finset.mem_filter.mp hSsub).2
          have hk' : k ∈ keyImage := by
            refine Finset.mem_image.mpr ?_
            exact ⟨Ssub, (Finset.mem_filter.mp hSsub).1, hEq⟩
          exact False.elim (hk hk')
        · intro hSsub
          exact False.elim (Finset.notMem_empty Ssub hSsub)
      simp [hempty]
  have hcard := card_le_card_image_mul_of_fiber_le (family := family) dom hdom (ground.card ^ 20) hK
  simpa [dom, hdom] using hcard

theorem card_o1aWitnessLiftDomWL_le_card_keyImage_mul_pow20_of_choiceFree.{u}
    {α : Type u} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h : α}
    (hreg : O1aUpgradeRegime family ground A0 h)
    (hChoice : o1a_wlcert_choiceFree_multiplicity_pow20_target.{u}) :
    (o1aWitnessLiftDomWL family h).card ≤
      ((o1aWitnessLiftDomWL family h).attach.image
          (wlcertKeyOnDom
            (family := family)
            (o1aWitnessLiftDomWL family h)
            (wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
              (family := family) (ground := ground) (A0 := A0) (h := h) hreg))).card *
        (ground.card ^ 20) := by
  have hMultKey : o1a_wlcert_multiplicity_pow20_target.{u} :=
    o1a_wlcert_multiplicity_pow20_target_of_choiceFree hChoice
  exact
    card_o1aWitnessLiftDomWL_le_card_keyImage_mul_pow20_of_wlcert_multiplicity
      (family := family) (ground := ground) (A0 := A0) (h := h) hreg hMultKey

theorem card_o1aWitnessLiftDomWL_le_B_mul_slice_sq_mul_pow20 {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h : α} (B : ℕ → ℕ)
    (hreg : O1aUpgradeRegime family ground A0 h)
    (hMult :
      let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h
      let hdom : ∀ S ∈ dom, Nonempty (WLcert family S) :=
        wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
          (family := family) (ground := ground) (A0 := A0) (h := h) hreg
      let keyImage := dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)
      ∀ k : WLcertKey α, k ∈ keyImage →
        (wlcertAdmissibleFiber (family := family) dom k).card ≤ (ground.card) ^ 20)
    (hKeys :
      ((o1aWitnessLiftDomWL family h).attach.image
          (wlcertKeyOnDom
            (family := family)
            (o1aWitnessLiftDomWL family h)
            (wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
              (family := family) (ground := ground) (A0 := A0) (h := h) hreg))).card ≤
        B ground.card * (coreSliceContains family h).card ^ 2) :
    (o1aWitnessLiftDomWL family h).card ≤
      (B ground.card * (coreSliceContains family h).card ^ 2) * (ground.card ^ 20) := by
  classical
  have h1 :=
    card_o1aWitnessLiftDomWL_le_card_keyImage_mul_pow20
      (family := family) (ground := ground) (A0 := A0) (h := h) hreg hMult
  have h2 :
      ((o1aWitnessLiftDomWL family h).attach.image
          (wlcertKeyOnDom
            (family := family)
            (o1aWitnessLiftDomWL family h)
            (wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
              (family := family) (ground := ground) (A0 := A0) (h := h) hreg))).card *
        (ground.card ^ 20) ≤
        (B ground.card * (coreSliceContains family h).card ^ 2) * (ground.card ^ 20) :=
    Nat.mul_le_mul_right (ground.card ^ 20) hKeys
  exact h1.trans h2

theorem card_o1aWitnessLiftDomWL_le_B_mul_slice_sq_mul_pow20_of_choiceFree.{u}
    {α : Type u} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h : α} (B : ℕ → ℕ)
    (hreg : O1aUpgradeRegime family ground A0 h)
    (hChoice : o1a_wlcert_choiceFree_multiplicity_pow20_target.{u})
    (hKeys :
      ((o1aWitnessLiftDomWL family h).attach.image
          (wlcertKeyOnDom
            (family := family)
            (o1aWitnessLiftDomWL family h)
            (wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
              (family := family) (ground := ground) (A0 := A0) (h := h) hreg))).card ≤
        B ground.card * (coreSliceContains family h).card ^ 2) :
    (o1aWitnessLiftDomWL family h).card ≤
      (B ground.card * (coreSliceContains family h).card ^ 2) * (ground.card ^ 20) := by
  have h1 :=
    card_o1aWitnessLiftDomWL_le_card_keyImage_mul_pow20_of_choiceFree
      (family := family) (ground := ground) (A0 := A0) (h := h) hreg hChoice
  have h2 :
      ((o1aWitnessLiftDomWL family h).attach.image
          (wlcertKeyOnDom
            (family := family)
            (o1aWitnessLiftDomWL family h)
            (wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
              (family := family) (ground := ground) (A0 := A0) (h := h) hreg))).card *
        (ground.card ^ 20) ≤
        (B ground.card * (coreSliceContains family h).card ^ 2) * (ground.card ^ 20) :=
    Nat.mul_le_mul_right (ground.card ^ 20) hKeys
  exact h1.trans h2

/--
Intermediate realized-chain consumer:
from the realized seam-conditional admissible-fiber bound, obtain the key-fiber `n^20` bound.
-/
theorem o1a_wlcert_keyFiber_multiplicity_pow20_of_KeyBadAggZeroAt_realized.{u}
    {α : Type u} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h : α}
    (hreg : O1aUpgradeRegime family ground A0 h)
    (hAssume :
      let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h
      let hdom : ∀ S ∈ dom, Nonempty (WLcert family S) :=
        wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
          (family := family) (ground := ground) (A0 := A0) (h := h) hreg
      let keyImage := dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)
      (∀ k : WLcertKey α, k ∈ keyImage →
        let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
        fiber.Nonempty →
          ∃ Sstar : {S // S ∈ dom}, ∃ hSstar : Sstar ∈ fiber,
            let hSstarCanonical :
                Sstar ∈ wlcertAdmissibleFiber_hNotMem (family := family) dom k := by
                  simpa [fiber] using hSstar
            (∀ Ssub ∈ fiber, Ssub ≠ Sstar →
                ∃ x,
                  x ∈ realizedXSet
                    (dom := dom) fiber Sstar.1 (ground \ (k.2.2.1 ∪ k.2.2.2.1)) ∧
                  x ∈ Ssub.1 ∧ x ∉ Sstar.1) ∧
            KeyBadAggZeroAt
              (family := family) (ground := ground) (A0 := A0) (h0 := h)
              hreg k Sstar hSstarCanonical)) :
    let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h
    let hdom : ∀ S ∈ dom, Nonempty (WLcert family S) :=
      wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
        (family := family) (ground := ground) (A0 := A0) (h := h) hreg
    let keyImage := dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)
    ∀ k : WLcertKey α, k ∈ keyImage →
      (wlcertKeyFiber (family := family) dom hdom k).card ≤ ground.card ^ 20 := by
  intro dom hdom keyImage k hk
  have hChoice :
      ∀ k : WLcertKey α, k ∈ keyImage →
        (wlcertAdmissibleFiber (family := family) dom k).card ≤ ground.card ^ 20 := by
    have hChoiceRaw :
        let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h
        let hdom : ∀ S ∈ dom, Nonempty (WLcert family S) :=
          wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
            (family := family) (ground := ground) (A0 := A0) (h := h) hreg
        let keyImage := dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)
        ∀ k : WLcertKey α, k ∈ keyImage →
          (wlcertAdmissibleFiber (family := family) dom k).card ≤ ground.card ^ 20 := by
      exact
        (o1a_wlcert_choiceFree_multiplicity_pow20_target_of_KeyBadAggZeroAt_realized
          (family := family) (ground := ground) (A0 := A0) (h0 := h) hreg)
          hAssume
    simpa [dom, hdom, keyImage] using hChoiceRaw
  have hsub :=
    wlcertKeyFiber_subset_admissibleFiber
      (family := family) (dom := dom) (hdom := hdom) (k := k)
  exact (Finset.card_le_card hsub).trans (hChoice k hk)

/--
Intermediate realized-chain consumer:
from the realized seam-conditional multiplicity wrapper, obtain the key-image
times `n^20` cardinality bound.
-/
theorem card_o1aWitnessLiftDomWL_le_card_keyImage_mul_pow20_of_KeyBadAggZeroAt_realized.{u}
    {α : Type u} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h : α}
    (hreg : O1aUpgradeRegime family ground A0 h)
    (hAssume :
      let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h
      let hdom : ∀ S ∈ dom, Nonempty (WLcert family S) :=
        wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
          (family := family) (ground := ground) (A0 := A0) (h := h) hreg
      let keyImage := dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)
      (∀ k : WLcertKey α, k ∈ keyImage →
        let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
        fiber.Nonempty →
          ∃ Sstar : {S // S ∈ dom}, ∃ hSstar : Sstar ∈ fiber,
            let hSstarCanonical :
                Sstar ∈ wlcertAdmissibleFiber_hNotMem (family := family) dom k := by
                  simpa [fiber] using hSstar
            (∀ Ssub ∈ fiber, Ssub ≠ Sstar →
                ∃ x,
                  x ∈ realizedXSet
                    (dom := dom) fiber Sstar.1 (ground \ (k.2.2.1 ∪ k.2.2.2.1)) ∧
                  x ∈ Ssub.1 ∧ x ∉ Sstar.1) ∧
            KeyBadAggZeroAt
              (family := family) (ground := ground) (A0 := A0) (h0 := h)
              hreg k Sstar hSstarCanonical)) :
    (o1aWitnessLiftDomWL family h).card ≤
      ((o1aWitnessLiftDomWL family h).attach.image
          (wlcertKeyOnDom
            (family := family)
            (o1aWitnessLiftDomWL family h)
            (wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
              (family := family) (ground := ground) (A0 := A0) (h := h) hreg))).card *
        (ground.card ^ 20) := by
  have hMult :
      let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h
      let hdom : ∀ S ∈ dom, Nonempty (WLcert family S) :=
        wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
          (family := family) (ground := ground) (A0 := A0) (h := h) hreg
      let keyImage := dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)
      ∀ k : WLcertKey α, k ∈ keyImage →
        (wlcertAdmissibleFiber (family := family) dom k).card ≤ (ground.card) ^ 20 := by
    exact
      (o1a_wlcert_choiceFree_multiplicity_pow20_target_of_KeyBadAggZeroAt_realized
        (family := family) (ground := ground) (A0 := A0) (h0 := h) hreg)
        hAssume
  exact
    card_o1aWitnessLiftDomWL_le_card_keyImage_mul_pow20
      (family := family) (ground := ground) (A0 := A0) (h := h) hreg hMult

/--
Export map (ready-to-use chain):
- Start from realized seam-conditional multiplicity:
  `o1a_wlcert_choiceFree_multiplicity_pow20_target_of_KeyBadAggZeroAt_realized`.
- Instantiate it in the current `(family, ground, A0, h)` context under `hAssume`.
- Get `|o1aWitnessLiftDomWL| ≤ |keyImage| * n^20` via
  `card_o1aWitnessLiftDomWL_le_card_keyImage_mul_pow20_of_KeyBadAggZeroAt_realized`.
- Use the supplied key-image cap `hKeys`.
- Conclude:
  `|o1aWitnessLiftDomWL| ≤ (B n * |coreSliceContains|^2) * n^20`.
-/
theorem card_o1aWitnessLiftDomWL_le_B_mul_slice_sq_mul_pow20_of_KeyBadAggZeroAt_realized.{u}
    {α : Type u} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h : α} (B : ℕ → ℕ)
    (hreg : O1aUpgradeRegime family ground A0 h)
    (hAssume :
      let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h
      let hdom : ∀ S ∈ dom, Nonempty (WLcert family S) :=
        wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
          (family := family) (ground := ground) (A0 := A0) (h := h) hreg
      let keyImage := dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)
      (∀ k : WLcertKey α, k ∈ keyImage →
        let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
        fiber.Nonempty →
          ∃ Sstar : {S // S ∈ dom}, ∃ hSstar : Sstar ∈ fiber,
            let hSstarCanonical :
                Sstar ∈ wlcertAdmissibleFiber_hNotMem (family := family) dom k := by
                  simpa [fiber] using hSstar
            (∀ Ssub ∈ fiber, Ssub ≠ Sstar →
                ∃ x,
                  x ∈ realizedXSet
                    (dom := dom) fiber Sstar.1 (ground \ (k.2.2.1 ∪ k.2.2.2.1)) ∧
                  x ∈ Ssub.1 ∧ x ∉ Sstar.1) ∧
            KeyBadAggZeroAt
              (family := family) (ground := ground) (A0 := A0) (h0 := h)
              hreg k Sstar hSstarCanonical))
    (hKeys :
      ((o1aWitnessLiftDomWL family h).attach.image
          (wlcertKeyOnDom
            (family := family)
            (o1aWitnessLiftDomWL family h)
            (wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
              (family := family) (ground := ground) (A0 := A0) (h := h) hreg))).card ≤
        B ground.card * (coreSliceContains family h).card ^ 2) :
    (o1aWitnessLiftDomWL family h).card ≤
      (B ground.card * (coreSliceContains family h).card ^ 2) * (ground.card ^ 20) := by
  have h1 :
      (o1aWitnessLiftDomWL family h).card ≤
        ((o1aWitnessLiftDomWL family h).attach.image
            (wlcertKeyOnDom
              (family := family)
              (o1aWitnessLiftDomWL family h)
              (wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
                (family := family) (ground := ground) (A0 := A0) (h := h) hreg))).card *
          (ground.card ^ 20) := by
    exact
      card_o1aWitnessLiftDomWL_le_card_keyImage_mul_pow20_of_KeyBadAggZeroAt_realized
        (family := family) (ground := ground) (A0 := A0) (h := h) hreg hAssume
  have h2 :
      ((o1aWitnessLiftDomWL family h).attach.image
          (wlcertKeyOnDom
            (family := family)
            (o1aWitnessLiftDomWL family h)
            (wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
              (family := family) (ground := ground) (A0 := A0) (h := h) hreg))).card *
        (ground.card ^ 20) ≤
        (B ground.card * (coreSliceContains family h).card ^ 2) * (ground.card ^ 20) :=
    Nat.mul_le_mul_right (ground.card ^ 20) hKeys
  exact h1.trans h2

theorem card_o1aWitnessLiftDomWL_le_B_mul_slice_sq_mul_pow20_of_keyImage_bound_target_and_KeyBadAggZeroAt_realized.{v}
    {α : Type v} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h : α} (B : ℕ → ℕ)
    (hreg : O1aUpgradeRegime family ground A0 h)
    (hKeyImage : o1a_wlcert_key_image_bound_target.{v} B)
    (hAssume :
      let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h
      let hdom : ∀ S ∈ dom, Nonempty (WLcert family S) :=
        wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
          (family := family) (ground := ground) (A0 := A0) (h := h) hreg
      let keyImage := dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)
      (∀ k : WLcertKey α, k ∈ keyImage →
        let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
        fiber.Nonempty →
          ∃ Sstar : {S // S ∈ dom}, ∃ hSstar : Sstar ∈ fiber,
            let hSstarCanonical :
                Sstar ∈ wlcertAdmissibleFiber_hNotMem (family := family) dom k := by
                  simpa [fiber] using hSstar
            (∀ Ssub ∈ fiber, Ssub ≠ Sstar →
                ∃ x,
                  x ∈ realizedXSet
                    (dom := dom) fiber Sstar.1 (ground \ (k.2.2.1 ∪ k.2.2.2.1)) ∧
                  x ∈ Ssub.1 ∧ x ∉ Sstar.1) ∧
            KeyBadAggZeroAt
              (family := family) (ground := ground) (A0 := A0) (h0 := h)
              hreg k Sstar hSstarCanonical)) :
    (o1aWitnessLiftDomWL family h).card ≤
      (B ground.card * (coreSliceContains family h).card ^ 2) * (ground.card ^ 20) := by
  have hKeys :=
    hKeyImage (family := family) (ground := ground) (A0 := A0) (h := h) hreg
  exact
    card_o1aWitnessLiftDomWL_le_B_mul_slice_sq_mul_pow20_of_KeyBadAggZeroAt_realized
      (family := family) (ground := ground) (A0 := A0) (h := h) (B := B) hreg hAssume hKeys

theorem b2_spine_card_o1aWitnessLiftDomWL_le_B_mul_slice_sq_mul_pow20_of_KeyBadAggZeroAt_realized.{v}
    {α : Type v} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h : α} (B : ℕ → ℕ)
    (hreg : O1aUpgradeRegime family ground A0 h)
    (hKeyImage : o1a_wlcert_key_image_bound_target.{v} B)
    (hAssume :
      let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h
      let hdom : ∀ S ∈ dom, Nonempty (WLcert family S) :=
        wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
          (family := family) (ground := ground) (A0 := A0) (h := h) hreg
      let keyImage := dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)
      (∀ k : WLcertKey α, k ∈ keyImage →
        let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
        fiber.Nonempty →
          ∃ Sstar : {S // S ∈ dom}, ∃ hSstar : Sstar ∈ fiber,
            let hSstarCanonical :
                Sstar ∈ wlcertAdmissibleFiber_hNotMem (family := family) dom k := by
                  simpa [fiber] using hSstar
            (∀ Ssub ∈ fiber, Ssub ≠ Sstar →
                ∃ x,
                  x ∈ realizedXSet
                    (dom := dom) fiber Sstar.1 (ground \ (k.2.2.1 ∪ k.2.2.2.1)) ∧
                  x ∈ Ssub.1 ∧ x ∉ Sstar.1) ∧
            KeyBadAggZeroAt
              (family := family) (ground := ground) (A0 := A0) (h0 := h)
              hreg k Sstar hSstarCanonical)) :
    (o1aWitnessLiftDomWL family h).card ≤
      (B ground.card * (coreSliceContains family h).card ^ 2) * (ground.card ^ 20) := by
  have hClosure :
      (o1aWitnessLiftDomWL family h).card ≤
        (B ground.card * (coreSliceContains family h).card ^ 2) * (ground.card ^ 20) := by
    exact
      card_o1aWitnessLiftDomWL_le_B_mul_slice_sq_mul_pow20_of_keyImage_bound_target_and_KeyBadAggZeroAt_realized
        (family := family) (ground := ground) (A0 := A0) (h := h) (B := B) hreg hKeyImage hAssume
  exact hClosure

theorem b2_spine_card_o1aWitnessLiftDomWL_le_maxSunflowerFreeCard_sdiff_add_of_KeyBadAggZeroAt_realized.{v}
    {α : Type v} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h : α} (B : ℕ → ℕ) (A : ℕ)
    (hreg : O1aUpgradeRegime family ground A0 h)
    (hKeyImage : o1a_wlcert_key_image_bound_target.{v} B)
    (hAssume :
      let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h
      let hdom : ∀ S ∈ dom, Nonempty (WLcert family S) :=
        wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
          (family := family) (ground := ground) (A0 := A0) (h := h) hreg
      let keyImage := dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)
      (∀ k : WLcertKey α, k ∈ keyImage →
        let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
        fiber.Nonempty →
          ∃ Sstar : {S // S ∈ dom}, ∃ hSstar : Sstar ∈ fiber,
            let hSstarCanonical :
                Sstar ∈ wlcertAdmissibleFiber_hNotMem (family := family) dom k := by
                  simpa [fiber] using hSstar
            (∀ Ssub ∈ fiber, Ssub ≠ Sstar →
                ∃ x,
                  x ∈ realizedXSet
                    (dom := dom) fiber Sstar.1 (ground \ (k.2.2.1 ∪ k.2.2.2.1)) ∧
                  x ∈ Ssub.1 ∧ x ∉ Sstar.1) ∧
            KeyBadAggZeroAt
              (family := family) (ground := ground) (A0 := A0) (h0 := h)
              hreg k Sstar hSstarCanonical))
    (hRemainder :
      (B ground.card * (coreSliceContains family h).card ^ 2) * (ground.card ^ 20) ≤ A) :
    (o1aWitnessLiftDomWL family h).card ≤
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 + A := by
  have hSpine :
      (o1aWitnessLiftDomWL family h).card ≤
        (B ground.card * (coreSliceContains family h).card ^ 2) * (ground.card ^ 20) := by
    exact
      b2_spine_card_o1aWitnessLiftDomWL_le_B_mul_slice_sq_mul_pow20_of_KeyBadAggZeroAt_realized
        (family := family) (ground := ground) (A0 := A0) (h := h) (B := B)
        hreg hKeyImage hAssume
  have hA :
      (o1aWitnessLiftDomWL family h).card ≤ A := by
    exact hSpine.trans hRemainder
  have hLift :
      A ≤ maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 + A := by
    exact Nat.le_add_left _ _
  exact hA.trans hLift

theorem b2_recurrence_interface_adapter_of_KeyBadAggZeroAt_realized.{v}
    {α : Type v} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h : α} (B : ℕ → ℕ) (A : ℕ)
    (hreg : O1aUpgradeRegime family ground A0 h)
    (hKeyImage : o1a_wlcert_key_image_bound_target.{v} B)
    (hAssume :
      let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h
      let hdom : ∀ S ∈ dom, Nonempty (WLcert family S) :=
        wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
          (family := family) (ground := ground) (A0 := A0) (h := h) hreg
      let keyImage := dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)
      (∀ k : WLcertKey α, k ∈ keyImage →
        let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
        fiber.Nonempty →
          ∃ Sstar : {S // S ∈ dom}, ∃ hSstar : Sstar ∈ fiber,
            let hSstarCanonical :
                Sstar ∈ wlcertAdmissibleFiber_hNotMem (family := family) dom k := by
                  simpa [fiber] using hSstar
            (∀ Ssub ∈ fiber, Ssub ≠ Sstar →
                ∃ x,
                  x ∈ realizedXSet
                    (dom := dom) fiber Sstar.1 (ground \ (k.2.2.1 ∪ k.2.2.2.1)) ∧
                  x ∈ Ssub.1 ∧ x ∉ Sstar.1) ∧
            KeyBadAggZeroAt
              (family := family) (ground := ground) (A0 := A0) (h0 := h)
              hreg k Sstar hSstarCanonical))
    (hRemainder :
      (B ground.card * (coreSliceContains family h).card ^ 2) * (ground.card ^ 20) ≤ A) :
    (o1aWitnessLiftDomWL family h).card ≤
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 + A := by
  have hRec :
      (o1aWitnessLiftDomWL family h).card ≤
        maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 + A := by
    exact
      b2_spine_card_o1aWitnessLiftDomWL_le_maxSunflowerFreeCard_sdiff_add_of_KeyBadAggZeroAt_realized
        (family := family) (ground := ground) (A0 := A0) (h := h) (B := B) (A := A)
        hreg hKeyImage hAssume hRemainder
  exact hRec


theorem card_coreSliceContains_add_card_coreSliceAvoid_eq_card {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (h : α) :
    (coreSliceContains family h).card + (coreSliceAvoid family h).card = family.card := by
  classical
  -- Partition by membership of h.
  simpa [coreSliceContains, coreSliceAvoid] using
    (Finset.filter_card_add_filter_neg_card_eq_card
      (s := family) (p := fun S : Finset α => h ∈ S))

theorem card_coreOverlap_add_card_coreRemainder_eq_card_coreSliceAvoid {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (h : α) :
    (coreOverlap family h).card + (coreRemainder family h).card =
      (coreSliceAvoid family h).card := by
  classical
  -- X ∪ Y = B with X = B ∩ A' and Y = B \ A'.
  simp [coreOverlap, coreRemainder]



end SunflowerLean
