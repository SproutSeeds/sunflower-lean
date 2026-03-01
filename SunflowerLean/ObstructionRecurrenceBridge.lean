import SunflowerLean.ObstructionExport

namespace SunflowerLean
open scoped BigOperators

theorem b2_recurrence_bridge_of_KeyBadAggZeroAt_realized.{v}
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
  exact
    b2_recurrence_interface_adapter_of_KeyBadAggZeroAt_realized
      (family := family) (ground := ground) (A0 := A0) (h := h) (B := B) (A := A)
      hreg hKeyImage hAssume hRemainder

end SunflowerLean
