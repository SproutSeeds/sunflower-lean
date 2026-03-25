import SunflowerLean.ObstructionExport

namespace SunflowerLean
open scoped BigOperators

theorem hAssume_of_KeyBadAggZeroAt_builder.{v}
    {α : Type v} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h : α}
    (hreg : O1aUpgradeRegime family ground A0 h)
    (hBuilder :
      let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h
      let hdom : ∀ S ∈ dom, Nonempty (WLcert family S) :=
        wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
          (family := family) (ground := ground) (A0 := A0) (h := h) hreg
      let keyImage := dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)
      ∀ k : WLcertKey α, k ∈ keyImage →
        let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
        ∀ Sstar : {S // S ∈ dom}, ∀ hSstar : Sstar ∈ fiber,
          (∀ Ssub ∈ fiber, Ssub ≠ Sstar →
            ∃ x,
              x ∈ realizedXSet
                (dom := dom) fiber Sstar.1 (ground \ (k.2.2.1 ∪ k.2.2.2.1)) ∧
              x ∈ Ssub.1 ∧ x ∉ Sstar.1) →
          KeyBadAggZeroAt
            (family := family) (ground := ground) (A0 := A0) (h0 := h)
            hreg k Sstar (by simpa [fiber] using hSstar)) :
    let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h
    let hdom : ∀ S ∈ dom, Nonempty (WLcert family S) :=
      wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
        (family := family) (ground := ground) (A0 := A0) (h := h) hreg
    let keyImage := dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)
    ∀ k : WLcertKey α, k ∈ keyImage →
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
            hreg k Sstar hSstarCanonical := by
  intro dom hdom keyImage k hk fiber hFiber
  have hCoverExists :
      ∃ Sstar : {S // S ∈ dom}, ∃ hSstar : Sstar ∈ fiber,
        ∀ Ssub ∈ fiber, Ssub ≠ Sstar →
          ∃ x,
            x ∈ realizedXSet
              (dom := dom) fiber Sstar.1 (ground \ (k.2.2.1 ∪ k.2.2.2.1)) ∧
            x ∈ Ssub.1 ∧ x ∉ Sstar.1 := by
    simpa [dom, fiber] using
      (exists_minCard_mem_wlcertAdmissibleFiber_hNotMem_and_realizedX_of_ne
        (family := family) (ground := ground) (A0 := A0) (h0 := h) hreg k hFiber)
  rcases hCoverExists with ⟨Sstar, hSstar, hCover⟩
  have hKnob :
      KeyBadAggZeroAt
        (family := family) (ground := ground) (A0 := A0) (h0 := h)
        hreg k Sstar (by simpa [fiber] using hSstar) := by
    simpa [dom, hdom, keyImage, fiber] using hBuilder k hk Sstar hSstar hCover
  refine ⟨Sstar, hSstar, ?_⟩
  simpa [fiber] using And.intro hCover hKnob

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

theorem b2_recurrence_bridge_of_KeyBadAggZeroAt_builder.{v}
    {α : Type v} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h : α} (B : ℕ → ℕ) (A : ℕ)
    (hreg : O1aUpgradeRegime family ground A0 h)
    (hKeyImage : o1a_wlcert_key_image_bound_target.{v} B)
    (hBuilder :
      let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h
      let hdom : ∀ S ∈ dom, Nonempty (WLcert family S) :=
        wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
          (family := family) (ground := ground) (A0 := A0) (h := h) hreg
      let keyImage := dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)
      ∀ k : WLcertKey α, k ∈ keyImage →
        let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
        ∀ Sstar : {S // S ∈ dom}, ∀ hSstar : Sstar ∈ fiber,
          (∀ Ssub ∈ fiber, Ssub ≠ Sstar →
            ∃ x,
              x ∈ realizedXSet
                (dom := dom) fiber Sstar.1 (ground \ (k.2.2.1 ∪ k.2.2.2.1)) ∧
              x ∈ Ssub.1 ∧ x ∉ Sstar.1) →
          KeyBadAggZeroAt
            (family := family) (ground := ground) (A0 := A0) (h0 := h)
            hreg k Sstar (by simpa [fiber] using hSstar))
    (hRemainder :
      (B ground.card * (coreSliceContains family h).card ^ 2) * (ground.card ^ 20) ≤ A) :
    (o1aWitnessLiftDomWL family h).card ≤
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 + A := by
  have hAssume :
      let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h
      let hdom : ∀ S ∈ dom, Nonempty (WLcert family S) :=
        wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
          (family := family) (ground := ground) (A0 := A0) (h := h) hreg
      let keyImage := dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)
      ∀ k : WLcertKey α, k ∈ keyImage →
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
              hreg k Sstar hSstarCanonical :=
    hAssume_of_KeyBadAggZeroAt_builder
      (family := family) (ground := ground) (A0 := A0) (h := h) hreg hBuilder
  exact
    b2_recurrence_bridge_of_KeyBadAggZeroAt_realized
      (family := family) (ground := ground) (A0 := A0) (h := h) (B := B) (A := A)
      hreg hKeyImage hAssume hRemainder

theorem keyBadAgg_builder_on_minFiber_hardUpgrade.{v}
    {α : Type v} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h : α}
    (hreg : O1aUpgradeRegime family ground A0 h)
    (h2 : 2 ≤ maxCoDegree family ground)
    (hSplitBuilder :
      let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h
      let hdom : ∀ S ∈ dom, Nonempty (WLcert family S) :=
        wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
          (family := family) (ground := ground) (A0 := A0) (h := h) hreg
      let keyImage := dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)
      ∀ k : WLcertKey α, k ∈ keyImage →
        let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
        ∀ Sstar : {S // S ∈ dom}, ∀ hSstar : Sstar ∈ fiber,
          (∀ Ssub ∈ fiber, Ssub ≠ Sstar →
            ∃ x,
              x ∈ realizedXSet
                (dom := dom) fiber Sstar.1 (ground \ (k.2.2.1 ∪ k.2.2.2.1)) ∧
              x ∈ Ssub.1 ∧ x ∉ Sstar.1) →
          ((∃ j, j ∈ Sstar.1 ∧ j ∈ Nmax family ground h ∧
              ∃ U ∈ WmaxAt family ground h j, ∃ V ∈ WmaxAt family ground h j, U ≠ V) ∨
            Sstar.1 ∩ supportMaxCoDegreePairs family ground = ∅) →
          KeyBadAggZeroAt
            (family := family) (ground := ground) (A0 := A0) (h0 := h)
            hreg k Sstar (by simpa [fiber] using hSstar)) :
    let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h
    let hdom : ∀ S ∈ dom, Nonempty (WLcert family S) :=
      wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
        (family := family) (ground := ground) (A0 := A0) (h := h) hreg
    let keyImage := dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)
    ∀ k : WLcertKey α, k ∈ keyImage →
      let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
      ∀ Sstar : {S // S ∈ dom}, ∀ hSstar : Sstar ∈ fiber,
        (∀ Ssub ∈ fiber, Ssub ≠ Sstar →
          ∃ x,
            x ∈ realizedXSet
              (dom := dom) fiber Sstar.1 (ground \ (k.2.2.1 ∪ k.2.2.2.1)) ∧
            x ∈ Ssub.1 ∧ x ∉ Sstar.1) →
        KeyBadAggZeroAt
          (family := family) (ground := ground) (A0 := A0) (h0 := h)
          hreg k Sstar (by simpa [fiber] using hSstar) := by
  have hPackage :
      (∀ S ∈ o1aWitnessLiftDomWL family h, Nonempty (WLcert family S)) ∧
        (∀ S ∈ o1aWitnessLiftDomWL family h,
          (∃ j, j ∈ S ∧ j ∈ Nmax family ground h ∧
            ∃ U ∈ WmaxAt family ground h j, ∃ V ∈ WmaxAt family ground h j, U ≠ V) ∨
          S ∩ supportMaxCoDegreePairs family ground = ∅) :=
    o1aWitnessLiftDomWL_hardUpgrade_package_of_O1aUpgradeRegime
      (family := family) (ground := ground) (A0 := A0) (h := h) hreg h2
  intro dom hdom keyImage k hk fiber Sstar hSstar hCover
  have hSplit :
      (∃ j, j ∈ Sstar.1 ∧ j ∈ Nmax family ground h ∧
          ∃ U ∈ WmaxAt family ground h j, ∃ V ∈ WmaxAt family ground h j, U ≠ V) ∨
        Sstar.1 ∩ supportMaxCoDegreePairs family ground = ∅ := by
    simpa [dom] using hPackage.2 Sstar.1 Sstar.2
  simpa [dom, hdom, keyImage, fiber] using hSplitBuilder k hk Sstar hSstar hCover hSplit

theorem b2_spine_card_o1aWitnessLiftDomWL_le_B_mul_slice_sq_mul_pow20_of_keyBadAgg_builder_on_minFiber_hardUpgrade.{v}
    {α : Type v} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h : α} (B : ℕ → ℕ)
    (hreg : O1aUpgradeRegime family ground A0 h)
    (h2 : 2 ≤ maxCoDegree family ground)
    (hKeyImage : o1a_wlcert_key_image_bound_target.{v} B)
    (hSplitBuilder :
      let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h
      let hdom : ∀ S ∈ dom, Nonempty (WLcert family S) :=
        wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
          (family := family) (ground := ground) (A0 := A0) (h := h) hreg
      let keyImage := dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)
      ∀ k : WLcertKey α, k ∈ keyImage →
        let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
        ∀ Sstar : {S // S ∈ dom}, ∀ hSstar : Sstar ∈ fiber,
          (∀ Ssub ∈ fiber, Ssub ≠ Sstar →
            ∃ x,
              x ∈ realizedXSet
                (dom := dom) fiber Sstar.1 (ground \ (k.2.2.1 ∪ k.2.2.2.1)) ∧
              x ∈ Ssub.1 ∧ x ∉ Sstar.1) →
          ((∃ j, j ∈ Sstar.1 ∧ j ∈ Nmax family ground h ∧
              ∃ U ∈ WmaxAt family ground h j, ∃ V ∈ WmaxAt family ground h j, U ≠ V) ∨
            Sstar.1 ∩ supportMaxCoDegreePairs family ground = ∅) →
          KeyBadAggZeroAt
            (family := family) (ground := ground) (A0 := A0) (h0 := h)
            hreg k Sstar (by simpa [fiber] using hSstar)) :
    (o1aWitnessLiftDomWL family h).card ≤
      (B ground.card * (coreSliceContains family h).card ^ 2) * (ground.card ^ 20) := by
  have hBuilder :
      let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h
      let hdom : ∀ S ∈ dom, Nonempty (WLcert family S) :=
        wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
          (family := family) (ground := ground) (A0 := A0) (h := h) hreg
      let keyImage := dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)
      ∀ k : WLcertKey α, k ∈ keyImage →
        let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
        ∀ Sstar : {S // S ∈ dom}, ∀ hSstar : Sstar ∈ fiber,
          (∀ Ssub ∈ fiber, Ssub ≠ Sstar →
            ∃ x,
              x ∈ realizedXSet
                (dom := dom) fiber Sstar.1 (ground \ (k.2.2.1 ∪ k.2.2.2.1)) ∧
              x ∈ Ssub.1 ∧ x ∉ Sstar.1) →
          KeyBadAggZeroAt
            (family := family) (ground := ground) (A0 := A0) (h0 := h)
            hreg k Sstar (by simpa [fiber] using hSstar) :=
    keyBadAgg_builder_on_minFiber_hardUpgrade
      (family := family) (ground := ground) (A0 := A0) (h := h) hreg h2 hSplitBuilder
  have hAssume :
      let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h
      let hdom : ∀ S ∈ dom, Nonempty (WLcert family S) :=
        wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
          (family := family) (ground := ground) (A0 := A0) (h := h) hreg
      let keyImage := dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)
      ∀ k : WLcertKey α, k ∈ keyImage →
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
              hreg k Sstar hSstarCanonical :=
    hAssume_of_KeyBadAggZeroAt_builder
      (family := family) (ground := ground) (A0 := A0) (h := h) hreg hBuilder
  exact
    card_o1aWitnessLiftDomWL_le_B_mul_slice_sq_mul_pow20_of_keyImage_bound_target_and_KeyBadAggZeroAt_realized
      (family := family) (ground := ground) (A0 := A0) (h := h) (B := B) hreg hKeyImage hAssume

theorem b2_recurrence_bridge_of_split_to_KeyBadAgg_under_O1aUpgradeRegime.{v}
    {α : Type v} [DecidableEq α]
    {family : Finset (Finset α)} {ground : Finset α} {A0 : ℕ} {h : α} (B : ℕ → ℕ) (A : ℕ)
    (hreg : O1aUpgradeRegime family ground A0 h)
    (h2 : 2 ≤ maxCoDegree family ground)
    (hKeyImage : o1a_wlcert_key_image_bound_target.{v} B)
    (hSplitBuilder :
      let dom : Finset (Finset α) := o1aWitnessLiftDomWL family h
      let hdom : ∀ S ∈ dom, Nonempty (WLcert family S) :=
        wlcert_exists_on_o1aWitnessLiftDomWL_of_O1aUpgradeRegime
          (family := family) (ground := ground) (A0 := A0) (h := h) hreg
      let keyImage := dom.attach.image (wlcertKeyOnDom (family := family) dom hdom)
      ∀ k : WLcertKey α, k ∈ keyImage →
        let fiber : Finset {S // S ∈ dom} := wlcertAdmissibleFiber_hNotMem (family := family) dom k
        ∀ Sstar : {S // S ∈ dom}, ∀ hSstar : Sstar ∈ fiber,
          (∀ Ssub ∈ fiber, Ssub ≠ Sstar →
            ∃ x,
              x ∈ realizedXSet
                (dom := dom) fiber Sstar.1 (ground \ (k.2.2.1 ∪ k.2.2.2.1)) ∧
              x ∈ Ssub.1 ∧ x ∉ Sstar.1) →
          ((∃ j, j ∈ Sstar.1 ∧ j ∈ Nmax family ground h ∧
              ∃ U ∈ WmaxAt family ground h j, ∃ V ∈ WmaxAt family ground h j, U ≠ V) ∨
            Sstar.1 ∩ supportMaxCoDegreePairs family ground = ∅) →
          KeyBadAggZeroAt
            (family := family) (ground := ground) (A0 := A0) (h0 := h)
            hreg k Sstar (by simpa [fiber] using hSstar))
    (hRemainder :
      (B ground.card * (coreSliceContains family h).card ^ 2) * (ground.card ^ 20) ≤ A) :
    (o1aWitnessLiftDomWL family h).card ≤
      maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 + A := by
  have hSpine :
      (o1aWitnessLiftDomWL family h).card ≤
        (B ground.card * (coreSliceContains family h).card ^ 2) * (ground.card ^ 20) := by
    exact
      b2_spine_card_o1aWitnessLiftDomWL_le_B_mul_slice_sq_mul_pow20_of_keyBadAgg_builder_on_minFiber_hardUpgrade
        (family := family) (ground := ground) (A0 := A0) (h := h) (B := B)
        hreg h2 hKeyImage hSplitBuilder
  have hA :
      (o1aWitnessLiftDomWL family h).card ≤ A := by
    exact hSpine.trans hRemainder
  have hLift :
      A ≤ maxSunflowerFreeCard (ground \ ({h} : Finset α)) 3 + A := by
    exact Nat.le_add_left _ _
  exact hA.trans hLift

end SunflowerLean
