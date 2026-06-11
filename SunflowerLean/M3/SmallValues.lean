/-
  M3 (F4c/F4d): small exact values — witnesses and certified bounds.

  F4c witness half: I12, the engine's optimal I3(4,2) family (12
  four-sets on 10 points, pairwise intersecting, intersections of size
  1 and 2, 3-sunflower-free), ported from
  erdos-problems/packs/sunflower/problems/857/m3_small_l_exact_orderly.mjs
  (I12_L4_T2, relabeled from points 4..13 to 0..9) and re-certified here
  by kernel `decide` (no native_decide on the witness side).

  Authors: Cody Mitchell, Claude (Fable)
  Date: June 2026
  Provenance: witness found by the deterministic orderly engine
  (36,329,094 nodes exhaustion, I3(4,2) = 12 exact engine-side);
  acceptance criterion here is `lake build` (kernel) + axiom audit.
-/

import SunflowerLean.M3.SATEncoding

namespace M3

/-- The engine's I3(4,2) optimum: 12 pairwise-intersecting 4-sets on 10
    points, pairwise intersections of size ≤ 2, 3-sunflower-free. -/
def i12Witness : Finset (Finset (Fin 10)) :=
  { {0, 1, 2, 3}, {0, 4, 5, 6}, {0, 4, 7, 8}, {1, 2, 4, 9},
    {1, 3, 4, 5}, {1, 5, 7, 8}, {1, 6, 7, 9}, {2, 3, 6, 7},
    {2, 4, 6, 8}, {2, 5, 8, 9}, {3, 4, 7, 9}, {3, 6, 8, 9} }

theorem i12Witness_card : i12Witness.card = 12 := by decide

set_option maxRecDepth 65536 in
-- The kernel `decide` walks C(12,3) = 220 subfamilies of explicit Fin 10
-- set literals; the default heartbeat budget is far too small for it.
set_option maxHeartbeats 4000000 in
-- See the comment above: 220-subfamily kernel decide.
theorem i12Witness_admissible : I3Admissible i12Witness 4 2 :=
  ⟨⟨by unfold IsUniform; decide, by unfold PairwiseCapped; decide,
    (SunflowerLean.isSFreeC_iff _ 3).mp (by decide)⟩,
   by unfold IsIntersectingFam; decide⟩

/-- F4c, lower bound: `I3(4,2) ≥ 12`, kernel-verified witness. -/
theorem I3_4_2_lower :
    ∃ F : Finset (Finset (Fin 10)), I3Admissible F 4 2 ∧ F.card = 12 :=
  ⟨i12Witness, i12Witness_admissible, i12Witness_card⟩

end M3
