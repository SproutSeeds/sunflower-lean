#!/bin/sh
# verify_m3.sh — one-shot verification of the M3 development.
# Runs the full lake build (which itself re-checks the committed LRAT
# certificates against the Lean-generated CNFs via native_decide), then
# audits the axioms of every M3 result and fails on sorryAx or any
# axiom outside the documented profiles (see FORMAL_RESULTS_M3.md).
# Exit code 0 = everything green.
set -e
cd "$(dirname "$0")"

echo "== lake build (full library, includes LRAT rechecks) =="
lake build

echo "== axiom audits =="
AUDIT=$(lake env lean --stdin <<'LEAN'
import SunflowerLean.M3
#print axioms M3.doubling
#print axioms M3.M3_ge_two_I3
#print axioms M3.degree_le_two
#print axioms M3.I3_card_le_t1
#print axioms M3.M3_card_le_t1
#print axioms M3.starFam_I3Admissible
#print axioms M3.starFam_card
#print axioms M3.I3_one_exact
#print axioms M3.M3_one_exact
#print axioms M3.I3_extremal_no_private_points
#print axioms M3.I3_extremal_degree_eq_two
#print axioms M3.I3_unique_common_point_t1
#print axioms M3.I3_extremal_star_incidence
#print axioms M3.M3_card_le_t0
#print axioms M3.link_recursion
#print axioms M3.M3_card_le_t2
#print axioms M3.M3_card_le_t2_sharp
#print axioms M3.M3_card_le_t2_no_singletons
#print axioms M3.inter_card_sum_eq_deg_offDiag
#print axioms M3.M3_t3_no_exact3_card_le_t2_sharp
#print axioms M3.M3_extremal_two_disjoint_stars_of_split
#print axioms M3.disjGraph_cliqueFree
#print axioms M3.disjGraph_edge_le
#print axioms M3.inter_pairs_le
#print axioms M3.disjoint_pairs_ge
#print axioms M3.two_mul_edge_eq_disjoint_pairs
#print axioms M3.disjGraph_edge_eq
#print axioms M3.disjGraph_isTuranMaximal
#print axioms M3.disjGraph_nonempty_iso_turanGraph
#print axioms M3.fin_residue0_card
#print axioms M3.fin_residue1_card
#print axioms M3.disjGraph_extremal_bipartition
#print axioms M3.M3_extremal_classification
#print axioms M3.disjGraph_turanMaximal_bipartition
#print axioms M3.M3_mantel_tight_reduction
#print axioms M3.M3_upper_of_fin
#print axioms M3.I3_upper_of_fin
#print axioms M3.m3_bridge
#print axioms M3.i3_bridge
#print axioms M3.I3_4_2_lower
#print axioms M3.M3_4_2_lower
#print axioms M3.M3_2_1_fin7_anchor
#print axioms M3.M3_3_2_fin7_anchor
#print axioms M3.pencilFam_I3Admissible
#print axioms M3.pencilFam_card
#print axioms M3.doubled_pencilFam
#print axioms M3.fanoOrthogovalPair
#print axioms M3.M3_quadratic_lower
LEAN
)
echo "$AUDIT"

# join wrapped axiom lists onto single lines
NORM=$(printf '%s\n' "$AUDIT" | awk "/^'/{if(buf)print buf; buf=\$0; next}{buf=buf\" \"\$0} END{if(buf)print buf}")

echo "== audit checks =="
COUNT=$(printf '%s\n' "$NORM" | grep -c "depends on axioms") || true
if [ "$COUNT" -ne 48 ]; then
  echo "FAIL: expected 48 audited results, saw $COUNT"; exit 1
fi
if printf '%s\n' "$NORM" | grep -q "sorryAx"; then
  echo "FAIL: sorryAx found"; exit 1
fi
# strip the documented axioms; anything left on an axiom line is foreign
FOREIGN=$(printf '%s\n' "$NORM" | tr -d '[],' | tr ' ' '\n' \
  | grep -v -E "^(propext|Classical\.choice|Quot\.sound|Lean\.ofReduceBool|Lean\.trustCompiler|depends|on|axioms:?)$" \
  | grep -v "^'" | grep -v "^$") || true
if [ -n "$FOREIGN" ]; then
  echo "FAIL: unexpected axiom tokens:"; echo "$FOREIGN"; exit 1
fi
# the kernel-only spine must not mention the compiler axioms; native finite
# reductions are confined to the bridge/LRAT and explicit I12 witness lanes.
SPINE=$(printf '%s\n' "$NORM" | grep -v -E "m3_bridge|i3_bridge|fin7_anchor|I3_4_2_lower|M3_4_2_lower")
if printf '%s\n' "$SPINE" | grep -q "ofReduceBool"; then
  echo "FAIL: compiler axiom leaked into the kernel spine"; exit 1
fi

echo "== LRAT certificate presence =="
for f in SunflowerLean/M3/sat_m3_7_2_1_7.lrat SunflowerLean/M3/sat_m3_7_3_2_21.lrat; do
  [ -s "$f" ] || { echo "FAIL: missing certificate $f"; exit 1; }
done

echo "VERIFY_M3: ALL GREEN"
