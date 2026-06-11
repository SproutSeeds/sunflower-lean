# FORMAL_RESULTS_M3 — paper ↔ Lean mapping

Companion to the paper *"Three-sunflower-free set systems with bounded
pairwise intersections"* (draft in
`erdos-problems/packs/sunflower/problems/857/bld_note/`). Every row's
axiom audit below is the verbatim `#print axioms` output (30 results),
re-derived 2026-06-11 against the full green `lake build` (toolchain
`leanprover/lean4:v4.26.0`, mathlib `v4.26.0`).

Axiom profiles:

- **kernel** = `[propext, Classical.choice, Quot.sound]` (Lean's three
  standard axioms; some rows use only a subset). No `sorryAx` anywhere.
- **kernel+LRAT** = the above plus `[Lean.ofReduceBool,
  Lean.trustCompiler]`: the result consumes a committed LRAT
  certificate whose check runs through the compiler (`native_decide`),
  the same trust profile as this repository's existing
  `M_n_3_upper_bridge` results.

## Definitions

| Object | Lean name | File |
|---|---|---|
| admissible family for M3(l,t) | `M3.M3Admissible` | `SunflowerLean/M3/Defs.lean` |
| admissible family for I3(l,t) (intersecting) | `M3.I3Admissible` | `SunflowerLean/M3/Defs.lean` |
| 3-sunflower (empty core included) | `IsSunflower` (reused) | `SunflowerLean/Basic.lean` |

## Theorems

| Paper statement | Lean name | File | Axioms |
|---|---|---|---|
| Lemma 2.4 (doubling): two disjoint I3-admissible copies form an M3-admissible family, M3 ≥ 2·I3 | `M3.doubling`, `M3.M3_ge_two_I3` | `M3/Doubling.lean` | kernel |
| Thm 1.1 step (i): point degree ≤ 2 at cap 1 | `M3.degree_le_two` | `M3/T1Exact.lean` | kernel |
| Thm 1.1 (intersecting): I3(l,1) ≤ l+1 | `M3.I3_card_le_t1` | `M3/T1Exact.lean` | kernel |
| Thm 1.1 (upper): M3(l,1) ≤ 2l+2 | `M3.M3_card_le_t1` | `M3/T1Exact.lean` | kernel |
| Thm 1.1 (witness): K_{l+1} star family, I3-admissible(l,1), card l+1 for l ≥ 2 | `M3.starFam_I3Admissible`, `M3.starFam_card` | `M3/T1Exact.lean` | kernel |
| Thm 1.1 (exact): I3(l,1) = l+1, M3(l,1) = 2l+2 (l ≥ 2) | `M3.I3_one_exact`, `M3.M3_one_exact` | `M3/T1Exact.lean` | kernel |
| Thm 1.1 equality rigidity (intersecting): extremal I3(l,1) families have complete-graph star incidence | `M3.I3_extremal_no_private_points`, `M3.I3_extremal_degree_eq_two`, `M3.I3_unique_common_point_t1`, `M3.I3_extremal_star_incidence` | `M3/T1Rigidity.lean` | kernel |
| t=1 table rows l = 2,3,4 (I3 = 3,4,5; M3 = 6,8,10) | `M3.I3_2_1_row` … `M3.M3_4_1_row` | `M3/SmallValues.lean` | kernel |
| Lemma 2.1 base: M3(l,0) ≤ 2 | `M3.M3_card_le_t0` | `M3/LinkRecursion.lean` | kernel |
| Lemma 2.1 (link recursion): M3(l,t) ≤ 2 + 2l·B given link bound B | `M3.link_recursion` | `M3/LinkRecursion.lean` | kernel |
| Link-recursion corollary: M3(l,2) ≤ 4l² + 2 | `M3.M3_card_le_t2` | `M3/LinkRecursion.lean` | kernel |
| Thm 1.2 sharp counting upper bound: M3(l,2) ≤ 3l²-l+2 for l ≥ 3 | `M3.M3_card_le_t2_sharp` | `M3/T2Counting.lean` | kernel |
| Support/relabel soundness: Fin ((v+1)·l) bounds are universal | `M3.M3_upper_of_fin`, `M3.I3_upper_of_fin` | `M3/Relabel.lean` | kernel |
| SAT bridge soundness: UNSAT ⇒ cardinality bound on Fin n | `M3.m3_bridge`, `M3.i3_bridge` | `M3/SATEncoding.lean` | kernel+LRAT* |
| Engine value, witness side: I3(4,2) ≥ 12 (I12 on 10 points) | `M3.I3_4_2_lower` | `M3/SmallValues.lean` | kernel |
| Doubled I12: M3(4,2) ≥ 24 (paper's bracket, lower half) | `M3.M3_4_2_lower` | `M3/SmallValues.lean` | kernel |
| Encoder anchors: no 7-member M3(2,1)- / 21-member M3(3,2)-family on Fin 7 | `M3.M3_2_1_fin7_anchor`, `M3.M3_3_2_fin7_anchor` | `M3/SmallValues.lean` | kernel+LRAT |
| Lemma 4.1 (pencil): an orthogoval pair of order q yields an I3-admissible(2q+2, 2) family of card q²+q+1 | `M3.pencilFam_I3Admissible`, `M3.pencilFam_card` | `M3/Pencil.lean` | kernel |
| Lemma 4.1 + 2.4: doubled pencil family, M3-admissible, card 2(q²+q+1) | `M3.doubled_pencilFam` | `M3/Pencil.lean` | kernel |
| Non-vacuity: explicit orthogoval pair at q = 2 (Fano pair) | `M3.fanoOrthogovalPair` | `M3/Pencil.lean` | kernel |
| Thm 1.2 (lower): M3(l,2) ≥ (l−2)²/8 for l ≥ 4, conditional on `OrthogovalExistence` | `M3.M3_quadratic_lower` | `M3/Bertrand.lean` | kernel |

\* The bridge *theorems* inherit the LRAT profile from the shared
SATBridge internals; their clause-spec lemmas
(`capViolationClauses_spec` etc.) are kernel-only.

Conditionality note (verbatim policy): `M3.M3_quadratic_lower` and the
F5 results are **formalized modulo the cited existence theorem** —
CIJSSS, arXiv:2210.11961, Theorem 2.2 (orthogoval planes at every prime
power) is cited, not formalized; the hypothesis class `OrthogovalPair`
packages exactly what it provides, and `fanoOrthogovalPair` certifies
the class non-vacuous at q = 2 by kernel `decide`.

## Verbatim audit output (2026-06-11)

```
'M3.doubling' depends on axioms: [propext, Classical.choice, Quot.sound]
'M3.M3_ge_two_I3' depends on axioms: [propext, Classical.choice, Quot.sound]
'M3.degree_le_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'M3.I3_card_le_t1' depends on axioms: [propext, Classical.choice, Quot.sound]
'M3.M3_card_le_t1' depends on axioms: [propext, Classical.choice, Quot.sound]
'M3.starFam_I3Admissible' depends on axioms: [propext, Classical.choice, Quot.sound]
'M3.starFam_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'M3.I3_one_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'M3.M3_one_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'M3.I3_extremal_no_private_points' depends on axioms: [propext, Classical.choice, Quot.sound]
'M3.I3_extremal_degree_eq_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'M3.I3_unique_common_point_t1' depends on axioms: [propext, Quot.sound]
'M3.I3_extremal_star_incidence' depends on axioms: [propext, Classical.choice, Quot.sound]
'M3.M3_card_le_t0' depends on axioms: [propext, Classical.choice, Quot.sound]
'M3.link_recursion' depends on axioms: [propext, Classical.choice, Quot.sound]
'M3.M3_card_le_t2' depends on axioms: [propext, Classical.choice, Quot.sound]
'M3.M3_card_le_t2_sharp' depends on axioms: [propext, Classical.choice, Quot.sound]
'M3.M3_upper_of_fin' depends on axioms: [propext, Classical.choice, Quot.sound]
'M3.I3_upper_of_fin' depends on axioms: [propext, Classical.choice, Quot.sound]
'M3.m3_bridge' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]
'M3.i3_bridge' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]
'M3.I3_4_2_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'M3.M3_4_2_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'M3.M3_2_1_fin7_anchor' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]
'M3.M3_3_2_fin7_anchor' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]
'M3.pencilFam_I3Admissible' depends on axioms: [propext, Classical.choice, Quot.sound]
'M3.pencilFam_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'M3.doubled_pencilFam' depends on axioms: [propext, Classical.choice, Quot.sound]
'M3.fanoOrthogovalPair' depends on axioms: [propext, Classical.choice, Quot.sound]
'M3.M3_quadratic_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## LRAT certificate inventory

| Certificate | CNF | Result it feeds |
|---|---|---|
| `SunflowerLean/M3/sat_m3_7_2_1_7.lrat` | `M3.m3CNF 7 2 1 7` | `M3.M3_2_1_fin7_anchor` |
| `SunflowerLean/M3/sat_m3_7_3_2_21.lrat` | `M3.m3CNF 7 3 2 21` | `M3.M3_3_2_fin7_anchor` |

Reproduce: `lake env lean --run tools/export_m3_cnf.lean` writes the
DIMACS files; `cadical --plain --lrat --no-binary <cnf> <lrat>`
regenerates certificates; the in-repo `native_decide` checks re-verify
the committed certificates against the Lean-generated CNFs on every
build (no external tool needed for verification).

## Engine results that remain checker-level (not Lean)

I3(4,2) ≤ 12 (orderly exhaustion, 36,329,094 nodes) — the ≥ 12 half
and the doubled M3(4,2) ≥ 24 are kernel-verified above; the ≤ 12 half
is engine + deterministic checker in the erdos-problems pack (SAT
certification attempt recorded in MASTER_PLAN_TO_DONE.md under F4c).
Other t = 2 engine bounds (e.g. I3(5,2) ≥ 16) remain checker-level.
