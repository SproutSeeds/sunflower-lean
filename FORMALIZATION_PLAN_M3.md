# Formalization Plan: M3(l,t) — the uniform, intersection-capped spine

Companion to the paper *"Three-sunflower-free set systems with bounded
pairwise intersections"* (draft in
`erdos-problems/packs/sunflower/problems/857/three_sunflower_paper/`). Goal: formalize
the paper's spine in this repo before arXiv submission, unifying the
M(n,3) weak-value certifications (already here) and the uniform capped
results (the paper) under one kernel-verified methodology.

Working protocol (unchanged from this repo's standing discipline):
models generate candidates; `lake build` is the only acceptance criterion;
nothing is claimed or committed with `sorry`; SAT results ship with
independently checkable LRAT certificates; provenance recorded per file.

Time-box: two weeks of sessions. The paper ships at box end with whatever
is kernel-verified, and a "formalization in progress" note for the rest.

## Definitions (M0 — `SunflowerLean/M3/Defs.lean`, DONE: kernel-verified)

Reuses `IsSunflower` / `IsSunflowerFree` from `SunflowerLean.Basic`
(empty core included, matching the paper). New predicates:
`IsUniform F l`, `PairwiseCapped F t`, `IsIntersectingFam F`,
`M3Admissible F l t`, `I3Admissible F l t`.

**STATUS 2026-06-11: ALL MILESTONES LANDED** (M4 witness half; its
UNSAT half is blocked, see MASTER_PLAN_TO_DONE.md F4c). M2 =
T1Exact.lean (DONE) plus T1Rigidity.lean (DONE), M3 =
LinkRecursion.lean (DONE) plus T2Counting.lean (DONE), M4 =
Relabel/SATEncoding/SmallValues.lean (witness + anchors DONE), M5 =
Pencil.lean (DONE incl. q=2 instance), M6 = Bertrand.lean (DONE).
Verification: FORMAL_RESULTS_M3.md + verify_m3.sh. This file is kept
as the original milestone design; MASTER_PLAN_TO_DONE.md is the
binding ledger.

## Targets, in milestone order

- M1 — Doubling lemma (`M3/Doubling.lean`). DONE 2026-06-10: kernel-verified,
  zero warnings; axiom audit clean (propext, Classical.choice, Quot.sound —
  no sorryAx) for `M3.doubling` and `M3.M3_ge_two_I3`.
  Statement: if `F` on `α` and `G` on `β` are both I3-admissible(l,t),
  then the family `F.map (embedding of Sum.inl) ∪ G.map (Sum.inr)` on
  `α ⊕ β` is M3-admissible(l,t) with cardinality `F.card + G.card`.
  Proof shape: `Finset.map` preserves cards and intersections; cross
  pairs have empty intersection; the three-case triple analysis
  (within-copy / 2+1 mixed / no all-cross with two copies). Paper
  Lemma 2.4. Pure finite combinatorics; no mathlib depth.

- M2 — t=1 exact (`M3/T1Exact.lean`). Paper Theorem 1.1.
  (a) Upper bound `M3 ≤ 2l+2`: point-degree ≤ 2 (three sets through a
  point at cap 1 form a sunflower with singleton core); intersecting
  pairs ≤ (degree sum)/2 = m*l/2; disjoint pairs ≤ m²/4 by Mantel on the
  disjointness graph (mathlib: Turán/triangle-free edge bound — use
  `SimpleGraph` Turán API if friction is low, else a direct double-count
  of cherries, which is ~30 lines and dependency-free); conclude
  `m(m-1)/2 ≤ m²/4 + m*l/2` → `m ≤ 2l+2` by `omega`/`nlinarith`.
  (b) Intersecting cap `I3 ≤ l+1`: same counting, disjoint term zero.
  (c) Witness `I3(l,1) ≥ l+1`: the K_{l+1} star family, formalized
  parametrically — ground type `Sym2 (Fin (l+1))` (edges), star of `v` =
  edges incident to `v`; pairwise intersection = the single edge
  `s(v,w)`; cores pairwise distinct. (d) `M3(l,1) = 2l+2` by M1 + (a).
  For small `l`, `decide`/`native_decide` cross-checks of (a) mirror the
  existing `M_n_3` idiom. Equality-case rigidity for the intersecting
  extremals is formalized separately in `M3/T1Rigidity.lean`.

- M3 — Link recursion (`M3/LinkRecursion.lean`). Paper Lemma 2.1:
  `M3(l,t) ≤ 2 + 2l * M3(l-1, t-1)` and `M3(l,0) ≤ 2`. Maximal disjoint
  pair + pigeonhole on the ≤ 2l covered points + link inherits
  (uniform l-1, capped t-1, SF-free; lifting lemma re-adjoining x).
  Corollary: `M3(l,2) ≤ 4l² + 2` from M2; superseded for the paper headline by the sharp counting file `M3/T2Counting.lean`, proving `M3(l,2) ≤ 3l²-l+2` for `l ≥ 3`.

- M4 — Small exact values via the SAT bridge (`M3/SmallValues.lean` +
  encoder extension). Re-target the existing Lean-to-SAT pipeline:
  add uniformity and pairwise-cap clauses to the CNF generator
  (incidence-matrix encoding as for M(n,3); the SF-freeness clauses are
  unchanged). Ground-set soundness lemma (easy, formalize first): any
  family of m l-sets has support of size ≤ m*l, hence embeds into
  `Fin (m*l)`; so UNSAT at target v+1 over `Fin ((v+1)*l)` certifies the
  upper bound. Targets, with paper/engine expected values:
  I3(4,2) = 12 (the engine-exhausted value; LRAT this), the t=1 table
  rows l ≤ 4 (decide), and the unrestricted anchors f(2,3) = 6,
  f(3,3) = 20 as cross-validation against the existing M(n,3)-style
  machinery. Every LRAT certificate committed and re-checkable.

- M5 — Conditional pencil lemma (`M3/Pencil.lean`). Paper Lemma 4.1,
  formalized CONDITIONALLY, mirroring how the paper cites CIJSSS
  Theorem 2.2: define `OrthogovalPair` abstractly (two line-systems on a
  point type: each a "projective-plane-like" incidence with the
  two-points-one-line-per-plane property; no shared lines; cross
  intersections ≤ 2); prove: an orthogoval pair of order q yields an
  I3-admissible(2q+2, 2) family of cardinality q²+q+1 (sizes, exact-2
  intersections, key uniqueness, no equal-core triple). Then doubling
  (M1) gives the paper's lower bound modulo the cited existence theorem.
  Concrete instances: `decide`-certify an explicit orthogoval pair at
  q = 2 or 3 (small enough for kernel-native checking) so the
  hypothesis class is demonstrably non-vacuous.
  NOT in scope: formalizing CIJSSS's Cremona construction for all prime
  powers (months-scale; cited, exactly as in the paper).

- M6 — Unconditional all-l constant (`M3/Bertrand.lean`).
  `M3(l,2) ≥ (l-2)²/8` for l ≥ 4 via M5 + M1 + mathlib's Bertrand
  (`Nat.bertrand` / `Nat.exists_prime_lt_and_le_two_mul`). The
  (1/2−o(1)) refinement (Baker–Harman–Pintz) stays a cited classical
  result — explicitly out of formalization scope.

## Explicitly out of scope (cite, don't formalize)

CIJSSS Theorem 2.2 (all prime powers); Baker–Harman–Pintz; the Ramsey
bracket's R(3,k) asymptotics (the bracket is a remark in the paper; if
desired later, `M < R(3, I3+1)` is formalizable against a mathlib Ramsey
API, but it gates nothing).

## Paper interlock

Each milestone that lands gets a line in the paper's Data section
("formalized in Lean 4, sorry-free, [repo]"). If all of M1–M4 land in
the box, the paper's two headline theorems are kernel-verified at t=1
and kernel-verified-modulo-citation at t=2, with all computational
claims LRAT-certified — at which point the verification story in the
paper upgrades from "deterministic checkers" to "Lean kernel + LRAT".

## Provenance

Plan drafted 2026-06-10 by Claude (Fable) with Cody Mitchell, following
the repo's standing AI-disclosure policy (`AI_DISCLOSURE.md`): models
propose, the kernel disposes.
