# MASTER PLAN TO DONE — M3(l,t): formalize, integrate, publish

THE GOAL, in one sentence: the paper "Three-sunflower-free set systems with
bounded pairwise intersections" is publicly posted (arXiv + Zenodo DOI) with
its spine formally verified in Lean 4 in this repository, the repository is
public, citable, reproducible, and linked from the paper, and the relevant
Erdős-problem forum threads carry the announcement comments — with every
step verified before it is claimed.

This file is the single source of truth for the run-until-done loop. Each
session: read this file, pick the FIRST unchecked non-OWNER item, complete
it to its acceptance criterion, flip its checkbox with a dated note, and
continue. OWNER items (marked 🔑) are Cody's buttons: the agent PREPARES
everything for them, queues them, and reports them at session end — never
performs them. The loop is done when every box is checked.

## Standing rules (apply to every item, no exceptions)

- Kernel is ground truth: nothing Lean is claimed/checked-off without
  `lake build` success AND `#print axioms` showing only
  [propext, Classical.choice, Quot.sound] (no sorryAx) for every new result.
- SAT results require committed LRAT certificates re-checkable by an
  independent verifier; the recheck command is part of the acceptance.
- No `sorry` in any committed file. Warning-clean preferred; deviations noted.
- Provenance headers on every new file (authors, date, models-propose/
  kernel-disposes note).
- The agent NEVER pushes to GitHub, posts publicly, or submits anywhere.
  All public actions are 🔑 OWNER items. LOCAL git commits of verified,
  sorry-free work are authorized (owner confirmation, 2026-06-10); the
  push and everything beyond it remain owner-only.
- Mechanically verify every ordering/numbering/cross-reference claim
  (this project's recurring lesson).
- Paper edits recompile cleanly (2× pdflatex: 0 errors, 0 overfulls) before
  check-off.

## Phase F — Formalization (sunflower-lean)

- [x] F0. Definitions module `SunflowerLean/M3/Defs.lean`
      (IsUniform, PairwiseCapped, IsIntersectingFam, M3Admissible,
      I3Admissible). DONE 2026-06-10, kernel-verified.
- [x] F1. Doubling lemma `SunflowerLean/M3/Doubling.lean`
      (`M3.doubling`, `M3.M3_ge_two_I3`). DONE 2026-06-10,
      kernel-verified, axiom audit clean, zero warnings.
- [x] F2. t=1 exact theorem `SunflowerLean/M3/T1Exact.lean` (paper Thm 1.1).
      DONE 2026-06-10 — all sub-items kernel-verified, axiom audits clean.
      Sub-items, each kernel-gated:
      - [x] F2a. Degree lemma. DONE 2026-06-10: `inter_eq_singleton_of_capped`,
            `no_three_through_point`, `degree_le_two` in M3/T1Exact.lean;
            lake build green first attempt; axioms: [propext, Quot.sound] /
            [propext, Classical.choice, Quot.sound] — no sorryAx.
      - [x] F2b. Counting upper bound `I3 ≤ l+1`. DONE 2026-06-10:
            `M3.I3_card_le_t1` in M3/T1Exact.lean — each ordered distinct
            pair maps to its unique common point (card_eq_sum_card_fiberwise);
            fibers ⊆ (filter x).offDiag so ≤ deg²−deg ≤ deg (degree_le_two);
            Σ deg = m·l by sum swap; m(m−1) ≤ m·l → m ≤ l+1. lake build
            green, zero warnings; axioms [propext, Classical.choice,
            Quot.sound] — no sorryAx.
      - [x] F2c. DONE 2026-06-10 (route revised, Mantel not needed): the
            partition at a fixed member A replaces the disjointness-graph
            bound — `disjoint_part_intersecting` (members disjoint from A
            pairwise intersect, else empty-core 3-sunflower with A) +
            `meets_part_card_le` (members meeting A inject into A's points
            by key uniqueness + degree lemma) + `M3Admissible.subset`.
            Same parent acceptance (F2d below) reached with a simpler
            kernel object. lake build green first attempt, zero warnings;
            axioms clean, no sorryAx.
      - [x] F2d. Counting upper bound `M3 ≤ 2l+2`. DONE 2026-06-10:
            `M3.M3_card_le_t1` in M3/T1Exact.lean — F ⊆ Dis ∪ Mee ∪ {A},
            |Dis| ≤ l+1 by F2b (intersecting subfamily), |Mee| ≤ l by
            injection into A; l = 0 and F = ∅ edge cases handled. axioms
            [propext, Classical.choice, Quot.sound] — no sorryAx.
      - [x] F2e. Star witness. DONE 2026-06-10: `starAt`/`starFam` over
            `Sym2 (Fin (l+1))`; `starFam_I3Admissible` (all l) and
            `starFam_card = l+1` (for 2 ≤ l — at l=1 the two stars of K₂
            coincide, matching the paper's l ≥ 2). starAt_card,
            starAt_inter (= {s(u,v)}), starAt_injective. lake build green
            (one omega fix-up for l+1-1), zero warnings; axioms [propext,
            Classical.choice, Quot.sound] — no sorryAx.
      - [x] F2f. Exact statements. DONE 2026-06-10: `I3_one_exact` and
            `M3_one_exact` (l ≥ 2) in the SmallCases existence-plus-
            universal-upper-bound idiom; M3 witness = doubled star family
            via M3_ge_two_I3. lake build green, zero warnings; axioms
            [propext, Classical.choice, Quot.sound] — no sorryAx.
      - [x] F2g. decide cross-checks. DONE 2026-06-10: starFam_two/_three
            card + admissibility anchors (I3(2,1)=3, I3(3,1)=4) via kernel
            `decide` + SunflowerLean.isSFreeC_iff bridge — deliberately NO
            native_decide, so axioms stay [propext, Classical.choice,
            Quot.sound] (no ofReduceBool); maxRecDepth 8192 at l=3.
            Doubled-family decide anchor dropped: kernel reduction sticks
            on Sum/map/union instances; the doubled card is already the
            kernel theorem M3_one_exact.
- [x] F3. Link recursion `SunflowerLean/M3/LinkRecursion.lean` (paper
      Lemma 2.1). DONE 2026-06-10: `M3_card_le_t0` (≤ 2 at cap 0);
      `link`/`erase_inter_erase`/`erase_injOn_through`/`link_admissible`
      (uniform l−1, capped t−1, SF-free via insert-x lift);
      `card_through_le`; `link_recursion` (F.card ≤ 2 + 2l·B given any
      link bound B; disjoint-pair vs intersecting case split, biUnion
      cover counting); corollary `M3_card_le_t2` (≤ 4l²+2 via F2's
      M3_card_le_t1). lake build green (3 fix iterations: Set coercion
      for standalone InjOn, beta-reduction bridge, push_neg Nonempty
      form), zero warnings in-file; all five declarations audit to
      [propext, Classical.choice, Quot.sound] — no sorryAx.
- [ ] F4. SAT bridge retarget + small exact values
      `SunflowerLean/M3/SmallValues.lean` + encoder extension.
      - [ ] F4a. Support/relabel lemma: any family of m l-sets is
            isomorphic (intersection-pattern-preserving) to one on
            `Fin (m*l)`; upper bounds over `Fin ((v+1)*l)` therefore
            certify M3/I3 upper bounds. Kernel-gated.
      - [ ] F4b. Extend the existing Lean→CNF generator with uniformity
            (exactly-l per set) and pairwise-cap (≤ t common) clauses;
            document the encoding in the file header.
      - [ ] F4c. LRAT-certify I3(4,2) = 12: UNSAT at 13 over the F4a
            ground set + Lean-verified witness at 12 (port the engine's
            I12 witness). Certificates committed; recheck command recorded.
      - [ ] F4d. decide/LRAT the t=1 table rows l ≤ 4 (values 6, 8, 10 for
            M3; 3, 4, 5 for I3) as redundancy against F2f.
      - [ ] F4e. Cross-validation anchors: f(2,3) = 6 and f(3,3) = 20 in
            the M3-encoder (vacuous cap t = l−1), matching the existing
            M(n,3) machinery's values.
- [ ] F5. Conditional pencil lemma `SunflowerLean/M3/Pencil.lean`.
      - [ ] F5a. `structure OrthogovalPair` (point/line types, two
            incidences, two-points-one-line-per-plane, no shared lines,
            cross-intersections ≤ 2, order q) + the pencil family
            definition.
      - [ ] F5b. Theorem: an OrthogovalPair of order q yields an
            I3Admissible(2(q+1), 2) family of card q²+q+1 (sizes,
            exact-2 pairwise, key uniqueness, no equal-core triple).
      - [ ] F5c. Corollary via F1: M3Admissible family of card 2(q²+q+1)
            — the paper's lower-bound mechanism, modulo the cited CIJSSS
            Theorem 2.2 (existence), exactly as in the paper.
      - [ ] F5d. Non-vacuity instance: an explicit OrthogovalPair at the
            smallest feasible order (q = 2 or 3), decide/native_decide
            certified.
- [ ] F6. Bertrand bound `SunflowerLean/M3/Bertrand.lean`:
      unconditional `(l-2)²/8`-type lower statement for all l ≥ 4 from
      F5b/F5c + mathlib's Bertrand postulate, stated conditionally on the
      orthogoval-pair existence hypothesis class (with F5d showing
      non-vacuity; the all-prime-powers input remains cited).
- [ ] F7. Glue, index, and verification harness.
      - [ ] F7a. `SunflowerLean/M3.lean` umbrella import; root
            `SunflowerLean.lean` updated; full `lake build` green.
      - [ ] F7b. `FORMAL_RESULTS_M3.md`: a mapping table — paper statement
            ↔ Lean name ↔ file ↔ axiom audit output — for every formalized
            result. Every row mechanically re-derived (run the audits while
            writing the table, paste actual output).
      - [ ] F7c. `verify_m3.sh`: one script that runs lake build, the
            axiom audits, and the LRAT rechecks; exits nonzero on any
            failure. Run it; commit it; record its output.
      - [ ] F7d. README.md gains an "M3 development" section (results,
            how to verify, link to plan + mapping table + paper).
            AI_DISCLOSURE.md extended to cover this development.

## Phase R — Repository publication readiness

- [ ] R1. LICENSE file: agent prepares Apache-2.0 (code) text and notes
      the option (MIT alternative); 🔑 OWNER chooses and the file is
      committed with that choice recorded here.
- [ ] R2. Reproduction documentation: exact toolchain pin, clean-clone
      build instructions, verify_m3.sh usage, LRAT independent-recheck
      instructions (solver-free, verifier-only path). Tested by actually
      following them in a scratch clone (`git clone . /tmp/...`).
- [ ] R3. 🔑 OWNER: commit the M3 development (suggested message prepared
      by agent), push to GitHub.
- [ ] R4. 🔑 OWNER: tag a citable release (suggested: `paper-v1`);
      optionally enable the Zenodo–GitHub integration so the release
      mints a software DOI automatically.
- [ ] R5. Post-push verification (agent): clean clone FROM GITHUB builds
      green and verify_m3.sh passes (this also validates R2 for the
      public).

## Phase P — Paper integration (bld_note, in erdos-problems pack)

- [ ] P1. Rewrite the paper's "Data and verification" section: Lean 4
      formalization paragraph (what is formalized, the axiom audit
      statement, the repo URL + release tag, LRAT methodology), keeping
      the deterministic-checker description for the engine results that
      remain checker-level. Add one sentence to the introduction noting
      the formalization. Recompile clean.
- [ ] P2. Insert the paper↔Lean mapping reference (cite
      FORMAL_RESULTS_M3.md in the repo) and per-theorem formalization
      footnotes for the formalized results only (no overclaiming for
      M5's conditional form — state "formalized modulo the cited
      existence theorem" verbatim).
- [ ] P3. Bibliography: add the repository as a citable artifact entry
      (and the Zenodo software DOI once R4 mints it). Mechanically verify
      bibliography ordering after every insertion.
- [ ] P4. Full reconciliation pass: every number in the paper's tables
      against the Lean/LRAT values; every claim labeled with its
      verification level (kernel / LRAT / checker / cited). Record the
      reconciliation in this file when done.
- [ ] P5. 🔑 OWNER: affiliation/contact + final AI-disclosure wording +
      complete read-through sign-off.

## Phase A — Archival and announcement (owner-gated, agent-prepared)

- [ ] A1. Zenodo deposit bundle prepared by agent: paper PDF, the
      erdos-problems checker artifacts (.mjs + JSON certificates), pointer
      to the GitHub release; metadata text (title, authors, description,
      keywords, license) ready to paste. 🔑 OWNER publishes; DOI recorded
      HERE and pasted into the paper (P-section placeholder), recompile.
- [ ] A2. arXiv package prepared by agent: self-contained .tex verified to
      compile on a clean TeX tree, abstract text, category math.CO,
      license selection notes. 🔑 OWNER submits (endorsement flow if
      needed); arXiv ID recorded HERE; Zenodo and GitHub cross-linked to
      it.
- [ ] A3. Forum comments finalized by agent with live links (drafts exist
      in the session record: one for problem 20 — primary, the strong
      sunflower problem; one companion for problem 857 noting the
      formalization in this repo). 🔑 OWNER posts both.
- [ ] A4. The erdos-problems pack updated (agent): bld_note README marked
      published, links recorded; memory updated.

## Phase X — Final audit (the loop's exit gate)

- [ ] X1. Fresh-clone full verification: clone the public repo into a
      scratch directory, `lake build` everything, run verify_m3.sh, run
      every LRAT recheck — all green, output pasted here.
- [ ] X2. Link integrity: paper PDF (arXiv version) links resolve to the
      repo/release/DOI; repo README links back to arXiv/Zenodo; forum
      comments' links resolve. Each checked mechanically (curl status).
- [ ] X3. Closing ledger appended to this file: dates, final axiom
      audits, certificate inventory, and the statement that every box
      above is checked. THE LOOP ENDS HERE.

## Loop protocol

1. Open this file; find the first unchecked item top-to-bottom, skipping
   🔑 items whose prerequisites are met (prepare them instead, then move
   on — owner items never block agent items that don't depend on them).
2. Complete the item to its acceptance criterion. Verify mechanically.
3. Flip the checkbox with a one-line dated note (and paste key evidence:
   axiom audit lines, build output, file names).
4. If an attempt fails twice in materially the same way, record the
   blocker under the item, move to the next item, and surface it in the
   session report.
5. At session end: report items completed, blockers, and the queued 🔑
   owner actions.

## Provenance

Plan drafted 2026-06-10 by Claude (Fable) with Cody Mitchell. Models
propose; the kernel, the certificates, and the owner dispose.
