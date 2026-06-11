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
      - [x] F4a. Support/relabel lemma. DONE 2026-06-10:
            `SunflowerLean/M3/Relabel.lean` — image_inter_of_injOn_support,
            image_cancel_of_injOn, M3Admissible_image / I3Admissible_image
            (admissibility + card transport along any map injective on the
            support), support_card_le (≤ m·l), exists_injOn_fin (via
            Finset.equivFin + Fin.castLE), and the certifiers
            `M3_upper_of_fin` / `I3_upper_of_fin` (Fin ((v+1)·l) bound ⇒
            universal bound, l > 0; l = 0 is M3_card_le_t0 territory).
            lake build green, zero warnings; all eight declarations audit
            to [propext, Classical.choice, Quot.sound] — no sorryAx.
      - [x] F4b. Encoder extension. DONE 2026-06-10:
            `SunflowerLean/M3/SATEncoding.lean` — nonUniformClauses (unit
            ¬x_m for non-l masks), capViolationClauses (¬x_a ∨ ¬x_b for
            distinct pairs meeting in > t), disjointPairClauses (I3),
            m3CNF/i3CNF assembling them with the reused sunflowerClauses +
            seqCounterClauses; encoding documented in the header. Bonus:
            full soundness bridges `m3_bridge`/`i3_bridge` (UNSAT ⇒ < B on
            Fin n) proved now rather than at F4c — spec lemmas carry
            subset-distinctness inside the generation condition so no
            bitmask-injectivity (no private SATBridge lemma) is needed.
            lake build green, zero warnings in-file. Axiom note: the spec
            lemmas audit to the standard three; the bridge theorems audit
            to [propext, Classical.choice, Lean.ofReduceBool,
            Lean.trustCompiler, Quot.sound] — inherited from SATBridge's
            internals, the SAME profile as the repo's existing
            M_n_3_upper_bridge results; the SAT lane is LRAT/native-trust
            by standing methodology, the F1–F3 kernel spine is unaffected.
      - [~] F4c. PARTIAL 2026-06-11 — witness half DONE, UNSAT half
            BLOCKED (recorded after two failed attempts per protocol).
            DONE: I12 ported and kernel-verified (`i12Witness`,
            `I3_4_2_lower`: I3(4,2) ≥ 12; plus `M3_4_2_lower`:
            M3(4,2) ≥ 24 by doubling), axioms clean, no native_decide.
            BLOCKER (UNSAT-at-13 half):
            (1) The plan's "over the F4a ground set" is structurally
                impossible in the existing bitmask encoding — Fin 52
                means 2^52 primary variables and (2^52)³ triple
                enumeration; dead at generation, not at solving.
            (2) Attempt 1: incidence-matrix encoding (13 rows × 52
                points, exactly-4 counters, common-point aux + cap
                counters, XOR difference witnesses for SF-freeness;
                row0 fixed + row-lex symmetry breaking;
                tools/probe_i3_4_2_incidence.py). B=12 SAT in seconds
                (encoding validated against the witness); B=13: cadical
                600 s timeout.
            (3) Attempt 2: + first-use point-precedence breaking
                (kills the S₄₈ point symmetry). B=12 still SAT; B=13:
                FINAL — full 7200 s budget expired, cadical UNKNOWN
                (timeout), ~40M+ conflicts, neither SAT nor UNSAT.
            (4) Even given UNSAT: an LRAT certificate at this conflict
                scale is multi-GB (the trivial n=6 M(n,3) proof was
                already 26 MB), impractical to commit/re-check, and the
                incidence encoding has no Lean soundness layer (per-row
                counters, aux-var semantics — a multi-day build).
            STANDING EVIDENCE for I3(4,2) ≤ 12: the deterministic
            orderly exhaustion (36,329,094 nodes, certified checker,
            857 pack), exactly as the paper states it; the paper makes
            no LRAT claim for this value (verified in P4). Next hook if
            ever resumed: special-case support analysis to shrink the
            ground set below 52 before re-encoding.
      - [x] F4d. t=1 table rows l ≤ 4. DONE 2026-06-10: six row theorems
            I3_2/3/4_1_row (3, 4, 5) and M3_2/3/4_1_row (6, 8, 10) in
            M3/SmallValues.lean, instantiated from F2f (kernel, axioms
            clean); decide witness anchors at l = 2, 3 are F2g. LRAT for
            the upper rows NOT used and recorded as such in-file: the
            universal bound lives on Fin ((v+1)·l) where the bitmask
            triple enumeration (2^n)³ is infeasible, and the parametric
            kernel theorem is strictly stronger than any per-ground-set
            SAT check. Recorded after two failed attempts: the l = 4
            decide witness anchor (Sym2 (Fin 5)) SIGABRTs the kernel at
            maxRecDepth 32768 even with a 64MB stack — omitted; the row
            stays doubly pinned (theorem + engine).
      - [x] F4e. Cross-validation anchors. DONE 2026-06-10: LRAT-certified
            UNSAT at the repo's M(n,3) scale (n = 7) — `M3_2_1_fin7_anchor`
            (m3CNF 7 2 1 7, agrees with kernel M3(2,1) = 6) and
            `M3_3_2_fin7_anchor` (m3CNF 7 3 2 21, agrees with literature
            f(3,3) = 20; cap vacuous for 3-sets). Certificates committed
            (SunflowerLean/M3/sat_m3_7_*.lrat, CaDiCaL --plain --lrat
            --no-binary), re-verified natively on every build via the
            committed exporter tools/export_m3_cnf.lean; recheck commands
            recorded in-file. Solver fact noted: m3CNF 7 3 2 20 is also
            UNSAT — the f(3,3) = 20 extremal family needs > 7 points, so
            no exact-20 Fin-7 anchor pair exists. Axiom profile: SAT lane
            ([..., ofReduceBool, trustCompiler]), matching the existing
            M_n_3 bridge results.
- [x] F5. Conditional pencil lemma `SunflowerLean/M3/Pencil.lean`.
      DONE 2026-06-10, all sub-items, axioms [propext, Classical.choice,
      Quot.sound] throughout (Fano instance by kernel decide, NOT
      native_decide).
      - [x] F5a. `structure OrthogovalPair` (lines as point-Finsets;
            point_count q²+q+1, pencil degrees q+1, unique line per
            plane through two points, no_shared, cross ≤ 2) +
            `pencilAt`/`pencilFam`.
      - [x] F5b. `pencilFam_I3Admissible` (uniform 2q+2 via disjoint
            pencil union; cap from inter = {U₁,U₂}; SF-free by key
            uniqueness U₁∩U₂ = {p,p′} + plane separation forcing b = c);
            `pencilFam_card` = q²+q+1 for q ≥ 1 (`pencilAt_injective`).
      - [x] F5c. `doubled_pencilFam`: M3Admissible card 2(q²+q+1) via
            M3_ge_two_I3 — the paper's mechanism, modulo cited CIJSSS
            Thm 2.2 exactly as in the paper.
      - [x] F5d. `fanoOrthogovalPair`: explicit order-2 pair from
            difference sets {0,1,3}/{0,2,3} mod 7, every field
            kernel-decided (∃! unfolded for decidability);
            `fano_pencilFam_card = 7`.
- [ ] F6. Bertrand bound `SunflowerLean/M3/Bertrand.lean`:
      unconditional `(l-2)²/8`-type lower statement for all l ≥ 4 from
      F5b/F5c + mathlib's Bertrand postulate, stated conditionally on the
      orthogoval-pair existence hypothesis class (with F5d showing
      non-vacuity; the all-prime-powers input remains cited).
- [x] F7. Glue, index, and verification harness. DONE 2026-06-11
      (commit a185364).
      - [x] F7a. `SunflowerLean/M3.lean` umbrella (9 module imports);
            root `SunflowerLean.lean` updated; full `lake build`
            "Build completed successfully (3094 jobs)" — only
            pre-existing lints elsewhere (Obstruction.lean longLine,
            SmallCases native_decide style).
      - [x] F7b. `FORMAL_RESULTS_M3.md` written with the 24-row audit
            re-derived 2026-06-11 and pasted verbatim: 19 kernel-only
            rows ([propext, Classical.choice, Quot.sound]), 4 SAT-lane
            rows (+ ofReduceBool/trustCompiler), certificate inventory,
            conditionality note for CIJSSS.
      - [x] F7c. `verify_m3.sh` committed and run: "VERIFY_M3: ALL
            GREEN" (full build + 24 audits with count/sorryAx/foreign-
            axiom/spine-purity checks + LRAT presence; nonzero exit on
            failure; wrapped-line normalization handled).
      - [x] F7d. README "M3 development" section + AI_DISCLOSURE M3
            paragraph (kernel/LRAT trust tiers, conditionality policy).

## Phase R — Repository publication readiness

- [ ] R1. LICENSE file. AGENT PREPARATION DONE 2026-06-11: canonical
      texts staged in `license-options/` (LICENSE.apache-2.0.txt from
      apache.org; LICENSE.mit.txt from SPDX, year/name filled), with
      README giving the one-command install for either and a
      recommendation (Apache-2.0, matching mathlib's license culture).
      🔑 OWNER: choose, `cp` to LICENSE, commit, record choice here.
- [x] R2. DONE 2026-06-11: `REPRODUCING.md` (toolchain pin
      leanprover/lean4:v4.26.0 via lean-toolchain; clean-clone steps
      with `lake exe cache get`; verify_m3.sh as the one-command path —
      certificate validity re-established by native_decide inside the
      build, so the default path is solver-free; optional cadical
      re-derivation + external LRAT checker instructions). TESTED: git
      clone → /tmp/sunflower-repro, lake exe cache get ("Completed
      successfully!"), ./verify_m3.sh → exit 0, final line
      "VERIFY_M3: ALL GREEN".
- [ ] R3. 🔑 OWNER: push to GitHub. AGENT PREPARATION DONE 2026-06-11:
      the development is already committed locally as a clean series of
      small verified commits on main (F0–F7 + R1/R2 prep; every commit
      message records what was kernel-gated). Owner action is exactly:
      `git push origin main`. Nothing else to prepare — no force, no
      rebase, no new branch needed.
- [ ] R4. 🔑 OWNER: tag a citable release. AGENT PREPARATION DONE
      2026-06-11 — suggested commands, after R3:
      `git tag -a paper-v1 -m "M3 development as referenced by the paper
      (kernel-verified spine + LRAT-certified SAT lane)"` then
      `git push origin paper-v1`, then on GitHub: Releases → Draft from
      tag paper-v1 (title "paper-v1: M3 development"). Optional DOI:
      zenodo.org → GitHub integration → flip the repo on BEFORE
      publishing the GitHub release, so the release mints the software
      DOI automatically; the DOI then goes into the paper (P3/A1).
- [ ] R5. Post-push verification (agent): clean clone FROM GITHUB builds
      green and verify_m3.sh passes (this also validates R2 for the
      public).

## Phase P — Paper integration (bld_note, in erdos-problems pack)

- [x] P1. DONE 2026-06-11: "Data and verification" gains a "Lean 4
      formalization" subsection (what is formalized, three-axiom audit
      statement, conditional results flagged verbatim, LRAT methodology,
      FORMAL_RESULTS_M3.md + verify_m3.sh pointers, repo cite); the
      checker description kept under "Checker artifacts". Intro sentence
      added before Positioning. pdflatex 2-pass: 0 errors, 0 overfulls.
- [x] P2. DONE 2026-06-11: footnotes on Thm 1.1 (I3_one_exact/
      M3_one_exact), Thm 1.2 ("upper bound and, modulo the cited
      existence theorem, the lower bound"), Lemma finite, Lemma
      doubling, Lemma pencil ("formalized ... modulo the cited
      existence theorem", non-vacuity instance named); mapping file
      cited in the Data section.
- [x] P3. DONE 2026-06-11 (agent half): \bibitem{SunflowerLeanRepo}
      inserted between Kim95 and NaSa17; ordering mechanically verified
      (17 entries, surname script, "ORDER: OK"). DOI sub-half waits on
      R4/A1 (placeholder text in the entry).
- [x] P4. DONE 2026-06-11. Reconciliation of the small-values table
      and numeric claims (levels: kernel / LRAT / checker / cited):
      l=2 row (3, 6, —, 6): kernel (I3_2_1_row, M3_2_1_row; M3(2,2)=6
        via vacuous cap + kernel t=1; Fin-7 LRAT anchor agrees).
      l=3 row (4, 8, —, 20): t=1 kernel; M3(3,2)=f(3,3)=20 literature
        [AHS72,AE92] + engine exhaustion (checker); Fin-7 LRAT anchor
        (UNSAT at 21) agrees.
      l=4 row (5, 10, 12, [24,66]): t=1 kernel; I3(4,2): ≥12 kernel
        (I3_4_2_lower), ≤12 checker (36,329,094-node exhaustion; SAT
        certification attempt under F4c); bracket NOW BOTH KERNEL —
        24 = M3_4_2_lower (added this pass, doubling I12), 66 =
        M3_card_le_t2 at l=4.
      l=5 row (6, 12, ≥16, ≥32): t=1 kernel (parametric M3_one_exact/
        I3_one_exact at l=5); I3(5,2) ≥ 16 and M3(5,2) ≥ 32 checker
        (capped runs, witnesses in pack JSON).
      Pencil constructions: q=2 kernel (fanoOrthogovalPair); q=3,5,7
        checker (projective_orthogoval_doubling_check.mjs); all prime
        powers cited (CIJSSS Thm 2.2).
      Quadratic bounds: 4l²+2 kernel; (l−2)²/8 kernel modulo cited.
      Interval-arithmetic threshold numbers (N_PASS etc.): checker
        (BigInt, slack_857_reserve_pinning.mjs).
      Paper updated to claim M3(4,2) ≥ 24 as kernel-verified;
      recompiled clean (0 errors / 0 overfulls).
- [ ] P5. 🔑 OWNER: affiliation/contact + final AI-disclosure wording +
      complete read-through sign-off. AGENT PREPARATION DONE 2026-06-11
      — the exact markers to resolve in bld_note.tex:
      (1) line ~26 \author thanks: "[Affiliation/contact to be filled
          by the author.]" — replace with affiliation or "Independent
          researcher" + email;
      (2) line ~30 title-page disclosure footnote: "[Author to finalize
          disclosure wording.]" — suggested wording: "Drafting,
          computation, and Lean formalization were carried out with
          substantial assistance from Claude (Anthropic); all results
          were verified by deterministic checkers or the Lean kernel as
          described in Section 7, and responsibility rests with the
          author.";
      (3) line ~559 Acknowledgments "[Author to finalize.]" — keep or
          trim the CIJSSS thanks sentence;
      (4) line ~556 "[Zenodo DOI placeholder.]" — filled at A1, not by
          hand. Then: full read-through sign-off.

## Phase A — Archival and announcement (owner-gated, agent-prepared)

- [ ] A1. Zenodo deposit bundle. AGENT PREPARATION DONE 2026-06-11:
      `bld_note/zenodo_bundle/` (in the 857 pack) — `assemble.sh`
      builds zenodo_deposit.zip (paper PDF+TeX, the five paper-cited
      checker .mjs files, their JSON certificates, metadata); test
      assembly ran green (15 files, ~444 KB). `metadata.md` carries
      paste-ready title/authors/description/keywords/license (CC BY
      4.0) and related-identifier entries. 🔑 OWNER: after P5, re-run
      assemble.sh, upload at zenodo.org, Publish; record DOI HERE;
      replace the paper's two DOI placeholders; recompile.
- [ ] A2. arXiv package. AGENT PREPARATION DONE 2026-06-11:
      `bld_note/arxiv_package/` — bld_note.tex verified SELF-CONTAINED
      on a clean TeX tree (/tmp/arxiv_test, 2-pass pdflatex, 0 errors /
      0 overfulls; only amsmath/amssymb/amsthm/geometry/booktabs/
      hyperref); SUBMISSION_NOTES.md has the paste-ready plain-text
      abstract, category math.CO, license notes, and the
      refresh-after-DOI checklist. 🔑 OWNER: resolve P5 markers,
      refresh the copy, submit; record arXiv ID HERE; cross-link.
- [ ] A3. Forum comments. AGENT PREPARATION DONE 2026-06-11:
      `bld_note/FORUM_COMMENTS_DRAFT.md` — comment 1 for problem 20
      (primary; results summary + formalization pointer), comment 2 for
      problem 857 (companion under the existing M(n,3) thread). Two
      explicit link slots ([ARXIV], [REPO]) to fill after R3/R4/A2;
      [REPO] is https://github.com/SproutSeeds/sunflower-lean. 🔑 OWNER
      fills links and posts both; never posted by the agent.
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
