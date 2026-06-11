# Sunflower Lean - Formal Verification Project

Lean 4 formalization of sunflower combinatorics, using Mathlib and Aristotle verification.

## Purpose

After a failed proof attempt (see [/CORRECTION_NOTICE.md](../CORRECTION_NOTICE.md)), we are now:

1. **Learning the correct approach** — Studying ALWZ (2019) via Rao's survey
2. **Formalizing our understanding** — Machine-verifying definitions and lemmas in Lean 4
3. **Building rigorous foundations** — Before claiming any new results

## Current Status

### Verified (Lean build)

| File | Theorem | Status |
|------|---------|--------|
| `SunflowerLean/Basic.lean` | `entanglement` | Verified |
| `SunflowerLean/Basic.lean` | `reduction_lemma` | Verified |
| `SunflowerLean/Basic.lean` | `disjoint_is_sunflower` | Verified |
| `SunflowerLean/LocalTuran.lean` | `count_triples` | Verified |
| `SunflowerLean/LocalTuran.lean` | `sum_degrees_uniform` | Verified |
| `SunflowerLean/LocalTuran.lean` | `three_sunflower_iff_not_blocked` | Verified |
| `SunflowerLean/LocalTuran.lean` | `local_turan_inequality` | Verified |
| `SunflowerLean/LocalTuran.lean` | `local_turan_growth_constraint` | Verified |

### In Progress

| File | Content | Status |
|------|---------|--------|
| `SunflowerLean/Spread.lean` | Spread family definitions | Draft (not verified) |


## M3 development (uniform, intersection-capped, 2026-06)

Kernel-verified companion to the paper *"Three-sunflower-free set
systems with bounded pairwise intersections"*: the quantities M3(l,t)
and I3(l,t) (largest 3-sunflower-free family of l-sets with pairwise
intersections ≤ t; empty core counts as a sunflower; I3 additionally
intersecting).

Results, all sorry-free (see `FORMAL_RESULTS_M3.md` for the full
paper ↔ Lean mapping with verbatim axiom audits):

- doubling lemma M3 ≥ 2·I3 (`M3/Doubling.lean`)
- the exact t = 1 theorem I3(l,1) = l+1, M3(l,1) = 2l+2 for l ≥ 2,
  with the K_{l+1} star-family witness (`M3/T1Exact.lean`)
- link recursion and M3(l,2) ≤ 4l²+2 (`M3/LinkRecursion.lean`)
- support-relabel soundness: Fin-type upper bounds are universal
  (`M3/Relabel.lean`)
- SAT encoder + soundness bridges for M3/I3 on the bitmask variable
  space, with LRAT-certified encoder anchors at n = 7
  (`M3/SATEncoding.lean`, `M3/SmallValues.lean`)
- the engine's I3(4,2) optimum I12 re-certified by kernel decide:
  I3(4,2) ≥ 12 (`M3/SmallValues.lean`)
- the conditional pencil lemma: orthogoval plane pairs give
  I3-admissible(2q+2, 2) families of q²+q+1 pencils, doubled to the
  paper's M3 lower bound; explicit kernel-decided Fano pair at q = 2
  (`M3/Pencil.lean`)
- the quadratic bound M3(l,2) ≥ (l−2)²/8 for all l ≥ 4 via Bertrand,
  conditional on the orthogoval existence class — CIJSSS
  (arXiv:2210.11961) Theorem 2.2 is cited, not formalized
  (`M3/Bertrand.lean`)

Verify everything with one command:

```bash
./verify_m3.sh
```

(full `lake build`, axiom audits with profile checks, LRAT certificate
rechecks; exits nonzero on any failure).

## Key Definitions

### Sunflower (Basic.lean)

```lean
def IsSunflower {α : Type*} [DecidableEq α] (family : Finset (Finset α)) (k : ℕ) : Prop :=
  family.card = k ∧
  ∃ core : Finset α, ∀ S T : Finset α, S ∈ family → T ∈ family → S ≠ T → S ∩ T = core
```

### r-Spread Family (Spread.lean)

```lean
def IsRSpread {α : Type*} [DecidableEq α] (family : Finset (Finset α)) (r : ℕ) : Prop :=
  r > 0 ∧ family.Nonempty ∧
  ∀ Z : Finset α, (family.filter (fun S => Z ⊆ S)).card * r ^ Z.card ≤ family.card
```

This is the key concept from ALWZ: "no subset is too popular."

## Building

```bash
lake build
```

## Verification with Aristotle

```python
from aristotlelib import AristotleClient

client = AristotleClient(api_key="...")
project = client.create_project_from_lake(
    ".",
    description="Sunflower combinatorics formalization"
)
client.submit_project(project)
```

Notes:
- Aristotle submission is optional; `lake build` already certifies the current proofs locally.
- If you submit, treat it like sharing code with a third-party service; avoid including non-public data.

## References

- **Rao (2020):** "Sunflowers: from Soil to Oil" — Survey paper we're studying
- **ALWZ (2019):** "Improved bounds for the sunflower lemma" — Breakthrough paper
- **Aristotle:** Formal verification system for Lean 4

## Authors

Cody Mitchell & Claude (Opus)

January 2026
