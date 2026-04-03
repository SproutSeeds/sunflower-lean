# Sunflower Lean - Formal Verification Project

Maintained by SproutSeeds. Research stewardship: Fractal Research Group ([frg.earth](https://frg.earth)).

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
