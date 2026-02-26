# sunflower-lean

A Lean 4 formalization of exact values and structural properties of sunflower-free families.

## What's here

### Certified status (non-uniform model, ∅ included)

| Result | Status | Method |
|--------|--------|--------|
| M(1,3) = 2 | Verified | `native_decide` |
| M(2,3) = 3 | Verified | `native_decide` |
| M(3,3) = 5 | Verified | `native_decide` |
| M(4,3) = 8 | Verified | `native_decide` |
| M(5,3) = 12 | Verified | SAT + LRAT bridge |
| M(6,3) = 19 | Verified | SAT + LRAT bridge |
| M(7,3) = 29 | SAT-certified | UNSAT at 30; Lean statement has one `sorry` due LRAT size |

`M(n,3)` is the maximum size of a 3-sunflower-free family on `[n]` in this repository's non-uniform convention.

### Active work (open problems)

- **Erdős Problem #20** (`ErdosProblem20.lean`) — uniform sunflower route, `f(r,3) ≤ C^r`.
  Framework and finite-`r` components are formalized; global bound remains open.

## Building

Requires [Lean 4](https://leanprover.github.io/) and [Lake](https://github.com/leanprover/lake).

```bash
lake exe cache get   # download Mathlib cache (fast)
lake build           # build everything (~4 min first time)
```

## Key files

| File | Contents |
|------|----------|
| `Basic.lean` | Core definitions: `IsSunflower`, `IsSunflowerFree`, `IsSFreeC` |
| `SmallCases.lean` | Exact values for `n=1..4`, plus witness lower bounds including `n=5..7` |
| `SATBridge.lean` | Sorry-free LRAT bridge theorems for n=5 (253KB) and n=6 (26MB) |
| `SATUpperBound.lean` | Exact values `M(5,3)=12`, `M(6,3)=19`; SAT-certified `M(7,3)=29` status |
| `BalanceCore.lean` | Foundational balance definitions and Local Turan bridge layer |
| `PairWeight.lean` | Pair-weight counting machinery (public aggregator module) |
| `UnionBounds.lean` | Union-size bound layer and transfer theorems |
| `ErdosProblem20.lean` | Erdős Problem #20 framework and base cases |

## Notes

- Exact values `M(n,3)` for `n ≤ 6` are fully sorry-free in this model.
- `M(7,3)=29` is SAT-certified; Lean-level ingestion of the full LRAT artifact is currently size-limited.
- `ErdosProblem20.lean` and parts of the balance program still contain open `sorry` stubs.

## Author

Cody Mitchell
