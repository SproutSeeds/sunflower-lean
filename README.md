# sunflower-lean

A Lean 4 formalization of exact values and structural properties of sunflower-free families.

## What's here

### Certified exact values (sorry-free)

| Result | Status | Method |
|--------|--------|--------|
| M(1,3) = 1 | Verified | Trivial |
| M(2,3) = 3 | Verified | `native_decide` |
| M(3,3) = 5 | Verified | `native_decide` |
| M(4,3) = 8 | Verified | `native_decide` |
| M(5,3) = 12 | Verified | SAT + LRAT bridge |
| M(6,3) = 19 | Verified | SAT + LRAT bridge |
| M(7,3) = 29 | Certified | 4 independent SAT solvers (UNSAT at 30) |

M(n,3) is the maximum size of a 3-sunflower-free family on [n].

### Active work (open problems)

- **Erdős Problem #20** (`ErdosProblem20.lean`) — uniform sunflower conjecture, f(r,3) ≤ C^r.
  Base cases f(1,3) through f(6,3) proved. General bound open.

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
| `SmallCases.lean` | Verified exact values M(1,3)–M(7,3), lower bounds M(5,3)–M(7,3) |
| `SATBridge.lean` | Sorry-free LRAT bridge theorems for n=5 (253KB) and n=6 (26MB) |
| `SATUpperBound.lean` | M(5,3)=12 and M(6,3)=19 fully verified |
| `Balance.lean` | Two-sided degree window theorem |
| `ErdosProblem20.lean` | Erdős Problem #20 framework and base cases |

## Notes

- All M(n,3) results for n ≤ 6 are fully sorry-free.
- M(7,3) = 29 is SAT-certified (logs and SHA256 hashes available on request).
- `ErdosProblem20.lean` contains open `sorry` stubs for the unsolved general bound.

## Author

Cody Mitchell
