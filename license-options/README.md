# License options (R1, owner decision pending)

The repo has no LICENSE yet. Two prepared options — pick one, copy it
to the repo root as `LICENSE`, commit, and record the choice in
MASTER_PLAN_TO_DONE.md under R1:

- `LICENSE.apache-2.0.txt` — Apache-2.0 (recommended for code:
  explicit patent grant, the common choice for Lean/mathlib-adjacent
  projects; mathlib itself is Apache-2.0, so this matches the
  dependency's culture). If chosen, optionally append a NOTICE line:
  "Copyright 2026 Cody Mitchell".
- `LICENSE.mit.txt` — MIT (shorter, maximally permissive, no patent
  language), already filled in with year/name.

Either is fine for Zenodo/arXiv; the paper itself is licensed
separately at submission time (arXiv license selection, A2).

```sh
# Apache-2.0:
cp license-options/LICENSE.apache-2.0.txt LICENSE
# or MIT:
cp license-options/LICENSE.mit.txt LICENSE
git add LICENSE && git commit -m "Add LICENSE"
```
