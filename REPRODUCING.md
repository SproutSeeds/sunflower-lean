# Reproducing the M3 verification

Everything below is deterministic; no step needs a SAT solver — the
committed LRAT certificates are re-verified inside the build.

## Toolchain

- Lean: pinned by `lean-toolchain` (`leanprover/lean4:v4.26.0`);
  installing [elan](https://github.com/leanprover/elan) is enough, it
  reads the pin automatically.
- mathlib: pinned in `lakefile.toml` (`v4.26.0`) and resolved by lake.

## Clean-clone verification

```sh
git clone https://github.com/SproutSeeds/sunflower-lean.git
cd sunflower-lean
lake exe cache get     # prebuilt mathlib oleans (otherwise hours)
./verify_m3.sh
```

Expected final line: `VERIFY_M3: ALL GREEN`. The script runs the full
`lake build`, audits the axioms of all 24 M3 results against the
documented profiles (no `sorryAx`; kernel spine free of compiler
axioms), and checks the LRAT certificates are present. The build itself
re-verifies each committed certificate against the Lean-generated CNF
via `native_decide`, so certificate validity is re-established on every
build, with no external tools.

## Independent LRAT recheck (optional, solver-level)

To re-derive the certificates from scratch rather than trust the
committed ones:

```sh
lake env lean --run tools/export_m3_cnf.lean   # writes /tmp/m3_*.cnf
cadical --plain --lrat --no-binary /tmp/m3_7_2_1_7.cnf  /tmp/a.lrat
cadical --plain --lrat --no-binary /tmp/m3_7_3_2_21.cnf /tmp/b.lrat
```

Both must report `s UNSATISFIABLE`. Any LRAT-producing solver works;
any external LRAT checker (e.g. `lrat-check` from drat-trim) can
validate the certificates against the exported DIMACS independently of
Lean.

## What is verified where

See `FORMAL_RESULTS_M3.md` for the complete paper ↔ Lean mapping with
verbatim axiom audits, and `MASTER_PLAN_TO_DONE.md` /
`FORMALIZATION_PLAN_M3.md` for process provenance.
