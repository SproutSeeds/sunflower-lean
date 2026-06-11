# AI Disclosure and Verification Boundary

This repository includes AI-assisted research and engineering.

## Scope of AI assistance

- AI systems were used for ideation, drafting, proof-attempt generation,
  and implementation iteration.
- AI outputs were treated as candidate steps, not as trusted evidence.

## Acceptance boundary

- Mathematical claims are accepted only when they pass local verification.
- Lean statements are accepted only when the Lean kernel checks them.
- SAT-backed claims are accepted only with reproducible local certificate checks.

## Workflow discipline

- Proposed proof steps that failed verification were rejected.
- The working process iterated quickly: propose, verify locally, accept or reject.
- No result is counted as established from model output alone.

## Transparency policy

- Public claims are separated by verification tier in `README.md`.
- Open obligations (for example, remaining `sorry` declarations) are stated
  explicitly.
- This disclosure exists so readers can audit both results and process.

## M3 development (2026-06)

The M3(l,t) development (`SunflowerLean/M3/`, `FORMAL_RESULTS_M3.md`,
`verify_m3.sh`) followed the same discipline, with the AI collaborator
(Claude, Fable) generating all candidate Lean proofs and the kernel
disposing: `lake build` + `#print axioms` (standard three axioms, no
`sorryAx`) gate every commit. SAT results in that development carry
committed, independently re-checkable LRAT certificates; certificate
checks run through `native_decide` (compiler trust), exactly as the
repository's earlier M(n,3) bridge results, and are labeled as such in
`FORMAL_RESULTS_M3.md`. Results conditional on a cited-but-not-
formalized input (CIJSSS Theorem 2.2) say so explicitly in their
docstrings and in the mapping table.
