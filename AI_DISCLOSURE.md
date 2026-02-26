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
