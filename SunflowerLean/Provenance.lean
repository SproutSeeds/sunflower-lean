namespace SunflowerLean

/-- Public in-repo disclosure: AI systems were used during development. -/
def aiAssistanceDisclosure : List String :=
  [ "AI systems were used for ideation, drafting, and proof-attempt generation.",
    "Model output is treated as candidate reasoning, not trusted evidence.",
    "Claims are accepted only after local verification." ]

/-- Verification boundary used for public claims in this repository. -/
def verificationBoundary : List String :=
  [ "Lean results are accepted only when checked by the Lean kernel.",
    "SAT-backed claims are accepted only with reproducible certificate checks.",
    "No theorem is accepted from model output alone." ]

/-- Process commitment for auditability. -/
def processDiscipline : List String :=
  [ "Failed proof attempts are rejected.",
    "Iteration cycle: propose, verify locally, accept or reject.",
    "Open obligations are disclosed explicitly." ]

theorem aiAssistanceDisclosure_head :
    aiAssistanceDisclosure.head? =
      some "AI systems were used for ideation, drafting, and proof-attempt generation." := by
  rfl

theorem verificationBoundary_head :
    verificationBoundary.head? =
      some "Lean results are accepted only when checked by the Lean kernel." := by
  rfl

theorem processDiscipline_head :
    processDiscipline.head? = some "Failed proof attempts are rejected." := by
  rfl

end SunflowerLean
