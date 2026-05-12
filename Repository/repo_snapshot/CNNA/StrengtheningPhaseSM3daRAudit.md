# Strengthening Phase SM3daR Audit

Status: implementation patch prepared; local Lean build must be run by the editor.

Implemented files:

- `CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorEliminationCandidateEntry.lean`
- `CNNA/PillarA/Arithmetic/BuildAll.lean`
- `CNNA/PillarA/Arithmetic/Notation.lean`
- `CNNA/StrengtheningPhaseSM3daRAudit.md`

SM3daR scope:

- Builds a derived-only `GeneratedInteriorEliminationCandidateEntry` layer from the SM3dR candidate.
- Exposes `candidateEntry_from_treeRecursiveProfile` for regular and variable generated candidates.
- Exposes `candidateMatrix_from_candidateEntry` and proves its entries are exactly the candidate-entry function.
- Carries profile provenance through `candidateEntry_profile_eq_SM3dR_source`.
- Adds a main `SM3daRGeneratedInteriorEliminationCandidateEntryLedger` with regular and variable candidate-entry interfaces.
- Marks the entry as not product-validated until SM3eR. SM3daR therefore does not claim inverse correctness.

Discipline checks by construction:

- No `Matrix.inv` is introduced.
- No free candidate-entry table is introduced; the matrix is definitionally obtained from the candidate-entry function.
- No external inverse oracle is introduced.
- No `TwoSidedInv` proof is introduced.
- No external `InteriorEliminationCertificate` typeclass or assumption is introduced.
- No DtN, GeneralizedDtN, MultiSchur, Charpoly, factorization, discriminant, L2/L3 target, or downstream arithmetic target is produced.
- The only candidate input is the SM3dR candidate, which itself carries SM3cR profile provenance.
- No `noncomputable`, `classical`, `sorry`, `admit`, `axiom`, or broad `@[simp]` marker is introduced by this patch.

Mathlib import check:

- This patch adds no direct `Mathlib.*` import.
- The new file imports only `CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCandidate`.
- Existing internal imports remain unchanged except for adding the new SM3daR module to `BuildAll.lean` and `Notation.lean`.

Required local checks:

```bash
lake build
rg -n "sorry|admit|axiom|Axiom|noncomputable|classical|@\[simp\]|Matrix\.inv|TwoSidedInv|InteriorEliminationCertificate|GeneratedDtN|GeneratedGeneralizedDtN|MultiSchur|Charpoly|Discriminant" \
  CNNA/PillarA/Arithmetic/Smoke/GeneratedInteriorEliminationCandidateEntry.lean \
  CNNA/PillarA/Arithmetic/Notation.lean \
  CNNA/PillarA/Arithmetic/BuildAll.lean
```

Expected grep result: only status/audit names that deliberately state the SM3daR bans should appear; no operative construction of the banned objects should appear.
