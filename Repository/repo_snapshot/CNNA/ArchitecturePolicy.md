# CNNA architecture policy — Strengthening step 2 after green P27

This file records the repository-wide constraints for the active Strengthening path.
It is policy text only and is not imported by Lean.

## 1. Active doctrine

- No total repo restart. The active work continues inside the current repo.
- Refactor step 1 is closed with green P27 as architecture, cutover, and detachment work.
- Strengthening step 2 is the active program: the cleaned Pillar-A path is sharpened into a real generator path.
- The active production logic lives under `CNNA/PillarA/...`.
- `legacy_sources/CNNA_v0.100_unstable` and `legacy_sources/REALOQS_v0.0605_stable` are regression oracles and migration search space only.
- Archived paths are not to be treated as semantically equal active alternatives.

## 2. Active build topology

- The active root build stays minimal: `CNNA/BuildAll -> CNNA/Notation -> CNNA/PillarA/BuildAll`.
- `CNNA/PillarB` through `CNNA/PillarE` remain active-tree stubs until their own strengthening phases begin.
- No second shadow topology is introduced for smoke tests, audits, or temporary experiments.
- New active modules are introduced only when their phase actually begins.

## 3. Derived-only and import discipline

- Every active module must carry its own strong artifact locally.
- Every active module may consume only already closed strong predecessors on the intended path.
- No import cycle may be introduced.
- No active Pillar-A module may fall back to archived CNNA or REALOQS files as ontic authority.
- Export and handoff modules are downstream couplings of already closed A-data, not new homes of primary mathematical construction.

## 4. ToC and generator doctrine

- The ToC root is modeled first as an ideal infinite substrate.
- Real finite objects are derived approximants of that ideal substrate and not its replacement.
- `REAL∞ -> IDEAL∞` is read as a directed reconstruction path, not as a raw type equality.
- The abstract ideal contract and the addressed presentation are not to be collapsed by fiat.
- Reference family and later substrate variations must consume the same downstream production path.
- Productive Pillar-A runs vary over the generator input vector `(Substrate, WeightPolicy, Cutoff)`.

## 5. Operator and closure discipline

- Free operator witnesses are not acceptable as a permanent public architecture state.
- Current public generator bottlenecks such as `DirichletWeight`, `InteriorInverse`, `epsilon`, and `interfaceInverse` are to be internalized phasewise where the plan says so.
- If a local noncomputable remainder is temporarily unavoidable, it must stay hidden behind a theorematic surface and fit the explicit whitelist classes of the plan.
- A diffuse global `noncomputable` status of the generator is not allowed.

## 6. Algebraic seed doctrine

- Finite algebraic seeds that arise directly from A-generated carriers and matrices belong in Pillar A.
- Hermitian, Hilbert, matrix-`*`-algebra, commutator, spectral, state-space, thermal, and dynamical finite seeds are not to be rebuilt later in Pillars B/C as hidden prerequisites.
- These seeds must remain fachlich getrennt from AQFT-, OQS-, geometry-, and matter-specific later semantics.
- The algebraic Foundation root is governed by a dual-strand doctrine: a future executable production strand over `ExecComplex` and a future analytic mirror strand over `ℂ`.
- Public consumers on the active generator path may not silently use the analytic mirror as their operative surface.
- Public `noncomputable` residue in the algebraic A-root is a policy violation unless it belongs to the explicit whitelist classes of the Strengthening plan.

## 7. Audit discipline

- Green local build remains a gate, but grep-auditable discipline is part of the architecture itself.
- The active tree must stay auditable for imports, `sorry`/`admit`/free axioms, `noncomputable`, `classical`, and broad `@[simp]` surfaces.
- In-code comments and docstrings are not normative architecture; the active Lean tree should stay prose-light.
- Repo-level explanatory prose belongs in dedicated markdown files rather than in active Lean modules.
