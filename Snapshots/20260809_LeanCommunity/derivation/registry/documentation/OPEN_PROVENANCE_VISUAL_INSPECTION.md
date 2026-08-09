# Open-provenance documentation visual inspection

- Main paper: `derivation/paper/main/paper.pdf` — 35 pages — SHA-256 `288f6ef13bac7cfb6606b8aca77b64a00f596cdc06ee4521ac380c595b9f95fe`.
- Supplement: `derivation/supplement/supplementary.pdf` — 112 pages — SHA-256 `a32baa1f1b7fe4cc17f2740724c54169750b0299ad2f4dd6bc67c7d5f1e95c60`.
- Main pages inspected in the current build: pages 32–33, covering the C016/C017 handoff, the C009 raw-codomain assembly contract, the assembly-vs-recurrent-closure guard, the kernel result, and the T002 handoff.
- Supplement pages inspected in the current build: pages 111–112, covering the C009 mathematical contract, invariants, explicit construction, boundary cases, cross-layer comparison, countercheck, kernel result, trust profile, and downstream handoff.
- Result: no clipped title, formula, callout box, theorem-status text, code-anchor list, or footer was observed on the inspected pages; no overlapping text or broken glyphs were observed.
- The scope guard remains visible: C009 proves unique raw codomain assembly only; universal re-entry into the full C005 state schema remains T002, and any missing supporting closure is assigned back to its semantic origin rather than hidden downstream.
