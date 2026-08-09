# Proposed Lean-community thread introduction

## From Primitive Provenance to Mathematical Structure - request for architecture/formalization review

I would like to ask for feedback on an experimental Lean/Python formalization project that I have been developing with substantial AI assistance.

The project asks a deliberately constrained question: **given a very small combinatorial provenance structure, what additional mathematical structure can actually be derived without assuming the desired output in the input?**

The working rule is:

> **Do not assume as input what the construction is meant to derive as output.**

The project is intentionally open-ended. Failure to derive a candidate structure, a Lean obstruction, or a finite Python counterexample is treated as a result and can change the dependency DAG.

I am posting the project **before** the later candidate F1/F2 skew-symmetric structure is formally reached. At this stage I am mainly interested in whether the formalization architecture itself is sound and reviewable.

Current snapshot (9 August 2026):

- Lean 4.31.0;
- 145-node / 401-edge derivation DAG;
- verified through T002; T003 is the current frontier;
- 35-module Lean Core with zero dependencies and zero mathlib imports;
- separate proof package using mathlib v4.31.0;
- T002 closes recurrent re-entry and post-step live/state coherence;
- 120 Python tests / 1086 registered subtests as finite regression/counterexample evidence;
- no project-local axioms or `sorry` in the admitted verified proof path.

The Core/proof split is intentional: the primitive/domain construction remains mathlib-free so that imported abstractions cannot easily hide structure that is intended to be derived later; mathlib is allowed in the separate proof layer. I am very interested in whether experienced Lean users consider this useful, excessive, or simply drawn at the wrong boundary.

The project is maintained as four coupled representations:

- Lean for kernel-checked deduction;
- Python for finite exploration, regression and falsification;
- human-readable documentation for semantic intent and interpretation boundaries;
- a machine-readable DAG/registry for dependencies, proof ownership, obstructions and frontier status.

AI use is explicit. I determine the research question, admissibility constraints, resets and interpretation; ChatGPT has been used heavily for structural search, implementation and proof construction; Claude has been used as an additional coherence/review partner. LLM output is not treated as evidence merely because an LLM produced it - Lean kernel checks, executable tests and source/audit evidence remain separate.

The repository is intentionally machine-readable enough that the complete snapshot can also be given to ChatGPT or Claude and explored as a connected artifact. That is an additional navigation interface, not a substitute for ordinary documentation.

The feedback I would most value is:

1. Is the Lean implementation idiomatic and correctly layered?
2. Is the Core / `CNNAProofs` separation sensible?
3. Are any intended outputs already hidden in types, constructors or interface assumptions?
4. Are the closure theorems strong enough, or are some merely restating definitions?
5. Is proof ownership in the DAG sensible?
6. Is the Python/Lean/documentation/DAG separation understandable and useful?
7. What should be simplified before I continue to the next mathematical layer?

There is also an older `Snapshots/20260717` exploratory snapshot that goes much further, but it predates the present proof discipline. The new snapshot deliberately went back and rebuilt the derivation node by node. I therefore regard the current snapshot as the formal claim boundary and the older one only as research-history/context.

The main paper and supplement included in the snapshot remain explicitly marked **DRAFT**.

I would be grateful especially for critical feedback on the implementation and on places where the formal architecture may be giving me a false sense of independence or generality.
