---
title: "From Primitive Provenance to Mathematical Structure"
subtitle: "A short architecture and review note for the Lean community"
author: "Jan Seeck"
date: "9 August 2026"
---

# Purpose of this note

This is a request for architectural and formalization feedback on an experimental Lean/Python research project. It is not a claim of a completed theory of physics, and it is intentionally being presented before the later candidate F1/F2 skew-symmetric structure has been formally reached.

The central question is deliberately modest:

> **Starting from a small combinatorial provenance structure, what additional mathematical structure can actually be derived without placing the intended output into the input?**

The project name, **From Primitive Provenance to Mathematical Structure**, is meant literally. The derivation is open-ended: a failed derivation, obstruction or counterexample is considered a result and can change the dependency DAG.

# 1. Why the project was organized this way

The project grew out of repeated attempts to ask foundational questions without silently importing the structures that were supposed to emerge later. This produced a practical admissibility rule:

> **Do not assume as input what the construction is meant to derive as output.**

For the current path this means, in particular, that later physical or mathematical structures are not granted primitive status merely because they would make a target derivation convenient. The present formal core instead begins with finite provenance/growth data and follows explicit interfaces from node to node.

The purpose is not to guarantee that any particular sophisticated structure will emerge. Quite the opposite: the construction is intended to make failure visible. If a desired structure cannot be obtained under the current assumptions, that constrains the next hypothesis rather than licensing an extra hidden input.

# 2. Current formal frontier

As of 9 August 2026 the review snapshot has:

| Item | Current state |
|---|---|
| Lean toolchain | 4.31.0 |
| DAG | 145 nodes / 401 edges |
| Status | 31 FINISHED / 113 UNFINISHED / 1 ACTIVE |
| Verified through | T002 |
| Active node | T003 |
| Core | 35 Lean modules, 0 dependencies, 0 mathlib imports |
| Proof layer | 25 source modules; mathlib v4.31.0 + local Core |
| T002 | 26 audited declarations, kernel verified |
| Python regression | 120 tests / 1086 registered subtests PASS |

The current verified path now closes one complete recurrent step: an admissible response-capable state can be advanced to its canonical successor while re-establishing the state/live-channel coherence required for the next step. This is important for the project because recurrence is now a proved interface property rather than only an executable finite construction.

The later F1/F2 axes and their candidate skew-symmetric relationship are **not** claimed by this snapshot. They belong to the subsequent research frontier.

\newpage

# 3. Lean architecture

The Lean implementation has two packages with a one-way dependency:

```text
+---------------------------+
| CNNAProofs                |
| - may use mathlib         |
| - larger closure proofs   |
| - proof facades/audits    |
+-------------+-------------+
              |
              v
+---------------------------+
| CNNA Core                 |
| - domain definitions      |
| - constructive derivation |
| - elementary closures     |
| - no mathlib imports      |
+---------------------------+
```

The mathlib-free Core is an auditing choice. It is intended to keep the primitive/domain layer inspectable and to reduce the chance that a structure intended as a later output arrives implicitly through a powerful imported abstraction. The separate proof package is free to use mathlib where doing so is mathematically appropriate.

This boundary is itself one of the things on which feedback is requested. It may be too strict, insufficiently idiomatic, or drawn at the wrong locations.

# 4. Proof ownership and the DAG

The derivation is represented as a directed acyclic graph. A node may represent a primitive input, construction, measurement/cut, theorem, proof obligation, obstruction or later specialization. Edges record semantic dependence.

A key implementation rule is **proof ownership at the point of origin**. If a downstream theorem reveals that a closure fact is actually a property of an upstream construction, that fact is moved back and proved at the upstream node rather than hidden as a local helper in the downstream theorem.

The recent T002 closure is a useful example. Recurrent closure required facts owned by C004/C005/C006/C007/M001/M004. Those facts were proved at those origins; T002 then owns only the cross-interface facts that become meaningful when the interfaces are composed.

The DAG therefore serves as more than a project plan. It is intended as an externalized, revisable record of the current derivation state: assumptions, dependencies, proof ownership, obstructions and frontier.

# 5. Python, Lean, documentation and registry are complementary

The project deliberately separates evidence roles:

**Lean** - kernel-checked deduction. It certifies that a formal conclusion follows from the formal assumptions and imported theorems. It does not certify relevance or physical interpretation.

**Python** - finite construction, exploration, regression and falsification. A finite run can expose counterexamples or stable patterns, but it is not treated as a universal proof.

**Documentation** - semantic intent, interfaces, interpretation limits and reading paths. This is where a formally correct theorem can be checked against what the project claims it means.

**DAG/registry** - persistent provenance and dependency state. It connects code, proof status, documentation and open obligations.

The project therefore tries to avoid both failure modes: treating numerical evidence as proof, and treating a kernel-checked theorem as scientifically relevant merely because it is formally valid.

# 6. AI use and epistemic roles

AI assistance is disclosed rather than hidden.

- **Human:** research question, admissibility constraints, hypothesis selection, interpretation, external criticism, resets and decisions about what is allowed to count as an input.
- **ChatGPT:** broad structural search, cross-domain connections, candidate hypotheses, Lean/Python implementation, proof construction and integration work.
- **Claude:** additional review, semantic-coherence checking and adversarial/conservative pressure on proposed closures.
- **Python:** executable finite exploration and counterexample/regression layer.
- **Lean:** kernel-checked deduction.

LLM-generated text or proof scripts are not evidence merely because an LLM produced them. The evidential distinction is explicit: kernel verification, executable regression, source hashes, documentation and external review are separate layers.

The repository is intentionally machine-readable enough that a full snapshot can be given to an LLM and explored as a coupled artifact: code, DAG, proof status, hashes, documentation and open obligations. This is useful for navigating a large cross-linked project, but the repository is also intended to remain understandable to a human reviewer without an LLM.

# 7. Why ask for review now rather than after F1/F2?

Because architectural criticism is cheapest now.

If the Core/proof boundary is misguided, if a theorem is stated at the wrong level, if an intended output has leaked into an input type, if the local exact-rational infrastructure should be replaced by a standard abstraction, or if the DAG does not represent proof ownership cleanly, those problems should be found before another layer of mathematics is built on top of them.

The later F1/F2 skew-symmetric structure would make a natural second review milestone. The present review is about whether the machinery that is supposed to reach such structures is itself sound, transparent and idiomatic.

# 8. Questions for Lean reviewers

The most useful feedback would be concrete answers to questions such as:

1. Is the Core/proof-package split sensible, or would you draw the boundary differently?
2. Are the main structures and theorem statements idiomatic Lean?
3. Do any definitions make important results true by construction when a stronger independent closure theorem should be stated instead?
4. Are there assumptions hidden in types/interfaces that undermine the stated provenance discipline?
5. Which locally implemented objects should instead use Lean/mathlib abstractions?
6. Are proof obligations located at the correct semantic owner node?
7. Is the distinction between finite Python evidence and universal Lean claims clear enough?
8. Can a reviewer reconstruct the current state from the README, DAG and node documentation without reading the entire supplement?
9. Are the axiom/trust audits presented in a useful way, or are they excessive/noisy?
10. What would make this repository easier for an experienced Lean contributor to review?

# 9. Reproduction

Full Lean boundary/build audit:

```bash
cd derivation/code/lean
./audit/run_package_boundary_audit.sh --build
```

Finite Python regression:

```bash
cd derivation/code/python
python -m pytest
```

The main paper and supplementary material are included as **DRAFT** documents. They are context, not prerequisites for reviewing the Lean architecture.

# 10. Historical context

The repository also contains an older `Snapshots/20260717` exploratory state. It reaches further into candidate mathematical/physical structures, but much of it predates the current proof discipline. The present review snapshot should therefore be treated as the authoritative statement of what is currently claimed to be verified.

The intended relationship is:

```text
exploratory search -> obstruction/reset -> stricter provenance discipline
                   -> nodewise Lean verification -> current frontier
```

That distinction is deliberate: the old snapshot records the search path; the present snapshot records the current formal claim boundary.
