# AI and research workflow

This project uses several imperfect components deliberately rather than treating any one of them as sufficient.

## Human role

The human role owns the research question and, crucially, the admissibility boundary: which structures may be primitive and which must remain targets of derivation. It also owns interpretation, resets, prioritization and the decision that an apparent positive result is scientifically relevant rather than merely mathematically available.

## LLM role

ChatGPT is used for broad structural search, cross-domain pattern recognition, hypothesis generation, Lean/Python implementation, proof construction and integration. Claude is used as an additional independent/conservative review channel for semantic coherence, missing cases and questionable assumptions.

LLM output is never promoted to proof evidence by provenance alone.

## Python role

Python provides finite executable constructions, regression tests, scaling experiments and counterexample search. It is especially valuable as a negative filter: one counterexample can kill an overgeneralized universal hypothesis. Passing finite tests does not establish universality.

## Lean role

Lean is the deductive certification layer. The kernel checks that the formal theorem follows from its formal assumptions and trusted dependencies. Lean does not decide whether the theorem is the right theorem, whether an assumption is scientifically legitimate, or whether an interpretation is physically meaningful.

## Documentation and DAG role

Documentation records semantic intent and interpretation boundaries. The DAG/registry records the evolving dependency state, proof ownership, obstructions and current frontier. Together they act as persistent research memory and make resets/revisions explicit.

## Compact epistemic summary

```text
Human:       problem formulation, admissibility, interpretation
LLM:         search and candidate construction, not certification
Python:      finite evidence and falsification, not universality
Lean:        certified deduction, not relevance
DAG/docs:    persistent state and semantic provenance
```

The workflow is deliberately cyclic:

```text
human/LLM hypothesis
        -> Python exploration / counterexamples
        -> Lean formalization / obstruction
        -> independent review
        -> DAG + documentation revision
        -> human reassessment
        -> next hypothesis
```

The value of the workflow lies in the mismatch of failure modes. LLMs can hallucinate plausible bridges; Python can overfit finite cases; Lean can certify an irrelevant theorem; human judgment can miss technical constraints. The project tries to make those weaknesses collide rather than align.
