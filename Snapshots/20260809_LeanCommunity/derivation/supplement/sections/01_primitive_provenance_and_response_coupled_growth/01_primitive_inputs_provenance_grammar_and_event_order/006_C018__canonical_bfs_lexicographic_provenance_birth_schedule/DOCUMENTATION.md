# 006 · C018 — Canonical BFS/lexicographic provenance birth schedule

**Canonical node label:** `006 · C018`  
**Semantic ID:** `C018`  
**Current section path:** `1.1.6`  
**Documentation tier:** `D2`  
**Documentation state:** `COMPLETE_V2`

## Position In Derivation

C018 is canonical node 006. Its sole hard scientific predecessor is `005 · C003`, which supplies the finite branching grammar, the root address, the local slot alphabet and the depth cutoff. C018 is introduced only after those objects exist because an order cannot be defined before its carrier and local rank type are available.

The root itself is not scheduled: it was created by C002 and anchored to the empty word by C003. C018 orders non-root provenance births. The incoming hard edge is `E063: C003 -> C018` with relation `defines_canonical_birth_schedule`. The proof-certification edge `E141: P002 -> C018` is non-hard and records the dedicated static-order closure. Its six public declarations are now kernel-verified with empty axiom profiles; least-open state selection remains owned by C004.

## Formal Statement

Let `b` be the C001 branching parameter and write

\[
S_b=\{0,\ldots,b-1\},\qquad S_b^*=\bigcup_{d\ge 0}S_b^d.
\]

For local ranks `r,s in S_b`, define

\[
r <_S s \iff r<s.
\]

For provenance words \(a,c\in S_b^*\), let \(a<_{\mathrm{lex}}c\) be the lexicographic lift of \(<_S\). C018 defines

\[
a\prec c
\iff
|a|<|c|\ \lor\ \bigl(|a|=|c|\land a<_\mathrm{lex}c\bigr).
\]

The current Lean source proves:

1. `prec` is irreflexive;
2. `prec` is transitive;
3. `prec` is asymmetric;
4. for all addresses `a,c`, exactly one of the mutually exclusive cases `a prec c`, `a=c`, or `c prec a` holds;
5. every parent precedes each child;
6. for one parent, smaller sibling rank implies earlier child;
7. the relation induced on bounded slots through their child addresses is irreflexive, transitive and asymmetric;
8. two slots selecting distinct child addresses are comparable.

The phrase **strict total order** in the C018 contract refers to this address order and, conditionally on distinct selected children, to the induced slot order. It does not by itself assert that a dynamically evolving set of currently open slots has been constructed or that its least element is unique.

## Hypotheses

The address-order theorems require only the C003 address type generated from `b`. The lower bound `b >= 2` is carried by `BranchingParameter`, although the order-theoretic proof itself uses only the finiteness and decidable natural values of the local slot type.

The bounded-slot layer additionally requires:

- a `CanonicalBirthSchedule` carrying a C003 grammar;
- a bounded parent address;
- a local rank;
- a proof that the child depth satisfies `|parent|+1 <= L`.

The theorem `openSlotBefore_total_of_distinct_children` explicitly assumes that the two selected child addresses are unequal. No theorem in C018 assumes a born-set, an event history, a response history, or a physical state.

## Introduction Reason

C003 constructs a rooted ordered word grammar but deliberately does not linearize its nodes. Recurrent growth requires one deterministic choice of which admissible slot is considered next. C018 therefore fixes a schedule convention before C004A selects the first non-root slot and before C004 defines the recurrent next-open-slot interface.

The convention is canonical only **relative to the locked CNNA rule**. Other strict total orders on the same finite grammar exist. The current node proves that the chosen rule is mathematically coherent and unambiguous after selection; it does not derive shortlex order uniquely from the grammar alone.

## Proof Strategy

The formal proof is layered so that each mathematical responsibility is isolated.

1. **Local rank order.** `SlotBefore r s` is defined as strict natural-number comparison of the finite slot values.
2. **Word order.** `AddressLexBefore` uses `List.Lex SlotBefore`.
3. **Schedule order.** `BirthBefore` is the disjoint depth/lexicographic definition above.
4. **Same-parent compatibility.** Induction on the common parent word proves that appending ranks `r<s` preserves lexicographic order.
5. **Word-order laws.** Structural recursion on lists proves lexicographic irreflexivity, transitivity and constructive trichotomy.
6. **Depth/lex lift.** Case analysis over the two defining branches and `Nat.lt_trichotomy` yields address-order transitivity and trichotomy.
7. **Asymmetry and totality.** Asymmetry follows by composing opposite directions and contradicting irreflexivity; totality for distinct addresses follows by eliminating the equality branch of trichotomy.
8. **Bounded slots.** A slot is mapped to its bounded C003 child address, and all order laws are inherited from `BirthBefore`.

This architecture avoids treating the Python loop as the proof. The executable enumeration is evidence for the same specification, while the Lean order laws are proved directly from the typed address grammar.

## Lemma Chain

The load-bearing chain is

```text
SlotBefore
  -> AddressLexBefore
  -> BirthBefore

lex_snoc_same_parent
  -> sameParentIncreasingRank

slotBefore_irrefl
  -> addressLexBefore_irrefl
  -> birthBefore_irrefl

addressLexBefore_trans
  -> birthBefore_trans
  -> birthBefore_asymm

addressLexBefore_trichotomy
  -> birthBefore_trichotomy
  -> birthBefore_total_of_ne

OpenBirthSlot.childAddress
  -> OpenSlotBefore
  -> sameParentOpenSlotIncreasingRank
  -> openSlotBefore_irrefl
  -> openSlotBefore_trans
  -> openSlotBefore_asymm
  -> openSlotBefore_total_of_distinct_children
```

The proof of `addressLexBefore_trans` exhausts the constructors of the two lexicographic witnesses. The proof of `addressLexBefore_trichotomy` compares the heads by `Nat.lt_trichotomy`; equal heads reduce recursively to the tails. `birthBefore_trans` then handles the four combinations depth/depth, depth/lex, lex/depth and lex/lex.

## Formal Realization

### Python

Source: `derivation/code/python/src/cnna/derivation/s01_primitive_response_coupled_finite_provenance/s01_primitive_inputs_grammar_and_event_order/s06_c018__canonical_bfs_lexicographic_provenance_birth_schedule.py`  
SHA-256: `c99afaef142d6f3d4d74b26de21db6c1450ff1af1098f449746da5e5f6c4dae7`

`OpenBirthSlot` stores parent, rank and child explicitly. `open_slot_key` returns `(len(parent), parent, rank)`. `canonical_birth_slots` maintains a FIFO parent list and cursor. Whenever one parent is processed, ranks are emitted in increasing order and each child is appended to the end of the parent queue. Therefore all parents at depth `d` are processed before any parent at depth `d+1`, and parents at one depth occur in lexicographic order.

The key and the enumerator are extensionally consistent: comparing `(len(u),u,r)` and `(len(v),v,s)` is equivalent to comparing child words `u||(r)` and `v||(s)` by depth and lexicographic order. This statement is supported by the definitions and exhaustive finite tests in the current package; it is not yet exported as a cross-language theorem.

### Lean

Source: `derivation/code/lean/core/src/CNNA/Derivation/S01_PrimitiveResponseCoupledFiniteProvenance/S01_PrimitiveInputsGrammarAndEventOrder/S06_C018_CanonicalBfsLexicographicProvenanceBirthSchedule.lean`  
SHA-256: `d332704d80a9aaa1eca72b7961d868aabceeead7320bbbd5766b1d2ba2bb53a1`

Lean represents ranks by `Fin b.value` and words by lists of those ranks. Thus malformed local ranks cannot inhabit the slot type. The address relation is independent of `L`; the cutoff enters only when `OpenBirthSlot` stores a bounded parent and a proof that the selected child remains within the approximant. The derived slot order compares the selected child addresses rather than comparing an unrelated slot identifier.

### Executable tests

Source: `derivation/code/python/tests/derivation/s01_primitive_response_coupled_finite_provenance/s01_primitive_inputs_grammar_and_event_order/test_s06_c018__canonical_bfs_lexicographic_provenance_birth_schedule.py`  
SHA-256: `12fcb32879313f7cd3e4bd9b5b004437767bd1876920aef7bf365fa5ae154653`

The nine node-local tests verify:

- the exact binary depth-three address order;
- the ternary depth-two parent/rank order;
- child extension and strict adjacency direction;
- irreflexivity, pairwise total direction and transitivity on the finite sample;
- the empty non-root schedule at `L=0`;
- determinism and absence of hidden schedule inputs;
- absence of event, time, geometry, conductance, response and batch state;
- rejection of invalid predecessors and operands;
- cardinality \(\sum_{d=1}^L b^d\) and uniqueness of emitted child addresses for the tested ranges.

## Counterexamples Or Necessity Checks

1. **Depth comparison is necessary.** Pure lexicographic order may place a deeper word before a shallower word. For example, `(0,0)` is lexicographically before `(1)` under ordinary list lexicography, whereas the active BFS convention requires `(1)` before every depth-two word.
2. **Sibling rank is necessary.** Omitting the final rank from the executable key makes all siblings of one parent indistinguishable and fails to determine a strict order.
3. **Root exclusion is necessary.** Including the empty word as a scheduled birth would duplicate the already completed C002 genesis and shift every downstream event label.
4. **The cutoff proof is necessary for bounded slots.** Without `|parent|+1 <= L`, the slot structure could select a child outside the finite approximant even though its parent is admitted.
5. **Distinct-child hypothesis is necessary for slot totality.** Two record values that select the same child address are not ordered in either direction because the underlying address relation is irreflexive. C018 therefore proves total comparability only after excluding this equality case.
6. **Order does not imply least-open uniqueness.** A strict total order on the ambient address set does not define which slots are currently open. A born-set predicate and proof that the relevant open set is nonempty are required before a least element can be selected. This state-dependent selection problem is deliberately outside P002 and is owned by C004.
7. **Finite enumeration is not yet a Lean theorem.** Python's loop terminates and the tests match the carrier cardinality, but C018's Lean module defines the order and bounded slot objects, not an executable finite enumeration theorem. Exhaustivity and termination remain P004.

## Axiom Profile

C018 is part of the mathlib-free `cnna_core` package. The current source contains no `axiom`, `sorry`, `admit`, `Classical`, `noncomputable`, `unsafe`, `partial`, `simp`, or `simpa` use. The prefix-free source was included in the successful 26-job core build reported for Lean 4.31.0. The node-local registry classifies the proof audit as PASS.

The source-local theorem chain is constructive. No transitive Mathlib choice profile is involved because this module does not import Mathlib. The separate long-term project goal of eliminating transitive axioms in Mathlib-dependent proof packages is therefore not a limitation of C018.

## Result

C018 establishes a coherent deterministic shortlex schedule convention:

- all shallower addresses are earlier;
- addresses at one depth are lexicographically ordered;
- parents precede children;
- siblings follow increasing local rank;
- the address order is strict and total;
- bounded admissible slots inherit the order through their selected children.

The Python implementation enumerates the bounded non-root addresses in that order for the tested finite grammars, and its state surface contains no downstream physical fields.

## Remaining Limits

C018 does **not** close the following statements:

- construction of the state-dependent set of currently open slots;
- existence and uniqueness of its least element;
- a kernel theorem equating the Python selector with the Lean relation;
- finite-schedule exhaustivity and termination for every `b,L`;
- event-index or birth-time assignment;
- label-equivariance and absence of hard-coded rank bias;
- response, conductance, geometry or dynamics.

These are downstream responsibilities represented by P004, C010, T003 and later nodes. P002 has closed the dedicated static-order certification, so C018 is `IMPLEMENTED_VERIFIED`; this still does not imply finite exhaustivity or any state-dependent least-open theorem.

## Downstream Handoff

- `E064 C018 -> C004A`: selects the first provenance slot.
- `E065 C018 -> C004`: orders the recurrent next-open-slot interface.
- `E066 C018 -> C010`: supplies the order from which event indices will later be assigned; C018 itself assigns none.
- `E073 C018 -> T003`: supplies the label-order contract for the future equivariance theorem.
- `E080 C018 -> C019`: orders the future finite iteration.
- `E089 C018 -> C042`: fixes the active schedule scope for ancestor-return rank closure.
- `E106 C018 -> CTRL005`: defines the active reference against which the layer-batch control is compared.
- `E144 C018 -> P003`: supports birth-cut canonicity.
- `E150 C018 -> P004`: supports finite exhaustivity and termination.
- `E141 P002 -> C018`: kernel-verified certification of the dedicated static-order closure (six axiom-free public declarations).


## Code Line Register

### Python source

| Symbol | Kind | Lines | Scientific role |
|---|---|---:|---|
| `OpenBirthSlot` | `CLASS` | 32-37 | slot record or bounded admissible slot structure |
| `_require_grammar` | `FUNCTION` | 40-43 | exact C003 predecessor type gate |
| `open_slot_key` | `FUNCTION` | 46-53 | executable BFS/lex ordering key |
| `slot_precedes` | `FUNCTION` | 56-58 | strict comparison induced by the key |
| `canonical_birth_slots` | `FUNCTION` | 61-88 | breadth-first finite slot enumerator |
| `canonical_birth_addresses` | `FUNCTION` | 91-93 | projection to selected child addresses |
| `CanonicalBirthSchedule` | `CLASS` | 97-114 | rule object carrying only C003 |
| `build_canonical_birth_schedule` | `FUNCTION` | 117-121 | canonical Python constructor |

### Python tests

| Symbol | Kind | Lines | Scientific role |
|---|---|---:|---|
| `TestCanonicalBfsLexicographicSchedule` | `CLASS` | 22-123 | node-local executable contract and negative controls |

### Lean core

| Symbol | Kind | Lines | Scientific role |
|---|---|---:|---|
| `SlotBefore` | `DEF` | 24-27 | strict local rank relation |
| `AddressLexBefore` | `DEF` | 28-32 | lexicographic word relation |
| `BirthBefore` | `DEF` | 33-39 | depth-then-lex address relation |
| `shallower_before` | `THEOREM` | 40-46 | depth branch introduction |
| `sameDepthLex_before` | `THEOREM` | 47-53 | equal-depth lex branch introduction |
| `lex_snoc_same_parent` | `THEOREM` | 54-64 | lexicographic preservation under common prefix |
| `sameParentIncreasingRank` | `THEOREM` | 65-73 | sibling-order theorem |
| `parent_before_child` | `THEOREM` | 74-81 | breadth-first parent/child theorem |
| `slotBefore_irrefl` | `THEOREM` | 82-86 | rank-order irreflexivity |
| `addressLexBefore_irrefl` | `THEOREM` | 87-100 | word-order irreflexivity |
| `addressLexBefore_trans` | `THEOREM` | 101-141 | word-order transitivity |
| `addressLexBefore_trichotomy` | `THEOREM` | 142-172 | constructive word trichotomy |
| `birthBefore_irrefl` | `THEOREM` | 173-182 | address-order irreflexivity |
| `birthBefore_trans` | `THEOREM` | 183-199 | address-order transitivity |
| `birthBefore_asymm` | `THEOREM` | 200-204 | address-order asymmetry |
| `birthBefore_trichotomy` | `THEOREM` | 205-225 | constructive address trichotomy |
| `birthBefore_total_of_ne` | `THEOREM` | 226-240 | total comparability for distinct addresses |
| `CanonicalBirthSchedule` | `STRUCTURE` | 241-246 | rule object carrying only C003 |
| `build` | `DEF` | 247-250 | Lean constructor carrying only C003 |
| `build_grammar` | `THEOREM` | 251-256 | constructor equation |
| `OpenBirthSlot` | `STRUCTURE` | 257-265 | slot record or bounded admissible slot structure |
| `childAddress` | `DEF` | 266-271 | bounded C003 child constructor |
| `childAddress_address` | `THEOREM` | 272-279 | child word equation |
| `OpenSlotBefore` | `DEF` | 280-286 | slot order induced by child addresses |
| `sameParentOpenSlotIncreasingRank` | `THEOREM` | 287-301 | bounded sibling-order theorem |
| `openSlotBefore_irrefl` | `THEOREM` | 302-306 | slot-order irreflexivity |
| `openSlotBefore_trans` | `THEOREM` | 307-313 | slot-order transitivity |
| `openSlotBefore_asymm` | `THEOREM` | 314-319 | slot-order asymmetry |
| `openSlotBefore_total_of_distinct_children` | `THEOREM` | 320-329 | slot comparability under distinct-child hypothesis |

The canonical machine-readable register is `derivation/registry/documentation/CODE_ANCHORS.tsv`. The stable anchor identity is source path plus symbol plus source SHA-256; line numbers are a human navigation aid and are regenerated after source edits.

<!-- CNNA-OPEN-PROVENANCE-BEGIN C018 -->
## Open-provenance role: Event provenance versus recurrent live dynamics

C018 orders birth events in an acyclic provenance history.  Later live-state feedback may be recurrent or cyclic without turning the event-provenance relation itself into a cycle.

<!-- CNNA-OPEN-PROVENANCE-END C018 -->
