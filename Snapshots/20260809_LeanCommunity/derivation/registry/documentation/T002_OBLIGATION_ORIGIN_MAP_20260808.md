# T002 obligation-origin map — 2026-08-08

T002 proves only the closure that first exists at the merge of C005 state data,
C009 raw codomain assembly and the M004 update.  Supporting statements are
proved at their semantic origin and consumed by T002.

| T002 target / auxiliary fact | Semantic owner | Closure status in D14R19 source |
|---|---|---|
| inherited grammar and schedule | C009 / T002 assembly | local T002 projection |
| `bornNonRoot = X.bornNonRoot ++ [next]` | C009 | already kernel-verified |
| new child inside cutoff | C004 | already kernel-verified |
| new child non-root | C004 | already kernel-verified |
| born-prefix nonempty | C005 schema + append | local T002 structural consequence |
| born-prefix cutoff closure | C004 | `C004_SuccessorBornPrefixClosure` |
| born-prefix non-root closure | C004 | `C004_SuccessorBornPrefixClosure` |
| born-prefix canonical-order Pairwise closure | C004 | `C004_SuccessorBornPrefixClosure` |
| born-prefix initial-segment closure | C004 | `C004_SuccessorBornPrefixClosure` |
| exact M004 value realized as rational C005 value | C006 | `C006_ExactFractionRatRealizationClosure` |
| positivity of rational realization from `PositiveSteering` | C006 | `C006_ExactFractionRatRealizationClosure` |
| canonical rational realization of C007 raw C005 blocks | C007 | `C007_StateDirectedBlockRealizationClosure` |
| M001 causal/sibling port support is born and structurally separated | M001 | `M001_PortSupportClosure` |
| M004 new update endpoints lie in old carrier or new child | M004 | `M004_LiveUpdateSupportClosure` |
| every M004 update touches the new child | M004 | `M004_LiveUpdateSupportClosure` |
| M004 update endpoints are distinct | M004 | `M004_LiveUpdateSupportClosure` |
| M004 ordered update pairs are unique | M004 | `M004_LiveUpdateSupportClosure` |
| old/new conductance pair disjointness | T002 merge boundary | local T002 lemma from C004 freshness + C005 old support + M004 touches-child |
| appended conductance Pairwise uniqueness | C005 generic list schema | `C005_ConductanceAppendClosure` |
| inherited old parent backbone | C005 | inherited |
| new child parent↔child backbone | M004 support + C004 parent identity | consumed locally by T002 |
| post-step C005↔C017 live coherence | T002 merge boundary | local T002 theorem using C009 pre-coherence + C006 realization |
| unique successor state | T002 | local extensional assembly theorem |

Scope guard: T002 does not define the next C004 slot, assume an external C007 block realization, compute response/steering,
or invent record/live laws.  It closes only the C005 successor schema after those
inputs are already canonically fixed.
