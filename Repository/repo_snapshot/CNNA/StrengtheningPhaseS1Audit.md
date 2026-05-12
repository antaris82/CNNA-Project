# CNNA Strengthening Phase S1 audit

Stand of this audit: updated for the S1 implementation pass on top of the uploaded green V5 tree.

This file is prose only. It is not imported by Lean.

## 1. S1 closure target

After green V5, the remaining mathematically new S1 obligation is **not** more algebra work.
It is the Foundation-side closure of a computable concrete reference substrate that can serve as the
first robust reference run of the later generator while leaving the generic `SubstrateClass` root intact.

So the intended S1 reading is now:

- the algebraic side from V0-V5 stays frozen and active,
- the concrete reference family is supplied as a new Foundation module,
- later phases must consume that family through the existing generic interfaces instead of smuggling in a second start object.

## 2. What this implementation adds

The S1 pass introduces `CNNA/PillarA/Foundation/ConcreteSubstrate.lean`.
Its active role is deliberately narrow:

- it defines a computable concrete reference carrier `RegularCell b L := Fin L → Fin (b + 1)`,
- it equips that carrier with an explicit `SubstrateClass` instance,
- it also provides a matching `DeterministicSubstrateClass` instance,
- it keeps the branching factor uniformly computable as `b + 1`,
- and it exposes a canonical `zeroThread` as an explicit infinite thread on the reference family.

The point is not yet to close the full IDEAL-side family from S3. The point is to make the Foundation root carry a real executable reference family already in S1.

## 3. Why this is architecturally legal

This module is legal under the plan because it does **not** replace the generic root.
The active root remains the typeclass-parametric `SubstrateClass` doctrine.
`ConcreteSubstrate` is only the first concrete witness family that instantiates that doctrine.

This preserves the intended split:

- **generic root**: `SubstrateClass`, `Interfaces`, determinism/key transport,
- **first concrete witness**: regular computable reference family,
- **future variation**: level-variable substrate and explicit policy axes in S2.

## 4. What must stay true after this S1 pass

The following points are part of the intended S1 gate and should be treated as regressions if broken:

- no `sorry` in the concrete reference family,
- no avoidable public `noncomputable` in the concrete reference family,
- no reopening of the algebraic Foundation root toward public analytic assumptions,
- no concrete helper path that bypasses `SubstrateClass` and becomes a second semantic root,
- no hidden migration of later ToC/finite logic back down into Foundation/ConcreteSubstrate.

## 5. Surface integration expected from this pass

The concrete reference family is expected to be visible in the active Foundation surface:

- `Foundation/BuildAll` imports the new module,
- `Foundation/Notation` mirrors the reference-family names at the public notation layer,
- downstream phases may now instantiate the generic Foundation/ToC path with a real computable substrate family instead of leaving S1 prose-only open.

## 6. What this pass still does not claim

This S1 implementation pass does **not** yet claim that the later ideal/addressed reference family work from S3 is closed.
In particular it does not yet claim:

- the fully closed concrete IDEAL-ToC family from `ToC/Contract` + `Addressing` + `IdealAddressEquiv`,
- the second legal substrate family from S2,
- the policy axes from S2,
- the downstream proof that reference and variation runs share the same real ToC/finite box path from S4 onward.

Those remain separate obligations.

## 7. Immediate consequence for the next phases

With this S1 pass, the next legitimate work is no longer to reopen V0-V5 or to add ad-hoc Foundation shortcuts.
The next mathematically coherent steps are:

- S2: second family plus policy axes and universality analysis,
- S3: ideal-side closure of the concrete reference family,
- S4: proof-carrying joint entry of reference and variation runs into the same finite consumer path.
