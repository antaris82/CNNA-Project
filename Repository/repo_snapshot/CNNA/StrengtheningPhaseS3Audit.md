# CNNA Strengthening Phase S3 audit

Stand of this audit: prepared for the S3 implementation pass on top of the uploaded green S2 tree and aligned with the plan dated 12 April 2026.

This file is prose only. It is not imported by Lean.

## 1. S3 closure target

S3 is the IDEAL-side closure of the concrete reference run.
It must not yet reopen the downstream finite path; that comes only in S4.
The exact S3 obligation is narrower and sharper:

- the concrete reference case of the IDEAL-ToC must exist as a genuine family,
- it must be rebound lawfully to `ToC/Contract`, `ToC/Addressing` and `ToC/IdealAddressEquiv`,
- and deterministic structure may appear only as a flank condition of the concrete witness, not as a hidden strengthening of the generic contract.

## 2. What this implementation adds

This pass introduces `CNNA/PillarA/ToC/ConcreteIdeal.lean`.
Its role is deliberately S3-local:

- it defines the concrete IDEAL reference family from the already closed Foundation reference substrate,
- it introduces an explicit address type `ReferenceAddr b L` distinct from the cell carrier,
- it supplies a concrete `AddressPresentation` instance for that reference family,
- it closes the corresponding `IdealAddressEquiv` instance,
- and it exposes both the cell-side ideal family and the addressed ideal family as explicit S3 objects.

## 3. Why the separate address type matters

The implementation does not use a mere type alias for addresses.
That would keep the cell and address carriers definitionally identical and would invite overlapping `SubstrateClass` instance search exactly at the contract/address boundary.
The S3 pass instead uses a dedicated wrapper type for addresses, with explicit encode/decode transport.

So the reference case is now not only informally but also type-theoretically split into:

- the cell-side ideal contract carrier,
- the addressed presentation carrier,
- and the proof-carrying equivalence between them.

## 4. What remains outside S3

This pass does **not** yet claim the S4 closure.
In particular it does not yet claim that:

- the level-variable family already enters the same real `ToCStrong`/finite consumer path,
- reference and variation runs already share the same first concrete box path,
- the downstream finite modules already typecheck both families through one common entry.

Those are the next obligations.

## 5. Expected integration after this pass

The S3 additions are expected to be visible on the active ToC and Pillar-A surfaces:

- `ToC/BuildAll` imports `ConcreteIdeal` before `Concrete`,
- `ToC/Notation` mirrors the reference ideal cell/address/family surface,
- `PillarA/Notation` mirrors the same aliases at the public Pillar-A layer.

## 6. Regression conditions after this pass

Treat the following as regressions if they appear:

- reidentifying address and cell carriers by alias instead of proof-carrying transport,
- pulling deterministic assumptions into the generic `DirectedFamily` or generic contract root,
- reopening a smoke-test-only reference path that does not pass through `Contract`/`Addressing`/`IdealAddressEquiv`,
- using the new reference family to bypass the still-open S4 unification with the variation family.
