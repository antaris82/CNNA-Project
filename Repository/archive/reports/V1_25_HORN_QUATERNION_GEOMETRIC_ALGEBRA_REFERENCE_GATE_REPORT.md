# V1.25 Horn Quaternion / Geometric Algebra Reference-Gate Integration Report

## Scope

This update integrates Martin Erik Horn's uploaded paper `0709.2238v1.pdf`, *Quaternions and Geometric Algebra*, into the CNNA planning tool strictly as external reference and target-gate material. It does not introduce Lean source changes, CNNA generators, phase-release evidence, handoff data, or a new scalar layer.

## Source reading result

The paper is useful for CNNA because it collects and relates several target structures that may later become comparison gates:

- Hamilton quaternion unit relations and anti-commutation patterns.
- Pauli matrix square and anti-commutation patterns.
- The Cartan/Jordan relation between quaternion units and Pauli matrices, with sign-convention ambiguity.
- The semantic warning that complex `i` and quaternion `i` are distinct symbols/functions.
- Geometric algebra grade structure: scalar, vector, bivector and pseudoscalar.
- Pseudoscalar duality: vector/bivector pairing and pure quaternions as oriented planes/bivectors.
- Complex-quaternion / biquaternion eight-component bookkeeping as a multivector target.
- Late comparison directions: Dirac/spacetime algebra and conformal geometric algebra.

## Planning changes

### New phases

- `1.4.9` - Quaternion/geometric-algebra external reference gateway for the Cayley-Dickson structural path.
- `1.4.9.1` - Hamilton unit and Pauli/Cartan sign-convention comparison profile.
- `1.4.9.2` - Bivector/pseudoscalar duality and complex-quaternion multivector comparison profile.
- `13.2.1` - Pauli/Clifford boundary-star-algebra comparison gate.
- `13.6.1` - Dirac/spacetime-algebra comparison target behind CPT, spin-statistics and split gates.
- `18.5` - Geometric and conformal algebra side-comparison register.

### New objects

- `GA0` - Horn quaternion/geometric-algebra reference-gate packet.
- `GA1` - Hamilton unit and Pauli/Cartan sign-convention comparison profile.
- `GA2` - Pauli bivector/pseudoscalar duality comparison profile.
- `GA3` - Complex-quaternion eight-basis multivector comparison profile.
- `GA4` - Boundary Pauli/Clifford comparison gate.
- `GA5` - Dirac/spacetime-algebra comparison target gate.
- `GA6` - Geometric and conformal algebra side-comparison register.

All `GA*` objects are black/reference objects, have no handoff rights, and may be consumed only by comparison/review phases after the corresponding CNNA-derived predecessor data exists.

### Updated governance

- Added `GNG37`: Quaternion/geometric-algebra references are target gates only.
- Added `SLTG-07`: Geometric-algebra comparison map for later CNNA-derived algebraic and spacetime structures.
- Added `SCF56`: closed planning finding for preventing external quaternion/GA material from becoming a CNNA input.
- Added `HORN-GA-01`, `HORN-GA-02`, `HORN-GA-03` to the external-source crosscheck ledger.

## Lean object decision

No Lean source object was created in this update. The correct immediate action is planning/object-register registration only.

Reason: the relevant CNNA predecessor structures are not yet naturally available. In particular:

- CD neutral reintegration is still a future comparison/refactor path.
- CD scalar-surface noncircularity remains open (`CD9`, phase `10.4.3`).
- Pillar-B boundary-star-algebra and local-net/modular data are not derived yet.
- Mathlib API names and theorem availability must be checked against the pinned Lean/mathlib project snapshot before any implementation.

Potential future reference APIs recorded in scratchpads:

- `Mathlib.Algebra.Quaternion`
- `Mathlib.Analysis.Quaternion`
- `Mathlib.LinearAlgebra.CliffordAlgebra.Basic`

## Verification

Commands run from `Repository/`:

```bash
python scripts/generate_tables.py
python scripts/generate_full_document.py --compile
```

Results:

- Generated tables validated successfully.
- Full A3 PDF compiled successfully.
- No Lean source files were changed.
- No Lean build was run because this was a planning/reference-gate update only.

## Known uncertainty

Live mathlib documentation may differ from the project's pinned Lean/mathlib snapshot. Every future Lean implementation phase must re-check exact imports, declarations, theorem names and noncomputable/classical pressure locally against the pinned project configuration.
