# v27 Report: Computable Instance Traversal and Object/Quantities Proof Dossiers

## Summary

v27 addresses two planning weaknesses:

1. The operational computable path must not remain a proof-shaped skeleton. Future operational implementation phases must be exercised by concrete finite instances or explicitly marked as infrastructure-only.
2. Mathlib complications, especially `noncomputable`/`classical` pressure, must be logged at scratchpad level instead of being handled informally during proof repair.

It also changes the proofbook presentation from one dense table to scratchpad-style dossiers and renames the section to **Object and quantities proof documentation**.

## New phase

Inserted before the active module-manifest gate:

- `1.1.1.1.0.1 - Concrete computable instance traversal and mathlib-complication scratchpad contract` — green as planning infrastructure.

The unique active phase remains:

- `1.1.1.1.1 - Implementation module manifest and semantic placement gate`.

No white predecessor stands before the active phase on the active branch.

## New scratchpad fields

Every implementation scratchpad record now has:

- `concrete_instance_traversal`
- `computable_path_not_skeleton_status`
- `expected_executable_witness`
- `mathlib_complication_log`
- `noncomputable_boundary_audit`
- `mathlib_mitigation_or_refactor_layer`

The generator validates these fields and renders them in the scratchpad.

## New workflow policy

Added workflow:

- `Concrete computable instance traversal`

Rule: an operational implementation may start only if it has a concrete finite instance path through the intended computable code or is explicitly infrastructure-only. Mathlib noncomputable leaks must be isolated in the allowed mirror/non-operational layer or backjumped/refactored at the natural source layer.

## New registered objects

- `LEG14 - Concrete computable instance traversal contract`
- `LEG15 - Mathlib complication and noncomputable-boundary log`

Both have proof-dossier records and are planning/workflow infrastructure, not CNNA mathematical inputs.

## Proofbook rendering change

The heading is now:

- `Object and quantities proof documentation`

The proofbook is no longer rendered as one dense table in the PDF. Each object/quantity receives a scratchpad-style dossier with fields for source objects, definitions, proof target, proof sketch, verification/audit, and next documentation action.

## Build status

PDF generation was executed. The generated PDF has 155 pages and was rendered to PNG pages for visual verification.

No Lean build was run or claimed.
