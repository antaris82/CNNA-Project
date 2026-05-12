# CNNA v25 - Derivation order repair and object proofbook infrastructure

## What changed

v25 fixes two planning-level defects and adds a third workflow.

1. **Active-front derivation order repaired.** The active branch now has green decomposition-closed umbrella rows before the unique yellow active phase `1.1.1.1.1`. White rows no longer appear as predecessors on the active branch. Green on these umbrella rows means the split/order/cursor is closed; it does not claim descendant Lean implementation closure.

2. **Scratch-pad list serialization repaired.** Affected string-valued list fields, especially in Phase `1.1.3` and neighboring records, no longer render as one item per character. The generator now treats accidental strings in list fields as single list items rather than iterating over characters.

3. **Object/size proof documentation added as a third workflow.** Every registered object/size now has:
   - `Proof documentation status`
   - `Proof dossier`
   - a generated row in `object_proof_dossiers`
   - a PDF/TeX anchor in the new object proof documentation section.

## New phase structure

The former declaration-classification child was shifted to make room for proofbook infrastructure:

- `1.1.1.1.1` - Implementation module manifest and semantic placement gate **active**
- `1.1.1.1.2` - Reuse / duplication audit and canonical generator policy
- `1.1.1.1.3` - Object and size proof-documentation infrastructure gate
- `1.1.1.1.4` - Declaration consumption classification map finalization

The blue-object semantic correction ledger now depends on declaration classification plus proof-dossier infrastructure. Public API exposure excludes any public object that lacks proof-documentation status or remains blue/semantically unfinished.

## New object

`LEG12` was added:

**Object and size proof-documentation infrastructure** - generated proofbook infrastructure linking each registered object/size to source objects, definitions, proof target, proof sketch, and verification/audit status.

This object is planning/documentation governance only; it is not a mathematical generator and is not exported through handoffs.

## Generated artifacts

New generated artifacts include:

- `tables/object_proof_documentation.tex`
- `tables/object_proof_documentation_table.tex`
- `tables/object_proof_link_register.tex`
- `generated_exports/object_proof_documentation.generated.tsv`

## Build status

This package changes planning artifacts and generated views only. No Lean build was run or claimed.
