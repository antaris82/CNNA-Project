# Lean package boundary

The Lean tree contains two Lake packages:

- `core/`: `cnna_core` / `CNNA`, Lean 4.31.0, **35 modules**, no package dependencies and **no mathlib imports**;
- `proofs/`: `cnna_proofs`, Lean 4.31.0, pinned mathlib `v4.31.0`, local dependency `../core`, and the proof library targets used by the current verified chain.

The current proof tree contains **25 source modules**. Retained exact-source kernel evidence covers all 25 through the T002 recurrent-state closure. P002 remains independently axiom-free for all six audited public declarations. T002 contributes 26 audited declarations: 19 with the accepted transitive profile `[propext, Classical.choice, Quot.sound]` and 7 with `[propext, Quot.sound]`; there are no project-local axioms and no `sorry` in the accepted T002 path.

The only permitted import direction is from the proof package to the Core:

```text
CNNAProofs  --->  CNNA Core
                 ^
                 |
             no mathlib
```

The current boundary audit checks retained exact-source manifests for P001, M003/M004, P002, C008, C016/C017, C009, T002, and the audit infrastructure itself. It also checks that the Core remains dependency-free and mathlib-free and that the permitted package direction is not reversed.

```bash
python3 audit/check_package_boundary.py
./audit/run_package_boundary_audit.sh --build
```

Current formal frontier for this snapshot: **T002 kernel verified; T003 active**.

## Toolchain provenance

<!-- CNNA-EXTREF-BEGIN EXT-USE-TOOLCHAIN-LEAN431 -->
The Lean 4 Development Team, *Lean 4.31.0 Release Notes*, Lean FRO, LLC (2026). DOI status: `NOT_ASSIGNED_SOFTWARE_RELEASE`. Stable source: `https://lean-lang.org/doc/reference/latest/releases/v4.31.0/`; accessed 2026-07-31. Context: Binds consulted official Lean documentation to the exact project toolchain generation. Formal status: `REGISTRY_METADATA_ONLY`
<!-- CNNA-EXTREF-END EXT-USE-TOOLCHAIN-LEAN431 -->
