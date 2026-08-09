# Lean package boundary

The Lean tree contains two Lake packages:

- `core/`: `cnna_core` / `CNNA`, Lean 4.31.0, 24 modules, no package dependencies and no mathlib imports;
- `proofs/`: `cnna_proofs`, Lean 4.31.0, pinned mathlib `v4.31.0`, local dependency `../core`, and two library targets: `CNNAProofs` and `CNNAProofsP002`.

The current proof tree contains 17 source modules. Retained exact-source kernel evidence covers all 17: the 15 modules of `CNNAProofs` plus the two-module independent `CNNAProofsP002` target. All six public P002 declarations have empty axiom profiles.

The only permitted import direction is from the proof package to the Core. P002 imports its C018 owner module; the Core never imports a proof library.

Four disjoint exact-hash scopes are checked before a build begins:

1. immutable P001 proof and axiom-audit sources;
2. verified M003/M004 integration and aggregation sources;
3. P002 library configuration, root, proof module, and axiom audit;
4. audit-runner infrastructure.

```bash
python3 audit/check_package_boundary.py
./audit/run_package_boundary_audit.sh --build
```

## Toolchain provenance

<!-- CNNA-EXTREF-BEGIN EXT-USE-TOOLCHAIN-LEAN431 -->
The Lean 4 Development Team, *Lean 4.31.0 Release Notes*, Lean FRO, LLC (2026). DOI status: `NOT_ASSIGNED_SOFTWARE_RELEASE`. Stable source: `https://lean-lang.org/doc/reference/latest/releases/v4.31.0/`; accessed 2026-07-31. Context: Binds consulted official Lean documentation to the exact project toolchain generation. Formal status: `REGISTRY_METADATA_ONLY`
<!-- CNNA-EXTREF-END EXT-USE-TOOLCHAIN-LEAN431 -->
