# CNNA proof package

`CNNAProofs` depends on pinned mathlib `v4.31.0` and the sibling `cnna_core`
package. It never reverses the permitted `CNNAProofs -> CNNA` dependency.

The retained `CNNAProofs` library contains the exact-source-bound P001 and
M003/M004 closures:

- P001: 142 kernel-verified, axiom-audited declarations;
- M003/M004: 11 kernel-verified public closure and handoff declarations.

P002 is built as the separate `CNNAProofsP002` library target so that adding
its new source does not mutate the exact source set previously verified for
P001 or M003/M004. Its public contract is the static C018 schedule-order
closure; state-dependent least-open selection remains owned by C004.

```bash
cd ..
./audit/run_package_boundary_audit.sh --build
```
