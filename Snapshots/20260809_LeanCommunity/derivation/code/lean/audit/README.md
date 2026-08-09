# Lean package-boundary and source-integrity audit

The audit checks the one-way package boundary, policy constraints, exact source
integrity, retained P001 kernel evidence, current M003/M004 sources, registered
axiom profiles, and required build artifacts.

The source hashes are deliberately partitioned into three disjoint scopes:

- `P001_CURRENT_SOURCE_SHA256.txt`: the twelve immutable P001 proof modules and
  the P001 axiom-audit module;
- `M003M004_CURRENT_SOURCE_SHA256.txt`: the two Core interfaces, two closure
  modules, proof aggregator, and M003/M004 axiom-audit module;
- `AUDIT_INFRASTRUCTURE_CURRENT_SOURCE_SHA256.txt`: the package-boundary checker
  and its build runner.

The audit rejects any overlap between these scopes. In particular,
`CNNAProofs.lean` belongs to the current M003/M004 integration scope rather than
to the retained immutable P001 evidence set.

Static current-source audit:

```bash
python3 check_package_boundary.py
```

Local kernel rebuild and complete audit:

```bash
./run_package_boundary_audit.sh --build
```

The Core package has no dependencies and may not import mathlib or
`CNNAProofs`. The proof package may import pinned mathlib and the Core. Retained
P001 kernel evidence is accepted only when the transcript hash and every one of
the twelve registered P001 proof-source SHA-256 values match the current
package.
