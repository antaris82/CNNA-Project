# v31 Schur-Duality Order Lock Report

## What changed

The horizontal/vertical Schur-complement observation was accepted as a mandatory future investigation target, but not as a generative premise.

New planning gate:

- `1.1.1.1.0.8` - Horizontal/vertical Schur-complement duality dependency-order lock

New future phases:

- `10.4.1` - Multiscale Schur-duality bridge: horizontal sector elimination versus vertical level recursion
- `10.4.2` - Arithmetic-CD compatibility as Schur-duality corollary

New or revised objects:

- `LEG27` - Horizontal/vertical Schur-duality dependency-order lock
- `BR08` - Horizontal/vertical Schur-duality bridge
- `BR09` - Subsystem-induced invariant bifurcation profile
- `CD8` - moved to the later corollary position after BR08

## Derivation-order correction

The final Arithmetic-CD compatibility theorem is no longer scheduled as a Phase-6 result. Phase `6.5` now only records source sites and preconditions. The final theorem belongs to `10.4.2`, after the transfermatrix route and the multiscale Schur-duality bridge have been prepared.

## New global guardrail

`GNG14` forbids using the Schur-duality idea, subsystem analogy, or string-like interpretation as an input to earlier generator, Schur, arithmetic, or Cayley-Dickson definitions.

## Validation

Generated tables validate:

- 168 phases
- 177 objects
- 168 scratchpad records
- 177 proof-dossier records
- exactly one active cursor: `1.1.1.1.1`

No Lean build was executed or claimed.
