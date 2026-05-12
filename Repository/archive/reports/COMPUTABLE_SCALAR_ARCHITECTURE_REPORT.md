# v35 computable scalar architecture report

## Question
Should CNNA accept the limits of `ExecComplex`, introduce a stronger exact scalar layer, or derive a complex layer through Cayley-Dickson?

## Code findings

- `CNNA/PillarA/Foundation/ExecComplex.lean` defines `ExecComplex` as two rational coordinates `re : Q` and `im : Q`. It is therefore exact and executable, but only a rational-pair complex surface.
- `CNNA/PillarA/Foundation/ExecComplexBridge.lean` maps `ExecComplex` into mathlib `Complex` through `ExecComplexBridge.toComplex`; this is a bridge/mirror direction, not an operational replacement.
- `CNNA/PillarA/Arithmetic/CayleyDickson/ArithmeticCDBridge.lean` keeps CD and Exec/mirror scalar structures separate and contains an explicit no-identification status: no Exec-mirror/CD-complex identification without a transfer lemma.
- Several `CNNA/PillarA/Finite/*` mirror modules use `noncomputable def` on analytic/mirror paths. That supports the current policy: mirror layers are allowed to be noncomputable, operational layers are not.

## Web/mathlib findings

- mathlib `Complex` is a structure with `re : Real` and `im : Real`, so it is formally rich but not an exact executable algebraic-number layer by itself.
- mathlib `NumberField` defines number fields as finite-dimensional fields over Q and `RingOfIntegers` as integral closure; this is useful for proof/mirror layers, but not automatically a concrete executable scalar API.
- mathlib `QuadraticAlgebra R a b` is a two-coordinate quadratic algebra over a ring, with `re` and `im`, and is closer to CNNA's exact imaginary-quadratic arithmetic needs.
- The public discussion around Lean algebraic closures/computable algebraic numbers warns that general algebraic closure field structures are not generally a computable representation.

## Decision added to plan

v35 adds `LEG31` / phase `1.1.1.1.0.12`:

- keep `ExecComplex` as rational operational floor;
- do not widen it into full `Complex`;
- evaluate a separate exact quadratic operational candidate `O09`;
- keep analytic `Complex`/`Real` mirror-only;
- defer any CD-derived C-layer to late `CD9` / phase `10.4.3` after noncircularity proof.

## New future phases

- `1.2.1.1` ExecComplex capability and limitation audit
- `1.2.1.2` Exact quadratic scalar layer pilot decision
- `4.0.3` Scalar-layer computation test rows: ExecComplex vs exact quadratic extension boundary
- `10.4.3` Cayley-Dickson scalar-surface noncircularity and possible C-layer bridge

## New objects

- `LEG31` Computable scalar architecture contract
- `O09` Exact quadratic operational scalar candidate
- `BR13` ExecComplex to exact-quadratic projection bridge
- `CD9` Cayley-Dickson C-layer noncircularity audit

## Validation

- 182 phases
- 193 objects
- 182 scratchpad records
- 193 proof-dossiers
- exactly one active cursor: `1.1.1.1.1`
- no white phase before the active cursor
- PDF compiled twice with `pdflatex`: 218 pages
- selected render pages checked: 1, 4, 120, 210
- no Lean build executed or claimed
