# CNNA Strengthening Phase V0 audit

Stand of this audit: prepared against the green post-S0 tree and the Strengthening plan dated 11 April 2026.

This file is V0 prose only. It is not imported by Lean.

## 1. V0 result in one sentence

The public algebraic A-root is now explicitly split conceptually into a future executable production strand and a future analytic mirror strand, and the missing algebraic seed modules required for that split are present in the active Foundation tree.

## 2. Why V0 is opened

The current active tree after green P27 and S0 is architecturally clean, but the algebraic seed layer that later pillars will need is still too implicit:

- `Foundation/MatrixNorms.lean` is already active and consumed downstream, but it is still the only visible algebraic seed module.
- the Foundation tree previously had no dedicated modules for hermitian finite matrix structure, finite state vectors, or matrix-`*`-algebra operations.
- the plan now requires that the public algebraic seed root be read under a dual-strand doctrine: a future executable production strand over `ExecComplex`, and a future analytic mirror strand over `ℂ`.

V0 is therefore not a cosmetic documentation phase. It is the architectural opening move that prevents later Seed/Hilbert/Matrix work from silently collapsing back into a public complex-valued noncomputable surface.

## 3. Explicit V0 doctrine

The active interpretation for the algebraic Foundation root is now:

- `MatrixNorms` remains the first already active seed module and the first downstream consumer that will later have to be sharpened into an explicit dual-strand consumer.
- `HermitianStructure`, `FiniteHilbert`, and `MatrixAlgebra` are introduced as separate Foundation modules so that hermitian predicates, finite state vectors / sesquilinear seeds, and matrix algebra operations live in distinct fachliche modules instead of an undifferentiated blob.
- the executable production strand is not yet implemented in V0; that begins in V1 with `ExecComplex`.
- the analytic mirror strand over `ℂ` is likewise not yet implemented as a direct active Foundation consumer; only its future role is fixed.

## 4. Public noncomputable policy for the algebraic A-root

For the algebraic A-root, any public noncomputable remainder is to be treated as a plan violation unless it belongs to one of the explicitly allowed classes:

- a local hidden solver witness,
- IDEAL-side transport that cannot yet be made constructive,
- a genuine limit-selection issue,
- a later explicitly marked analytic mirror over `ℂ`.

This does not mean every later noncomputable proof is forbidden everywhere in the repo. It means the public operative algebraic seed surface of the active generator path may not quietly become diffuse-noncomputable.

## 5. What V0 adds to the Lean tree

The active Foundation tree now contains dedicated algebraic seed modules:

- `CNNA/PillarA/Foundation/HermitianStructure.lean`
- `CNNA/PillarA/Foundation/FiniteHilbert.lean`
- `CNNA/PillarA/Foundation/MatrixAlgebra.lean`

Their present role is deliberately modest:

- `HermitianStructure` fixes the small algebraic seed scalar class and the hermitian matrix predicate.
- `FiniteHilbert` fixes finite state vectors, a minimal sesquilinear seed, and basis vectors.
- `MatrixAlgebra` fixes algebraic matrix action, adjoint, commutator, and anticommutator seeds.

At V0 these modules are not yet the final executable production strand. They are the explicit algebraic staging area on which V1-V4 can act without reopening the repository topology.

## 6. Notation and visibility policy at V0

The Foundation notation layer now exposes the new algebraic seeds only with coefficient and carrier/index parameters visible.

That is intentional:

- notation must not hide whether a later consumer uses the future executable strand or the future analytic mirror,
- notation must not erase dependent transport obligations,
- notation must remain a review surface and not a semantic disguise.

## 7. Immediate consequence for V1-V2

The next step is now sharply staged:

- V1 introduces the explicit executable coefficient type `ExecComplex`.
- V2 makes the new algebraic seed modules genuinely generic over the small algebraic surface and reworks `MatrixNorms` into the first explicit dual-strand consumer.

V0 is closed only if later work can proceed through these modules instead of smuggling the algebraic root back into a single public `ℂ`-based surface.
