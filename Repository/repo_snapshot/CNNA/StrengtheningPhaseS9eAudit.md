# Strengthening Phase S9e Audit

## Scope of this patch

This patch hardens `Finite/UnitaryEvolution.lean` at the exact point named by S9e in the plan.
It does **not** yet close the full proof-carrying dynamics adapter or channel semantics. Instead it
sharpens the public finite dynamics surface itself:

`MatrixExponential -> UnitaryEvolution`

by introducing an explicit computable approximation axis on the operative `ExecComplex` strand and
by separating Schrödinger and Heisenberg conjugation directionally through propagator vs.
inverse-propagator consumption.

## What changed

### `Finite/MatrixExponential.lean`

Two explicit zero-time closure lemmas were added for the already operative approximation surface:

- `expApprox_zero`
- `evolutionApproxAt_zero`

These are the local algebraic base that S9e needs in order to state null-time laws on top of the
S9c executable exponential approximation.

### `Finite/UnitaryEvolution.lean`

The public operative dynamics path is now explicit on the `ExecComplex` strand:

- `EvolutionApproxAxis`
- `propagator`
- `inversePropagator`
- `schrodingerConjugation`
- `heisenbergConjugation`

The crucial change is that Schrödinger and Heisenberg are no longer merely the same formula under
another name. They now consume the directional pair

- `propagator`
- `inversePropagator`

in opposite order:

- Schrödinger: `propagator * ρ * inversePropagator`
- Heisenberg: `inversePropagator * A * propagator`

This is exactly the S9e sharpening requested by the plan.

### Explicit computable time axis

The operative public path no longer opens through a naked real time parameter. Instead it is indexed
by the explicit computable approximation axis

- `EvolutionApproxAxis` with fields `order : Nat` and `time : ℚ`

so the truncation order and rational time parameter stay visible and audit-ready on the public
`ExecComplex` strand.

### Null-time and composition laws

The following explicit laws are now pulled through on the operative surface:

- `propagator_zero`
- `inversePropagator_zero`
- `propagator_neg_eq_inversePropagator`
- `inversePropagator_neg_eq_propagator`
- `schrodingerConjugation_zero`
- `heisenbergConjugation_zero`
- `schrodingerConjugation_comp`
- `heisenbergConjugation_comp`

The composition laws are stated at the level actually justified by the finite approximation surface:
composition of the induced conjugation maps is theorematically reduced to the product of the two
successive propagator / inverse-propagator factors. The patch deliberately does **not** overclaim a
single-step semigroup law for truncated exponentials.

The zero-time proofs on the operative path were also tightened to explicit rewrite-based structural proofs instead of closing through broad `simp` / `simpa` reductions.

### Mirror island remains explicit

The mirror-side complex definitions remain present only as explicitly named analysis / bridge
surface:

- `mirrorSkewGenerator`, `mirrorBackwardSkewGenerator`
- `mirrorPropagator`, `mirrorInversePropagator`
- `mirrorSchrodingerConjugation`, `mirrorHeisenbergConjugation`

They were also directionally corrected so that the mirror Heisenberg action is no longer the same
formula as the mirror Schrödinger action.

### Notation wiring

The new public approximation-axis name is wired into the notation layers via

- `FiniteEvolutionApproxAxis` in `Finite/Notation.lean`
- `FiniteEvolutionApproxAxis` in `PillarA/Notation.lean`

so the new S9e surface is not only locally defined but also globally consumable in the active
notation spine.

## What S9e still does not close

This patch does **not** yet:

- turn the dynamics adapter into a proof-carrying `StarAlgDynamics` seed,
- relate state, density and observable dynamics theorematically beyond the sharpened unitary layer,
- prove adjoint-compatibility results for the operative path,
- or add Kraus / Choi / CPTP channel structure.

Those remain the explicit targets of S9f-S9g.
