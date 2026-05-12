import CNNA.PillarA.Structural.CayleyDickson.S6HurwitzStopSeed

set_option autoImplicit false

namespace CNNA.PillarA.Structural.CayleyDickson

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.Finite
open CNNA.PillarA.DtN
open CNNA.PillarA.Sectors
open CNNA.PillarA.Closure
open CNNA.PillarA.Network
open CNNA.PillarA.Coupling

universe u

section ClosedChain

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}

structure CanonicalIdealAlgebraizationDuty
    {X : CayleyDicksonSource Cell T}
    (seed : HurwitzStopSeed X) : Prop where
  canonicalIdealAlgebraization :
    seed.openProofObligations.canonicalIdealAlgebraization
  canonicalTriadicMultiplication :
    seed.canonicalTriadicMultiplication
  dualCompatibleConjugation :
    seed.dualCompatibleConjugation
  positiveDefiniteNormSq :
    seed.positiveDefiniteNormSq
  alternativeLaw :
    seed.alternativeLaw
  divisionFromNormSq :
    seed.divisionFromNormSq
  externalHurwitzCompatibility :
    seed.externalHurwitzCompatibility

def FunctorialApproximantCompatibilityDuty
    {X : CayleyDicksonSource Cell T}
    (seed : HurwitzStopSeed X) : Prop :=
  seed.openProofObligations.functorialApproximantCompatibility

def RegimeRecoveryDuty
    {X : CayleyDicksonSource Cell T}
    (seed : HurwitzStopSeed X) : Prop :=
  seed.openProofObligations.regimeRecovery

def ThreeProofDutiesClosed
    {X : CayleyDicksonSource Cell T}
    (seed : HurwitzStopSeed X) : Prop :=
  CanonicalIdealAlgebraizationDuty seed ∧
    FunctorialApproximantCompatibilityDuty seed ∧
    RegimeRecoveryDuty seed

theorem hurwitzStopClosed_implies_canonicalIdealAlgebraizationDuty
    {X : CayleyDicksonSource Cell T}
    {seed : HurwitzStopSeed X}
    (h : HurwitzStopClosed seed) :
    CanonicalIdealAlgebraizationDuty seed := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hurwitzStopClosed_implies_canonicalIdealAlgebraization h
  · exact hurwitzStopClosed_implies_canonicalTriadicMultiplication h
  · exact hurwitzStopClosed_implies_dualCompatibleConjugation h
  · exact hurwitzStopClosed_implies_positiveDefiniteNormSq h
  · exact hurwitzStopClosed_implies_alternativeLaw h
  · exact hurwitzStopClosed_implies_divisionFromNormSq h
  · exact hurwitzStopClosed_implies_externalHurwitzCompatibility h

theorem hurwitzStopClosed_implies_threeProofDutiesClosed
    {X : CayleyDicksonSource Cell T}
    {seed : HurwitzStopSeed X}
    (h : HurwitzStopClosed seed) :
    ThreeProofDutiesClosed seed := by
  refine ⟨?_, ?_, ?_⟩
  · exact hurwitzStopClosed_implies_canonicalIdealAlgebraizationDuty h
  · exact hurwitzStopClosed_implies_functorialApproximantCompatibility h
  · exact hurwitzStopClosed_implies_regimeRecovery h

theorem canonicalIdealAlgebraizationDuty_implies_canonicalIdealAlgebraization
    {X : CayleyDicksonSource Cell T}
    {seed : HurwitzStopSeed X}
    (h : CanonicalIdealAlgebraizationDuty seed) :
    seed.openProofObligations.canonicalIdealAlgebraization := by
  exact h.canonicalIdealAlgebraization

theorem canonicalIdealAlgebraizationDuty_implies_canonicalTriadicMultiplication
    {X : CayleyDicksonSource Cell T}
    {seed : HurwitzStopSeed X}
    (h : CanonicalIdealAlgebraizationDuty seed) :
    seed.canonicalTriadicMultiplication := by
  exact h.canonicalTriadicMultiplication

theorem canonicalIdealAlgebraizationDuty_implies_dualCompatibleConjugation
    {X : CayleyDicksonSource Cell T}
    {seed : HurwitzStopSeed X}
    (h : CanonicalIdealAlgebraizationDuty seed) :
    seed.dualCompatibleConjugation := by
  exact h.dualCompatibleConjugation

theorem canonicalIdealAlgebraizationDuty_implies_positiveDefiniteNormSq
    {X : CayleyDicksonSource Cell T}
    {seed : HurwitzStopSeed X}
    (h : CanonicalIdealAlgebraizationDuty seed) :
    seed.positiveDefiniteNormSq := by
  exact h.positiveDefiniteNormSq

theorem canonicalIdealAlgebraizationDuty_implies_alternativeLaw
    {X : CayleyDicksonSource Cell T}
    {seed : HurwitzStopSeed X}
    (h : CanonicalIdealAlgebraizationDuty seed) :
    seed.alternativeLaw := by
  exact h.alternativeLaw

theorem canonicalIdealAlgebraizationDuty_implies_divisionFromNormSq
    {X : CayleyDicksonSource Cell T}
    {seed : HurwitzStopSeed X}
    (h : CanonicalIdealAlgebraizationDuty seed) :
    seed.divisionFromNormSq := by
  exact h.divisionFromNormSq

theorem canonicalIdealAlgebraizationDuty_implies_externalHurwitzCompatibility
    {X : CayleyDicksonSource Cell T}
    {seed : HurwitzStopSeed X}
    (h : CanonicalIdealAlgebraizationDuty seed) :
    seed.externalHurwitzCompatibility := by
  exact h.externalHurwitzCompatibility

theorem threeProofDutiesClosed_implies_hurwitzStopClosed
    {X : CayleyDicksonSource Cell T}
    {seed : HurwitzStopSeed X}
    (h : ThreeProofDutiesClosed seed) :
    HurwitzStopClosed seed := by
  rcases h with ⟨hAlg, hApprox, hRecovery⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hAlg.canonicalIdealAlgebraization
  · exact hApprox
  · exact hRecovery
  · exact hAlg.canonicalTriadicMultiplication
  · exact hAlg.dualCompatibleConjugation
  · exact hAlg.positiveDefiniteNormSq
  · exact hAlg.alternativeLaw
  · exact hAlg.divisionFromNormSq
  · exact hAlg.externalHurwitzCompatibility

theorem hurwitzStopClosed_iff_threeProofDutiesClosed
    {X : CayleyDicksonSource Cell T}
    {seed : HurwitzStopSeed X} :
    HurwitzStopClosed seed ↔ ThreeProofDutiesClosed seed := by
  constructor
  · intro h
    exact hurwitzStopClosed_implies_threeProofDutiesClosed h
  · intro h
    exact threeProofDutiesClosed_implies_hurwitzStopClosed h

end ClosedChain

end CNNA.PillarA.Structural.CayleyDickson
