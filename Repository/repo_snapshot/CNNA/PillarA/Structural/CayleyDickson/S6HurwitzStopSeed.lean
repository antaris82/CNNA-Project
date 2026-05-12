import CNNA.PillarA.Structural.CayleyDickson.S6OctonionicSeed

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

structure HurwitzUpgradeSchema where
  canonicalIdealAlgebraization : DirectedFamily (Cell := Cell) → Prop
  approximantProjectionCompatibility : CayleyDicksonSource Cell T → Prop
  regimeRecovery : CayleyDicksonSource Cell T → Prop
  canonicalTriadicMultiplication : CayleyDicksonSource Cell T → Prop
  dualCompatibleConjugation : CayleyDicksonSource Cell T → Prop
  positiveDefiniteNormSq : CayleyDicksonSource Cell T → Prop
  alternativeLaw : CayleyDicksonSource Cell T → Prop
  divisionFromNormSq : CayleyDicksonSource Cell T → Prop
  externalHurwitzCompatibility : CayleyDicksonSource Cell T → Prop

def hurwitzOpenProofObligations
    (schema : HurwitzUpgradeSchema (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) :
    S6OpenProofObligations X :=
  s6_open_proof_obligations
    schema.canonicalIdealAlgebraization
    schema.approximantProjectionCompatibility
    schema.regimeRecovery
    X

structure HurwitzStopSeed
    (X : CayleyDicksonSource Cell T) where
  octonionic : OctonionicSeed X
  octonionic_eq : octonionic = octonionicSeedOf X
  schema : HurwitzUpgradeSchema (Cell := Cell) (T := T)
  openProofObligations : S6OpenProofObligations X
  openProofObligations_eq :
    openProofObligations = hurwitzOpenProofObligations schema X
  canonicalTriadicMultiplication : Prop
  canonicalTriadicMultiplication_eq :
    canonicalTriadicMultiplication = schema.canonicalTriadicMultiplication X
  dualCompatibleConjugation : Prop
  dualCompatibleConjugation_eq :
    dualCompatibleConjugation = schema.dualCompatibleConjugation X
  positiveDefiniteNormSq : Prop
  positiveDefiniteNormSq_eq :
    positiveDefiniteNormSq = schema.positiveDefiniteNormSq X
  alternativeLaw : Prop
  alternativeLaw_eq :
    alternativeLaw = schema.alternativeLaw X
  divisionFromNormSq : Prop
  divisionFromNormSq_eq :
    divisionFromNormSq = schema.divisionFromNormSq X
  externalHurwitzCompatibility : Prop
  externalHurwitzCompatibility_eq :
    externalHurwitzCompatibility = schema.externalHurwitzCompatibility X

def hurwitzStopSeedOf
    (schema : HurwitzUpgradeSchema (Cell := Cell) (T := T))
    (X : CayleyDicksonSource Cell T) : HurwitzStopSeed X where
  octonionic := octonionicSeedOf X
  octonionic_eq := rfl
  schema := schema
  openProofObligations := hurwitzOpenProofObligations schema X
  openProofObligations_eq := rfl
  canonicalTriadicMultiplication := schema.canonicalTriadicMultiplication X
  canonicalTriadicMultiplication_eq := rfl
  dualCompatibleConjugation := schema.dualCompatibleConjugation X
  dualCompatibleConjugation_eq := rfl
  positiveDefiniteNormSq := schema.positiveDefiniteNormSq X
  positiveDefiniteNormSq_eq := rfl
  alternativeLaw := schema.alternativeLaw X
  alternativeLaw_eq := rfl
  divisionFromNormSq := schema.divisionFromNormSq X
  divisionFromNormSq_eq := rfl
  externalHurwitzCompatibility := schema.externalHurwitzCompatibility X
  externalHurwitzCompatibility_eq := rfl

def HurwitzStopClosed
    {X : CayleyDicksonSource Cell T}
    (seed : HurwitzStopSeed X) : Prop :=
  seed.openProofObligations.canonicalIdealAlgebraization ∧
    seed.openProofObligations.functorialApproximantCompatibility ∧
    seed.openProofObligations.regimeRecovery ∧
    seed.canonicalTriadicMultiplication ∧
    seed.dualCompatibleConjugation ∧
    seed.positiveDefiniteNormSq ∧
    seed.alternativeLaw ∧
    seed.divisionFromNormSq ∧
    seed.externalHurwitzCompatibility

theorem hurwitzStopClosed_iff
    {X : CayleyDicksonSource Cell T}
    (seed : HurwitzStopSeed X) :
    HurwitzStopClosed seed ↔
      seed.openProofObligations.canonicalIdealAlgebraization ∧
        seed.openProofObligations.functorialApproximantCompatibility ∧
        seed.openProofObligations.regimeRecovery ∧
        seed.canonicalTriadicMultiplication ∧
        seed.dualCompatibleConjugation ∧
        seed.positiveDefiniteNormSq ∧
        seed.alternativeLaw ∧
        seed.divisionFromNormSq ∧
        seed.externalHurwitzCompatibility := by
  rfl

theorem hurwitzStopClosed_implies_canonicalIdealAlgebraization
    {X : CayleyDicksonSource Cell T}
    {seed : HurwitzStopSeed X}
    (h : HurwitzStopClosed seed) :
    seed.openProofObligations.canonicalIdealAlgebraization := by
  exact h.1

theorem hurwitzStopClosed_implies_functorialApproximantCompatibility
    {X : CayleyDicksonSource Cell T}
    {seed : HurwitzStopSeed X}
    (h : HurwitzStopClosed seed) :
    seed.openProofObligations.functorialApproximantCompatibility := by
  exact h.2.1

theorem hurwitzStopClosed_implies_regimeRecovery
    {X : CayleyDicksonSource Cell T}
    {seed : HurwitzStopSeed X}
    (h : HurwitzStopClosed seed) :
    seed.openProofObligations.regimeRecovery := by
  exact h.2.2.1

theorem hurwitzStopClosed_implies_canonicalTriadicMultiplication
    {X : CayleyDicksonSource Cell T}
    {seed : HurwitzStopSeed X}
    (h : HurwitzStopClosed seed) :
    seed.canonicalTriadicMultiplication := by
  exact h.2.2.2.1

theorem hurwitzStopClosed_implies_dualCompatibleConjugation
    {X : CayleyDicksonSource Cell T}
    {seed : HurwitzStopSeed X}
    (h : HurwitzStopClosed seed) :
    seed.dualCompatibleConjugation := by
  exact h.2.2.2.2.1

theorem hurwitzStopClosed_implies_positiveDefiniteNormSq
    {X : CayleyDicksonSource Cell T}
    {seed : HurwitzStopSeed X}
    (h : HurwitzStopClosed seed) :
    seed.positiveDefiniteNormSq := by
  exact h.2.2.2.2.2.1

theorem hurwitzStopClosed_implies_alternativeLaw
    {X : CayleyDicksonSource Cell T}
    {seed : HurwitzStopSeed X}
    (h : HurwitzStopClosed seed) :
    seed.alternativeLaw := by
  exact h.2.2.2.2.2.2.1

theorem hurwitzStopClosed_implies_divisionFromNormSq
    {X : CayleyDicksonSource Cell T}
    {seed : HurwitzStopSeed X}
    (h : HurwitzStopClosed seed) :
    seed.divisionFromNormSq := by
  exact h.2.2.2.2.2.2.2.1

theorem hurwitzStopClosed_implies_externalHurwitzCompatibility
    {X : CayleyDicksonSource Cell T}
    {seed : HurwitzStopSeed X}
    (h : HurwitzStopClosed seed) :
    seed.externalHurwitzCompatibility := by
  exact h.2.2.2.2.2.2.2.2

theorem hurwitzStop_status_open
    (X : CayleyDicksonSource Cell T) :
    (statusLedgerOf X).hurwitzStopStatus = SeedStatus.open := by
  rfl

end ClosedChain

end CNNA.PillarA.Structural.CayleyDickson
