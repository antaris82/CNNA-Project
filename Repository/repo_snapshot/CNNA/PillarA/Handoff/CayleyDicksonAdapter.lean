import CNNA.PillarA.Handoff.Outputs.Closed
import CNNA.PillarA.Structural.CayleyDickson.S6ProofDutyGroups
import CNNA.PillarA.Structural.CayleyDickson.S6StatusLayer

set_option autoImplicit false

namespace CNNA.PillarA.Handoff

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}

abbrev HandoffCayleyDicksonSource
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  CNNA.PillarA.Structural.CayleyDickson.CayleyDicksonSource Cell T

def cayleyDicksonSourceOfClosed
    (X : PillarAStep1Closed Cell T) :
    HandoffCayleyDicksonSource Cell T where
  carrier := X.carrier
  regularization := X.regularization
  schur := X.schur
  regularization_split := X.exportData.regularization_split_eq_split
  schur_split := X.exportData.schur_split_eq_split

theorem cayleyDicksonSourceOfClosed_carrier
    (X : PillarAStep1Closed Cell T) :
    (cayleyDicksonSourceOfClosed X).carrier = X.carrier := by
  rfl

theorem cayleyDicksonSourceOfClosed_regularization
    (X : PillarAStep1Closed Cell T) :
    (cayleyDicksonSourceOfClosed X).regularization = X.regularization := by
  rfl

theorem cayleyDicksonSourceOfClosed_schur
    (X : PillarAStep1Closed Cell T) :
    (cayleyDicksonSourceOfClosed X).schur = X.schur := by
  rfl

abbrev HandoffHurwitzStopSeed
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (X : HandoffCayleyDicksonSource Cell T) :=
  CNNA.PillarA.Structural.CayleyDickson.HurwitzStopSeed X

abbrev HandoffHurwitzStopClosed
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {X : HandoffCayleyDicksonSource Cell T}
    (seed : HandoffHurwitzStopSeed X) : Prop :=
  CNNA.PillarA.Structural.CayleyDickson.HurwitzStopClosed seed

abbrev HandoffCanonicalIdealAlgebraizationDuty
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {X : HandoffCayleyDicksonSource Cell T}
    (seed : HandoffHurwitzStopSeed X) : Prop :=
  CNNA.PillarA.Structural.CayleyDickson.CanonicalIdealAlgebraizationDuty seed

abbrev HandoffThreeProofDutiesClosed
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {X : HandoffCayleyDicksonSource Cell T}
    (seed : HandoffHurwitzStopSeed X) : Prop :=
  CNNA.PillarA.Structural.CayleyDickson.ThreeProofDutiesClosed seed

abbrev HandoffFunctorialApproximantCompatibilityObligation
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (approximantsExposeProjectiveSubregimes :
      HandoffCayleyDicksonSource Cell T → Prop)
    (X : HandoffCayleyDicksonSource Cell T) : Prop :=
  CNNA.PillarA.Structural.CayleyDickson.FunctorialApproximantCompatibilityObligation
    approximantsExposeProjectiveSubregimes X

abbrev HandoffRegimeRecoveryObligation
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (realToIdealLimitRealizesAlgebraLift :
      HandoffCayleyDicksonSource Cell T → Prop)
    (X : HandoffCayleyDicksonSource Cell T) : Prop :=
  CNNA.PillarA.Structural.CayleyDickson.RegimeRecoveryObligation
    realToIdealLimitRealizesAlgebraLift X

theorem handoffHurwitzStopClosed_implies_canonicalIdealAlgebraizationDuty
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {X : HandoffCayleyDicksonSource Cell T}
    {seed : HandoffHurwitzStopSeed X}
    (h : HandoffHurwitzStopClosed seed) :
    HandoffCanonicalIdealAlgebraizationDuty seed :=
  CNNA.PillarA.Structural.CayleyDickson.hurwitzStopClosed_implies_canonicalIdealAlgebraizationDuty h

theorem handoffHurwitzStopClosed_implies_threeProofDutiesClosed
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {X : HandoffCayleyDicksonSource Cell T}
    {seed : HandoffHurwitzStopSeed X}
    (h : HandoffHurwitzStopClosed seed) :
    HandoffThreeProofDutiesClosed seed :=
  CNNA.PillarA.Structural.CayleyDickson.hurwitzStopClosed_implies_threeProofDutiesClosed h

end CNNA.PillarA.Handoff
