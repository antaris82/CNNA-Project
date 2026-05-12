import CNNA.PillarA.Handoff.CayleyDicksonAdapter

set_option autoImplicit false

namespace CNNA.PillarA.Handoff

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

structure AToCayleyDicksonHandoffStrong
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  source : PillarAStep1Closed Cell T
  cayleyDicksonSource : HandoffCayleyDicksonSource Cell T
  cayleyDicksonSource_eq_source :
    cayleyDicksonSource = cayleyDicksonSourceOfClosed source

abbrev AToCayleyDicksonHandoffStrongOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  AToCayleyDicksonHandoffStrong (Cell := Cell) T

namespace AToCayleyDicksonHandoffStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

@[ext] theorem ext
    (X Y : AToCayleyDicksonHandoffStrong Cell T)
    (hsource : X.source = Y.source)
    (hcd : X.cayleyDicksonSource = Y.cayleyDicksonSource) :
    X = Y := by
  cases X with
  | mk sourceX cayleyDicksonSourceX hsourceX =>
    cases Y with
    | mk sourceY cayleyDicksonSourceY hsourceY =>
      cases hsource
      cases hcd
      have hproof : hsourceX = hsourceY := Subsingleton.elim _ _
      cases hproof
      rfl

def cast (h : T = U) (X : AToCayleyDicksonHandoffStrong Cell T) :
    AToCayleyDicksonHandoffStrong Cell U := by
  cases h
  exact X

theorem cast_rfl (X : AToCayleyDicksonHandoffStrong Cell T) :
    cast (Cell := Cell) rfl X = X := by
  rfl

def ofClosed (X : PillarAStep1Closed Cell T) :
    AToCayleyDicksonHandoffStrong Cell T where
  source := X
  cayleyDicksonSource := cayleyDicksonSourceOfClosed X
  cayleyDicksonSource_eq_source := rfl

theorem ofClosed_source (X : PillarAStep1Closed Cell T) :
    (ofClosed X).source = X := by
  rfl

theorem ofClosed_cayleyDicksonSource (X : PillarAStep1Closed Cell T) :
    (ofClosed X).cayleyDicksonSource = cayleyDicksonSourceOfClosed X := by
  rfl

def closed (X : AToCayleyDicksonHandoffStrong Cell T) :
    PillarAStep1Closed Cell T :=
  X.source

def cdSource (X : AToCayleyDicksonHandoffStrong Cell T) :
    HandoffCayleyDicksonSource Cell T :=
  X.cayleyDicksonSource

theorem cdSource_eq_source
    (X : AToCayleyDicksonHandoffStrong Cell T) :
    X.cdSource = cayleyDicksonSourceOfClosed X.closed := by
  exact X.cayleyDicksonSource_eq_source

theorem source_eq_closed
    (X : AToCayleyDicksonHandoffStrong Cell T) :
    X.source = X.closed := by
  rfl

theorem cayleyDicksonSource_eq_cdSource
    (X : AToCayleyDicksonHandoffStrong Cell T) :
    X.cayleyDicksonSource = X.cdSource := by
  rfl

theorem cdSource_carrier_eq_closed_carrier
    (X : AToCayleyDicksonHandoffStrong Cell T) :
    X.cdSource.carrier = X.closed.carrier := by
  rw [cdSource_eq_source X]
  exact cayleyDicksonSourceOfClosed_carrier X.closed

theorem cdSource_regularization_eq_closed_regularization
    (X : AToCayleyDicksonHandoffStrong Cell T) :
    X.cdSource.regularization = X.closed.regularization := by
  rw [cdSource_eq_source X]
  exact cayleyDicksonSourceOfClosed_regularization X.closed

theorem cdSource_schur_eq_closed_schur
    (X : AToCayleyDicksonHandoffStrong Cell T) :
    X.cdSource.schur = X.closed.schur := by
  rw [cdSource_eq_source X]
  exact cayleyDicksonSourceOfClosed_schur X.closed

abbrev HurwitzStopSeed
    (X : AToCayleyDicksonHandoffStrong Cell T) :=
  HandoffHurwitzStopSeed X.cdSource

abbrev HurwitzStopClosed
    {X : AToCayleyDicksonHandoffStrong Cell T}
    (seed : HurwitzStopSeed X) : Prop :=
  HandoffHurwitzStopClosed seed

abbrev CanonicalIdealAlgebraizationDuty
    {X : AToCayleyDicksonHandoffStrong Cell T}
    (seed : HurwitzStopSeed X) : Prop :=
  HandoffCanonicalIdealAlgebraizationDuty seed

abbrev ThreeProofDutiesClosed
    {X : AToCayleyDicksonHandoffStrong Cell T}
    (seed : HurwitzStopSeed X) : Prop :=
  HandoffThreeProofDutiesClosed seed

theorem hurwitzStopClosed_implies_canonicalIdealAlgebraizationDuty
    {X : AToCayleyDicksonHandoffStrong Cell T}
    {seed : HurwitzStopSeed X}
    (h : HurwitzStopClosed seed) :
    CanonicalIdealAlgebraizationDuty seed :=
  handoffHurwitzStopClosed_implies_canonicalIdealAlgebraizationDuty h

theorem hurwitzStopClosed_implies_threeProofDutiesClosed
    {X : AToCayleyDicksonHandoffStrong Cell T}
    {seed : HurwitzStopSeed X}
    (h : HurwitzStopClosed seed) :
    ThreeProofDutiesClosed seed :=
  handoffHurwitzStopClosed_implies_threeProofDutiesClosed h

end AToCayleyDicksonHandoffStrong

end CNNA.PillarA.Handoff
