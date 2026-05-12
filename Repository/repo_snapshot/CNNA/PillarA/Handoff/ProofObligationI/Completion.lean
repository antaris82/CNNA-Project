import CNNA.PillarA.Handoff.CayleyDicksonAdapter

set_option autoImplicit false

namespace CNNA.PillarA.Handoff

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

section DutyI

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}

abbrev ProofObligationISeed
    (X : PillarAStep1Closed Cell T) :=
  HandoffHurwitzStopSeed (cayleyDicksonSourceOfClosed X)

abbrev ProofObligationIClosed
    (X : PillarAStep1Closed Cell T)
    (seed : ProofObligationISeed (Cell := Cell) (T := T) X) : Prop :=
  HandoffCanonicalIdealAlgebraizationDuty seed

abbrev ProofObligationIThreeDutyClosure
    (X : PillarAStep1Closed Cell T)
    (seed : ProofObligationISeed (Cell := Cell) (T := T) X) : Prop :=
  HandoffThreeProofDutiesClosed seed

theorem proofObligationIClosed_of_hurwitzStopClosed
    {X : PillarAStep1Closed Cell T}
    {seed : ProofObligationISeed (Cell := Cell) (T := T) X}
    (h : HandoffHurwitzStopClosed seed) :
    ProofObligationIClosed (Cell := Cell) (T := T) X seed :=
  handoffHurwitzStopClosed_implies_canonicalIdealAlgebraizationDuty h

theorem proofObligationIThreeDutyClosure_of_hurwitzStopClosed
    {X : PillarAStep1Closed Cell T}
    {seed : ProofObligationISeed (Cell := Cell) (T := T) X}
    (h : HandoffHurwitzStopClosed seed) :
    ProofObligationIThreeDutyClosure (Cell := Cell) (T := T) X seed :=
  handoffHurwitzStopClosed_implies_threeProofDutiesClosed h

end DutyI

end CNNA.PillarA.Handoff
