import CNNA.PillarA.Handoff.CayleyDicksonAdapter

set_option autoImplicit false

namespace CNNA.PillarA.Handoff

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

section DutyIII

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}

variable {X : PillarAStep1Closed Cell T}

structure ProofObligationIIIPreparation
    (X : PillarAStep1Closed Cell T) where
  realToIdealLimitRealizesAlgebraLift :
    HandoffCayleyDicksonSource Cell T → Prop

abbrev ProofObligationIIIReady
    (prep : ProofObligationIIIPreparation (Cell := Cell) (T := T) X) : Prop :=
  HandoffRegimeRecoveryObligation
    prep.realToIdealLimitRealizesAlgebraLift (cayleyDicksonSourceOfClosed X)

end DutyIII

end CNNA.PillarA.Handoff
