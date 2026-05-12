import CNNA.PillarA.Handoff.CayleyDicksonAdapter

set_option autoImplicit false

namespace CNNA.PillarA.Handoff

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

section DutyII

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}

variable {X : PillarAStep1Closed Cell T}

structure ProofObligationIIPreparation
    (X : PillarAStep1Closed Cell T) where
  approximantsExposeProjectiveSubregimes :
    HandoffCayleyDicksonSource Cell T → Prop

abbrev ProofObligationIIReady
    (prep : ProofObligationIIPreparation (Cell := Cell) (T := T) X) : Prop :=
  HandoffFunctorialApproximantCompatibilityObligation
    prep.approximantsExposeProjectiveSubregimes (cayleyDicksonSourceOfClosed X)

end DutyII

end CNNA.PillarA.Handoff
