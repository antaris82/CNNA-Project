import CNNA.PillarA.Handoff.Outputs.Closed

set_option autoImplicit false

namespace CNNA.PillarA.Handoff

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u v

structure EToAInput
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) (Feedback : Type v) where
  source : PillarAStep1Closed Cell T
  feedback : Feedback

namespace EToAInput

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell} {Feedback : Type v}

@[ext] theorem ext (X Y : EToAInput Cell T Feedback)
    (hsource : X.source = Y.source)
    (hfeedback : X.feedback = Y.feedback) :
    X = Y := by
  cases X
  cases Y
  cases hsource
  cases hfeedback
  rfl

def handoff (X : EToAInput Cell T Feedback) : PillarAStep1Closed Cell T :=
  X.source

end EToAInput

end CNNA.PillarA.Handoff
