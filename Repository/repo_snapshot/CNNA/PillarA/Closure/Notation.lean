import CNNA.PillarA.Closure.RegularizationClosure

set_option autoImplicit false

namespace CNNA.PillarA.Closure

universe u

abbrev ParameterClosure
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Closure.ParameterClosureStrong (Cell := Cell) T

abbrev ClosureRegularizationPolicy
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    {T : CNNA.PillarA.ToC.TruncatedFamily Cell}
    (P : CNNA.PillarA.Closure.ParameterClosureStrong Cell T) :=
  P.regularizationPolicy

abbrev ClosureComparisonOperator
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    {T : CNNA.PillarA.ToC.TruncatedFamily Cell}
    (P : CNNA.PillarA.Closure.ParameterClosureStrong Cell T) :=
  P.comparisonOperator

abbrev ClosureRegularizationShiftQ
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    {T : CNNA.PillarA.ToC.TruncatedFamily Cell}
    (P : CNNA.PillarA.Closure.ParameterClosureStrong Cell T) :=
  P.regularizationShiftQ

abbrev RegularizationClosure
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Closure.RegularizationClosureStrong (Cell := Cell) T

end CNNA.PillarA.Closure
