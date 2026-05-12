import CNNA.PillarA.Coupling.MultiSchur

set_option autoImplicit false

namespace CNNA.PillarA.Coupling

universe u

abbrev GeneralizedDtN
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Coupling.GeneralizedDtNStrong (Cell := Cell) T


abbrev MultiSchur
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Coupling.MultiSchurStrong (Cell := Cell) T


end CNNA.PillarA.Coupling
