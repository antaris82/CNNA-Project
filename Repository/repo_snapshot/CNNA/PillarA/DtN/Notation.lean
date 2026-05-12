import CNNA.PillarA.DtN.DtNStabilized

set_option autoImplicit false

namespace CNNA.PillarA.DtN

universe u

abbrev BinaryDtN
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.DtN.DtNStrong (Cell := Cell) T

abbrev BinaryInteriorEliminationMode :=
  CNNA.PillarA.DtN.InteriorEliminationMode

abbrev BinaryInteriorSolve
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    {T : CNNA.PillarA.ToC.TruncatedFamily Cell}
    (K : CNNA.PillarA.DtN.DtNStrong Cell T) :=
  K.interiorSolve

abbrev BinaryBoundaryOperator
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    {T : CNNA.PillarA.ToC.TruncatedFamily Cell}
    (K : CNNA.PillarA.DtN.DtNStrong Cell T) :=
  K.boundaryOperator

abbrev StabilizedBinaryDtN
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.DtN.DtNStabilizedStrong (Cell := Cell) T

abbrev StabilizationPolicy
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    {T : CNNA.PillarA.ToC.TruncatedFamily Cell}
    (K : CNNA.PillarA.DtN.DtNStabilizedStrong Cell T) :=
  K.regularizationPolicy

abbrev RegularizationComparisonOperator
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    {T : CNNA.PillarA.ToC.TruncatedFamily Cell}
    (K : CNNA.PillarA.DtN.DtNStabilizedStrong Cell T) :=
  K.comparisonOperator

abbrev RegularizationShiftQ
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    {T : CNNA.PillarA.ToC.TruncatedFamily Cell}
    (K : CNNA.PillarA.DtN.DtNStabilizedStrong Cell T) :=
  K.regularizationShiftQ

abbrev RawBoundaryOperator
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    {T : CNNA.PillarA.ToC.TruncatedFamily Cell}
    (K : CNNA.PillarA.DtN.DtNStabilizedStrong Cell T) :=
  K.rawBoundaryOperator

abbrev SymmetrizedBoundaryOperator
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    {T : CNNA.PillarA.ToC.TruncatedFamily Cell}
    (K : CNNA.PillarA.DtN.DtNStabilizedStrong Cell T) :=
  K.symmetrizedBoundaryOperator

abbrev StabilizedBoundaryOperator
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    {T : CNNA.PillarA.ToC.TruncatedFamily Cell}
    (K : CNNA.PillarA.DtN.DtNStabilizedStrong Cell T) :=
  K.stabilizedOperator

abbrev StabilizedSymmetricBoundaryOperator
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    {T : CNNA.PillarA.ToC.TruncatedFamily Cell}
    (K : CNNA.PillarA.DtN.DtNStabilizedStrong Cell T) :=
  K.stabilizedSymmetricOperator

end CNNA.PillarA.DtN
