import CNNA.PillarA.Arithmetic.BoundarySource.LevelHistoryMatrix

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

namespace BoundarySource

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}

structure MultiSchurToLevelHistoryAdapter
    (source : ArithmeticSource Cell T) (L : Nat)
    (carrier : RecursiveLevelHistoryCarrier source L) where
  package : LevelHistoryMatrixPackage source L carrier
  sourceMultiSchur_eq : source.coupling = source.multiSchur
  sourceDtn_eq : source.dtn = source.multiSchur.binary
  sourceGeneralizedDtN_eq : source.generalizedDtN = source.multiSchur.generalized
  adapterOnlyBeforeEqualityLemmas : True

namespace MultiSchurToLevelHistoryAdapter

variable (source : ArithmeticSource Cell T) (L : Nat)
variable (carrier : RecursiveLevelHistoryCarrier source L)

theorem matrix_from_source
    (A : MultiSchurToLevelHistoryAdapter source L carrier) :
    MatrixDerivedFrom source L carrier A.package.matrix :=
  A.package.matrix_from_source

theorem adapter_multiSchurAnchor
    (A : MultiSchurToLevelHistoryAdapter source L carrier) :
    source.coupling = source.multiSchur :=
  A.sourceMultiSchur_eq

theorem adapter_dtnAnchor
    (A : MultiSchurToLevelHistoryAdapter source L carrier) :
    source.dtn = source.multiSchur.binary :=
  A.sourceDtn_eq

end MultiSchurToLevelHistoryAdapter

end BoundarySource

namespace StrengtheningAR2bD

abbrev AR2bDMultiSchurToLevelHistoryAdapterOf
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (source : ArithmeticSource Cell T) (L : Nat)
    (carrier : BoundarySource.RecursiveLevelHistoryCarrier source L) :=
  BoundarySource.MultiSchurToLevelHistoryAdapter (Cell := Cell) (T := T) source L carrier

end StrengtheningAR2bD

end CNNA.PillarA.Arithmetic
