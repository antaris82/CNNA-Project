import Mathlib.Data.Matrix.Basic
import CNNA.PillarA.Foundation.ExecComplex
import CNNA.PillarA.Arithmetic.BoundarySource.RecursiveLevelHistoryCarrier

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u v

namespace BoundarySource

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}

abbrev LevelHistoryMatrix (L : Nat) :=
  Matrix (LevelHistoryIndex L) (LevelHistoryIndex L) ExecComplex

structure MatrixDerivedFrom
    (source : ArithmeticSource Cell T) (L : Nat)
    (carrier : RecursiveLevelHistoryCarrier source L)
    (matrix : LevelHistoryMatrix L) where
  witnessCarrier : RecursiveLevelHistoryCarrier source L
  witnessCarrier_eq : witnessCarrier = carrier
  dtnAnchor : source.dtn = source.multiSchur.binary
  generalizedDtNAnchor : source.generalizedDtN = source.multiSchur.generalized
  multiSchurAnchor : source.coupling = source.multiSchur
  noCutSpecCarrierClaim : ∀ _k : LevelHistoryIndex L,
    source.toc.approximant source.concretePolicy = T

structure LevelHistoryMatrixPackage
    (source : ArithmeticSource Cell T) (L : Nat)
    (carrier : RecursiveLevelHistoryCarrier source L) where
  matrix : LevelHistoryMatrix L
  matrix_from_source : MatrixDerivedFrom source L carrier matrix

namespace MatrixDerivedFrom

variable (source : ArithmeticSource Cell T) (L : Nat)
variable (carrier : RecursiveLevelHistoryCarrier source L)
variable (matrix : LevelHistoryMatrix L)

theorem witnessCarrier_eq_carrier
    (D : MatrixDerivedFrom source L carrier matrix) :
    D.witnessCarrier = carrier :=
  D.witnessCarrier_eq

theorem dtnAnchor_eq
    (D : MatrixDerivedFrom source L carrier matrix) :
    source.dtn = source.multiSchur.binary :=
  D.dtnAnchor

theorem generalizedDtNAnchor_eq
    (D : MatrixDerivedFrom source L carrier matrix) :
    source.generalizedDtN = source.multiSchur.generalized :=
  D.generalizedDtNAnchor

theorem multiSchurAnchor_eq
    (D : MatrixDerivedFrom source L carrier matrix) :
    source.coupling = source.multiSchur :=
  D.multiSchurAnchor

theorem noCutSpecCarrierClaim_at
    (D : MatrixDerivedFrom source L carrier matrix)
    (k : LevelHistoryIndex L) :
    source.toc.approximant source.concretePolicy = T :=
  D.noCutSpecCarrierClaim k

end MatrixDerivedFrom

namespace LevelHistoryMatrixPackage

variable {source : ArithmeticSource Cell T} {L : Nat}
variable {carrier : RecursiveLevelHistoryCarrier source L}

theorem matrix_from_source_anchor
    (P : LevelHistoryMatrixPackage source L carrier) :
    MatrixDerivedFrom source L carrier P.matrix :=
  P.matrix_from_source

theorem noCutSpecCarrierClaim_at
    (P : LevelHistoryMatrixPackage source L carrier)
    (k : LevelHistoryIndex L) :
    source.toc.approximant source.concretePolicy = T :=
  P.matrix_from_source.noCutSpecCarrierClaim k

end LevelHistoryMatrixPackage

def transportLevelHistoryMatrix
    {ι : Type v} {L : Nat}
    (e : ι ≃ LevelHistoryIndex L)
    (A : LevelHistoryMatrix L) : Matrix ι ι ExecComplex :=
  fun i j => A (e i) (e j)

theorem transportLevelHistoryMatrix_apply
    {ι : Type v} {L : Nat}
    (e : ι ≃ LevelHistoryIndex L)
    (A : LevelHistoryMatrix L) (i j : ι) :
    transportLevelHistoryMatrix e A i j = A (e i) (e j) := by
  rfl

end BoundarySource

namespace StrengtheningAR2bD

abbrev AR2bDLevelHistoryMatrixOf (L : Nat) :=
  BoundarySource.LevelHistoryMatrix L

abbrev AR2bDMatrixDerivedFromOf
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (source : ArithmeticSource Cell T) (L : Nat)
    (carrier : BoundarySource.RecursiveLevelHistoryCarrier source L)
    (matrix : BoundarySource.LevelHistoryMatrix L) :=
  BoundarySource.MatrixDerivedFrom (Cell := Cell) (T := T) source L carrier matrix

abbrev AR2bDLevelHistoryMatrixPackageOf
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (source : ArithmeticSource Cell T) (L : Nat)
    (carrier : BoundarySource.RecursiveLevelHistoryCarrier source L) :=
  BoundarySource.LevelHistoryMatrixPackage (Cell := Cell) (T := T) source L carrier

end StrengtheningAR2bD

end CNNA.PillarA.Arithmetic
