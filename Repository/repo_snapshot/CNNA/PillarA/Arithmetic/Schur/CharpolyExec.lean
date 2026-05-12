import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import CNNA.PillarA.Arithmetic.Schur.Recurrence

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u v

namespace Schur

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}
variable {source : ArithmeticSource Cell T} {L : Nat}

abbrev SpectralParameter := ℚ

inductive OperativeCharpolyComputationStatus where
  | determinantAndPencilEvaluationClosed
  deriving DecidableEq, Repr

inductive SmallDimensionDeterminantStatus where
  | explicitFinOneTwoThreeFormulasCertified
  deriving DecidableEq, Repr

inductive GeneralDimensionDeterminantStatus where
  | certifiedFiniteMatrixDeterminant
  deriving DecidableEq, Repr

inductive CharpolySchurNumeratorStatus where
  | boundaryDiagonalAgreesWithAR4Numerator
  deriving DecidableEq, Repr

inductive AR5NoFreeAssumptionStatus where
  | noHCharpolyNoFactorizationNoCharpolyEqAssumption
  deriving DecidableEq, Repr

def spectralParameterExec (z : SpectralParameter) : ExecComplex :=
  ExecComplex.ofRat z

def spectralPencil
    {ι : Type v} [DecidableEq ι] [Fintype ι]
    (A : Matrix ι ι ExecComplex) (z : SpectralParameter) :
    Matrix ι ι ExecComplex :=
  Matrix.scalar ι (spectralParameterExec z) - A

def operativeDeterminant
    {ι : Type v} [DecidableEq ι] [Fintype ι]
    (A : Matrix ι ι ExecComplex) : ExecComplex :=
  Matrix.det A

def operativeCharpolyEvaluation
    {ι : Type v} [DecidableEq ι] [Fintype ι]
    (A : Matrix ι ι ExecComplex) (z : SpectralParameter) : ExecComplex :=
  operativeDeterminant (spectralPencil A z)

theorem operativeDeterminant_eq_matrix_det
    {ι : Type v} [DecidableEq ι] [Fintype ι]
    (A : Matrix ι ι ExecComplex) :
    operativeDeterminant A = Matrix.det A := by
  rfl

theorem operativeCharpolyEvaluation_eq_det_pencil
    {ι : Type v} [DecidableEq ι] [Fintype ι]
    (A : Matrix ι ι ExecComplex) (z : SpectralParameter) :
    operativeCharpolyEvaluation A z = Matrix.det (spectralPencil A z) := by
  rfl

def boundaryLevelHistoryMatrix
    (B : BoundarySource.BoundarySourceSurface source L) :
    BoundarySource.LevelHistoryMatrix L :=
  fun i j => boundaryMatrixAt B i j

theorem boundaryLevelHistoryMatrix_apply
    (B : BoundarySource.BoundarySourceSurface source L)
    (i j : BoundarySource.LevelHistoryIndex L) :
    boundaryLevelHistoryMatrix B i j = boundaryMatrixAt B i j := by
  rfl

theorem boundaryLevelHistoryMatrix_diag_eq_schurNumerator
    (R : RecursiveSchurSource source L)
    (k : BoundarySource.LevelHistoryIndex L) :
    boundaryLevelHistoryMatrix R.boundarySource k k = R.numerator k := by
  exact (R.numerator_from_boundary k).symm

def detFinOneFormula
    (A : Matrix (Fin 1) (Fin 1) ExecComplex) : ExecComplex :=
  A 0 0

def detFinTwoFormula
    (A : Matrix (Fin 2) (Fin 2) ExecComplex) : ExecComplex :=
  A 0 0 * A 1 1 - A 0 1 * A 1 0

def detFinThreeFormula
    (A : Matrix (Fin 3) (Fin 3) ExecComplex) : ExecComplex :=
  A 0 0 * A 1 1 * A 2 2 -
    A 0 0 * A 1 2 * A 2 1 -
    A 0 1 * A 1 0 * A 2 2 +
    A 0 1 * A 1 2 * A 2 0 +
    A 0 2 * A 1 0 * A 2 1 -
    A 0 2 * A 1 1 * A 2 0

theorem detFinOneFormula_eq_det
    (A : Matrix (Fin 1) (Fin 1) ExecComplex) :
    detFinOneFormula A = operativeDeterminant A := by
  exact (Matrix.det_fin_one A).symm

theorem detFinTwoFormula_eq_det
    (A : Matrix (Fin 2) (Fin 2) ExecComplex) :
    detFinTwoFormula A = operativeDeterminant A := by
  exact (Matrix.det_fin_two A).symm

theorem detFinThreeFormula_eq_det
    (A : Matrix (Fin 3) (Fin 3) ExecComplex) :
    detFinThreeFormula A = operativeDeterminant A := by
  exact (Matrix.det_fin_three A).symm

def charpolyEvalFinOneFormula
    (A : Matrix (Fin 1) (Fin 1) ExecComplex)
    (z : SpectralParameter) : ExecComplex :=
  detFinOneFormula (spectralPencil A z)

def charpolyEvalFinTwoFormula
    (A : Matrix (Fin 2) (Fin 2) ExecComplex)
    (z : SpectralParameter) : ExecComplex :=
  detFinTwoFormula (spectralPencil A z)

def charpolyEvalFinThreeFormula
    (A : Matrix (Fin 3) (Fin 3) ExecComplex)
    (z : SpectralParameter) : ExecComplex :=
  detFinThreeFormula (spectralPencil A z)

theorem charpolyEvalFinOneFormula_eq_eval
    (A : Matrix (Fin 1) (Fin 1) ExecComplex)
    (z : SpectralParameter) :
    charpolyEvalFinOneFormula A z = operativeCharpolyEvaluation A z := by
  exact detFinOneFormula_eq_det (spectralPencil A z)

theorem charpolyEvalFinTwoFormula_eq_eval
    (A : Matrix (Fin 2) (Fin 2) ExecComplex)
    (z : SpectralParameter) :
    charpolyEvalFinTwoFormula A z = operativeCharpolyEvaluation A z := by
  exact detFinTwoFormula_eq_det (spectralPencil A z)

theorem charpolyEvalFinThreeFormula_eq_eval
    (A : Matrix (Fin 3) (Fin 3) ExecComplex)
    (z : SpectralParameter) :
    charpolyEvalFinThreeFormula A z = operativeCharpolyEvaluation A z := by
  exact detFinThreeFormula_eq_det (spectralPencil A z)

structure OperativeCharpolyProfile
    (R : RecursiveSchurSource source L)
    (z : SpectralParameter) where
  matrix : BoundarySource.LevelHistoryMatrix L
  matrix_eq_boundary : matrix = boundaryLevelHistoryMatrix R.boundarySource
  determinant : ExecComplex
  determinant_eq_matrix_det : determinant = operativeDeterminant matrix
  charpolyEvaluation : ExecComplex
  charpolyEvaluation_eq_det_pencil :
    charpolyEvaluation = operativeCharpolyEvaluation matrix z
  schurNumeratorAgreement :
    ∀ k : BoundarySource.LevelHistoryIndex L, matrix k k = R.numerator k
  computationStatus : OperativeCharpolyComputationStatus
  computationStatus_eq :
    computationStatus =
      OperativeCharpolyComputationStatus.determinantAndPencilEvaluationClosed
  smallDimensionStatus : SmallDimensionDeterminantStatus
  smallDimensionStatus_eq :
    smallDimensionStatus =
      SmallDimensionDeterminantStatus.explicitFinOneTwoThreeFormulasCertified
  generalDimensionStatus : GeneralDimensionDeterminantStatus
  generalDimensionStatus_eq :
    generalDimensionStatus =
      GeneralDimensionDeterminantStatus.certifiedFiniteMatrixDeterminant
  numeratorStatus : CharpolySchurNumeratorStatus
  numeratorStatus_eq :
    numeratorStatus =
      CharpolySchurNumeratorStatus.boundaryDiagonalAgreesWithAR4Numerator
  noFreeAssumptionStatus : AR5NoFreeAssumptionStatus
  noFreeAssumptionStatus_eq :
    noFreeAssumptionStatus =
      AR5NoFreeAssumptionStatus.noHCharpolyNoFactorizationNoCharpolyEqAssumption
  route :
    R.boundarySource.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory
  noCutSpecCarrierClaim :
    ∀ _k : BoundarySource.LevelHistoryIndex L,
      source.toc.approximant source.concretePolicy = T

namespace OperativeCharpolyProfile

variable {R : RecursiveSchurSource source L} {z : SpectralParameter}

def fromRecursiveSchurSource
    (R : RecursiveSchurSource source L) (z : SpectralParameter) :
    OperativeCharpolyProfile R z where
  matrix := boundaryLevelHistoryMatrix R.boundarySource
  matrix_eq_boundary := by
    rfl
  determinant := operativeDeterminant (boundaryLevelHistoryMatrix R.boundarySource)
  determinant_eq_matrix_det := by
    rfl
  charpolyEvaluation :=
    operativeCharpolyEvaluation (boundaryLevelHistoryMatrix R.boundarySource) z
  charpolyEvaluation_eq_det_pencil := by
    rfl
  schurNumeratorAgreement := by
    intro k
    exact boundaryLevelHistoryMatrix_diag_eq_schurNumerator R k
  computationStatus :=
    OperativeCharpolyComputationStatus.determinantAndPencilEvaluationClosed
  computationStatus_eq := by
    rfl
  smallDimensionStatus :=
    SmallDimensionDeterminantStatus.explicitFinOneTwoThreeFormulasCertified
  smallDimensionStatus_eq := by
    rfl
  generalDimensionStatus :=
    GeneralDimensionDeterminantStatus.certifiedFiniteMatrixDeterminant
  generalDimensionStatus_eq := by
    rfl
  numeratorStatus :=
    CharpolySchurNumeratorStatus.boundaryDiagonalAgreesWithAR4Numerator
  numeratorStatus_eq := by
    rfl
  noFreeAssumptionStatus :=
    AR5NoFreeAssumptionStatus.noHCharpolyNoFactorizationNoCharpolyEqAssumption
  noFreeAssumptionStatus_eq := by
    rfl
  route := R.route_recursiveHistory
  noCutSpecCarrierClaim := by
    intro k
    exact R.noCutSpecCarrierClaim_at k

theorem matrix_from_boundary
    (P : OperativeCharpolyProfile R z) :
    P.matrix = boundaryLevelHistoryMatrix R.boundarySource :=
  P.matrix_eq_boundary

theorem determinant_from_matrix
    (P : OperativeCharpolyProfile R z) :
    P.determinant = operativeDeterminant P.matrix :=
  P.determinant_eq_matrix_det

theorem charpolyEvaluation_from_det_pencil
    (P : OperativeCharpolyProfile R z) :
    P.charpolyEvaluation = operativeCharpolyEvaluation P.matrix z :=
  P.charpolyEvaluation_eq_det_pencil

theorem diagonal_agrees_with_schurNumerator
    (P : OperativeCharpolyProfile R z)
    (k : BoundarySource.LevelHistoryIndex L) :
    P.matrix k k = R.numerator k :=
  P.schurNumeratorAgreement k

theorem computation_status_closed
    (P : OperativeCharpolyProfile R z) :
    P.computationStatus =
      OperativeCharpolyComputationStatus.determinantAndPencilEvaluationClosed :=
  P.computationStatus_eq

theorem no_free_assumption_status
    (P : OperativeCharpolyProfile R z) :
    P.noFreeAssumptionStatus =
      AR5NoFreeAssumptionStatus.noHCharpolyNoFactorizationNoCharpolyEqAssumption :=
  P.noFreeAssumptionStatus_eq

theorem route_recursiveHistory
    (P : OperativeCharpolyProfile R z) :
    R.boundarySource.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory :=
  P.route

theorem noCutSpecCarrierClaim_at
    (P : OperativeCharpolyProfile R z)
    (k : BoundarySource.LevelHistoryIndex L) :
    source.toc.approximant source.concretePolicy = T :=
  P.noCutSpecCarrierClaim k

end OperativeCharpolyProfile

structure OperativeCharpolyLedger
    (source : ArithmeticSource Cell T) (L : Nat)
    (z : SpectralParameter) where
  recurrenceLedger : SchurMobiusRecurrenceLedger source L
  profile : OperativeCharpolyProfile recurrenceLedger.recursiveSource z
  recurrenceClosed :
    recurrenceLedger.recurrenceStatus =
      SchurMobiusRecurrenceStatus.ar4SchurMobiusRecursionClosed
  profileClosed :
    profile.computationStatus =
      OperativeCharpolyComputationStatus.determinantAndPencilEvaluationClosed
  numeratorAgreement :
    ∀ k : BoundarySource.LevelHistoryIndex L,
      profile.matrix k k = recurrenceLedger.recursiveSource.numerator k
  noFreeAssumptions :
    profile.noFreeAssumptionStatus =
      AR5NoFreeAssumptionStatus.noHCharpolyNoFactorizationNoCharpolyEqAssumption
  route :
    recurrenceLedger.recursiveSource.boundarySource.interface.route =
      BoundarySource.BoundarySourceRoute.recursiveHistory
  noCutSpecCarrierClaim :
    ∀ _k : BoundarySource.LevelHistoryIndex L,
      source.toc.approximant source.concretePolicy = T

namespace OperativeCharpolyLedger

variable {z : SpectralParameter}

def fromBoundarySource
    (B : BoundarySource.BoundarySourceSurface source L)
    (z : SpectralParameter) :
    OperativeCharpolyLedger source L z where
  recurrenceLedger := SchurMobiusRecurrenceLedger.fromBoundarySource B
  profile :=
    OperativeCharpolyProfile.fromRecursiveSchurSource
      (SchurMobiusRecurrenceLedger.fromBoundarySource B).recursiveSource z
  recurrenceClosed := by
    rfl
  profileClosed := by
    rfl
  numeratorAgreement := by
    intro k
    exact boundaryLevelHistoryMatrix_diag_eq_schurNumerator
      (SchurMobiusRecurrenceLedger.fromBoundarySource B).recursiveSource k
  noFreeAssumptions := by
    rfl
  route := B.route_recursiveHistory
  noCutSpecCarrierClaim := by
    intro k
    exact B.noCutSpecCarrierClaim_at k

theorem profile_status_closed
    (Ldg : OperativeCharpolyLedger source L z) :
    Ldg.profile.computationStatus =
      OperativeCharpolyComputationStatus.determinantAndPencilEvaluationClosed :=
  Ldg.profileClosed

theorem recurrence_status_closed
    (Ldg : OperativeCharpolyLedger source L z) :
    Ldg.recurrenceLedger.recurrenceStatus =
      SchurMobiusRecurrenceStatus.ar4SchurMobiusRecursionClosed :=
  Ldg.recurrenceClosed

theorem diagonal_agrees_with_schurNumerator
    (Ldg : OperativeCharpolyLedger source L z)
    (k : BoundarySource.LevelHistoryIndex L) :
    Ldg.profile.matrix k k = Ldg.recurrenceLedger.recursiveSource.numerator k :=
  Ldg.numeratorAgreement k

theorem no_free_assumption_status
    (Ldg : OperativeCharpolyLedger source L z) :
    Ldg.profile.noFreeAssumptionStatus =
      AR5NoFreeAssumptionStatus.noHCharpolyNoFactorizationNoCharpolyEqAssumption :=
  Ldg.noFreeAssumptions

theorem route_recursiveHistory
    (Ldg : OperativeCharpolyLedger source L z) :
    Ldg.recurrenceLedger.recursiveSource.boundarySource.interface.route =
      BoundarySource.BoundarySourceRoute.recursiveHistory :=
  Ldg.route

theorem noCutSpecCarrierClaim_at
    (Ldg : OperativeCharpolyLedger source L z)
    (k : BoundarySource.LevelHistoryIndex L) :
    source.toc.approximant source.concretePolicy = T :=
  Ldg.noCutSpecCarrierClaim k

end OperativeCharpolyLedger

end Schur


end CNNA.PillarA.Arithmetic
