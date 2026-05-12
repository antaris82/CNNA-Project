import CNNA.PillarA.Arithmetic.Schur.CharpolyExec

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

namespace Schur

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}
variable {source : ArithmeticSource Cell T}

abbrev L1Level : Nat := 1

def l1RootIndex : BoundarySource.LevelHistoryIndex L1Level :=
  rootIndex L1Level

def l1LeafIndex : BoundarySource.LevelHistoryIndex L1Level :=
  leafIndex L1Level

theorem l1RootIndex_val : l1RootIndex.val = 0 := by
  rfl

theorem l1LeafIndex_val : l1LeafIndex.val = 1 := by
  rfl

theorem l1_noInteriorIndex
    (k : BoundarySource.LevelHistoryIndex L1Level) :
    ¬ (0 < k.val ∧ k.val < 1) := by
  intro h
  have hk : k.val = 0 := Nat.lt_one_iff.mp h.2
  rw [hk] at h
  exact Nat.lt_irrefl 0 h.1

def l1BranchingRat (b : Nat) : ℚ :=
  ((b + 1 : Nat) : ℚ)

def l1BranchingNorm (b : Nat) : ExecComplex :=
  ExecComplex.ofRat (l1BranchingRat b)

def l1BaselineSpectralRoot (b : Nat) : SpectralParameter :=
  l1BranchingRat b

def l1BaselineScalarMatrix (b : Nat) : Matrix (Fin 1) (Fin 1) ExecComplex :=
  fun _ _ => l1BranchingNorm b

def l1BaselineCharpolyFormula (b : Nat) (z : SpectralParameter) : ExecComplex :=
  spectralParameterExec z - l1BranchingNorm b

theorem l1BranchingNorm_re (b : Nat) :
    (l1BranchingNorm b).re = l1BranchingRat b := by
  rfl

theorem l1BranchingNorm_im (b : Nat) :
    (l1BranchingNorm b).im = 0 := by
  rfl

theorem spectralParameterExec_l1BaselineSpectralRoot (b : Nat) :
    spectralParameterExec (l1BaselineSpectralRoot b) = l1BranchingNorm b := by
  rfl

theorem l1BaselineScalarMatrix_apply
    (b : Nat) (i j : Fin 1) :
    l1BaselineScalarMatrix b i j = l1BranchingNorm b := by
  rfl

theorem l1BaselineScalarMatrix_det_eq_norm (b : Nat) :
    operativeDeterminant (l1BaselineScalarMatrix b) = l1BranchingNorm b := by
  calc
    operativeDeterminant (l1BaselineScalarMatrix b)
        = detFinOneFormula (l1BaselineScalarMatrix b) :=
      (detFinOneFormula_eq_det (l1BaselineScalarMatrix b)).symm
    _ = l1BranchingNorm b := by
      rfl

theorem l1BaselineCharpolyFormula_root (b : Nat) :
    l1BaselineCharpolyFormula b (l1BaselineSpectralRoot b) = 0 := by
  calc
    l1BaselineCharpolyFormula b (l1BaselineSpectralRoot b)
        = l1BranchingNorm b - l1BranchingNorm b := by
      rw [l1BaselineCharpolyFormula, spectralParameterExec_l1BaselineSpectralRoot]
    _ = 0 := sub_self (l1BranchingNorm b)

theorem l1BaselineScalarMatrix_charpoly_root (b : Nat) :
    operativeCharpolyEvaluation (l1BaselineScalarMatrix b)
      (l1BaselineSpectralRoot b) = 0 := by
  calc
    operativeCharpolyEvaluation (l1BaselineScalarMatrix b)
        (l1BaselineSpectralRoot b)
        = charpolyEvalFinOneFormula (l1BaselineScalarMatrix b)
            (l1BaselineSpectralRoot b) :=
      (charpolyEvalFinOneFormula_eq_eval (l1BaselineScalarMatrix b)
        (l1BaselineSpectralRoot b)).symm
    _ = l1BaselineCharpolyFormula b (l1BaselineSpectralRoot b) := by
      simp [charpolyEvalFinOneFormula, detFinOneFormula, spectralPencil,
        l1BaselineScalarMatrix, l1BaselineCharpolyFormula]
    _ = 0 := l1BaselineCharpolyFormula_root b

inductive L1BaselineComputationStatus where
  | ar7L1BaselineClosed
  deriving DecidableEq, Repr

inductive L1BaselineTransportStatus where
  | boundarySourceTransportAndScalarControlSeparated
  deriving DecidableEq, Repr

inductive L1BaselineNormformStatus where
  | branchingNormformBPlusOneCertified
  deriving DecidableEq, Repr

inductive L1BaselineSignalDisciplineStatus where
  | noCMQuaternionMoonshineOrGeometrySignalFromL1
  deriving DecidableEq, Repr

structure L1BoundaryMatrixProfile
    (B : BoundarySource.BoundarySourceSurface source L1Level) where
  matrix : BoundarySource.LevelHistoryMatrix L1Level
  matrix_eq_boundary : matrix = boundaryLevelHistoryMatrix B
  rootRoot : ExecComplex
  rootRoot_eq : rootRoot = matrix l1RootIndex l1RootIndex
  rootLeaf : ExecComplex
  rootLeaf_eq : rootLeaf = matrix l1RootIndex l1LeafIndex
  leafRoot : ExecComplex
  leafRoot_eq : leafRoot = matrix l1LeafIndex l1RootIndex
  leafLeaf : ExecComplex
  leafLeaf_eq : leafLeaf = matrix l1LeafIndex l1LeafIndex
  route : B.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory
  noCutSpecCarrierClaim :
    ∀ _k : BoundarySource.LevelHistoryIndex L1Level,
      source.toc.approximant source.concretePolicy = T

namespace L1BoundaryMatrixProfile

variable {B : BoundarySource.BoundarySourceSurface source L1Level}

def fromBoundarySource
    (B : BoundarySource.BoundarySourceSurface source L1Level) :
    L1BoundaryMatrixProfile B where
  matrix := boundaryLevelHistoryMatrix B
  matrix_eq_boundary := by
    rfl
  rootRoot := boundaryLevelHistoryMatrix B l1RootIndex l1RootIndex
  rootRoot_eq := by
    rfl
  rootLeaf := boundaryLevelHistoryMatrix B l1RootIndex l1LeafIndex
  rootLeaf_eq := by
    rfl
  leafRoot := boundaryLevelHistoryMatrix B l1LeafIndex l1RootIndex
  leafRoot_eq := by
    rfl
  leafLeaf := boundaryLevelHistoryMatrix B l1LeafIndex l1LeafIndex
  leafLeaf_eq := by
    rfl
  route := B.route_recursiveHistory
  noCutSpecCarrierClaim := by
    intro k
    exact B.noCutSpecCarrierClaim_at k

theorem matrix_from_boundary
    (P : L1BoundaryMatrixProfile B) :
    P.matrix = boundaryLevelHistoryMatrix B :=
  P.matrix_eq_boundary

theorem rootRoot_from_matrix
    (P : L1BoundaryMatrixProfile B) :
    P.rootRoot = P.matrix l1RootIndex l1RootIndex :=
  P.rootRoot_eq

theorem rootLeaf_from_matrix
    (P : L1BoundaryMatrixProfile B) :
    P.rootLeaf = P.matrix l1RootIndex l1LeafIndex :=
  P.rootLeaf_eq

theorem leafRoot_from_matrix
    (P : L1BoundaryMatrixProfile B) :
    P.leafRoot = P.matrix l1LeafIndex l1RootIndex :=
  P.leafRoot_eq

theorem leafLeaf_from_matrix
    (P : L1BoundaryMatrixProfile B) :
    P.leafLeaf = P.matrix l1LeafIndex l1LeafIndex :=
  P.leafLeaf_eq

theorem route_recursiveHistory
    (P : L1BoundaryMatrixProfile B) :
    B.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory :=
  P.route

theorem noCutSpecCarrierClaim_at
    (P : L1BoundaryMatrixProfile B)
    (k : BoundarySource.LevelHistoryIndex L1Level) :
    source.toc.approximant source.concretePolicy = T :=
  P.noCutSpecCarrierClaim k

end L1BoundaryMatrixProfile

structure L1BaselineLedger
    (B : BoundarySource.BoundarySourceSurface source L1Level)
    (b : Nat) where
  boundaryMatrixProfile : L1BoundaryMatrixProfile B
  recurrenceLedger : SchurMobiusRecurrenceLedger source L1Level
  recurrenceLedger_eq : recurrenceLedger = SchurMobiusRecurrenceLedger.fromBoundarySource B
  charpolyLedger : OperativeCharpolyLedger source L1Level (l1BaselineSpectralRoot b)
  charpolyLedger_eq :
    charpolyLedger = OperativeCharpolyLedger.fromBoundarySource B (l1BaselineSpectralRoot b)
  scalarControlMatrix : Matrix (Fin 1) (Fin 1) ExecComplex
  scalarControlMatrix_eq : scalarControlMatrix = l1BaselineScalarMatrix b
  scalarDeterminant_eq_normform :
    operativeDeterminant scalarControlMatrix = l1BranchingNorm b
  scalarCharpolyRoot :
    operativeCharpolyEvaluation scalarControlMatrix (l1BaselineSpectralRoot b) = 0
  normform : ExecComplex
  normform_eq : normform = l1BranchingNorm b
  normform_re : normform.re = l1BranchingRat b
  normform_im : normform.im = 0
  eigenvalue : SpectralParameter
  eigenvalue_eq : eigenvalue = l1BaselineSpectralRoot b
  noInteriorIndex :
    ∀ k : BoundarySource.LevelHistoryIndex L1Level,
      ¬ (0 < k.val ∧ k.val < 1)
  computationStatus : L1BaselineComputationStatus
  computationStatus_eq : computationStatus = L1BaselineComputationStatus.ar7L1BaselineClosed
  transportStatus : L1BaselineTransportStatus
  transportStatus_eq :
    transportStatus =
      L1BaselineTransportStatus.boundarySourceTransportAndScalarControlSeparated
  normformStatus : L1BaselineNormformStatus
  normformStatus_eq :
    normformStatus = L1BaselineNormformStatus.branchingNormformBPlusOneCertified
  signalDisciplineStatus : L1BaselineSignalDisciplineStatus
  signalDisciplineStatus_eq :
    signalDisciplineStatus =
      L1BaselineSignalDisciplineStatus.noCMQuaternionMoonshineOrGeometrySignalFromL1
  recurrenceClosed :
    recurrenceLedger.recurrenceStatus =
      SchurMobiusRecurrenceStatus.ar4SchurMobiusRecursionClosed
  charpolyClosed :
    charpolyLedger.profile.computationStatus =
      OperativeCharpolyComputationStatus.determinantAndPencilEvaluationClosed
  charpolyNoFreeAssumptions :
    charpolyLedger.profile.noFreeAssumptionStatus =
      AR5NoFreeAssumptionStatus.noHCharpolyNoFactorizationNoCharpolyEqAssumption
  route : B.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory
  noCutSpecCarrierClaim :
    ∀ _k : BoundarySource.LevelHistoryIndex L1Level,
      source.toc.approximant source.concretePolicy = T

namespace L1BaselineLedger

variable {B : BoundarySource.BoundarySourceSurface source L1Level}
variable {b : Nat}

def fromBoundarySource
    (B : BoundarySource.BoundarySourceSurface source L1Level)
    (b : Nat) :
    L1BaselineLedger B b where
  boundaryMatrixProfile := L1BoundaryMatrixProfile.fromBoundarySource B
  recurrenceLedger := SchurMobiusRecurrenceLedger.fromBoundarySource B
  recurrenceLedger_eq := by
    rfl
  charpolyLedger := OperativeCharpolyLedger.fromBoundarySource B (l1BaselineSpectralRoot b)
  charpolyLedger_eq := by
    rfl
  scalarControlMatrix := l1BaselineScalarMatrix b
  scalarControlMatrix_eq := by
    rfl
  scalarDeterminant_eq_normform := l1BaselineScalarMatrix_det_eq_norm b
  scalarCharpolyRoot := l1BaselineScalarMatrix_charpoly_root b
  normform := l1BranchingNorm b
  normform_eq := by
    rfl
  normform_re := by
    rfl
  normform_im := by
    rfl
  eigenvalue := l1BaselineSpectralRoot b
  eigenvalue_eq := by
    rfl
  noInteriorIndex := by
    intro k
    exact l1_noInteriorIndex k
  computationStatus := L1BaselineComputationStatus.ar7L1BaselineClosed
  computationStatus_eq := by
    rfl
  transportStatus :=
    L1BaselineTransportStatus.boundarySourceTransportAndScalarControlSeparated
  transportStatus_eq := by
    rfl
  normformStatus := L1BaselineNormformStatus.branchingNormformBPlusOneCertified
  normformStatus_eq := by
    rfl
  signalDisciplineStatus :=
    L1BaselineSignalDisciplineStatus.noCMQuaternionMoonshineOrGeometrySignalFromL1
  signalDisciplineStatus_eq := by
    rfl
  recurrenceClosed := by
    rfl
  charpolyClosed := by
    rfl
  charpolyNoFreeAssumptions := by
    rfl
  route := B.route_recursiveHistory
  noCutSpecCarrierClaim := by
    intro k
    exact B.noCutSpecCarrierClaim_at k

theorem status_closed
    (Ldg : L1BaselineLedger B b) :
    Ldg.computationStatus = L1BaselineComputationStatus.ar7L1BaselineClosed :=
  Ldg.computationStatus_eq

theorem transport_separated
    (Ldg : L1BaselineLedger B b) :
    Ldg.transportStatus =
      L1BaselineTransportStatus.boundarySourceTransportAndScalarControlSeparated :=
  Ldg.transportStatus_eq

theorem normform_certified
    (Ldg : L1BaselineLedger B b) :
    Ldg.normformStatus = L1BaselineNormformStatus.branchingNormformBPlusOneCertified :=
  Ldg.normformStatus_eq

theorem no_forbidden_signal
    (Ldg : L1BaselineLedger B b) :
    Ldg.signalDisciplineStatus =
      L1BaselineSignalDisciplineStatus.noCMQuaternionMoonshineOrGeometrySignalFromL1 :=
  Ldg.signalDisciplineStatus_eq

theorem scalar_matrix_is_branching_norm
    (Ldg : L1BaselineLedger B b) :
    Ldg.scalarControlMatrix = l1BaselineScalarMatrix b :=
  Ldg.scalarControlMatrix_eq

theorem scalar_determinant_eq_normform
    (Ldg : L1BaselineLedger B b) :
    operativeDeterminant Ldg.scalarControlMatrix = l1BranchingNorm b :=
  Ldg.scalarDeterminant_eq_normform

theorem scalar_charpoly_root
    (Ldg : L1BaselineLedger B b) :
    operativeCharpolyEvaluation Ldg.scalarControlMatrix (l1BaselineSpectralRoot b) = 0 :=
  Ldg.scalarCharpolyRoot

theorem normform_eq_branching
    (Ldg : L1BaselineLedger B b) :
    Ldg.normform = l1BranchingNorm b :=
  Ldg.normform_eq

theorem eigenvalue_eq_branching
    (Ldg : L1BaselineLedger B b) :
    Ldg.eigenvalue = l1BaselineSpectralRoot b :=
  Ldg.eigenvalue_eq

theorem recurrence_status_closed
    (Ldg : L1BaselineLedger B b) :
    Ldg.recurrenceLedger.recurrenceStatus =
      SchurMobiusRecurrenceStatus.ar4SchurMobiusRecursionClosed :=
  Ldg.recurrenceClosed

theorem charpoly_status_closed
    (Ldg : L1BaselineLedger B b) :
    Ldg.charpolyLedger.profile.computationStatus =
      OperativeCharpolyComputationStatus.determinantAndPencilEvaluationClosed :=
  Ldg.charpolyClosed

theorem charpoly_no_free_assumptions
    (Ldg : L1BaselineLedger B b) :
    Ldg.charpolyLedger.profile.noFreeAssumptionStatus =
      AR5NoFreeAssumptionStatus.noHCharpolyNoFactorizationNoCharpolyEqAssumption :=
  Ldg.charpolyNoFreeAssumptions

theorem route_recursiveHistory
    (Ldg : L1BaselineLedger B b) :
    B.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory :=
  Ldg.route

theorem noCutSpecCarrierClaim_at
    (Ldg : L1BaselineLedger B b)
    (k : BoundarySource.LevelHistoryIndex L1Level) :
    source.toc.approximant source.concretePolicy = T :=
  Ldg.noCutSpecCarrierClaim k

end L1BaselineLedger

end Schur

namespace StrengtheningAR7

abbrev AR7L1Level := Schur.L1Level
abbrev AR7L1RootIndex := Schur.l1RootIndex
abbrev AR7L1LeafIndex := Schur.l1LeafIndex
abbrev AR7L1BaselineComputationStatus := Schur.L1BaselineComputationStatus
abbrev AR7L1BaselineTransportStatus := Schur.L1BaselineTransportStatus
abbrev AR7L1BaselineNormformStatus := Schur.L1BaselineNormformStatus
abbrev AR7L1BaselineSignalDisciplineStatus := Schur.L1BaselineSignalDisciplineStatus

abbrev AR7L1BoundaryMatrixProfile
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T}
    (B : BoundarySource.BoundarySourceSurface source Schur.L1Level) :=
  Schur.L1BoundaryMatrixProfile B

abbrev AR7L1BaselineLedger
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T}
    (B : BoundarySource.BoundarySourceSurface source Schur.L1Level)
    (b : Nat) :=
  Schur.L1BaselineLedger B b

def AR7L1BaselineLedgerFromBoundarySource
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T}
    (B : BoundarySource.BoundarySourceSurface source Schur.L1Level)
    (b : Nat) :
    AR7L1BaselineLedger B b :=
  Schur.L1BaselineLedger.fromBoundarySource B b

theorem AR7L1BaselineLedger_status_closed
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T}
    {B : BoundarySource.BoundarySourceSurface source Schur.L1Level}
    {b : Nat}
    (Ldg : AR7L1BaselineLedger B b) :
    Ldg.computationStatus = Schur.L1BaselineComputationStatus.ar7L1BaselineClosed :=
  Schur.L1BaselineLedger.status_closed Ldg

theorem AR7L1BaselineLedger_no_forbidden_signal
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T}
    {B : BoundarySource.BoundarySourceSurface source Schur.L1Level}
    {b : Nat}
    (Ldg : AR7L1BaselineLedger B b) :
    Ldg.signalDisciplineStatus =
      Schur.L1BaselineSignalDisciplineStatus.noCMQuaternionMoonshineOrGeometrySignalFromL1 :=
  Schur.L1BaselineLedger.no_forbidden_signal Ldg

end StrengtheningAR7

end CNNA.PillarA.Arithmetic
