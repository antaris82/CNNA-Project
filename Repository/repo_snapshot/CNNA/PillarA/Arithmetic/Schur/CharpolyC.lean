import CNNA.PillarA.Foundation.ExecComplexBridge
import CNNA.PillarA.Arithmetic.Schur.CharpolyExec

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u v

namespace Schur

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}
variable {source : ArithmeticSource Cell T} {L : Nat}

abbrev MirrorSpectralParameter := ℂ

def spectralParameterC (z : SpectralParameter) : MirrorSpectralParameter :=
  ExecComplexBridge.toComplex (spectralParameterExec z)

theorem spectralParameterC_eq_ratCast (z : SpectralParameter) :
    spectralParameterC z = (z : ℂ) := by
  simpa [spectralParameterC, spectralParameterExec] using
    ExecComplexBridge.toComplex_ofRat z

def mirrorMatrix
    {ι : Type v} (A : Matrix ι ι ExecComplex) : Matrix ι ι ℂ :=
  ExecComplexBridge.mapMatrix A

theorem mirrorMatrix_apply
    {ι : Type v} (A : Matrix ι ι ExecComplex) (i j : ι) :
    mirrorMatrix A i j = ExecComplexBridge.toComplex (A i j) := by
  rfl

def mirrorDeterminant
    {ι : Type v} [DecidableEq ι] [Fintype ι]
    (A : Matrix ι ι ExecComplex) : ℂ :=
  Matrix.det (mirrorMatrix A)

theorem mirrorDeterminant_eq_map_operativeDeterminant
    {ι : Type v} [DecidableEq ι] [Fintype ι]
    (A : Matrix ι ι ExecComplex) :
    mirrorDeterminant A = ExecComplexBridge.toComplex (operativeDeterminant A) := by
  simpa [mirrorDeterminant, mirrorMatrix, operativeDeterminant,
    ExecComplexBridge.toComplexHom_apply,
    ExecComplexBridge.mapSquareMatrix_apply] using
    (RingHom.map_det ExecComplexBridge.toComplexHom A).symm

def mirrorSpectralPencil
    {ι : Type v} [DecidableEq ι] [Fintype ι]
    (A : Matrix ι ι ExecComplex) (z : SpectralParameter) : Matrix ι ι ℂ :=
  ExecComplexBridge.mapMatrix (spectralPencil A z)

theorem mirrorSpectralPencil_eq_map
    {ι : Type v} [DecidableEq ι] [Fintype ι]
    (A : Matrix ι ι ExecComplex) (z : SpectralParameter) :
    mirrorSpectralPencil A z = ExecComplexBridge.mapMatrix (spectralPencil A z) := by
  rfl

def mirrorCharpolyEvaluation
    {ι : Type v} [DecidableEq ι] [Fintype ι]
    (A : Matrix ι ι ExecComplex) (z : SpectralParameter) : ℂ :=
  Matrix.det (mirrorSpectralPencil A z)

theorem mirrorCharpolyEvaluation_eq_map_operativeCharpolyEvaluation
    {ι : Type v} [DecidableEq ι] [Fintype ι]
    (A : Matrix ι ι ExecComplex) (z : SpectralParameter) :
    mirrorCharpolyEvaluation A z =
      ExecComplexBridge.toComplex (operativeCharpolyEvaluation A z) := by
  simpa [mirrorCharpolyEvaluation, mirrorSpectralPencil,
    operativeCharpolyEvaluation, operativeDeterminant,
    ExecComplexBridge.toComplexHom_apply,
    ExecComplexBridge.mapSquareMatrix_apply] using
    (RingHom.map_det ExecComplexBridge.toComplexHom (spectralPencil A z)).symm

theorem mirrorCharpolyEvaluation_zero_of_exec_zero
    {ι : Type v} [DecidableEq ι] [Fintype ι]
    {A : Matrix ι ι ExecComplex} {z : SpectralParameter}
    (h : operativeCharpolyEvaluation A z = 0) :
    mirrorCharpolyEvaluation A z = 0 := by
  rw [mirrorCharpolyEvaluation_eq_map_operativeCharpolyEvaluation, h,
    ExecComplexBridge.toComplex_zero]

structure MirrorEigenvalueCertificate
    {ι : Type v} [DecidableEq ι] [Fintype ι]
    (A : Matrix ι ι ExecComplex) where
  spectralParameter : SpectralParameter
  spectralValue : MirrorSpectralParameter
  spectralValue_eq_map : spectralValue = spectralParameterC spectralParameter
  determinantZero : mirrorCharpolyEvaluation A spectralParameter = 0
  sourceIsExecRoot : operativeCharpolyEvaluation A spectralParameter = 0

namespace MirrorEigenvalueCertificate

variable {ι : Type v} [DecidableEq ι] [Fintype ι]
variable {A : Matrix ι ι ExecComplex}

def fromExecRoot
    (z : SpectralParameter)
    (h : operativeCharpolyEvaluation A z = 0) :
    MirrorEigenvalueCertificate A where
  spectralParameter := z
  spectralValue := spectralParameterC z
  spectralValue_eq_map := by
    rfl
  determinantZero := mirrorCharpolyEvaluation_zero_of_exec_zero h
  sourceIsExecRoot := h

theorem determinant_zero
    (E : MirrorEigenvalueCertificate A) :
    mirrorCharpolyEvaluation A E.spectralParameter = 0 :=
  E.determinantZero

theorem exec_root
    (E : MirrorEigenvalueCertificate A) :
    operativeCharpolyEvaluation A E.spectralParameter = 0 :=
  E.sourceIsExecRoot

end MirrorEigenvalueCertificate

structure MirrorUpperHalfPlanePoint where
  point : ℂ
  im_pos : 0 < point.im

inductive CMirrorConstructionStatus where
  | complexMatrixAndPencilMappedFromExec
  deriving DecidableEq, Repr

inductive CMirrorEigenvalueStatus where
  | determinantZeroCertificateOnly
  deriving DecidableEq, Repr

inductive CMirrorUpperHalfPlaneStatus where
  | upperHalfPlaneCarrierOnlyNoCMPointClaim
  deriving DecidableEq, Repr

inductive CMirrorNoReverseConsumptionStatus where
  | execPathDoesNotConsumeMirror
  deriving DecidableEq, Repr

inductive CMirrorLegacySeparationStatus where
  | realoqsPatternsAreInspirationOnlyNoImportPath
  deriving DecidableEq, Repr

inductive CMirrorParameterSeparationStatus where
  | spectralRatSeparateFromModularQ
  deriving DecidableEq, Repr

structure CMirrorCharpolyProfile
    {z : SpectralParameter}
    (Ldg : OperativeCharpolyLedger source L z) where
  execMatrix : BoundarySource.LevelHistoryMatrix L
  execMatrix_eq_profile : execMatrix = Ldg.profile.matrix
  complexMatrix : Matrix (BoundarySource.LevelHistoryIndex L)
      (BoundarySource.LevelHistoryIndex L) ℂ
  complexMatrix_eq_map : complexMatrix = mirrorMatrix execMatrix
  execCharpolyEvaluation : ExecComplex
  execCharpolyEvaluation_eq_profile : execCharpolyEvaluation = Ldg.profile.charpolyEvaluation
  complexCharpolyEvaluation : ℂ
  complexCharpolyEvaluation_eq_det_pencil :
    complexCharpolyEvaluation = mirrorCharpolyEvaluation execMatrix z
  charpolyEvaluation_eq_map_exec :
    complexCharpolyEvaluation = ExecComplexBridge.toComplex execCharpolyEvaluation
  determinantTransfer :
    mirrorDeterminant execMatrix =
      ExecComplexBridge.toComplex (operativeDeterminant execMatrix)
  pencilTransfer :
    mirrorSpectralPencil execMatrix z =
      ExecComplexBridge.mapMatrix (spectralPencil execMatrix z)
  constructionStatus : CMirrorConstructionStatus
  constructionStatus_eq :
    constructionStatus = CMirrorConstructionStatus.complexMatrixAndPencilMappedFromExec
  eigenvalueStatus : CMirrorEigenvalueStatus
  eigenvalueStatus_eq :
    eigenvalueStatus = CMirrorEigenvalueStatus.determinantZeroCertificateOnly
  upperHalfPlaneStatus : CMirrorUpperHalfPlaneStatus
  upperHalfPlaneStatus_eq :
    upperHalfPlaneStatus =
      CMirrorUpperHalfPlaneStatus.upperHalfPlaneCarrierOnlyNoCMPointClaim
  noReverseConsumptionStatus : CMirrorNoReverseConsumptionStatus
  noReverseConsumptionStatus_eq :
    noReverseConsumptionStatus =
      CMirrorNoReverseConsumptionStatus.execPathDoesNotConsumeMirror
  legacySeparationStatus : CMirrorLegacySeparationStatus
  legacySeparationStatus_eq :
    legacySeparationStatus =
      CMirrorLegacySeparationStatus.realoqsPatternsAreInspirationOnlyNoImportPath
  parameterSeparationStatus : CMirrorParameterSeparationStatus
  parameterSeparationStatus_eq :
    parameterSeparationStatus =
      CMirrorParameterSeparationStatus.spectralRatSeparateFromModularQ
  ar5Closed :
    Ldg.profile.computationStatus =
      OperativeCharpolyComputationStatus.determinantAndPencilEvaluationClosed
  ar5NoFreeAssumptions :
    Ldg.profile.noFreeAssumptionStatus =
      AR5NoFreeAssumptionStatus.noHCharpolyNoFactorizationNoCharpolyEqAssumption
  route :
    Ldg.recurrenceLedger.recursiveSource.boundarySource.interface.route =
      BoundarySource.BoundarySourceRoute.recursiveHistory
  noCutSpecCarrierClaim :
    ∀ _k : BoundarySource.LevelHistoryIndex L,
      source.toc.approximant source.concretePolicy = T

namespace CMirrorCharpolyProfile

variable {z : SpectralParameter}
variable {Ldg : OperativeCharpolyLedger source L z}

def fromOperativeCharpolyLedger
    (Ldg : OperativeCharpolyLedger source L z) :
    CMirrorCharpolyProfile Ldg where
  execMatrix := Ldg.profile.matrix
  execMatrix_eq_profile := by
    rfl
  complexMatrix := mirrorMatrix Ldg.profile.matrix
  complexMatrix_eq_map := by
    rfl
  execCharpolyEvaluation := Ldg.profile.charpolyEvaluation
  execCharpolyEvaluation_eq_profile := by
    rfl
  complexCharpolyEvaluation := mirrorCharpolyEvaluation Ldg.profile.matrix z
  complexCharpolyEvaluation_eq_det_pencil := by
    rfl
  charpolyEvaluation_eq_map_exec := by
    calc
      mirrorCharpolyEvaluation Ldg.profile.matrix z =
          ExecComplexBridge.toComplex
            (operativeCharpolyEvaluation Ldg.profile.matrix z) :=
        mirrorCharpolyEvaluation_eq_map_operativeCharpolyEvaluation Ldg.profile.matrix z
      _ = ExecComplexBridge.toComplex Ldg.profile.charpolyEvaluation := by
        rw [← Ldg.profile.charpolyEvaluation_eq_det_pencil]
  determinantTransfer :=
    mirrorDeterminant_eq_map_operativeDeterminant Ldg.profile.matrix
  pencilTransfer := by
    rfl
  constructionStatus := CMirrorConstructionStatus.complexMatrixAndPencilMappedFromExec
  constructionStatus_eq := by
    rfl
  eigenvalueStatus := CMirrorEigenvalueStatus.determinantZeroCertificateOnly
  eigenvalueStatus_eq := by
    rfl
  upperHalfPlaneStatus :=
    CMirrorUpperHalfPlaneStatus.upperHalfPlaneCarrierOnlyNoCMPointClaim
  upperHalfPlaneStatus_eq := by
    rfl
  noReverseConsumptionStatus :=
    CMirrorNoReverseConsumptionStatus.execPathDoesNotConsumeMirror
  noReverseConsumptionStatus_eq := by
    rfl
  legacySeparationStatus :=
    CMirrorLegacySeparationStatus.realoqsPatternsAreInspirationOnlyNoImportPath
  legacySeparationStatus_eq := by
    rfl
  parameterSeparationStatus :=
    CMirrorParameterSeparationStatus.spectralRatSeparateFromModularQ
  parameterSeparationStatus_eq := by
    rfl
  ar5Closed := Ldg.profileClosed
  ar5NoFreeAssumptions := Ldg.noFreeAssumptions
  route := Ldg.route
  noCutSpecCarrierClaim := by
    intro k
    exact Ldg.noCutSpecCarrierClaim_at k

theorem complex_charpoly_maps_exec
    (P : CMirrorCharpolyProfile Ldg) :
    P.complexCharpolyEvaluation =
      ExecComplexBridge.toComplex P.execCharpolyEvaluation :=
  P.charpolyEvaluation_eq_map_exec

theorem construction_status_closed
    (P : CMirrorCharpolyProfile Ldg) :
    P.constructionStatus = CMirrorConstructionStatus.complexMatrixAndPencilMappedFromExec :=
  P.constructionStatus_eq

theorem no_reverse_consumption
    (P : CMirrorCharpolyProfile Ldg) :
    P.noReverseConsumptionStatus =
      CMirrorNoReverseConsumptionStatus.execPathDoesNotConsumeMirror :=
  P.noReverseConsumptionStatus_eq

theorem upperHalfPlane_carrier_only
    (P : CMirrorCharpolyProfile Ldg) :
    P.upperHalfPlaneStatus =
      CMirrorUpperHalfPlaneStatus.upperHalfPlaneCarrierOnlyNoCMPointClaim :=
  P.upperHalfPlaneStatus_eq

theorem parameter_separation
    (P : CMirrorCharpolyProfile Ldg) :
    P.parameterSeparationStatus =
      CMirrorParameterSeparationStatus.spectralRatSeparateFromModularQ :=
  P.parameterSeparationStatus_eq

theorem no_free_assumptions
    (P : CMirrorCharpolyProfile Ldg) :
    Ldg.profile.noFreeAssumptionStatus =
      AR5NoFreeAssumptionStatus.noHCharpolyNoFactorizationNoCharpolyEqAssumption :=
  P.ar5NoFreeAssumptions

theorem route_recursiveHistory
    (P : CMirrorCharpolyProfile Ldg) :
    Ldg.recurrenceLedger.recursiveSource.boundarySource.interface.route =
      BoundarySource.BoundarySourceRoute.recursiveHistory :=
  P.route

end CMirrorCharpolyProfile

structure CMirrorCharpolyLedger
    (source : ArithmeticSource Cell T) (L : Nat)
    (z : SpectralParameter) where
  operativeLedger : OperativeCharpolyLedger source L z
  mirrorProfile : CMirrorCharpolyProfile operativeLedger
  constructionClosed :
    mirrorProfile.constructionStatus =
      CMirrorConstructionStatus.complexMatrixAndPencilMappedFromExec
  charpolyBridge :
    mirrorProfile.complexCharpolyEvaluation =
      ExecComplexBridge.toComplex mirrorProfile.execCharpolyEvaluation
  upperHalfPlaneStatus :
    mirrorProfile.upperHalfPlaneStatus =
      CMirrorUpperHalfPlaneStatus.upperHalfPlaneCarrierOnlyNoCMPointClaim
  noReverseConsumption :
    mirrorProfile.noReverseConsumptionStatus =
      CMirrorNoReverseConsumptionStatus.execPathDoesNotConsumeMirror
  parameterSeparation :
    mirrorProfile.parameterSeparationStatus =
      CMirrorParameterSeparationStatus.spectralRatSeparateFromModularQ
  route :
    operativeLedger.recurrenceLedger.recursiveSource.boundarySource.interface.route =
      BoundarySource.BoundarySourceRoute.recursiveHistory
  noCutSpecCarrierClaim :
    ∀ _k : BoundarySource.LevelHistoryIndex L,
      source.toc.approximant source.concretePolicy = T

namespace CMirrorCharpolyLedger

variable {z : SpectralParameter}

def fromOperativeCharpolyLedger
    (Ldg : OperativeCharpolyLedger source L z) :
    CMirrorCharpolyLedger source L z where
  operativeLedger := Ldg
  mirrorProfile := CMirrorCharpolyProfile.fromOperativeCharpolyLedger Ldg
  constructionClosed := by
    rfl
  charpolyBridge := by
    exact (CMirrorCharpolyProfile.fromOperativeCharpolyLedger Ldg).charpolyEvaluation_eq_map_exec
  upperHalfPlaneStatus := by
    rfl
  noReverseConsumption := by
    rfl
  parameterSeparation := by
    rfl
  route := Ldg.route
  noCutSpecCarrierClaim := by
    intro k
    exact Ldg.noCutSpecCarrierClaim_at k

def fromBoundarySource
    (B : BoundarySource.BoundarySourceSurface source L)
    (z : SpectralParameter) :
    CMirrorCharpolyLedger source L z :=
  fromOperativeCharpolyLedger (OperativeCharpolyLedger.fromBoundarySource B z)

theorem construction_status_closed
    (Ldg : CMirrorCharpolyLedger source L z) :
    Ldg.mirrorProfile.constructionStatus =
      CMirrorConstructionStatus.complexMatrixAndPencilMappedFromExec :=
  Ldg.constructionClosed

theorem charpoly_bridge
    (Ldg : CMirrorCharpolyLedger source L z) :
    Ldg.mirrorProfile.complexCharpolyEvaluation =
      ExecComplexBridge.toComplex Ldg.mirrorProfile.execCharpolyEvaluation :=
  Ldg.charpolyBridge

theorem upperHalfPlane_carrier_only
    (Ldg : CMirrorCharpolyLedger source L z) :
    Ldg.mirrorProfile.upperHalfPlaneStatus =
      CMirrorUpperHalfPlaneStatus.upperHalfPlaneCarrierOnlyNoCMPointClaim :=
  Ldg.upperHalfPlaneStatus

theorem no_reverse_consumption
    (Ldg : CMirrorCharpolyLedger source L z) :
    Ldg.mirrorProfile.noReverseConsumptionStatus =
      CMirrorNoReverseConsumptionStatus.execPathDoesNotConsumeMirror :=
  Ldg.noReverseConsumption

theorem parameter_separation
    (Ldg : CMirrorCharpolyLedger source L z) :
    Ldg.mirrorProfile.parameterSeparationStatus =
      CMirrorParameterSeparationStatus.spectralRatSeparateFromModularQ :=
  Ldg.parameterSeparation

theorem route_recursiveHistory
    (Ldg : CMirrorCharpolyLedger source L z) :
    Ldg.operativeLedger.recurrenceLedger.recursiveSource.boundarySource.interface.route =
      BoundarySource.BoundarySourceRoute.recursiveHistory :=
  Ldg.route

theorem noCutSpecCarrierClaim_at
    (Ldg : CMirrorCharpolyLedger source L z)
    (k : BoundarySource.LevelHistoryIndex L) :
    source.toc.approximant source.concretePolicy = T :=
  Ldg.noCutSpecCarrierClaim k

end CMirrorCharpolyLedger

end Schur

end CNNA.PillarA.Arithmetic
