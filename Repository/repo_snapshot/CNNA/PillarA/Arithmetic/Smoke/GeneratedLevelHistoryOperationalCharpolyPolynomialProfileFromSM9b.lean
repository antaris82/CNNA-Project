import CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryCharpolyExecFromMirrorSM9b

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.DtN

namespace Smoke

universe u

inductive SM9cOperationalPolynomialProfileStatus where
  | evaluationFamilyClosedFromSM9b
  deriving DecidableEq, Repr

inductive SM9cCoefficientExtractionStatus where
  | blockedUntilOperationalCoefficientSource
  deriving DecidableEq, Repr

inductive SM9cNextPhaseStatus where
  | coefficientSourceBeforeDiscriminantGate
  deriving DecidableEq, Repr

inductive SM9cNoFreeCoefficientTableStatus where
  | noFreeCoefficientTable
  deriving DecidableEq, Repr

inductive SM9cNoFactorizationStatus where
  | noFactorization
  deriving DecidableEq, Repr

inductive SM9cNoDiscriminantStatus where
  | noDiscriminant
  deriving DecidableEq, Repr

inductive SM9cNoRootExtractionStatus where
  | noRootExtraction
  deriving DecidableEq, Repr

inductive SM9cNoHeegnerTargetStatus where
  | noHeegnerTarget
  deriving DecidableEq, Repr

inductive SM9cNoCMTargetStatus where
  | noCMTarget
  deriving DecidableEq, Repr

inductive SM9cNoMatrixInvStatus where
  | noMatrixInv
  deriving DecidableEq, Repr

inductive SM9cNoFieldSimpStatus where
  | noFieldSimp
  deriving DecidableEq, Repr

inductive SM9cNoScalarInvStatus where
  | noScalarInv
  deriving DecidableEq, Repr

inductive SM9cNoNoncomputableOperationalSourceStatus where
  | noNoncomputableOperationalSource
  deriving DecidableEq, Repr

inductive SM9cNoMatrixCharpolyOracleStatus where
  | noMatrixCharpolyOracle
  deriving DecidableEq, Repr

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {p : ConcretePolicyOf}
variable {A : GeneratedApproximantStrong Cell p}
variable [Fintype (GeneratedBoundaryIndex A)]
variable [Fintype (GeneratedInteriorIndex A)]
variable [DecidableEq (GeneratedInteriorIndex A)]
variable {P : GeneratedBoundaryInteriorPartition Cell p A}
variable {wp : WeightPolicy}
variable {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
variable {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
variable {K : GeneratedInteriorEliminationCarrier Cell p A P wp W E}
variable {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}
variable {M : GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T}
variable {S : GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M}
variable {H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S}
variable {G : GeneratedMultiSchurSM4 Cell p A P wp W E K T M S H}

def generatedLevelHistoryOperationalCharpolyEvaluationFamilySM9c
    (C : GeneratedLevelHistoryCharpolyExecFromMirrorSM9b Cell p A P wp W E K T M S H G)
    (z : Schur.SpectralParameter) : ExecComplex :=
  Schur.operativeCharpolyEvaluation C.matrix z

def generatedLevelHistoryOperationalCharpolyEvaluationAtSM9bParameterSM9c
    (C : GeneratedLevelHistoryCharpolyExecFromMirrorSM9b Cell p A P wp W E K T M S H G) :
    ExecComplex :=
  generatedLevelHistoryOperationalCharpolyEvaluationFamilySM9c C C.z

theorem generatedLevelHistoryOperationalCharpolyEvaluationAtSM9bParameterSM9c_eq_SM9b
    (C : GeneratedLevelHistoryCharpolyExecFromMirrorSM9b Cell p A P wp W E K T M S H G) :
    generatedLevelHistoryOperationalCharpolyEvaluationAtSM9bParameterSM9c C =
      C.charpolyEvaluation := by
  exact C.charpolyEvaluation_eq_operative.symm

theorem generatedLevelHistoryOperationalCharpolyEvaluationFamilySM9c_eq_operative
    (C : GeneratedLevelHistoryCharpolyExecFromMirrorSM9b Cell p A P wp W E K T M S H G)
    (z : Schur.SpectralParameter) :
    generatedLevelHistoryOperationalCharpolyEvaluationFamilySM9c C z =
      Schur.operativeCharpolyEvaluation C.matrix z := by
  rfl

theorem generatedLevelHistoryOperationalCharpolyEvaluationAtSM9bParameterSM9c_eq_det_pencil
    (C : GeneratedLevelHistoryCharpolyExecFromMirrorSM9b Cell p A P wp W E K T M S H G) :
    generatedLevelHistoryOperationalCharpolyEvaluationAtSM9bParameterSM9c C =
      Matrix.det C.spectralPencil := by
  calc
    generatedLevelHistoryOperationalCharpolyEvaluationAtSM9bParameterSM9c C =
        C.charpolyEvaluation :=
      generatedLevelHistoryOperationalCharpolyEvaluationAtSM9bParameterSM9c_eq_SM9b C
    _ = Matrix.det C.spectralPencil :=
      C.charpolyEvaluation_eq_det_pencil

structure GeneratedLevelHistoryOperationalCharpolyPolynomialProfileFromSM9b
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf)
    (A : GeneratedApproximantStrong Cell p)
    [Fintype (GeneratedBoundaryIndex A)]
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    (P : GeneratedBoundaryInteriorPartition Cell p A)
    (wp : WeightPolicy)
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W)
    (K : GeneratedInteriorEliminationCarrier Cell p A P wp W E)
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K)
    (M : GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T)
    (S : GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M)
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S)
    (G : GeneratedMultiSchurSM4 Cell p A P wp W E K T M S H) where
  sourceSM9b : GeneratedLevelHistoryCharpolyExecFromMirrorSM9b Cell p A P wp W E K T M S H G
  matrix : Matrix (GeneratedLevelHistoryCharpolyExecIndexSM9b sourceSM9b.sourceSM9aRecheck)
    (GeneratedLevelHistoryCharpolyExecIndexSM9b sourceSM9b.sourceSM9aRecheck) ExecComplex
  matrix_eq_SM9b : matrix = sourceSM9b.matrix
  evaluationFamily : Schur.SpectralParameter → ExecComplex
  evaluationFamily_eq_operative :
    evaluationFamily = fun z => Schur.operativeCharpolyEvaluation matrix z
  sourceParameter : Schur.SpectralParameter
  sourceParameter_eq_SM9b : sourceParameter = sourceSM9b.z
  spectralPencilAtSource : Matrix (GeneratedLevelHistoryCharpolyExecIndexSM9b sourceSM9b.sourceSM9aRecheck)
    (GeneratedLevelHistoryCharpolyExecIndexSM9b sourceSM9b.sourceSM9aRecheck) ExecComplex
  spectralPencilAtSource_eq_SM9b : spectralPencilAtSource = sourceSM9b.spectralPencil
  spectralPencilAtSource_eq_from_matrix : spectralPencilAtSource = Schur.spectralPencil matrix sourceParameter
  determinantAtSource : ExecComplex
  determinantAtSource_eq_matrix_det : determinantAtSource = Matrix.det spectralPencilAtSource
  evaluationAtSource : ExecComplex
  evaluationAtSource_eq_family : evaluationAtSource = evaluationFamily sourceParameter
  evaluationAtSource_eq_SM9b_charpolyEvaluation : evaluationAtSource = sourceSM9b.charpolyEvaluation
  evaluationAtSource_eq_det_pencil : evaluationAtSource = Matrix.det spectralPencilAtSource
  operationalPolynomialProfileStatus : SM9cOperationalPolynomialProfileStatus
  operationalPolynomialProfileStatus_eq :
    operationalPolynomialProfileStatus =
      SM9cOperationalPolynomialProfileStatus.evaluationFamilyClosedFromSM9b
  coefficientExtractionStatus : SM9cCoefficientExtractionStatus
  coefficientExtractionStatus_eq :
    coefficientExtractionStatus =
      SM9cCoefficientExtractionStatus.blockedUntilOperationalCoefficientSource
  nextPhaseStatus : SM9cNextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus = SM9cNextPhaseStatus.coefficientSourceBeforeDiscriminantGate
  noFreeCoefficientTableStatus : SM9cNoFreeCoefficientTableStatus
  noFreeCoefficientTableStatus_eq :
    noFreeCoefficientTableStatus = SM9cNoFreeCoefficientTableStatus.noFreeCoefficientTable
  noFactorizationStatus : SM9cNoFactorizationStatus
  noFactorizationStatus_eq : noFactorizationStatus = SM9cNoFactorizationStatus.noFactorization
  noDiscriminantStatus : SM9cNoDiscriminantStatus
  noDiscriminantStatus_eq : noDiscriminantStatus = SM9cNoDiscriminantStatus.noDiscriminant
  noRootExtractionStatus : SM9cNoRootExtractionStatus
  noRootExtractionStatus_eq : noRootExtractionStatus = SM9cNoRootExtractionStatus.noRootExtraction
  noHeegnerTargetStatus : SM9cNoHeegnerTargetStatus
  noHeegnerTargetStatus_eq : noHeegnerTargetStatus = SM9cNoHeegnerTargetStatus.noHeegnerTarget
  noCMTargetStatus : SM9cNoCMTargetStatus
  noCMTargetStatus_eq : noCMTargetStatus = SM9cNoCMTargetStatus.noCMTarget
  noMatrixInvStatus : SM9cNoMatrixInvStatus
  noMatrixInvStatus_eq : noMatrixInvStatus = SM9cNoMatrixInvStatus.noMatrixInv
  noFieldSimpStatus : SM9cNoFieldSimpStatus
  noFieldSimpStatus_eq : noFieldSimpStatus = SM9cNoFieldSimpStatus.noFieldSimp
  noScalarInvStatus : SM9cNoScalarInvStatus
  noScalarInvStatus_eq : noScalarInvStatus = SM9cNoScalarInvStatus.noScalarInv
  noNoncomputableOperationalSourceStatus : SM9cNoNoncomputableOperationalSourceStatus
  noNoncomputableOperationalSourceStatus_eq :
    noNoncomputableOperationalSourceStatus =
      SM9cNoNoncomputableOperationalSourceStatus.noNoncomputableOperationalSource
  noMatrixCharpolyOracleStatus : SM9cNoMatrixCharpolyOracleStatus
  noMatrixCharpolyOracleStatus_eq :
    noMatrixCharpolyOracleStatus = SM9cNoMatrixCharpolyOracleStatus.noMatrixCharpolyOracle

namespace GeneratedLevelHistoryOperationalCharpolyPolynomialProfileFromSM9b

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {p : ConcretePolicyOf}
variable {A : GeneratedApproximantStrong Cell p}
variable [Fintype (GeneratedBoundaryIndex A)]
variable [Fintype (GeneratedInteriorIndex A)]
variable [DecidableEq (GeneratedInteriorIndex A)]
variable {P : GeneratedBoundaryInteriorPartition Cell p A}
variable {wp : WeightPolicy}
variable {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
variable {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
variable {K : GeneratedInteriorEliminationCarrier Cell p A P wp W E}
variable {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}
variable {M : GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T}
variable {S : GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M}
variable {H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S}
variable {G : GeneratedMultiSchurSM4 Cell p A P wp W E K T M S H}

def fromSM9b
    (C : GeneratedLevelHistoryCharpolyExecFromMirrorSM9b Cell p A P wp W E K T M S H G) :
    GeneratedLevelHistoryOperationalCharpolyPolynomialProfileFromSM9b Cell p A P wp W E K T M S H G where
  sourceSM9b := C
  matrix := C.matrix
  matrix_eq_SM9b := by
    rfl
  evaluationFamily := generatedLevelHistoryOperationalCharpolyEvaluationFamilySM9c C
  evaluationFamily_eq_operative := by
    rfl
  sourceParameter := C.z
  sourceParameter_eq_SM9b := by
    rfl
  spectralPencilAtSource := C.spectralPencil
  spectralPencilAtSource_eq_SM9b := by
    rfl
  spectralPencilAtSource_eq_from_matrix := by
    exact C.spectralPencil_eq_from_matrix
  determinantAtSource := C.charpolyEvaluation
  determinantAtSource_eq_matrix_det := by
    exact C.charpolyEvaluation_eq_det_pencil
  evaluationAtSource := C.charpolyEvaluation
  evaluationAtSource_eq_family := by
    exact C.charpolyEvaluation_eq_operative
  evaluationAtSource_eq_SM9b_charpolyEvaluation := by
    rfl
  evaluationAtSource_eq_det_pencil := by
    exact C.charpolyEvaluation_eq_det_pencil
  operationalPolynomialProfileStatus :=
    SM9cOperationalPolynomialProfileStatus.evaluationFamilyClosedFromSM9b
  operationalPolynomialProfileStatus_eq := by
    rfl
  coefficientExtractionStatus :=
    SM9cCoefficientExtractionStatus.blockedUntilOperationalCoefficientSource
  coefficientExtractionStatus_eq := by
    rfl
  nextPhaseStatus := SM9cNextPhaseStatus.coefficientSourceBeforeDiscriminantGate
  nextPhaseStatus_eq := by
    rfl
  noFreeCoefficientTableStatus := SM9cNoFreeCoefficientTableStatus.noFreeCoefficientTable
  noFreeCoefficientTableStatus_eq := by
    rfl
  noFactorizationStatus := SM9cNoFactorizationStatus.noFactorization
  noFactorizationStatus_eq := by
    rfl
  noDiscriminantStatus := SM9cNoDiscriminantStatus.noDiscriminant
  noDiscriminantStatus_eq := by
    rfl
  noRootExtractionStatus := SM9cNoRootExtractionStatus.noRootExtraction
  noRootExtractionStatus_eq := by
    rfl
  noHeegnerTargetStatus := SM9cNoHeegnerTargetStatus.noHeegnerTarget
  noHeegnerTargetStatus_eq := by
    rfl
  noCMTargetStatus := SM9cNoCMTargetStatus.noCMTarget
  noCMTargetStatus_eq := by
    rfl
  noMatrixInvStatus := SM9cNoMatrixInvStatus.noMatrixInv
  noMatrixInvStatus_eq := by
    rfl
  noFieldSimpStatus := SM9cNoFieldSimpStatus.noFieldSimp
  noFieldSimpStatus_eq := by
    rfl
  noScalarInvStatus := SM9cNoScalarInvStatus.noScalarInv
  noScalarInvStatus_eq := by
    rfl
  noNoncomputableOperationalSourceStatus :=
    SM9cNoNoncomputableOperationalSourceStatus.noNoncomputableOperationalSource
  noNoncomputableOperationalSourceStatus_eq := by
    rfl
  noMatrixCharpolyOracleStatus := SM9cNoMatrixCharpolyOracleStatus.noMatrixCharpolyOracle
  noMatrixCharpolyOracleStatus_eq := by
    rfl

theorem matrix_from_SM9b
    (P9 : GeneratedLevelHistoryOperationalCharpolyPolynomialProfileFromSM9b Cell p A P wp W E K T M S H G) :
    P9.matrix = P9.sourceSM9b.matrix :=
  P9.matrix_eq_SM9b

theorem evaluationFamily_from_operative
    (P9 : GeneratedLevelHistoryOperationalCharpolyPolynomialProfileFromSM9b Cell p A P wp W E K T M S H G) :
    P9.evaluationFamily = fun z => Schur.operativeCharpolyEvaluation P9.matrix z :=
  P9.evaluationFamily_eq_operative

theorem evaluationAtSource_from_SM9b_charpolyEvaluation
    (P9 : GeneratedLevelHistoryOperationalCharpolyPolynomialProfileFromSM9b Cell p A P wp W E K T M S H G) :
    P9.evaluationAtSource = P9.sourceSM9b.charpolyEvaluation :=
  P9.evaluationAtSource_eq_SM9b_charpolyEvaluation

theorem evaluationAtSource_from_det_pencil
    (P9 : GeneratedLevelHistoryOperationalCharpolyPolynomialProfileFromSM9b Cell p A P wp W E K T M S H G) :
    P9.evaluationAtSource = Matrix.det P9.spectralPencilAtSource :=
  P9.evaluationAtSource_eq_det_pencil

theorem coefficientExtraction_blocked
    (P9 : GeneratedLevelHistoryOperationalCharpolyPolynomialProfileFromSM9b Cell p A P wp W E K T M S H G) :
    P9.coefficientExtractionStatus =
      SM9cCoefficientExtractionStatus.blockedUntilOperationalCoefficientSource :=
  P9.coefficientExtractionStatus_eq

theorem no_forbidden_consumers
    (P9 : GeneratedLevelHistoryOperationalCharpolyPolynomialProfileFromSM9b Cell p A P wp W E K T M S H G) :
    P9.noFreeCoefficientTableStatus = SM9cNoFreeCoefficientTableStatus.noFreeCoefficientTable ∧
    P9.noFactorizationStatus = SM9cNoFactorizationStatus.noFactorization ∧
    P9.noDiscriminantStatus = SM9cNoDiscriminantStatus.noDiscriminant ∧
    P9.noRootExtractionStatus = SM9cNoRootExtractionStatus.noRootExtraction ∧
    P9.noHeegnerTargetStatus = SM9cNoHeegnerTargetStatus.noHeegnerTarget ∧
    P9.noCMTargetStatus = SM9cNoCMTargetStatus.noCMTarget ∧
    P9.noMatrixInvStatus = SM9cNoMatrixInvStatus.noMatrixInv ∧
    P9.noFieldSimpStatus = SM9cNoFieldSimpStatus.noFieldSimp ∧
    P9.noScalarInvStatus = SM9cNoScalarInvStatus.noScalarInv ∧
    P9.noNoncomputableOperationalSourceStatus =
      SM9cNoNoncomputableOperationalSourceStatus.noNoncomputableOperationalSource ∧
    P9.noMatrixCharpolyOracleStatus = SM9cNoMatrixCharpolyOracleStatus.noMatrixCharpolyOracle :=
  ⟨P9.noFreeCoefficientTableStatus_eq,
   P9.noFactorizationStatus_eq,
   P9.noDiscriminantStatus_eq,
   P9.noRootExtractionStatus_eq,
   P9.noHeegnerTargetStatus_eq,
   P9.noCMTargetStatus_eq,
   P9.noMatrixInvStatus_eq,
   P9.noFieldSimpStatus_eq,
   P9.noScalarInvStatus_eq,
   P9.noNoncomputableOperationalSourceStatus_eq,
   P9.noMatrixCharpolyOracleStatus_eq⟩

end GeneratedLevelHistoryOperationalCharpolyPolynomialProfileFromSM9b

def regularGeneratedLevelHistoryOperationalCharpolyPolynomialProfileFromSM9b
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9bGeneratedLevelHistoryCharpolyExecLedger b β p regularWeight variableWeight z) :
    GeneratedLevelHistoryOperationalCharpolyPolynomialProfileFromSM9b
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
      L.sourceSM9aRecheckLedger.sourceSM8RecheckLedger.sourceSM8Ledger.sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.regularMultiSchur :=
  GeneratedLevelHistoryOperationalCharpolyPolynomialProfileFromSM9b.fromSM9b L.regularCharpoly

def variableGeneratedLevelHistoryOperationalCharpolyPolynomialProfileFromSM9b
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9bGeneratedLevelHistoryCharpolyExecLedger b β p regularWeight variableWeight z) :
    GeneratedLevelHistoryOperationalCharpolyPolynomialProfileFromSM9b
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
      L.sourceSM9aRecheckLedger.sourceSM8RecheckLedger.sourceSM8Ledger.sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.variableMultiSchur :=
  GeneratedLevelHistoryOperationalCharpolyPolynomialProfileFromSM9b.fromSM9b L.variableCharpoly

structure SM9cGeneratedLevelHistoryOperationalCharpolyPolynomialProfileLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (z : Schur.SpectralParameter) where
  sourceSM9bLedger :
    SM9bGeneratedLevelHistoryCharpolyExecLedger b β p regularWeight variableWeight z
  regularPolynomialProfile :
    GeneratedLevelHistoryOperationalCharpolyPolynomialProfileFromSM9b
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
      sourceSM9bLedger.sourceSM9aRecheckLedger.sourceSM8RecheckLedger.sourceSM8Ledger.sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.regularMultiSchur
  variablePolynomialProfile :
    GeneratedLevelHistoryOperationalCharpolyPolynomialProfileFromSM9b
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
      sourceSM9bLedger.sourceSM9aRecheckLedger.sourceSM8RecheckLedger.sourceSM8Ledger.sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.variableMultiSchur
  regularPolynomialProfile_eq_from_SM9b :
    regularPolynomialProfile = regularGeneratedLevelHistoryOperationalCharpolyPolynomialProfileFromSM9b sourceSM9bLedger
  variablePolynomialProfile_eq_from_SM9b :
    variablePolynomialProfile = variableGeneratedLevelHistoryOperationalCharpolyPolynomialProfileFromSM9b sourceSM9bLedger
  regularEvaluationAtSource_eq_SM9b :
    regularPolynomialProfile.evaluationAtSource = sourceSM9bLedger.regularCharpoly.charpolyEvaluation
  variableEvaluationAtSource_eq_SM9b :
    variablePolynomialProfile.evaluationAtSource = sourceSM9bLedger.variableCharpoly.charpolyEvaluation
  regularEvaluationAtSource_eq_det_pencil :
    regularPolynomialProfile.evaluationAtSource = Matrix.det regularPolynomialProfile.spectralPencilAtSource
  variableEvaluationAtSource_eq_det_pencil :
    variablePolynomialProfile.evaluationAtSource = Matrix.det variablePolynomialProfile.spectralPencilAtSource
  operationalPolynomialProfileStatus : SM9cOperationalPolynomialProfileStatus
  operationalPolynomialProfileStatus_eq :
    operationalPolynomialProfileStatus =
      SM9cOperationalPolynomialProfileStatus.evaluationFamilyClosedFromSM9b
  coefficientExtractionStatus : SM9cCoefficientExtractionStatus
  coefficientExtractionStatus_eq :
    coefficientExtractionStatus =
      SM9cCoefficientExtractionStatus.blockedUntilOperationalCoefficientSource
  nextPhaseStatus : SM9cNextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus = SM9cNextPhaseStatus.coefficientSourceBeforeDiscriminantGate
  noFreeCoefficientTableStatus : SM9cNoFreeCoefficientTableStatus
  noFreeCoefficientTableStatus_eq :
    noFreeCoefficientTableStatus = SM9cNoFreeCoefficientTableStatus.noFreeCoefficientTable
  noFactorizationStatus : SM9cNoFactorizationStatus
  noFactorizationStatus_eq : noFactorizationStatus = SM9cNoFactorizationStatus.noFactorization
  noDiscriminantStatus : SM9cNoDiscriminantStatus
  noDiscriminantStatus_eq : noDiscriminantStatus = SM9cNoDiscriminantStatus.noDiscriminant
  noRootExtractionStatus : SM9cNoRootExtractionStatus
  noRootExtractionStatus_eq : noRootExtractionStatus = SM9cNoRootExtractionStatus.noRootExtraction
  noHeegnerTargetStatus : SM9cNoHeegnerTargetStatus
  noHeegnerTargetStatus_eq : noHeegnerTargetStatus = SM9cNoHeegnerTargetStatus.noHeegnerTarget
  noCMTargetStatus : SM9cNoCMTargetStatus
  noCMTargetStatus_eq : noCMTargetStatus = SM9cNoCMTargetStatus.noCMTarget
  noMatrixInvStatus : SM9cNoMatrixInvStatus
  noMatrixInvStatus_eq : noMatrixInvStatus = SM9cNoMatrixInvStatus.noMatrixInv
  noFieldSimpStatus : SM9cNoFieldSimpStatus
  noFieldSimpStatus_eq : noFieldSimpStatus = SM9cNoFieldSimpStatus.noFieldSimp
  noScalarInvStatus : SM9cNoScalarInvStatus
  noScalarInvStatus_eq : noScalarInvStatus = SM9cNoScalarInvStatus.noScalarInv
  noNoncomputableOperationalSourceStatus : SM9cNoNoncomputableOperationalSourceStatus
  noNoncomputableOperationalSourceStatus_eq :
    noNoncomputableOperationalSourceStatus =
      SM9cNoNoncomputableOperationalSourceStatus.noNoncomputableOperationalSource
  noMatrixCharpolyOracleStatus : SM9cNoMatrixCharpolyOracleStatus
  noMatrixCharpolyOracleStatus_eq :
    noMatrixCharpolyOracleStatus = SM9cNoMatrixCharpolyOracleStatus.noMatrixCharpolyOracle

def sm9cGeneratedLevelHistoryOperationalCharpolyPolynomialProfileLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9bGeneratedLevelHistoryCharpolyExecLedger b β p regularWeight variableWeight z) :
    SM9cGeneratedLevelHistoryOperationalCharpolyPolynomialProfileLedger
      b β p regularWeight variableWeight z :=
  let R := regularGeneratedLevelHistoryOperationalCharpolyPolynomialProfileFromSM9b L
  let V := variableGeneratedLevelHistoryOperationalCharpolyPolynomialProfileFromSM9b L
  { sourceSM9bLedger := L
    regularPolynomialProfile := R
    variablePolynomialProfile := V
    regularPolynomialProfile_eq_from_SM9b := by
      rfl
    variablePolynomialProfile_eq_from_SM9b := by
      rfl
    regularEvaluationAtSource_eq_SM9b := R.evaluationAtSource_eq_SM9b_charpolyEvaluation
    variableEvaluationAtSource_eq_SM9b := V.evaluationAtSource_eq_SM9b_charpolyEvaluation
    regularEvaluationAtSource_eq_det_pencil := R.evaluationAtSource_eq_det_pencil
    variableEvaluationAtSource_eq_det_pencil := V.evaluationAtSource_eq_det_pencil
    operationalPolynomialProfileStatus :=
      SM9cOperationalPolynomialProfileStatus.evaluationFamilyClosedFromSM9b
    operationalPolynomialProfileStatus_eq := by
      rfl
    coefficientExtractionStatus :=
      SM9cCoefficientExtractionStatus.blockedUntilOperationalCoefficientSource
    coefficientExtractionStatus_eq := by
      rfl
    nextPhaseStatus := SM9cNextPhaseStatus.coefficientSourceBeforeDiscriminantGate
    nextPhaseStatus_eq := by
      rfl
    noFreeCoefficientTableStatus := SM9cNoFreeCoefficientTableStatus.noFreeCoefficientTable
    noFreeCoefficientTableStatus_eq := by
      rfl
    noFactorizationStatus := SM9cNoFactorizationStatus.noFactorization
    noFactorizationStatus_eq := by
      rfl
    noDiscriminantStatus := SM9cNoDiscriminantStatus.noDiscriminant
    noDiscriminantStatus_eq := by
      rfl
    noRootExtractionStatus := SM9cNoRootExtractionStatus.noRootExtraction
    noRootExtractionStatus_eq := by
      rfl
    noHeegnerTargetStatus := SM9cNoHeegnerTargetStatus.noHeegnerTarget
    noHeegnerTargetStatus_eq := by
      rfl
    noCMTargetStatus := SM9cNoCMTargetStatus.noCMTarget
    noCMTargetStatus_eq := by
      rfl
    noMatrixInvStatus := SM9cNoMatrixInvStatus.noMatrixInv
    noMatrixInvStatus_eq := by
      rfl
    noFieldSimpStatus := SM9cNoFieldSimpStatus.noFieldSimp
    noFieldSimpStatus_eq := by
      rfl
    noScalarInvStatus := SM9cNoScalarInvStatus.noScalarInv
    noScalarInvStatus_eq := by
      rfl
    noNoncomputableOperationalSourceStatus :=
      SM9cNoNoncomputableOperationalSourceStatus.noNoncomputableOperationalSource
    noNoncomputableOperationalSourceStatus_eq := by
      rfl
    noMatrixCharpolyOracleStatus := SM9cNoMatrixCharpolyOracleStatus.noMatrixCharpolyOracle
    noMatrixCharpolyOracleStatus_eq := by
      rfl }

def sm9cGeneratedLevelHistoryOperationalCharpolyPolynomialProfileLedger_from_SM9aRecheckLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM9aRecheckGeneratedLevelHistoryExecMirrorSourceLedger b β p regularWeight variableWeight)
    (z : Schur.SpectralParameter) :
    SM9cGeneratedLevelHistoryOperationalCharpolyPolynomialProfileLedger
      b β p regularWeight variableWeight z :=
  sm9cGeneratedLevelHistoryOperationalCharpolyPolynomialProfileLedger
    (sm9bGeneratedLevelHistoryCharpolyExecLedger L z)

def sm9cGeneratedLevelHistoryOperationalCharpolyPolynomialProfileLedger_from_accumulatedEntryCancellationLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight)
    (level : Nat)
    (levelIndex : GeneratedLevelHistoryIndexSM6 level)
    (z : Schur.SpectralParameter) :
    SM9cGeneratedLevelHistoryOperationalCharpolyPolynomialProfileLedger
      b β p regularWeight variableWeight z :=
  sm9cGeneratedLevelHistoryOperationalCharpolyPolynomialProfileLedger
    (sm9bGeneratedLevelHistoryCharpolyExecLedger_from_accumulatedEntryCancellationLedger
      L level levelIndex z)

theorem sm9c_regularPolynomialEvaluation_eq_SM9b
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9cGeneratedLevelHistoryOperationalCharpolyPolynomialProfileLedger
      b β p regularWeight variableWeight z) :
    L.regularPolynomialProfile.evaluationAtSource =
      L.sourceSM9bLedger.regularCharpoly.charpolyEvaluation :=
  L.regularEvaluationAtSource_eq_SM9b

theorem sm9c_variablePolynomialEvaluation_eq_SM9b
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9cGeneratedLevelHistoryOperationalCharpolyPolynomialProfileLedger
      b β p regularWeight variableWeight z) :
    L.variablePolynomialProfile.evaluationAtSource =
      L.sourceSM9bLedger.variableCharpoly.charpolyEvaluation :=
  L.variableEvaluationAtSource_eq_SM9b

theorem sm9c_regularEvaluationAtSource_eq_det_pencil
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9cGeneratedLevelHistoryOperationalCharpolyPolynomialProfileLedger
      b β p regularWeight variableWeight z) :
    L.regularPolynomialProfile.evaluationAtSource =
      Matrix.det L.regularPolynomialProfile.spectralPencilAtSource :=
  L.regularEvaluationAtSource_eq_det_pencil

theorem sm9c_variableEvaluationAtSource_eq_det_pencil
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9cGeneratedLevelHistoryOperationalCharpolyPolynomialProfileLedger
      b β p regularWeight variableWeight z) :
    L.variablePolynomialProfile.evaluationAtSource =
      Matrix.det L.variablePolynomialProfile.spectralPencilAtSource :=
  L.variableEvaluationAtSource_eq_det_pencil

theorem sm9c_coefficientExtraction_blocked
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9cGeneratedLevelHistoryOperationalCharpolyPolynomialProfileLedger
      b β p regularWeight variableWeight z) :
    L.coefficientExtractionStatus =
      SM9cCoefficientExtractionStatus.blockedUntilOperationalCoefficientSource :=
  L.coefficientExtractionStatus_eq

theorem sm9c_nextPhase_coefficientSourceBeforeDiscriminantGate
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9cGeneratedLevelHistoryOperationalCharpolyPolynomialProfileLedger
      b β p regularWeight variableWeight z) :
    L.nextPhaseStatus = SM9cNextPhaseStatus.coefficientSourceBeforeDiscriminantGate :=
  L.nextPhaseStatus_eq

theorem sm9c_noFactorization
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9cGeneratedLevelHistoryOperationalCharpolyPolynomialProfileLedger
      b β p regularWeight variableWeight z) :
    L.noFactorizationStatus = SM9cNoFactorizationStatus.noFactorization :=
  L.noFactorizationStatus_eq

theorem sm9c_noDiscriminant
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9cGeneratedLevelHistoryOperationalCharpolyPolynomialProfileLedger
      b β p regularWeight variableWeight z) :
    L.noDiscriminantStatus = SM9cNoDiscriminantStatus.noDiscriminant :=
  L.noDiscriminantStatus_eq

theorem sm9c_noHeegnerTarget
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9cGeneratedLevelHistoryOperationalCharpolyPolynomialProfileLedger
      b β p regularWeight variableWeight z) :
    L.noHeegnerTargetStatus = SM9cNoHeegnerTargetStatus.noHeegnerTarget :=
  L.noHeegnerTargetStatus_eq

end Smoke

end CNNA.PillarA.Arithmetic
