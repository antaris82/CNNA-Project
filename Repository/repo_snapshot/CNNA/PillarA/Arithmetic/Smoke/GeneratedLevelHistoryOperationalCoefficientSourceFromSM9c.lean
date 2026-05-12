import CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryOperationalCharpolyPolynomialProfileFromSM9b

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.DtN

namespace Smoke

universe u

inductive SM9dOperationalCoefficientSourceStatus where
  | blockedMissingOperationalCoefficientRecurrenceSource
  deriving DecidableEq, Repr

inductive SM9dNextPhaseStatus where
  | operationalCoefficientRecurrenceBeforeDiscriminantGate
  deriving DecidableEq, Repr

inductive SM9dNoFreeCoefficientTableStatus where
  | noFreeCoefficientTable
  deriving DecidableEq, Repr

inductive SM9dNoPolynomialSemiringRuntimeStatus where
  | noPolynomialSemiringRuntime
  deriving DecidableEq, Repr

inductive SM9dNoMathlibPolynomialOperationalPathStatus where
  | noMathlibPolynomialOperationalPath
  deriving DecidableEq, Repr

inductive SM9dNoMatrixCharpolyOracleStatus where
  | noMatrixCharpolyOracle
  deriving DecidableEq, Repr

inductive SM9dNoFactorizationStatus where
  | noFactorization
  deriving DecidableEq, Repr

inductive SM9dNoDiscriminantStatus where
  | noDiscriminant
  deriving DecidableEq, Repr

inductive SM9dNoHeegnerTargetStatus where
  | noHeegnerTarget
  deriving DecidableEq, Repr

inductive SM9dNoCMTargetStatus where
  | noCMTarget
  deriving DecidableEq, Repr

inductive SM9dNoMatrixInvStatus where
  | noMatrixInv
  deriving DecidableEq, Repr

inductive SM9dNoFieldSimpStatus where
  | noFieldSimp
  deriving DecidableEq, Repr

inductive SM9dNoScalarInvStatus where
  | noScalarInv
  deriving DecidableEq, Repr

inductive SM9dNoNoncomputableOperationalSourceStatus where
  | noNoncomputableOperationalSource
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

def generatedLevelHistoryOperationalDegreeBoundSM9d
    (P9 : GeneratedLevelHistoryOperationalCharpolyPolynomialProfileFromSM9b
      Cell p A P wp W E K T M S H G) : Nat :=
  P9.sourceSM9b.sourceSM9aRecheck.sourceSM8Recheck.sourceSM8.sourceBridge.sourceSM6Witness.level + 1

structure GeneratedLevelHistoryOperationalCoefficientSourceFromSM9c
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
  sourceSM9c : GeneratedLevelHistoryOperationalCharpolyPolynomialProfileFromSM9b
    Cell p A P wp W E K T M S H G
  matrix : Matrix (GeneratedLevelHistoryCharpolyExecIndexSM9b sourceSM9c.sourceSM9b.sourceSM9aRecheck)
    (GeneratedLevelHistoryCharpolyExecIndexSM9b sourceSM9c.sourceSM9b.sourceSM9aRecheck) ExecComplex
  matrix_eq_SM9c : matrix = sourceSM9c.matrix
  evaluationFamily : Schur.SpectralParameter → ExecComplex
  evaluationFamily_eq_SM9c : evaluationFamily = sourceSM9c.evaluationFamily
  evaluationFamily_eq_operative :
    evaluationFamily = fun z => Schur.operativeCharpolyEvaluation matrix z
  sourceParameter : Schur.SpectralParameter
  sourceParameter_eq_SM9c : sourceParameter = sourceSM9c.sourceParameter
  evaluationAtSource : ExecComplex
  evaluationAtSource_eq_SM9c : evaluationAtSource = sourceSM9c.evaluationAtSource
  evaluationAtSource_eq_family : evaluationAtSource = evaluationFamily sourceParameter
  evaluationAtSource_eq_det_pencil : evaluationAtSource = Matrix.det sourceSM9c.spectralPencilAtSource
  degreeBound : Nat
  degreeBound_eq_levelHistoryLength : degreeBound = generatedLevelHistoryOperationalDegreeBoundSM9d sourceSM9c
  coefficientSourceStatus : SM9dOperationalCoefficientSourceStatus
  coefficientSourceStatus_eq :
    coefficientSourceStatus =
      SM9dOperationalCoefficientSourceStatus.blockedMissingOperationalCoefficientRecurrenceSource
  nextPhaseStatus : SM9dNextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus = SM9dNextPhaseStatus.operationalCoefficientRecurrenceBeforeDiscriminantGate
  noFreeCoefficientTableStatus : SM9dNoFreeCoefficientTableStatus
  noFreeCoefficientTableStatus_eq :
    noFreeCoefficientTableStatus = SM9dNoFreeCoefficientTableStatus.noFreeCoefficientTable
  noPolynomialSemiringRuntimeStatus : SM9dNoPolynomialSemiringRuntimeStatus
  noPolynomialSemiringRuntimeStatus_eq :
    noPolynomialSemiringRuntimeStatus = SM9dNoPolynomialSemiringRuntimeStatus.noPolynomialSemiringRuntime
  noMathlibPolynomialOperationalPathStatus : SM9dNoMathlibPolynomialOperationalPathStatus
  noMathlibPolynomialOperationalPathStatus_eq :
    noMathlibPolynomialOperationalPathStatus =
      SM9dNoMathlibPolynomialOperationalPathStatus.noMathlibPolynomialOperationalPath
  noMatrixCharpolyOracleStatus : SM9dNoMatrixCharpolyOracleStatus
  noMatrixCharpolyOracleStatus_eq :
    noMatrixCharpolyOracleStatus = SM9dNoMatrixCharpolyOracleStatus.noMatrixCharpolyOracle
  noFactorizationStatus : SM9dNoFactorizationStatus
  noFactorizationStatus_eq : noFactorizationStatus = SM9dNoFactorizationStatus.noFactorization
  noDiscriminantStatus : SM9dNoDiscriminantStatus
  noDiscriminantStatus_eq : noDiscriminantStatus = SM9dNoDiscriminantStatus.noDiscriminant
  noHeegnerTargetStatus : SM9dNoHeegnerTargetStatus
  noHeegnerTargetStatus_eq : noHeegnerTargetStatus = SM9dNoHeegnerTargetStatus.noHeegnerTarget
  noCMTargetStatus : SM9dNoCMTargetStatus
  noCMTargetStatus_eq : noCMTargetStatus = SM9dNoCMTargetStatus.noCMTarget
  noMatrixInvStatus : SM9dNoMatrixInvStatus
  noMatrixInvStatus_eq : noMatrixInvStatus = SM9dNoMatrixInvStatus.noMatrixInv
  noFieldSimpStatus : SM9dNoFieldSimpStatus
  noFieldSimpStatus_eq : noFieldSimpStatus = SM9dNoFieldSimpStatus.noFieldSimp
  noScalarInvStatus : SM9dNoScalarInvStatus
  noScalarInvStatus_eq : noScalarInvStatus = SM9dNoScalarInvStatus.noScalarInv
  noNoncomputableOperationalSourceStatus : SM9dNoNoncomputableOperationalSourceStatus
  noNoncomputableOperationalSourceStatus_eq :
    noNoncomputableOperationalSourceStatus =
      SM9dNoNoncomputableOperationalSourceStatus.noNoncomputableOperationalSource

namespace GeneratedLevelHistoryOperationalCoefficientSourceFromSM9c

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

def fromSM9c
    (P9 : GeneratedLevelHistoryOperationalCharpolyPolynomialProfileFromSM9b
      Cell p A P wp W E K T M S H G) :
    GeneratedLevelHistoryOperationalCoefficientSourceFromSM9c Cell p A P wp W E K T M S H G where
  sourceSM9c := P9
  matrix := P9.matrix
  matrix_eq_SM9c := by
    rfl
  evaluationFamily := P9.evaluationFamily
  evaluationFamily_eq_SM9c := by
    rfl
  evaluationFamily_eq_operative := by
    exact P9.evaluationFamily_eq_operative
  sourceParameter := P9.sourceParameter
  sourceParameter_eq_SM9c := by
    rfl
  evaluationAtSource := P9.evaluationAtSource
  evaluationAtSource_eq_SM9c := by
    rfl
  evaluationAtSource_eq_family := by
    exact P9.evaluationAtSource_eq_family
  evaluationAtSource_eq_det_pencil := by
    exact P9.evaluationAtSource_eq_det_pencil
  degreeBound := generatedLevelHistoryOperationalDegreeBoundSM9d P9
  degreeBound_eq_levelHistoryLength := by
    rfl
  coefficientSourceStatus :=
    SM9dOperationalCoefficientSourceStatus.blockedMissingOperationalCoefficientRecurrenceSource
  coefficientSourceStatus_eq := by
    rfl
  nextPhaseStatus := SM9dNextPhaseStatus.operationalCoefficientRecurrenceBeforeDiscriminantGate
  nextPhaseStatus_eq := by
    rfl
  noFreeCoefficientTableStatus := SM9dNoFreeCoefficientTableStatus.noFreeCoefficientTable
  noFreeCoefficientTableStatus_eq := by
    rfl
  noPolynomialSemiringRuntimeStatus := SM9dNoPolynomialSemiringRuntimeStatus.noPolynomialSemiringRuntime
  noPolynomialSemiringRuntimeStatus_eq := by
    rfl
  noMathlibPolynomialOperationalPathStatus :=
    SM9dNoMathlibPolynomialOperationalPathStatus.noMathlibPolynomialOperationalPath
  noMathlibPolynomialOperationalPathStatus_eq := by
    rfl
  noMatrixCharpolyOracleStatus := SM9dNoMatrixCharpolyOracleStatus.noMatrixCharpolyOracle
  noMatrixCharpolyOracleStatus_eq := by
    rfl
  noFactorizationStatus := SM9dNoFactorizationStatus.noFactorization
  noFactorizationStatus_eq := by
    rfl
  noDiscriminantStatus := SM9dNoDiscriminantStatus.noDiscriminant
  noDiscriminantStatus_eq := by
    rfl
  noHeegnerTargetStatus := SM9dNoHeegnerTargetStatus.noHeegnerTarget
  noHeegnerTargetStatus_eq := by
    rfl
  noCMTargetStatus := SM9dNoCMTargetStatus.noCMTarget
  noCMTargetStatus_eq := by
    rfl
  noMatrixInvStatus := SM9dNoMatrixInvStatus.noMatrixInv
  noMatrixInvStatus_eq := by
    rfl
  noFieldSimpStatus := SM9dNoFieldSimpStatus.noFieldSimp
  noFieldSimpStatus_eq := by
    rfl
  noScalarInvStatus := SM9dNoScalarInvStatus.noScalarInv
  noScalarInvStatus_eq := by
    rfl
  noNoncomputableOperationalSourceStatus :=
    SM9dNoNoncomputableOperationalSourceStatus.noNoncomputableOperationalSource
  noNoncomputableOperationalSourceStatus_eq := by
    rfl

theorem matrix_from_SM9c
    (D : GeneratedLevelHistoryOperationalCoefficientSourceFromSM9c Cell p A P wp W E K T M S H G) :
    D.matrix = D.sourceSM9c.matrix :=
  D.matrix_eq_SM9c

theorem evaluationFamily_from_SM9c
    (D : GeneratedLevelHistoryOperationalCoefficientSourceFromSM9c Cell p A P wp W E K T M S H G) :
    D.evaluationFamily = D.sourceSM9c.evaluationFamily :=
  D.evaluationFamily_eq_SM9c

theorem evaluationFamily_from_operative
    (D : GeneratedLevelHistoryOperationalCoefficientSourceFromSM9c Cell p A P wp W E K T M S H G) :
    D.evaluationFamily = fun z => Schur.operativeCharpolyEvaluation D.matrix z :=
  D.evaluationFamily_eq_operative

theorem evaluationAtSource_from_SM9c
    (D : GeneratedLevelHistoryOperationalCoefficientSourceFromSM9c Cell p A P wp W E K T M S H G) :
    D.evaluationAtSource = D.sourceSM9c.evaluationAtSource :=
  D.evaluationAtSource_eq_SM9c

theorem evaluationAtSource_from_det_pencil
    (D : GeneratedLevelHistoryOperationalCoefficientSourceFromSM9c Cell p A P wp W E K T M S H G) :
    D.evaluationAtSource = Matrix.det D.sourceSM9c.spectralPencilAtSource :=
  D.evaluationAtSource_eq_det_pencil

theorem degreeBound_from_levelHistory
    (D : GeneratedLevelHistoryOperationalCoefficientSourceFromSM9c Cell p A P wp W E K T M S H G) :
    D.degreeBound = generatedLevelHistoryOperationalDegreeBoundSM9d D.sourceSM9c :=
  D.degreeBound_eq_levelHistoryLength

theorem blockedMissingOperationalCoefficientRecurrenceSource
    (D : GeneratedLevelHistoryOperationalCoefficientSourceFromSM9c Cell p A P wp W E K T M S H G) :
    D.coefficientSourceStatus =
      SM9dOperationalCoefficientSourceStatus.blockedMissingOperationalCoefficientRecurrenceSource :=
  D.coefficientSourceStatus_eq

theorem no_forbidden_consumers
    (D : GeneratedLevelHistoryOperationalCoefficientSourceFromSM9c Cell p A P wp W E K T M S H G) :
    D.noFreeCoefficientTableStatus = SM9dNoFreeCoefficientTableStatus.noFreeCoefficientTable ∧
    D.noPolynomialSemiringRuntimeStatus = SM9dNoPolynomialSemiringRuntimeStatus.noPolynomialSemiringRuntime ∧
    D.noMathlibPolynomialOperationalPathStatus =
      SM9dNoMathlibPolynomialOperationalPathStatus.noMathlibPolynomialOperationalPath ∧
    D.noMatrixCharpolyOracleStatus = SM9dNoMatrixCharpolyOracleStatus.noMatrixCharpolyOracle ∧
    D.noFactorizationStatus = SM9dNoFactorizationStatus.noFactorization ∧
    D.noDiscriminantStatus = SM9dNoDiscriminantStatus.noDiscriminant ∧
    D.noHeegnerTargetStatus = SM9dNoHeegnerTargetStatus.noHeegnerTarget ∧
    D.noCMTargetStatus = SM9dNoCMTargetStatus.noCMTarget ∧
    D.noMatrixInvStatus = SM9dNoMatrixInvStatus.noMatrixInv ∧
    D.noFieldSimpStatus = SM9dNoFieldSimpStatus.noFieldSimp ∧
    D.noScalarInvStatus = SM9dNoScalarInvStatus.noScalarInv ∧
    D.noNoncomputableOperationalSourceStatus =
      SM9dNoNoncomputableOperationalSourceStatus.noNoncomputableOperationalSource :=
  ⟨D.noFreeCoefficientTableStatus_eq,
   D.noPolynomialSemiringRuntimeStatus_eq,
   D.noMathlibPolynomialOperationalPathStatus_eq,
   D.noMatrixCharpolyOracleStatus_eq,
   D.noFactorizationStatus_eq,
   D.noDiscriminantStatus_eq,
   D.noHeegnerTargetStatus_eq,
   D.noCMTargetStatus_eq,
   D.noMatrixInvStatus_eq,
   D.noFieldSimpStatus_eq,
   D.noScalarInvStatus_eq,
   D.noNoncomputableOperationalSourceStatus_eq⟩

end GeneratedLevelHistoryOperationalCoefficientSourceFromSM9c

def regularGeneratedLevelHistoryOperationalCoefficientSourceFromSM9c
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9cGeneratedLevelHistoryOperationalCharpolyPolynomialProfileLedger
      b β p regularWeight variableWeight z) :
    GeneratedLevelHistoryOperationalCoefficientSourceFromSM9c
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
      L.sourceSM9bLedger.sourceSM9aRecheckLedger.sourceSM8RecheckLedger.sourceSM8Ledger.sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.regularMultiSchur :=
  GeneratedLevelHistoryOperationalCoefficientSourceFromSM9c.fromSM9c L.regularPolynomialProfile

def variableGeneratedLevelHistoryOperationalCoefficientSourceFromSM9c
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9cGeneratedLevelHistoryOperationalCharpolyPolynomialProfileLedger
      b β p regularWeight variableWeight z) :
    GeneratedLevelHistoryOperationalCoefficientSourceFromSM9c
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
      L.sourceSM9bLedger.sourceSM9aRecheckLedger.sourceSM8RecheckLedger.sourceSM8Ledger.sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.variableMultiSchur :=
  GeneratedLevelHistoryOperationalCoefficientSourceFromSM9c.fromSM9c L.variablePolynomialProfile

structure SM9dGeneratedLevelHistoryOperationalCoefficientSourceLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (z : Schur.SpectralParameter) where
  sourceSM9cLedger :
    SM9cGeneratedLevelHistoryOperationalCharpolyPolynomialProfileLedger b β p regularWeight variableWeight z
  regularCoefficientSource :
    GeneratedLevelHistoryOperationalCoefficientSourceFromSM9c
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
      sourceSM9cLedger.sourceSM9bLedger.sourceSM9aRecheckLedger.sourceSM8RecheckLedger.sourceSM8Ledger.sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.regularMultiSchur
  variableCoefficientSource :
    GeneratedLevelHistoryOperationalCoefficientSourceFromSM9c
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
      sourceSM9cLedger.sourceSM9bLedger.sourceSM9aRecheckLedger.sourceSM8RecheckLedger.sourceSM8Ledger.sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.variableMultiSchur
  regularCoefficientSource_eq_from_SM9c :
    regularCoefficientSource = regularGeneratedLevelHistoryOperationalCoefficientSourceFromSM9c sourceSM9cLedger
  variableCoefficientSource_eq_from_SM9c :
    variableCoefficientSource = variableGeneratedLevelHistoryOperationalCoefficientSourceFromSM9c sourceSM9cLedger
  regularEvaluationAtSource_eq_SM9c :
    regularCoefficientSource.evaluationAtSource = sourceSM9cLedger.regularPolynomialProfile.evaluationAtSource
  variableEvaluationAtSource_eq_SM9c :
    variableCoefficientSource.evaluationAtSource = sourceSM9cLedger.variablePolynomialProfile.evaluationAtSource
  regularEvaluationAtSource_eq_det_pencil :
    regularCoefficientSource.evaluationAtSource = Matrix.det regularCoefficientSource.sourceSM9c.spectralPencilAtSource
  variableEvaluationAtSource_eq_det_pencil :
    variableCoefficientSource.evaluationAtSource = Matrix.det variableCoefficientSource.sourceSM9c.spectralPencilAtSource
  coefficientSourceStatus : SM9dOperationalCoefficientSourceStatus
  coefficientSourceStatus_eq :
    coefficientSourceStatus =
      SM9dOperationalCoefficientSourceStatus.blockedMissingOperationalCoefficientRecurrenceSource
  nextPhaseStatus : SM9dNextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus = SM9dNextPhaseStatus.operationalCoefficientRecurrenceBeforeDiscriminantGate
  noFreeCoefficientTableStatus : SM9dNoFreeCoefficientTableStatus
  noFreeCoefficientTableStatus_eq :
    noFreeCoefficientTableStatus = SM9dNoFreeCoefficientTableStatus.noFreeCoefficientTable
  noPolynomialSemiringRuntimeStatus : SM9dNoPolynomialSemiringRuntimeStatus
  noPolynomialSemiringRuntimeStatus_eq :
    noPolynomialSemiringRuntimeStatus = SM9dNoPolynomialSemiringRuntimeStatus.noPolynomialSemiringRuntime
  noMathlibPolynomialOperationalPathStatus : SM9dNoMathlibPolynomialOperationalPathStatus
  noMathlibPolynomialOperationalPathStatus_eq :
    noMathlibPolynomialOperationalPathStatus =
      SM9dNoMathlibPolynomialOperationalPathStatus.noMathlibPolynomialOperationalPath
  noMatrixCharpolyOracleStatus : SM9dNoMatrixCharpolyOracleStatus
  noMatrixCharpolyOracleStatus_eq :
    noMatrixCharpolyOracleStatus = SM9dNoMatrixCharpolyOracleStatus.noMatrixCharpolyOracle
  noFactorizationStatus : SM9dNoFactorizationStatus
  noFactorizationStatus_eq : noFactorizationStatus = SM9dNoFactorizationStatus.noFactorization
  noDiscriminantStatus : SM9dNoDiscriminantStatus
  noDiscriminantStatus_eq : noDiscriminantStatus = SM9dNoDiscriminantStatus.noDiscriminant
  noHeegnerTargetStatus : SM9dNoHeegnerTargetStatus
  noHeegnerTargetStatus_eq : noHeegnerTargetStatus = SM9dNoHeegnerTargetStatus.noHeegnerTarget
  noCMTargetStatus : SM9dNoCMTargetStatus
  noCMTargetStatus_eq : noCMTargetStatus = SM9dNoCMTargetStatus.noCMTarget
  noMatrixInvStatus : SM9dNoMatrixInvStatus
  noMatrixInvStatus_eq : noMatrixInvStatus = SM9dNoMatrixInvStatus.noMatrixInv
  noFieldSimpStatus : SM9dNoFieldSimpStatus
  noFieldSimpStatus_eq : noFieldSimpStatus = SM9dNoFieldSimpStatus.noFieldSimp
  noScalarInvStatus : SM9dNoScalarInvStatus
  noScalarInvStatus_eq : noScalarInvStatus = SM9dNoScalarInvStatus.noScalarInv
  noNoncomputableOperationalSourceStatus : SM9dNoNoncomputableOperationalSourceStatus
  noNoncomputableOperationalSourceStatus_eq :
    noNoncomputableOperationalSourceStatus =
      SM9dNoNoncomputableOperationalSourceStatus.noNoncomputableOperationalSource

def sm9dGeneratedLevelHistoryOperationalCoefficientSourceLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9cGeneratedLevelHistoryOperationalCharpolyPolynomialProfileLedger
      b β p regularWeight variableWeight z) :
    SM9dGeneratedLevelHistoryOperationalCoefficientSourceLedger b β p regularWeight variableWeight z :=
  let R := regularGeneratedLevelHistoryOperationalCoefficientSourceFromSM9c L
  let V := variableGeneratedLevelHistoryOperationalCoefficientSourceFromSM9c L
  { sourceSM9cLedger := L
    regularCoefficientSource := R
    variableCoefficientSource := V
    regularCoefficientSource_eq_from_SM9c := by
      rfl
    variableCoefficientSource_eq_from_SM9c := by
      rfl
    regularEvaluationAtSource_eq_SM9c := R.evaluationAtSource_eq_SM9c
    variableEvaluationAtSource_eq_SM9c := V.evaluationAtSource_eq_SM9c
    regularEvaluationAtSource_eq_det_pencil := R.evaluationAtSource_eq_det_pencil
    variableEvaluationAtSource_eq_det_pencil := V.evaluationAtSource_eq_det_pencil
    coefficientSourceStatus :=
      SM9dOperationalCoefficientSourceStatus.blockedMissingOperationalCoefficientRecurrenceSource
    coefficientSourceStatus_eq := by
      rfl
    nextPhaseStatus := SM9dNextPhaseStatus.operationalCoefficientRecurrenceBeforeDiscriminantGate
    nextPhaseStatus_eq := by
      rfl
    noFreeCoefficientTableStatus := SM9dNoFreeCoefficientTableStatus.noFreeCoefficientTable
    noFreeCoefficientTableStatus_eq := by
      rfl
    noPolynomialSemiringRuntimeStatus := SM9dNoPolynomialSemiringRuntimeStatus.noPolynomialSemiringRuntime
    noPolynomialSemiringRuntimeStatus_eq := by
      rfl
    noMathlibPolynomialOperationalPathStatus :=
      SM9dNoMathlibPolynomialOperationalPathStatus.noMathlibPolynomialOperationalPath
    noMathlibPolynomialOperationalPathStatus_eq := by
      rfl
    noMatrixCharpolyOracleStatus := SM9dNoMatrixCharpolyOracleStatus.noMatrixCharpolyOracle
    noMatrixCharpolyOracleStatus_eq := by
      rfl
    noFactorizationStatus := SM9dNoFactorizationStatus.noFactorization
    noFactorizationStatus_eq := by
      rfl
    noDiscriminantStatus := SM9dNoDiscriminantStatus.noDiscriminant
    noDiscriminantStatus_eq := by
      rfl
    noHeegnerTargetStatus := SM9dNoHeegnerTargetStatus.noHeegnerTarget
    noHeegnerTargetStatus_eq := by
      rfl
    noCMTargetStatus := SM9dNoCMTargetStatus.noCMTarget
    noCMTargetStatus_eq := by
      rfl
    noMatrixInvStatus := SM9dNoMatrixInvStatus.noMatrixInv
    noMatrixInvStatus_eq := by
      rfl
    noFieldSimpStatus := SM9dNoFieldSimpStatus.noFieldSimp
    noFieldSimpStatus_eq := by
      rfl
    noScalarInvStatus := SM9dNoScalarInvStatus.noScalarInv
    noScalarInvStatus_eq := by
      rfl
    noNoncomputableOperationalSourceStatus :=
      SM9dNoNoncomputableOperationalSourceStatus.noNoncomputableOperationalSource
    noNoncomputableOperationalSourceStatus_eq := by
      rfl }

def sm9dGeneratedLevelHistoryOperationalCoefficientSourceLedger_from_SM9aRecheckLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM9aRecheckGeneratedLevelHistoryExecMirrorSourceLedger b β p regularWeight variableWeight)
    (z : Schur.SpectralParameter) :
    SM9dGeneratedLevelHistoryOperationalCoefficientSourceLedger b β p regularWeight variableWeight z :=
  sm9dGeneratedLevelHistoryOperationalCoefficientSourceLedger
    (sm9cGeneratedLevelHistoryOperationalCharpolyPolynomialProfileLedger_from_SM9aRecheckLedger L z)

def sm9dGeneratedLevelHistoryOperationalCoefficientSourceLedger_from_accumulatedEntryCancellationLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight)
    (level : Nat)
    (levelIndex : GeneratedLevelHistoryIndexSM6 level)
    (z : Schur.SpectralParameter) :
    SM9dGeneratedLevelHistoryOperationalCoefficientSourceLedger b β p regularWeight variableWeight z :=
  sm9dGeneratedLevelHistoryOperationalCoefficientSourceLedger
    (sm9cGeneratedLevelHistoryOperationalCharpolyPolynomialProfileLedger_from_accumulatedEntryCancellationLedger
      L level levelIndex z)

theorem sm9d_regularEvaluationAtSource_eq_SM9c
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9dGeneratedLevelHistoryOperationalCoefficientSourceLedger
      b β p regularWeight variableWeight z) :
    L.regularCoefficientSource.evaluationAtSource =
      L.sourceSM9cLedger.regularPolynomialProfile.evaluationAtSource :=
  L.regularEvaluationAtSource_eq_SM9c

theorem sm9d_variableEvaluationAtSource_eq_SM9c
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9dGeneratedLevelHistoryOperationalCoefficientSourceLedger
      b β p regularWeight variableWeight z) :
    L.variableCoefficientSource.evaluationAtSource =
      L.sourceSM9cLedger.variablePolynomialProfile.evaluationAtSource :=
  L.variableEvaluationAtSource_eq_SM9c

theorem sm9d_regularEvaluationAtSource_eq_det_pencil
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9dGeneratedLevelHistoryOperationalCoefficientSourceLedger
      b β p regularWeight variableWeight z) :
    L.regularCoefficientSource.evaluationAtSource =
      Matrix.det L.regularCoefficientSource.sourceSM9c.spectralPencilAtSource :=
  L.regularEvaluationAtSource_eq_det_pencil

theorem sm9d_variableEvaluationAtSource_eq_det_pencil
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9dGeneratedLevelHistoryOperationalCoefficientSourceLedger
      b β p regularWeight variableWeight z) :
    L.variableCoefficientSource.evaluationAtSource =
      Matrix.det L.variableCoefficientSource.sourceSM9c.spectralPencilAtSource :=
  L.variableEvaluationAtSource_eq_det_pencil

theorem sm9d_blockedMissingOperationalCoefficientRecurrenceSource
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9dGeneratedLevelHistoryOperationalCoefficientSourceLedger
      b β p regularWeight variableWeight z) :
    L.coefficientSourceStatus =
      SM9dOperationalCoefficientSourceStatus.blockedMissingOperationalCoefficientRecurrenceSource :=
  L.coefficientSourceStatus_eq

theorem sm9d_nextPhase_operationalCoefficientRecurrenceBeforeDiscriminantGate
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9dGeneratedLevelHistoryOperationalCoefficientSourceLedger
      b β p regularWeight variableWeight z) :
    L.nextPhaseStatus = SM9dNextPhaseStatus.operationalCoefficientRecurrenceBeforeDiscriminantGate :=
  L.nextPhaseStatus_eq

theorem sm9d_noFactorization
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9dGeneratedLevelHistoryOperationalCoefficientSourceLedger
      b β p regularWeight variableWeight z) :
    L.noFactorizationStatus = SM9dNoFactorizationStatus.noFactorization :=
  L.noFactorizationStatus_eq

theorem sm9d_noDiscriminant
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9dGeneratedLevelHistoryOperationalCoefficientSourceLedger
      b β p regularWeight variableWeight z) :
    L.noDiscriminantStatus = SM9dNoDiscriminantStatus.noDiscriminant :=
  L.noDiscriminantStatus_eq

theorem sm9d_noHeegnerTarget
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9dGeneratedLevelHistoryOperationalCoefficientSourceLedger
      b β p regularWeight variableWeight z) :
    L.noHeegnerTargetStatus = SM9dNoHeegnerTargetStatus.noHeegnerTarget :=
  L.noHeegnerTargetStatus_eq

end Smoke

end CNNA.PillarA.Arithmetic
