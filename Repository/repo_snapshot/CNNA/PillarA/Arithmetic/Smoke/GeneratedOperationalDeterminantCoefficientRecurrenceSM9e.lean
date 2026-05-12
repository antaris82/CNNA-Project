import CNNA.PillarA.Arithmetic.Smoke.GeneratedLevelHistoryOperationalCoefficientSourceFromSM9c

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.DtN

namespace Smoke

universe u v

inductive SM9eOperationalCoefficientRecurrenceStatus where
  | operationalDeterminantCoefficientRecurrenceClosed
  deriving DecidableEq, Repr

inductive SM9eDeterminantBridgeStatus where
  | determinantBridgeDeferredToSM9f
  deriving DecidableEq, Repr

inductive SM9eNextPhaseStatus where
  | determinantEvaluationBridgeBeforeDiscriminantGate
  deriving DecidableEq, Repr

inductive SM9eNoFreeCoefficientTableStatus where
  | noFreeCoefficientTable
  deriving DecidableEq, Repr

inductive SM9eNoPolynomialSemiringRuntimeStatus where
  | noPolynomialSemiringRuntime
  deriving DecidableEq, Repr

inductive SM9eNoMathlibPolynomialOperationalPathStatus where
  | noMathlibPolynomialOperationalPath
  deriving DecidableEq, Repr

inductive SM9eNoMatrixCharpolyOracleStatus where
  | noMatrixCharpolyOracle
  deriving DecidableEq, Repr

inductive SM9eNoFactorizationStatus where
  | noFactorization
  deriving DecidableEq, Repr

inductive SM9eNoDiscriminantStatus where
  | noDiscriminant
  deriving DecidableEq, Repr

inductive SM9eNoHeegnerTargetStatus where
  | noHeegnerTarget
  deriving DecidableEq, Repr

inductive SM9eNoCMTargetStatus where
  | noCMTarget
  deriving DecidableEq, Repr

inductive SM9eNoMatrixInvStatus where
  | noMatrixInv
  deriving DecidableEq, Repr

inductive SM9eNoFieldSimpStatus where
  | noFieldSimp
  deriving DecidableEq, Repr

inductive SM9eNoScalarInvStatus where
  | noScalarInv
  deriving DecidableEq, Repr

inductive SM9eNoNoncomputableOperationalSourceStatus where
  | noNoncomputableOperationalSource
  deriving DecidableEq, Repr

structure OperationalBoundedPolynomialSM9e (degreeBound : Nat) where
  coefficient : Fin (degreeBound + 1) → ExecComplex

namespace OperationalBoundedPolynomialSM9e

variable {degreeBound : Nat}

def coefficientAt
    (P : OperationalBoundedPolynomialSM9e degreeBound) (n : Nat) : ExecComplex :=
  if h : n < degreeBound + 1 then P.coefficient ⟨n, h⟩ else 0

def hornerAux
    (P : OperationalBoundedPolynomialSM9e degreeBound)
    (z : Schur.SpectralParameter) : Nat → ExecComplex
  | 0 => coefficientAt P 0
  | n + 1 => coefficientAt P (n + 1) + Schur.spectralParameterExec z * hornerAux P z n

def eval
    (P : OperationalBoundedPolynomialSM9e degreeBound)
    (z : Schur.SpectralParameter) : ExecComplex :=
  hornerAux P z degreeBound

def zero (degreeBound : Nat) : OperationalBoundedPolynomialSM9e degreeBound where
  coefficient := fun _ => 0

def one (degreeBound : Nat) : OperationalBoundedPolynomialSM9e degreeBound where
  coefficient := fun n => if n.val = 0 then 1 else 0

def const (degreeBound : Nat) (c : ExecComplex) : OperationalBoundedPolynomialSM9e degreeBound where
  coefficient := fun n => if n.val = 0 then c else 0

def linear (degreeBound : Nat) (c0 c1 : ExecComplex) : OperationalBoundedPolynomialSM9e degreeBound where
  coefficient := fun n =>
    if n.val = 0 then c0 else if n.val = 1 then c1 else 0

def add
    (P Q : OperationalBoundedPolynomialSM9e degreeBound) :
    OperationalBoundedPolynomialSM9e degreeBound where
  coefficient := fun n => P.coefficient n + Q.coefficient n

def neg
    (P : OperationalBoundedPolynomialSM9e degreeBound) :
    OperationalBoundedPolynomialSM9e degreeBound where
  coefficient := fun n => -P.coefficient n

def sub
    (P Q : OperationalBoundedPolynomialSM9e degreeBound) :
    OperationalBoundedPolynomialSM9e degreeBound :=
  add P (neg Q)

def scale
    (c : ExecComplex) (P : OperationalBoundedPolynomialSM9e degreeBound) :
    OperationalBoundedPolynomialSM9e degreeBound where
  coefficient := fun n => c * P.coefficient n

def convolutionCoeffAux
    (P Q : OperationalBoundedPolynomialSM9e degreeBound)
    (n : Nat) : Nat → ExecComplex
  | 0 => coefficientAt P 0 * coefficientAt Q n
  | k + 1 =>
      convolutionCoeffAux P Q n k +
        coefficientAt P (k + 1) * coefficientAt Q (n - (k + 1))

def convolutionCoeff
    (P Q : OperationalBoundedPolynomialSM9e degreeBound) (n : Nat) : ExecComplex :=
  convolutionCoeffAux P Q n n

def boundedMul
    (P Q : OperationalBoundedPolynomialSM9e degreeBound) :
    OperationalBoundedPolynomialSM9e degreeBound where
  coefficient := fun n => convolutionCoeff P Q n.val

def listProduct
    {α : Type v} (degreeBound : Nat) (xs : List α)
    (f : α → OperationalBoundedPolynomialSM9e degreeBound) :
    OperationalBoundedPolynomialSM9e degreeBound :=
  xs.foldl (fun acc x => boundedMul acc (f x)) (one degreeBound)

theorem eval_eq_horner
    (P : OperationalBoundedPolynomialSM9e degreeBound)
    (z : Schur.SpectralParameter) :
    eval P z = hornerAux P z degreeBound := by
  rfl

end OperationalBoundedPolynomialSM9e

def operationalLinearPencilEntryPolynomialSM9e
    {ι : Type v} [DecidableEq ι]
    (degreeBound : Nat) (A : Matrix ι ι ExecComplex) (i j : ι) :
    OperationalBoundedPolynomialSM9e degreeBound :=
  OperationalBoundedPolynomialSM9e.linear degreeBound (-(A i j)) (if i = j then 1 else 0)

def operationalSignedPolynomialSM9e
    {degreeBound : Nat} (positive : Bool)
    (P : OperationalBoundedPolynomialSM9e degreeBound) :
    OperationalBoundedPolynomialSM9e degreeBound :=
  if positive then P else OperationalBoundedPolynomialSM9e.neg P

def operationalDeterminantColumnExpansionAuxSM9e
    {ι : Type v} [DecidableEq ι]
    (degreeBound : Nat) (A : Matrix ι ι ExecComplex)
    (minorDet : List ι → List ι → OperationalBoundedPolynomialSM9e degreeBound)
    (row : ι) (rowsTail leftRev : List ι) (positive : Bool) :
    List ι → OperationalBoundedPolynomialSM9e degreeBound
  | [] => OperationalBoundedPolynomialSM9e.zero degreeBound
  | col :: right =>
      let minorCols := leftRev.reverse ++ right
      let entryPolynomial := operationalLinearPencilEntryPolynomialSM9e degreeBound A row col
      let minorPolynomial := minorDet rowsTail minorCols
      let signedTerm :=
        operationalSignedPolynomialSM9e positive
          (OperationalBoundedPolynomialSM9e.boundedMul entryPolynomial minorPolynomial)
      OperationalBoundedPolynomialSM9e.add signedTerm
        (operationalDeterminantColumnExpansionAuxSM9e degreeBound A minorDet row rowsTail
          (col :: leftRev) (Bool.not positive) right)

def operationalDeterminantCoefficientRecurrenceFromRowsColsFuelSM9e
    {ι : Type v} [DecidableEq ι]
    (degreeBound : Nat) (A : Matrix ι ι ExecComplex) :
    Nat → List ι → List ι → OperationalBoundedPolynomialSM9e degreeBound
  | 0, rows, cols =>
      if rows.isEmpty && cols.isEmpty then
        OperationalBoundedPolynomialSM9e.one degreeBound
      else
        OperationalBoundedPolynomialSM9e.zero degreeBound
  | _fuel + 1, [], cols =>
      if cols.isEmpty then
        OperationalBoundedPolynomialSM9e.one degreeBound
      else
        OperationalBoundedPolynomialSM9e.zero degreeBound
  | fuel + 1, row :: rowsTail, cols =>
      operationalDeterminantColumnExpansionAuxSM9e degreeBound A
        (fun minorRows minorCols =>
          operationalDeterminantCoefficientRecurrenceFromRowsColsFuelSM9e
            degreeBound A fuel minorRows minorCols)
        row rowsTail [] true cols

def operationalDeterminantCoefficientRecurrenceFromOrderSM9e
    {ι : Type v} [DecidableEq ι]
    (degreeBound : Nat) (A : Matrix ι ι ExecComplex) (indexOrder : List ι) :
    OperationalBoundedPolynomialSM9e degreeBound :=
  operationalDeterminantCoefficientRecurrenceFromRowsColsFuelSM9e
    degreeBound A indexOrder.length indexOrder indexOrder

def operationalDeterminantCoefficientRecurrenceSM9e
    {n : Nat} (degreeBound : Nat) (A : Matrix (Fin n) (Fin n) ExecComplex) :
    OperationalBoundedPolynomialSM9e degreeBound :=
  operationalDeterminantCoefficientRecurrenceFromOrderSM9e degreeBound A (List.finRange n)

def operationalDeterminantCoefficientEvaluationSM9e
    {n : Nat} (degreeBound : Nat) (A : Matrix (Fin n) (Fin n) ExecComplex)
    (z : Schur.SpectralParameter) : ExecComplex :=
  OperationalBoundedPolynomialSM9e.eval
    (operationalDeterminantCoefficientRecurrenceSM9e degreeBound A) z

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

structure GeneratedOperationalDeterminantCoefficientRecurrenceSM9e
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
  sourceSM9d : GeneratedLevelHistoryOperationalCoefficientSourceFromSM9c
    Cell p A P wp W E K T M S H G
  degreeBound : Nat
  degreeBound_eq_SM9d : degreeBound = sourceSM9d.degreeBound
  coefficientPolynomial : OperationalBoundedPolynomialSM9e degreeBound
  coefficients_source_eq_linearPencil :
    coefficientPolynomial =
      operationalDeterminantCoefficientRecurrenceSM9e degreeBound sourceSM9d.matrix
  evaluationFromCoefficients : Schur.SpectralParameter → ExecComplex
  evaluationFromCoefficients_eq_eval :
    evaluationFromCoefficients = fun z =>
      OperationalBoundedPolynomialSM9e.eval coefficientPolynomial z
  evaluationAtSource : ExecComplex
  evaluationAtSource_eq_coefficients :
    evaluationAtSource = evaluationFromCoefficients sourceSM9d.sourceParameter
  recurrenceStatus : SM9eOperationalCoefficientRecurrenceStatus
  recurrenceStatus_eq :
    recurrenceStatus =
      SM9eOperationalCoefficientRecurrenceStatus.operationalDeterminantCoefficientRecurrenceClosed
  determinantBridgeStatus : SM9eDeterminantBridgeStatus
  determinantBridgeStatus_eq :
    determinantBridgeStatus = SM9eDeterminantBridgeStatus.determinantBridgeDeferredToSM9f
  nextPhaseStatus : SM9eNextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus = SM9eNextPhaseStatus.determinantEvaluationBridgeBeforeDiscriminantGate
  noFreeCoefficientTableStatus : SM9eNoFreeCoefficientTableStatus
  noFreeCoefficientTableStatus_eq :
    noFreeCoefficientTableStatus = SM9eNoFreeCoefficientTableStatus.noFreeCoefficientTable
  noPolynomialSemiringRuntimeStatus : SM9eNoPolynomialSemiringRuntimeStatus
  noPolynomialSemiringRuntimeStatus_eq :
    noPolynomialSemiringRuntimeStatus = SM9eNoPolynomialSemiringRuntimeStatus.noPolynomialSemiringRuntime
  noMathlibPolynomialOperationalPathStatus : SM9eNoMathlibPolynomialOperationalPathStatus
  noMathlibPolynomialOperationalPathStatus_eq :
    noMathlibPolynomialOperationalPathStatus =
      SM9eNoMathlibPolynomialOperationalPathStatus.noMathlibPolynomialOperationalPath
  noMatrixCharpolyOracleStatus : SM9eNoMatrixCharpolyOracleStatus
  noMatrixCharpolyOracleStatus_eq :
    noMatrixCharpolyOracleStatus = SM9eNoMatrixCharpolyOracleStatus.noMatrixCharpolyOracle
  noFactorizationStatus : SM9eNoFactorizationStatus
  noFactorizationStatus_eq : noFactorizationStatus = SM9eNoFactorizationStatus.noFactorization
  noDiscriminantStatus : SM9eNoDiscriminantStatus
  noDiscriminantStatus_eq : noDiscriminantStatus = SM9eNoDiscriminantStatus.noDiscriminant
  noHeegnerTargetStatus : SM9eNoHeegnerTargetStatus
  noHeegnerTargetStatus_eq : noHeegnerTargetStatus = SM9eNoHeegnerTargetStatus.noHeegnerTarget
  noCMTargetStatus : SM9eNoCMTargetStatus
  noCMTargetStatus_eq : noCMTargetStatus = SM9eNoCMTargetStatus.noCMTarget
  noMatrixInvStatus : SM9eNoMatrixInvStatus
  noMatrixInvStatus_eq : noMatrixInvStatus = SM9eNoMatrixInvStatus.noMatrixInv
  noFieldSimpStatus : SM9eNoFieldSimpStatus
  noFieldSimpStatus_eq : noFieldSimpStatus = SM9eNoFieldSimpStatus.noFieldSimp
  noScalarInvStatus : SM9eNoScalarInvStatus
  noScalarInvStatus_eq : noScalarInvStatus = SM9eNoScalarInvStatus.noScalarInv
  noNoncomputableOperationalSourceStatus : SM9eNoNoncomputableOperationalSourceStatus
  noNoncomputableOperationalSourceStatus_eq :
    noNoncomputableOperationalSourceStatus =
      SM9eNoNoncomputableOperationalSourceStatus.noNoncomputableOperationalSource

namespace GeneratedOperationalDeterminantCoefficientRecurrenceSM9e

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

def fromSM9d
    (D : GeneratedLevelHistoryOperationalCoefficientSourceFromSM9c Cell p A P wp W E K T M S H G) :
    GeneratedOperationalDeterminantCoefficientRecurrenceSM9e Cell p A P wp W E K T M S H G :=
  let degreeBound := D.degreeBound
  let coefficientPolynomial := operationalDeterminantCoefficientRecurrenceSM9e degreeBound D.matrix
  { sourceSM9d := D
    degreeBound := degreeBound
    degreeBound_eq_SM9d := by
      rfl
    coefficientPolynomial := coefficientPolynomial
    coefficients_source_eq_linearPencil := by
      rfl
    evaluationFromCoefficients := fun z =>
      OperationalBoundedPolynomialSM9e.eval coefficientPolynomial z
    evaluationFromCoefficients_eq_eval := by
      rfl
    evaluationAtSource :=
      OperationalBoundedPolynomialSM9e.eval coefficientPolynomial D.sourceParameter
    evaluationAtSource_eq_coefficients := by
      rfl
    recurrenceStatus :=
      SM9eOperationalCoefficientRecurrenceStatus.operationalDeterminantCoefficientRecurrenceClosed
    recurrenceStatus_eq := by
      rfl
    determinantBridgeStatus := SM9eDeterminantBridgeStatus.determinantBridgeDeferredToSM9f
    determinantBridgeStatus_eq := by
      rfl
    nextPhaseStatus := SM9eNextPhaseStatus.determinantEvaluationBridgeBeforeDiscriminantGate
    nextPhaseStatus_eq := by
      rfl
    noFreeCoefficientTableStatus := SM9eNoFreeCoefficientTableStatus.noFreeCoefficientTable
    noFreeCoefficientTableStatus_eq := by
      rfl
    noPolynomialSemiringRuntimeStatus := SM9eNoPolynomialSemiringRuntimeStatus.noPolynomialSemiringRuntime
    noPolynomialSemiringRuntimeStatus_eq := by
      rfl
    noMathlibPolynomialOperationalPathStatus :=
      SM9eNoMathlibPolynomialOperationalPathStatus.noMathlibPolynomialOperationalPath
    noMathlibPolynomialOperationalPathStatus_eq := by
      rfl
    noMatrixCharpolyOracleStatus := SM9eNoMatrixCharpolyOracleStatus.noMatrixCharpolyOracle
    noMatrixCharpolyOracleStatus_eq := by
      rfl
    noFactorizationStatus := SM9eNoFactorizationStatus.noFactorization
    noFactorizationStatus_eq := by
      rfl
    noDiscriminantStatus := SM9eNoDiscriminantStatus.noDiscriminant
    noDiscriminantStatus_eq := by
      rfl
    noHeegnerTargetStatus := SM9eNoHeegnerTargetStatus.noHeegnerTarget
    noHeegnerTargetStatus_eq := by
      rfl
    noCMTargetStatus := SM9eNoCMTargetStatus.noCMTarget
    noCMTargetStatus_eq := by
      rfl
    noMatrixInvStatus := SM9eNoMatrixInvStatus.noMatrixInv
    noMatrixInvStatus_eq := by
      rfl
    noFieldSimpStatus := SM9eNoFieldSimpStatus.noFieldSimp
    noFieldSimpStatus_eq := by
      rfl
    noScalarInvStatus := SM9eNoScalarInvStatus.noScalarInv
    noScalarInvStatus_eq := by
      rfl
    noNoncomputableOperationalSourceStatus :=
      SM9eNoNoncomputableOperationalSourceStatus.noNoncomputableOperationalSource
    noNoncomputableOperationalSourceStatus_eq := by
      rfl }

theorem degreeBound_from_SM9d
    (R : GeneratedOperationalDeterminantCoefficientRecurrenceSM9e Cell p A P wp W E K T M S H G) :
    R.degreeBound = R.sourceSM9d.degreeBound :=
  R.degreeBound_eq_SM9d

theorem coefficients_from_linearPencil
    (R : GeneratedOperationalDeterminantCoefficientRecurrenceSM9e Cell p A P wp W E K T M S H G) :
    R.coefficientPolynomial =
      operationalDeterminantCoefficientRecurrenceSM9e R.degreeBound R.sourceSM9d.matrix :=
  R.coefficients_source_eq_linearPencil

theorem evaluationFromCoefficients_from_eval
    (R : GeneratedOperationalDeterminantCoefficientRecurrenceSM9e Cell p A P wp W E K T M S H G) :
    R.evaluationFromCoefficients = fun z =>
      OperationalBoundedPolynomialSM9e.eval R.coefficientPolynomial z :=
  R.evaluationFromCoefficients_eq_eval

theorem evaluationAtSource_from_coefficients
    (R : GeneratedOperationalDeterminantCoefficientRecurrenceSM9e Cell p A P wp W E K T M S H G) :
    R.evaluationAtSource = R.evaluationFromCoefficients R.sourceSM9d.sourceParameter :=
  R.evaluationAtSource_eq_coefficients

theorem determinantBridge_deferred_to_SM9f
    (R : GeneratedOperationalDeterminantCoefficientRecurrenceSM9e Cell p A P wp W E K T M S H G) :
    R.determinantBridgeStatus = SM9eDeterminantBridgeStatus.determinantBridgeDeferredToSM9f :=
  R.determinantBridgeStatus_eq

theorem no_forbidden_consumers
    (R : GeneratedOperationalDeterminantCoefficientRecurrenceSM9e Cell p A P wp W E K T M S H G) :
    R.noFreeCoefficientTableStatus = SM9eNoFreeCoefficientTableStatus.noFreeCoefficientTable ∧
    R.noPolynomialSemiringRuntimeStatus = SM9eNoPolynomialSemiringRuntimeStatus.noPolynomialSemiringRuntime ∧
    R.noMathlibPolynomialOperationalPathStatus =
      SM9eNoMathlibPolynomialOperationalPathStatus.noMathlibPolynomialOperationalPath ∧
    R.noMatrixCharpolyOracleStatus = SM9eNoMatrixCharpolyOracleStatus.noMatrixCharpolyOracle ∧
    R.noFactorizationStatus = SM9eNoFactorizationStatus.noFactorization ∧
    R.noDiscriminantStatus = SM9eNoDiscriminantStatus.noDiscriminant ∧
    R.noHeegnerTargetStatus = SM9eNoHeegnerTargetStatus.noHeegnerTarget ∧
    R.noCMTargetStatus = SM9eNoCMTargetStatus.noCMTarget ∧
    R.noMatrixInvStatus = SM9eNoMatrixInvStatus.noMatrixInv ∧
    R.noFieldSimpStatus = SM9eNoFieldSimpStatus.noFieldSimp ∧
    R.noScalarInvStatus = SM9eNoScalarInvStatus.noScalarInv ∧
    R.noNoncomputableOperationalSourceStatus =
      SM9eNoNoncomputableOperationalSourceStatus.noNoncomputableOperationalSource :=
  ⟨R.noFreeCoefficientTableStatus_eq,
   R.noPolynomialSemiringRuntimeStatus_eq,
   R.noMathlibPolynomialOperationalPathStatus_eq,
   R.noMatrixCharpolyOracleStatus_eq,
   R.noFactorizationStatus_eq,
   R.noDiscriminantStatus_eq,
   R.noHeegnerTargetStatus_eq,
   R.noCMTargetStatus_eq,
   R.noMatrixInvStatus_eq,
   R.noFieldSimpStatus_eq,
   R.noScalarInvStatus_eq,
   R.noNoncomputableOperationalSourceStatus_eq⟩

end GeneratedOperationalDeterminantCoefficientRecurrenceSM9e

def regularGeneratedOperationalDeterminantCoefficientRecurrenceSM9e
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9dGeneratedLevelHistoryOperationalCoefficientSourceLedger
      b β p regularWeight variableWeight z) :
    GeneratedOperationalDeterminantCoefficientRecurrenceSM9e
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
      L.sourceSM9cLedger.sourceSM9bLedger.sourceSM9aRecheckLedger.sourceSM8RecheckLedger.sourceSM8Ledger.sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.regularMultiSchur :=
  GeneratedOperationalDeterminantCoefficientRecurrenceSM9e.fromSM9d L.regularCoefficientSource

def variableGeneratedOperationalDeterminantCoefficientRecurrenceSM9e
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9dGeneratedLevelHistoryOperationalCoefficientSourceLedger
      b β p regularWeight variableWeight z) :
    GeneratedOperationalDeterminantCoefficientRecurrenceSM9e
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
      L.sourceSM9cLedger.sourceSM9bLedger.sourceSM9aRecheckLedger.sourceSM8RecheckLedger.sourceSM8Ledger.sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.variableMultiSchur :=
  GeneratedOperationalDeterminantCoefficientRecurrenceSM9e.fromSM9d L.variableCoefficientSource

structure SM9eGeneratedOperationalDeterminantCoefficientRecurrenceLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (z : Schur.SpectralParameter) where
  sourceSM9dLedger :
    SM9dGeneratedLevelHistoryOperationalCoefficientSourceLedger b β p regularWeight variableWeight z
  regularRecurrence :
    GeneratedOperationalDeterminantCoefficientRecurrenceSM9e
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
      sourceSM9dLedger.sourceSM9cLedger.sourceSM9bLedger.sourceSM9aRecheckLedger.sourceSM8RecheckLedger.sourceSM8Ledger.sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.regularMultiSchur
  variableRecurrence :
    GeneratedOperationalDeterminantCoefficientRecurrenceSM9e
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
      sourceSM9dLedger.sourceSM9cLedger.sourceSM9bLedger.sourceSM9aRecheckLedger.sourceSM8RecheckLedger.sourceSM8Ledger.sourceSM7BridgeRecheckLedger.sourceSM6aLedger.sourceSM6Ledger.sourceSM5Ledger.sourceSM4Ledger.variableMultiSchur
  regularRecurrence_eq_from_SM9d :
    regularRecurrence = regularGeneratedOperationalDeterminantCoefficientRecurrenceSM9e sourceSM9dLedger
  variableRecurrence_eq_from_SM9d :
    variableRecurrence = variableGeneratedOperationalDeterminantCoefficientRecurrenceSM9e sourceSM9dLedger
  regularDegreeBound_eq_SM9d :
    regularRecurrence.degreeBound = sourceSM9dLedger.regularCoefficientSource.degreeBound
  variableDegreeBound_eq_SM9d :
    variableRecurrence.degreeBound = sourceSM9dLedger.variableCoefficientSource.degreeBound
  regularCoefficients_source_eq_linearPencil :
    regularRecurrence.coefficientPolynomial =
      operationalDeterminantCoefficientRecurrenceSM9e
        regularRecurrence.degreeBound regularRecurrence.sourceSM9d.matrix
  variableCoefficients_source_eq_linearPencil :
    variableRecurrence.coefficientPolynomial =
      operationalDeterminantCoefficientRecurrenceSM9e
        variableRecurrence.degreeBound variableRecurrence.sourceSM9d.matrix
  regularEvaluationAtSource_eq_coefficients :
    regularRecurrence.evaluationAtSource =
      regularRecurrence.evaluationFromCoefficients regularRecurrence.sourceSM9d.sourceParameter
  variableEvaluationAtSource_eq_coefficients :
    variableRecurrence.evaluationAtSource =
      variableRecurrence.evaluationFromCoefficients variableRecurrence.sourceSM9d.sourceParameter
  determinantBridgeStatus : SM9eDeterminantBridgeStatus
  determinantBridgeStatus_eq :
    determinantBridgeStatus = SM9eDeterminantBridgeStatus.determinantBridgeDeferredToSM9f
  nextPhaseStatus : SM9eNextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus = SM9eNextPhaseStatus.determinantEvaluationBridgeBeforeDiscriminantGate
  noFreeCoefficientTableStatus : SM9eNoFreeCoefficientTableStatus
  noFreeCoefficientTableStatus_eq :
    noFreeCoefficientTableStatus = SM9eNoFreeCoefficientTableStatus.noFreeCoefficientTable
  noPolynomialSemiringRuntimeStatus : SM9eNoPolynomialSemiringRuntimeStatus
  noPolynomialSemiringRuntimeStatus_eq :
    noPolynomialSemiringRuntimeStatus = SM9eNoPolynomialSemiringRuntimeStatus.noPolynomialSemiringRuntime
  noMathlibPolynomialOperationalPathStatus : SM9eNoMathlibPolynomialOperationalPathStatus
  noMathlibPolynomialOperationalPathStatus_eq :
    noMathlibPolynomialOperationalPathStatus =
      SM9eNoMathlibPolynomialOperationalPathStatus.noMathlibPolynomialOperationalPath
  noMatrixCharpolyOracleStatus : SM9eNoMatrixCharpolyOracleStatus
  noMatrixCharpolyOracleStatus_eq :
    noMatrixCharpolyOracleStatus = SM9eNoMatrixCharpolyOracleStatus.noMatrixCharpolyOracle
  noFactorizationStatus : SM9eNoFactorizationStatus
  noFactorizationStatus_eq : noFactorizationStatus = SM9eNoFactorizationStatus.noFactorization
  noDiscriminantStatus : SM9eNoDiscriminantStatus
  noDiscriminantStatus_eq : noDiscriminantStatus = SM9eNoDiscriminantStatus.noDiscriminant
  noHeegnerTargetStatus : SM9eNoHeegnerTargetStatus
  noHeegnerTargetStatus_eq : noHeegnerTargetStatus = SM9eNoHeegnerTargetStatus.noHeegnerTarget
  noCMTargetStatus : SM9eNoCMTargetStatus
  noCMTargetStatus_eq : noCMTargetStatus = SM9eNoCMTargetStatus.noCMTarget
  noMatrixInvStatus : SM9eNoMatrixInvStatus
  noMatrixInvStatus_eq : noMatrixInvStatus = SM9eNoMatrixInvStatus.noMatrixInv
  noFieldSimpStatus : SM9eNoFieldSimpStatus
  noFieldSimpStatus_eq : noFieldSimpStatus = SM9eNoFieldSimpStatus.noFieldSimp
  noScalarInvStatus : SM9eNoScalarInvStatus
  noScalarInvStatus_eq : noScalarInvStatus = SM9eNoScalarInvStatus.noScalarInv
  noNoncomputableOperationalSourceStatus : SM9eNoNoncomputableOperationalSourceStatus
  noNoncomputableOperationalSourceStatus_eq :
    noNoncomputableOperationalSourceStatus =
      SM9eNoNoncomputableOperationalSourceStatus.noNoncomputableOperationalSource

def sm9eGeneratedOperationalDeterminantCoefficientRecurrenceLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9dGeneratedLevelHistoryOperationalCoefficientSourceLedger
      b β p regularWeight variableWeight z) :
    SM9eGeneratedOperationalDeterminantCoefficientRecurrenceLedger b β p regularWeight variableWeight z :=
  let R := regularGeneratedOperationalDeterminantCoefficientRecurrenceSM9e L
  let V := variableGeneratedOperationalDeterminantCoefficientRecurrenceSM9e L
  { sourceSM9dLedger := L
    regularRecurrence := R
    variableRecurrence := V
    regularRecurrence_eq_from_SM9d := by
      rfl
    variableRecurrence_eq_from_SM9d := by
      rfl
    regularDegreeBound_eq_SM9d := R.degreeBound_eq_SM9d
    variableDegreeBound_eq_SM9d := V.degreeBound_eq_SM9d
    regularCoefficients_source_eq_linearPencil := R.coefficients_source_eq_linearPencil
    variableCoefficients_source_eq_linearPencil := V.coefficients_source_eq_linearPencil
    regularEvaluationAtSource_eq_coefficients := R.evaluationAtSource_eq_coefficients
    variableEvaluationAtSource_eq_coefficients := V.evaluationAtSource_eq_coefficients
    determinantBridgeStatus := SM9eDeterminantBridgeStatus.determinantBridgeDeferredToSM9f
    determinantBridgeStatus_eq := by
      rfl
    nextPhaseStatus := SM9eNextPhaseStatus.determinantEvaluationBridgeBeforeDiscriminantGate
    nextPhaseStatus_eq := by
      rfl
    noFreeCoefficientTableStatus := SM9eNoFreeCoefficientTableStatus.noFreeCoefficientTable
    noFreeCoefficientTableStatus_eq := by
      rfl
    noPolynomialSemiringRuntimeStatus := SM9eNoPolynomialSemiringRuntimeStatus.noPolynomialSemiringRuntime
    noPolynomialSemiringRuntimeStatus_eq := by
      rfl
    noMathlibPolynomialOperationalPathStatus :=
      SM9eNoMathlibPolynomialOperationalPathStatus.noMathlibPolynomialOperationalPath
    noMathlibPolynomialOperationalPathStatus_eq := by
      rfl
    noMatrixCharpolyOracleStatus := SM9eNoMatrixCharpolyOracleStatus.noMatrixCharpolyOracle
    noMatrixCharpolyOracleStatus_eq := by
      rfl
    noFactorizationStatus := SM9eNoFactorizationStatus.noFactorization
    noFactorizationStatus_eq := by
      rfl
    noDiscriminantStatus := SM9eNoDiscriminantStatus.noDiscriminant
    noDiscriminantStatus_eq := by
      rfl
    noHeegnerTargetStatus := SM9eNoHeegnerTargetStatus.noHeegnerTarget
    noHeegnerTargetStatus_eq := by
      rfl
    noCMTargetStatus := SM9eNoCMTargetStatus.noCMTarget
    noCMTargetStatus_eq := by
      rfl
    noMatrixInvStatus := SM9eNoMatrixInvStatus.noMatrixInv
    noMatrixInvStatus_eq := by
      rfl
    noFieldSimpStatus := SM9eNoFieldSimpStatus.noFieldSimp
    noFieldSimpStatus_eq := by
      rfl
    noScalarInvStatus := SM9eNoScalarInvStatus.noScalarInv
    noScalarInvStatus_eq := by
      rfl
    noNoncomputableOperationalSourceStatus :=
      SM9eNoNoncomputableOperationalSourceStatus.noNoncomputableOperationalSource
    noNoncomputableOperationalSourceStatus_eq := by
      rfl }

def sm9eGeneratedOperationalDeterminantCoefficientRecurrenceLedger_from_SM9aRecheckLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM9aRecheckGeneratedLevelHistoryExecMirrorSourceLedger b β p regularWeight variableWeight)
    (z : Schur.SpectralParameter) :
    SM9eGeneratedOperationalDeterminantCoefficientRecurrenceLedger b β p regularWeight variableWeight z :=
  sm9eGeneratedOperationalDeterminantCoefficientRecurrenceLedger
    (sm9dGeneratedLevelHistoryOperationalCoefficientSourceLedger_from_SM9aRecheckLedger L z)

def sm9eGeneratedOperationalDeterminantCoefficientRecurrenceLedger_from_accumulatedEntryCancellationLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight)
    (level : Nat)
    (levelIndex : GeneratedLevelHistoryIndexSM6 level)
    (z : Schur.SpectralParameter) :
    SM9eGeneratedOperationalDeterminantCoefficientRecurrenceLedger b β p regularWeight variableWeight z :=
  sm9eGeneratedOperationalDeterminantCoefficientRecurrenceLedger
    (sm9dGeneratedLevelHistoryOperationalCoefficientSourceLedger_from_accumulatedEntryCancellationLedger
      L level levelIndex z)

theorem sm9e_regularCoefficients_source_eq_linearPencil
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9eGeneratedOperationalDeterminantCoefficientRecurrenceLedger
      b β p regularWeight variableWeight z) :
    L.regularRecurrence.coefficientPolynomial =
      operationalDeterminantCoefficientRecurrenceSM9e
        L.regularRecurrence.degreeBound L.regularRecurrence.sourceSM9d.matrix :=
  L.regularCoefficients_source_eq_linearPencil

theorem sm9e_variableCoefficients_source_eq_linearPencil
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9eGeneratedOperationalDeterminantCoefficientRecurrenceLedger
      b β p regularWeight variableWeight z) :
    L.variableRecurrence.coefficientPolynomial =
      operationalDeterminantCoefficientRecurrenceSM9e
        L.variableRecurrence.degreeBound L.variableRecurrence.sourceSM9d.matrix :=
  L.variableCoefficients_source_eq_linearPencil

theorem sm9e_regularEvaluationAtSource_eq_coefficients
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9eGeneratedOperationalDeterminantCoefficientRecurrenceLedger
      b β p regularWeight variableWeight z) :
    L.regularRecurrence.evaluationAtSource =
      L.regularRecurrence.evaluationFromCoefficients L.regularRecurrence.sourceSM9d.sourceParameter :=
  L.regularEvaluationAtSource_eq_coefficients

theorem sm9e_variableEvaluationAtSource_eq_coefficients
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9eGeneratedOperationalDeterminantCoefficientRecurrenceLedger
      b β p regularWeight variableWeight z) :
    L.variableRecurrence.evaluationAtSource =
      L.variableRecurrence.evaluationFromCoefficients L.variableRecurrence.sourceSM9d.sourceParameter :=
  L.variableEvaluationAtSource_eq_coefficients

theorem sm9e_determinantBridge_deferred_to_SM9f
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9eGeneratedOperationalDeterminantCoefficientRecurrenceLedger
      b β p regularWeight variableWeight z) :
    L.determinantBridgeStatus = SM9eDeterminantBridgeStatus.determinantBridgeDeferredToSM9f :=
  L.determinantBridgeStatus_eq

theorem sm9e_noFactorization
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9eGeneratedOperationalDeterminantCoefficientRecurrenceLedger
      b β p regularWeight variableWeight z) :
    L.noFactorizationStatus = SM9eNoFactorizationStatus.noFactorization :=
  L.noFactorizationStatus_eq

theorem sm9e_noDiscriminant
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9eGeneratedOperationalDeterminantCoefficientRecurrenceLedger
      b β p regularWeight variableWeight z) :
    L.noDiscriminantStatus = SM9eNoDiscriminantStatus.noDiscriminant :=
  L.noDiscriminantStatus_eq

theorem sm9e_noHeegnerTarget
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9eGeneratedOperationalDeterminantCoefficientRecurrenceLedger
      b β p regularWeight variableWeight z) :
    L.noHeegnerTargetStatus = SM9eNoHeegnerTargetStatus.noHeegnerTarget :=
  L.noHeegnerTargetStatus_eq

end Smoke

end CNNA.PillarA.Arithmetic
