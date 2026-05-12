import CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDiscriminantFactorGateFromSM9fFull

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.DtN

namespace Smoke

inductive SM9g1QuadraticCoefficientWindowStatus where
  | quadraticWindowValidatedFromSM9dSM9e
  deriving DecidableEq, Repr

inductive SM9g1SM10ReleaseStatus where
  | sm10BlockedUntilOperationalDiscriminantSourceFromWindow
  deriving DecidableEq, Repr

inductive SM9g1NextPhaseStatus where
  | operationalQuadraticDiscriminantSourceFromWindow
  deriving DecidableEq, Repr

inductive SM9g1NoFreeWindowTableStatus where
  | noFreeWindowTable
  deriving DecidableEq, Repr

structure OperationalQuadraticCoefficientWindowSM9g1 (degreeBound : Nat) where
  sourceCoefficientPolynomial : OperationalBoundedPolynomialSM9e degreeBound
  constantCoeff : ExecComplex
  constantCoeff_eq_coefficientAt :
    constantCoeff = OperationalBoundedPolynomialSM9e.coefficientAt sourceCoefficientPolynomial 0
  linearCoeff : ExecComplex
  linearCoeff_eq_coefficientAt :
    linearCoeff = OperationalBoundedPolynomialSM9e.coefficientAt sourceCoefficientPolynomial 1
  quadraticCoeff : ExecComplex
  quadraticCoeff_eq_coefficientAt :
    quadraticCoeff = OperationalBoundedPolynomialSM9e.coefficientAt sourceCoefficientPolynomial 2

namespace OperationalQuadraticCoefficientWindowSM9g1

variable {degreeBound : Nat}

def fromCoefficientSource
    (P : OperationalBoundedPolynomialSM9e degreeBound) :
    OperationalQuadraticCoefficientWindowSM9g1 degreeBound :=
  { sourceCoefficientPolynomial := P
    constantCoeff := OperationalBoundedPolynomialSM9e.coefficientAt P 0
    constantCoeff_eq_coefficientAt := by
      rfl
    linearCoeff := OperationalBoundedPolynomialSM9e.coefficientAt P 1
    linearCoeff_eq_coefficientAt := by
      rfl
    quadraticCoeff := OperationalBoundedPolynomialSM9e.coefficientAt P 2
    quadraticCoeff_eq_coefficientAt := by
      rfl }

end OperationalQuadraticCoefficientWindowSM9g1

structure SM9g1GeneratedOperationalQuadraticCoefficientWindowLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (z : Schur.SpectralParameter) where
  sourceSM9gGate :
    SM9gGeneratedOperationalDiscriminantFactorGateLedger
      b β p regularWeight variableWeight z
  sourceSM9gGate_nextPhase_eq :
    sourceSM9gGate.nextPhaseStatus =
      SM9gNextPhaseStatus.operationalQuadraticCoefficientWindowFromSM9dSM9e
  regularWindow :
    OperationalQuadraticCoefficientWindowSM9g1
      sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.degreeBound
  regularWindow_source_eq_SM9g :
    regularWindow.sourceCoefficientPolynomial = sourceSM9gGate.regularCoefficientSource
  regularConstantCoeff_eq_SM9gCoefficientAt :
    regularWindow.constantCoeff =
      OperationalBoundedPolynomialSM9e.coefficientAt sourceSM9gGate.regularCoefficientSource 0
  regularLinearCoeff_eq_SM9gCoefficientAt :
    regularWindow.linearCoeff =
      OperationalBoundedPolynomialSM9e.coefficientAt sourceSM9gGate.regularCoefficientSource 1
  regularQuadraticCoeff_eq_SM9gCoefficientAt :
    regularWindow.quadraticCoeff =
      OperationalBoundedPolynomialSM9e.coefficientAt sourceSM9gGate.regularCoefficientSource 2
  regularConstantCoeff_eq_operationalRecurrence :
    regularWindow.constantCoeff =
      OperationalBoundedPolynomialSM9e.coefficientAt
        (operationalDeterminantCoefficientRecurrenceSM9e
          sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.degreeBound
          sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.sourceSM9d.matrix) 0
  regularLinearCoeff_eq_operationalRecurrence :
    regularWindow.linearCoeff =
      OperationalBoundedPolynomialSM9e.coefficientAt
        (operationalDeterminantCoefficientRecurrenceSM9e
          sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.degreeBound
          sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.sourceSM9d.matrix) 1
  regularQuadraticCoeff_eq_operationalRecurrence :
    regularWindow.quadraticCoeff =
      OperationalBoundedPolynomialSM9e.coefficientAt
        (operationalDeterminantCoefficientRecurrenceSM9e
          sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.degreeBound
          sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.sourceSM9d.matrix) 2
  variableWindow :
    OperationalQuadraticCoefficientWindowSM9g1
      sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.degreeBound
  variableWindow_source_eq_SM9g :
    variableWindow.sourceCoefficientPolynomial = sourceSM9gGate.variableCoefficientSource
  variableConstantCoeff_eq_SM9gCoefficientAt :
    variableWindow.constantCoeff =
      OperationalBoundedPolynomialSM9e.coefficientAt sourceSM9gGate.variableCoefficientSource 0
  variableLinearCoeff_eq_SM9gCoefficientAt :
    variableWindow.linearCoeff =
      OperationalBoundedPolynomialSM9e.coefficientAt sourceSM9gGate.variableCoefficientSource 1
  variableQuadraticCoeff_eq_SM9gCoefficientAt :
    variableWindow.quadraticCoeff =
      OperationalBoundedPolynomialSM9e.coefficientAt sourceSM9gGate.variableCoefficientSource 2
  variableConstantCoeff_eq_operationalRecurrence :
    variableWindow.constantCoeff =
      OperationalBoundedPolynomialSM9e.coefficientAt
        (operationalDeterminantCoefficientRecurrenceSM9e
          sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.degreeBound
          sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.sourceSM9d.matrix) 0
  variableLinearCoeff_eq_operationalRecurrence :
    variableWindow.linearCoeff =
      OperationalBoundedPolynomialSM9e.coefficientAt
        (operationalDeterminantCoefficientRecurrenceSM9e
          sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.degreeBound
          sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.sourceSM9d.matrix) 1
  variableQuadraticCoeff_eq_operationalRecurrence :
    variableWindow.quadraticCoeff =
      OperationalBoundedPolynomialSM9e.coefficientAt
        (operationalDeterminantCoefficientRecurrenceSM9e
          sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.degreeBound
          sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.sourceSM9d.matrix) 2
  quadraticWindowStatus : SM9g1QuadraticCoefficientWindowStatus
  quadraticWindowStatus_eq :
    quadraticWindowStatus =
      SM9g1QuadraticCoefficientWindowStatus.quadraticWindowValidatedFromSM9dSM9e
  sm10ReleaseStatus : SM9g1SM10ReleaseStatus
  sm10ReleaseStatus_eq :
    sm10ReleaseStatus =
      SM9g1SM10ReleaseStatus.sm10BlockedUntilOperationalDiscriminantSourceFromWindow
  nextPhaseStatus : SM9g1NextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus = SM9g1NextPhaseStatus.operationalQuadraticDiscriminantSourceFromWindow
  noFreeWindowTableStatus : SM9g1NoFreeWindowTableStatus
  noFreeWindowTableStatus_eq : noFreeWindowTableStatus = SM9g1NoFreeWindowTableStatus.noFreeWindowTable
  noFreeFactorFormStatus : SM9gNoFreeFactorFormStatus
  noFreeFactorFormStatus_eq : noFreeFactorFormStatus = SM9gNoFreeFactorFormStatus.noFreeFactorForm
  noFreeDiscriminantStatus : SM9gNoFreeDiscriminantStatus
  noFreeDiscriminantStatus_eq : noFreeDiscriminantStatus = SM9gNoFreeDiscriminantStatus.noFreeDiscriminant
  noFreeTargetValueStatus : SM9gNoFreeTargetValueStatus
  noFreeTargetValueStatus_eq : noFreeTargetValueStatus = SM9gNoFreeTargetValueStatus.noFreeTargetValue
  noExternalComparisonMatrixStatus : SM9gNoExternalComparisonMatrixStatus
  noExternalComparisonMatrixStatus_eq :
    noExternalComparisonMatrixStatus =
      SM9gNoExternalComparisonMatrixStatus.noExternalComparisonMatrix
  noEisensteinGaussHeegnerCMJConsumerStatus : SM9gNoEisensteinGaussHeegnerCMJConsumerStatus
  noEisensteinGaussHeegnerCMJConsumerStatus_eq :
    noEisensteinGaussHeegnerCMJConsumerStatus =
      SM9gNoEisensteinGaussHeegnerCMJConsumerStatus.noEisensteinGaussHeegnerCMJConsumer
  noNewMatrixStatus : SM9gNoNewMatrixStatus
  noNewMatrixStatus_eq : noNewMatrixStatus = SM9gNoNewMatrixStatus.noNewMatrix
  noNewDeterminantRecurrenceStatus : SM9gNoNewDeterminantRecurrenceStatus
  noNewDeterminantRecurrenceStatus_eq :
    noNewDeterminantRecurrenceStatus =
      SM9gNoNewDeterminantRecurrenceStatus.noNewDeterminantRecurrence
  noCharpolyRecomputationStatus : SM9gNoCharpolyRecomputationStatus
  noCharpolyRecomputationStatus_eq :
    noCharpolyRecomputationStatus = SM9gNoCharpolyRecomputationStatus.noCharpolyRecomputation
  noPolynomialSemiringRuntimeStatus : SM9eNoPolynomialSemiringRuntimeStatus
  noPolynomialSemiringRuntimeStatus_eq :
    noPolynomialSemiringRuntimeStatus =
      SM9eNoPolynomialSemiringRuntimeStatus.noPolynomialSemiringRuntime
  noMathlibPolynomialOperationalPathStatus : SM9eNoMathlibPolynomialOperationalPathStatus
  noMathlibPolynomialOperationalPathStatus_eq :
    noMathlibPolynomialOperationalPathStatus =
      SM9eNoMathlibPolynomialOperationalPathStatus.noMathlibPolynomialOperationalPath
  noTwoSidedInvStatus : SM9gNoTwoSidedInvStatus
  noTwoSidedInvStatus_eq : noTwoSidedInvStatus = SM9gNoTwoSidedInvStatus.noTwoSidedInv
  noMatrixInvStatus : SM9fNoMatrixInvStatus
  noMatrixInvStatus_eq : noMatrixInvStatus = SM9fNoMatrixInvStatus.noMatrixInv
  noFieldSimpStatus : SM9fNoFieldSimpStatus
  noFieldSimpStatus_eq : noFieldSimpStatus = SM9fNoFieldSimpStatus.noFieldSimp
  noScalarInvStatus : SM9fNoScalarInvStatus
  noScalarInvStatus_eq : noScalarInvStatus = SM9fNoScalarInvStatus.noScalarInv
  noNoncomputableOperationalSourceStatus : SM9fNoNoncomputableOperationalSourceStatus
  noNoncomputableOperationalSourceStatus_eq :
    noNoncomputableOperationalSourceStatus =
      SM9fNoNoncomputableOperationalSourceStatus.noNoncomputableOperationalSource

def sm9g1GeneratedOperationalQuadraticCoefficientWindowLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (G : SM9gGeneratedOperationalDiscriminantFactorGateLedger
      b β p regularWeight variableWeight z) :
    SM9g1GeneratedOperationalQuadraticCoefficientWindowLedger
      b β p regularWeight variableWeight z :=
  let RW := OperationalQuadraticCoefficientWindowSM9g1.fromCoefficientSource G.regularCoefficientSource
  let VW := OperationalQuadraticCoefficientWindowSM9g1.fromCoefficientSource G.variableCoefficientSource
  { sourceSM9gGate := G
    sourceSM9gGate_nextPhase_eq := G.nextPhaseStatus_eq
    regularWindow := RW
    regularWindow_source_eq_SM9g := by
      rfl
    regularConstantCoeff_eq_SM9gCoefficientAt := by
      calc
        RW.constantCoeff =
            OperationalBoundedPolynomialSM9e.coefficientAt RW.sourceCoefficientPolynomial 0 := by
          exact RW.constantCoeff_eq_coefficientAt
        _ = OperationalBoundedPolynomialSM9e.coefficientAt G.regularCoefficientSource 0 := by
          rfl
    regularLinearCoeff_eq_SM9gCoefficientAt := by
      calc
        RW.linearCoeff =
            OperationalBoundedPolynomialSM9e.coefficientAt RW.sourceCoefficientPolynomial 1 := by
          exact RW.linearCoeff_eq_coefficientAt
        _ = OperationalBoundedPolynomialSM9e.coefficientAt G.regularCoefficientSource 1 := by
          rfl
    regularQuadraticCoeff_eq_SM9gCoefficientAt := by
      calc
        RW.quadraticCoeff =
            OperationalBoundedPolynomialSM9e.coefficientAt RW.sourceCoefficientPolynomial 2 := by
          exact RW.quadraticCoeff_eq_coefficientAt
        _ = OperationalBoundedPolynomialSM9e.coefficientAt G.regularCoefficientSource 2 := by
          rfl
    regularConstantCoeff_eq_operationalRecurrence := by
      calc
        RW.constantCoeff =
            OperationalBoundedPolynomialSM9e.coefficientAt RW.sourceCoefficientPolynomial 0 := by
          exact RW.constantCoeff_eq_coefficientAt
        _ = OperationalBoundedPolynomialSM9e.coefficientAt G.regularCoefficientSource 0 := by
          rfl
        _ = OperationalBoundedPolynomialSM9e.coefficientAt
            (operationalDeterminantCoefficientRecurrenceSM9e
              G.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.degreeBound
              G.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.sourceSM9d.matrix) 0 := by
          rw [G.regularCoefficientSource_eq_operationalRecurrence]
    regularLinearCoeff_eq_operationalRecurrence := by
      calc
        RW.linearCoeff =
            OperationalBoundedPolynomialSM9e.coefficientAt RW.sourceCoefficientPolynomial 1 := by
          exact RW.linearCoeff_eq_coefficientAt
        _ = OperationalBoundedPolynomialSM9e.coefficientAt G.regularCoefficientSource 1 := by
          rfl
        _ = OperationalBoundedPolynomialSM9e.coefficientAt
            (operationalDeterminantCoefficientRecurrenceSM9e
              G.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.degreeBound
              G.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.sourceSM9d.matrix) 1 := by
          rw [G.regularCoefficientSource_eq_operationalRecurrence]
    regularQuadraticCoeff_eq_operationalRecurrence := by
      calc
        RW.quadraticCoeff =
            OperationalBoundedPolynomialSM9e.coefficientAt RW.sourceCoefficientPolynomial 2 := by
          exact RW.quadraticCoeff_eq_coefficientAt
        _ = OperationalBoundedPolynomialSM9e.coefficientAt G.regularCoefficientSource 2 := by
          rfl
        _ = OperationalBoundedPolynomialSM9e.coefficientAt
            (operationalDeterminantCoefficientRecurrenceSM9e
              G.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.degreeBound
              G.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.sourceSM9d.matrix) 2 := by
          rw [G.regularCoefficientSource_eq_operationalRecurrence]
    variableWindow := VW
    variableWindow_source_eq_SM9g := by
      rfl
    variableConstantCoeff_eq_SM9gCoefficientAt := by
      calc
        VW.constantCoeff =
            OperationalBoundedPolynomialSM9e.coefficientAt VW.sourceCoefficientPolynomial 0 := by
          exact VW.constantCoeff_eq_coefficientAt
        _ = OperationalBoundedPolynomialSM9e.coefficientAt G.variableCoefficientSource 0 := by
          rfl
    variableLinearCoeff_eq_SM9gCoefficientAt := by
      calc
        VW.linearCoeff =
            OperationalBoundedPolynomialSM9e.coefficientAt VW.sourceCoefficientPolynomial 1 := by
          exact VW.linearCoeff_eq_coefficientAt
        _ = OperationalBoundedPolynomialSM9e.coefficientAt G.variableCoefficientSource 1 := by
          rfl
    variableQuadraticCoeff_eq_SM9gCoefficientAt := by
      calc
        VW.quadraticCoeff =
            OperationalBoundedPolynomialSM9e.coefficientAt VW.sourceCoefficientPolynomial 2 := by
          exact VW.quadraticCoeff_eq_coefficientAt
        _ = OperationalBoundedPolynomialSM9e.coefficientAt G.variableCoefficientSource 2 := by
          rfl
    variableConstantCoeff_eq_operationalRecurrence := by
      calc
        VW.constantCoeff =
            OperationalBoundedPolynomialSM9e.coefficientAt VW.sourceCoefficientPolynomial 0 := by
          exact VW.constantCoeff_eq_coefficientAt
        _ = OperationalBoundedPolynomialSM9e.coefficientAt G.variableCoefficientSource 0 := by
          rfl
        _ = OperationalBoundedPolynomialSM9e.coefficientAt
            (operationalDeterminantCoefficientRecurrenceSM9e
              G.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.degreeBound
              G.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.sourceSM9d.matrix) 0 := by
          rw [G.variableCoefficientSource_eq_operationalRecurrence]
    variableLinearCoeff_eq_operationalRecurrence := by
      calc
        VW.linearCoeff =
            OperationalBoundedPolynomialSM9e.coefficientAt VW.sourceCoefficientPolynomial 1 := by
          exact VW.linearCoeff_eq_coefficientAt
        _ = OperationalBoundedPolynomialSM9e.coefficientAt G.variableCoefficientSource 1 := by
          rfl
        _ = OperationalBoundedPolynomialSM9e.coefficientAt
            (operationalDeterminantCoefficientRecurrenceSM9e
              G.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.degreeBound
              G.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.sourceSM9d.matrix) 1 := by
          rw [G.variableCoefficientSource_eq_operationalRecurrence]
    variableQuadraticCoeff_eq_operationalRecurrence := by
      calc
        VW.quadraticCoeff =
            OperationalBoundedPolynomialSM9e.coefficientAt VW.sourceCoefficientPolynomial 2 := by
          exact VW.quadraticCoeff_eq_coefficientAt
        _ = OperationalBoundedPolynomialSM9e.coefficientAt G.variableCoefficientSource 2 := by
          rfl
        _ = OperationalBoundedPolynomialSM9e.coefficientAt
            (operationalDeterminantCoefficientRecurrenceSM9e
              G.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.degreeBound
              G.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.sourceSM9d.matrix) 2 := by
          rw [G.variableCoefficientSource_eq_operationalRecurrence]
    quadraticWindowStatus :=
      SM9g1QuadraticCoefficientWindowStatus.quadraticWindowValidatedFromSM9dSM9e
    quadraticWindowStatus_eq := by
      rfl
    sm10ReleaseStatus :=
      SM9g1SM10ReleaseStatus.sm10BlockedUntilOperationalDiscriminantSourceFromWindow
    sm10ReleaseStatus_eq := by
      rfl
    nextPhaseStatus := SM9g1NextPhaseStatus.operationalQuadraticDiscriminantSourceFromWindow
    nextPhaseStatus_eq := by
      rfl
    noFreeWindowTableStatus := SM9g1NoFreeWindowTableStatus.noFreeWindowTable
    noFreeWindowTableStatus_eq := by
      rfl
    noFreeFactorFormStatus := SM9gNoFreeFactorFormStatus.noFreeFactorForm
    noFreeFactorFormStatus_eq := by
      rfl
    noFreeDiscriminantStatus := SM9gNoFreeDiscriminantStatus.noFreeDiscriminant
    noFreeDiscriminantStatus_eq := by
      rfl
    noFreeTargetValueStatus := SM9gNoFreeTargetValueStatus.noFreeTargetValue
    noFreeTargetValueStatus_eq := by
      rfl
    noExternalComparisonMatrixStatus := SM9gNoExternalComparisonMatrixStatus.noExternalComparisonMatrix
    noExternalComparisonMatrixStatus_eq := by
      rfl
    noEisensteinGaussHeegnerCMJConsumerStatus :=
      SM9gNoEisensteinGaussHeegnerCMJConsumerStatus.noEisensteinGaussHeegnerCMJConsumer
    noEisensteinGaussHeegnerCMJConsumerStatus_eq := by
      rfl
    noNewMatrixStatus := SM9gNoNewMatrixStatus.noNewMatrix
    noNewMatrixStatus_eq := by
      rfl
    noNewDeterminantRecurrenceStatus := SM9gNoNewDeterminantRecurrenceStatus.noNewDeterminantRecurrence
    noNewDeterminantRecurrenceStatus_eq := by
      rfl
    noCharpolyRecomputationStatus := SM9gNoCharpolyRecomputationStatus.noCharpolyRecomputation
    noCharpolyRecomputationStatus_eq := by
      rfl
    noPolynomialSemiringRuntimeStatus := SM9eNoPolynomialSemiringRuntimeStatus.noPolynomialSemiringRuntime
    noPolynomialSemiringRuntimeStatus_eq := by
      rfl
    noMathlibPolynomialOperationalPathStatus :=
      SM9eNoMathlibPolynomialOperationalPathStatus.noMathlibPolynomialOperationalPath
    noMathlibPolynomialOperationalPathStatus_eq := by
      rfl
    noTwoSidedInvStatus := SM9gNoTwoSidedInvStatus.noTwoSidedInv
    noTwoSidedInvStatus_eq := by
      rfl
    noMatrixInvStatus := SM9fNoMatrixInvStatus.noMatrixInv
    noMatrixInvStatus_eq := by
      rfl
    noFieldSimpStatus := SM9fNoFieldSimpStatus.noFieldSimp
    noFieldSimpStatus_eq := by
      rfl
    noScalarInvStatus := SM9fNoScalarInvStatus.noScalarInv
    noScalarInvStatus_eq := by
      rfl
    noNoncomputableOperationalSourceStatus :=
      SM9fNoNoncomputableOperationalSourceStatus.noNoncomputableOperationalSource
    noNoncomputableOperationalSourceStatus_eq := by
      rfl }

def sm9g1GeneratedOperationalQuadraticCoefficientWindowLedger_from_SM9eLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9eGeneratedOperationalDeterminantCoefficientRecurrenceLedger
      b β p regularWeight variableWeight z) :
    SM9g1GeneratedOperationalQuadraticCoefficientWindowLedger
      b β p regularWeight variableWeight z :=
  sm9g1GeneratedOperationalQuadraticCoefficientWindowLedger
    (sm9gGeneratedOperationalDiscriminantFactorGateLedger_from_SM9eLedger L)

theorem sm9g1_regularCoefficientWindow_eq_SM9gCoefficientAt
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9g1GeneratedOperationalQuadraticCoefficientWindowLedger
      b β p regularWeight variableWeight z) :
    L.regularWindow.constantCoeff =
      OperationalBoundedPolynomialSM9e.coefficientAt L.sourceSM9gGate.regularCoefficientSource 0 ∧
    L.regularWindow.linearCoeff =
      OperationalBoundedPolynomialSM9e.coefficientAt L.sourceSM9gGate.regularCoefficientSource 1 ∧
    L.regularWindow.quadraticCoeff =
      OperationalBoundedPolynomialSM9e.coefficientAt L.sourceSM9gGate.regularCoefficientSource 2 :=
  ⟨L.regularConstantCoeff_eq_SM9gCoefficientAt,
    L.regularLinearCoeff_eq_SM9gCoefficientAt,
    L.regularQuadraticCoeff_eq_SM9gCoefficientAt⟩

theorem sm9g1_variableCoefficientWindow_eq_SM9gCoefficientAt
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9g1GeneratedOperationalQuadraticCoefficientWindowLedger
      b β p regularWeight variableWeight z) :
    L.variableWindow.constantCoeff =
      OperationalBoundedPolynomialSM9e.coefficientAt L.sourceSM9gGate.variableCoefficientSource 0 ∧
    L.variableWindow.linearCoeff =
      OperationalBoundedPolynomialSM9e.coefficientAt L.sourceSM9gGate.variableCoefficientSource 1 ∧
    L.variableWindow.quadraticCoeff =
      OperationalBoundedPolynomialSM9e.coefficientAt L.sourceSM9gGate.variableCoefficientSource 2 :=
  ⟨L.variableConstantCoeff_eq_SM9gCoefficientAt,
    L.variableLinearCoeff_eq_SM9gCoefficientAt,
    L.variableQuadraticCoeff_eq_SM9gCoefficientAt⟩

theorem sm9g1_regularCoefficientWindow_eq_operationalRecurrence
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9g1GeneratedOperationalQuadraticCoefficientWindowLedger
      b β p regularWeight variableWeight z) :
    L.regularWindow.constantCoeff =
      OperationalBoundedPolynomialSM9e.coefficientAt
        (operationalDeterminantCoefficientRecurrenceSM9e
          L.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.degreeBound
          L.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.sourceSM9d.matrix) 0 ∧
    L.regularWindow.linearCoeff =
      OperationalBoundedPolynomialSM9e.coefficientAt
        (operationalDeterminantCoefficientRecurrenceSM9e
          L.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.degreeBound
          L.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.sourceSM9d.matrix) 1 ∧
    L.regularWindow.quadraticCoeff =
      OperationalBoundedPolynomialSM9e.coefficientAt
        (operationalDeterminantCoefficientRecurrenceSM9e
          L.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.degreeBound
          L.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.sourceSM9d.matrix) 2 :=
  ⟨L.regularConstantCoeff_eq_operationalRecurrence,
    L.regularLinearCoeff_eq_operationalRecurrence,
    L.regularQuadraticCoeff_eq_operationalRecurrence⟩

theorem sm9g1_variableCoefficientWindow_eq_operationalRecurrence
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9g1GeneratedOperationalQuadraticCoefficientWindowLedger
      b β p regularWeight variableWeight z) :
    L.variableWindow.constantCoeff =
      OperationalBoundedPolynomialSM9e.coefficientAt
        (operationalDeterminantCoefficientRecurrenceSM9e
          L.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.degreeBound
          L.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.sourceSM9d.matrix) 0 ∧
    L.variableWindow.linearCoeff =
      OperationalBoundedPolynomialSM9e.coefficientAt
        (operationalDeterminantCoefficientRecurrenceSM9e
          L.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.degreeBound
          L.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.sourceSM9d.matrix) 1 ∧
    L.variableWindow.quadraticCoeff =
      OperationalBoundedPolynomialSM9e.coefficientAt
        (operationalDeterminantCoefficientRecurrenceSM9e
          L.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.degreeBound
          L.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.sourceSM9d.matrix) 2 :=
  ⟨L.variableConstantCoeff_eq_operationalRecurrence,
    L.variableLinearCoeff_eq_operationalRecurrence,
    L.variableQuadraticCoeff_eq_operationalRecurrence⟩

theorem sm9g1_quadraticWindowValidatedFromSM9dSM9e
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9g1GeneratedOperationalQuadraticCoefficientWindowLedger
      b β p regularWeight variableWeight z) :
    L.quadraticWindowStatus =
      SM9g1QuadraticCoefficientWindowStatus.quadraticWindowValidatedFromSM9dSM9e :=
  L.quadraticWindowStatus_eq

theorem sm9g1_nextPhase_eq_operationalQuadraticDiscriminantSourceFromWindow
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9g1GeneratedOperationalQuadraticCoefficientWindowLedger
      b β p regularWeight variableWeight z) :
    L.nextPhaseStatus = SM9g1NextPhaseStatus.operationalQuadraticDiscriminantSourceFromWindow :=
  L.nextPhaseStatus_eq

theorem sm9g1_sm10BlockedUntilOperationalDiscriminantSourceFromWindow
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9g1GeneratedOperationalQuadraticCoefficientWindowLedger
      b β p regularWeight variableWeight z) :
    L.sm10ReleaseStatus =
      SM9g1SM10ReleaseStatus.sm10BlockedUntilOperationalDiscriminantSourceFromWindow :=
  L.sm10ReleaseStatus_eq

theorem sm9g1_noFreeFactorDiscriminantOrTarget
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9g1GeneratedOperationalQuadraticCoefficientWindowLedger
      b β p regularWeight variableWeight z) :
    L.noFreeWindowTableStatus = SM9g1NoFreeWindowTableStatus.noFreeWindowTable ∧
    L.noFreeFactorFormStatus = SM9gNoFreeFactorFormStatus.noFreeFactorForm ∧
    L.noFreeDiscriminantStatus = SM9gNoFreeDiscriminantStatus.noFreeDiscriminant ∧
    L.noFreeTargetValueStatus = SM9gNoFreeTargetValueStatus.noFreeTargetValue ∧
    L.noExternalComparisonMatrixStatus =
      SM9gNoExternalComparisonMatrixStatus.noExternalComparisonMatrix :=
  ⟨L.noFreeWindowTableStatus_eq, L.noFreeFactorFormStatus_eq,
    L.noFreeDiscriminantStatus_eq, L.noFreeTargetValueStatus_eq,
    L.noExternalComparisonMatrixStatus_eq⟩

theorem sm9g1_noPolynomialRuntimeOrForbiddenAlgebra
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9g1GeneratedOperationalQuadraticCoefficientWindowLedger
      b β p regularWeight variableWeight z) :
    L.noPolynomialSemiringRuntimeStatus =
      SM9eNoPolynomialSemiringRuntimeStatus.noPolynomialSemiringRuntime ∧
    L.noMathlibPolynomialOperationalPathStatus =
      SM9eNoMathlibPolynomialOperationalPathStatus.noMathlibPolynomialOperationalPath ∧
    L.noMatrixInvStatus = SM9fNoMatrixInvStatus.noMatrixInv ∧
    L.noFieldSimpStatus = SM9fNoFieldSimpStatus.noFieldSimp ∧
    L.noScalarInvStatus = SM9fNoScalarInvStatus.noScalarInv ∧
    L.noNoncomputableOperationalSourceStatus =
      SM9fNoNoncomputableOperationalSourceStatus.noNoncomputableOperationalSource :=
  ⟨L.noPolynomialSemiringRuntimeStatus_eq,
    L.noMathlibPolynomialOperationalPathStatus_eq,
    L.noMatrixInvStatus_eq, L.noFieldSimpStatus_eq, L.noScalarInvStatus_eq,
    L.noNoncomputableOperationalSourceStatus_eq⟩

end Smoke

end CNNA.PillarA.Arithmetic
