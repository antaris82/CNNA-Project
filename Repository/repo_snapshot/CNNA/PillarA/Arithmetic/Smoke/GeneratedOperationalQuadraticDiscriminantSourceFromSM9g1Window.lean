import CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalQuadraticCoefficientWindowFromSM9dSM9e

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.DtN

namespace Smoke

inductive SM9hOperationalDiscriminantSourceStatus where
  | discriminantSourceValidatedFromSM9g1Window
  deriving DecidableEq, Repr

inductive SM9hNextPhaseStatus where
  | sm10MayConsumeOperationalDiscriminantSource
  deriving DecidableEq, Repr

inductive SM9hNoFreeDiscriminantTableStatus where
  | noFreeDiscriminantTable
  deriving DecidableEq, Repr

inductive SM9hNoFactorProofStatus where
  | noFactorProof
  deriving DecidableEq, Repr

inductive SM9hNoFundamentalDiscriminantConventionBridgeStatus where
  | noFundamentalDiscriminantConventionBridge
  deriving DecidableEq, Repr

inductive SM9hNoComparisonTargetStatus where
  | noComparisonTarget
  deriving DecidableEq, Repr

inductive SM9hNoClassicalStatus where
  | noClassicalInOperationalDiscriminantSource
  deriving DecidableEq, Repr

structure OperationalQuadraticDiscriminantSourceSM9h (degreeBound : Nat) where
  sourceWindow : OperationalQuadraticCoefficientWindowSM9g1 degreeBound
  discriminantValue : ExecComplex
  discriminantValue_eq_windowFormula :
    discriminantValue =
      sourceWindow.linearCoeff * sourceWindow.linearCoeff -
        (ExecComplex.ofRat 4) * sourceWindow.quadraticCoeff * sourceWindow.constantCoeff

namespace OperationalQuadraticDiscriminantSourceSM9h

variable {degreeBound : Nat}

def fromWindow
    (W : OperationalQuadraticCoefficientWindowSM9g1 degreeBound) :
    OperationalQuadraticDiscriminantSourceSM9h degreeBound :=
  { sourceWindow := W
    discriminantValue :=
      W.linearCoeff * W.linearCoeff -
        (ExecComplex.ofRat 4) * W.quadraticCoeff * W.constantCoeff
    discriminantValue_eq_windowFormula := by
      rfl }

end OperationalQuadraticDiscriminantSourceSM9h

structure SM9hGeneratedOperationalQuadraticDiscriminantSourceLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (z : Schur.SpectralParameter) where
  sourceSM9g1Ledger :
    SM9g1GeneratedOperationalQuadraticCoefficientWindowLedger
      b β p regularWeight variableWeight z
  sourceSM9g1Ledger_nextPhase_eq :
    sourceSM9g1Ledger.nextPhaseStatus =
      SM9g1NextPhaseStatus.operationalQuadraticDiscriminantSourceFromWindow
  regularDiscriminantSource :
    OperationalQuadraticDiscriminantSourceSM9h
      sourceSM9g1Ledger.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.degreeBound
  regularSourceWindow_eq_SM9g1Window :
    regularDiscriminantSource.sourceWindow = sourceSM9g1Ledger.regularWindow
  regularDiscriminantValue_eq_windowFormula :
    regularDiscriminantSource.discriminantValue =
      regularDiscriminantSource.sourceWindow.linearCoeff *
        regularDiscriminantSource.sourceWindow.linearCoeff -
          (ExecComplex.ofRat 4) * regularDiscriminantSource.sourceWindow.quadraticCoeff *
            regularDiscriminantSource.sourceWindow.constantCoeff
  regularDiscriminantValue_eq_SM9g1WindowFormula :
    regularDiscriminantSource.discriminantValue =
      sourceSM9g1Ledger.regularWindow.linearCoeff * sourceSM9g1Ledger.regularWindow.linearCoeff -
        (ExecComplex.ofRat 4) * sourceSM9g1Ledger.regularWindow.quadraticCoeff *
          sourceSM9g1Ledger.regularWindow.constantCoeff
  regularDiscriminantValue_eq_SM9gCoefficientWindowFormula :
    regularDiscriminantSource.discriminantValue =
      OperationalBoundedPolynomialSM9e.coefficientAt
          sourceSM9g1Ledger.sourceSM9gGate.regularCoefficientSource 1 *
        OperationalBoundedPolynomialSM9e.coefficientAt
          sourceSM9g1Ledger.sourceSM9gGate.regularCoefficientSource 1 -
          (ExecComplex.ofRat 4) *
            OperationalBoundedPolynomialSM9e.coefficientAt
              sourceSM9g1Ledger.sourceSM9gGate.regularCoefficientSource 2 *
              OperationalBoundedPolynomialSM9e.coefficientAt
                sourceSM9g1Ledger.sourceSM9gGate.regularCoefficientSource 0
  regularDiscriminantValue_eq_operationalRecurrenceWindowFormula :
    regularDiscriminantSource.discriminantValue =
      OperationalBoundedPolynomialSM9e.coefficientAt
          (operationalDeterminantCoefficientRecurrenceSM9e
            sourceSM9g1Ledger.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.degreeBound
            sourceSM9g1Ledger.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.sourceSM9d.matrix) 1 *
        OperationalBoundedPolynomialSM9e.coefficientAt
          (operationalDeterminantCoefficientRecurrenceSM9e
            sourceSM9g1Ledger.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.degreeBound
            sourceSM9g1Ledger.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.sourceSM9d.matrix) 1 -
          (ExecComplex.ofRat 4) *
            OperationalBoundedPolynomialSM9e.coefficientAt
              (operationalDeterminantCoefficientRecurrenceSM9e
                sourceSM9g1Ledger.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.degreeBound
                sourceSM9g1Ledger.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.sourceSM9d.matrix) 2 *
              OperationalBoundedPolynomialSM9e.coefficientAt
                (operationalDeterminantCoefficientRecurrenceSM9e
                  sourceSM9g1Ledger.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.degreeBound
                  sourceSM9g1Ledger.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.sourceSM9d.matrix) 0
  variableDiscriminantSource :
    OperationalQuadraticDiscriminantSourceSM9h
      sourceSM9g1Ledger.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.degreeBound
  variableSourceWindow_eq_SM9g1Window :
    variableDiscriminantSource.sourceWindow = sourceSM9g1Ledger.variableWindow
  variableDiscriminantValue_eq_windowFormula :
    variableDiscriminantSource.discriminantValue =
      variableDiscriminantSource.sourceWindow.linearCoeff *
        variableDiscriminantSource.sourceWindow.linearCoeff -
          (ExecComplex.ofRat 4) * variableDiscriminantSource.sourceWindow.quadraticCoeff *
            variableDiscriminantSource.sourceWindow.constantCoeff
  variableDiscriminantValue_eq_SM9g1WindowFormula :
    variableDiscriminantSource.discriminantValue =
      sourceSM9g1Ledger.variableWindow.linearCoeff * sourceSM9g1Ledger.variableWindow.linearCoeff -
        (ExecComplex.ofRat 4) * sourceSM9g1Ledger.variableWindow.quadraticCoeff *
          sourceSM9g1Ledger.variableWindow.constantCoeff
  variableDiscriminantValue_eq_SM9gCoefficientWindowFormula :
    variableDiscriminantSource.discriminantValue =
      OperationalBoundedPolynomialSM9e.coefficientAt
          sourceSM9g1Ledger.sourceSM9gGate.variableCoefficientSource 1 *
        OperationalBoundedPolynomialSM9e.coefficientAt
          sourceSM9g1Ledger.sourceSM9gGate.variableCoefficientSource 1 -
          (ExecComplex.ofRat 4) *
            OperationalBoundedPolynomialSM9e.coefficientAt
              sourceSM9g1Ledger.sourceSM9gGate.variableCoefficientSource 2 *
              OperationalBoundedPolynomialSM9e.coefficientAt
                sourceSM9g1Ledger.sourceSM9gGate.variableCoefficientSource 0
  variableDiscriminantValue_eq_operationalRecurrenceWindowFormula :
    variableDiscriminantSource.discriminantValue =
      OperationalBoundedPolynomialSM9e.coefficientAt
          (operationalDeterminantCoefficientRecurrenceSM9e
            sourceSM9g1Ledger.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.degreeBound
            sourceSM9g1Ledger.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.sourceSM9d.matrix) 1 *
        OperationalBoundedPolynomialSM9e.coefficientAt
          (operationalDeterminantCoefficientRecurrenceSM9e
            sourceSM9g1Ledger.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.degreeBound
            sourceSM9g1Ledger.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.sourceSM9d.matrix) 1 -
          (ExecComplex.ofRat 4) *
            OperationalBoundedPolynomialSM9e.coefficientAt
              (operationalDeterminantCoefficientRecurrenceSM9e
                sourceSM9g1Ledger.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.degreeBound
                sourceSM9g1Ledger.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.sourceSM9d.matrix) 2 *
              OperationalBoundedPolynomialSM9e.coefficientAt
                (operationalDeterminantCoefficientRecurrenceSM9e
                  sourceSM9g1Ledger.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.degreeBound
                  sourceSM9g1Ledger.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.sourceSM9d.matrix) 0
  discriminantSourceStatus : SM9hOperationalDiscriminantSourceStatus
  discriminantSourceStatus_eq :
    discriminantSourceStatus =
      SM9hOperationalDiscriminantSourceStatus.discriminantSourceValidatedFromSM9g1Window
  noFreeDiscriminantTableStatus : SM9hNoFreeDiscriminantTableStatus
  noFreeDiscriminantTableStatus_eq :
    noFreeDiscriminantTableStatus = SM9hNoFreeDiscriminantTableStatus.noFreeDiscriminantTable
  noFreeFactorFormStatus : SM9gNoFreeFactorFormStatus
  noFreeFactorFormStatus_eq : noFreeFactorFormStatus = SM9gNoFreeFactorFormStatus.noFreeFactorForm
  noFactorProofStatus : SM9hNoFactorProofStatus
  noFactorProofStatus_eq : noFactorProofStatus = SM9hNoFactorProofStatus.noFactorProof
  noFundamentalDiscriminantConventionBridgeStatus :
    SM9hNoFundamentalDiscriminantConventionBridgeStatus
  noFundamentalDiscriminantConventionBridgeStatus_eq :
    noFundamentalDiscriminantConventionBridgeStatus =
      SM9hNoFundamentalDiscriminantConventionBridgeStatus.noFundamentalDiscriminantConventionBridge
  noFreeTargetValueStatus : SM9gNoFreeTargetValueStatus
  noFreeTargetValueStatus_eq : noFreeTargetValueStatus = SM9gNoFreeTargetValueStatus.noFreeTargetValue
  noComparisonTargetStatus : SM9hNoComparisonTargetStatus
  noComparisonTargetStatus_eq : noComparisonTargetStatus = SM9hNoComparisonTargetStatus.noComparisonTarget
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
  noClassicalStatus : SM9hNoClassicalStatus
  noClassicalStatus_eq :
    noClassicalStatus = SM9hNoClassicalStatus.noClassicalInOperationalDiscriminantSource
  nextPhaseStatus : SM9hNextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus = SM9hNextPhaseStatus.sm10MayConsumeOperationalDiscriminantSource

def sm9hGeneratedOperationalQuadraticDiscriminantSourceLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9g1GeneratedOperationalQuadraticCoefficientWindowLedger
      b β p regularWeight variableWeight z) :
    SM9hGeneratedOperationalQuadraticDiscriminantSourceLedger
      b β p regularWeight variableWeight z :=
  let RS := OperationalQuadraticDiscriminantSourceSM9h.fromWindow L.regularWindow
  let VS := OperationalQuadraticDiscriminantSourceSM9h.fromWindow L.variableWindow
  { sourceSM9g1Ledger := L
    sourceSM9g1Ledger_nextPhase_eq := L.nextPhaseStatus_eq
    regularDiscriminantSource := RS
    regularSourceWindow_eq_SM9g1Window := by
      rfl
    regularDiscriminantValue_eq_windowFormula := by
      exact RS.discriminantValue_eq_windowFormula
    regularDiscriminantValue_eq_SM9g1WindowFormula := by
      rfl
    regularDiscriminantValue_eq_SM9gCoefficientWindowFormula := by
      calc
        RS.discriminantValue =
            L.regularWindow.linearCoeff * L.regularWindow.linearCoeff -
              (ExecComplex.ofRat 4) * L.regularWindow.quadraticCoeff *
                L.regularWindow.constantCoeff := by
          rfl
        _ = OperationalBoundedPolynomialSM9e.coefficientAt L.sourceSM9gGate.regularCoefficientSource 1 *
              OperationalBoundedPolynomialSM9e.coefficientAt L.sourceSM9gGate.regularCoefficientSource 1 -
              (ExecComplex.ofRat 4) *
                OperationalBoundedPolynomialSM9e.coefficientAt L.sourceSM9gGate.regularCoefficientSource 2 *
                  OperationalBoundedPolynomialSM9e.coefficientAt L.sourceSM9gGate.regularCoefficientSource 0 := by
          rw [L.regularLinearCoeff_eq_SM9gCoefficientAt,
            L.regularQuadraticCoeff_eq_SM9gCoefficientAt,
            L.regularConstantCoeff_eq_SM9gCoefficientAt]
    regularDiscriminantValue_eq_operationalRecurrenceWindowFormula := by
      calc
        RS.discriminantValue =
            L.regularWindow.linearCoeff * L.regularWindow.linearCoeff -
              (ExecComplex.ofRat 4) * L.regularWindow.quadraticCoeff *
                L.regularWindow.constantCoeff := by
          rfl
        _ = OperationalBoundedPolynomialSM9e.coefficientAt
              (operationalDeterminantCoefficientRecurrenceSM9e
                L.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.degreeBound
                L.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.sourceSM9d.matrix) 1 *
              OperationalBoundedPolynomialSM9e.coefficientAt
                (operationalDeterminantCoefficientRecurrenceSM9e
                  L.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.degreeBound
                  L.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.sourceSM9d.matrix) 1 -
                (ExecComplex.ofRat 4) *
                  OperationalBoundedPolynomialSM9e.coefficientAt
                    (operationalDeterminantCoefficientRecurrenceSM9e
                      L.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.degreeBound
                      L.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.sourceSM9d.matrix) 2 *
                    OperationalBoundedPolynomialSM9e.coefficientAt
                      (operationalDeterminantCoefficientRecurrenceSM9e
                        L.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.degreeBound
                        L.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.sourceSM9d.matrix) 0 := by
          rw [L.regularLinearCoeff_eq_operationalRecurrence,
            L.regularQuadraticCoeff_eq_operationalRecurrence,
            L.regularConstantCoeff_eq_operationalRecurrence]
    variableDiscriminantSource := VS
    variableSourceWindow_eq_SM9g1Window := by
      rfl
    variableDiscriminantValue_eq_windowFormula := by
      exact VS.discriminantValue_eq_windowFormula
    variableDiscriminantValue_eq_SM9g1WindowFormula := by
      rfl
    variableDiscriminantValue_eq_SM9gCoefficientWindowFormula := by
      calc
        VS.discriminantValue =
            L.variableWindow.linearCoeff * L.variableWindow.linearCoeff -
              (ExecComplex.ofRat 4) * L.variableWindow.quadraticCoeff *
                L.variableWindow.constantCoeff := by
          rfl
        _ = OperationalBoundedPolynomialSM9e.coefficientAt L.sourceSM9gGate.variableCoefficientSource 1 *
              OperationalBoundedPolynomialSM9e.coefficientAt L.sourceSM9gGate.variableCoefficientSource 1 -
              (ExecComplex.ofRat 4) *
                OperationalBoundedPolynomialSM9e.coefficientAt L.sourceSM9gGate.variableCoefficientSource 2 *
                  OperationalBoundedPolynomialSM9e.coefficientAt L.sourceSM9gGate.variableCoefficientSource 0 := by
          rw [L.variableLinearCoeff_eq_SM9gCoefficientAt,
            L.variableQuadraticCoeff_eq_SM9gCoefficientAt,
            L.variableConstantCoeff_eq_SM9gCoefficientAt]
    variableDiscriminantValue_eq_operationalRecurrenceWindowFormula := by
      calc
        VS.discriminantValue =
            L.variableWindow.linearCoeff * L.variableWindow.linearCoeff -
              (ExecComplex.ofRat 4) * L.variableWindow.quadraticCoeff *
                L.variableWindow.constantCoeff := by
          rfl
        _ = OperationalBoundedPolynomialSM9e.coefficientAt
              (operationalDeterminantCoefficientRecurrenceSM9e
                L.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.degreeBound
                L.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.sourceSM9d.matrix) 1 *
              OperationalBoundedPolynomialSM9e.coefficientAt
                (operationalDeterminantCoefficientRecurrenceSM9e
                  L.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.degreeBound
                  L.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.sourceSM9d.matrix) 1 -
                (ExecComplex.ofRat 4) *
                  OperationalBoundedPolynomialSM9e.coefficientAt
                    (operationalDeterminantCoefficientRecurrenceSM9e
                      L.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.degreeBound
                      L.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.sourceSM9d.matrix) 2 *
                    OperationalBoundedPolynomialSM9e.coefficientAt
                      (operationalDeterminantCoefficientRecurrenceSM9e
                        L.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.degreeBound
                        L.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.sourceSM9d.matrix) 0 := by
          rw [L.variableLinearCoeff_eq_operationalRecurrence,
            L.variableQuadraticCoeff_eq_operationalRecurrence,
            L.variableConstantCoeff_eq_operationalRecurrence]
    discriminantSourceStatus :=
      SM9hOperationalDiscriminantSourceStatus.discriminantSourceValidatedFromSM9g1Window
    discriminantSourceStatus_eq := by
      rfl
    noFreeDiscriminantTableStatus := SM9hNoFreeDiscriminantTableStatus.noFreeDiscriminantTable
    noFreeDiscriminantTableStatus_eq := by
      rfl
    noFreeFactorFormStatus := SM9gNoFreeFactorFormStatus.noFreeFactorForm
    noFreeFactorFormStatus_eq := by
      rfl
    noFactorProofStatus := SM9hNoFactorProofStatus.noFactorProof
    noFactorProofStatus_eq := by
      rfl
    noFundamentalDiscriminantConventionBridgeStatus :=
      SM9hNoFundamentalDiscriminantConventionBridgeStatus.noFundamentalDiscriminantConventionBridge
    noFundamentalDiscriminantConventionBridgeStatus_eq := by
      rfl
    noFreeTargetValueStatus := SM9gNoFreeTargetValueStatus.noFreeTargetValue
    noFreeTargetValueStatus_eq := by
      rfl
    noComparisonTargetStatus := SM9hNoComparisonTargetStatus.noComparisonTarget
    noComparisonTargetStatus_eq := by
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
      rfl
    noClassicalStatus := SM9hNoClassicalStatus.noClassicalInOperationalDiscriminantSource
    noClassicalStatus_eq := by
      rfl
    nextPhaseStatus := SM9hNextPhaseStatus.sm10MayConsumeOperationalDiscriminantSource
    nextPhaseStatus_eq := by
      rfl }

def sm9hGeneratedOperationalQuadraticDiscriminantSourceLedger_from_SM9eLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9eGeneratedOperationalDeterminantCoefficientRecurrenceLedger
      b β p regularWeight variableWeight z) :
    SM9hGeneratedOperationalQuadraticDiscriminantSourceLedger
      b β p regularWeight variableWeight z :=
  sm9hGeneratedOperationalQuadraticDiscriminantSourceLedger
    (sm9g1GeneratedOperationalQuadraticCoefficientWindowLedger_from_SM9eLedger L)

theorem sm9h_regularDiscriminantValue_from_SM9g1WindowFormula
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9hGeneratedOperationalQuadraticDiscriminantSourceLedger
      b β p regularWeight variableWeight z) :
    L.regularDiscriminantSource.discriminantValue =
      L.sourceSM9g1Ledger.regularWindow.linearCoeff *
        L.sourceSM9g1Ledger.regularWindow.linearCoeff -
          (ExecComplex.ofRat 4) * L.sourceSM9g1Ledger.regularWindow.quadraticCoeff *
            L.sourceSM9g1Ledger.regularWindow.constantCoeff :=
  L.regularDiscriminantValue_eq_SM9g1WindowFormula

theorem sm9h_variableDiscriminantValue_from_SM9g1WindowFormula
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9hGeneratedOperationalQuadraticDiscriminantSourceLedger
      b β p regularWeight variableWeight z) :
    L.variableDiscriminantSource.discriminantValue =
      L.sourceSM9g1Ledger.variableWindow.linearCoeff *
        L.sourceSM9g1Ledger.variableWindow.linearCoeff -
          (ExecComplex.ofRat 4) * L.sourceSM9g1Ledger.variableWindow.quadraticCoeff *
            L.sourceSM9g1Ledger.variableWindow.constantCoeff :=
  L.variableDiscriminantValue_eq_SM9g1WindowFormula

theorem sm9h_regularDiscriminantValue_from_operationalRecurrenceWindow
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9hGeneratedOperationalQuadraticDiscriminantSourceLedger
      b β p regularWeight variableWeight z) :
    L.regularDiscriminantSource.discriminantValue =
      OperationalBoundedPolynomialSM9e.coefficientAt
          (operationalDeterminantCoefficientRecurrenceSM9e
            L.sourceSM9g1Ledger.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.degreeBound
            L.sourceSM9g1Ledger.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.sourceSM9d.matrix) 1 *
        OperationalBoundedPolynomialSM9e.coefficientAt
          (operationalDeterminantCoefficientRecurrenceSM9e
            L.sourceSM9g1Ledger.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.degreeBound
            L.sourceSM9g1Ledger.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.sourceSM9d.matrix) 1 -
          (ExecComplex.ofRat 4) *
            OperationalBoundedPolynomialSM9e.coefficientAt
              (operationalDeterminantCoefficientRecurrenceSM9e
                L.sourceSM9g1Ledger.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.degreeBound
                L.sourceSM9g1Ledger.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.sourceSM9d.matrix) 2 *
              OperationalBoundedPolynomialSM9e.coefficientAt
                (operationalDeterminantCoefficientRecurrenceSM9e
                  L.sourceSM9g1Ledger.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.degreeBound
                  L.sourceSM9g1Ledger.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.sourceSM9d.matrix) 0 :=
  L.regularDiscriminantValue_eq_operationalRecurrenceWindowFormula

theorem sm9h_variableDiscriminantValue_from_operationalRecurrenceWindow
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9hGeneratedOperationalQuadraticDiscriminantSourceLedger
      b β p regularWeight variableWeight z) :
    L.variableDiscriminantSource.discriminantValue =
      OperationalBoundedPolynomialSM9e.coefficientAt
          (operationalDeterminantCoefficientRecurrenceSM9e
            L.sourceSM9g1Ledger.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.degreeBound
            L.sourceSM9g1Ledger.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.sourceSM9d.matrix) 1 *
        OperationalBoundedPolynomialSM9e.coefficientAt
          (operationalDeterminantCoefficientRecurrenceSM9e
            L.sourceSM9g1Ledger.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.degreeBound
            L.sourceSM9g1Ledger.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.sourceSM9d.matrix) 1 -
          (ExecComplex.ofRat 4) *
            OperationalBoundedPolynomialSM9e.coefficientAt
              (operationalDeterminantCoefficientRecurrenceSM9e
                L.sourceSM9g1Ledger.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.degreeBound
                L.sourceSM9g1Ledger.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.sourceSM9d.matrix) 2 *
              OperationalBoundedPolynomialSM9e.coefficientAt
                (operationalDeterminantCoefficientRecurrenceSM9e
                  L.sourceSM9g1Ledger.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.degreeBound
                  L.sourceSM9g1Ledger.sourceSM9gGate.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.sourceSM9d.matrix) 0 :=
  L.variableDiscriminantValue_eq_operationalRecurrenceWindowFormula

theorem sm9h_discriminantSourceValidatedFromSM9g1Window
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9hGeneratedOperationalQuadraticDiscriminantSourceLedger
      b β p regularWeight variableWeight z) :
    L.discriminantSourceStatus =
      SM9hOperationalDiscriminantSourceStatus.discriminantSourceValidatedFromSM9g1Window :=
  L.discriminantSourceStatus_eq

theorem sm9h_noFreeTargetOrComparisonConsumer
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9hGeneratedOperationalQuadraticDiscriminantSourceLedger
      b β p regularWeight variableWeight z) :
    L.noFreeDiscriminantTableStatus = SM9hNoFreeDiscriminantTableStatus.noFreeDiscriminantTable ∧
    L.noFreeFactorFormStatus = SM9gNoFreeFactorFormStatus.noFreeFactorForm ∧
    L.noFactorProofStatus = SM9hNoFactorProofStatus.noFactorProof ∧
    L.noFundamentalDiscriminantConventionBridgeStatus =
      SM9hNoFundamentalDiscriminantConventionBridgeStatus.noFundamentalDiscriminantConventionBridge ∧
    L.noFreeTargetValueStatus = SM9gNoFreeTargetValueStatus.noFreeTargetValue ∧
    L.noComparisonTargetStatus = SM9hNoComparisonTargetStatus.noComparisonTarget ∧
    L.noExternalComparisonMatrixStatus =
      SM9gNoExternalComparisonMatrixStatus.noExternalComparisonMatrix :=
  ⟨L.noFreeDiscriminantTableStatus_eq, L.noFreeFactorFormStatus_eq,
    L.noFactorProofStatus_eq, L.noFundamentalDiscriminantConventionBridgeStatus_eq,
    L.noFreeTargetValueStatus_eq, L.noComparisonTargetStatus_eq,
    L.noExternalComparisonMatrixStatus_eq⟩

theorem sm9h_noForbiddenOperationalAlgebra
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9hGeneratedOperationalQuadraticDiscriminantSourceLedger
      b β p regularWeight variableWeight z) :
    L.noPolynomialSemiringRuntimeStatus =
      SM9eNoPolynomialSemiringRuntimeStatus.noPolynomialSemiringRuntime ∧
    L.noMathlibPolynomialOperationalPathStatus =
      SM9eNoMathlibPolynomialOperationalPathStatus.noMathlibPolynomialOperationalPath ∧
    L.noMatrixInvStatus = SM9fNoMatrixInvStatus.noMatrixInv ∧
    L.noFieldSimpStatus = SM9fNoFieldSimpStatus.noFieldSimp ∧
    L.noScalarInvStatus = SM9fNoScalarInvStatus.noScalarInv ∧
    L.noNoncomputableOperationalSourceStatus =
      SM9fNoNoncomputableOperationalSourceStatus.noNoncomputableOperationalSource ∧
    L.noClassicalStatus = SM9hNoClassicalStatus.noClassicalInOperationalDiscriminantSource :=
  ⟨L.noPolynomialSemiringRuntimeStatus_eq,
    L.noMathlibPolynomialOperationalPathStatus_eq,
    L.noMatrixInvStatus_eq, L.noFieldSimpStatus_eq, L.noScalarInvStatus_eq,
    L.noNoncomputableOperationalSourceStatus_eq, L.noClassicalStatus_eq⟩

theorem sm9h_nextPhase_eq_sm10MayConsumeOperationalDiscriminantSource
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9hGeneratedOperationalQuadraticDiscriminantSourceLedger
      b β p regularWeight variableWeight z) :
    L.nextPhaseStatus = SM9hNextPhaseStatus.sm10MayConsumeOperationalDiscriminantSource :=
  L.nextPhaseStatus_eq

end Smoke

end CNNA.PillarA.Arithmetic
