import CNNA.PillarA.Arithmetic.Smoke.GeneratedOperationalDeterminantForwardEvaluationBridgeFromSM9ePlus

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.DtN

namespace Smoke

inductive SM9gDeterminantSourceStatus where
  | validatedFromSM9fFullForwardBridge
  deriving DecidableEq, Repr

inductive SM9gCoefficientSourceStatus where
  | validatedFromSM9dSM9eOperationalRecurrence
  deriving DecidableEq, Repr

inductive SM9gQuadraticCoefficientWindowStatus where
  | missingConsumableWindowFromValidatedCoefficients
  deriving DecidableEq, Repr

inductive SM9gFactorSourcePolicyStatus where
  | factorSourceMustBeDerivedFromValidatedCoefficients
  deriving DecidableEq, Repr

inductive SM9gDiscriminantSourcePolicyStatus where
  | discriminantSourceMustBeDerivedFromValidatedFactorOrQuadraticCoefficientWindow
  deriving DecidableEq, Repr

inductive SM9gSM10ReleaseStatus where
  | sm10L2ComparisonBlockedUntilGateSourceIsConsumable
  deriving DecidableEq, Repr

inductive SM9gNextPhaseStatus where
  | operationalQuadraticCoefficientWindowFromSM9dSM9e
  deriving DecidableEq, Repr

inductive SM9gNoFreeFactorFormStatus where
  | noFreeFactorForm
  deriving DecidableEq, Repr

inductive SM9gNoFreeDiscriminantStatus where
  | noFreeDiscriminant
  deriving DecidableEq, Repr

inductive SM9gNoFreeTargetValueStatus where
  | noFreeTargetValue
  deriving DecidableEq, Repr

inductive SM9gNoExternalComparisonMatrixStatus where
  | noExternalComparisonMatrix
  deriving DecidableEq, Repr

inductive SM9gNoEisensteinGaussHeegnerCMJConsumerStatus where
  | noEisensteinGaussHeegnerCMJConsumer
  deriving DecidableEq, Repr

inductive SM9gNoNewMatrixStatus where
  | noNewMatrix
  deriving DecidableEq, Repr

inductive SM9gNoNewDeterminantRecurrenceStatus where
  | noNewDeterminantRecurrence
  deriving DecidableEq, Repr

inductive SM9gNoCharpolyRecomputationStatus where
  | noCharpolyRecomputation
  deriving DecidableEq, Repr

inductive SM9gNoTwoSidedInvStatus where
  | noTwoSidedInv
  deriving DecidableEq, Repr

structure SM9gGeneratedOperationalDiscriminantFactorGateLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (z : Schur.SpectralParameter) where
  sourceSM9fFullLedger :
    SM9fFullGeneratedOperationalDeterminantForwardEvaluationBridgeLedger
      b β p regularWeight variableWeight z
  regularDeterminantSource : ExecComplex
  regularDeterminantSource_eq_SM9fFull :
    regularDeterminantSource = sourceSM9fFullLedger.regularBridge.forwardEvaluationAtSource
  regularDeterminantSource_eq_SM9cDetPencil :
    regularDeterminantSource =
      Matrix.det sourceSM9fFullLedger.regularBridge.sourceSM9fRequirement.sourceSM9e.sourceSM9d.sourceSM9c.spectralPencilAtSource
  variableDeterminantSource : ExecComplex
  variableDeterminantSource_eq_SM9fFull :
    variableDeterminantSource = sourceSM9fFullLedger.variableBridge.forwardEvaluationAtSource
  variableDeterminantSource_eq_SM9cDetPencil :
    variableDeterminantSource =
      Matrix.det sourceSM9fFullLedger.variableBridge.sourceSM9fRequirement.sourceSM9e.sourceSM9d.sourceSM9c.spectralPencilAtSource
  regularCoefficientSource :
    OperationalBoundedPolynomialSM9e
      sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.degreeBound
  regularCoefficientSource_eq_SM9e :
    regularCoefficientSource =
      sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.coefficientPolynomial
  regularCoefficientSource_eq_operationalRecurrence :
    regularCoefficientSource =
      operationalDeterminantCoefficientRecurrenceSM9e
        sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.degreeBound
        sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.sourceSM9d.matrix
  variableCoefficientSource :
    OperationalBoundedPolynomialSM9e
      sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.degreeBound
  variableCoefficientSource_eq_SM9e :
    variableCoefficientSource =
      sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.coefficientPolynomial
  variableCoefficientSource_eq_operationalRecurrence :
    variableCoefficientSource =
      operationalDeterminantCoefficientRecurrenceSM9e
        sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.degreeBound
        sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.sourceSM9d.matrix
  determinantSourceStatus : SM9gDeterminantSourceStatus
  determinantSourceStatus_eq :
    determinantSourceStatus = SM9gDeterminantSourceStatus.validatedFromSM9fFullForwardBridge
  coefficientSourceStatus : SM9gCoefficientSourceStatus
  coefficientSourceStatus_eq :
    coefficientSourceStatus = SM9gCoefficientSourceStatus.validatedFromSM9dSM9eOperationalRecurrence
  quadraticCoefficientWindowStatus : SM9gQuadraticCoefficientWindowStatus
  quadraticCoefficientWindowStatus_eq :
    quadraticCoefficientWindowStatus =
      SM9gQuadraticCoefficientWindowStatus.missingConsumableWindowFromValidatedCoefficients
  factorSourcePolicyStatus : SM9gFactorSourcePolicyStatus
  factorSourcePolicyStatus_eq :
    factorSourcePolicyStatus =
      SM9gFactorSourcePolicyStatus.factorSourceMustBeDerivedFromValidatedCoefficients
  discriminantSourcePolicyStatus : SM9gDiscriminantSourcePolicyStatus
  discriminantSourcePolicyStatus_eq :
    discriminantSourcePolicyStatus =
      SM9gDiscriminantSourcePolicyStatus.discriminantSourceMustBeDerivedFromValidatedFactorOrQuadraticCoefficientWindow
  sm10ReleaseStatus : SM9gSM10ReleaseStatus
  sm10ReleaseStatus_eq :
    sm10ReleaseStatus =
      SM9gSM10ReleaseStatus.sm10L2ComparisonBlockedUntilGateSourceIsConsumable
  nextPhaseStatus : SM9gNextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus = SM9gNextPhaseStatus.operationalQuadraticCoefficientWindowFromSM9dSM9e
  noFreeFactorFormStatus : SM9gNoFreeFactorFormStatus
  noFreeFactorFormStatus_eq :
    noFreeFactorFormStatus = SM9gNoFreeFactorFormStatus.noFreeFactorForm
  noFreeDiscriminantStatus : SM9gNoFreeDiscriminantStatus
  noFreeDiscriminantStatus_eq :
    noFreeDiscriminantStatus = SM9gNoFreeDiscriminantStatus.noFreeDiscriminant
  noFreeTargetValueStatus : SM9gNoFreeTargetValueStatus
  noFreeTargetValueStatus_eq :
    noFreeTargetValueStatus = SM9gNoFreeTargetValueStatus.noFreeTargetValue
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

def sm9gGeneratedOperationalDiscriminantFactorGateLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9fFullGeneratedOperationalDeterminantForwardEvaluationBridgeLedger
      b β p regularWeight variableWeight z) :
    SM9gGeneratedOperationalDiscriminantFactorGateLedger b β p regularWeight variableWeight z :=
  let R := L.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence
  let V := L.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence
  { sourceSM9fFullLedger := L
    regularDeterminantSource := L.regularBridge.forwardEvaluationAtSource
    regularDeterminantSource_eq_SM9fFull := by
      rfl
    regularDeterminantSource_eq_SM9cDetPencil := by
      exact L.regularForwardEvaluationAtSource_eq_SM9cDetPencil
    variableDeterminantSource := L.variableBridge.forwardEvaluationAtSource
    variableDeterminantSource_eq_SM9fFull := by
      rfl
    variableDeterminantSource_eq_SM9cDetPencil := by
      exact L.variableForwardEvaluationAtSource_eq_SM9cDetPencil
    regularCoefficientSource := R.coefficientPolynomial
    regularCoefficientSource_eq_SM9e := by
      rfl
    regularCoefficientSource_eq_operationalRecurrence := by
      exact R.coefficients_source_eq_linearPencil
    variableCoefficientSource := V.coefficientPolynomial
    variableCoefficientSource_eq_SM9e := by
      rfl
    variableCoefficientSource_eq_operationalRecurrence := by
      exact V.coefficients_source_eq_linearPencil
    determinantSourceStatus := SM9gDeterminantSourceStatus.validatedFromSM9fFullForwardBridge
    determinantSourceStatus_eq := by
      rfl
    coefficientSourceStatus := SM9gCoefficientSourceStatus.validatedFromSM9dSM9eOperationalRecurrence
    coefficientSourceStatus_eq := by
      rfl
    quadraticCoefficientWindowStatus :=
      SM9gQuadraticCoefficientWindowStatus.missingConsumableWindowFromValidatedCoefficients
    quadraticCoefficientWindowStatus_eq := by
      rfl
    factorSourcePolicyStatus :=
      SM9gFactorSourcePolicyStatus.factorSourceMustBeDerivedFromValidatedCoefficients
    factorSourcePolicyStatus_eq := by
      rfl
    discriminantSourcePolicyStatus :=
      SM9gDiscriminantSourcePolicyStatus.discriminantSourceMustBeDerivedFromValidatedFactorOrQuadraticCoefficientWindow
    discriminantSourcePolicyStatus_eq := by
      rfl
    sm10ReleaseStatus :=
      SM9gSM10ReleaseStatus.sm10L2ComparisonBlockedUntilGateSourceIsConsumable
    sm10ReleaseStatus_eq := by
      rfl
    nextPhaseStatus := SM9gNextPhaseStatus.operationalQuadraticCoefficientWindowFromSM9dSM9e
    nextPhaseStatus_eq := by
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
    noNewDeterminantRecurrenceStatus :=
      SM9gNoNewDeterminantRecurrenceStatus.noNewDeterminantRecurrence
    noNewDeterminantRecurrenceStatus_eq := by
      rfl
    noCharpolyRecomputationStatus := SM9gNoCharpolyRecomputationStatus.noCharpolyRecomputation
    noCharpolyRecomputationStatus_eq := by
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

def sm9gGeneratedOperationalDiscriminantFactorGateLedger_from_SM9eLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9eGeneratedOperationalDeterminantCoefficientRecurrenceLedger
      b β p regularWeight variableWeight z) :
    SM9gGeneratedOperationalDiscriminantFactorGateLedger b β p regularWeight variableWeight z :=
  sm9gGeneratedOperationalDiscriminantFactorGateLedger
    (sm9fFullGeneratedOperationalDeterminantForwardEvaluationBridgeLedger_from_SM9eLedger L)

theorem sm9g_regularDeterminantSource_eq_SM9cDetPencil
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9gGeneratedOperationalDiscriminantFactorGateLedger
      b β p regularWeight variableWeight z) :
    L.regularDeterminantSource =
      Matrix.det L.sourceSM9fFullLedger.regularBridge.sourceSM9fRequirement.sourceSM9e.sourceSM9d.sourceSM9c.spectralPencilAtSource :=
  L.regularDeterminantSource_eq_SM9cDetPencil

theorem sm9g_variableDeterminantSource_eq_SM9cDetPencil
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9gGeneratedOperationalDiscriminantFactorGateLedger
      b β p regularWeight variableWeight z) :
    L.variableDeterminantSource =
      Matrix.det L.sourceSM9fFullLedger.variableBridge.sourceSM9fRequirement.sourceSM9e.sourceSM9d.sourceSM9c.spectralPencilAtSource :=
  L.variableDeterminantSource_eq_SM9cDetPencil

theorem sm9g_regularCoefficientSource_eq_operationalRecurrence
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9gGeneratedOperationalDiscriminantFactorGateLedger
      b β p regularWeight variableWeight z) :
    L.regularCoefficientSource =
      operationalDeterminantCoefficientRecurrenceSM9e
        L.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.degreeBound
        L.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.regularRecurrence.sourceSM9d.matrix :=
  L.regularCoefficientSource_eq_operationalRecurrence

theorem sm9g_variableCoefficientSource_eq_operationalRecurrence
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9gGeneratedOperationalDiscriminantFactorGateLedger
      b β p regularWeight variableWeight z) :
    L.variableCoefficientSource =
      operationalDeterminantCoefficientRecurrenceSM9e
        L.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.degreeBound
        L.sourceSM9fFullLedger.sourceSM9fRequirementLedger.sourceSM9eLedger.variableRecurrence.sourceSM9d.matrix :=
  L.variableCoefficientSource_eq_operationalRecurrence

theorem sm9g_factorSourceMustBeDerivedFromValidatedCoefficients
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9gGeneratedOperationalDiscriminantFactorGateLedger
      b β p regularWeight variableWeight z) :
    L.factorSourcePolicyStatus =
      SM9gFactorSourcePolicyStatus.factorSourceMustBeDerivedFromValidatedCoefficients :=
  L.factorSourcePolicyStatus_eq

theorem sm9g_discriminantSourceMustBeDerivedFromValidatedFactorOrQuadraticCoefficientWindow
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9gGeneratedOperationalDiscriminantFactorGateLedger
      b β p regularWeight variableWeight z) :
    L.discriminantSourcePolicyStatus =
      SM9gDiscriminantSourcePolicyStatus.discriminantSourceMustBeDerivedFromValidatedFactorOrQuadraticCoefficientWindow :=
  L.discriminantSourcePolicyStatus_eq

theorem sm9g_sm10BlockedUntilGateSourceIsConsumable
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9gGeneratedOperationalDiscriminantFactorGateLedger
      b β p regularWeight variableWeight z) :
    L.sm10ReleaseStatus =
      SM9gSM10ReleaseStatus.sm10L2ComparisonBlockedUntilGateSourceIsConsumable :=
  L.sm10ReleaseStatus_eq

theorem sm9g_nextPhase_eq_operationalQuadraticCoefficientWindow
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9gGeneratedOperationalDiscriminantFactorGateLedger
      b β p regularWeight variableWeight z) :
    L.nextPhaseStatus = SM9gNextPhaseStatus.operationalQuadraticCoefficientWindowFromSM9dSM9e :=
  L.nextPhaseStatus_eq

theorem sm9g_noFreeFactorOrDiscriminant
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    {z : Schur.SpectralParameter}
    (L : SM9gGeneratedOperationalDiscriminantFactorGateLedger
      b β p regularWeight variableWeight z) :
    L.noFreeFactorFormStatus = SM9gNoFreeFactorFormStatus.noFreeFactorForm ∧
    L.noFreeDiscriminantStatus = SM9gNoFreeDiscriminantStatus.noFreeDiscriminant ∧
    L.noFreeTargetValueStatus = SM9gNoFreeTargetValueStatus.noFreeTargetValue ∧
    L.noExternalComparisonMatrixStatus =
      SM9gNoExternalComparisonMatrixStatus.noExternalComparisonMatrix :=
  ⟨L.noFreeFactorFormStatus_eq, L.noFreeDiscriminantStatus_eq,
    L.noFreeTargetValueStatus_eq, L.noExternalComparisonMatrixStatus_eq⟩

end Smoke

end CNNA.PillarA.Arithmetic
