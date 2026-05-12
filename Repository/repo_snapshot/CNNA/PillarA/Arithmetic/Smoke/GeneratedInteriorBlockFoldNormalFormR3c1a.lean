import CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorAccumulatedTraceEvaluation

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

open scoped BigOperators

namespace Smoke

universe u

inductive SM3eRr3c1aBlockFoldNormalFormStatus where
  | blockFoldNormalFormFromAccumulatedTraceExpansion
  deriving DecidableEq, Repr

inductive SM3eRr3c1aBlockFoldSourceStatus where
  | sourceFromSM3cRInteriorBlockAndSM3db4aRAccumulatedEntry
  deriving DecidableEq, Repr

inductive SM3eRr3c1aNoBlockFoldIdentityStatus where
  | noBlockFoldIdentityInR3c1a
  deriving DecidableEq, Repr

inductive SM3eRr3c1aNoProductIdentityProofStatus where
  | noProductIdentityProofInR3c1a
  deriving DecidableEq, Repr

inductive SM3eRr3c1aNoTwoSidedInvStatus where
  | noTwoSidedInvInR3c1a
  deriving DecidableEq, Repr

inductive SM3eRr3c1aNextPhaseStatus where
  | sm3eRr3c1b0LocalStepSchurCancellationSourceAudit
  deriving DecidableEq, Repr

def generatedInteriorAccumulatedLeftConvolution
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
    {K : GeneratedInteriorEliminationCarrier Cell p A P wp W E}
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K)
    (i j : GeneratedInteriorIndex A) : ℝ :=
  ∑ k : GeneratedInteriorIndex A,
    generatedInteriorBlock W i k * generatedInteriorAccumulatedEntryValue T k j

def generatedInteriorAccumulatedRightConvolution
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
    {K : GeneratedInteriorEliminationCarrier Cell p A P wp W E}
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K)
    (i j : GeneratedInteriorIndex A) : ℝ :=
  ∑ k : GeneratedInteriorIndex A,
    generatedInteriorAccumulatedEntryValue T i k * generatedInteriorBlock W k j

def generatedInteriorLeftBlockFoldKernel
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
    {K : GeneratedInteriorEliminationCarrier Cell p A P wp W E}
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K)
    (i j k : GeneratedInteriorIndex A) : ℝ :=
  generatedInteriorBlock W i k *
    (generatedInteriorTracePivotContribution T k j +
      generatedInteriorTraceLocalStepContribution T k j +
        generatedInteriorTraceResidualContribution T k j +
          generatedInteriorTraceFoldUpdateOrderContribution T k j)

def generatedInteriorRightBlockFoldKernel
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
    {K : GeneratedInteriorEliminationCarrier Cell p A P wp W E}
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K)
    (i j k : GeneratedInteriorIndex A) : ℝ :=
  (generatedInteriorTracePivotContribution T i k +
      generatedInteriorTraceLocalStepContribution T i k +
        generatedInteriorTraceResidualContribution T i k +
          generatedInteriorTraceFoldUpdateOrderContribution T i k) *
    generatedInteriorBlock W k j

def generatedInteriorLeftBlockFold
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
    {K : GeneratedInteriorEliminationCarrier Cell p A P wp W E}
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K)
    (i j : GeneratedInteriorIndex A) : ℝ :=
  ∑ k : GeneratedInteriorIndex A,
    generatedInteriorLeftBlockFoldKernel W T i j k

def generatedInteriorRightBlockFold
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
    {K : GeneratedInteriorEliminationCarrier Cell p A P wp W E}
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K)
    (i j : GeneratedInteriorIndex A) : ℝ :=
  ∑ k : GeneratedInteriorIndex A,
    generatedInteriorRightBlockFoldKernel W T i j k

structure GeneratedInteriorBlockFoldNormalFormR3c1a
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf)
    (A : GeneratedApproximantStrong Cell p)
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    (P : GeneratedBoundaryInteriorPartition Cell p A)
    (wp : WeightPolicy)
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W)
    (K : GeneratedInteriorEliminationCarrier Cell p A P wp W E)
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K) where
  accumulatedTraceEvaluation :
    GeneratedInteriorAccumulatedTraceEvaluation Cell p A P wp W E K T
  accumulatedEntryFold : GeneratedInteriorAccumulatedEntryFold Cell p A P wp W E K T
  normalFormStatus : SM3eRr3c1aBlockFoldNormalFormStatus
  sourceStatus : SM3eRr3c1aBlockFoldSourceStatus
  noBlockFoldIdentityStatus : SM3eRr3c1aNoBlockFoldIdentityStatus
  noProductIdentityProofStatus : SM3eRr3c1aNoProductIdentityProofStatus
  noTwoSidedInvStatus : SM3eRr3c1aNoTwoSidedInvStatus
  noInteriorEliminationCertificateStatus : SM3db4RNoInteriorEliminationCertificateStatus
  noInteriorEliminationDataStatus : SM3db4RNoInteriorEliminationDataStatus
  noDtnDataStatus : SM3db4RNoDtnDataStatus
  noArithmeticTargetStatus : SM3db4RNoArithmeticTargetStatus
  nextPhaseStatus : SM3eRr3c1aNextPhaseStatus
  accumulatedTraceEvaluation_is_fromTrace :
    accumulatedTraceEvaluation =
      GeneratedInteriorAccumulatedTraceEvaluation.fromEliminationTrace T
  accumulatedEntryFold_is_fromTrace :
    accumulatedEntryFold = GeneratedInteriorAccumulatedEntryFold.fromEliminationTrace T
  trace_source_eq_SM3db3R :
    T.sourceStatus =
      SM3db3RTraceSourceStatus.traceFromSM3db1RCarrierAndSM3db2RLocalSteps
  accumulatedTraceSource_eq_SM3db4aR :
    accumulatedTraceEvaluation.sourceStatus =
      SM3db4aRAccumulatedSourceStatus.accumulatedEntryFromSM3db3RTraceAndSM3db2RLocalSteps
  accumulatedFoldSource_eq_SM3db4aR :
    accumulatedEntryFold.sourceStatus =
      SM3db4aRAccumulatedSourceStatus.accumulatedEntryFromSM3db3RTraceAndSM3db2RLocalSteps
  accumulatedEntry_from_components :
    ∀ i j : GeneratedInteriorIndex A,
      accumulatedEntryFold.accumulatedEntry i j =
        generatedInteriorTracePivotContribution T i j +
          generatedInteriorTraceLocalStepContribution T i j +
            generatedInteriorTraceResidualContribution T i j +
              generatedInteriorTraceFoldUpdateOrderContribution T i j
  accumulatedEntry_from_trace :
    ∀ i j : GeneratedInteriorIndex A,
      accumulatedEntryFold.accumulatedEntry i j = generatedInteriorAccumulatedEntryValue T i j
  leftKernel_eq_components :
    ∀ i j k : GeneratedInteriorIndex A,
      generatedInteriorLeftBlockFoldKernel W T i j k =
        generatedInteriorBlock W i k *
          (generatedInteriorTracePivotContribution T k j +
            generatedInteriorTraceLocalStepContribution T k j +
              generatedInteriorTraceResidualContribution T k j +
                generatedInteriorTraceFoldUpdateOrderContribution T k j)
  rightKernel_eq_components :
    ∀ i j k : GeneratedInteriorIndex A,
      generatedInteriorRightBlockFoldKernel W T i j k =
        (generatedInteriorTracePivotContribution T i k +
            generatedInteriorTraceLocalStepContribution T i k +
              generatedInteriorTraceResidualContribution T i k +
                generatedInteriorTraceFoldUpdateOrderContribution T i k) *
          generatedInteriorBlock W k j
  leftBlockFold_eq_kernelSum :
    ∀ i j : GeneratedInteriorIndex A,
      generatedInteriorLeftBlockFold W T i j =
        ∑ k : GeneratedInteriorIndex A,
          generatedInteriorLeftBlockFoldKernel W T i j k
  rightBlockFold_eq_kernelSum :
    ∀ i j : GeneratedInteriorIndex A,
      generatedInteriorRightBlockFold W T i j =
        ∑ k : GeneratedInteriorIndex A,
          generatedInteriorRightBlockFoldKernel W T i j k
  leftAccumulatedConvolution_eq_blockFold :
    ∀ i j : GeneratedInteriorIndex A,
      generatedInteriorAccumulatedLeftConvolution W T i j =
        generatedInteriorLeftBlockFold W T i j
  rightAccumulatedConvolution_eq_blockFold :
    ∀ i j : GeneratedInteriorIndex A,
      generatedInteriorAccumulatedRightConvolution W T i j =
        generatedInteriorRightBlockFold W T i j
  normalFormStatus_eq :
    normalFormStatus =
      SM3eRr3c1aBlockFoldNormalFormStatus.blockFoldNormalFormFromAccumulatedTraceExpansion
  sourceStatus_eq :
    sourceStatus =
      SM3eRr3c1aBlockFoldSourceStatus.sourceFromSM3cRInteriorBlockAndSM3db4aRAccumulatedEntry
  noBlockFoldIdentityStatus_eq :
    noBlockFoldIdentityStatus =
      SM3eRr3c1aNoBlockFoldIdentityStatus.noBlockFoldIdentityInR3c1a
  noProductIdentityProofStatus_eq :
    noProductIdentityProofStatus =
      SM3eRr3c1aNoProductIdentityProofStatus.noProductIdentityProofInR3c1a
  noTwoSidedInvStatus_eq :
    noTwoSidedInvStatus = SM3eRr3c1aNoTwoSidedInvStatus.noTwoSidedInvInR3c1a
  noInteriorEliminationCertificateStatus_eq :
    noInteriorEliminationCertificateStatus =
      SM3db4RNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificateInSM3db4R
  noInteriorEliminationDataStatus_eq :
    noInteriorEliminationDataStatus =
      SM3db4RNoInteriorEliminationDataStatus.noInteriorEliminationDataInSM3db4R
  noDtnDataStatus_eq :
    noDtnDataStatus =
      SM3db4RNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db4R
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3db4RNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db4R
  nextPhaseStatus_eq :
    nextPhaseStatus =
      SM3eRr3c1aNextPhaseStatus.sm3eRr3c1b0LocalStepSchurCancellationSourceAudit

namespace GeneratedInteriorBlockFoldNormalFormR3c1a

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {p : ConcretePolicyOf}
variable {A : GeneratedApproximantStrong Cell p}
variable [Fintype (GeneratedInteriorIndex A)]
variable [DecidableEq (GeneratedInteriorIndex A)]
variable {P : GeneratedBoundaryInteriorPartition Cell p A}
variable {wp : WeightPolicy}
variable {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
variable {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
variable {K : GeneratedInteriorEliminationCarrier Cell p A P wp W E}


def fromEliminationTrace
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K) :
    GeneratedInteriorBlockFoldNormalFormR3c1a Cell p A P wp W E K T where
  accumulatedTraceEvaluation :=
    GeneratedInteriorAccumulatedTraceEvaluation.fromEliminationTrace T
  accumulatedEntryFold := GeneratedInteriorAccumulatedEntryFold.fromEliminationTrace T
  normalFormStatus :=
    SM3eRr3c1aBlockFoldNormalFormStatus.blockFoldNormalFormFromAccumulatedTraceExpansion
  sourceStatus :=
    SM3eRr3c1aBlockFoldSourceStatus.sourceFromSM3cRInteriorBlockAndSM3db4aRAccumulatedEntry
  noBlockFoldIdentityStatus :=
    SM3eRr3c1aNoBlockFoldIdentityStatus.noBlockFoldIdentityInR3c1a
  noProductIdentityProofStatus :=
    SM3eRr3c1aNoProductIdentityProofStatus.noProductIdentityProofInR3c1a
  noTwoSidedInvStatus := SM3eRr3c1aNoTwoSidedInvStatus.noTwoSidedInvInR3c1a
  noInteriorEliminationCertificateStatus :=
    SM3db4RNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificateInSM3db4R
  noInteriorEliminationDataStatus :=
    SM3db4RNoInteriorEliminationDataStatus.noInteriorEliminationDataInSM3db4R
  noDtnDataStatus :=
    SM3db4RNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db4R
  noArithmeticTargetStatus :=
    SM3db4RNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db4R
  nextPhaseStatus :=
    SM3eRr3c1aNextPhaseStatus.sm3eRr3c1b0LocalStepSchurCancellationSourceAudit
  accumulatedTraceEvaluation_is_fromTrace := by
    rfl
  accumulatedEntryFold_is_fromTrace := by
    rfl
  trace_source_eq_SM3db3R :=
    T.sourceStatus_eq
  accumulatedTraceSource_eq_SM3db4aR := by
    rfl
  accumulatedFoldSource_eq_SM3db4aR := by
    rfl
  accumulatedEntry_from_components := by
    intro i j
    rfl
  accumulatedEntry_from_trace := by
    intro i j
    rfl
  leftKernel_eq_components := by
    intro i j k
    rfl
  rightKernel_eq_components := by
    intro i j k
    rfl
  leftBlockFold_eq_kernelSum := by
    intro i j
    rfl
  rightBlockFold_eq_kernelSum := by
    intro i j
    rfl
  leftAccumulatedConvolution_eq_blockFold := by
    intro i j
    rfl
  rightAccumulatedConvolution_eq_blockFold := by
    intro i j
    rfl
  normalFormStatus_eq := by
    rfl
  sourceStatus_eq := by
    rfl
  noBlockFoldIdentityStatus_eq := by
    rfl
  noProductIdentityProofStatus_eq := by
    rfl
  noTwoSidedInvStatus_eq := by
    rfl
  noInteriorEliminationCertificateStatus_eq := by
    rfl
  noInteriorEliminationDataStatus_eq := by
    rfl
  noDtnDataStatus_eq := by
    rfl
  noArithmeticTargetStatus_eq := by
    rfl
  nextPhaseStatus_eq := by
    rfl

theorem leftAccumulatedConvolution_eq_blockFold_of_normalForm
    {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}
    (N : GeneratedInteriorBlockFoldNormalFormR3c1a Cell p A P wp W E K T)
    (i j : GeneratedInteriorIndex A) :
    generatedInteriorAccumulatedLeftConvolution W T i j =
      generatedInteriorLeftBlockFold W T i j :=
  N.leftAccumulatedConvolution_eq_blockFold i j

theorem rightAccumulatedConvolution_eq_blockFold_of_normalForm
    {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}
    (N : GeneratedInteriorBlockFoldNormalFormR3c1a Cell p A P wp W E K T)
    (i j : GeneratedInteriorIndex A) :
    generatedInteriorAccumulatedRightConvolution W T i j =
      generatedInteriorRightBlockFold W T i j :=
  N.rightAccumulatedConvolution_eq_blockFold i j

theorem nextPhase_is_r3c1b
    {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}
    (N : GeneratedInteriorBlockFoldNormalFormR3c1a Cell p A P wp W E K T) :
    N.nextPhaseStatus =
      SM3eRr3c1aNextPhaseStatus.sm3eRr3c1b0LocalStepSchurCancellationSourceAudit :=
  N.nextPhaseStatus_eq

theorem no_identity_proof_in_r3c1a
    {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}
    (N : GeneratedInteriorBlockFoldNormalFormR3c1a Cell p A P wp W E K T) :
    N.noBlockFoldIdentityStatus =
      SM3eRr3c1aNoBlockFoldIdentityStatus.noBlockFoldIdentityInR3c1a :=
  N.noBlockFoldIdentityStatus_eq

end GeneratedInteriorBlockFoldNormalFormR3c1a

abbrev RegularGeneratedInteriorBlockFoldNormalFormR3c1a
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorBlockFoldNormalFormR3c1a
    (ConcreteSubstrate.RegularCell b) p
    (regularGeneratedApproximantStrong b p)
    (regularGeneratedBoundaryInteriorPartition b p) wp
    (regularGeneratedWeightPolicyEntrySource b p wp)
    (regularGeneratedInteriorEliminationCandidateEntry b p wp)
    (regularGeneratedInteriorEliminationCarrier b p wp)
    (regularGeneratedInteriorEliminationTrace b p wp)

abbrev VariableGeneratedInteriorBlockFoldNormalFormR3c1a
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorBlockFoldNormalFormR3c1a
    (LevelVariableSubstrate.LevelVariableCell β) p
    (variableGeneratedApproximantStrong β p)
    (variableGeneratedBoundaryInteriorPartition β p) wp
    (variableGeneratedWeightPolicyEntrySource β p wp)
    (variableGeneratedInteriorEliminationCandidateEntry β p wp)
    (variableGeneratedInteriorEliminationCarrier β p wp)
    (variableGeneratedInteriorEliminationTrace β p wp)

def regularBlockFoldNormalFormR3c1a
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    RegularGeneratedInteriorBlockFoldNormalFormR3c1a b p wp :=
  GeneratedInteriorBlockFoldNormalFormR3c1a.fromEliminationTrace
    (regularGeneratedInteriorEliminationTrace b p wp)

def variableBlockFoldNormalFormR3c1a
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    VariableGeneratedInteriorBlockFoldNormalFormR3c1a β p wp :=
  GeneratedInteriorBlockFoldNormalFormR3c1a.fromEliminationTrace
    (variableGeneratedInteriorEliminationTrace β p wp)

structure SM3eRr3c1aBlockFoldNormalFormLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  regularNormalForm : RegularGeneratedInteriorBlockFoldNormalFormR3c1a b p regularWeight
  variableNormalForm : VariableGeneratedInteriorBlockFoldNormalFormR3c1a β p variableWeight
  status : SM3eRr3c1aBlockFoldNormalFormStatus
  nextPhaseStatus : SM3eRr3c1aNextPhaseStatus
  regularStatus_eq :
    regularNormalForm.normalFormStatus =
      SM3eRr3c1aBlockFoldNormalFormStatus.blockFoldNormalFormFromAccumulatedTraceExpansion
  variableStatus_eq :
    variableNormalForm.normalFormStatus =
      SM3eRr3c1aBlockFoldNormalFormStatus.blockFoldNormalFormFromAccumulatedTraceExpansion
  regularNoIdentity_eq :
    regularNormalForm.noBlockFoldIdentityStatus =
      SM3eRr3c1aNoBlockFoldIdentityStatus.noBlockFoldIdentityInR3c1a
  variableNoIdentity_eq :
    variableNormalForm.noBlockFoldIdentityStatus =
      SM3eRr3c1aNoBlockFoldIdentityStatus.noBlockFoldIdentityInR3c1a
  status_eq :
    status =
      SM3eRr3c1aBlockFoldNormalFormStatus.blockFoldNormalFormFromAccumulatedTraceExpansion
  nextPhaseStatus_eq :
    nextPhaseStatus =
      SM3eRr3c1aNextPhaseStatus.sm3eRr3c1b0LocalStepSchurCancellationSourceAudit

def sm3eRr3c1aBlockFoldNormalFormLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    SM3eRr3c1aBlockFoldNormalFormLedger b β p regularWeight variableWeight where
  regularNormalForm := regularBlockFoldNormalFormR3c1a b p regularWeight
  variableNormalForm := variableBlockFoldNormalFormR3c1a β p variableWeight
  status :=
    SM3eRr3c1aBlockFoldNormalFormStatus.blockFoldNormalFormFromAccumulatedTraceExpansion
  nextPhaseStatus := SM3eRr3c1aNextPhaseStatus.sm3eRr3c1b0LocalStepSchurCancellationSourceAudit
  regularStatus_eq := by
    rfl
  variableStatus_eq := by
    rfl
  regularNoIdentity_eq := by
    rfl
  variableNoIdentity_eq := by
    rfl
  status_eq := by
    rfl
  nextPhaseStatus_eq := by
    rfl

theorem sm3eRr3c1aBlockFoldNormalFormLedger_next
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3eRr3c1aBlockFoldNormalFormLedger
      b β p regularWeight variableWeight).nextPhaseStatus =
      SM3eRr3c1aNextPhaseStatus.sm3eRr3c1b0LocalStepSchurCancellationSourceAudit := by
  rfl

end Smoke

end CNNA.PillarA.Arithmetic
