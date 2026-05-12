import CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldNormalFormR3c1a

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

namespace Smoke

universe u

inductive SM3eRr3c1AccumulatedEntryCancellationStatus where
  | accumulatedEntryCancellationFromSM3db4aRFold
  deriving DecidableEq, Repr

inductive SM3eRr3c1AccumulatedEntryCancellationSourceStatus where
  | sourceFromSM3cRInteriorBlockAndSM3db4aRAccumulatedEntry
  deriving DecidableEq, Repr

inductive SM3eRr3c1NoProductIdentityProofStatus where
  | noProductIdentityProofInAccumulatedEntryCancellation
  deriving DecidableEq, Repr

inductive SM3eRr3c1NoTwoSidedInvStatus where
  | noTwoSidedInvInAccumulatedEntryCancellation
  deriving DecidableEq, Repr

inductive SM3eRr3c1NextPhaseStatus where
  | sm3eRr3c2MayConsumeAccumulatedEntryCancellationInvariant
  deriving DecidableEq, Repr

structure GeneratedInteriorAccumulatedEntryCancellationInvariant
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
  cancellationStatus : SM3eRr3c1AccumulatedEntryCancellationStatus
  sourceStatus : SM3eRr3c1AccumulatedEntryCancellationSourceStatus
  noFreeEntryTableStatus : SM3db4RNoFreeInverseEntryTableStatus
  noMatrixInvStatus : SM3db4RNoMatrixInvStatus
  noExternalInverseOracleStatus : SM3db4RNoExternalInverseOracleStatus
  noProductIdentityProofStatus : SM3eRr3c1NoProductIdentityProofStatus
  noTwoSidedInvStatus : SM3eRr3c1NoTwoSidedInvStatus
  noInteriorEliminationCertificateStatus : SM3db4RNoInteriorEliminationCertificateStatus
  noInteriorEliminationDataStatus : SM3db4RNoInteriorEliminationDataStatus
  noDtnDataStatus : SM3db4RNoDtnDataStatus
  noArithmeticTargetStatus : SM3db4RNoArithmeticTargetStatus
  nextPhaseStatus : SM3eRr3c1NextPhaseStatus
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
  accumulatedEntry_from_trace :
    ∀ i j : GeneratedInteriorIndex A,
      accumulatedEntryFold.accumulatedEntry i j = generatedInteriorAccumulatedEntryValue T i j
  leftAccumulatedConvolution_eq_identity :
    ∀ i j : GeneratedInteriorIndex A,
      generatedInteriorAccumulatedLeftConvolution W T i j =
        (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j
  rightAccumulatedConvolution_eq_identity :
    ∀ i j : GeneratedInteriorIndex A,
      generatedInteriorAccumulatedRightConvolution W T i j =
        (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j
  leftAccumulatedConvolution_diagonal :
    ∀ i : GeneratedInteriorIndex A,
      generatedInteriorAccumulatedLeftConvolution W T i i = 1
  leftAccumulatedConvolution_offdiag :
    ∀ i j : GeneratedInteriorIndex A,
      i ≠ j → generatedInteriorAccumulatedLeftConvolution W T i j = 0
  rightAccumulatedConvolution_diagonal :
    ∀ i : GeneratedInteriorIndex A,
      generatedInteriorAccumulatedRightConvolution W T i i = 1
  rightAccumulatedConvolution_offdiag :
    ∀ i j : GeneratedInteriorIndex A,
      i ≠ j → generatedInteriorAccumulatedRightConvolution W T i j = 0
  cancellationStatus_eq :
    cancellationStatus =
      SM3eRr3c1AccumulatedEntryCancellationStatus.accumulatedEntryCancellationFromSM3db4aRFold
  sourceStatus_eq :
    sourceStatus =
      SM3eRr3c1AccumulatedEntryCancellationSourceStatus.sourceFromSM3cRInteriorBlockAndSM3db4aRAccumulatedEntry
  noFreeEntryTableStatus_eq :
    noFreeEntryTableStatus = SM3db4RNoFreeInverseEntryTableStatus.noFreeInverseEntryTable
  noMatrixInvStatus_eq :
    noMatrixInvStatus = SM3db4RNoMatrixInvStatus.noMatrixInvForInverseCandidateEntry
  noExternalInverseOracleStatus_eq :
    noExternalInverseOracleStatus =
      SM3db4RNoExternalInverseOracleStatus.noExternalInverseOracleForInverseCandidateEntry
  noProductIdentityProofStatus_eq :
    noProductIdentityProofStatus =
      SM3eRr3c1NoProductIdentityProofStatus.noProductIdentityProofInAccumulatedEntryCancellation
  noTwoSidedInvStatus_eq :
    noTwoSidedInvStatus = SM3eRr3c1NoTwoSidedInvStatus.noTwoSidedInvInAccumulatedEntryCancellation
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
      SM3eRr3c1NextPhaseStatus.sm3eRr3c2MayConsumeAccumulatedEntryCancellationInvariant

namespace GeneratedInteriorAccumulatedEntryCancellationInvariant

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
variable {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}

theorem leftConvolution_entry_eq_identity
    (C : GeneratedInteriorAccumulatedEntryCancellationInvariant Cell p A P wp W E K T)
    (i j : GeneratedInteriorIndex A) :
    generatedInteriorAccumulatedLeftConvolution W T i j =
      (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j :=
  C.leftAccumulatedConvolution_eq_identity i j

theorem rightConvolution_entry_eq_identity
    (C : GeneratedInteriorAccumulatedEntryCancellationInvariant Cell p A P wp W E K T)
    (i j : GeneratedInteriorIndex A) :
    generatedInteriorAccumulatedRightConvolution W T i j =
      (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j :=
  C.rightAccumulatedConvolution_eq_identity i j

theorem leftConvolution_diagonal
    (C : GeneratedInteriorAccumulatedEntryCancellationInvariant Cell p A P wp W E K T)
    (i : GeneratedInteriorIndex A) :
    generatedInteriorAccumulatedLeftConvolution W T i i = 1 :=
  C.leftAccumulatedConvolution_diagonal i

theorem leftConvolution_offdiag
    (C : GeneratedInteriorAccumulatedEntryCancellationInvariant Cell p A P wp W E K T)
    (i j : GeneratedInteriorIndex A)
    (hij : i ≠ j) :
    generatedInteriorAccumulatedLeftConvolution W T i j = 0 :=
  C.leftAccumulatedConvolution_offdiag i j hij

theorem rightConvolution_diagonal
    (C : GeneratedInteriorAccumulatedEntryCancellationInvariant Cell p A P wp W E K T)
    (i : GeneratedInteriorIndex A) :
    generatedInteriorAccumulatedRightConvolution W T i i = 1 :=
  C.rightAccumulatedConvolution_diagonal i

theorem rightConvolution_offdiag
    (C : GeneratedInteriorAccumulatedEntryCancellationInvariant Cell p A P wp W E K T)
    (i j : GeneratedInteriorIndex A)
    (hij : i ≠ j) :
    generatedInteriorAccumulatedRightConvolution W T i j = 0 :=
  C.rightAccumulatedConvolution_offdiag i j hij

end GeneratedInteriorAccumulatedEntryCancellationInvariant

abbrev RegularGeneratedInteriorAccumulatedEntryCancellationInvariant
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorAccumulatedEntryCancellationInvariant
    (ConcreteSubstrate.RegularCell b) p
    (regularGeneratedApproximantStrong b p)
    (regularGeneratedBoundaryInteriorPartition b p) wp
    (regularGeneratedWeightPolicyEntrySource b p wp)
    (regularGeneratedInteriorEliminationCandidateEntry b p wp)
    (regularGeneratedInteriorEliminationCarrier b p wp)
    (regularGeneratedInteriorEliminationTrace b p wp)

abbrev VariableGeneratedInteriorAccumulatedEntryCancellationInvariant
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorAccumulatedEntryCancellationInvariant
    (LevelVariableSubstrate.LevelVariableCell β) p
    (variableGeneratedApproximantStrong β p)
    (variableGeneratedBoundaryInteriorPartition β p) wp
    (variableGeneratedWeightPolicyEntrySource β p wp)
    (variableGeneratedInteriorEliminationCandidateEntry β p wp)
    (variableGeneratedInteriorEliminationCarrier β p wp)
    (variableGeneratedInteriorEliminationTrace β p wp)

structure SM3eRr3c1AccumulatedEntryCancellationLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  regularCancellation :
    RegularGeneratedInteriorAccumulatedEntryCancellationInvariant b p regularWeight
  variableCancellation :
    VariableGeneratedInteriorAccumulatedEntryCancellationInvariant β p variableWeight
  nextPhaseStatus : SM3eRr3c1NextPhaseStatus
  regularStatus_eq :
    regularCancellation.cancellationStatus =
      SM3eRr3c1AccumulatedEntryCancellationStatus.accumulatedEntryCancellationFromSM3db4aRFold
  variableStatus_eq :
    variableCancellation.cancellationStatus =
      SM3eRr3c1AccumulatedEntryCancellationStatus.accumulatedEntryCancellationFromSM3db4aRFold
  regularNoProductIdentityProof :
    regularCancellation.noProductIdentityProofStatus =
      SM3eRr3c1NoProductIdentityProofStatus.noProductIdentityProofInAccumulatedEntryCancellation
  variableNoProductIdentityProof :
    variableCancellation.noProductIdentityProofStatus =
      SM3eRr3c1NoProductIdentityProofStatus.noProductIdentityProofInAccumulatedEntryCancellation
  regularNoTwoSidedInv :
    regularCancellation.noTwoSidedInvStatus =
      SM3eRr3c1NoTwoSidedInvStatus.noTwoSidedInvInAccumulatedEntryCancellation
  variableNoTwoSidedInv :
    variableCancellation.noTwoSidedInvStatus =
      SM3eRr3c1NoTwoSidedInvStatus.noTwoSidedInvInAccumulatedEntryCancellation
  nextPhaseStatus_eq :
    nextPhaseStatus =
      SM3eRr3c1NextPhaseStatus.sm3eRr3c2MayConsumeAccumulatedEntryCancellationInvariant

namespace SM3eRr3c1AccumulatedEntryCancellationLedger

def fromRegularAndVariable
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (regularCancellation :
      RegularGeneratedInteriorAccumulatedEntryCancellationInvariant b p regularWeight)
    (variableCancellation :
      VariableGeneratedInteriorAccumulatedEntryCancellationInvariant β p variableWeight) :
    SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight where
  regularCancellation := regularCancellation
  variableCancellation := variableCancellation
  nextPhaseStatus :=
    SM3eRr3c1NextPhaseStatus.sm3eRr3c2MayConsumeAccumulatedEntryCancellationInvariant
  regularStatus_eq := regularCancellation.cancellationStatus_eq
  variableStatus_eq := variableCancellation.cancellationStatus_eq
  regularNoProductIdentityProof := regularCancellation.noProductIdentityProofStatus_eq
  variableNoProductIdentityProof := variableCancellation.noProductIdentityProofStatus_eq
  regularNoTwoSidedInv := regularCancellation.noTwoSidedInvStatus_eq
  variableNoTwoSidedInv := variableCancellation.noTwoSidedInvStatus_eq
  nextPhaseStatus_eq := by
    rfl

end SM3eRr3c1AccumulatedEntryCancellationLedger

end Smoke

end CNNA.PillarA.Arithmetic
