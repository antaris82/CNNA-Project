import CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldTerminalIdentityR3c1d
import CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorAccumulatedEntryCancellationR3c1

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

namespace Smoke

universe u

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

def fromTerminalIdentityR3c1d
    (D : GeneratedInteriorBlockFoldTerminalIdentityR3c1d Cell p A P wp W E K T) :
    GeneratedInteriorAccumulatedEntryCancellationInvariant Cell p A P wp W E K T where
  accumulatedTraceEvaluation := D.invariance.blockFoldNormalForm.accumulatedTraceEvaluation
  accumulatedEntryFold := D.invariance.blockFoldNormalForm.accumulatedEntryFold
  cancellationStatus :=
    SM3eRr3c1AccumulatedEntryCancellationStatus.accumulatedEntryCancellationFromSM3db4aRFold
  sourceStatus :=
    SM3eRr3c1AccumulatedEntryCancellationSourceStatus.sourceFromSM3cRInteriorBlockAndSM3db4aRAccumulatedEntry
  noFreeEntryTableStatus := SM3db4RNoFreeInverseEntryTableStatus.noFreeInverseEntryTable
  noMatrixInvStatus := SM3db4RNoMatrixInvStatus.noMatrixInvForInverseCandidateEntry
  noExternalInverseOracleStatus :=
    SM3db4RNoExternalInverseOracleStatus.noExternalInverseOracleForInverseCandidateEntry
  noProductIdentityProofStatus :=
    SM3eRr3c1NoProductIdentityProofStatus.noProductIdentityProofInAccumulatedEntryCancellation
  noTwoSidedInvStatus := SM3eRr3c1NoTwoSidedInvStatus.noTwoSidedInvInAccumulatedEntryCancellation
  noInteriorEliminationCertificateStatus :=
    SM3db4RNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificateInSM3db4R
  noInteriorEliminationDataStatus :=
    SM3db4RNoInteriorEliminationDataStatus.noInteriorEliminationDataInSM3db4R
  noDtnDataStatus :=
    SM3db4RNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db4R
  noArithmeticTargetStatus :=
    SM3db4RNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db4R
  nextPhaseStatus :=
    SM3eRr3c1NextPhaseStatus.sm3eRr3c2MayConsumeAccumulatedEntryCancellationInvariant
  accumulatedTraceEvaluation_is_fromTrace :=
    D.invariance.blockFoldNormalForm.accumulatedTraceEvaluation_is_fromTrace
  accumulatedEntryFold_is_fromTrace :=
    D.invariance.blockFoldNormalForm.accumulatedEntryFold_is_fromTrace
  trace_source_eq_SM3db3R :=
    D.trace_source_eq_SM3db3R
  accumulatedTraceSource_eq_SM3db4aR :=
    D.accumulatedTraceSource_eq_SM3db4aR
  accumulatedFoldSource_eq_SM3db4aR :=
    D.accumulatedFoldSource_eq_SM3db4aR
  accumulatedEntry_from_trace :=
    D.invariance.blockFoldNormalForm.accumulatedEntry_from_trace
  leftAccumulatedConvolution_eq_identity :=
    D.leftAccumulatedConvolution_eq_identity
  rightAccumulatedConvolution_eq_identity :=
    D.rightAccumulatedConvolution_eq_identity
  leftAccumulatedConvolution_diagonal :=
    D.leftAccumulatedConvolution_diagonal
  leftAccumulatedConvolution_offdiag :=
    D.leftAccumulatedConvolution_offdiag
  rightAccumulatedConvolution_diagonal :=
    D.rightAccumulatedConvolution_diagonal
  rightAccumulatedConvolution_offdiag :=
    D.rightAccumulatedConvolution_offdiag
  cancellationStatus_eq := by
    rfl
  sourceStatus_eq := by
    rfl
  noFreeEntryTableStatus_eq := by
    rfl
  noMatrixInvStatus_eq := by
    rfl
  noExternalInverseOracleStatus_eq := by
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

end GeneratedInteriorAccumulatedEntryCancellationInvariant

def accumulatedEntryCancellationInvariant_from_terminalIdentityR3c1d
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
    {K : GeneratedInteriorEliminationCarrier Cell p A P wp W E}
    {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}
    (D : GeneratedInteriorBlockFoldTerminalIdentityR3c1d Cell p A P wp W E K T) :
    GeneratedInteriorAccumulatedEntryCancellationInvariant Cell p A P wp W E K T :=
  GeneratedInteriorAccumulatedEntryCancellationInvariant.fromTerminalIdentityR3c1d D

theorem accumulatedEntryCancellationInvariant_from_terminalIdentityR3c1d_left_identity
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
    {K : GeneratedInteriorEliminationCarrier Cell p A P wp W E}
    {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}
    (D : GeneratedInteriorBlockFoldTerminalIdentityR3c1d Cell p A P wp W E K T)
    (i j : GeneratedInteriorIndex A) :
    (accumulatedEntryCancellationInvariant_from_terminalIdentityR3c1d D).leftAccumulatedConvolution_eq_identity i j =
      D.leftAccumulatedConvolution_eq_identity i j := by
  rfl

theorem accumulatedEntryCancellationInvariant_from_terminalIdentityR3c1d_right_identity
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
    {K : GeneratedInteriorEliminationCarrier Cell p A P wp W E}
    {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}
    (D : GeneratedInteriorBlockFoldTerminalIdentityR3c1d Cell p A P wp W E K T)
    (i j : GeneratedInteriorIndex A) :
    (accumulatedEntryCancellationInvariant_from_terminalIdentityR3c1d D).rightAccumulatedConvolution_eq_identity i j =
      D.rightAccumulatedConvolution_eq_identity i j := by
  rfl

theorem accumulatedEntryCancellationInvariant_from_terminalIdentityR3c1d_nextPhase
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
    {K : GeneratedInteriorEliminationCarrier Cell p A P wp W E}
    {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}
    (D : GeneratedInteriorBlockFoldTerminalIdentityR3c1d Cell p A P wp W E K T) :
    (accumulatedEntryCancellationInvariant_from_terminalIdentityR3c1d D).nextPhaseStatus =
      SM3eRr3c1NextPhaseStatus.sm3eRr3c2MayConsumeAccumulatedEntryCancellationInvariant :=
  (accumulatedEntryCancellationInvariant_from_terminalIdentityR3c1d D).nextPhaseStatus_eq

def regularAccumulatedEntryCancellationInvariant_from_terminalIdentityR3c1d
    {b : Nat} {p : ConcretePolicyOf} {wp : WeightPolicy}
    (D : RegularGeneratedInteriorBlockFoldTerminalIdentityR3c1d b p wp) :
    RegularGeneratedInteriorAccumulatedEntryCancellationInvariant b p wp :=
  accumulatedEntryCancellationInvariant_from_terminalIdentityR3c1d D

def variableAccumulatedEntryCancellationInvariant_from_terminalIdentityR3c1d
    {β : Nat → Nat} {p : ConcretePolicyOf} {wp : WeightPolicy}
    (D : VariableGeneratedInteriorBlockFoldTerminalIdentityR3c1d β p wp) :
    VariableGeneratedInteriorAccumulatedEntryCancellationInvariant β p wp :=
  accumulatedEntryCancellationInvariant_from_terminalIdentityR3c1d D

def accumulatedEntryCancellationLedger_from_terminalIdentityLedgerR3c1d
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1dTerminalIdentityLedger b β p regularWeight variableWeight) :
    SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight :=
  SM3eRr3c1AccumulatedEntryCancellationLedger.fromRegularAndVariable
    (regularAccumulatedEntryCancellationInvariant_from_terminalIdentityR3c1d
      L.regularTerminalIdentity)
    (variableAccumulatedEntryCancellationInvariant_from_terminalIdentityR3c1d
      L.variableTerminalIdentity)

theorem accumulatedEntryCancellationLedger_from_terminalIdentityLedgerR3c1d_nextPhase
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1dTerminalIdentityLedger b β p regularWeight variableWeight) :
    (accumulatedEntryCancellationLedger_from_terminalIdentityLedgerR3c1d L).nextPhaseStatus =
      SM3eRr3c1NextPhaseStatus.sm3eRr3c2MayConsumeAccumulatedEntryCancellationInvariant :=
  (accumulatedEntryCancellationLedger_from_terminalIdentityLedgerR3c1d L).nextPhaseStatus_eq

end Smoke

end CNNA.PillarA.Arithmetic
