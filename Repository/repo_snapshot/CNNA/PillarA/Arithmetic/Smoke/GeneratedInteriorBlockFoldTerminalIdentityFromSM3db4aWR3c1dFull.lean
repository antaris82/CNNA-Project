import CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

namespace Smoke

universe u

def terminalIdentityR3c1d_from_SM3db4aWExport
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
    (X : GeneratedInteriorTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW
      Cell p A P wp W E K T) :
    GeneratedInteriorBlockFoldTerminalIdentityR3c1d Cell p A P wp W E K T :=
  GeneratedInteriorBlockFoldTerminalIdentityR3c1d.fromTerminalCoverage X.terminalCoverageSource

theorem terminalIdentityR3c1d_from_SM3db4aWExport_terminalCoverage
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
    (X : GeneratedInteriorTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW
      Cell p A P wp W E K T) :
    (terminalIdentityR3c1d_from_SM3db4aWExport X).terminalCoverage =
      X.terminalCoverageSource := by
  rfl

theorem terminalIdentityR3c1d_from_SM3db4aWExport_nextPhase
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
    (X : GeneratedInteriorTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW
      Cell p A P wp W E K T) :
    (terminalIdentityR3c1d_from_SM3db4aWExport X).nextPhaseStatus =
      SM3eRr3c1dNextPhaseStatus.sm3eRr3c1eAccumulatedEntryCancellationAdapter :=
  (terminalIdentityR3c1d_from_SM3db4aWExport X).nextPhaseStatus_eq

theorem terminalIdentityR3c1d_from_SM3db4aWExport_noProductIdentityProof
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
    (X : GeneratedInteriorTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW
      Cell p A P wp W E K T) :
    (terminalIdentityR3c1d_from_SM3db4aWExport X).noProductIdentityProofStatus =
      SM3eRr3c1dNoProductIdentityProofStatus.noProductIdentityProofInTerminalIdentity :=
  (terminalIdentityR3c1d_from_SM3db4aWExport X).noProductIdentityProofStatus_eq

theorem terminalIdentityR3c1d_from_SM3db4aWExport_noTwoSidedInv
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
    (X : GeneratedInteriorTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW
      Cell p A P wp W E K T) :
    (terminalIdentityR3c1d_from_SM3db4aWExport X).noTwoSidedInvStatus =
      SM3eRr3c1dNoTwoSidedInvStatus.noTwoSidedInvInTerminalIdentity :=
  (terminalIdentityR3c1d_from_SM3db4aWExport X).noTwoSidedInvStatus_eq

theorem terminalIdentityR3c1d_from_SM3db4aWExport_noAccumulatedEntryCancellation
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
    (X : GeneratedInteriorTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW
      Cell p A P wp W E K T) :
    (terminalIdentityR3c1d_from_SM3db4aWExport X).noAccumulatedEntryCancellationStatus =
      SM3eRr3c1dNoAccumulatedEntryCancellationStatus.noAccumulatedEntryCancellationInvariantInTerminalIdentity :=
  (terminalIdentityR3c1d_from_SM3db4aWExport X).noAccumulatedEntryCancellationStatus_eq

def regularTerminalIdentityR3c1dFromSM3db4aWExport
    {b : Nat} {p : ConcretePolicyOf} {wp : WeightPolicy}
    (X : RegularGeneratedInteriorTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW
      b p wp) :
    RegularGeneratedInteriorBlockFoldTerminalIdentityR3c1d b p wp :=
  terminalIdentityR3c1d_from_SM3db4aWExport X

def variableTerminalIdentityR3c1dFromSM3db4aWExport
    {β : Nat → Nat} {p : ConcretePolicyOf} {wp : WeightPolicy}
    (X : VariableGeneratedInteriorTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW
      β p wp) :
    VariableGeneratedInteriorBlockFoldTerminalIdentityR3c1d β p wp :=
  terminalIdentityR3c1d_from_SM3db4aWExport X

def regularTerminalIdentityR3c1dFromSM3db4aWSource
    {b : Nat} {p : ConcretePolicyOf} {wp : WeightPolicy}
    (S : RegularGeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV b p wp) :
    RegularGeneratedInteriorBlockFoldTerminalIdentityR3c1d b p wp :=
  regularBlockFoldTerminalIdentityR3c1d
    (regularBlockFoldTerminalCoverageSourceR3c1dFromSM3db4aW S)

def variableTerminalIdentityR3c1dFromSM3db4aWSource
    {β : Nat → Nat} {p : ConcretePolicyOf} {wp : WeightPolicy}
    (S : VariableGeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV β p wp) :
    VariableGeneratedInteriorBlockFoldTerminalIdentityR3c1d β p wp :=
  variableBlockFoldTerminalIdentityR3c1d
    (variableBlockFoldTerminalCoverageSourceR3c1dFromSM3db4aW S)

def terminalIdentityLedgerR3c1dFromSM3db4aW
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3db4aWTerminalIdentityFieldCertificateFromEquationSourceLedger
      b β p regularWeight variableWeight) :
    SM3eRr3c1dTerminalIdentityLedger b β p regularWeight variableWeight :=
  SM3eRr3c1dTerminalIdentityLedger.fromRegularAndVariableTerminalCoverage
    L.regularTerminalCoverageSource
    L.variableTerminalCoverageSource

theorem terminalIdentityLedgerR3c1dFromSM3db4aW_nextPhase
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3db4aWTerminalIdentityFieldCertificateFromEquationSourceLedger
      b β p regularWeight variableWeight) :
    (terminalIdentityLedgerR3c1dFromSM3db4aW L).nextPhaseStatus =
      SM3eRr3c1dNextPhaseStatus.sm3eRr3c1eAccumulatedEntryCancellationAdapter :=
  (terminalIdentityLedgerR3c1dFromSM3db4aW L).nextPhaseStatus_eq

structure SM3eRr3c1dFullTerminalIdentityFromSM3db4aWLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  sm3db4aWLedger :
    SM3db4aWTerminalIdentityFieldCertificateFromEquationSourceLedger
      b β p regularWeight variableWeight
  terminalIdentityLedger :
    SM3eRr3c1dTerminalIdentityLedger b β p regularWeight variableWeight
  terminalIdentityLedger_eq :
    terminalIdentityLedger = terminalIdentityLedgerR3c1dFromSM3db4aW sm3db4aWLedger
  regularTerminalIdentity_eq_coverage :
    terminalIdentityLedger.regularTerminalIdentity =
      regularBlockFoldTerminalIdentityR3c1d sm3db4aWLedger.regularTerminalCoverageSource
  variableTerminalIdentity_eq_coverage :
    terminalIdentityLedger.variableTerminalIdentity =
      variableBlockFoldTerminalIdentityR3c1d sm3db4aWLedger.variableTerminalCoverageSource
  regularCoverage_eq_WExport :
    sm3db4aWLedger.regularTerminalCoverageSource =
      sm3db4aWLedger.regularExport.terminalCoverageSource
  variableCoverage_eq_WExport :
    sm3db4aWLedger.variableTerminalCoverageSource =
      sm3db4aWLedger.variableExport.terminalCoverageSource
  regularCoverage_eq_WSource :
    sm3db4aWLedger.regularTerminalCoverageSource =
      regularBlockFoldTerminalCoverageSourceR3c1dFromSM3db4aW
        sm3db4aWLedger.equationSourceLedger.regularSource
  variableCoverage_eq_WSource :
    sm3db4aWLedger.variableTerminalCoverageSource =
      variableBlockFoldTerminalCoverageSourceR3c1dFromSM3db4aW
        sm3db4aWLedger.equationSourceLedger.variableSource
  regularNextPhaseStatus_eq :
    terminalIdentityLedger.regularTerminalIdentity.nextPhaseStatus =
      SM3eRr3c1dNextPhaseStatus.sm3eRr3c1eAccumulatedEntryCancellationAdapter
  variableNextPhaseStatus_eq :
    terminalIdentityLedger.variableTerminalIdentity.nextPhaseStatus =
      SM3eRr3c1dNextPhaseStatus.sm3eRr3c1eAccumulatedEntryCancellationAdapter
  terminalIdentityLedgerNextPhase_eq :
    terminalIdentityLedger.nextPhaseStatus =
      SM3eRr3c1dNextPhaseStatus.sm3eRr3c1eAccumulatedEntryCancellationAdapter
  regularNoAccumulatedEntryCancellation_eq :
    terminalIdentityLedger.regularTerminalIdentity.noAccumulatedEntryCancellationStatus =
      SM3eRr3c1dNoAccumulatedEntryCancellationStatus.noAccumulatedEntryCancellationInvariantInTerminalIdentity
  variableNoAccumulatedEntryCancellation_eq :
    terminalIdentityLedger.variableTerminalIdentity.noAccumulatedEntryCancellationStatus =
      SM3eRr3c1dNoAccumulatedEntryCancellationStatus.noAccumulatedEntryCancellationInvariantInTerminalIdentity
  regularNoProductIdentityProof_eq :
    terminalIdentityLedger.regularTerminalIdentity.noProductIdentityProofStatus =
      SM3eRr3c1dNoProductIdentityProofStatus.noProductIdentityProofInTerminalIdentity
  variableNoProductIdentityProof_eq :
    terminalIdentityLedger.variableTerminalIdentity.noProductIdentityProofStatus =
      SM3eRr3c1dNoProductIdentityProofStatus.noProductIdentityProofInTerminalIdentity
  regularNoTwoSidedInv_eq :
    terminalIdentityLedger.regularTerminalIdentity.noTwoSidedInvStatus =
      SM3eRr3c1dNoTwoSidedInvStatus.noTwoSidedInvInTerminalIdentity
  variableNoTwoSidedInv_eq :
    terminalIdentityLedger.variableTerminalIdentity.noTwoSidedInvStatus =
      SM3eRr3c1dNoTwoSidedInvStatus.noTwoSidedInvInTerminalIdentity

namespace SM3eRr3c1dFullTerminalIdentityFromSM3db4aWLedger

def fromSM3db4aWLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3db4aWTerminalIdentityFieldCertificateFromEquationSourceLedger
      b β p regularWeight variableWeight) :
    SM3eRr3c1dFullTerminalIdentityFromSM3db4aWLedger
      b β p regularWeight variableWeight where
  sm3db4aWLedger := L
  terminalIdentityLedger := terminalIdentityLedgerR3c1dFromSM3db4aW L
  terminalIdentityLedger_eq := by
    rfl
  regularTerminalIdentity_eq_coverage := by
    rfl
  variableTerminalIdentity_eq_coverage := by
    rfl
  regularCoverage_eq_WExport :=
    L.regularCoverage_eq_export
  variableCoverage_eq_WExport :=
    L.variableCoverage_eq_export
  regularCoverage_eq_WSource :=
    L.regularCoverage_eq_source
  variableCoverage_eq_WSource :=
    L.variableCoverage_eq_source
  regularNextPhaseStatus_eq := by
    rfl
  variableNextPhaseStatus_eq := by
    rfl
  terminalIdentityLedgerNextPhase_eq := by
    rfl
  regularNoAccumulatedEntryCancellation_eq := by
    rfl
  variableNoAccumulatedEntryCancellation_eq := by
    rfl
  regularNoProductIdentityProof_eq := by
    rfl
  variableNoProductIdentityProof_eq := by
    rfl
  regularNoTwoSidedInv_eq := by
    rfl
  variableNoTwoSidedInv_eq := by
    rfl

theorem nextPhase_is_r3c1e
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1dFullTerminalIdentityFromSM3db4aWLedger
      b β p regularWeight variableWeight) :
    L.terminalIdentityLedger.nextPhaseStatus =
      SM3eRr3c1dNextPhaseStatus.sm3eRr3c1eAccumulatedEntryCancellationAdapter :=
  L.terminalIdentityLedgerNextPhase_eq

theorem regular_noProductIdentityProof
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1dFullTerminalIdentityFromSM3db4aWLedger
      b β p regularWeight variableWeight) :
    L.terminalIdentityLedger.regularTerminalIdentity.noProductIdentityProofStatus =
      SM3eRr3c1dNoProductIdentityProofStatus.noProductIdentityProofInTerminalIdentity :=
  L.regularNoProductIdentityProof_eq

theorem variable_noProductIdentityProof
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1dFullTerminalIdentityFromSM3db4aWLedger
      b β p regularWeight variableWeight) :
    L.terminalIdentityLedger.variableTerminalIdentity.noProductIdentityProofStatus =
      SM3eRr3c1dNoProductIdentityProofStatus.noProductIdentityProofInTerminalIdentity :=
  L.variableNoProductIdentityProof_eq

theorem regular_noTwoSidedInv
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1dFullTerminalIdentityFromSM3db4aWLedger
      b β p regularWeight variableWeight) :
    L.terminalIdentityLedger.regularTerminalIdentity.noTwoSidedInvStatus =
      SM3eRr3c1dNoTwoSidedInvStatus.noTwoSidedInvInTerminalIdentity :=
  L.regularNoTwoSidedInv_eq

theorem variable_noTwoSidedInv
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1dFullTerminalIdentityFromSM3db4aWLedger
      b β p regularWeight variableWeight) :
    L.terminalIdentityLedger.variableTerminalIdentity.noTwoSidedInvStatus =
      SM3eRr3c1dNoTwoSidedInvStatus.noTwoSidedInvInTerminalIdentity :=
  L.variableNoTwoSidedInv_eq

end SM3eRr3c1dFullTerminalIdentityFromSM3db4aWLedger

def sm3eRr3c1dFullTerminalIdentityFromSM3db4aWLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3db4aWTerminalIdentityFieldCertificateFromEquationSourceLedger
      b β p regularWeight variableWeight) :
    SM3eRr3c1dFullTerminalIdentityFromSM3db4aWLedger
      b β p regularWeight variableWeight :=
  SM3eRr3c1dFullTerminalIdentityFromSM3db4aWLedger.fromSM3db4aWLedger L

end Smoke

end CNNA.PillarA.Arithmetic
