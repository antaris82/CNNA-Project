import CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV
import CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlockFoldTerminalIdentityR3c1d

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

namespace Smoke

universe u

inductive SM3db4aWCertificateSourceStatus where
  | terminalIdentityFieldCertificateFromSM3db4aVEquationSource
  deriving DecidableEq, Repr

inductive SM3db4aWTerminalCoverageExportStatus where
  | terminalCoverageSourceFromSM3db4aUCertificate
  deriving DecidableEq, Repr

inductive SM3db4aWEquationDatumSourceStatus where
  | equationDatumCarriedOnlyBySM3db4aVSource
  deriving DecidableEq, Repr

inductive SM3db4aWNoFreeIdentityFieldStatus where
  | noFreeIdentityFieldsInSM3db4aWExport
  deriving DecidableEq, Repr

inductive SM3db4aWNoProductIdentityProofStatus where
  | noProductIdentityProofInSM3db4aWExport
  deriving DecidableEq, Repr

inductive SM3db4aWNoTwoSidedInvStatus where
  | noTwoSidedInvInSM3db4aWExport
  deriving DecidableEq, Repr

inductive SM3db4aWNoInteriorEliminationDataStatus where
  | noInteriorEliminationDataInSM3db4aWExport
  deriving DecidableEq, Repr

inductive SM3db4aWNoDtnDataStatus where
  | noDtnGeneralizedDtnOrMultiSchurDataInSM3db4aWExport
  deriving DecidableEq, Repr

inductive SM3db4aWNoArithmeticTargetStatus where
  | noCharpolyFactorDiscriminantOrL23TargetInSM3db4aWExport
  deriving DecidableEq, Repr

inductive SM3db4aWNextPhaseStatus where
  | sm3eRr3c1dFullTerminalCoverageConsumer
  deriving DecidableEq, Repr

inductive SM3db4aWLedgerStatus where
  | terminalIdentityFieldCertificateAndCoverageExportFromEquationSource
  deriving DecidableEq, Repr

def terminalFoldResidualIdentityFieldCertificateFromEquationSourceSM3db4aW
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
    (S : GeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV Cell p A P wp W E K T) :
    GeneratedInteriorTerminalFoldResidualIdentityFieldCertificateSM3db4aU Cell p A P wp W E K T :=
  terminalFoldResidualIdentityFieldCertificateFromSM3db4aV S

def blockFoldTerminalCoverageSourceFromEquationSourceSM3db4aW
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
    (S : GeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV Cell p A P wp W E K T) :
    GeneratedInteriorBlockFoldTerminalCoverageSourceR3c1d Cell p A P wp W E K T :=
  GeneratedInteriorBlockFoldTerminalCoverageSourceR3c1d.fromSM3db4aUTerminalIdentityFieldCertificate
    (terminalFoldResidualIdentityFieldCertificateFromEquationSourceSM3db4aW S)

structure GeneratedInteriorTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW
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
  equationSource : GeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV Cell p A P wp W E K T
  equationDatum : GeneratedInteriorTerminalFoldResidualIdentityEquationDatumSM3db4aV Cell p A P wp W E K T
  terminalIdentityFieldCertificate : GeneratedInteriorTerminalFoldResidualIdentityFieldCertificateSM3db4aU Cell p A P wp W E K T
  terminalCoverageSource : GeneratedInteriorBlockFoldTerminalCoverageSourceR3c1d Cell p A P wp W E K T
  certificateSourceStatus : SM3db4aWCertificateSourceStatus
  terminalCoverageExportStatus : SM3db4aWTerminalCoverageExportStatus
  equationDatumSourceStatus : SM3db4aWEquationDatumSourceStatus
  noFreeIdentityFieldStatus : SM3db4aWNoFreeIdentityFieldStatus
  noProductIdentityProofStatus : SM3db4aWNoProductIdentityProofStatus
  noTwoSidedInvStatus : SM3db4aWNoTwoSidedInvStatus
  noInteriorEliminationDataStatus : SM3db4aWNoInteriorEliminationDataStatus
  noDtnDataStatus : SM3db4aWNoDtnDataStatus
  noArithmeticTargetStatus : SM3db4aWNoArithmeticTargetStatus
  nextPhaseStatus : SM3db4aWNextPhaseStatus
  equationDatum_eq_source : equationDatum = equationSource.equationDatum
  terminalIdentityFieldCertificate_eq_source :
    terminalIdentityFieldCertificate =
      terminalFoldResidualIdentityFieldCertificateFromEquationSourceSM3db4aW equationSource
  terminalCoverageSource_eq_certificate :
    terminalCoverageSource =
      GeneratedInteriorBlockFoldTerminalCoverageSourceR3c1d.fromSM3db4aUTerminalIdentityFieldCertificate
        terminalIdentityFieldCertificate
  terminalCoverageSource_eq_source :
    terminalCoverageSource =
      blockFoldTerminalCoverageSourceFromEquationSourceSM3db4aW equationSource
  equationSourceStatus_eq :
    equationSource.equationSourceStatus =
      SM3db4aVEquationSourceStatus.terminalFoldResidualIdentityEquationSourceCarriedByDatum
  equationSourceCertificateExportStatus_eq :
    equationSource.certificateExportStatus =
      SM3db4aVCertificateExportStatus.terminalIdentityFieldCertificatePreparedFromEquationSource
  certificateNextPhaseStatus_eq :
    terminalIdentityFieldCertificate.nextPhaseStatus =
      SM3db4aUNextPhaseStatus.sm3eRr3c1dFullTerminalCoverageConsumer
  terminalCoverageTracePivotCoverageStatus_eq :
    terminalCoverageSource.tracePivotCoverageStatus =
      SM3eRr3c1dTracePivotCoverageStatus.sourceFromSM3db3RTracePivotCoverage
  terminalCoverageFoldResidualCoverageStatus_eq :
    terminalCoverageSource.terminalFoldResidualCoverageStatus =
      SM3eRr3c1dTerminalFoldResidualCoverageStatus.sourceFromSM3db4aRTerminalFoldResidualCoverage
  certificateSourceStatus_eq :
    certificateSourceStatus =
      SM3db4aWCertificateSourceStatus.terminalIdentityFieldCertificateFromSM3db4aVEquationSource
  terminalCoverageExportStatus_eq :
    terminalCoverageExportStatus =
      SM3db4aWTerminalCoverageExportStatus.terminalCoverageSourceFromSM3db4aUCertificate
  equationDatumSourceStatus_eq :
    equationDatumSourceStatus =
      SM3db4aWEquationDatumSourceStatus.equationDatumCarriedOnlyBySM3db4aVSource
  noFreeIdentityFieldStatus_eq :
    noFreeIdentityFieldStatus =
      SM3db4aWNoFreeIdentityFieldStatus.noFreeIdentityFieldsInSM3db4aWExport
  noProductIdentityProofStatus_eq :
    noProductIdentityProofStatus =
      SM3db4aWNoProductIdentityProofStatus.noProductIdentityProofInSM3db4aWExport
  noTwoSidedInvStatus_eq :
    noTwoSidedInvStatus = SM3db4aWNoTwoSidedInvStatus.noTwoSidedInvInSM3db4aWExport
  noInteriorEliminationDataStatus_eq :
    noInteriorEliminationDataStatus =
      SM3db4aWNoInteriorEliminationDataStatus.noInteriorEliminationDataInSM3db4aWExport
  noDtnDataStatus_eq :
    noDtnDataStatus = SM3db4aWNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db4aWExport
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3db4aWNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db4aWExport
  nextPhaseStatus_eq :
    nextPhaseStatus = SM3db4aWNextPhaseStatus.sm3eRr3c1dFullTerminalCoverageConsumer

namespace GeneratedInteriorTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW

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

def fromEquationSource
    (S : GeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV Cell p A P wp W E K T) :
    GeneratedInteriorTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW Cell p A P wp W E K T where
  equationSource := S
  equationDatum := S.equationDatum
  terminalIdentityFieldCertificate :=
    terminalFoldResidualIdentityFieldCertificateFromEquationSourceSM3db4aW S
  terminalCoverageSource := blockFoldTerminalCoverageSourceFromEquationSourceSM3db4aW S
  certificateSourceStatus :=
    SM3db4aWCertificateSourceStatus.terminalIdentityFieldCertificateFromSM3db4aVEquationSource
  terminalCoverageExportStatus :=
    SM3db4aWTerminalCoverageExportStatus.terminalCoverageSourceFromSM3db4aUCertificate
  equationDatumSourceStatus :=
    SM3db4aWEquationDatumSourceStatus.equationDatumCarriedOnlyBySM3db4aVSource
  noFreeIdentityFieldStatus :=
    SM3db4aWNoFreeIdentityFieldStatus.noFreeIdentityFieldsInSM3db4aWExport
  noProductIdentityProofStatus :=
    SM3db4aWNoProductIdentityProofStatus.noProductIdentityProofInSM3db4aWExport
  noTwoSidedInvStatus := SM3db4aWNoTwoSidedInvStatus.noTwoSidedInvInSM3db4aWExport
  noInteriorEliminationDataStatus :=
    SM3db4aWNoInteriorEliminationDataStatus.noInteriorEliminationDataInSM3db4aWExport
  noDtnDataStatus := SM3db4aWNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db4aWExport
  noArithmeticTargetStatus :=
    SM3db4aWNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db4aWExport
  nextPhaseStatus := SM3db4aWNextPhaseStatus.sm3eRr3c1dFullTerminalCoverageConsumer
  equationDatum_eq_source := by
    rfl
  terminalIdentityFieldCertificate_eq_source := by
    rfl
  terminalCoverageSource_eq_certificate := by
    rfl
  terminalCoverageSource_eq_source := by
    rfl
  equationSourceStatus_eq :=
    S.equationSourceStatus_eq
  equationSourceCertificateExportStatus_eq :=
    S.certificateExportStatus_eq
  certificateNextPhaseStatus_eq := by
    rfl
  terminalCoverageTracePivotCoverageStatus_eq := by
    rfl
  terminalCoverageFoldResidualCoverageStatus_eq := by
    rfl
  certificateSourceStatus_eq := by
    rfl
  terminalCoverageExportStatus_eq := by
    rfl
  equationDatumSourceStatus_eq := by
    rfl
  noFreeIdentityFieldStatus_eq := by
    rfl
  noProductIdentityProofStatus_eq := by
    rfl
  noTwoSidedInvStatus_eq := by
    rfl
  noInteriorEliminationDataStatus_eq := by
    rfl
  noDtnDataStatus_eq := by
    rfl
  noArithmeticTargetStatus_eq := by
    rfl
  nextPhaseStatus_eq := by
    rfl

theorem noProductIdentityProof
    (X : GeneratedInteriorTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW Cell p A P wp W E K T) :
    X.noProductIdentityProofStatus =
      SM3db4aWNoProductIdentityProofStatus.noProductIdentityProofInSM3db4aWExport :=
  X.noProductIdentityProofStatus_eq

theorem noTwoSidedInv
    (X : GeneratedInteriorTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW Cell p A P wp W E K T) :
    X.noTwoSidedInvStatus = SM3db4aWNoTwoSidedInvStatus.noTwoSidedInvInSM3db4aWExport :=
  X.noTwoSidedInvStatus_eq

theorem terminalCoverageSource_from_source
    (X : GeneratedInteriorTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW Cell p A P wp W E K T) :
    X.terminalCoverageSource = blockFoldTerminalCoverageSourceFromEquationSourceSM3db4aW X.equationSource :=
  X.terminalCoverageSource_eq_source

end GeneratedInteriorTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW

abbrev RegularGeneratedInteriorTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW
    (ConcreteSubstrate.RegularCell b) p
    (regularGeneratedApproximantStrong b p)
    (regularGeneratedBoundaryInteriorPartition b p) wp
    (regularGeneratedWeightPolicyEntrySource b p wp)
    (regularGeneratedInteriorEliminationCandidateEntry b p wp)
    (regularGeneratedInteriorEliminationCarrier b p wp)
    (regularGeneratedInteriorEliminationTrace b p wp)

abbrev VariableGeneratedInteriorTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedInteriorTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW
    (LevelVariableSubstrate.LevelVariableCell β) p
    (variableGeneratedApproximantStrong β p)
    (variableGeneratedBoundaryInteriorPartition β p) wp
    (variableGeneratedWeightPolicyEntrySource β p wp)
    (variableGeneratedInteriorEliminationCandidateEntry β p wp)
    (variableGeneratedInteriorEliminationCarrier β p wp)
    (variableGeneratedInteriorEliminationTrace β p wp)

def regularTerminalFoldResidualIdentityFieldCertificateFromEquationSourceSM3db4aW
    {b : Nat} {p : ConcretePolicyOf} {wp : WeightPolicy}
    (S : RegularGeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV b p wp) :
    RegularGeneratedInteriorTerminalFoldResidualIdentityFieldCertificateSM3db4aU b p wp :=
  terminalFoldResidualIdentityFieldCertificateFromEquationSourceSM3db4aW S

def variableTerminalFoldResidualIdentityFieldCertificateFromEquationSourceSM3db4aW
    {β : Nat → Nat} {p : ConcretePolicyOf} {wp : WeightPolicy}
    (S : VariableGeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV β p wp) :
    VariableGeneratedInteriorTerminalFoldResidualIdentityFieldCertificateSM3db4aU β p wp :=
  terminalFoldResidualIdentityFieldCertificateFromEquationSourceSM3db4aW S

def regularBlockFoldTerminalCoverageSourceR3c1dFromSM3db4aW
    {b : Nat} {p : ConcretePolicyOf} {wp : WeightPolicy}
    (S : RegularGeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV b p wp) :
    RegularGeneratedInteriorBlockFoldTerminalCoverageSourceR3c1d b p wp :=
  regularBlockFoldTerminalCoverageSourceR3c1dFromSM3db4aU
    (regularTerminalFoldResidualIdentityFieldCertificateFromEquationSourceSM3db4aW S)

def variableBlockFoldTerminalCoverageSourceR3c1dFromSM3db4aW
    {β : Nat → Nat} {p : ConcretePolicyOf} {wp : WeightPolicy}
    (S : VariableGeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV β p wp) :
    VariableGeneratedInteriorBlockFoldTerminalCoverageSourceR3c1d β p wp :=
  variableBlockFoldTerminalCoverageSourceR3c1dFromSM3db4aU
    (variableTerminalFoldResidualIdentityFieldCertificateFromEquationSourceSM3db4aW S)

def regularTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW
    {b : Nat} {p : ConcretePolicyOf} {wp : WeightPolicy}
    (S : RegularGeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV b p wp) :
    RegularGeneratedInteriorTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW b p wp :=
  GeneratedInteriorTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW.fromEquationSource S

def variableTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW
    {β : Nat → Nat} {p : ConcretePolicyOf} {wp : WeightPolicy}
    (S : VariableGeneratedInteriorTerminalFoldResidualIdentityEquationSourceSM3db4aV β p wp) :
    VariableGeneratedInteriorTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW β p wp :=
  GeneratedInteriorTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW.fromEquationSource S

structure SM3db4aWTerminalIdentityFieldCertificateFromEquationSourceLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  equationSourceLedger : SM3db4aVTerminalFoldResidualIdentityEquationSourceLedger b β p regularWeight variableWeight
  regularExport : RegularGeneratedInteriorTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW b p regularWeight
  variableExport : VariableGeneratedInteriorTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW β p variableWeight
  regularCertificate : RegularGeneratedInteriorTerminalFoldResidualIdentityFieldCertificateSM3db4aU b p regularWeight
  variableCertificate : VariableGeneratedInteriorTerminalFoldResidualIdentityFieldCertificateSM3db4aU β p variableWeight
  regularTerminalCoverageSource : RegularGeneratedInteriorBlockFoldTerminalCoverageSourceR3c1d b p regularWeight
  variableTerminalCoverageSource : VariableGeneratedInteriorBlockFoldTerminalCoverageSourceR3c1d β p variableWeight
  ledgerStatus : SM3db4aWLedgerStatus
  nextPhaseStatus : SM3db4aWNextPhaseStatus
  regularExport_eq_source :
    regularExport =
      regularTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW equationSourceLedger.regularSource
  variableExport_eq_source :
    variableExport =
      variableTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW equationSourceLedger.variableSource
  regularCertificate_eq_export :
    regularCertificate = regularExport.terminalIdentityFieldCertificate
  variableCertificate_eq_export :
    variableCertificate = variableExport.terminalIdentityFieldCertificate
  regularCoverage_eq_export :
    regularTerminalCoverageSource = regularExport.terminalCoverageSource
  variableCoverage_eq_export :
    variableTerminalCoverageSource = variableExport.terminalCoverageSource
  regularCertificate_eq_VLedger :
    regularCertificate = equationSourceLedger.regularCertificate
  variableCertificate_eq_VLedger :
    variableCertificate = equationSourceLedger.variableCertificate
  regularCoverage_eq_source :
    regularTerminalCoverageSource =
      regularBlockFoldTerminalCoverageSourceR3c1dFromSM3db4aW equationSourceLedger.regularSource
  variableCoverage_eq_source :
    variableTerminalCoverageSource =
      variableBlockFoldTerminalCoverageSourceR3c1dFromSM3db4aW equationSourceLedger.variableSource
  ledgerStatus_eq :
    ledgerStatus =
      SM3db4aWLedgerStatus.terminalIdentityFieldCertificateAndCoverageExportFromEquationSource
  nextPhaseStatus_eq :
    nextPhaseStatus = SM3db4aWNextPhaseStatus.sm3eRr3c1dFullTerminalCoverageConsumer

namespace SM3db4aWTerminalIdentityFieldCertificateFromEquationSourceLedger

def fromSM3db4aVLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3db4aVTerminalFoldResidualIdentityEquationSourceLedger b β p regularWeight variableWeight) :
    SM3db4aWTerminalIdentityFieldCertificateFromEquationSourceLedger b β p regularWeight variableWeight where
  equationSourceLedger := L
  regularExport := regularTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW L.regularSource
  variableExport := variableTerminalIdentityFieldCertificateFromEquationSourceSM3db4aW L.variableSource
  regularCertificate := L.regularCertificate
  variableCertificate := L.variableCertificate
  regularTerminalCoverageSource := regularBlockFoldTerminalCoverageSourceR3c1dFromSM3db4aW L.regularSource
  variableTerminalCoverageSource := variableBlockFoldTerminalCoverageSourceR3c1dFromSM3db4aW L.variableSource
  ledgerStatus := SM3db4aWLedgerStatus.terminalIdentityFieldCertificateAndCoverageExportFromEquationSource
  nextPhaseStatus := SM3db4aWNextPhaseStatus.sm3eRr3c1dFullTerminalCoverageConsumer
  regularExport_eq_source := by
    rfl
  variableExport_eq_source := by
    rfl
  regularCertificate_eq_export := by
    exact L.regularCertificate_eq_source
  variableCertificate_eq_export := by
    exact L.variableCertificate_eq_source
  regularCoverage_eq_export := by
    rfl
  variableCoverage_eq_export := by
    rfl
  regularCertificate_eq_VLedger := by
    rfl
  variableCertificate_eq_VLedger := by
    rfl
  regularCoverage_eq_source := by
    rfl
  variableCoverage_eq_source := by
    rfl
  ledgerStatus_eq := by
    rfl
  nextPhaseStatus_eq := by
    rfl

end SM3db4aWTerminalIdentityFieldCertificateFromEquationSourceLedger

end Smoke

end CNNA.PillarA.Arithmetic
