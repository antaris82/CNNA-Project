import CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorBlock

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

namespace Smoke

universe u

inductive GeneratedInteriorEliminationCandidateSource where
  | candidateFromDiagonalOnly
  | candidateFromDegreeDiagonal
  | candidateFromOffdiagCoupledProfile
  | candidateFromTreeRecursiveProfile
  | candidateFromGeneralFiniteEliminationProfile
  | candidateObstructed
  deriving DecidableEq, Repr

inductive GeneratedInteriorEliminationCandidateSourceCompatible :
    GeneratedInteriorEliminationCandidateSource → InteriorBlockStructureProfile → Prop where
  | diagonalOnly :
      GeneratedInteriorEliminationCandidateSourceCompatible
        GeneratedInteriorEliminationCandidateSource.candidateFromDiagonalOnly
        InteriorBlockStructureProfile.diagonalOnly
  | degreeDiagonal :
      GeneratedInteriorEliminationCandidateSourceCompatible
        GeneratedInteriorEliminationCandidateSource.candidateFromDegreeDiagonal
        InteriorBlockStructureProfile.degreeDiagonal
  | offdiagCoupled :
      GeneratedInteriorEliminationCandidateSourceCompatible
        GeneratedInteriorEliminationCandidateSource.candidateFromOffdiagCoupledProfile
        InteriorBlockStructureProfile.offdiagCoupled
  | treeRecursive :
      GeneratedInteriorEliminationCandidateSourceCompatible
        GeneratedInteriorEliminationCandidateSource.candidateFromTreeRecursiveProfile
        InteriorBlockStructureProfile.treeRecursive
  | generalFiniteEliminationNeeded :
      GeneratedInteriorEliminationCandidateSourceCompatible
        GeneratedInteriorEliminationCandidateSource.candidateFromGeneralFiniteEliminationProfile
        InteriorBlockStructureProfile.generalFiniteEliminationNeeded
  | obstructed :
      GeneratedInteriorEliminationCandidateSourceCompatible
        GeneratedInteriorEliminationCandidateSource.candidateObstructed
        InteriorBlockStructureProfile.obstructed

inductive SM3dRProfileOriginStatus where
  | profileFromSM3cRInteriorBlockStructureProfile
  deriving DecidableEq, Repr

inductive SM3dRCandidateKindStatus where
  | structureDependentCandidateOnly
  deriving DecidableEq, Repr

inductive SM3dRNoMatrixInvStatus where
  | noMatrixInv
  deriving DecidableEq, Repr

inductive SM3dRNoFreeInverseStatus where
  | noFreeInverseField
  deriving DecidableEq, Repr

inductive SM3dRNoTwoSidedInvStatus where
  | noTwoSidedInvProofInSM3dR
  deriving DecidableEq, Repr

inductive SM3dRNoExternalInteriorEliminationCertificateStatus where
  | noExternalInteriorEliminationCertificateAssumption
  deriving DecidableEq, Repr

inductive SM3dRNoDtnDataStatus where
  | noDtnGeneralizedDtnOrMultiSchurDataYet
  deriving DecidableEq, Repr

inductive SM3dRNoArithmeticTargetStatus where
  | noCharpolyFactorDiscriminantOrL23TargetInSM3dR
  deriving DecidableEq, Repr

inductive SM3dRGeneratedInteriorEliminationCandidateLedgerStatus where
  | generatedInteriorEliminationCandidatesBuiltFromSM3cRProfiles
  deriving DecidableEq, Repr

structure GeneratedInteriorEliminationCandidate
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf)
    (A : GeneratedApproximantStrong Cell p)
    (P : GeneratedBoundaryInteriorPartition Cell p A)
    (wp : WeightPolicy)
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp) where
  profileData : GeneratedInteriorBlockStructureProfile Cell p A P wp W
  profile : InteriorBlockStructureProfile
  source : GeneratedInteriorEliminationCandidateSource
  sourceCompatible :
    GeneratedInteriorEliminationCandidateSourceCompatible source profileData.profile
  profileOriginStatus : SM3dRProfileOriginStatus
  candidateKindStatus : SM3dRCandidateKindStatus
  noMatrixInvStatus : SM3dRNoMatrixInvStatus
  noFreeInverseStatus : SM3dRNoFreeInverseStatus
  noTwoSidedInvStatus : SM3dRNoTwoSidedInvStatus
  noExternalInteriorEliminationCertificateStatus :
    SM3dRNoExternalInteriorEliminationCertificateStatus
  noDtnDataStatus : SM3dRNoDtnDataStatus
  noArithmeticTargetStatus : SM3dRNoArithmeticTargetStatus
  profile_eq_SM3cR_profile : profile = profileData.profile
  profileOriginStatus_eq :
    profileOriginStatus =
      SM3dRProfileOriginStatus.profileFromSM3cRInteriorBlockStructureProfile
  candidateKindStatus_eq :
    candidateKindStatus = SM3dRCandidateKindStatus.structureDependentCandidateOnly
  noMatrixInvStatus_eq : noMatrixInvStatus = SM3dRNoMatrixInvStatus.noMatrixInv
  noFreeInverseStatus_eq :
    noFreeInverseStatus = SM3dRNoFreeInverseStatus.noFreeInverseField
  noTwoSidedInvStatus_eq :
    noTwoSidedInvStatus = SM3dRNoTwoSidedInvStatus.noTwoSidedInvProofInSM3dR
  noExternalInteriorEliminationCertificateStatus_eq :
    noExternalInteriorEliminationCertificateStatus =
      SM3dRNoExternalInteriorEliminationCertificateStatus.noExternalInteriorEliminationCertificateAssumption
  noDtnDataStatus_eq :
    noDtnDataStatus = SM3dRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataYet
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3dRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3dR

namespace GeneratedInteriorEliminationCandidate

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {p : ConcretePolicyOf}
variable {A : GeneratedApproximantStrong Cell p}
variable {P : GeneratedBoundaryInteriorPartition Cell p A}
variable {wp : WeightPolicy}
variable {W : GeneratedWeightPolicyEntrySource Cell p A P wp}

private def fromProfileWithSource
    (G : GeneratedInteriorBlockStructureProfile Cell p A P wp W)
    (source : GeneratedInteriorEliminationCandidateSource)
    (sourceCompatible :
      GeneratedInteriorEliminationCandidateSourceCompatible source G.profile) :
    GeneratedInteriorEliminationCandidate Cell p A P wp W where
  profileData := G
  profile := G.profile
  source := source
  sourceCompatible := sourceCompatible
  profileOriginStatus :=
    SM3dRProfileOriginStatus.profileFromSM3cRInteriorBlockStructureProfile
  candidateKindStatus := SM3dRCandidateKindStatus.structureDependentCandidateOnly
  noMatrixInvStatus := SM3dRNoMatrixInvStatus.noMatrixInv
  noFreeInverseStatus := SM3dRNoFreeInverseStatus.noFreeInverseField
  noTwoSidedInvStatus := SM3dRNoTwoSidedInvStatus.noTwoSidedInvProofInSM3dR
  noExternalInteriorEliminationCertificateStatus :=
    SM3dRNoExternalInteriorEliminationCertificateStatus.noExternalInteriorEliminationCertificateAssumption
  noDtnDataStatus := SM3dRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataYet
  noArithmeticTargetStatus :=
    SM3dRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3dR
  profile_eq_SM3cR_profile := by
    rfl
  profileOriginStatus_eq := by
    rfl
  candidateKindStatus_eq := by
    rfl
  noMatrixInvStatus_eq := by
    rfl
  noFreeInverseStatus_eq := by
    rfl
  noTwoSidedInvStatus_eq := by
    rfl
  noExternalInteriorEliminationCertificateStatus_eq := by
    rfl
  noDtnDataStatus_eq := by
    rfl
  noArithmeticTargetStatus_eq := by
    rfl

def candidate_from_diagonalOnly
    (G : GeneratedInteriorBlockStructureProfile Cell p A P wp W)
    (hG : G.profile = InteriorBlockStructureProfile.diagonalOnly) :
    GeneratedInteriorEliminationCandidate Cell p A P wp W :=
  fromProfileWithSource G
    GeneratedInteriorEliminationCandidateSource.candidateFromDiagonalOnly
    (hG.symm ▸ GeneratedInteriorEliminationCandidateSourceCompatible.diagonalOnly)

def candidate_from_degreeDiagonal
    (G : GeneratedInteriorBlockStructureProfile Cell p A P wp W)
    (hG : G.profile = InteriorBlockStructureProfile.degreeDiagonal) :
    GeneratedInteriorEliminationCandidate Cell p A P wp W :=
  fromProfileWithSource G
    GeneratedInteriorEliminationCandidateSource.candidateFromDegreeDiagonal
    (hG.symm ▸ GeneratedInteriorEliminationCandidateSourceCompatible.degreeDiagonal)

def candidate_from_offdiagCoupledProfile
    (G : GeneratedInteriorBlockStructureProfile Cell p A P wp W)
    (hG : G.profile = InteriorBlockStructureProfile.offdiagCoupled) :
    GeneratedInteriorEliminationCandidate Cell p A P wp W :=
  fromProfileWithSource G
    GeneratedInteriorEliminationCandidateSource.candidateFromOffdiagCoupledProfile
    (hG.symm ▸ GeneratedInteriorEliminationCandidateSourceCompatible.offdiagCoupled)

def candidate_from_treeRecursiveProfile
    (G : GeneratedInteriorBlockStructureProfile Cell p A P wp W)
    (hG : G.profile = InteriorBlockStructureProfile.treeRecursive) :
    GeneratedInteriorEliminationCandidate Cell p A P wp W :=
  fromProfileWithSource G
    GeneratedInteriorEliminationCandidateSource.candidateFromTreeRecursiveProfile
    (hG.symm ▸ GeneratedInteriorEliminationCandidateSourceCompatible.treeRecursive)

def candidate_from_generalFiniteEliminationProfile
    (G : GeneratedInteriorBlockStructureProfile Cell p A P wp W)
    (hG : G.profile = InteriorBlockStructureProfile.generalFiniteEliminationNeeded) :
    GeneratedInteriorEliminationCandidate Cell p A P wp W :=
  fromProfileWithSource G
    GeneratedInteriorEliminationCandidateSource.candidateFromGeneralFiniteEliminationProfile
    (hG.symm ▸ GeneratedInteriorEliminationCandidateSourceCompatible.generalFiniteEliminationNeeded)

def candidate_obstructed
    (G : GeneratedInteriorBlockStructureProfile Cell p A P wp W)
    (hG : G.profile = InteriorBlockStructureProfile.obstructed) :
    GeneratedInteriorEliminationCandidate Cell p A P wp W :=
  fromProfileWithSource G
    GeneratedInteriorEliminationCandidateSource.candidateObstructed
    (hG.symm ▸ GeneratedInteriorEliminationCandidateSourceCompatible.obstructed)

theorem candidate_profile_eq_SM3cR_profile
    (C : GeneratedInteriorEliminationCandidate Cell p A P wp W) :
    C.profile = C.profileData.profile :=
  C.profile_eq_SM3cR_profile

theorem candidate_source_compatible
    (C : GeneratedInteriorEliminationCandidate Cell p A P wp W) :
    GeneratedInteriorEliminationCandidateSourceCompatible C.source C.profileData.profile :=
  C.sourceCompatible

theorem noMatrixInv
    (C : GeneratedInteriorEliminationCandidate Cell p A P wp W) :
    C.noMatrixInvStatus = SM3dRNoMatrixInvStatus.noMatrixInv :=
  C.noMatrixInvStatus_eq

theorem noFreeInverse
    (C : GeneratedInteriorEliminationCandidate Cell p A P wp W) :
    C.noFreeInverseStatus = SM3dRNoFreeInverseStatus.noFreeInverseField :=
  C.noFreeInverseStatus_eq

theorem noTwoSidedInv
    (C : GeneratedInteriorEliminationCandidate Cell p A P wp W) :
    C.noTwoSidedInvStatus = SM3dRNoTwoSidedInvStatus.noTwoSidedInvProofInSM3dR :=
  C.noTwoSidedInvStatus_eq

theorem noExternalInteriorEliminationCertificate
    (C : GeneratedInteriorEliminationCandidate Cell p A P wp W) :
    C.noExternalInteriorEliminationCertificateStatus =
      SM3dRNoExternalInteriorEliminationCertificateStatus.noExternalInteriorEliminationCertificateAssumption :=
  C.noExternalInteriorEliminationCertificateStatus_eq

theorem noDtnDataYet
    (C : GeneratedInteriorEliminationCandidate Cell p A P wp W) :
    C.noDtnDataStatus = SM3dRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataYet :=
  C.noDtnDataStatus_eq

theorem noArithmeticTarget
    (C : GeneratedInteriorEliminationCandidate Cell p A P wp W) :
    C.noArithmeticTargetStatus =
      SM3dRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3dR :=
  C.noArithmeticTargetStatus_eq

end GeneratedInteriorEliminationCandidate

def regularGeneratedInteriorEliminationCandidate
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedInteriorEliminationCandidate
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) wp
      (regularGeneratedWeightPolicyEntrySource b p wp) :=
  GeneratedInteriorEliminationCandidate.candidate_from_treeRecursiveProfile
    (regularGeneratedInteriorBlockStructureProfile b p wp)
    (regularGeneratedInteriorBlockStructureProfile b p wp).profile_eq_treeRecursive

def variableGeneratedInteriorEliminationCandidate
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedInteriorEliminationCandidate
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) wp
      (variableGeneratedWeightPolicyEntrySource β p wp) :=
  GeneratedInteriorEliminationCandidate.candidate_from_treeRecursiveProfile
    (variableGeneratedInteriorBlockStructureProfile β p wp)
    (variableGeneratedInteriorBlockStructureProfile β p wp).profile_eq_treeRecursive

structure SM3dRGeneratedInteriorEliminationCandidateLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  status : SM3dRGeneratedInteriorEliminationCandidateLedgerStatus
  sm3cLedger : SM3cRGeneratedInteriorBlockLedger b β p regularWeight variableWeight
  regularCandidate :
    GeneratedInteriorEliminationCandidate
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
  variableCandidate :
    GeneratedInteriorEliminationCandidate
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
  sm3cLedger_eq_main :
    sm3cLedger = sm3cRGeneratedInteriorBlockLedger b β p regularWeight variableWeight
  regularCandidate_eq_main :
    regularCandidate = regularGeneratedInteriorEliminationCandidate b p regularWeight
  variableCandidate_eq_main :
    variableCandidate = variableGeneratedInteriorEliminationCandidate β p variableWeight
  regularProfile_eq_sm3cRProfile :
    regularCandidate.profile = regularCandidate.profileData.profile
  variableProfile_eq_sm3cRProfile :
    variableCandidate.profile = variableCandidate.profileData.profile
  regularSource_treeRecursive :
    regularCandidate.source =
      GeneratedInteriorEliminationCandidateSource.candidateFromTreeRecursiveProfile
  variableSource_treeRecursive :
    variableCandidate.source =
      GeneratedInteriorEliminationCandidateSource.candidateFromTreeRecursiveProfile
  regularProfile_treeRecursive :
    regularCandidate.profile = InteriorBlockStructureProfile.treeRecursive
  variableProfile_treeRecursive :
    variableCandidate.profile = InteriorBlockStructureProfile.treeRecursive
  regularNoMatrixInv :
    regularCandidate.noMatrixInvStatus = SM3dRNoMatrixInvStatus.noMatrixInv
  variableNoMatrixInv :
    variableCandidate.noMatrixInvStatus = SM3dRNoMatrixInvStatus.noMatrixInv
  regularNoFreeInverse :
    regularCandidate.noFreeInverseStatus = SM3dRNoFreeInverseStatus.noFreeInverseField
  variableNoFreeInverse :
    variableCandidate.noFreeInverseStatus = SM3dRNoFreeInverseStatus.noFreeInverseField
  regularNoTwoSidedInv :
    regularCandidate.noTwoSidedInvStatus = SM3dRNoTwoSidedInvStatus.noTwoSidedInvProofInSM3dR
  variableNoTwoSidedInv :
    variableCandidate.noTwoSidedInvStatus = SM3dRNoTwoSidedInvStatus.noTwoSidedInvProofInSM3dR
  regularNoExternalInteriorEliminationCertificate :
    regularCandidate.noExternalInteriorEliminationCertificateStatus =
      SM3dRNoExternalInteriorEliminationCertificateStatus.noExternalInteriorEliminationCertificateAssumption
  variableNoExternalInteriorEliminationCertificate :
    variableCandidate.noExternalInteriorEliminationCertificateStatus =
      SM3dRNoExternalInteriorEliminationCertificateStatus.noExternalInteriorEliminationCertificateAssumption
  regularNoDtnDataYet :
    regularCandidate.noDtnDataStatus =
      SM3dRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataYet
  variableNoDtnDataYet :
    variableCandidate.noDtnDataStatus =
      SM3dRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataYet
  regularNoArithmeticTarget :
    regularCandidate.noArithmeticTargetStatus =
      SM3dRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3dR
  variableNoArithmeticTarget :
    variableCandidate.noArithmeticTargetStatus =
      SM3dRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3dR
  status_eq_closed :
    status =
      SM3dRGeneratedInteriorEliminationCandidateLedgerStatus.generatedInteriorEliminationCandidatesBuiltFromSM3cRProfiles

def sm3dRGeneratedInteriorEliminationCandidateLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    SM3dRGeneratedInteriorEliminationCandidateLedger b β p regularWeight variableWeight where
  status :=
    SM3dRGeneratedInteriorEliminationCandidateLedgerStatus.generatedInteriorEliminationCandidatesBuiltFromSM3cRProfiles
  sm3cLedger := sm3cRGeneratedInteriorBlockLedger b β p regularWeight variableWeight
  regularCandidate := regularGeneratedInteriorEliminationCandidate b p regularWeight
  variableCandidate := variableGeneratedInteriorEliminationCandidate β p variableWeight
  sm3cLedger_eq_main := by
    rfl
  regularCandidate_eq_main := by
    rfl
  variableCandidate_eq_main := by
    rfl
  regularProfile_eq_sm3cRProfile := by
    rfl
  variableProfile_eq_sm3cRProfile := by
    rfl
  regularSource_treeRecursive := by
    rfl
  variableSource_treeRecursive := by
    rfl
  regularProfile_treeRecursive := by
    rfl
  variableProfile_treeRecursive := by
    rfl
  regularNoMatrixInv := by
    rfl
  variableNoMatrixInv := by
    rfl
  regularNoFreeInverse := by
    rfl
  variableNoFreeInverse := by
    rfl
  regularNoTwoSidedInv := by
    rfl
  variableNoTwoSidedInv := by
    rfl
  regularNoExternalInteriorEliminationCertificate := by
    rfl
  variableNoExternalInteriorEliminationCertificate := by
    rfl
  regularNoDtnDataYet := by
    rfl
  variableNoDtnDataYet := by
    rfl
  regularNoArithmeticTarget := by
    rfl
  variableNoArithmeticTarget := by
    rfl
  status_eq_closed := by
    rfl

theorem sm3dRGeneratedInteriorEliminationCandidateLedger_status
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3dRGeneratedInteriorEliminationCandidateLedger b β p regularWeight variableWeight).status =
      SM3dRGeneratedInteriorEliminationCandidateLedgerStatus.generatedInteriorEliminationCandidatesBuiltFromSM3cRProfiles := by
  rfl

theorem sm3dRGeneratedInteriorEliminationCandidateLedger_regularSource_treeRecursive
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3dRGeneratedInteriorEliminationCandidateLedger b β p regularWeight variableWeight).regularCandidate.source =
      GeneratedInteriorEliminationCandidateSource.candidateFromTreeRecursiveProfile := by
  rfl

theorem sm3dRGeneratedInteriorEliminationCandidateLedger_variableSource_treeRecursive
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3dRGeneratedInteriorEliminationCandidateLedger b β p regularWeight variableWeight).variableCandidate.source =
      GeneratedInteriorEliminationCandidateSource.candidateFromTreeRecursiveProfile := by
  rfl

theorem sm3dRGeneratedInteriorEliminationCandidateLedger_regularNoMatrixInv
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3dRGeneratedInteriorEliminationCandidateLedger b β p regularWeight variableWeight).regularCandidate.noMatrixInvStatus =
      SM3dRNoMatrixInvStatus.noMatrixInv := by
  rfl

theorem sm3dRGeneratedInteriorEliminationCandidateLedger_variableNoFreeInverse
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3dRGeneratedInteriorEliminationCandidateLedger b β p regularWeight variableWeight).variableCandidate.noFreeInverseStatus =
      SM3dRNoFreeInverseStatus.noFreeInverseField := by
  rfl

theorem sm3dRGeneratedInteriorEliminationCandidateLedger_regularNoTwoSidedInv
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3dRGeneratedInteriorEliminationCandidateLedger b β p regularWeight variableWeight).regularCandidate.noTwoSidedInvStatus =
      SM3dRNoTwoSidedInvStatus.noTwoSidedInvProofInSM3dR := by
  rfl

theorem sm3dRGeneratedInteriorEliminationCandidateLedger_variableNoDtnDataYet
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3dRGeneratedInteriorEliminationCandidateLedger b β p regularWeight variableWeight).variableCandidate.noDtnDataStatus =
      SM3dRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataYet := by
  rfl

end Smoke

end CNNA.PillarA.Arithmetic
