import CNNA.PillarA.Arithmetic.Smoke.GeneratedDegreeFormulaAuditSM3db2eR0

set_option autoImplicit false
open scoped BigOperators

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

namespace Smoke

universe u

inductive SM3db2eRUnitDegreeCaseStatus where
  | noDefinitionalUnitDegreeCaseInCurrentGeneratedDegreeAPI
  deriving DecidableEq, Repr

inductive SM3db2eRWeightPolicyReciprocalDatumStatus where
  | noOperationalWeightPolicyReciprocalDatumInCurrentGeneratedDegreeAPI
  deriving DecidableEq, Repr

inductive SM3db2eRGeneratedReciprocalSourceStatus where
  | noGeneratedReciprocalSourceInCurrentGeneratedDegreeAPI
  deriving DecidableEq, Repr

inductive SM3db2eRProfileConstructionStatus where
  | generatedDegreePivotReciprocalProfileNotConstructedFromCurrentWeightPolicySumAPI
  deriving DecidableEq, Repr

inductive SM3db2eRNoScalarInvStatus where
  | noScalarInvInGeneratedDegreePivotReciprocalProfileFromWeightPolicy
  deriving DecidableEq, Repr

inductive SM3db2eRNoMatrixInvStatus where
  | noMatrixInvInGeneratedDegreePivotReciprocalProfileFromWeightPolicy
  deriving DecidableEq, Repr

inductive SM3db2eRNoExternalScaleOracleStatus where
  | noExternalScaleOracleInGeneratedDegreePivotReciprocalProfileFromWeightPolicy
  deriving DecidableEq, Repr

inductive SM3db2eRNoFreeScaleTableStatus where
  | noFreeScaleTableInGeneratedDegreePivotReciprocalProfileFromWeightPolicy
  deriving DecidableEq, Repr

inductive SM3db2eRNoProductIdentityProofStatus where
  | noProductIdentityProofInGeneratedDegreePivotReciprocalProfileFromWeightPolicy
  deriving DecidableEq, Repr

inductive SM3db2eRNoTwoSidedInvStatus where
  | noTwoSidedInvInGeneratedDegreePivotReciprocalProfileFromWeightPolicy
  deriving DecidableEq, Repr

inductive SM3db2eRNoDtnDataStatus where
  | noDtnGeneralizedDtnOrMultiSchurDataInSM3db2eR
  deriving DecidableEq, Repr

inductive SM3db2eRNoArithmeticTargetStatus where
  | noCharpolyFactorDiscriminantOrL23TargetInSM3db2eR
  deriving DecidableEq, Repr

inductive SM3db2eRNextPhaseStatus where
  | sm3db2fRGeneratedOperationalDegreeReciprocalSource
  deriving DecidableEq, Repr

structure GeneratedDegreePivotReciprocalProfileFromWeightPolicySM3db2eR
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
  audit : GeneratedDegreeFormulaAuditSM3db2eR0 Cell p A P wp W E K T
  unitDegreeCaseStatus : SM3db2eRUnitDegreeCaseStatus
  weightPolicyReciprocalDatumStatus : SM3db2eRWeightPolicyReciprocalDatumStatus
  generatedReciprocalSourceStatus : SM3db2eRGeneratedReciprocalSourceStatus
  profileConstructionStatus : SM3db2eRProfileConstructionStatus
  noScalarInvStatus : SM3db2eRNoScalarInvStatus
  noMatrixInvStatus : SM3db2eRNoMatrixInvStatus
  noExternalScaleOracleStatus : SM3db2eRNoExternalScaleOracleStatus
  noFreeScaleTableStatus : SM3db2eRNoFreeScaleTableStatus
  noProductIdentityProofStatus : SM3db2eRNoProductIdentityProofStatus
  noTwoSidedInvStatus : SM3db2eRNoTwoSidedInvStatus
  noDtnDataStatus : SM3db2eRNoDtnDataStatus
  noArithmeticTargetStatus : SM3db2eRNoArithmeticTargetStatus
  nextPhaseStatus : SM3db2eRNextPhaseStatus
  degree_eq_inputPolicyAdjacencyWeight_sum :
    ∀ i : GeneratedApproximantIndex A,
      generatedDirichlet_degree W i =
        ∑ j : GeneratedApproximantIndex A,
          if generatedAdjacent i j then wp.constantWeight i j else 0
  pivotEntry_eq_generatedDegree :
    ∀ pivot : GeneratedInteriorIndex A,
      (T.localStepOf pivot).stepUpdate.pivotEntry =
        generatedDirichlet_degree W
          (GeneratedInteriorIndex.toApproximantIndex
            (T.localStepOf pivot).pivotDatum.pivotIndex)
  pivotEntry_eq_inputPolicyAdjacencyWeight_sum :
    ∀ pivot : GeneratedInteriorIndex A,
      (T.localStepOf pivot).stepUpdate.pivotEntry =
        ∑ j : GeneratedApproximantIndex A,
          if generatedAdjacent
              (GeneratedInteriorIndex.toApproximantIndex
                (T.localStepOf pivot).pivotDatum.pivotIndex)
              j then
            wp.constantWeight
              (GeneratedInteriorIndex.toApproximantIndex
                (T.localStepOf pivot).pivotDatum.pivotIndex)
              j
          else 0
  audit_operationalReciprocalSourceStatus_eq :
    audit.operationalReciprocalSourceStatus =
      SM3db2eR0OperationalReciprocalSourceStatus.noOperationalReciprocalSourceExposedByCurrentGeneratedDegreeAPI
  unitDegreeCaseStatus_eq :
    unitDegreeCaseStatus =
      SM3db2eRUnitDegreeCaseStatus.noDefinitionalUnitDegreeCaseInCurrentGeneratedDegreeAPI
  weightPolicyReciprocalDatumStatus_eq :
    weightPolicyReciprocalDatumStatus =
      SM3db2eRWeightPolicyReciprocalDatumStatus.noOperationalWeightPolicyReciprocalDatumInCurrentGeneratedDegreeAPI
  generatedReciprocalSourceStatus_eq :
    generatedReciprocalSourceStatus =
      SM3db2eRGeneratedReciprocalSourceStatus.noGeneratedReciprocalSourceInCurrentGeneratedDegreeAPI
  profileConstructionStatus_eq :
    profileConstructionStatus =
      SM3db2eRProfileConstructionStatus.generatedDegreePivotReciprocalProfileNotConstructedFromCurrentWeightPolicySumAPI
  noScalarInvStatus_eq :
    noScalarInvStatus =
      SM3db2eRNoScalarInvStatus.noScalarInvInGeneratedDegreePivotReciprocalProfileFromWeightPolicy
  noMatrixInvStatus_eq :
    noMatrixInvStatus =
      SM3db2eRNoMatrixInvStatus.noMatrixInvInGeneratedDegreePivotReciprocalProfileFromWeightPolicy
  noExternalScaleOracleStatus_eq :
    noExternalScaleOracleStatus =
      SM3db2eRNoExternalScaleOracleStatus.noExternalScaleOracleInGeneratedDegreePivotReciprocalProfileFromWeightPolicy
  noFreeScaleTableStatus_eq :
    noFreeScaleTableStatus =
      SM3db2eRNoFreeScaleTableStatus.noFreeScaleTableInGeneratedDegreePivotReciprocalProfileFromWeightPolicy
  noProductIdentityProofStatus_eq :
    noProductIdentityProofStatus =
      SM3db2eRNoProductIdentityProofStatus.noProductIdentityProofInGeneratedDegreePivotReciprocalProfileFromWeightPolicy
  noTwoSidedInvStatus_eq :
    noTwoSidedInvStatus =
      SM3db2eRNoTwoSidedInvStatus.noTwoSidedInvInGeneratedDegreePivotReciprocalProfileFromWeightPolicy
  noDtnDataStatus_eq :
    noDtnDataStatus = SM3db2eRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db2eR
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3db2eRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db2eR
  nextPhaseStatus_eq :
    nextPhaseStatus = SM3db2eRNextPhaseStatus.sm3db2fRGeneratedOperationalDegreeReciprocalSource

namespace GeneratedDegreePivotReciprocalProfileFromWeightPolicySM3db2eR

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

def fromFormulaAudit
    (A0 : GeneratedDegreeFormulaAuditSM3db2eR0 Cell p A P wp W E K T) :
    GeneratedDegreePivotReciprocalProfileFromWeightPolicySM3db2eR Cell p A P wp W E K T where
  audit := A0
  unitDegreeCaseStatus :=
    SM3db2eRUnitDegreeCaseStatus.noDefinitionalUnitDegreeCaseInCurrentGeneratedDegreeAPI
  weightPolicyReciprocalDatumStatus :=
    SM3db2eRWeightPolicyReciprocalDatumStatus.noOperationalWeightPolicyReciprocalDatumInCurrentGeneratedDegreeAPI
  generatedReciprocalSourceStatus :=
    SM3db2eRGeneratedReciprocalSourceStatus.noGeneratedReciprocalSourceInCurrentGeneratedDegreeAPI
  profileConstructionStatus :=
    SM3db2eRProfileConstructionStatus.generatedDegreePivotReciprocalProfileNotConstructedFromCurrentWeightPolicySumAPI
  noScalarInvStatus :=
    SM3db2eRNoScalarInvStatus.noScalarInvInGeneratedDegreePivotReciprocalProfileFromWeightPolicy
  noMatrixInvStatus :=
    SM3db2eRNoMatrixInvStatus.noMatrixInvInGeneratedDegreePivotReciprocalProfileFromWeightPolicy
  noExternalScaleOracleStatus :=
    SM3db2eRNoExternalScaleOracleStatus.noExternalScaleOracleInGeneratedDegreePivotReciprocalProfileFromWeightPolicy
  noFreeScaleTableStatus :=
    SM3db2eRNoFreeScaleTableStatus.noFreeScaleTableInGeneratedDegreePivotReciprocalProfileFromWeightPolicy
  noProductIdentityProofStatus :=
    SM3db2eRNoProductIdentityProofStatus.noProductIdentityProofInGeneratedDegreePivotReciprocalProfileFromWeightPolicy
  noTwoSidedInvStatus :=
    SM3db2eRNoTwoSidedInvStatus.noTwoSidedInvInGeneratedDegreePivotReciprocalProfileFromWeightPolicy
  noDtnDataStatus := SM3db2eRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db2eR
  noArithmeticTargetStatus :=
    SM3db2eRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db2eR
  nextPhaseStatus := SM3db2eRNextPhaseStatus.sm3db2fRGeneratedOperationalDegreeReciprocalSource
  degree_eq_inputPolicyAdjacencyWeight_sum := by
    intro i
    exact A0.degree_eq_inputPolicyAdjacencyWeight_sum i
  pivotEntry_eq_generatedDegree := by
    intro pivot
    exact A0.pivotEntry_eq_generatedDegree pivot
  pivotEntry_eq_inputPolicyAdjacencyWeight_sum := by
    intro pivot
    exact A0.pivotEntry_eq_inputPolicyAdjacencyWeight_sum pivot
  audit_operationalReciprocalSourceStatus_eq := A0.operationalReciprocalSourceStatus_eq
  unitDegreeCaseStatus_eq := by
    rfl
  weightPolicyReciprocalDatumStatus_eq := by
    rfl
  generatedReciprocalSourceStatus_eq := by
    rfl
  profileConstructionStatus_eq := by
    rfl
  noScalarInvStatus_eq := by
    rfl
  noMatrixInvStatus_eq := by
    rfl
  noExternalScaleOracleStatus_eq := by
    rfl
  noFreeScaleTableStatus_eq := by
    rfl
  noProductIdentityProofStatus_eq := by
    rfl
  noTwoSidedInvStatus_eq := by
    rfl
  noDtnDataStatus_eq := by
    rfl
  noArithmeticTargetStatus_eq := by
    rfl
  nextPhaseStatus_eq := by
    rfl

theorem degree_formula_from_weightPolicy_sum
    (D : GeneratedDegreePivotReciprocalProfileFromWeightPolicySM3db2eR Cell p A P wp W E K T)
    (i : GeneratedApproximantIndex A) :
    generatedDirichlet_degree W i =
      ∑ j : GeneratedApproximantIndex A,
        if generatedAdjacent i j then wp.constantWeight i j else 0 :=
  D.degree_eq_inputPolicyAdjacencyWeight_sum i

theorem pivotEntry_formula_from_weightPolicy_sum
    (D : GeneratedDegreePivotReciprocalProfileFromWeightPolicySM3db2eR Cell p A P wp W E K T)
    (pivot : GeneratedInteriorIndex A) :
    (T.localStepOf pivot).stepUpdate.pivotEntry =
      ∑ j : GeneratedApproximantIndex A,
        if generatedAdjacent
            (GeneratedInteriorIndex.toApproximantIndex
              (T.localStepOf pivot).pivotDatum.pivotIndex)
            j then
          wp.constantWeight
            (GeneratedInteriorIndex.toApproximantIndex
              (T.localStepOf pivot).pivotDatum.pivotIndex)
            j
        else 0 :=
  D.pivotEntry_eq_inputPolicyAdjacencyWeight_sum pivot

theorem profileConstructionStatus_notConstructed
    (D : GeneratedDegreePivotReciprocalProfileFromWeightPolicySM3db2eR Cell p A P wp W E K T) :
    D.profileConstructionStatus =
      SM3db2eRProfileConstructionStatus.generatedDegreePivotReciprocalProfileNotConstructedFromCurrentWeightPolicySumAPI :=
  D.profileConstructionStatus_eq

theorem nextPhase_is_SM3db2fR
    (D : GeneratedDegreePivotReciprocalProfileFromWeightPolicySM3db2eR Cell p A P wp W E K T) :
    D.nextPhaseStatus = SM3db2eRNextPhaseStatus.sm3db2fRGeneratedOperationalDegreeReciprocalSource :=
  D.nextPhaseStatus_eq

end GeneratedDegreePivotReciprocalProfileFromWeightPolicySM3db2eR

abbrev RegularGeneratedDegreePivotReciprocalProfileFromWeightPolicySM3db2eR
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedDegreePivotReciprocalProfileFromWeightPolicySM3db2eR
    (ConcreteSubstrate.RegularCell b) p
    (regularGeneratedApproximantStrong b p)
    (regularGeneratedBoundaryInteriorPartition b p) wp
    (regularGeneratedWeightPolicyEntrySource b p wp)
    (regularGeneratedInteriorEliminationCandidateEntry b p wp)
    (regularGeneratedInteriorEliminationCarrier b p wp)
    (regularGeneratedInteriorEliminationTrace b p wp)

abbrev VariableGeneratedDegreePivotReciprocalProfileFromWeightPolicySM3db2eR
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedDegreePivotReciprocalProfileFromWeightPolicySM3db2eR
    (LevelVariableSubstrate.LevelVariableCell β) p
    (variableGeneratedApproximantStrong β p)
    (variableGeneratedBoundaryInteriorPartition β p) wp
    (variableGeneratedWeightPolicyEntrySource β p wp)
    (variableGeneratedInteriorEliminationCandidateEntry β p wp)
    (variableGeneratedInteriorEliminationCarrier β p wp)
    (variableGeneratedInteriorEliminationTrace β p wp)

def regularGeneratedDegreePivotReciprocalProfileFromWeightPolicySM3db2eR
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    RegularGeneratedDegreePivotReciprocalProfileFromWeightPolicySM3db2eR b p wp :=
  GeneratedDegreePivotReciprocalProfileFromWeightPolicySM3db2eR.fromFormulaAudit
    (regularGeneratedDegreeFormulaAuditSM3db2eR0 b p wp)

def variableGeneratedDegreePivotReciprocalProfileFromWeightPolicySM3db2eR
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    VariableGeneratedDegreePivotReciprocalProfileFromWeightPolicySM3db2eR β p wp :=
  GeneratedDegreePivotReciprocalProfileFromWeightPolicySM3db2eR.fromFormulaAudit
    (variableGeneratedDegreeFormulaAuditSM3db2eR0 β p wp)

structure SM3db2eRGeneratedDegreePivotReciprocalProfileFromWeightPolicyLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  regularAttempt : RegularGeneratedDegreePivotReciprocalProfileFromWeightPolicySM3db2eR b p regularWeight
  variableAttempt : VariableGeneratedDegreePivotReciprocalProfileFromWeightPolicySM3db2eR β p variableWeight
  regularProfileConstructionStatus_eq :
    regularAttempt.profileConstructionStatus =
      SM3db2eRProfileConstructionStatus.generatedDegreePivotReciprocalProfileNotConstructedFromCurrentWeightPolicySumAPI
  variableProfileConstructionStatus_eq :
    variableAttempt.profileConstructionStatus =
      SM3db2eRProfileConstructionStatus.generatedDegreePivotReciprocalProfileNotConstructedFromCurrentWeightPolicySumAPI
  regularNoFreeScaleTableStatus_eq :
    regularAttempt.noFreeScaleTableStatus =
      SM3db2eRNoFreeScaleTableStatus.noFreeScaleTableInGeneratedDegreePivotReciprocalProfileFromWeightPolicy
  variableNoFreeScaleTableStatus_eq :
    variableAttempt.noFreeScaleTableStatus =
      SM3db2eRNoFreeScaleTableStatus.noFreeScaleTableInGeneratedDegreePivotReciprocalProfileFromWeightPolicy
  regularNoScalarInvStatus_eq :
    regularAttempt.noScalarInvStatus =
      SM3db2eRNoScalarInvStatus.noScalarInvInGeneratedDegreePivotReciprocalProfileFromWeightPolicy
  variableNoScalarInvStatus_eq :
    variableAttempt.noScalarInvStatus =
      SM3db2eRNoScalarInvStatus.noScalarInvInGeneratedDegreePivotReciprocalProfileFromWeightPolicy
  regularNoMatrixInvStatus_eq :
    regularAttempt.noMatrixInvStatus =
      SM3db2eRNoMatrixInvStatus.noMatrixInvInGeneratedDegreePivotReciprocalProfileFromWeightPolicy
  variableNoMatrixInvStatus_eq :
    variableAttempt.noMatrixInvStatus =
      SM3db2eRNoMatrixInvStatus.noMatrixInvInGeneratedDegreePivotReciprocalProfileFromWeightPolicy
  regularNoExternalScaleOracleStatus_eq :
    regularAttempt.noExternalScaleOracleStatus =
      SM3db2eRNoExternalScaleOracleStatus.noExternalScaleOracleInGeneratedDegreePivotReciprocalProfileFromWeightPolicy
  variableNoExternalScaleOracleStatus_eq :
    variableAttempt.noExternalScaleOracleStatus =
      SM3db2eRNoExternalScaleOracleStatus.noExternalScaleOracleInGeneratedDegreePivotReciprocalProfileFromWeightPolicy
  regularNoProductIdentityProofStatus_eq :
    regularAttempt.noProductIdentityProofStatus =
      SM3db2eRNoProductIdentityProofStatus.noProductIdentityProofInGeneratedDegreePivotReciprocalProfileFromWeightPolicy
  variableNoProductIdentityProofStatus_eq :
    variableAttempt.noProductIdentityProofStatus =
      SM3db2eRNoProductIdentityProofStatus.noProductIdentityProofInGeneratedDegreePivotReciprocalProfileFromWeightPolicy
  regularNoTwoSidedInvStatus_eq :
    regularAttempt.noTwoSidedInvStatus =
      SM3db2eRNoTwoSidedInvStatus.noTwoSidedInvInGeneratedDegreePivotReciprocalProfileFromWeightPolicy
  variableNoTwoSidedInvStatus_eq :
    variableAttempt.noTwoSidedInvStatus =
      SM3db2eRNoTwoSidedInvStatus.noTwoSidedInvInGeneratedDegreePivotReciprocalProfileFromWeightPolicy
  regularNoDtnDataStatus_eq :
    regularAttempt.noDtnDataStatus = SM3db2eRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db2eR
  variableNoDtnDataStatus_eq :
    variableAttempt.noDtnDataStatus = SM3db2eRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db2eR
  regularNoArithmeticTargetStatus_eq :
    regularAttempt.noArithmeticTargetStatus =
      SM3db2eRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db2eR
  variableNoArithmeticTargetStatus_eq :
    variableAttempt.noArithmeticTargetStatus =
      SM3db2eRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db2eR
  regularNextPhaseStatus_eq :
    regularAttempt.nextPhaseStatus = SM3db2eRNextPhaseStatus.sm3db2fRGeneratedOperationalDegreeReciprocalSource
  variableNextPhaseStatus_eq :
    variableAttempt.nextPhaseStatus = SM3db2eRNextPhaseStatus.sm3db2fRGeneratedOperationalDegreeReciprocalSource

namespace SM3db2eRGeneratedDegreePivotReciprocalProfileFromWeightPolicyLedger

def fromRegularAndVariable
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (regularAttempt : RegularGeneratedDegreePivotReciprocalProfileFromWeightPolicySM3db2eR b p regularWeight)
    (variableAttempt : VariableGeneratedDegreePivotReciprocalProfileFromWeightPolicySM3db2eR β p variableWeight) :
    SM3db2eRGeneratedDegreePivotReciprocalProfileFromWeightPolicyLedger b β p regularWeight variableWeight where
  regularAttempt := regularAttempt
  variableAttempt := variableAttempt
  regularProfileConstructionStatus_eq := regularAttempt.profileConstructionStatus_eq
  variableProfileConstructionStatus_eq := variableAttempt.profileConstructionStatus_eq
  regularNoFreeScaleTableStatus_eq := regularAttempt.noFreeScaleTableStatus_eq
  variableNoFreeScaleTableStatus_eq := variableAttempt.noFreeScaleTableStatus_eq
  regularNoScalarInvStatus_eq := regularAttempt.noScalarInvStatus_eq
  variableNoScalarInvStatus_eq := variableAttempt.noScalarInvStatus_eq
  regularNoMatrixInvStatus_eq := regularAttempt.noMatrixInvStatus_eq
  variableNoMatrixInvStatus_eq := variableAttempt.noMatrixInvStatus_eq
  regularNoExternalScaleOracleStatus_eq := regularAttempt.noExternalScaleOracleStatus_eq
  variableNoExternalScaleOracleStatus_eq := variableAttempt.noExternalScaleOracleStatus_eq
  regularNoProductIdentityProofStatus_eq := regularAttempt.noProductIdentityProofStatus_eq
  variableNoProductIdentityProofStatus_eq := variableAttempt.noProductIdentityProofStatus_eq
  regularNoTwoSidedInvStatus_eq := regularAttempt.noTwoSidedInvStatus_eq
  variableNoTwoSidedInvStatus_eq := variableAttempt.noTwoSidedInvStatus_eq
  regularNoDtnDataStatus_eq := regularAttempt.noDtnDataStatus_eq
  variableNoDtnDataStatus_eq := variableAttempt.noDtnDataStatus_eq
  regularNoArithmeticTargetStatus_eq := regularAttempt.noArithmeticTargetStatus_eq
  variableNoArithmeticTargetStatus_eq := variableAttempt.noArithmeticTargetStatus_eq
  regularNextPhaseStatus_eq := regularAttempt.nextPhaseStatus_eq
  variableNextPhaseStatus_eq := variableAttempt.nextPhaseStatus_eq

end SM3db2eRGeneratedDegreePivotReciprocalProfileFromWeightPolicyLedger

def sm3db2eRGeneratedDegreePivotReciprocalProfileFromWeightPolicyLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    SM3db2eRGeneratedDegreePivotReciprocalProfileFromWeightPolicyLedger b β p regularWeight variableWeight :=
  SM3db2eRGeneratedDegreePivotReciprocalProfileFromWeightPolicyLedger.fromRegularAndVariable
    (regularGeneratedDegreePivotReciprocalProfileFromWeightPolicySM3db2eR b p regularWeight)
    (variableGeneratedDegreePivotReciprocalProfileFromWeightPolicySM3db2eR β p variableWeight)

end Smoke

end CNNA.PillarA.Arithmetic
