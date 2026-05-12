import CNNA.PillarA.Arithmetic.Smoke.GeneratedDegreePivotScaleSourceSM3db2dR

set_option autoImplicit false
open scoped BigOperators

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

namespace Smoke

universe u

inductive SM3db2eR0GeneratedDegreeFormulaStatus where
  | generatedDirichletDegreeIsFiniteGeneratedWeightSum
  deriving DecidableEq, Repr

inductive SM3db2eR0WeightPolicyFormulaStatus where
  | generatedDegreeFormulaDependsOnInputWeightPolicy
  deriving DecidableEq, Repr

inductive SM3db2eR0ConstantUnitFormulaStatus where
  | noConstantUnitFormulaExposedByCurrentGeneratedDegreeAPI
  deriving DecidableEq, Repr

inductive SM3db2eR0NatCastFormulaStatus where
  | noNatCastDegreeFormulaExposedByCurrentGeneratedDegreeAPI
  deriving DecidableEq, Repr

inductive SM3db2eR0OperationalReciprocalSourceStatus where
  | noOperationalReciprocalSourceExposedByCurrentGeneratedDegreeAPI
  deriving DecidableEq, Repr

inductive SM3db2eR0NoScalarInvStatus where
  | noScalarInvInGeneratedDegreeFormulaAudit
  deriving DecidableEq, Repr

inductive SM3db2eR0NoMatrixInvStatus where
  | noMatrixInvInGeneratedDegreeFormulaAudit
  deriving DecidableEq, Repr

inductive SM3db2eR0NoExternalScaleOracleStatus where
  | noExternalScaleOracleInGeneratedDegreeFormulaAudit
  deriving DecidableEq, Repr

inductive SM3db2eR0NoProductIdentityProofStatus where
  | noProductIdentityProofInGeneratedDegreeFormulaAudit
  deriving DecidableEq, Repr

inductive SM3db2eR0NoTwoSidedInvStatus where
  | noTwoSidedInvInGeneratedDegreeFormulaAudit
  deriving DecidableEq, Repr

inductive SM3db2eR0NoDtnDataStatus where
  | noDtnGeneralizedDtnOrMultiSchurDataInSM3db2eR0
  deriving DecidableEq, Repr

inductive SM3db2eR0NoArithmeticTargetStatus where
  | noCharpolyFactorDiscriminantOrL23TargetInSM3db2eR0
  deriving DecidableEq, Repr

inductive SM3db2eR0NextPhaseStatus where
  | sm3db2eRGeneratedDegreePivotReciprocalProfileFromWeightPolicy
  deriving DecidableEq, Repr

theorem generatedDirichlet_degree_eq_entryWeight_sum_SM3db2eR0
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (i : GeneratedApproximantIndex A) :
    generatedDirichlet_degree W i =
      ∑ j : GeneratedApproximantIndex A, generatedEntryWeight W i j := by
  unfold generatedDirichlet_degree
  rfl

theorem generatedDirichlet_degree_eq_generatedAdjacencyWeight_sum_SM3db2eR0
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (i : GeneratedApproximantIndex A) :
    generatedDirichlet_degree W i =
      ∑ j : GeneratedApproximantIndex A,
        if generatedAdjacent i j then W.policy.constantWeight i j else 0 := by
  unfold generatedDirichlet_degree generatedEntryWeight
  rfl

theorem generatedDirichlet_degree_eq_inputPolicyAdjacencyWeight_sum_SM3db2eR0
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (i : GeneratedApproximantIndex A) :
    generatedDirichlet_degree W i =
      ∑ j : GeneratedApproximantIndex A,
        if generatedAdjacent i j then wp.constantWeight i j else 0 := by
  calc
    generatedDirichlet_degree W i =
        ∑ j : GeneratedApproximantIndex A,
          if generatedAdjacent i j then W.policy.constantWeight i j else 0 := by
      exact generatedDirichlet_degree_eq_generatedAdjacencyWeight_sum_SM3db2eR0 W i
    _ = ∑ j : GeneratedApproximantIndex A,
          if generatedAdjacent i j then wp.constantWeight i j else 0 := by
      rw [W.policy_eq_input]

structure GeneratedDegreeFormulaAuditSM3db2eR0
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
  requirement : GeneratedInteriorTracePivotScaleSourceRequirementSM3db2cR Cell p A P wp W E K T
  formulaStatus : SM3db2eR0GeneratedDegreeFormulaStatus
  weightPolicyFormulaStatus : SM3db2eR0WeightPolicyFormulaStatus
  constantUnitFormulaStatus : SM3db2eR0ConstantUnitFormulaStatus
  natCastFormulaStatus : SM3db2eR0NatCastFormulaStatus
  operationalReciprocalSourceStatus : SM3db2eR0OperationalReciprocalSourceStatus
  noScalarInvStatus : SM3db2eR0NoScalarInvStatus
  noMatrixInvStatus : SM3db2eR0NoMatrixInvStatus
  noExternalScaleOracleStatus : SM3db2eR0NoExternalScaleOracleStatus
  noProductIdentityProofStatus : SM3db2eR0NoProductIdentityProofStatus
  noTwoSidedInvStatus : SM3db2eR0NoTwoSidedInvStatus
  noDtnDataStatus : SM3db2eR0NoDtnDataStatus
  noArithmeticTargetStatus : SM3db2eR0NoArithmeticTargetStatus
  nextPhaseStatus : SM3db2eR0NextPhaseStatus
  degree_eq_entryWeight_sum :
    ∀ i : GeneratedApproximantIndex A,
      generatedDirichlet_degree W i =
        ∑ j : GeneratedApproximantIndex A, generatedEntryWeight W i j
  degree_eq_generatedAdjacencyWeight_sum :
    ∀ i : GeneratedApproximantIndex A,
      generatedDirichlet_degree W i =
        ∑ j : GeneratedApproximantIndex A,
          if generatedAdjacent i j then W.policy.constantWeight i j else 0
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
  pivotEntry_eq_entryWeight_sum :
    ∀ pivot : GeneratedInteriorIndex A,
      (T.localStepOf pivot).stepUpdate.pivotEntry =
        ∑ j : GeneratedApproximantIndex A,
          generatedEntryWeight W
            (GeneratedInteriorIndex.toApproximantIndex
              (T.localStepOf pivot).pivotDatum.pivotIndex)
            j
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
  formulaStatus_eq :
    formulaStatus =
      SM3db2eR0GeneratedDegreeFormulaStatus.generatedDirichletDegreeIsFiniteGeneratedWeightSum
  weightPolicyFormulaStatus_eq :
    weightPolicyFormulaStatus =
      SM3db2eR0WeightPolicyFormulaStatus.generatedDegreeFormulaDependsOnInputWeightPolicy
  constantUnitFormulaStatus_eq :
    constantUnitFormulaStatus =
      SM3db2eR0ConstantUnitFormulaStatus.noConstantUnitFormulaExposedByCurrentGeneratedDegreeAPI
  natCastFormulaStatus_eq :
    natCastFormulaStatus =
      SM3db2eR0NatCastFormulaStatus.noNatCastDegreeFormulaExposedByCurrentGeneratedDegreeAPI
  operationalReciprocalSourceStatus_eq :
    operationalReciprocalSourceStatus =
      SM3db2eR0OperationalReciprocalSourceStatus.noOperationalReciprocalSourceExposedByCurrentGeneratedDegreeAPI
  noScalarInvStatus_eq :
    noScalarInvStatus = SM3db2eR0NoScalarInvStatus.noScalarInvInGeneratedDegreeFormulaAudit
  noMatrixInvStatus_eq :
    noMatrixInvStatus = SM3db2eR0NoMatrixInvStatus.noMatrixInvInGeneratedDegreeFormulaAudit
  noExternalScaleOracleStatus_eq :
    noExternalScaleOracleStatus =
      SM3db2eR0NoExternalScaleOracleStatus.noExternalScaleOracleInGeneratedDegreeFormulaAudit
  noProductIdentityProofStatus_eq :
    noProductIdentityProofStatus =
      SM3db2eR0NoProductIdentityProofStatus.noProductIdentityProofInGeneratedDegreeFormulaAudit
  noTwoSidedInvStatus_eq :
    noTwoSidedInvStatus = SM3db2eR0NoTwoSidedInvStatus.noTwoSidedInvInGeneratedDegreeFormulaAudit
  noDtnDataStatus_eq :
    noDtnDataStatus = SM3db2eR0NoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db2eR0
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3db2eR0NoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db2eR0
  nextPhaseStatus_eq :
    nextPhaseStatus =
      SM3db2eR0NextPhaseStatus.sm3db2eRGeneratedDegreePivotReciprocalProfileFromWeightPolicy

namespace GeneratedDegreeFormulaAuditSM3db2eR0

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

def fromRequirement
    (R : GeneratedInteriorTracePivotScaleSourceRequirementSM3db2cR Cell p A P wp W E K T) :
    GeneratedDegreeFormulaAuditSM3db2eR0 Cell p A P wp W E K T where
  requirement := R
  formulaStatus :=
    SM3db2eR0GeneratedDegreeFormulaStatus.generatedDirichletDegreeIsFiniteGeneratedWeightSum
  weightPolicyFormulaStatus :=
    SM3db2eR0WeightPolicyFormulaStatus.generatedDegreeFormulaDependsOnInputWeightPolicy
  constantUnitFormulaStatus :=
    SM3db2eR0ConstantUnitFormulaStatus.noConstantUnitFormulaExposedByCurrentGeneratedDegreeAPI
  natCastFormulaStatus :=
    SM3db2eR0NatCastFormulaStatus.noNatCastDegreeFormulaExposedByCurrentGeneratedDegreeAPI
  operationalReciprocalSourceStatus :=
    SM3db2eR0OperationalReciprocalSourceStatus.noOperationalReciprocalSourceExposedByCurrentGeneratedDegreeAPI
  noScalarInvStatus := SM3db2eR0NoScalarInvStatus.noScalarInvInGeneratedDegreeFormulaAudit
  noMatrixInvStatus := SM3db2eR0NoMatrixInvStatus.noMatrixInvInGeneratedDegreeFormulaAudit
  noExternalScaleOracleStatus :=
    SM3db2eR0NoExternalScaleOracleStatus.noExternalScaleOracleInGeneratedDegreeFormulaAudit
  noProductIdentityProofStatus :=
    SM3db2eR0NoProductIdentityProofStatus.noProductIdentityProofInGeneratedDegreeFormulaAudit
  noTwoSidedInvStatus := SM3db2eR0NoTwoSidedInvStatus.noTwoSidedInvInGeneratedDegreeFormulaAudit
  noDtnDataStatus := SM3db2eR0NoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3db2eR0
  noArithmeticTargetStatus :=
    SM3db2eR0NoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3db2eR0
  nextPhaseStatus :=
    SM3db2eR0NextPhaseStatus.sm3db2eRGeneratedDegreePivotReciprocalProfileFromWeightPolicy
  degree_eq_entryWeight_sum := by
    intro i
    exact generatedDirichlet_degree_eq_entryWeight_sum_SM3db2eR0 W i
  degree_eq_generatedAdjacencyWeight_sum := by
    intro i
    exact generatedDirichlet_degree_eq_generatedAdjacencyWeight_sum_SM3db2eR0 W i
  degree_eq_inputPolicyAdjacencyWeight_sum := by
    intro i
    exact generatedDirichlet_degree_eq_inputPolicyAdjacencyWeight_sum_SM3db2eR0 W i
  pivotEntry_eq_generatedDegree := by
    intro pivot
    exact R.pivotEntry_eq_generatedDegree pivot
  pivotEntry_eq_entryWeight_sum := by
    intro pivot
    calc
      (T.localStepOf pivot).stepUpdate.pivotEntry =
          generatedDirichlet_degree W
            (GeneratedInteriorIndex.toApproximantIndex
              (T.localStepOf pivot).pivotDatum.pivotIndex) := by
        exact R.pivotEntry_eq_generatedDegree pivot
      _ = ∑ j : GeneratedApproximantIndex A,
            generatedEntryWeight W
              (GeneratedInteriorIndex.toApproximantIndex
                (T.localStepOf pivot).pivotDatum.pivotIndex)
              j := by
        exact generatedDirichlet_degree_eq_entryWeight_sum_SM3db2eR0 W
          (GeneratedInteriorIndex.toApproximantIndex
            (T.localStepOf pivot).pivotDatum.pivotIndex)
  pivotEntry_eq_inputPolicyAdjacencyWeight_sum := by
    intro pivot
    calc
      (T.localStepOf pivot).stepUpdate.pivotEntry =
          generatedDirichlet_degree W
            (GeneratedInteriorIndex.toApproximantIndex
              (T.localStepOf pivot).pivotDatum.pivotIndex) := by
        exact R.pivotEntry_eq_generatedDegree pivot
      _ = ∑ j : GeneratedApproximantIndex A,
            if generatedAdjacent
                (GeneratedInteriorIndex.toApproximantIndex
                  (T.localStepOf pivot).pivotDatum.pivotIndex)
                j then
              wp.constantWeight
                (GeneratedInteriorIndex.toApproximantIndex
                  (T.localStepOf pivot).pivotDatum.pivotIndex)
                j
            else 0 := by
        exact generatedDirichlet_degree_eq_inputPolicyAdjacencyWeight_sum_SM3db2eR0 W
          (GeneratedInteriorIndex.toApproximantIndex
            (T.localStepOf pivot).pivotDatum.pivotIndex)
  formulaStatus_eq := by
    rfl
  weightPolicyFormulaStatus_eq := by
    rfl
  constantUnitFormulaStatus_eq := by
    rfl
  natCastFormulaStatus_eq := by
    rfl
  operationalReciprocalSourceStatus_eq := by
    rfl
  noScalarInvStatus_eq := by
    rfl
  noMatrixInvStatus_eq := by
    rfl
  noExternalScaleOracleStatus_eq := by
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

def fromSM3db2dAudit
    (A0 : GeneratedDegreePivotScaleSourceAuditSM3db2dR Cell p A P wp W E K T) :
    GeneratedDegreeFormulaAuditSM3db2eR0 Cell p A P wp W E K T :=
  fromRequirement A0.requirement

def fromSM3db2cRequirement
    (R : GeneratedInteriorTracePivotScaleSourceRequirementSM3db2cR Cell p A P wp W E K T) :
    GeneratedDegreeFormulaAuditSM3db2eR0 Cell p A P wp W E K T :=
  fromRequirement R

def fromSourceAudit
    (A0 : GeneratedInteriorLocalStepSchurCancellationSourceAuditR3c1b0 Cell p A P wp W E K T) :
    GeneratedDegreeFormulaAuditSM3db2eR0 Cell p A P wp W E K T :=
  fromRequirement
    (GeneratedInteriorTracePivotScaleSourceRequirementSM3db2cR.fromSourceAudit A0)

theorem degree_formula_is_inputPolicyAdjacencyWeight_sum
    (A0 : GeneratedDegreeFormulaAuditSM3db2eR0 Cell p A P wp W E K T)
    (i : GeneratedApproximantIndex A) :
    generatedDirichlet_degree W i =
      ∑ j : GeneratedApproximantIndex A,
        if generatedAdjacent i j then wp.constantWeight i j else 0 :=
  A0.degree_eq_inputPolicyAdjacencyWeight_sum i

theorem pivotEntry_formula_is_inputPolicyAdjacencyWeight_sum
    (A0 : GeneratedDegreeFormulaAuditSM3db2eR0 Cell p A P wp W E K T)
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
  A0.pivotEntry_eq_inputPolicyAdjacencyWeight_sum pivot

theorem operationalReciprocalSource_not_exposed
    (A0 : GeneratedDegreeFormulaAuditSM3db2eR0 Cell p A P wp W E K T) :
    A0.operationalReciprocalSourceStatus =
      SM3db2eR0OperationalReciprocalSourceStatus.noOperationalReciprocalSourceExposedByCurrentGeneratedDegreeAPI :=
  A0.operationalReciprocalSourceStatus_eq

theorem nextPhase_is_SM3db2eR
    (A0 : GeneratedDegreeFormulaAuditSM3db2eR0 Cell p A P wp W E K T) :
    A0.nextPhaseStatus =
      SM3db2eR0NextPhaseStatus.sm3db2eRGeneratedDegreePivotReciprocalProfileFromWeightPolicy :=
  A0.nextPhaseStatus_eq

end GeneratedDegreeFormulaAuditSM3db2eR0

abbrev RegularGeneratedDegreeFormulaAuditSM3db2eR0
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedDegreeFormulaAuditSM3db2eR0
    (ConcreteSubstrate.RegularCell b) p
    (regularGeneratedApproximantStrong b p)
    (regularGeneratedBoundaryInteriorPartition b p) wp
    (regularGeneratedWeightPolicyEntrySource b p wp)
    (regularGeneratedInteriorEliminationCandidateEntry b p wp)
    (regularGeneratedInteriorEliminationCarrier b p wp)
    (regularGeneratedInteriorEliminationTrace b p wp)

abbrev VariableGeneratedDegreeFormulaAuditSM3db2eR0
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :=
  GeneratedDegreeFormulaAuditSM3db2eR0
    (LevelVariableSubstrate.LevelVariableCell β) p
    (variableGeneratedApproximantStrong β p)
    (variableGeneratedBoundaryInteriorPartition β p) wp
    (variableGeneratedWeightPolicyEntrySource β p wp)
    (variableGeneratedInteriorEliminationCandidateEntry β p wp)
    (variableGeneratedInteriorEliminationCarrier β p wp)
    (variableGeneratedInteriorEliminationTrace β p wp)

def regularGeneratedDegreeFormulaAuditSM3db2eR0
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    RegularGeneratedDegreeFormulaAuditSM3db2eR0 b p wp :=
  GeneratedDegreeFormulaAuditSM3db2eR0.fromSourceAudit
    (regularLocalStepSchurCancellationSourceAuditR3c1b0 b p wp)

def variableGeneratedDegreeFormulaAuditSM3db2eR0
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    VariableGeneratedDegreeFormulaAuditSM3db2eR0 β p wp :=
  GeneratedDegreeFormulaAuditSM3db2eR0.fromSourceAudit
    (variableLocalStepSchurCancellationSourceAuditR3c1b0 β p wp)

structure SM3db2eR0GeneratedDegreeFormulaAuditLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  regularAudit : RegularGeneratedDegreeFormulaAuditSM3db2eR0 b p regularWeight
  variableAudit : VariableGeneratedDegreeFormulaAuditSM3db2eR0 β p variableWeight
  regularFormulaStatus_eq :
    regularAudit.formulaStatus =
      SM3db2eR0GeneratedDegreeFormulaStatus.generatedDirichletDegreeIsFiniteGeneratedWeightSum
  variableFormulaStatus_eq :
    variableAudit.formulaStatus =
      SM3db2eR0GeneratedDegreeFormulaStatus.generatedDirichletDegreeIsFiniteGeneratedWeightSum
  regularWeightPolicyFormulaStatus_eq :
    regularAudit.weightPolicyFormulaStatus =
      SM3db2eR0WeightPolicyFormulaStatus.generatedDegreeFormulaDependsOnInputWeightPolicy
  variableWeightPolicyFormulaStatus_eq :
    variableAudit.weightPolicyFormulaStatus =
      SM3db2eR0WeightPolicyFormulaStatus.generatedDegreeFormulaDependsOnInputWeightPolicy
  regularNoOperationalReciprocal_eq :
    regularAudit.operationalReciprocalSourceStatus =
      SM3db2eR0OperationalReciprocalSourceStatus.noOperationalReciprocalSourceExposedByCurrentGeneratedDegreeAPI
  variableNoOperationalReciprocal_eq :
    variableAudit.operationalReciprocalSourceStatus =
      SM3db2eR0OperationalReciprocalSourceStatus.noOperationalReciprocalSourceExposedByCurrentGeneratedDegreeAPI
  regularNextPhase_eq :
    regularAudit.nextPhaseStatus =
      SM3db2eR0NextPhaseStatus.sm3db2eRGeneratedDegreePivotReciprocalProfileFromWeightPolicy
  variableNextPhase_eq :
    variableAudit.nextPhaseStatus =
      SM3db2eR0NextPhaseStatus.sm3db2eRGeneratedDegreePivotReciprocalProfileFromWeightPolicy

namespace SM3db2eR0GeneratedDegreeFormulaAuditLedger

def fromRegularAndVariable
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (regularAudit : RegularGeneratedDegreeFormulaAuditSM3db2eR0 b p regularWeight)
    (variableAudit : VariableGeneratedDegreeFormulaAuditSM3db2eR0 β p variableWeight) :
    SM3db2eR0GeneratedDegreeFormulaAuditLedger b β p regularWeight variableWeight where
  regularAudit := regularAudit
  variableAudit := variableAudit
  regularFormulaStatus_eq := regularAudit.formulaStatus_eq
  variableFormulaStatus_eq := variableAudit.formulaStatus_eq
  regularWeightPolicyFormulaStatus_eq := regularAudit.weightPolicyFormulaStatus_eq
  variableWeightPolicyFormulaStatus_eq := variableAudit.weightPolicyFormulaStatus_eq
  regularNoOperationalReciprocal_eq := regularAudit.operationalReciprocalSourceStatus_eq
  variableNoOperationalReciprocal_eq := variableAudit.operationalReciprocalSourceStatus_eq
  regularNextPhase_eq := regularAudit.nextPhaseStatus_eq
  variableNextPhase_eq := variableAudit.nextPhaseStatus_eq

end SM3db2eR0GeneratedDegreeFormulaAuditLedger

def sm3db2eR0GeneratedDegreeFormulaAuditLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    SM3db2eR0GeneratedDegreeFormulaAuditLedger b β p regularWeight variableWeight :=
  SM3db2eR0GeneratedDegreeFormulaAuditLedger.fromRegularAndVariable
    (regularGeneratedDegreeFormulaAuditSM3db2eR0 b p regularWeight)
    (variableGeneratedDegreeFormulaAuditSM3db2eR0 β p variableWeight)

end Smoke

end CNNA.PillarA.Arithmetic
