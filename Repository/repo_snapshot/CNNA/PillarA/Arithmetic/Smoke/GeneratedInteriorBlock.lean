import CNNA.PillarA.Arithmetic.Smoke.GeneratedDirichletEntry

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

namespace Smoke

universe u

inductive SM3cRInteriorRestrictionStatus where
  | interiorRestrictionFromSM3bRDirichletMatrix
  deriving DecidableEq, Repr

inductive SM3cREntryClassificationStatus where
  | interiorEntriesClassifiedFromGeneratedDirichletEntries
  deriving DecidableEq, Repr

inductive SM3cRNoFreeInteriorBlockStatus where
  | noFreeInteriorBlockTable
  deriving DecidableEq, Repr

inductive SM3cRZeroRuleStatus where
  | zeroRuleInheritedFromGeneratedAdjacency
  deriving DecidableEq, Repr

inductive SM3cROffdiagRuleStatus where
  | offdiagRuleInheritedFromParentChildOrCouplingAdjacency
  deriving DecidableEq, Repr

inductive SM3cRDiagRuleStatus where
  | diagonalRuleInheritedFromGeneratedDegree
  deriving DecidableEq, Repr

inductive InteriorBlockStructureProfile where
  | diagonalOnly
  | degreeDiagonal
  | offdiagCoupled
  | treeRecursive
  | generalFiniteEliminationNeeded
  | obstructed
  deriving DecidableEq, Repr

inductive SM3cRNoInverseStatus where
  | noInverseOrEliminationFormulaInSM3cR
  deriving DecidableEq, Repr

inductive SM3cRNoDtnStatus where
  | noDtnGeneralizedDtnOrMultiSchurInSM3cR
  deriving DecidableEq, Repr

inductive SM3cRNoArithmeticTargetStatus where
  | noCharpolyFactorDiscriminantOrL23TargetInSM3cR
  deriving DecidableEq, Repr

inductive SM3cRGeneratedInteriorBlockLedgerStatus where
  | generatedInteriorBlockEntriesClassified
  deriving DecidableEq, Repr

def generatedInteriorBlock_entry
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (i j : GeneratedInteriorIndex A) : ℝ :=
  generatedDirichlet_entry W
    (GeneratedInteriorIndex.toApproximantIndex i)
    (GeneratedInteriorIndex.toApproximantIndex j)

def generatedInteriorBlock
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp) :
    Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ :=
  fun i j => generatedInteriorBlock_entry W i j

theorem generatedInteriorBlock_entry_eq_dirichlet
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (i j : GeneratedInteriorIndex A) :
    generatedInteriorBlock_entry W i j =
      generatedDirichlet_entry W
        (GeneratedInteriorIndex.toApproximantIndex i)
        (GeneratedInteriorIndex.toApproximantIndex j) := by
  rfl

theorem generatedInteriorBlock_from_dirichlet
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (i j : GeneratedInteriorIndex A) :
    generatedInteriorBlock W i j =
      generatedDirichletMatrix W
        (GeneratedInteriorIndex.toApproximantIndex i)
        (GeneratedInteriorIndex.toApproximantIndex j) := by
  rfl

theorem generatedInteriorBlock_zero_of_not_adjacent
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    {i j : GeneratedInteriorIndex A}
    (hij : GeneratedInteriorIndex.toApproximantIndex i ≠
      GeneratedInteriorIndex.toApproximantIndex j)
    (hadj : ¬ generatedAdjacent
      (GeneratedInteriorIndex.toApproximantIndex i)
      (GeneratedInteriorIndex.toApproximantIndex j)) :
    generatedInteriorBlock W i j = 0 := by
  calc
    generatedInteriorBlock W i j =
        generatedDirichletMatrix W
          (GeneratedInteriorIndex.toApproximantIndex i)
          (GeneratedInteriorIndex.toApproximantIndex j) :=
      generatedInteriorBlock_from_dirichlet W i j
    _ = 0 :=
      zero_of_not_adjacent W hij hadj

theorem generatedInteriorBlock_offdiag_of_parent_child_or_coupling
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    {i j : GeneratedInteriorIndex A}
    (hij : GeneratedInteriorIndex.toApproximantIndex i ≠
      GeneratedInteriorIndex.toApproximantIndex j)
    (hadj : generatedAdjacent
      (GeneratedInteriorIndex.toApproximantIndex i)
      (GeneratedInteriorIndex.toApproximantIndex j)) :
    generatedInteriorBlock W i j =
      - W.policy.constantWeight
        (GeneratedInteriorIndex.toApproximantIndex i)
        (GeneratedInteriorIndex.toApproximantIndex j) := by
  calc
    generatedInteriorBlock W i j =
        generatedDirichletMatrix W
          (GeneratedInteriorIndex.toApproximantIndex i)
          (GeneratedInteriorIndex.toApproximantIndex j) :=
      generatedInteriorBlock_from_dirichlet W i j
    _ = - W.policy.constantWeight
          (GeneratedInteriorIndex.toApproximantIndex i)
          (GeneratedInteriorIndex.toApproximantIndex j) :=
      offdiag_of_adjacent W hij hadj

theorem generatedInteriorBlock_diag_degree_or_regularized_degree
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (i : GeneratedInteriorIndex A) :
    generatedInteriorBlock W i i =
      generatedDirichlet_degree W (GeneratedInteriorIndex.toApproximantIndex i) := by
  calc
    generatedInteriorBlock W i i =
        generatedDirichletMatrix W
          (GeneratedInteriorIndex.toApproximantIndex i)
          (GeneratedInteriorIndex.toApproximantIndex i) :=
      generatedInteriorBlock_from_dirichlet W i i
    _ = generatedDirichlet_degree W (GeneratedInteriorIndex.toApproximantIndex i) :=
      diag_degree_or_regularized_degree W (GeneratedInteriorIndex.toApproximantIndex i)

structure GeneratedInteriorBlockStructureProfile
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf)
    (A : GeneratedApproximantStrong Cell p)
    (P : GeneratedBoundaryInteriorPartition Cell p A)
    (wp : WeightPolicy)
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp) where
  profile : InteriorBlockStructureProfile
  restrictionStatus : SM3cRInteriorRestrictionStatus
  entryClassificationStatus : SM3cREntryClassificationStatus
  noFreeInteriorBlockStatus : SM3cRNoFreeInteriorBlockStatus
  zeroRuleStatus : SM3cRZeroRuleStatus
  offdiagRuleStatus : SM3cROffdiagRuleStatus
  diagRuleStatus : SM3cRDiagRuleStatus
  noInverseStatus : SM3cRNoInverseStatus
  noDtnStatus : SM3cRNoDtnStatus
  noArithmeticTargetStatus : SM3cRNoArithmeticTargetStatus
  profile_eq_treeRecursive : profile = InteriorBlockStructureProfile.treeRecursive
  restrictionStatus_eq :
    restrictionStatus =
      SM3cRInteriorRestrictionStatus.interiorRestrictionFromSM3bRDirichletMatrix
  entryClassificationStatus_eq :
    entryClassificationStatus =
      SM3cREntryClassificationStatus.interiorEntriesClassifiedFromGeneratedDirichletEntries
  noFreeInteriorBlockStatus_eq :
    noFreeInteriorBlockStatus = SM3cRNoFreeInteriorBlockStatus.noFreeInteriorBlockTable
  zeroRuleStatus_eq :
    zeroRuleStatus = SM3cRZeroRuleStatus.zeroRuleInheritedFromGeneratedAdjacency
  offdiagRuleStatus_eq :
    offdiagRuleStatus =
      SM3cROffdiagRuleStatus.offdiagRuleInheritedFromParentChildOrCouplingAdjacency
  diagRuleStatus_eq :
    diagRuleStatus = SM3cRDiagRuleStatus.diagonalRuleInheritedFromGeneratedDegree
  noInverseStatus_eq :
    noInverseStatus = SM3cRNoInverseStatus.noInverseOrEliminationFormulaInSM3cR
  noDtnStatus_eq :
    noDtnStatus = SM3cRNoDtnStatus.noDtnGeneralizedDtnOrMultiSchurInSM3cR
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3cRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3cR
  block_from_dirichlet :
    ∀ i j : GeneratedInteriorIndex A,
      generatedInteriorBlock W i j =
        generatedDirichletMatrix W
          (GeneratedInteriorIndex.toApproximantIndex i)
          (GeneratedInteriorIndex.toApproximantIndex j)
  block_zero_of_not_adjacent :
    ∀ {i j : GeneratedInteriorIndex A},
      GeneratedInteriorIndex.toApproximantIndex i ≠
        GeneratedInteriorIndex.toApproximantIndex j →
      ¬ generatedAdjacent
        (GeneratedInteriorIndex.toApproximantIndex i)
        (GeneratedInteriorIndex.toApproximantIndex j) →
      generatedInteriorBlock W i j = 0
  block_offdiag_of_parent_child_or_coupling :
    ∀ {i j : GeneratedInteriorIndex A},
      GeneratedInteriorIndex.toApproximantIndex i ≠
        GeneratedInteriorIndex.toApproximantIndex j →
      generatedAdjacent
        (GeneratedInteriorIndex.toApproximantIndex i)
        (GeneratedInteriorIndex.toApproximantIndex j) →
      generatedInteriorBlock W i j =
        - W.policy.constantWeight
          (GeneratedInteriorIndex.toApproximantIndex i)
          (GeneratedInteriorIndex.toApproximantIndex j)
  block_diag_degree_or_regularized_degree :
    ∀ i : GeneratedInteriorIndex A,
      generatedInteriorBlock W i i =
        generatedDirichlet_degree W (GeneratedInteriorIndex.toApproximantIndex i)

namespace GeneratedInteriorBlockStructureProfile

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {p : ConcretePolicyOf}
variable {A : GeneratedApproximantStrong Cell p}
variable {P : GeneratedBoundaryInteriorPartition Cell p A}
variable {wp : WeightPolicy}
variable (W : GeneratedWeightPolicyEntrySource Cell p A P wp)

def fromEntryLemmas :
    GeneratedInteriorBlockStructureProfile Cell p A P wp W where
  profile := InteriorBlockStructureProfile.treeRecursive
  restrictionStatus :=
    SM3cRInteriorRestrictionStatus.interiorRestrictionFromSM3bRDirichletMatrix
  entryClassificationStatus :=
    SM3cREntryClassificationStatus.interiorEntriesClassifiedFromGeneratedDirichletEntries
  noFreeInteriorBlockStatus := SM3cRNoFreeInteriorBlockStatus.noFreeInteriorBlockTable
  zeroRuleStatus := SM3cRZeroRuleStatus.zeroRuleInheritedFromGeneratedAdjacency
  offdiagRuleStatus :=
    SM3cROffdiagRuleStatus.offdiagRuleInheritedFromParentChildOrCouplingAdjacency
  diagRuleStatus := SM3cRDiagRuleStatus.diagonalRuleInheritedFromGeneratedDegree
  noInverseStatus := SM3cRNoInverseStatus.noInverseOrEliminationFormulaInSM3cR
  noDtnStatus := SM3cRNoDtnStatus.noDtnGeneralizedDtnOrMultiSchurInSM3cR
  noArithmeticTargetStatus :=
    SM3cRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3cR
  profile_eq_treeRecursive := by
    rfl
  restrictionStatus_eq := by
    rfl
  entryClassificationStatus_eq := by
    rfl
  noFreeInteriorBlockStatus_eq := by
    rfl
  zeroRuleStatus_eq := by
    rfl
  offdiagRuleStatus_eq := by
    rfl
  diagRuleStatus_eq := by
    rfl
  noInverseStatus_eq := by
    rfl
  noDtnStatus_eq := by
    rfl
  noArithmeticTargetStatus_eq := by
    rfl
  block_from_dirichlet := by
    intro i j
    exact generatedInteriorBlock_from_dirichlet W i j
  block_zero_of_not_adjacent := by
    intro i j hij hadj
    exact generatedInteriorBlock_zero_of_not_adjacent W hij hadj
  block_offdiag_of_parent_child_or_coupling := by
    intro i j hij hadj
    exact generatedInteriorBlock_offdiag_of_parent_child_or_coupling W hij hadj
  block_diag_degree_or_regularized_degree := by
    intro i
    exact generatedInteriorBlock_diag_degree_or_regularized_degree W i

theorem profile_treeRecursive
    (G : GeneratedInteriorBlockStructureProfile Cell p A P wp W) :
    G.profile = InteriorBlockStructureProfile.treeRecursive :=
  G.profile_eq_treeRecursive

theorem no_inverse
    (G : GeneratedInteriorBlockStructureProfile Cell p A P wp W) :
    G.noInverseStatus = SM3cRNoInverseStatus.noInverseOrEliminationFormulaInSM3cR :=
  G.noInverseStatus_eq

theorem no_dtn
    (G : GeneratedInteriorBlockStructureProfile Cell p A P wp W) :
    G.noDtnStatus = SM3cRNoDtnStatus.noDtnGeneralizedDtnOrMultiSchurInSM3cR :=
  G.noDtnStatus_eq

end GeneratedInteriorBlockStructureProfile

def regularGeneratedInteriorBlock
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    Matrix
      (GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
      (GeneratedInteriorIndex (regularGeneratedApproximantStrong b p)) ℝ :=
  generatedInteriorBlock (regularGeneratedWeightPolicyEntrySource b p wp)

def variableGeneratedInteriorBlock
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    Matrix
      (GeneratedInteriorIndex (variableGeneratedApproximantStrong β p))
      (GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) ℝ :=
  generatedInteriorBlock (variableGeneratedWeightPolicyEntrySource β p wp)

def regularGeneratedInteriorBlockStructureProfile
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedInteriorBlockStructureProfile
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) wp
      (regularGeneratedWeightPolicyEntrySource b p wp) :=
  GeneratedInteriorBlockStructureProfile.fromEntryLemmas
    (regularGeneratedWeightPolicyEntrySource b p wp)

def variableGeneratedInteriorBlockStructureProfile
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedInteriorBlockStructureProfile
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) wp
      (variableGeneratedWeightPolicyEntrySource β p wp) :=
  GeneratedInteriorBlockStructureProfile.fromEntryLemmas
    (variableGeneratedWeightPolicyEntrySource β p wp)

structure SM3cRGeneratedInteriorBlockLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  status : SM3cRGeneratedInteriorBlockLedgerStatus
  sm3bLedger : SM3bRGeneratedDirichletEntryLedger b β p regularWeight variableWeight
  regularProfile :
    GeneratedInteriorBlockStructureProfile
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
  variableProfile :
    GeneratedInteriorBlockStructureProfile
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
  sm3bLedger_eq_main :
    sm3bLedger = sm3bRGeneratedDirichletEntryLedger b β p regularWeight variableWeight
  regularProfile_eq_main :
    regularProfile = regularGeneratedInteriorBlockStructureProfile b p regularWeight
  variableProfile_eq_main :
    variableProfile = variableGeneratedInteriorBlockStructureProfile β p variableWeight
  regularProfile_treeRecursive :
    regularProfile.profile = InteriorBlockStructureProfile.treeRecursive
  variableProfile_treeRecursive :
    variableProfile.profile = InteriorBlockStructureProfile.treeRecursive
  regularNoFreeInteriorBlock :
    regularProfile.noFreeInteriorBlockStatus =
      SM3cRNoFreeInteriorBlockStatus.noFreeInteriorBlockTable
  variableNoFreeInteriorBlock :
    variableProfile.noFreeInteriorBlockStatus =
      SM3cRNoFreeInteriorBlockStatus.noFreeInteriorBlockTable
  regularNoInverse :
    regularProfile.noInverseStatus =
      SM3cRNoInverseStatus.noInverseOrEliminationFormulaInSM3cR
  variableNoInverse :
    variableProfile.noInverseStatus =
      SM3cRNoInverseStatus.noInverseOrEliminationFormulaInSM3cR
  regularNoDtn :
    regularProfile.noDtnStatus =
      SM3cRNoDtnStatus.noDtnGeneralizedDtnOrMultiSchurInSM3cR
  variableNoDtn :
    variableProfile.noDtnStatus =
      SM3cRNoDtnStatus.noDtnGeneralizedDtnOrMultiSchurInSM3cR
  regularNoArithmeticTarget :
    regularProfile.noArithmeticTargetStatus =
      SM3cRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3cR
  variableNoArithmeticTarget :
    variableProfile.noArithmeticTargetStatus =
      SM3cRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3cR
  status_eq_closed :
    status = SM3cRGeneratedInteriorBlockLedgerStatus.generatedInteriorBlockEntriesClassified

def sm3cRGeneratedInteriorBlockLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    SM3cRGeneratedInteriorBlockLedger b β p regularWeight variableWeight where
  status := SM3cRGeneratedInteriorBlockLedgerStatus.generatedInteriorBlockEntriesClassified
  sm3bLedger := sm3bRGeneratedDirichletEntryLedger b β p regularWeight variableWeight
  regularProfile := regularGeneratedInteriorBlockStructureProfile b p regularWeight
  variableProfile := variableGeneratedInteriorBlockStructureProfile β p variableWeight
  sm3bLedger_eq_main := by
    rfl
  regularProfile_eq_main := by
    rfl
  variableProfile_eq_main := by
    rfl
  regularProfile_treeRecursive := by
    rfl
  variableProfile_treeRecursive := by
    rfl
  regularNoFreeInteriorBlock := by
    rfl
  variableNoFreeInteriorBlock := by
    rfl
  regularNoInverse := by
    rfl
  variableNoInverse := by
    rfl
  regularNoDtn := by
    rfl
  variableNoDtn := by
    rfl
  regularNoArithmeticTarget := by
    rfl
  variableNoArithmeticTarget := by
    rfl
  status_eq_closed := by
    rfl

theorem sm3cRGeneratedInteriorBlockLedger_status
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3cRGeneratedInteriorBlockLedger b β p regularWeight variableWeight).status =
      SM3cRGeneratedInteriorBlockLedgerStatus.generatedInteriorBlockEntriesClassified := by
  rfl

theorem sm3cRGeneratedInteriorBlockLedger_regularProfile_treeRecursive
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3cRGeneratedInteriorBlockLedger b β p regularWeight variableWeight).regularProfile.profile =
      InteriorBlockStructureProfile.treeRecursive := by
  rfl

theorem sm3cRGeneratedInteriorBlockLedger_variableProfile_treeRecursive
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3cRGeneratedInteriorBlockLedger b β p regularWeight variableWeight).variableProfile.profile =
      InteriorBlockStructureProfile.treeRecursive := by
  rfl

theorem sm3cRGeneratedInteriorBlockLedger_regularNoInverse
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3cRGeneratedInteriorBlockLedger b β p regularWeight variableWeight).regularProfile.noInverseStatus =
      SM3cRNoInverseStatus.noInverseOrEliminationFormulaInSM3cR := by
  rfl

theorem sm3cRGeneratedInteriorBlockLedger_variableNoDtn
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3cRGeneratedInteriorBlockLedger b β p regularWeight variableWeight).variableProfile.noDtnStatus =
      SM3cRNoDtnStatus.noDtnGeneralizedDtnOrMultiSchurInSM3cR := by
  rfl

end Smoke

end CNNA.PillarA.Arithmetic
