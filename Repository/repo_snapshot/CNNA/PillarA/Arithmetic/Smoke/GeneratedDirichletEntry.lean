import CNNA.PillarA.Arithmetic.Smoke.GeneratedBoundaryInteriorPartition
import CNNA.PillarA.Foundation.WeightPolicy

set_option autoImplicit false
open scoped BigOperators

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

namespace Smoke

universe u

inductive SM3bRAdjacencySourceStatus where
  | parentChildLevelAdjacencyFromGeneratedCarrier
  deriving DecidableEq, Repr

inductive SM3bRWeightPolicySourceStatus where
  | weightPolicyCarriedToGeneratedEntries
  deriving DecidableEq, Repr

inductive SM3bRDirichletEntryStatus where
  | entryComputedFromGeneratedAdjacencyAndWeightPolicy
  deriving DecidableEq, Repr

inductive SM3bRNoFreeAdjacencyStatus where
  | noFreeAdjacencyRelation
  deriving DecidableEq, Repr

inductive SM3bRNoFreeWeightStatus where
  | noFreeWeightFunction
  deriving DecidableEq, Repr

inductive SM3bRNoFreeMatrixStatus where
  | matrixExposedOnlyAsEntryFunction
  deriving DecidableEq, Repr

inductive SM3bRNoInteriorBlockStatus where
  | noInteriorBlockProfileInSM3bR
  deriving DecidableEq, Repr

inductive SM3bRNoInverseStatus where
  | noInverseOrInteriorEliminationInSM3bR
  deriving DecidableEq, Repr

inductive SM3bRNoDtnStatus where
  | noDtnGeneralizedDtnOrMultiSchurInSM3bR
  deriving DecidableEq, Repr

inductive SM3bRGeneratedDirichletEntryLedgerStatus where
  | generatedDirichletEntryComputedFromSources
  deriving DecidableEq, Repr

def castGeneratedCell
    {Cell : Nat → Type u} {m n : Nat} (h : m = n) (x : Cell m) : Cell n := by
  cases h
  exact x

def generatedForwardAdjacent
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    (i j : GeneratedApproximantIndex A) : Prop :=
  if h : (GeneratedApproximantIndex.level j).val =
      (GeneratedApproximantIndex.level i).val + 1 then
    GeneratedApproximantIndex.cell i ∈
      SubstrateClass.parents
        (Cell := Cell)
        (castGeneratedCell h (GeneratedApproximantIndex.cell j))
  else
    False

instance generatedForwardAdjacentDecidable
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    (i j : GeneratedApproximantIndex A) :
    Decidable (generatedForwardAdjacent i j) := by
  unfold generatedForwardAdjacent
  infer_instance

def generatedAdjacent
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    (i j : GeneratedApproximantIndex A) : Prop :=
  generatedForwardAdjacent i j ∨ generatedForwardAdjacent j i

instance generatedAdjacentDecidable
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    (i j : GeneratedApproximantIndex A) :
    Decidable (generatedAdjacent i j) := by
  unfold generatedAdjacent
  infer_instance

theorem generatedAdjacent_comm
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    (i j : GeneratedApproximantIndex A) :
    generatedAdjacent i j ↔ generatedAdjacent j i := by
  constructor
  · intro h
    cases h with
    | inl hf => exact Or.inr hf
    | inr hr => exact Or.inl hr
  · intro h
    cases h with
    | inl hf => exact Or.inr hf
    | inr hr => exact Or.inl hr

structure GeneratedAdjacencySource
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf)
    (A : GeneratedApproximantStrong Cell p)
    (P : GeneratedBoundaryInteriorPartition Cell p A) where
  status : SM3bRAdjacencySourceStatus
  approximantRoute : A.route = SM2RApproximantRoute.generatedToCSubstrate
  partitionRoute : P.route = SM3aRPartitionRoute.generatedFromSM2RApproximantCarrier
  boundarySubset : P.boundaryCarrier ⊆ P.approximantCarrier
  interiorSubset : P.interiorCarrier ⊆ P.approximantCarrier
  noFreeAdjacencyStatus : SM3bRNoFreeAdjacencyStatus
  noCutSpecBoundaryPortsStatus : SM3aRNoCutSpecBoundaryPortsStatus
  status_eq_source :
    status =
      SM3bRAdjacencySourceStatus.parentChildLevelAdjacencyFromGeneratedCarrier
  noFreeAdjacencyStatus_eq :
    noFreeAdjacencyStatus = SM3bRNoFreeAdjacencyStatus.noFreeAdjacencyRelation
  noCutSpecBoundaryPortsStatus_eq :
    noCutSpecBoundaryPortsStatus =
      SM3aRNoCutSpecBoundaryPortsStatus.noCutSpecOrBoundaryPortsInPartitionCore

namespace GeneratedAdjacencySource

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {p : ConcretePolicyOf}
variable {A : GeneratedApproximantStrong Cell p}
variable {P : GeneratedBoundaryInteriorPartition Cell p A}

def fromPartition : GeneratedAdjacencySource Cell p A P where
  status := SM3bRAdjacencySourceStatus.parentChildLevelAdjacencyFromGeneratedCarrier
  approximantRoute := A.route_eq_generated
  partitionRoute := P.route_eq_generated
  boundarySubset := P.boundary_subset_approximantCarrier
  interiorSubset := P.interior_subset_approximantCarrier
  noFreeAdjacencyStatus := SM3bRNoFreeAdjacencyStatus.noFreeAdjacencyRelation
  noCutSpecBoundaryPortsStatus := P.noCutSpecBoundaryPortsStatus
  status_eq_source := by
    rfl
  noFreeAdjacencyStatus_eq := by
    rfl
  noCutSpecBoundaryPortsStatus_eq := by
    exact P.noCutSpecBoundaryPortsStatus_eq

def adjacent (_S : GeneratedAdjacencySource Cell p A P)
    (i j : GeneratedApproximantIndex A) : Prop :=
  generatedAdjacent i j

theorem adjacent_eq_generated
    (S : GeneratedAdjacencySource Cell p A P)
    (i j : GeneratedApproximantIndex A) :
    S.adjacent i j = generatedAdjacent i j := by
  rfl

theorem adjacent_comm
    (S : GeneratedAdjacencySource Cell p A P)
    (i j : GeneratedApproximantIndex A) :
    S.adjacent i j ↔ S.adjacent j i := by
  exact generatedAdjacent_comm i j

theorem no_free_adjacency
    (S : GeneratedAdjacencySource Cell p A P) :
    S.noFreeAdjacencyStatus = SM3bRNoFreeAdjacencyStatus.noFreeAdjacencyRelation :=
  S.noFreeAdjacencyStatus_eq

end GeneratedAdjacencySource

structure GeneratedWeightPolicyEntrySource
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf)
    (A : GeneratedApproximantStrong Cell p)
    (P : GeneratedBoundaryInteriorPartition Cell p A)
    (wp : WeightPolicy) where
  policy : WeightPolicy
  policy_eq_input : policy = wp
  status : SM3bRWeightPolicySourceStatus
  sm1WeightHookStatus : SM1RWeightProvenanceStatus
  noFreeWeightStatus : SM3bRNoFreeWeightStatus
  noFreeAdjacencyStatus : SM3bRNoFreeAdjacencyStatus
  partitionRoute : P.route = SM3aRPartitionRoute.generatedFromSM2RApproximantCarrier
  status_eq_source :
    status = SM3bRWeightPolicySourceStatus.weightPolicyCarriedToGeneratedEntries
  sm1WeightHookStatus_eq :
    sm1WeightHookStatus = SM1RWeightProvenanceStatus.weightDeferredToGeneratedEntryLemmas
  noFreeWeightStatus_eq :
    noFreeWeightStatus = SM3bRNoFreeWeightStatus.noFreeWeightFunction
  noFreeAdjacencyStatus_eq :
    noFreeAdjacencyStatus = SM3bRNoFreeAdjacencyStatus.noFreeAdjacencyRelation

namespace GeneratedWeightPolicyEntrySource

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {p : ConcretePolicyOf}
variable {A : GeneratedApproximantStrong Cell p}
variable {P : GeneratedBoundaryInteriorPartition Cell p A}
variable (wp : WeightPolicy)

def fromPartitionAndPolicy : GeneratedWeightPolicyEntrySource Cell p A P wp where
  policy := wp
  policy_eq_input := by
    rfl
  status := SM3bRWeightPolicySourceStatus.weightPolicyCarriedToGeneratedEntries
  sm1WeightHookStatus := SM1RWeightProvenanceStatus.weightDeferredToGeneratedEntryLemmas
  noFreeWeightStatus := SM3bRNoFreeWeightStatus.noFreeWeightFunction
  noFreeAdjacencyStatus := SM3bRNoFreeAdjacencyStatus.noFreeAdjacencyRelation
  partitionRoute := P.route_eq_generated
  status_eq_source := by
    rfl
  sm1WeightHookStatus_eq := by
    rfl
  noFreeWeightStatus_eq := by
    rfl
  noFreeAdjacencyStatus_eq := by
    rfl

theorem no_free_weight
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp) :
    W.noFreeWeightStatus = SM3bRNoFreeWeightStatus.noFreeWeightFunction :=
  W.noFreeWeightStatus_eq

end GeneratedWeightPolicyEntrySource

def generatedEntryWeight
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (i j : GeneratedApproximantIndex A) : ℝ :=
  if generatedAdjacent i j then W.policy.constantWeight i j else 0

theorem generatedEntryWeight_zero_of_not_adjacent
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    {i j : GeneratedApproximantIndex A}
    (h : ¬ generatedAdjacent i j) :
    generatedEntryWeight W i j = 0 := by
  unfold generatedEntryWeight
  simp [h]

theorem generatedEntryWeight_of_adjacent
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    {i j : GeneratedApproximantIndex A}
    (h : generatedAdjacent i j) :
    generatedEntryWeight W i j = W.policy.constantWeight i j := by
  unfold generatedEntryWeight
  simp [h]

def generatedDirichlet_degree
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (i : GeneratedApproximantIndex A) : ℝ :=
  ∑ j : GeneratedApproximantIndex A, generatedEntryWeight W i j

def generatedDirichlet_entry
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (i j : GeneratedApproximantIndex A) : ℝ :=
  if i = j then generatedDirichlet_degree W i else - generatedEntryWeight W i j

def generatedDirichletMatrix
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp) :
    Matrix (GeneratedApproximantIndex A) (GeneratedApproximantIndex A) ℝ :=
  fun i j => generatedDirichlet_entry W i j

theorem generatedDirichletMatrix_entry
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (i j : GeneratedApproximantIndex A) :
    generatedDirichletMatrix W i j = generatedDirichlet_entry W i j := by
  rfl

theorem generatedDirichlet_entry_zero_of_not_adjacent
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    {i j : GeneratedApproximantIndex A}
    (hij : i ≠ j)
    (hadj : ¬ generatedAdjacent i j) :
    generatedDirichlet_entry W i j = 0 := by
  unfold generatedDirichlet_entry generatedEntryWeight
  simp [hij, hadj]

theorem zero_of_not_adjacent
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    {i j : GeneratedApproximantIndex A}
    (hij : i ≠ j)
    (hadj : ¬ generatedAdjacent i j) :
    generatedDirichletMatrix W i j = 0 := by
  exact generatedDirichlet_entry_zero_of_not_adjacent W hij hadj

theorem generatedDirichlet_entry_offdiag_of_adjacent
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    {i j : GeneratedApproximantIndex A}
    (hij : i ≠ j)
    (hadj : generatedAdjacent i j) :
    generatedDirichlet_entry W i j = - W.policy.constantWeight i j := by
  unfold generatedDirichlet_entry generatedEntryWeight
  simp [hij, hadj]

theorem offdiag_of_adjacent
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    {i j : GeneratedApproximantIndex A}
    (hij : i ≠ j)
    (hadj : generatedAdjacent i j) :
    generatedDirichletMatrix W i j = - W.policy.constantWeight i j := by
  exact generatedDirichlet_entry_offdiag_of_adjacent W hij hadj

theorem diag_degree_or_regularized_degree
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (i : GeneratedApproximantIndex A) :
    generatedDirichletMatrix W i i = generatedDirichlet_degree W i := by
  unfold generatedDirichletMatrix generatedDirichlet_entry
  simp

def generatedBoundaryDirichletEntry
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (i : GeneratedBoundaryIndex A)
    (j : GeneratedApproximantIndex A) : ℝ :=
  generatedDirichlet_entry W (GeneratedBoundaryIndex.toApproximantIndex i) j

def generatedInteriorDirichletEntry
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (i : GeneratedInteriorIndex A)
    (j : GeneratedApproximantIndex A) : ℝ :=
  generatedDirichlet_entry W (GeneratedInteriorIndex.toApproximantIndex i) j

theorem boundary_entry_from_generated_source
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (i : GeneratedBoundaryIndex A)
    (j : GeneratedApproximantIndex A) :
    generatedDirichletMatrix W (GeneratedBoundaryIndex.toApproximantIndex i) j =
      generatedBoundaryDirichletEntry W i j := by
  rfl

theorem interior_entry_from_generated_source
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (i : GeneratedInteriorIndex A)
    (j : GeneratedApproximantIndex A) :
    generatedDirichletMatrix W (GeneratedInteriorIndex.toApproximantIndex i) j =
      generatedInteriorDirichletEntry W i j := by
  rfl

structure GeneratedDirichletEntrySource
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf)
    (A : GeneratedApproximantStrong Cell p)
    (P : GeneratedBoundaryInteriorPartition Cell p A)
    (wp : WeightPolicy) where
  adjacencySource : GeneratedAdjacencySource Cell p A P
  weightSource : GeneratedWeightPolicyEntrySource Cell p A P wp
  entryStatus : SM3bRDirichletEntryStatus
  noFreeMatrixStatus : SM3bRNoFreeMatrixStatus
  noInteriorBlockStatus : SM3bRNoInteriorBlockStatus
  noInverseStatus : SM3bRNoInverseStatus
  noDtnStatus : SM3bRNoDtnStatus
  matrix_eq_entry :
    generatedDirichletMatrix weightSource =
      fun i j => generatedDirichlet_entry weightSource i j
  entryStatus_eq :
    entryStatus =
      SM3bRDirichletEntryStatus.entryComputedFromGeneratedAdjacencyAndWeightPolicy
  noFreeMatrixStatus_eq :
    noFreeMatrixStatus = SM3bRNoFreeMatrixStatus.matrixExposedOnlyAsEntryFunction
  noInteriorBlockStatus_eq :
    noInteriorBlockStatus = SM3bRNoInteriorBlockStatus.noInteriorBlockProfileInSM3bR
  noInverseStatus_eq :
    noInverseStatus = SM3bRNoInverseStatus.noInverseOrInteriorEliminationInSM3bR
  noDtnStatus_eq :
    noDtnStatus = SM3bRNoDtnStatus.noDtnGeneralizedDtnOrMultiSchurInSM3bR

namespace GeneratedDirichletEntrySource

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {p : ConcretePolicyOf}
variable {A : GeneratedApproximantStrong Cell p}
variable {P : GeneratedBoundaryInteriorPartition Cell p A}
variable (wp : WeightPolicy)

def fromPartitionAndPolicy : GeneratedDirichletEntrySource Cell p A P wp where
  adjacencySource := GeneratedAdjacencySource.fromPartition
  weightSource := GeneratedWeightPolicyEntrySource.fromPartitionAndPolicy wp
  entryStatus :=
    SM3bRDirichletEntryStatus.entryComputedFromGeneratedAdjacencyAndWeightPolicy
  noFreeMatrixStatus := SM3bRNoFreeMatrixStatus.matrixExposedOnlyAsEntryFunction
  noInteriorBlockStatus := SM3bRNoInteriorBlockStatus.noInteriorBlockProfileInSM3bR
  noInverseStatus := SM3bRNoInverseStatus.noInverseOrInteriorEliminationInSM3bR
  noDtnStatus := SM3bRNoDtnStatus.noDtnGeneralizedDtnOrMultiSchurInSM3bR
  matrix_eq_entry := by
    rfl
  entryStatus_eq := by
    rfl
  noFreeMatrixStatus_eq := by
    rfl
  noInteriorBlockStatus_eq := by
    rfl
  noInverseStatus_eq := by
    rfl
  noDtnStatus_eq := by
    rfl

theorem no_free_matrix
    {wp : WeightPolicy}
    (D : GeneratedDirichletEntrySource Cell p A P wp) :
    D.noFreeMatrixStatus = SM3bRNoFreeMatrixStatus.matrixExposedOnlyAsEntryFunction :=
  D.noFreeMatrixStatus_eq

theorem no_inverse
    {wp : WeightPolicy}
    (D : GeneratedDirichletEntrySource Cell p A P wp) :
    D.noInverseStatus = SM3bRNoInverseStatus.noInverseOrInteriorEliminationInSM3bR :=
  D.noInverseStatus_eq

theorem no_dtn
    {wp : WeightPolicy}
    (D : GeneratedDirichletEntrySource Cell p A P wp) :
    D.noDtnStatus = SM3bRNoDtnStatus.noDtnGeneralizedDtnOrMultiSchurInSM3bR :=
  D.noDtnStatus_eq

end GeneratedDirichletEntrySource

def regularGeneratedAdjacencySource
    (b : Nat) (p : ConcretePolicyOf) :
    GeneratedAdjacencySource
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) :=
  GeneratedAdjacencySource.fromPartition

def variableGeneratedAdjacencySource
    (β : Nat → Nat) (p : ConcretePolicyOf) :
    GeneratedAdjacencySource
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) :=
  GeneratedAdjacencySource.fromPartition

def regularGeneratedWeightPolicyEntrySource
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedWeightPolicyEntrySource
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) wp :=
  GeneratedWeightPolicyEntrySource.fromPartitionAndPolicy wp

def variableGeneratedWeightPolicyEntrySource
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedWeightPolicyEntrySource
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) wp :=
  GeneratedWeightPolicyEntrySource.fromPartitionAndPolicy wp

def regularGeneratedDirichletEntrySource
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedDirichletEntrySource
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) wp :=
  GeneratedDirichletEntrySource.fromPartitionAndPolicy wp

def variableGeneratedDirichletEntrySource
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedDirichletEntrySource
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) wp :=
  GeneratedDirichletEntrySource.fromPartitionAndPolicy wp

structure SM3bRGeneratedDirichletEntryLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  status : SM3bRGeneratedDirichletEntryLedgerStatus
  sm3aLedger : SM3aRGeneratedPartitionLedger b β p
  regularAdjacencySource :
    GeneratedAdjacencySource
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p)
  variableAdjacencySource :
    GeneratedAdjacencySource
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p)
  regularWeightSource :
    GeneratedWeightPolicyEntrySource
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
  variableWeightSource :
    GeneratedWeightPolicyEntrySource
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
  regularEntrySource :
    GeneratedDirichletEntrySource
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
  variableEntrySource :
    GeneratedDirichletEntrySource
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
  sm3aLedger_eq_main : sm3aLedger = sm3aRGeneratedPartitionLedger b β p
  regularAdjacency_eq_main :
    regularAdjacencySource = regularGeneratedAdjacencySource b p
  variableAdjacency_eq_main :
    variableAdjacencySource = variableGeneratedAdjacencySource β p
  regularWeight_eq_main :
    regularWeightSource = regularGeneratedWeightPolicyEntrySource b p regularWeight
  variableWeight_eq_main :
    variableWeightSource = variableGeneratedWeightPolicyEntrySource β p variableWeight
  regularEntry_eq_main :
    regularEntrySource = regularGeneratedDirichletEntrySource b p regularWeight
  variableEntry_eq_main :
    variableEntrySource = variableGeneratedDirichletEntrySource β p variableWeight
  regularMatrix_eq_entry :
    generatedDirichletMatrix regularWeightSource =
      fun i j => generatedDirichlet_entry regularWeightSource i j
  variableMatrix_eq_entry :
    generatedDirichletMatrix variableWeightSource =
      fun i j => generatedDirichlet_entry variableWeightSource i j
  regularNoFreeAdjacency :
    regularAdjacencySource.noFreeAdjacencyStatus =
      SM3bRNoFreeAdjacencyStatus.noFreeAdjacencyRelation
  variableNoFreeAdjacency :
    variableAdjacencySource.noFreeAdjacencyStatus =
      SM3bRNoFreeAdjacencyStatus.noFreeAdjacencyRelation
  regularNoFreeWeight :
    regularWeightSource.noFreeWeightStatus = SM3bRNoFreeWeightStatus.noFreeWeightFunction
  variableNoFreeWeight :
    variableWeightSource.noFreeWeightStatus = SM3bRNoFreeWeightStatus.noFreeWeightFunction
  regularNoFreeMatrix :
    regularEntrySource.noFreeMatrixStatus =
      SM3bRNoFreeMatrixStatus.matrixExposedOnlyAsEntryFunction
  variableNoFreeMatrix :
    variableEntrySource.noFreeMatrixStatus =
      SM3bRNoFreeMatrixStatus.matrixExposedOnlyAsEntryFunction
  regularNoInteriorBlock :
    regularEntrySource.noInteriorBlockStatus =
      SM3bRNoInteriorBlockStatus.noInteriorBlockProfileInSM3bR
  variableNoInteriorBlock :
    variableEntrySource.noInteriorBlockStatus =
      SM3bRNoInteriorBlockStatus.noInteriorBlockProfileInSM3bR
  regularNoInverse :
    regularEntrySource.noInverseStatus =
      SM3bRNoInverseStatus.noInverseOrInteriorEliminationInSM3bR
  variableNoInverse :
    variableEntrySource.noInverseStatus =
      SM3bRNoInverseStatus.noInverseOrInteriorEliminationInSM3bR
  regularNoDtn :
    regularEntrySource.noDtnStatus =
      SM3bRNoDtnStatus.noDtnGeneralizedDtnOrMultiSchurInSM3bR
  variableNoDtn :
    variableEntrySource.noDtnStatus =
      SM3bRNoDtnStatus.noDtnGeneralizedDtnOrMultiSchurInSM3bR
  status_eq_closed :
    status =
      SM3bRGeneratedDirichletEntryLedgerStatus.generatedDirichletEntryComputedFromSources

def sm3bRGeneratedDirichletEntryLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    SM3bRGeneratedDirichletEntryLedger b β p regularWeight variableWeight where
  status :=
    SM3bRGeneratedDirichletEntryLedgerStatus.generatedDirichletEntryComputedFromSources
  sm3aLedger := sm3aRGeneratedPartitionLedger b β p
  regularAdjacencySource := regularGeneratedAdjacencySource b p
  variableAdjacencySource := variableGeneratedAdjacencySource β p
  regularWeightSource := regularGeneratedWeightPolicyEntrySource b p regularWeight
  variableWeightSource := variableGeneratedWeightPolicyEntrySource β p variableWeight
  regularEntrySource := regularGeneratedDirichletEntrySource b p regularWeight
  variableEntrySource := variableGeneratedDirichletEntrySource β p variableWeight
  sm3aLedger_eq_main := by
    rfl
  regularAdjacency_eq_main := by
    rfl
  variableAdjacency_eq_main := by
    rfl
  regularWeight_eq_main := by
    rfl
  variableWeight_eq_main := by
    rfl
  regularEntry_eq_main := by
    rfl
  variableEntry_eq_main := by
    rfl
  regularMatrix_eq_entry := by
    rfl
  variableMatrix_eq_entry := by
    rfl
  regularNoFreeAdjacency := by
    rfl
  variableNoFreeAdjacency := by
    rfl
  regularNoFreeWeight := by
    rfl
  variableNoFreeWeight := by
    rfl
  regularNoFreeMatrix := by
    rfl
  variableNoFreeMatrix := by
    rfl
  regularNoInteriorBlock := by
    rfl
  variableNoInteriorBlock := by
    rfl
  regularNoInverse := by
    rfl
  variableNoInverse := by
    rfl
  regularNoDtn := by
    rfl
  variableNoDtn := by
    rfl
  status_eq_closed := by
    rfl

theorem sm3bRGeneratedDirichletEntryLedger_status
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3bRGeneratedDirichletEntryLedger b β p regularWeight variableWeight).status =
      SM3bRGeneratedDirichletEntryLedgerStatus.generatedDirichletEntryComputedFromSources := by
  rfl

theorem sm3bRGeneratedDirichletEntryLedger_regularNoFreeMatrix
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3bRGeneratedDirichletEntryLedger b β p regularWeight variableWeight).regularEntrySource.noFreeMatrixStatus =
      SM3bRNoFreeMatrixStatus.matrixExposedOnlyAsEntryFunction := by
  rfl

theorem sm3bRGeneratedDirichletEntryLedger_variableNoFreeMatrix
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3bRGeneratedDirichletEntryLedger b β p regularWeight variableWeight).variableEntrySource.noFreeMatrixStatus =
      SM3bRNoFreeMatrixStatus.matrixExposedOnlyAsEntryFunction := by
  rfl

theorem sm3bRGeneratedDirichletEntryLedger_regularNoInverse
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3bRGeneratedDirichletEntryLedger b β p regularWeight variableWeight).regularEntrySource.noInverseStatus =
      SM3bRNoInverseStatus.noInverseOrInteriorEliminationInSM3bR := by
  rfl

theorem sm3bRGeneratedDirichletEntryLedger_variableNoInverse
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3bRGeneratedDirichletEntryLedger b β p regularWeight variableWeight).variableEntrySource.noInverseStatus =
      SM3bRNoInverseStatus.noInverseOrInteriorEliminationInSM3bR := by
  rfl

theorem sm3bRGeneratedDirichletEntryLedger_regularNoDtn
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3bRGeneratedDirichletEntryLedger b β p regularWeight variableWeight).regularEntrySource.noDtnStatus =
      SM3bRNoDtnStatus.noDtnGeneralizedDtnOrMultiSchurInSM3bR := by
  rfl

theorem sm3bRGeneratedDirichletEntryLedger_variableNoDtn
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3bRGeneratedDirichletEntryLedger b β p regularWeight variableWeight).variableEntrySource.noDtnStatus =
      SM3bRNoDtnStatus.noDtnGeneralizedDtnOrMultiSchurInSM3bR := by
  rfl

end Smoke

end CNNA.PillarA.Arithmetic
