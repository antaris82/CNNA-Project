import CNNA.PillarA.Arithmetic.Smoke.GeneratedApproximantCore

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

namespace Smoke

universe u

inductive SM3aRPartitionRoute where
  | generatedFromSM2RApproximantCarrier
  deriving DecidableEq, Repr

inductive SM3aRIndexOriginStatus where
  | subcarrierMembershipFromSM2RApproximant
  deriving DecidableEq, Repr

inductive SM3aRFinitePartitionAPIStatus where
  | finiteDecidableAPIForwardedFromSM2RCarrier
  deriving DecidableEq, Repr

inductive SM3aRPartitionStatus where
  | boundaryInteriorPartitionClosed
  deriving DecidableEq, Repr

inductive SM3aRNoFreeIndexStatus where
  | noFreeFinReplacementIndex
  deriving DecidableEq, Repr

inductive SM3aRNoCutSpecBoundaryPortsStatus where
  | noCutSpecOrBoundaryPortsInPartitionCore
  deriving DecidableEq, Repr

inductive SM3aRNoMatrixDataStatus where
  | noMatrixDirichletDtnInverseOrTargetData
  deriving DecidableEq, Repr

inductive SM3aRGeneratedPartitionLedgerStatus where
  | generatedBoundaryInteriorPartitionClosed
  deriving DecidableEq, Repr

abbrev GeneratedApproximantIndex
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    (A : GeneratedApproximantStrong Cell p) :=
  Σ L : Fin (p.L_max + 1),
    {x : Cell L.val // x ∈ A.approximant.carrier L.val}

namespace GeneratedApproximantIndex

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {p : ConcretePolicyOf}
variable {A : GeneratedApproximantStrong Cell p}


def level (i : GeneratedApproximantIndex A) : Fin (p.L_max + 1) :=
  i.1

def cell (i : GeneratedApproximantIndex A) : Cell (level i).val :=
  i.2.1

theorem cell_mem_approximant (i : GeneratedApproximantIndex A) :
    cell i ∈ A.approximant.carrier (level i).val :=
  i.2.2

theorem level_le_cutoff (i : GeneratedApproximantIndex A) :
    (level i).val ≤ p.L_max :=
  Nat.le_of_lt_succ (level i).isLt

end GeneratedApproximantIndex

def GeneratedBoundaryPredicate
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    (i : GeneratedApproximantIndex A) : Prop :=
  (GeneratedApproximantIndex.level i).val = p.L_max

def GeneratedInteriorPredicate
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    (i : GeneratedApproximantIndex A) : Prop :=
  (GeneratedApproximantIndex.level i).val < p.L_max

instance generatedBoundaryPredicateDecidable
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    (i : GeneratedApproximantIndex A) :
    Decidable (GeneratedBoundaryPredicate i) := by
  unfold GeneratedBoundaryPredicate
  infer_instance

instance generatedInteriorPredicateDecidable
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    (i : GeneratedApproximantIndex A) :
    Decidable (GeneratedInteriorPredicate i) := by
  unfold GeneratedInteriorPredicate
  infer_instance

abbrev GeneratedBoundaryIndex
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    (A : GeneratedApproximantStrong Cell p) :=
  {i : GeneratedApproximantIndex A // GeneratedBoundaryPredicate i}

abbrev GeneratedInteriorIndex
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    (A : GeneratedApproximantStrong Cell p) :=
  {i : GeneratedApproximantIndex A // GeneratedInteriorPredicate i}

namespace GeneratedBoundaryIndex

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {p : ConcretePolicyOf}
variable {A : GeneratedApproximantStrong Cell p}


def toApproximantIndex (i : GeneratedBoundaryIndex A) :
    GeneratedApproximantIndex A :=
  i.1

def level (i : GeneratedBoundaryIndex A) : Fin (p.L_max + 1) :=
  GeneratedApproximantIndex.level (toApproximantIndex i)

def cell (i : GeneratedBoundaryIndex A) : Cell (level i).val :=
  GeneratedApproximantIndex.cell (toApproximantIndex i)

theorem level_eq_cutoff (i : GeneratedBoundaryIndex A) :
    (level i).val = p.L_max :=
  i.2

theorem cell_mem_approximant (i : GeneratedBoundaryIndex A) :
    cell i ∈ A.approximant.carrier (level i).val :=
  GeneratedApproximantIndex.cell_mem_approximant (toApproximantIndex i)

end GeneratedBoundaryIndex

namespace GeneratedInteriorIndex

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {p : ConcretePolicyOf}
variable {A : GeneratedApproximantStrong Cell p}


def toApproximantIndex (i : GeneratedInteriorIndex A) :
    GeneratedApproximantIndex A :=
  i.1

def level (i : GeneratedInteriorIndex A) : Fin (p.L_max + 1) :=
  GeneratedApproximantIndex.level (toApproximantIndex i)

def cell (i : GeneratedInteriorIndex A) : Cell (level i).val :=
  GeneratedApproximantIndex.cell (toApproximantIndex i)

theorem level_lt_cutoff (i : GeneratedInteriorIndex A) :
    (level i).val < p.L_max :=
  i.2

theorem cell_mem_approximant (i : GeneratedInteriorIndex A) :
    cell i ∈ A.approximant.carrier (level i).val :=
  GeneratedApproximantIndex.cell_mem_approximant (toApproximantIndex i)

end GeneratedInteriorIndex

def GeneratedApproximantCarrier
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    (A : GeneratedApproximantStrong Cell p) :
    Finset (GeneratedApproximantIndex A) :=
  Finset.univ

def GeneratedBoundaryCarrier
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    (A : GeneratedApproximantStrong Cell p) :
    Finset (GeneratedApproximantIndex A) :=
  (GeneratedApproximantCarrier A).filter (fun i => GeneratedBoundaryPredicate i)

def GeneratedInteriorCarrier
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    (A : GeneratedApproximantStrong Cell p) :
    Finset (GeneratedApproximantIndex A) :=
  (GeneratedApproximantCarrier A).filter (fun i => GeneratedInteriorPredicate i)

theorem boundary_subset_approximantCarrier
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    (A : GeneratedApproximantStrong Cell p) :
    GeneratedBoundaryCarrier A ⊆ GeneratedApproximantCarrier A := by
  intro i hi
  exact (Finset.mem_filter.mp hi).1

theorem interior_subset_approximantCarrier
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    (A : GeneratedApproximantStrong Cell p) :
    GeneratedInteriorCarrier A ⊆ GeneratedApproximantCarrier A := by
  intro i hi
  exact (Finset.mem_filter.mp hi).1

theorem boundary_in_approximant
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    (i : GeneratedBoundaryIndex A) :
    GeneratedBoundaryIndex.toApproximantIndex i ∈ GeneratedApproximantCarrier A := by
  exact Finset.mem_univ _

theorem interior_in_approximant
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    (i : GeneratedInteriorIndex A) :
    GeneratedInteriorIndex.toApproximantIndex i ∈ GeneratedApproximantCarrier A := by
  exact Finset.mem_univ _

theorem boundary_mem_boundaryCarrier
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    (i : GeneratedBoundaryIndex A) :
    GeneratedBoundaryIndex.toApproximantIndex i ∈ GeneratedBoundaryCarrier A := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.2⟩

theorem interior_mem_interiorCarrier
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    (i : GeneratedInteriorIndex A) :
    GeneratedInteriorIndex.toApproximantIndex i ∈ GeneratedInteriorCarrier A := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.2⟩

theorem generatedBoundary_or_interior
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    (i : GeneratedApproximantIndex A) :
    GeneratedBoundaryPredicate i ∨ GeneratedInteriorPredicate i := by
  have hle : (GeneratedApproximantIndex.level i).val ≤ p.L_max :=
    GeneratedApproximantIndex.level_le_cutoff i
  by_cases hb : (GeneratedApproximantIndex.level i).val = p.L_max
  · exact Or.inl hb
  · have hlt : (GeneratedApproximantIndex.level i).val < p.L_max :=
      lt_of_le_of_ne hle hb
    exact Or.inr hlt

theorem generatedBoundaryInterior_predicate_disjoint
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    (i : GeneratedApproximantIndex A)
    (hb : GeneratedBoundaryPredicate i)
    (hi : GeneratedInteriorPredicate i) :
    False := by
  have hlt : p.L_max < p.L_max := by
    calc
      p.L_max = (GeneratedApproximantIndex.level i).val := Eq.symm hb
      _ < p.L_max := hi
  exact (Nat.lt_irrefl p.L_max) hlt

theorem boundaryInterior_disjoint
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    (A : GeneratedApproximantStrong Cell p)
    (i : GeneratedApproximantIndex A) :
    ¬ (i ∈ GeneratedBoundaryCarrier A ∧ i ∈ GeneratedInteriorCarrier A) := by
  intro h
  have hb : GeneratedBoundaryPredicate i := (Finset.mem_filter.mp h.1).2
  have hi : GeneratedInteriorPredicate i := (Finset.mem_filter.mp h.2).2
  exact generatedBoundaryInterior_predicate_disjoint i hb hi

theorem boundaryInterior_complete
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    (A : GeneratedApproximantStrong Cell p)
    (i : GeneratedApproximantIndex A)
    (hi : i ∈ GeneratedApproximantCarrier A) :
    i ∈ GeneratedBoundaryCarrier A ∨ i ∈ GeneratedInteriorCarrier A := by
  cases generatedBoundary_or_interior i with
  | inl hb =>
      exact Or.inl (Finset.mem_filter.mpr ⟨hi, hb⟩)
  | inr hint =>
      exact Or.inr (Finset.mem_filter.mpr ⟨hi, hint⟩)

structure GeneratedPartitionFiniteAPI
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    (A : GeneratedApproximantStrong Cell p) where
  approximantIndexDecidableEq : DecidableEq (GeneratedApproximantIndex A)
  approximantIndexFintype : Fintype (GeneratedApproximantIndex A)
  boundaryIndexDecidableEq : DecidableEq (GeneratedBoundaryIndex A)
  boundaryIndexFintype : Fintype (GeneratedBoundaryIndex A)
  interiorIndexDecidableEq : DecidableEq (GeneratedInteriorIndex A)
  interiorIndexFintype : Fintype (GeneratedInteriorIndex A)
  boundaryPredicateDecidable : ∀ i : GeneratedApproximantIndex A,
    Decidable (GeneratedBoundaryPredicate i)
  interiorPredicateDecidable : ∀ i : GeneratedApproximantIndex A,
    Decidable (GeneratedInteriorPredicate i)
  sm2FiniteCarrierAPIStatus : SM2RFiniteCarrierAPIStatus
  sm2FiniteCarrierAPIStatus_eq_forwarded :
    sm2FiniteCarrierAPIStatus =
      SM2RFiniteCarrierAPIStatus.substrateFintypeAndDecidableEqForwarded
  status : SM3aRFinitePartitionAPIStatus
  status_eq_forwarded :
    status =
      SM3aRFinitePartitionAPIStatus.finiteDecidableAPIForwardedFromSM2RCarrier

namespace GeneratedPartitionFiniteAPI

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {p : ConcretePolicyOf}
variable (A : GeneratedApproximantStrong Cell p)

def fromSM2R : GeneratedPartitionFiniteAPI A where
  approximantIndexDecidableEq := inferInstance
  approximantIndexFintype := inferInstance
  boundaryIndexDecidableEq := inferInstance
  boundaryIndexFintype := inferInstance
  interiorIndexDecidableEq := inferInstance
  interiorIndexFintype := inferInstance
  boundaryPredicateDecidable := by
    intro i
    infer_instance
  interiorPredicateDecidable := by
    intro i
    infer_instance
  sm2FiniteCarrierAPIStatus := A.finiteCarrierAPI.status
  sm2FiniteCarrierAPIStatus_eq_forwarded := by
    exact A.finiteCarrierAPI.status_eq_forwarded
  status :=
    SM3aRFinitePartitionAPIStatus.finiteDecidableAPIForwardedFromSM2RCarrier
  status_eq_forwarded := by
    rfl

theorem status_forwarded (F : GeneratedPartitionFiniteAPI A) :
    F.status =
      SM3aRFinitePartitionAPIStatus.finiteDecidableAPIForwardedFromSM2RCarrier :=
  F.status_eq_forwarded

end GeneratedPartitionFiniteAPI

structure GeneratedBoundaryInteriorPartition
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf)
    (A : GeneratedApproximantStrong Cell p) where
  approximantCarrier : Finset (GeneratedApproximantIndex A)
  boundaryCarrier : Finset (GeneratedApproximantIndex A)
  interiorCarrier : Finset (GeneratedApproximantIndex A)
  approximantCarrier_eq : approximantCarrier = GeneratedApproximantCarrier A
  boundaryCarrier_eq : boundaryCarrier = GeneratedBoundaryCarrier A
  interiorCarrier_eq : interiorCarrier = GeneratedInteriorCarrier A
  finiteAPI : GeneratedPartitionFiniteAPI A
  route : SM3aRPartitionRoute
  indexOriginStatus : SM3aRIndexOriginStatus
  partitionStatus : SM3aRPartitionStatus
  noFreeIndexStatus : SM3aRNoFreeIndexStatus
  noCutSpecBoundaryPortsStatus : SM3aRNoCutSpecBoundaryPortsStatus
  noMatrixDataStatus : SM3aRNoMatrixDataStatus
  boundary_subset_approximantCarrier : boundaryCarrier ⊆ approximantCarrier
  interior_subset_approximantCarrier : interiorCarrier ⊆ approximantCarrier
  boundaryInterior_disjoint :
    ∀ i : GeneratedApproximantIndex A,
      ¬ (i ∈ boundaryCarrier ∧ i ∈ interiorCarrier)
  boundaryInterior_complete :
    ∀ i : GeneratedApproximantIndex A,
      i ∈ approximantCarrier → i ∈ boundaryCarrier ∨ i ∈ interiorCarrier
  route_eq_generated :
    route = SM3aRPartitionRoute.generatedFromSM2RApproximantCarrier
  indexOriginStatus_eq :
    indexOriginStatus =
      SM3aRIndexOriginStatus.subcarrierMembershipFromSM2RApproximant
  partitionStatus_eq :
    partitionStatus = SM3aRPartitionStatus.boundaryInteriorPartitionClosed
  noFreeIndexStatus_eq :
    noFreeIndexStatus = SM3aRNoFreeIndexStatus.noFreeFinReplacementIndex
  noCutSpecBoundaryPortsStatus_eq :
    noCutSpecBoundaryPortsStatus =
      SM3aRNoCutSpecBoundaryPortsStatus.noCutSpecOrBoundaryPortsInPartitionCore
  noMatrixDataStatus_eq :
    noMatrixDataStatus =
      SM3aRNoMatrixDataStatus.noMatrixDirichletDtnInverseOrTargetData

namespace GeneratedBoundaryInteriorPartition

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {p : ConcretePolicyOf}
variable (A : GeneratedApproximantStrong Cell p)

def fromApproximant : GeneratedBoundaryInteriorPartition Cell p A where
  approximantCarrier := GeneratedApproximantCarrier A
  boundaryCarrier := GeneratedBoundaryCarrier A
  interiorCarrier := GeneratedInteriorCarrier A
  approximantCarrier_eq := by
    rfl
  boundaryCarrier_eq := by
    rfl
  interiorCarrier_eq := by
    rfl
  finiteAPI := GeneratedPartitionFiniteAPI.fromSM2R A
  route := SM3aRPartitionRoute.generatedFromSM2RApproximantCarrier
  indexOriginStatus :=
    SM3aRIndexOriginStatus.subcarrierMembershipFromSM2RApproximant
  partitionStatus := SM3aRPartitionStatus.boundaryInteriorPartitionClosed
  noFreeIndexStatus := SM3aRNoFreeIndexStatus.noFreeFinReplacementIndex
  noCutSpecBoundaryPortsStatus :=
    SM3aRNoCutSpecBoundaryPortsStatus.noCutSpecOrBoundaryPortsInPartitionCore
  noMatrixDataStatus :=
    SM3aRNoMatrixDataStatus.noMatrixDirichletDtnInverseOrTargetData
  boundary_subset_approximantCarrier := by
    exact _root_.CNNA.PillarA.Arithmetic.Smoke.boundary_subset_approximantCarrier A
  interior_subset_approximantCarrier := by
    exact _root_.CNNA.PillarA.Arithmetic.Smoke.interior_subset_approximantCarrier A
  boundaryInterior_disjoint := by
    intro i
    exact _root_.CNNA.PillarA.Arithmetic.Smoke.boundaryInterior_disjoint A i
  boundaryInterior_complete := by
    intro i hi
    exact _root_.CNNA.PillarA.Arithmetic.Smoke.boundaryInterior_complete A i hi
  route_eq_generated := by
    rfl
  indexOriginStatus_eq := by
    rfl
  partitionStatus_eq := by
    rfl
  noFreeIndexStatus_eq := by
    rfl
  noCutSpecBoundaryPortsStatus_eq := by
    rfl
  noMatrixDataStatus_eq := by
    rfl

theorem route_generated
    (P : GeneratedBoundaryInteriorPartition Cell p A) :
    P.route = SM3aRPartitionRoute.generatedFromSM2RApproximantCarrier :=
  P.route_eq_generated

theorem no_free_index
    (P : GeneratedBoundaryInteriorPartition Cell p A) :
    P.noFreeIndexStatus = SM3aRNoFreeIndexStatus.noFreeFinReplacementIndex :=
  P.noFreeIndexStatus_eq

theorem no_cutSpec_boundaryPorts
    (P : GeneratedBoundaryInteriorPartition Cell p A) :
    P.noCutSpecBoundaryPortsStatus =
      SM3aRNoCutSpecBoundaryPortsStatus.noCutSpecOrBoundaryPortsInPartitionCore :=
  P.noCutSpecBoundaryPortsStatus_eq

theorem no_matrix_data
    (P : GeneratedBoundaryInteriorPartition Cell p A) :
    P.noMatrixDataStatus =
      SM3aRNoMatrixDataStatus.noMatrixDirichletDtnInverseOrTargetData :=
  P.noMatrixDataStatus_eq

end GeneratedBoundaryInteriorPartition

def generatedBoundaryInteriorPartition
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf)
    (A : GeneratedApproximantStrong Cell p) :
    GeneratedBoundaryInteriorPartition Cell p A :=
  GeneratedBoundaryInteriorPartition.fromApproximant A

abbrev RegularGeneratedBoundaryInteriorPartition
    (b : Nat) (p : ConcretePolicyOf) :=
  GeneratedBoundaryInteriorPartition
    (ConcreteSubstrate.RegularCell b) p
    (regularGeneratedApproximantStrong b p)

abbrev VariableGeneratedBoundaryInteriorPartition
    (β : Nat → Nat) (p : ConcretePolicyOf) :=
  GeneratedBoundaryInteriorPartition
    (LevelVariableSubstrate.LevelVariableCell β) p
    (variableGeneratedApproximantStrong β p)

def regularGeneratedBoundaryInteriorPartition
    (b : Nat) (p : ConcretePolicyOf) :
    RegularGeneratedBoundaryInteriorPartition b p :=
  GeneratedBoundaryInteriorPartition.fromApproximant
    (regularGeneratedApproximantStrong b p)

def variableGeneratedBoundaryInteriorPartition
    (β : Nat → Nat) (p : ConcretePolicyOf) :
    VariableGeneratedBoundaryInteriorPartition β p :=
  GeneratedBoundaryInteriorPartition.fromApproximant
    (variableGeneratedApproximantStrong β p)

theorem regularGeneratedBoundaryInteriorPartition_route
    (b : Nat) (p : ConcretePolicyOf) :
    (regularGeneratedBoundaryInteriorPartition b p).route =
      SM3aRPartitionRoute.generatedFromSM2RApproximantCarrier := by
  rfl

theorem variableGeneratedBoundaryInteriorPartition_route
    (β : Nat → Nat) (p : ConcretePolicyOf) :
    (variableGeneratedBoundaryInteriorPartition β p).route =
      SM3aRPartitionRoute.generatedFromSM2RApproximantCarrier := by
  rfl

theorem regularGeneratedBoundaryInteriorPartition_noFreeIndex
    (b : Nat) (p : ConcretePolicyOf) :
    (regularGeneratedBoundaryInteriorPartition b p).noFreeIndexStatus =
      SM3aRNoFreeIndexStatus.noFreeFinReplacementIndex := by
  rfl

theorem variableGeneratedBoundaryInteriorPartition_noFreeIndex
    (β : Nat → Nat) (p : ConcretePolicyOf) :
    (variableGeneratedBoundaryInteriorPartition β p).noFreeIndexStatus =
      SM3aRNoFreeIndexStatus.noFreeFinReplacementIndex := by
  rfl

theorem regularGeneratedBoundaryInteriorPartition_noMatrixData
    (b : Nat) (p : ConcretePolicyOf) :
    (regularGeneratedBoundaryInteriorPartition b p).noMatrixDataStatus =
      SM3aRNoMatrixDataStatus.noMatrixDirichletDtnInverseOrTargetData := by
  rfl

theorem variableGeneratedBoundaryInteriorPartition_noMatrixData
    (β : Nat → Nat) (p : ConcretePolicyOf) :
    (variableGeneratedBoundaryInteriorPartition β p).noMatrixDataStatus =
      SM3aRNoMatrixDataStatus.noMatrixDirichletDtnInverseOrTargetData := by
  rfl

structure SM3aRGeneratedPartitionLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf) where
  status : SM3aRGeneratedPartitionLedgerStatus
  sm2rLedger : SM2RGeneratedApproximantLedger b β p
  regular : RegularGeneratedBoundaryInteriorPartition b p
  variablePath : VariableGeneratedBoundaryInteriorPartition β p
  sm2rLedger_eq_main : sm2rLedger = sm2RGeneratedApproximantLedger b β p
  regular_eq_main : regular = regularGeneratedBoundaryInteriorPartition b p
  variable_eq_main : variablePath = variableGeneratedBoundaryInteriorPartition β p
  sm2rRegular_eq_main :
    sm2rLedger.regular = regularGeneratedApproximantStrong b p
  sm2rVariable_eq_main :
    sm2rLedger.variablePath = variableGeneratedApproximantStrong β p
  regularBoundarySubset : regular.boundaryCarrier ⊆ regular.approximantCarrier
  regularInteriorSubset : regular.interiorCarrier ⊆ regular.approximantCarrier
  variableBoundarySubset : variablePath.boundaryCarrier ⊆ variablePath.approximantCarrier
  variableInteriorSubset : variablePath.interiorCarrier ⊆ variablePath.approximantCarrier
  regularDisjoint :
    ∀ i : GeneratedApproximantIndex (regularGeneratedApproximantStrong b p),
      ¬ (i ∈ regular.boundaryCarrier ∧ i ∈ regular.interiorCarrier)
  variableDisjoint :
    ∀ i : GeneratedApproximantIndex (variableGeneratedApproximantStrong β p),
      ¬ (i ∈ variablePath.boundaryCarrier ∧ i ∈ variablePath.interiorCarrier)
  regularComplete :
    ∀ i : GeneratedApproximantIndex (regularGeneratedApproximantStrong b p),
      i ∈ regular.approximantCarrier →
        i ∈ regular.boundaryCarrier ∨ i ∈ regular.interiorCarrier
  variableComplete :
    ∀ i : GeneratedApproximantIndex (variableGeneratedApproximantStrong β p),
      i ∈ variablePath.approximantCarrier →
        i ∈ variablePath.boundaryCarrier ∨ i ∈ variablePath.interiorCarrier
  regularNoFreeIndex :
    regular.noFreeIndexStatus = SM3aRNoFreeIndexStatus.noFreeFinReplacementIndex
  variableNoFreeIndex :
    variablePath.noFreeIndexStatus = SM3aRNoFreeIndexStatus.noFreeFinReplacementIndex
  regularNoCutSpecBoundaryPorts :
    regular.noCutSpecBoundaryPortsStatus =
      SM3aRNoCutSpecBoundaryPortsStatus.noCutSpecOrBoundaryPortsInPartitionCore
  variableNoCutSpecBoundaryPorts :
    variablePath.noCutSpecBoundaryPortsStatus =
      SM3aRNoCutSpecBoundaryPortsStatus.noCutSpecOrBoundaryPortsInPartitionCore
  regularNoMatrixData :
    regular.noMatrixDataStatus =
      SM3aRNoMatrixDataStatus.noMatrixDirichletDtnInverseOrTargetData
  variableNoMatrixData :
    variablePath.noMatrixDataStatus =
      SM3aRNoMatrixDataStatus.noMatrixDirichletDtnInverseOrTargetData
  sm2rRegularNoMatrixData :
    sm2rLedger.regular.matrixDataStatus = SM2RMatrixDataStatus.noMatrixDataYet
  sm2rVariableNoMatrixData :
    sm2rLedger.variablePath.matrixDataStatus = SM2RMatrixDataStatus.noMatrixDataYet
  sm2rRegularNoDirichletData :
    sm2rLedger.regular.dirichletDataStatus = SM2RDirichletDataStatus.noDirichletDataYet
  sm2rVariableNoDirichletData :
    sm2rLedger.variablePath.dirichletDataStatus = SM2RDirichletDataStatus.noDirichletDataYet
  status_eq_closed :
    status =
      SM3aRGeneratedPartitionLedgerStatus.generatedBoundaryInteriorPartitionClosed

def sm3aRGeneratedPartitionLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf) :
    SM3aRGeneratedPartitionLedger b β p where
  status := SM3aRGeneratedPartitionLedgerStatus.generatedBoundaryInteriorPartitionClosed
  sm2rLedger := sm2RGeneratedApproximantLedger b β p
  regular := regularGeneratedBoundaryInteriorPartition b p
  variablePath := variableGeneratedBoundaryInteriorPartition β p
  sm2rLedger_eq_main := by
    rfl
  regular_eq_main := by
    rfl
  variable_eq_main := by
    rfl
  sm2rRegular_eq_main := by
    rfl
  sm2rVariable_eq_main := by
    rfl
  regularBoundarySubset := by
    exact (regularGeneratedBoundaryInteriorPartition b p).boundary_subset_approximantCarrier
  regularInteriorSubset := by
    exact (regularGeneratedBoundaryInteriorPartition b p).interior_subset_approximantCarrier
  variableBoundarySubset := by
    exact (variableGeneratedBoundaryInteriorPartition β p).boundary_subset_approximantCarrier
  variableInteriorSubset := by
    exact (variableGeneratedBoundaryInteriorPartition β p).interior_subset_approximantCarrier
  regularDisjoint := by
    intro i
    exact (regularGeneratedBoundaryInteriorPartition b p).boundaryInterior_disjoint i
  variableDisjoint := by
    intro i
    exact (variableGeneratedBoundaryInteriorPartition β p).boundaryInterior_disjoint i
  regularComplete := by
    intro i hi
    exact (regularGeneratedBoundaryInteriorPartition b p).boundaryInterior_complete i hi
  variableComplete := by
    intro i hi
    exact (variableGeneratedBoundaryInteriorPartition β p).boundaryInterior_complete i hi
  regularNoFreeIndex := by
    rfl
  variableNoFreeIndex := by
    rfl
  regularNoCutSpecBoundaryPorts := by
    rfl
  variableNoCutSpecBoundaryPorts := by
    rfl
  regularNoMatrixData := by
    rfl
  variableNoMatrixData := by
    rfl
  sm2rRegularNoMatrixData := by
    rfl
  sm2rVariableNoMatrixData := by
    rfl
  sm2rRegularNoDirichletData := by
    rfl
  sm2rVariableNoDirichletData := by
    rfl
  status_eq_closed := by
    rfl

theorem sm3aRGeneratedPartitionLedger_status
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf) :
    (sm3aRGeneratedPartitionLedger b β p).status =
      SM3aRGeneratedPartitionLedgerStatus.generatedBoundaryInteriorPartitionClosed := by
  rfl

theorem sm3aRGeneratedPartitionLedger_regularNoFreeIndex
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf) :
    (sm3aRGeneratedPartitionLedger b β p).regular.noFreeIndexStatus =
      SM3aRNoFreeIndexStatus.noFreeFinReplacementIndex := by
  rfl

theorem sm3aRGeneratedPartitionLedger_variableNoFreeIndex
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf) :
    (sm3aRGeneratedPartitionLedger b β p).variablePath.noFreeIndexStatus =
      SM3aRNoFreeIndexStatus.noFreeFinReplacementIndex := by
  rfl

theorem sm3aRGeneratedPartitionLedger_regularNoMatrixData
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf) :
    (sm3aRGeneratedPartitionLedger b β p).regular.noMatrixDataStatus =
      SM3aRNoMatrixDataStatus.noMatrixDirichletDtnInverseOrTargetData := by
  rfl

theorem sm3aRGeneratedPartitionLedger_variableNoMatrixData
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf) :
    (sm3aRGeneratedPartitionLedger b β p).variablePath.noMatrixDataStatus =
      SM3aRNoMatrixDataStatus.noMatrixDirichletDtnInverseOrTargetData := by
  rfl

end Smoke

end CNNA.PillarA.Arithmetic
