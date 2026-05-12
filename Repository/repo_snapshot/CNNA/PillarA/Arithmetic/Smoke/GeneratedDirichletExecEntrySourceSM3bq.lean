import CNNA.PillarA.Foundation.ExecComplexBridge
import CNNA.PillarA.Arithmetic.Smoke.GeneratedDirichletEntry

set_option autoImplicit false
open scoped BigOperators

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

namespace Smoke

universe u

inductive SM3bqExecEntrySourceStatus where
  | execEntriesFromGeneratedDirichletWeightPolicy
  deriving DecidableEq, Repr

inductive SM3bqExecMatrixSourceStatus where
  | dirichletMatrixExecProjectedEntrywise
  deriving DecidableEq, Repr

inductive SM3bqNextPhaseStatus where
  | sm3eRqGeneratedInverseCandidateExecEntrySource
  deriving DecidableEq, Repr

inductive SM3bqNoFreeRationalTableStatus where
  | noFreeRationalTable
  deriving DecidableEq, Repr

inductive SM3bqNoRealToRatReverseCastStatus where
  | noRealToRatReverseCast
  deriving DecidableEq, Repr

inductive SM3bqNoScalarInverseStatus where
  | noScalarInverse
  deriving DecidableEq, Repr

inductive SM3bqNoMatrixInvStatus where
  | noMatrixInv
  deriving DecidableEq, Repr

inductive SM3bqNoSchurProductStatus where
  | noSchurProduct
  deriving DecidableEq, Repr

inductive SM3bqNoDtnStatus where
  | noDtnGeneralizedDtnOrMultiSchur
  deriving DecidableEq, Repr

inductive SM3bqNoCharpolyDiscriminantHeegnerStatus where
  | noCharpolyDiscriminantOrHeegner
  deriving DecidableEq, Repr

inductive SM3bqGeneratedDirichletExecEntrySourceLedgerStatus where
  | generatedDirichletExecEntrySourceClosed
  deriving DecidableEq, Repr

def generatedEntryWeightExecSM3bq
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (i j : GeneratedApproximantIndex A) : ExecComplex :=
  if generatedAdjacent i j then
    if i = j then 0 else ExecComplex.ofRat W.policy.beta
  else
    0

def generatedDirichletDegreeExecSM3bq
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (i : GeneratedApproximantIndex A) : ExecComplex :=
  ∑ j : GeneratedApproximantIndex A, generatedEntryWeightExecSM3bq W i j

def generatedDirichletEntryExecSM3bq
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (i j : GeneratedApproximantIndex A) : ExecComplex :=
  if i = j then generatedDirichletDegreeExecSM3bq W i else
    - generatedEntryWeightExecSM3bq W i j

def generatedDirichletMatrixExecSM3bq
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp) :
    Matrix (GeneratedApproximantIndex A) (GeneratedApproximantIndex A) ExecComplex :=
  fun i j => generatedDirichletEntryExecSM3bq W i j

theorem weightPolicy_beta_complex_eq_betaReal_complex
    (P : WeightPolicy) :
    ((P.beta : ℚ) : ℂ) = ((P.betaReal : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [WeightPolicy.beta, WeightPolicy.betaReal, ThermalAxis.betaReal]
  · simp [WeightPolicy.beta, WeightPolicy.betaReal, ThermalAxis.betaReal]

theorem generatedEntryWeightExecSM3bq_bridge
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (i j : GeneratedApproximantIndex A) :
    ExecComplexBridge.toComplex (generatedEntryWeightExecSM3bq W i j) =
      ((generatedEntryWeight W i j : ℝ) : ℂ) := by
  unfold generatedEntryWeightExecSM3bq generatedEntryWeight
  by_cases hadj : generatedAdjacent i j
  · simp only [if_pos hadj]
    by_cases hij : i = j
    · rw [if_pos hij]
      have hweight : W.policy.constantWeight i j = 0 := by
        rw [hij]
        exact WeightPolicy.constantWeight_self W.policy j
      rw [hweight]
      simpa using ExecComplexBridge.toComplex_zero
    · rw [if_neg hij]
      have hweight : W.policy.constantWeight i j = W.policy.betaReal := by
        exact WeightPolicy.constantWeight_of_ne W.policy hij
      rw [hweight]
      calc
        ExecComplexBridge.toComplex (ExecComplex.ofRat W.policy.beta) =
            (W.policy.beta : ℂ) := by
          exact ExecComplexBridge.toComplex_ofRat W.policy.beta
        _ = ((W.policy.betaReal : ℝ) : ℂ) := by
          exact weightPolicy_beta_complex_eq_betaReal_complex W.policy
  · simp only [if_neg hadj]
    simpa using ExecComplexBridge.toComplex_zero

theorem generatedDirichletDegreeExecSM3bq_eq_sum
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (i : GeneratedApproximantIndex A) :
    generatedDirichletDegreeExecSM3bq W i =
      ∑ j : GeneratedApproximantIndex A, generatedEntryWeightExecSM3bq W i j := by
  rfl

theorem generatedDirichletDegreeExecSM3bq_bridge
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (i : GeneratedApproximantIndex A) :
    ExecComplexBridge.toComplex (generatedDirichletDegreeExecSM3bq W i) =
      ((generatedDirichlet_degree W i : ℝ) : ℂ) := by
  unfold generatedDirichletDegreeExecSM3bq generatedDirichlet_degree
  calc
    ExecComplexBridge.toComplex
        (∑ j : GeneratedApproximantIndex A, generatedEntryWeightExecSM3bq W i j) =
        ∑ j : GeneratedApproximantIndex A,
          ExecComplexBridge.toComplex (generatedEntryWeightExecSM3bq W i j) := by
      exact ExecComplexBridge.toComplex_sum Finset.univ
        (fun j : GeneratedApproximantIndex A => generatedEntryWeightExecSM3bq W i j)
    _ = ∑ j : GeneratedApproximantIndex A,
          ((generatedEntryWeight W i j : ℝ) : ℂ) := by
      refine Finset.sum_congr rfl ?_
      intro j _hj
      exact generatedEntryWeightExecSM3bq_bridge W i j
    _ = ((∑ j : GeneratedApproximantIndex A, generatedEntryWeight W i j : ℝ) : ℂ) := by
      simp

theorem generatedDirichletEntryExecSM3bq_bridge
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (i j : GeneratedApproximantIndex A) :
    ExecComplexBridge.toComplex (generatedDirichletEntryExecSM3bq W i j) =
      ((generatedDirichlet_entry W i j : ℝ) : ℂ) := by
  unfold generatedDirichletEntryExecSM3bq generatedDirichlet_entry
  by_cases hij : i = j
  · simp only [if_pos hij]
    exact generatedDirichletDegreeExecSM3bq_bridge W i
  · simp only [if_neg hij]
    calc
      ExecComplexBridge.toComplex (-(generatedEntryWeightExecSM3bq W i j)) =
          -ExecComplexBridge.toComplex (generatedEntryWeightExecSM3bq W i j) := by
        exact ExecComplexBridge.toComplex_neg (generatedEntryWeightExecSM3bq W i j)
      _ = -((generatedEntryWeight W i j : ℝ) : ℂ) := by
        rw [generatedEntryWeightExecSM3bq_bridge W i j]
      _ = ((-generatedEntryWeight W i j : ℝ) : ℂ) := by
        simp

theorem generatedDirichletMatrixExecSM3bq_entry
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (i j : GeneratedApproximantIndex A) :
    generatedDirichletMatrixExecSM3bq W i j = generatedDirichletEntryExecSM3bq W i j := by
  rfl

theorem generatedDirichletMatrixExecSM3bq_bridge
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (i j : GeneratedApproximantIndex A) :
    ExecComplexBridge.toComplex (generatedDirichletMatrixExecSM3bq W i j) =
      ((generatedDirichletMatrix W i j : ℝ) : ℂ) := by
  rw [generatedDirichletMatrixExecSM3bq_entry W i j,
    generatedDirichletMatrix_entry W i j]
  exact generatedDirichletEntryExecSM3bq_bridge W i j

structure GeneratedDirichletExecEntrySourceSM3bq
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf)
    (A : GeneratedApproximantStrong Cell p)
    (P : GeneratedBoundaryInteriorPartition Cell p A)
    (wp : WeightPolicy)
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp) where
  sourceWeight : GeneratedWeightPolicyEntrySource Cell p A P wp
  sourceWeight_eq : sourceWeight = W
  entryWeightExec : GeneratedApproximantIndex A → GeneratedApproximantIndex A → ExecComplex
  entryWeightExec_eq : entryWeightExec = generatedEntryWeightExecSM3bq sourceWeight
  entryWeightExec_bridge : ∀ i j,
    ExecComplexBridge.toComplex (entryWeightExec i j) =
      ((generatedEntryWeight sourceWeight i j : ℝ) : ℂ)
  degreeExec : GeneratedApproximantIndex A → ExecComplex
  degreeExec_eq_sum : ∀ i,
    degreeExec i = ∑ j : GeneratedApproximantIndex A, entryWeightExec i j
  degreeExec_bridge : ∀ i,
    ExecComplexBridge.toComplex (degreeExec i) =
      ((generatedDirichlet_degree sourceWeight i : ℝ) : ℂ)
  dirichletEntryExec : GeneratedApproximantIndex A → GeneratedApproximantIndex A → ExecComplex
  dirichletEntryExec_eq : dirichletEntryExec = generatedDirichletEntryExecSM3bq sourceWeight
  dirichletEntryExec_bridge : ∀ i j,
    ExecComplexBridge.toComplex (dirichletEntryExec i j) =
      ((generatedDirichlet_entry sourceWeight i j : ℝ) : ℂ)
  dirichletMatrixExec :
    Matrix (GeneratedApproximantIndex A) (GeneratedApproximantIndex A) ExecComplex
  dirichletMatrixExec_eq : dirichletMatrixExec = generatedDirichletMatrixExecSM3bq sourceWeight
  dirichletMatrixExec_entry : ∀ i j,
    dirichletMatrixExec i j = dirichletEntryExec i j
  dirichletMatrixExec_bridge : ∀ i j,
    ExecComplexBridge.toComplex (dirichletMatrixExec i j) =
      ((generatedDirichletMatrix sourceWeight i j : ℝ) : ℂ)
  sourceStatus : SM3bqExecEntrySourceStatus
  sourceStatus_eq :
    sourceStatus = SM3bqExecEntrySourceStatus.execEntriesFromGeneratedDirichletWeightPolicy
  matrixStatus : SM3bqExecMatrixSourceStatus
  matrixStatus_eq :
    matrixStatus = SM3bqExecMatrixSourceStatus.dirichletMatrixExecProjectedEntrywise
  nextPhaseStatus : SM3bqNextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus = SM3bqNextPhaseStatus.sm3eRqGeneratedInverseCandidateExecEntrySource
  noFreeRationalTableStatus : SM3bqNoFreeRationalTableStatus
  noFreeRationalTableStatus_eq :
    noFreeRationalTableStatus = SM3bqNoFreeRationalTableStatus.noFreeRationalTable
  noRealToRatReverseCastStatus : SM3bqNoRealToRatReverseCastStatus
  noRealToRatReverseCastStatus_eq :
    noRealToRatReverseCastStatus =
      SM3bqNoRealToRatReverseCastStatus.noRealToRatReverseCast
  noScalarInverseStatus : SM3bqNoScalarInverseStatus
  noScalarInverseStatus_eq :
    noScalarInverseStatus = SM3bqNoScalarInverseStatus.noScalarInverse
  noMatrixInvStatus : SM3bqNoMatrixInvStatus
  noMatrixInvStatus_eq : noMatrixInvStatus = SM3bqNoMatrixInvStatus.noMatrixInv
  noSchurProductStatus : SM3bqNoSchurProductStatus
  noSchurProductStatus_eq :
    noSchurProductStatus = SM3bqNoSchurProductStatus.noSchurProduct
  noDtnStatus : SM3bqNoDtnStatus
  noDtnStatus_eq :
    noDtnStatus = SM3bqNoDtnStatus.noDtnGeneralizedDtnOrMultiSchur
  noCharpolyDiscriminantHeegnerStatus : SM3bqNoCharpolyDiscriminantHeegnerStatus
  noCharpolyDiscriminantHeegnerStatus_eq :
    noCharpolyDiscriminantHeegnerStatus =
      SM3bqNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantOrHeegner

namespace GeneratedDirichletExecEntrySourceSM3bq

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {p : ConcretePolicyOf}
variable {A : GeneratedApproximantStrong Cell p}
variable {P : GeneratedBoundaryInteriorPartition Cell p A}
variable {wp : WeightPolicy}
variable {W : GeneratedWeightPolicyEntrySource Cell p A P wp}

def fromWeightSource : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W where
  sourceWeight := W
  sourceWeight_eq := by
    rfl
  entryWeightExec := generatedEntryWeightExecSM3bq W
  entryWeightExec_eq := by
    rfl
  entryWeightExec_bridge := by
    intro i j
    exact generatedEntryWeightExecSM3bq_bridge W i j
  degreeExec := generatedDirichletDegreeExecSM3bq W
  degreeExec_eq_sum := by
    intro i
    rfl
  degreeExec_bridge := by
    intro i
    exact generatedDirichletDegreeExecSM3bq_bridge W i
  dirichletEntryExec := generatedDirichletEntryExecSM3bq W
  dirichletEntryExec_eq := by
    rfl
  dirichletEntryExec_bridge := by
    intro i j
    exact generatedDirichletEntryExecSM3bq_bridge W i j
  dirichletMatrixExec := generatedDirichletMatrixExecSM3bq W
  dirichletMatrixExec_eq := by
    rfl
  dirichletMatrixExec_entry := by
    intro i j
    rfl
  dirichletMatrixExec_bridge := by
    intro i j
    exact generatedDirichletMatrixExecSM3bq_bridge W i j
  sourceStatus := SM3bqExecEntrySourceStatus.execEntriesFromGeneratedDirichletWeightPolicy
  sourceStatus_eq := by
    rfl
  matrixStatus := SM3bqExecMatrixSourceStatus.dirichletMatrixExecProjectedEntrywise
  matrixStatus_eq := by
    rfl
  nextPhaseStatus := SM3bqNextPhaseStatus.sm3eRqGeneratedInverseCandidateExecEntrySource
  nextPhaseStatus_eq := by
    rfl
  noFreeRationalTableStatus := SM3bqNoFreeRationalTableStatus.noFreeRationalTable
  noFreeRationalTableStatus_eq := by
    rfl
  noRealToRatReverseCastStatus := SM3bqNoRealToRatReverseCastStatus.noRealToRatReverseCast
  noRealToRatReverseCastStatus_eq := by
    rfl
  noScalarInverseStatus := SM3bqNoScalarInverseStatus.noScalarInverse
  noScalarInverseStatus_eq := by
    rfl
  noMatrixInvStatus := SM3bqNoMatrixInvStatus.noMatrixInv
  noMatrixInvStatus_eq := by
    rfl
  noSchurProductStatus := SM3bqNoSchurProductStatus.noSchurProduct
  noSchurProductStatus_eq := by
    rfl
  noDtnStatus := SM3bqNoDtnStatus.noDtnGeneralizedDtnOrMultiSchur
  noDtnStatus_eq := by
    rfl
  noCharpolyDiscriminantHeegnerStatus :=
    SM3bqNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantOrHeegner
  noCharpolyDiscriminantHeegnerStatus_eq := by
    rfl

theorem sourceWeight_from_input
    (S : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W) :
    S.sourceWeight = W :=
  S.sourceWeight_eq

theorem entryWeightExec_bridge_to_generatedWeight
    (S : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W)
    (i j : GeneratedApproximantIndex A) :
    ExecComplexBridge.toComplex (S.entryWeightExec i j) =
      ((generatedEntryWeight S.sourceWeight i j : ℝ) : ℂ) :=
  S.entryWeightExec_bridge i j

theorem degreeExec_bridge_to_generatedDegree
    (S : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W)
    (i : GeneratedApproximantIndex A) :
    ExecComplexBridge.toComplex (S.degreeExec i) =
      ((generatedDirichlet_degree S.sourceWeight i : ℝ) : ℂ) :=
  S.degreeExec_bridge i

theorem dirichletEntryExec_bridge_to_generatedEntry
    (S : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W)
    (i j : GeneratedApproximantIndex A) :
    ExecComplexBridge.toComplex (S.dirichletEntryExec i j) =
      ((generatedDirichlet_entry S.sourceWeight i j : ℝ) : ℂ) :=
  S.dirichletEntryExec_bridge i j

theorem dirichletMatrixExec_bridge_to_generatedMatrix
    (S : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W)
    (i j : GeneratedApproximantIndex A) :
    ExecComplexBridge.toComplex (S.dirichletMatrixExec i j) =
      ((generatedDirichletMatrix S.sourceWeight i j : ℝ) : ℂ) :=
  S.dirichletMatrixExec_bridge i j

theorem no_real_to_rat_reverse_cast
    (S : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W) :
    S.noRealToRatReverseCastStatus =
      SM3bqNoRealToRatReverseCastStatus.noRealToRatReverseCast :=
  S.noRealToRatReverseCastStatus_eq

theorem no_scalar_inverse
    (S : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W) :
    S.noScalarInverseStatus = SM3bqNoScalarInverseStatus.noScalarInverse :=
  S.noScalarInverseStatus_eq

theorem no_matrix_inv
    (S : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W) :
    S.noMatrixInvStatus = SM3bqNoMatrixInvStatus.noMatrixInv :=
  S.noMatrixInvStatus_eq

theorem no_schur_product
    (S : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W) :
    S.noSchurProductStatus = SM3bqNoSchurProductStatus.noSchurProduct :=
  S.noSchurProductStatus_eq

theorem no_dtn
    (S : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W) :
    S.noDtnStatus = SM3bqNoDtnStatus.noDtnGeneralizedDtnOrMultiSchur :=
  S.noDtnStatus_eq

theorem no_charpoly_discriminant_heegner
    (S : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W) :
    S.noCharpolyDiscriminantHeegnerStatus =
      SM3bqNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantOrHeegner :=
  S.noCharpolyDiscriminantHeegnerStatus_eq

theorem next_phase_is_SM3eRq
    (S : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W) :
    S.nextPhaseStatus = SM3bqNextPhaseStatus.sm3eRqGeneratedInverseCandidateExecEntrySource :=
  S.nextPhaseStatus_eq

end GeneratedDirichletExecEntrySourceSM3bq

def regularGeneratedDirichletExecEntrySourceSM3bq
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedDirichletExecEntrySourceSM3bq
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) wp
      (regularGeneratedWeightPolicyEntrySource b p wp) :=
  GeneratedDirichletExecEntrySourceSM3bq.fromWeightSource

def variableGeneratedDirichletExecEntrySourceSM3bq
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedDirichletExecEntrySourceSM3bq
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) wp
      (variableGeneratedWeightPolicyEntrySource β p wp) :=
  GeneratedDirichletExecEntrySourceSM3bq.fromWeightSource

structure SM3bqGeneratedDirichletExecEntrySourceLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  status : SM3bqGeneratedDirichletExecEntrySourceLedgerStatus
  sm3bRLedger : SM3bRGeneratedDirichletEntryLedger b β p regularWeight variableWeight
  regularExecSource :
    GeneratedDirichletExecEntrySourceSM3bq
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
  variableExecSource :
    GeneratedDirichletExecEntrySourceSM3bq
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
  sm3bRLedger_eq_main :
    sm3bRLedger = sm3bRGeneratedDirichletEntryLedger b β p regularWeight variableWeight
  regularExecSource_eq_main :
    regularExecSource = regularGeneratedDirichletExecEntrySourceSM3bq b p regularWeight
  variableExecSource_eq_main :
    variableExecSource = variableGeneratedDirichletExecEntrySourceSM3bq β p variableWeight
  regularEntryWeightBridge : ∀ i j,
    ExecComplexBridge.toComplex (regularExecSource.entryWeightExec i j) =
      ((generatedEntryWeight regularExecSource.sourceWeight i j : ℝ) : ℂ)
  variableEntryWeightBridge : ∀ i j,
    ExecComplexBridge.toComplex (variableExecSource.entryWeightExec i j) =
      ((generatedEntryWeight variableExecSource.sourceWeight i j : ℝ) : ℂ)
  regularDegreeBridge : ∀ i,
    ExecComplexBridge.toComplex (regularExecSource.degreeExec i) =
      ((generatedDirichlet_degree regularExecSource.sourceWeight i : ℝ) : ℂ)
  variableDegreeBridge : ∀ i,
    ExecComplexBridge.toComplex (variableExecSource.degreeExec i) =
      ((generatedDirichlet_degree variableExecSource.sourceWeight i : ℝ) : ℂ)
  regularDirichletEntryBridge : ∀ i j,
    ExecComplexBridge.toComplex (regularExecSource.dirichletEntryExec i j) =
      ((generatedDirichlet_entry regularExecSource.sourceWeight i j : ℝ) : ℂ)
  variableDirichletEntryBridge : ∀ i j,
    ExecComplexBridge.toComplex (variableExecSource.dirichletEntryExec i j) =
      ((generatedDirichlet_entry variableExecSource.sourceWeight i j : ℝ) : ℂ)
  regularMatrixBridge : ∀ i j,
    ExecComplexBridge.toComplex (regularExecSource.dirichletMatrixExec i j) =
      ((generatedDirichletMatrix regularExecSource.sourceWeight i j : ℝ) : ℂ)
  variableMatrixBridge : ∀ i j,
    ExecComplexBridge.toComplex (variableExecSource.dirichletMatrixExec i j) =
      ((generatedDirichletMatrix variableExecSource.sourceWeight i j : ℝ) : ℂ)
  regularNoFreeRationalTable :
    regularExecSource.noFreeRationalTableStatus =
      SM3bqNoFreeRationalTableStatus.noFreeRationalTable
  variableNoFreeRationalTable :
    variableExecSource.noFreeRationalTableStatus =
      SM3bqNoFreeRationalTableStatus.noFreeRationalTable
  regularNoRealToRatReverseCast :
    regularExecSource.noRealToRatReverseCastStatus =
      SM3bqNoRealToRatReverseCastStatus.noRealToRatReverseCast
  variableNoRealToRatReverseCast :
    variableExecSource.noRealToRatReverseCastStatus =
      SM3bqNoRealToRatReverseCastStatus.noRealToRatReverseCast
  regularNoScalarInverse :
    regularExecSource.noScalarInverseStatus = SM3bqNoScalarInverseStatus.noScalarInverse
  variableNoScalarInverse :
    variableExecSource.noScalarInverseStatus = SM3bqNoScalarInverseStatus.noScalarInverse
  regularNoMatrixInv : regularExecSource.noMatrixInvStatus = SM3bqNoMatrixInvStatus.noMatrixInv
  variableNoMatrixInv : variableExecSource.noMatrixInvStatus = SM3bqNoMatrixInvStatus.noMatrixInv
  regularNoSchurProduct :
    regularExecSource.noSchurProductStatus = SM3bqNoSchurProductStatus.noSchurProduct
  variableNoSchurProduct :
    variableExecSource.noSchurProductStatus = SM3bqNoSchurProductStatus.noSchurProduct
  regularNoDtn :
    regularExecSource.noDtnStatus = SM3bqNoDtnStatus.noDtnGeneralizedDtnOrMultiSchur
  variableNoDtn :
    variableExecSource.noDtnStatus = SM3bqNoDtnStatus.noDtnGeneralizedDtnOrMultiSchur
  regularNoCharpolyDiscriminantHeegner :
    regularExecSource.noCharpolyDiscriminantHeegnerStatus =
      SM3bqNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantOrHeegner
  variableNoCharpolyDiscriminantHeegner :
    variableExecSource.noCharpolyDiscriminantHeegnerStatus =
      SM3bqNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantOrHeegner
  regularNextPhase :
    regularExecSource.nextPhaseStatus =
      SM3bqNextPhaseStatus.sm3eRqGeneratedInverseCandidateExecEntrySource
  variableNextPhase :
    variableExecSource.nextPhaseStatus =
      SM3bqNextPhaseStatus.sm3eRqGeneratedInverseCandidateExecEntrySource
  status_eq_closed :
    status =
      SM3bqGeneratedDirichletExecEntrySourceLedgerStatus.generatedDirichletExecEntrySourceClosed

def sm3bqGeneratedDirichletExecEntrySourceLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    SM3bqGeneratedDirichletExecEntrySourceLedger b β p regularWeight variableWeight where
  status :=
    SM3bqGeneratedDirichletExecEntrySourceLedgerStatus.generatedDirichletExecEntrySourceClosed
  sm3bRLedger := sm3bRGeneratedDirichletEntryLedger b β p regularWeight variableWeight
  regularExecSource := regularGeneratedDirichletExecEntrySourceSM3bq b p regularWeight
  variableExecSource := variableGeneratedDirichletExecEntrySourceSM3bq β p variableWeight
  sm3bRLedger_eq_main := by
    rfl
  regularExecSource_eq_main := by
    rfl
  variableExecSource_eq_main := by
    rfl
  regularEntryWeightBridge := by
    intro i j
    exact (regularGeneratedDirichletExecEntrySourceSM3bq b p regularWeight).entryWeightExec_bridge i j
  variableEntryWeightBridge := by
    intro i j
    exact (variableGeneratedDirichletExecEntrySourceSM3bq β p variableWeight).entryWeightExec_bridge i j
  regularDegreeBridge := by
    intro i
    exact (regularGeneratedDirichletExecEntrySourceSM3bq b p regularWeight).degreeExec_bridge i
  variableDegreeBridge := by
    intro i
    exact (variableGeneratedDirichletExecEntrySourceSM3bq β p variableWeight).degreeExec_bridge i
  regularDirichletEntryBridge := by
    intro i j
    exact (regularGeneratedDirichletExecEntrySourceSM3bq b p regularWeight).dirichletEntryExec_bridge i j
  variableDirichletEntryBridge := by
    intro i j
    exact (variableGeneratedDirichletExecEntrySourceSM3bq β p variableWeight).dirichletEntryExec_bridge i j
  regularMatrixBridge := by
    intro i j
    exact (regularGeneratedDirichletExecEntrySourceSM3bq b p regularWeight).dirichletMatrixExec_bridge i j
  variableMatrixBridge := by
    intro i j
    exact (variableGeneratedDirichletExecEntrySourceSM3bq β p variableWeight).dirichletMatrixExec_bridge i j
  regularNoFreeRationalTable := by
    rfl
  variableNoFreeRationalTable := by
    rfl
  regularNoRealToRatReverseCast := by
    rfl
  variableNoRealToRatReverseCast := by
    rfl
  regularNoScalarInverse := by
    rfl
  variableNoScalarInverse := by
    rfl
  regularNoMatrixInv := by
    rfl
  variableNoMatrixInv := by
    rfl
  regularNoSchurProduct := by
    rfl
  variableNoSchurProduct := by
    rfl
  regularNoDtn := by
    rfl
  variableNoDtn := by
    rfl
  regularNoCharpolyDiscriminantHeegner := by
    rfl
  variableNoCharpolyDiscriminantHeegner := by
    rfl
  regularNextPhase := by
    rfl
  variableNextPhase := by
    rfl
  status_eq_closed := by
    rfl

theorem sm3bqGeneratedDirichletExecEntrySourceLedger_status
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3bqGeneratedDirichletExecEntrySourceLedger b β p regularWeight variableWeight).status =
      SM3bqGeneratedDirichletExecEntrySourceLedgerStatus.generatedDirichletExecEntrySourceClosed := by
  rfl

theorem sm3bqGeneratedDirichletExecEntrySourceLedger_regularNextPhase
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3bqGeneratedDirichletExecEntrySourceLedger b β p regularWeight variableWeight).regularExecSource.nextPhaseStatus =
      SM3bqNextPhaseStatus.sm3eRqGeneratedInverseCandidateExecEntrySource := by
  rfl

theorem sm3bqGeneratedDirichletExecEntrySourceLedger_variableNextPhase
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3bqGeneratedDirichletExecEntrySourceLedger b β p regularWeight variableWeight).variableExecSource.nextPhaseStatus =
      SM3bqNextPhaseStatus.sm3eRqGeneratedInverseCandidateExecEntrySource := by
  rfl

theorem sm3bqGeneratedDirichletExecEntrySourceLedger_regularNoForbiddenShortcuts
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3bqGeneratedDirichletExecEntrySourceLedger b β p regularWeight variableWeight).regularExecSource.noSchurProductStatus =
      SM3bqNoSchurProductStatus.noSchurProduct ∧
    (sm3bqGeneratedDirichletExecEntrySourceLedger b β p regularWeight variableWeight).regularExecSource.noDtnStatus =
      SM3bqNoDtnStatus.noDtnGeneralizedDtnOrMultiSchur ∧
    (sm3bqGeneratedDirichletExecEntrySourceLedger b β p regularWeight variableWeight).regularExecSource.noCharpolyDiscriminantHeegnerStatus =
      SM3bqNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantOrHeegner := by
  exact ⟨rfl, rfl, rfl⟩

theorem sm3bqGeneratedDirichletExecEntrySourceLedger_variableNoForbiddenShortcuts
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3bqGeneratedDirichletExecEntrySourceLedger b β p regularWeight variableWeight).variableExecSource.noSchurProductStatus =
      SM3bqNoSchurProductStatus.noSchurProduct ∧
    (sm3bqGeneratedDirichletExecEntrySourceLedger b β p regularWeight variableWeight).variableExecSource.noDtnStatus =
      SM3bqNoDtnStatus.noDtnGeneralizedDtnOrMultiSchur ∧
    (sm3bqGeneratedDirichletExecEntrySourceLedger b β p regularWeight variableWeight).variableExecSource.noCharpolyDiscriminantHeegnerStatus =
      SM3bqNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantOrHeegner := by
  exact ⟨rfl, rfl, rfl⟩

end Smoke

end CNNA.PillarA.Arithmetic
