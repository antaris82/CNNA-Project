import CNNA.PillarA.Arithmetic.Smoke.GeneratedDirichletExecEntrySourceSM3bq
import CNNA.PillarA.Arithmetic.Smoke.SM3dbRToSM3eRHandoff

set_option autoImplicit false
open scoped BigOperators

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

namespace Smoke

universe u

inductive SM3eRqExecEntrySourceStatus where
  | inverseCandidateEntriesFromAccumulatedTraceAndDirichletExecSource
  deriving DecidableEq, Repr

inductive SM3eRqExecMatrixSourceStatus where
  | inverseCandidateMatrixExecProjectedEntrywise
  deriving DecidableEq, Repr

inductive SM3eRqNextPhaseStatus where
  | sm3fqPlusSchurExecCompletion
  deriving DecidableEq, Repr

inductive SM3eRqNoFreeRationalTableStatus where
  | noFreeRationalTable
  deriving DecidableEq, Repr

inductive SM3eRqNoRealToRatReverseCastStatus where
  | noRealToRatReverseCast
  deriving DecidableEq, Repr

inductive SM3eRqNoScalarInverseStatus where
  | noScalarInverse
  deriving DecidableEq, Repr

inductive SM3eRqNoMatrixInvStatus where
  | noMatrixInv
  deriving DecidableEq, Repr

inductive SM3eRqNoProductProofStatus where
  | noProductProof
  deriving DecidableEq, Repr

inductive SM3eRqNoTwoSidedInvStatus where
  | noTwoSidedInv
  deriving DecidableEq, Repr

inductive SM3eRqNoInteriorEliminationCertificateStatus where
  | noInteriorEliminationCertificate
  deriving DecidableEq, Repr

inductive SM3eRqNoSchurBoundaryOperatorStatus where
  | noSchurBoundaryOperator
  deriving DecidableEq, Repr

inductive SM3eRqNoDtnMultiSchurStatus where
  | noDtnGeneralizedDtnOrMultiSchur
  deriving DecidableEq, Repr

inductive SM3eRqNoCharpolyDiscriminantHeegnerStatus where
  | noCharpolyDiscriminantOrHeegner
  deriving DecidableEq, Repr

inductive SM3eRqGeneratedInverseCandidateExecEntrySourceLedgerStatus where
  | generatedInverseCandidateExecEntrySourceClosed
  deriving DecidableEq, Repr

def generatedInteriorBlockEntryExecSM3eRq
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    (D : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W)
    (i j : GeneratedInteriorIndex A) : ExecComplex :=
  D.dirichletMatrixExec
    (GeneratedInteriorIndex.toApproximantIndex i)
    (GeneratedInteriorIndex.toApproximantIndex j)

theorem generatedInteriorBlockEntryExecSM3eRq_bridge
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    (D : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W)
    (i j : GeneratedInteriorIndex A) :
    ExecComplexBridge.toComplex (generatedInteriorBlockEntryExecSM3eRq D i j) =
      ((generatedInteriorBlock W i j : ℝ) : ℂ) := by
  calc
    ExecComplexBridge.toComplex (generatedInteriorBlockEntryExecSM3eRq D i j) =
        ((generatedDirichletMatrix D.sourceWeight
          (GeneratedInteriorIndex.toApproximantIndex i)
          (GeneratedInteriorIndex.toApproximantIndex j) : ℝ) : ℂ) := by
      exact D.dirichletMatrixExec_bridge
        (GeneratedInteriorIndex.toApproximantIndex i)
        (GeneratedInteriorIndex.toApproximantIndex j)
    _ = ((generatedDirichletMatrix W
          (GeneratedInteriorIndex.toApproximantIndex i)
          (GeneratedInteriorIndex.toApproximantIndex j) : ℝ) : ℂ) := by
      rw [D.sourceWeight_eq]
    _ = ((generatedInteriorBlock W i j : ℝ) : ℂ) := by
      rw [← generatedInteriorBlock_from_dirichlet W i j]

def generatedInteriorTracePivotContributionExecSM3eRq
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
    (D : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W)
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K)
    (i j : GeneratedInteriorIndex A) : ExecComplex :=
  generatedInteriorBlockEntryExecSM3eRq D
      (T.localStepOf i).pivotDatum.pivotIndex
      (T.localStepOf i).pivotDatum.pivotIndex +
    generatedInteriorBlockEntryExecSM3eRq D
      (T.localStepOf j).pivotDatum.pivotIndex
      (T.localStepOf j).pivotDatum.pivotIndex

def generatedInteriorTraceLocalStepContributionExecSM3eRq
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    (D : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W)
    (i j : GeneratedInteriorIndex A) : ExecComplex :=
  generatedInteriorBlockEntryExecSM3eRq D i j

def generatedInteriorTraceResidualContributionExecSM3eRq
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
    (D : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W)
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K)
    (i j : GeneratedInteriorIndex A) : ExecComplex :=
  generatedInteriorBlockEntryExecSM3eRq D
    (T.localStepOf i).pivotDatum.pivotIndex j

def generatedInteriorTraceFoldUpdateOrderContributionExecSM3eRq
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
    (D : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W)
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K)
    (i j : GeneratedInteriorIndex A) : ExecComplex :=
  generatedInteriorBlockEntryExecSM3eRq D i
    (T.localStepOf j).pivotDatum.pivotIndex

theorem tracePivotEntry_eq_generatedInteriorBlockSM3eRq
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
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K)
    (i : GeneratedInteriorIndex A) :
    (T.traceStepOf i).pivotDatum.pivotEntry =
      generatedInteriorBlock W
        (T.localStepOf i).pivotDatum.pivotIndex
        (T.localStepOf i).pivotDatum.pivotIndex := by
  have hPivotDatum :
      (T.traceStepOf i).pivotDatum = (T.localStepOf i).pivotDatum :=
    (T.traceStepOf i).pivotDatum_eq_localStepPivot
  calc
    (T.traceStepOf i).pivotDatum.pivotEntry =
        (T.localStepOf i).pivotDatum.pivotEntry := by
      rw [hPivotDatum]
    _ = generatedInteriorBlock W
        (T.localStepOf i).pivotDatum.pivotIndex
        (T.localStepOf i).pivotDatum.pivotIndex := by
      change (T.localStepOf i).pivotDatum.pivotEntry =
        generatedInteriorLocalPivotEntry W (T.localStepOf i).pivotDatum.pivotIndex
      exact (T.localStepOf i).pivotDatum.pivotEntry_eq_interiorBlock

theorem traceLocalStepContribution_eq_generatedInteriorBlockSM3eRq
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
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K)
    (i j : GeneratedInteriorIndex A) :
    (T.traceStepOf i).localStep.stepUpdate.baseEntry i j =
      generatedInteriorBlock W i j := by
  have hLocalStep : (T.traceStepOf i).localStep = T.localStepOf i :=
    (T.traceStepOf i).localStep_eq_SM3db2R_step
  calc
    (T.traceStepOf i).localStep.stepUpdate.baseEntry i j =
        (T.localStepOf i).stepUpdate.baseEntry i j := by
      rw [hLocalStep]
    _ = generatedInteriorBlock W i j := by
      change (T.localStepOf i).stepUpdate.baseEntry i j =
        generatedInteriorLocalBaseEntry W i j
      exact (T.localStepOf i).stepUpdate.baseEntry_eq_interiorBlock i j

theorem traceResidualContribution_eq_generatedInteriorBlockSM3eRq
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
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K)
    (i j : GeneratedInteriorIndex A) :
    (T.traceStepOf i).residualDatum.rowResidual j =
      generatedInteriorBlock W (T.localStepOf i).pivotDatum.pivotIndex j := by
  have hResidualDatum :
      (T.traceStepOf i).residualDatum = (T.localStepOf i).residualDatum :=
    (T.traceStepOf i).residualDatum_eq_localStepResidual
  calc
    (T.traceStepOf i).residualDatum.rowResidual j =
        (T.localStepOf i).residualDatum.rowResidual j := by
      rw [hResidualDatum]
    _ = generatedInteriorLocalRowResidual W (T.localStepOf i).pivotDatum.pivotIndex j := by
      exact T.traceStep_residual_eq_SM3cR_interiorBlock i j
    _ = generatedInteriorBlock W (T.localStepOf i).pivotDatum.pivotIndex j := by
      rfl

theorem traceFoldUpdateOrderContribution_eq_generatedInteriorBlockSM3eRq
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
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K)
    (i j : GeneratedInteriorIndex A) :
    (T.traceStepOf j).stepUpdate.columnResidual i =
      generatedInteriorBlock W i (T.localStepOf j).pivotDatum.pivotIndex := by
  have hStepUpdate :
      (T.traceStepOf j).stepUpdate = (T.localStepOf j).stepUpdate :=
    (T.traceStepOf j).stepUpdate_eq_localStepUpdate
  calc
    (T.traceStepOf j).stepUpdate.columnResidual i =
        (T.localStepOf j).stepUpdate.columnResidual i := by
      rw [hStepUpdate]
    _ = (T.localStepOf j).residualDatum.columnResidual i := by
      exact (T.localStepOf j).stepUpdate.columnResidual_eq_residualDatum i
    _ = generatedInteriorLocalColumnResidual W (T.localStepOf j).pivotDatum.pivotIndex i := by
      exact T.traceStep_columnResidual_eq_SM3cR_interiorBlock j i
    _ = generatedInteriorBlock W i (T.localStepOf j).pivotDatum.pivotIndex := by
      rfl

theorem generatedInteriorTracePivotContributionExecSM3eRq_bridge
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
    (D : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W)
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K)
    (i j : GeneratedInteriorIndex A) :
    ExecComplexBridge.toComplex
        (generatedInteriorTracePivotContributionExecSM3eRq D T i j) =
      ((generatedInteriorTracePivotContribution T i j : ℝ) : ℂ) := by
  have hi := tracePivotEntry_eq_generatedInteriorBlockSM3eRq T i
  have hj := tracePivotEntry_eq_generatedInteriorBlockSM3eRq T j
  unfold generatedInteriorTracePivotContributionExecSM3eRq
  rw [ExecComplexBridge.toComplex_add]
  rw [generatedInteriorBlockEntryExecSM3eRq_bridge D
      (T.localStepOf i).pivotDatum.pivotIndex
      (T.localStepOf i).pivotDatum.pivotIndex]
  rw [generatedInteriorBlockEntryExecSM3eRq_bridge D
      (T.localStepOf j).pivotDatum.pivotIndex
      (T.localStepOf j).pivotDatum.pivotIndex]
  rw [← hi, ← hj]
  simp [generatedInteriorTracePivotContribution]

theorem generatedInteriorTraceLocalStepContributionExecSM3eRq_bridge
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
    (D : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W)
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K)
    (i j : GeneratedInteriorIndex A) :
    ExecComplexBridge.toComplex
        (generatedInteriorTraceLocalStepContributionExecSM3eRq D i j) =
      ((generatedInteriorTraceLocalStepContribution T i j : ℝ) : ℂ) := by
  have h := traceLocalStepContribution_eq_generatedInteriorBlockSM3eRq T i j
  unfold generatedInteriorTraceLocalStepContributionExecSM3eRq
  rw [generatedInteriorBlockEntryExecSM3eRq_bridge D i j]
  rw [← h]
  rfl

theorem generatedInteriorTraceResidualContributionExecSM3eRq_bridge
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
    (D : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W)
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K)
    (i j : GeneratedInteriorIndex A) :
    ExecComplexBridge.toComplex
        (generatedInteriorTraceResidualContributionExecSM3eRq D T i j) =
      ((generatedInteriorTraceResidualContribution T i j : ℝ) : ℂ) := by
  have h := traceResidualContribution_eq_generatedInteriorBlockSM3eRq T i j
  unfold generatedInteriorTraceResidualContributionExecSM3eRq
  rw [generatedInteriorBlockEntryExecSM3eRq_bridge D (T.localStepOf i).pivotDatum.pivotIndex j]
  rw [← h]
  rfl

theorem generatedInteriorTraceFoldUpdateOrderContributionExecSM3eRq_bridge
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
    (D : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W)
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K)
    (i j : GeneratedInteriorIndex A) :
    ExecComplexBridge.toComplex
        (generatedInteriorTraceFoldUpdateOrderContributionExecSM3eRq D T i j) =
      ((generatedInteriorTraceFoldUpdateOrderContribution T i j : ℝ) : ℂ) := by
  have h := traceFoldUpdateOrderContribution_eq_generatedInteriorBlockSM3eRq T i j
  unfold generatedInteriorTraceFoldUpdateOrderContributionExecSM3eRq
  rw [generatedInteriorBlockEntryExecSM3eRq_bridge D i (T.localStepOf j).pivotDatum.pivotIndex]
  rw [← h]
  rfl

def generatedInverseCandidateEntryExecSM3eRq
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
    (D : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W)
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K)
    (i j : GeneratedInteriorIndex A) : ExecComplex :=
  generatedInteriorTracePivotContributionExecSM3eRq D T i j +
    generatedInteriorTraceLocalStepContributionExecSM3eRq D i j +
      generatedInteriorTraceResidualContributionExecSM3eRq D T i j +
        generatedInteriorTraceFoldUpdateOrderContributionExecSM3eRq D T i j

def generatedInverseCandidateMatrixExecSM3eRq
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
    (D : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W)
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K) :
    Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ExecComplex :=
  fun i j => generatedInverseCandidateEntryExecSM3eRq D T i j

theorem generatedInverseCandidateEntryExecSM3eRq_bridge
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
    (D : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W)
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K)
    (i j : GeneratedInteriorIndex A) :
    ExecComplexBridge.toComplex (generatedInverseCandidateEntryExecSM3eRq D T i j) =
      ((generatedInteriorAccumulatedEntryValue T i j : ℝ) : ℂ) := by
  unfold generatedInverseCandidateEntryExecSM3eRq generatedInteriorAccumulatedEntryValue
  repeat rw [ExecComplexBridge.toComplex_add]
  rw [generatedInteriorTracePivotContributionExecSM3eRq_bridge D T i j]
  rw [generatedInteriorTraceLocalStepContributionExecSM3eRq_bridge D T i j]
  rw [generatedInteriorTraceResidualContributionExecSM3eRq_bridge D T i j]
  rw [generatedInteriorTraceFoldUpdateOrderContributionExecSM3eRq_bridge D T i j]
  simp

theorem generatedInverseCandidateMatrixExecSM3eRq_entry
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
    (D : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W)
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K)
    (i j : GeneratedInteriorIndex A) :
    generatedInverseCandidateMatrixExecSM3eRq D T i j =
      generatedInverseCandidateEntryExecSM3eRq D T i j := by
  rfl

theorem generatedInverseCandidateMatrixExecSM3eRq_bridge_to_accumulatedValue
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
    (D : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W)
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K)
    (i j : GeneratedInteriorIndex A) :
    ExecComplexBridge.toComplex (generatedInverseCandidateMatrixExecSM3eRq D T i j) =
      ((generatedInteriorAccumulatedEntryValue T i j : ℝ) : ℂ) := by
  rw [generatedInverseCandidateMatrixExecSM3eRq_entry D T i j]
  exact generatedInverseCandidateEntryExecSM3eRq_bridge D T i j

structure GeneratedInverseCandidateExecEntrySourceSM3eRq
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
    (T : GeneratedInteriorEliminationTrace Cell p A P wp W E K)
    (M : GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T)
    (S : GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M)
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S) where
  sourceDirichletExec : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W
  sourceHandoff : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S
  sourceMatrix : GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T
  sourceAccumulatedEntry : GeneratedInteriorAccumulatedInverseCandidateEntry Cell p A P wp W E K T
  candidateEntryExec : GeneratedInteriorIndex A → GeneratedInteriorIndex A → ExecComplex
  candidateMatrixExec : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ExecComplex
  candidateEntryExec_eq : candidateEntryExec = generatedInverseCandidateEntryExecSM3eRq sourceDirichletExec T
  candidateMatrixExec_eq : candidateMatrixExec = generatedInverseCandidateMatrixExecSM3eRq sourceDirichletExec T
  candidateMatrixExec_entry : ∀ i j,
    candidateMatrixExec i j = candidateEntryExec i j
  candidateEntryExec_bridge_to_accumulatedValue : ∀ i j,
    ExecComplexBridge.toComplex (candidateEntryExec i j) =
      ((generatedInteriorAccumulatedEntryValue T i j : ℝ) : ℂ)
  candidateMatrixExec_bridge_to_accumulatedValue : ∀ i j,
    ExecComplexBridge.toComplex (candidateMatrixExec i j) =
      ((generatedInteriorAccumulatedEntryValue T i j : ℝ) : ℂ)
  candidateMatrixExec_bridge_to_handoffCandidate : ∀ i j,
    ExecComplexBridge.toComplex (candidateMatrixExec i j) =
      ((H.candidateMatrix i j : ℝ) : ℂ)
  candidateMatrixExec_bridge_to_matrixExport : ∀ i j,
    ExecComplexBridge.toComplex (candidateMatrixExec i j) =
      ((M.matrix i j : ℝ) : ℂ)
  sourceDirichletReady :
    sourceDirichletExec.nextPhaseStatus =
      SM3bqNextPhaseStatus.sm3eRqGeneratedInverseCandidateExecEntrySource
  sourceHandoffReady : SM3eRMayConsumeOnlySM3dbRInverseCandidate sourceHandoff
  sourceMatrix_eq_handoffMatrix : sourceMatrix = H.sourceMatrix
  sourceAccumulatedEntry_eq_handoffAccumulatedEntry :
    sourceAccumulatedEntry = H.sourceAccumulatedEntry
  sourceMatrix_entry_eq_accumulatedTraceValue : ∀ i j,
    sourceMatrix.matrix i j = generatedInteriorAccumulatedEntryValue T i j
  sourceHandoff_entry_eq_accumulatedTraceValue : ∀ i j,
    sourceHandoff.candidateMatrix i j = generatedInteriorAccumulatedEntryValue T i j
  entrySourceStatus : SM3eRqExecEntrySourceStatus
  entrySourceStatus_eq :
    entrySourceStatus =
      SM3eRqExecEntrySourceStatus.inverseCandidateEntriesFromAccumulatedTraceAndDirichletExecSource
  matrixSourceStatus : SM3eRqExecMatrixSourceStatus
  matrixSourceStatus_eq :
    matrixSourceStatus = SM3eRqExecMatrixSourceStatus.inverseCandidateMatrixExecProjectedEntrywise
  nextPhaseStatus : SM3eRqNextPhaseStatus
  nextPhaseStatus_eq :
    nextPhaseStatus = SM3eRqNextPhaseStatus.sm3fqPlusSchurExecCompletion
  noFreeRationalTableStatus : SM3eRqNoFreeRationalTableStatus
  noFreeRationalTableStatus_eq :
    noFreeRationalTableStatus = SM3eRqNoFreeRationalTableStatus.noFreeRationalTable
  noRealToRatReverseCastStatus : SM3eRqNoRealToRatReverseCastStatus
  noRealToRatReverseCastStatus_eq :
    noRealToRatReverseCastStatus = SM3eRqNoRealToRatReverseCastStatus.noRealToRatReverseCast
  noScalarInverseStatus : SM3eRqNoScalarInverseStatus
  noScalarInverseStatus_eq :
    noScalarInverseStatus = SM3eRqNoScalarInverseStatus.noScalarInverse
  noMatrixInvStatus : SM3eRqNoMatrixInvStatus
  noMatrixInvStatus_eq : noMatrixInvStatus = SM3eRqNoMatrixInvStatus.noMatrixInv
  noProductProofStatus : SM3eRqNoProductProofStatus
  noProductProofStatus_eq :
    noProductProofStatus = SM3eRqNoProductProofStatus.noProductProof
  noTwoSidedInvStatus : SM3eRqNoTwoSidedInvStatus
  noTwoSidedInvStatus_eq :
    noTwoSidedInvStatus = SM3eRqNoTwoSidedInvStatus.noTwoSidedInv
  noInteriorEliminationCertificateStatus : SM3eRqNoInteriorEliminationCertificateStatus
  noInteriorEliminationCertificateStatus_eq :
    noInteriorEliminationCertificateStatus =
      SM3eRqNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificate
  noSchurBoundaryOperatorStatus : SM3eRqNoSchurBoundaryOperatorStatus
  noSchurBoundaryOperatorStatus_eq :
    noSchurBoundaryOperatorStatus = SM3eRqNoSchurBoundaryOperatorStatus.noSchurBoundaryOperator
  noDtnMultiSchurStatus : SM3eRqNoDtnMultiSchurStatus
  noDtnMultiSchurStatus_eq :
    noDtnMultiSchurStatus = SM3eRqNoDtnMultiSchurStatus.noDtnGeneralizedDtnOrMultiSchur
  noCharpolyDiscriminantHeegnerStatus : SM3eRqNoCharpolyDiscriminantHeegnerStatus
  noCharpolyDiscriminantHeegnerStatus_eq :
    noCharpolyDiscriminantHeegnerStatus =
      SM3eRqNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantOrHeegner

namespace GeneratedInverseCandidateExecEntrySourceSM3eRq

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
variable {M : GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T}
variable {S : GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M}
variable {H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S}

def fromHandoff
    (D : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W)
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S) :
    GeneratedInverseCandidateExecEntrySourceSM3eRq Cell p A P wp W E K T M S H where
  sourceDirichletExec := D
  sourceHandoff := H
  sourceMatrix := M
  sourceAccumulatedEntry := H.sourceAccumulatedEntry
  candidateEntryExec := generatedInverseCandidateEntryExecSM3eRq D T
  candidateMatrixExec := generatedInverseCandidateMatrixExecSM3eRq D T
  candidateEntryExec_eq := by
    rfl
  candidateMatrixExec_eq := by
    rfl
  candidateMatrixExec_entry := by
    intro i j
    rfl
  candidateEntryExec_bridge_to_accumulatedValue := by
    intro i j
    exact generatedInverseCandidateEntryExecSM3eRq_bridge D T i j
  candidateMatrixExec_bridge_to_accumulatedValue := by
    intro i j
    exact generatedInverseCandidateMatrixExecSM3eRq_bridge_to_accumulatedValue D T i j
  candidateMatrixExec_bridge_to_handoffCandidate := by
    intro i j
    calc
      ExecComplexBridge.toComplex (generatedInverseCandidateMatrixExecSM3eRq D T i j) =
          ((generatedInteriorAccumulatedEntryValue T i j : ℝ) : ℂ) :=
        generatedInverseCandidateMatrixExecSM3eRq_bridge_to_accumulatedValue D T i j
      _ = ((H.candidateMatrix i j : ℝ) : ℂ) := by
        rw [← H.candidateMatrixEntry_eq_accumulatedTraceValue i j]
  candidateMatrixExec_bridge_to_matrixExport := by
    intro i j
    calc
      ExecComplexBridge.toComplex (generatedInverseCandidateMatrixExecSM3eRq D T i j) =
          ((H.candidateMatrix i j : ℝ) : ℂ) := by
        calc
          ExecComplexBridge.toComplex (generatedInverseCandidateMatrixExecSM3eRq D T i j) =
              ((generatedInteriorAccumulatedEntryValue T i j : ℝ) : ℂ) :=
            generatedInverseCandidateMatrixExecSM3eRq_bridge_to_accumulatedValue D T i j
          _ = ((H.candidateMatrix i j : ℝ) : ℂ) := by
            rw [← H.candidateMatrixEntry_eq_accumulatedTraceValue i j]
      _ = ((M.matrix i j : ℝ) : ℂ) := by
        rw [H.candidateMatrixEntry_eq_SM3db5R_matrixExport i j]
  sourceDirichletReady :=
    D.nextPhaseStatus_eq
  sourceHandoffReady :=
    H.consumptionGateStatus_eq
  sourceMatrix_eq_handoffMatrix := by
    exact H.sourceMatrix_eq_SM3db5R_matrixExport.symm
  sourceAccumulatedEntry_eq_handoffAccumulatedEntry := by
    rfl
  sourceMatrix_entry_eq_accumulatedTraceValue := by
    intro i j
    exact M.matrixEntry_from_accumulatedTraceValue i j
  sourceHandoff_entry_eq_accumulatedTraceValue := by
    intro i j
    exact H.candidateMatrixEntry_eq_accumulatedTraceValue i j
  entrySourceStatus :=
    SM3eRqExecEntrySourceStatus.inverseCandidateEntriesFromAccumulatedTraceAndDirichletExecSource
  entrySourceStatus_eq := by
    rfl
  matrixSourceStatus := SM3eRqExecMatrixSourceStatus.inverseCandidateMatrixExecProjectedEntrywise
  matrixSourceStatus_eq := by
    rfl
  nextPhaseStatus := SM3eRqNextPhaseStatus.sm3fqPlusSchurExecCompletion
  nextPhaseStatus_eq := by
    rfl
  noFreeRationalTableStatus := SM3eRqNoFreeRationalTableStatus.noFreeRationalTable
  noFreeRationalTableStatus_eq := by
    rfl
  noRealToRatReverseCastStatus := SM3eRqNoRealToRatReverseCastStatus.noRealToRatReverseCast
  noRealToRatReverseCastStatus_eq := by
    rfl
  noScalarInverseStatus := SM3eRqNoScalarInverseStatus.noScalarInverse
  noScalarInverseStatus_eq := by
    rfl
  noMatrixInvStatus := SM3eRqNoMatrixInvStatus.noMatrixInv
  noMatrixInvStatus_eq := by
    rfl
  noProductProofStatus := SM3eRqNoProductProofStatus.noProductProof
  noProductProofStatus_eq := by
    rfl
  noTwoSidedInvStatus := SM3eRqNoTwoSidedInvStatus.noTwoSidedInv
  noTwoSidedInvStatus_eq := by
    rfl
  noInteriorEliminationCertificateStatus :=
    SM3eRqNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificate
  noInteriorEliminationCertificateStatus_eq := by
    rfl
  noSchurBoundaryOperatorStatus := SM3eRqNoSchurBoundaryOperatorStatus.noSchurBoundaryOperator
  noSchurBoundaryOperatorStatus_eq := by
    rfl
  noDtnMultiSchurStatus := SM3eRqNoDtnMultiSchurStatus.noDtnGeneralizedDtnOrMultiSchur
  noDtnMultiSchurStatus_eq := by
    rfl
  noCharpolyDiscriminantHeegnerStatus :=
    SM3eRqNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantOrHeegner
  noCharpolyDiscriminantHeegnerStatus_eq := by
    rfl

theorem candidateEntryExec_bridge_to_accumulatedValue_thm
    (X : GeneratedInverseCandidateExecEntrySourceSM3eRq Cell p A P wp W E K T M S H)
    (i j : GeneratedInteriorIndex A) :
    ExecComplexBridge.toComplex (X.candidateEntryExec i j) =
      ((generatedInteriorAccumulatedEntryValue T i j : ℝ) : ℂ) :=
  X.candidateEntryExec_bridge_to_accumulatedValue i j

theorem candidateMatrixExec_bridge_to_handoffCandidate_thm
    (X : GeneratedInverseCandidateExecEntrySourceSM3eRq Cell p A P wp W E K T M S H)
    (i j : GeneratedInteriorIndex A) :
    ExecComplexBridge.toComplex (X.candidateMatrixExec i j) =
      ((H.candidateMatrix i j : ℝ) : ℂ) :=
  X.candidateMatrixExec_bridge_to_handoffCandidate i j

theorem candidateMatrixExec_bridge_to_matrixExport_thm
    (X : GeneratedInverseCandidateExecEntrySourceSM3eRq Cell p A P wp W E K T M S H)
    (i j : GeneratedInteriorIndex A) :
    ExecComplexBridge.toComplex (X.candidateMatrixExec i j) =
      ((M.matrix i j : ℝ) : ℂ) :=
  X.candidateMatrixExec_bridge_to_matrixExport i j

theorem no_real_to_rat_reverse_cast
    (X : GeneratedInverseCandidateExecEntrySourceSM3eRq Cell p A P wp W E K T M S H) :
    X.noRealToRatReverseCastStatus = SM3eRqNoRealToRatReverseCastStatus.noRealToRatReverseCast :=
  X.noRealToRatReverseCastStatus_eq

theorem no_scalar_inverse
    (X : GeneratedInverseCandidateExecEntrySourceSM3eRq Cell p A P wp W E K T M S H) :
    X.noScalarInverseStatus = SM3eRqNoScalarInverseStatus.noScalarInverse :=
  X.noScalarInverseStatus_eq

theorem no_matrix_inv
    (X : GeneratedInverseCandidateExecEntrySourceSM3eRq Cell p A P wp W E K T M S H) :
    X.noMatrixInvStatus = SM3eRqNoMatrixInvStatus.noMatrixInv :=
  X.noMatrixInvStatus_eq

theorem no_product_proof
    (X : GeneratedInverseCandidateExecEntrySourceSM3eRq Cell p A P wp W E K T M S H) :
    X.noProductProofStatus = SM3eRqNoProductProofStatus.noProductProof :=
  X.noProductProofStatus_eq

theorem no_two_sided_inv
    (X : GeneratedInverseCandidateExecEntrySourceSM3eRq Cell p A P wp W E K T M S H) :
    X.noTwoSidedInvStatus = SM3eRqNoTwoSidedInvStatus.noTwoSidedInv :=
  X.noTwoSidedInvStatus_eq

theorem no_interior_elimination_certificate
    (X : GeneratedInverseCandidateExecEntrySourceSM3eRq Cell p A P wp W E K T M S H) :
    X.noInteriorEliminationCertificateStatus =
      SM3eRqNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificate :=
  X.noInteriorEliminationCertificateStatus_eq

theorem no_schur_boundary_operator
    (X : GeneratedInverseCandidateExecEntrySourceSM3eRq Cell p A P wp W E K T M S H) :
    X.noSchurBoundaryOperatorStatus = SM3eRqNoSchurBoundaryOperatorStatus.noSchurBoundaryOperator :=
  X.noSchurBoundaryOperatorStatus_eq

theorem no_dtn_multi_schur
    (X : GeneratedInverseCandidateExecEntrySourceSM3eRq Cell p A P wp W E K T M S H) :
    X.noDtnMultiSchurStatus = SM3eRqNoDtnMultiSchurStatus.noDtnGeneralizedDtnOrMultiSchur :=
  X.noDtnMultiSchurStatus_eq

theorem no_charpoly_discriminant_heegner
    (X : GeneratedInverseCandidateExecEntrySourceSM3eRq Cell p A P wp W E K T M S H) :
    X.noCharpolyDiscriminantHeegnerStatus =
      SM3eRqNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantOrHeegner :=
  X.noCharpolyDiscriminantHeegnerStatus_eq

theorem next_phase_is_SM3fqPlus
    (X : GeneratedInverseCandidateExecEntrySourceSM3eRq Cell p A P wp W E K T M S H) :
    X.nextPhaseStatus = SM3eRqNextPhaseStatus.sm3fqPlusSchurExecCompletion :=
  X.nextPhaseStatus_eq

end GeneratedInverseCandidateExecEntrySourceSM3eRq

def regularGeneratedInverseCandidateExecEntrySourceSM3eRq
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedInverseCandidateExecEntrySourceSM3eRq
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) wp
      (regularGeneratedWeightPolicyEntrySource b p wp)
      (regularGeneratedInteriorEliminationCandidateEntry b p wp)
      (regularGeneratedInteriorEliminationCarrier b p wp)
      (regularGeneratedInteriorEliminationTrace b p wp)
      (regularGeneratedInteriorInverseCandidateMatrix b p wp)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p wp)
      (regularSM3dbRToSM3eRHandoff b p wp) :=
  GeneratedInverseCandidateExecEntrySourceSM3eRq.fromHandoff
    (regularGeneratedDirichletExecEntrySourceSM3bq b p wp)
    (regularSM3dbRToSM3eRHandoff b p wp)

def variableGeneratedInverseCandidateExecEntrySourceSM3eRq
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedInverseCandidateExecEntrySourceSM3eRq
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) wp
      (variableGeneratedWeightPolicyEntrySource β p wp)
      (variableGeneratedInteriorEliminationCandidateEntry β p wp)
      (variableGeneratedInteriorEliminationCarrier β p wp)
      (variableGeneratedInteriorEliminationTrace β p wp)
      (variableGeneratedInteriorInverseCandidateMatrix β p wp)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p wp)
      (variableSM3dbRToSM3eRHandoff β p wp) :=
  GeneratedInverseCandidateExecEntrySourceSM3eRq.fromHandoff
    (variableGeneratedDirichletExecEntrySourceSM3bq β p wp)
    (variableSM3dbRToSM3eRHandoff β p wp)

structure SM3eRqGeneratedInverseCandidateExecEntrySourceLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) where
  status : SM3eRqGeneratedInverseCandidateExecEntrySourceLedgerStatus
  dirichletExecLedger :
    SM3bqGeneratedDirichletExecEntrySourceLedger b β p regularWeight variableWeight
  inverseHandoffLedger :
    SM3dbRGeneratedInverseCandidateLedger
      b β p regularWeight variableWeight regularPivot variablePivot
  regularExecSource :
    GeneratedInverseCandidateExecEntrySourceSM3eRq
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
  variableExecSource :
    GeneratedInverseCandidateExecEntrySourceSM3eRq
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
  dirichletExecLedger_eq_main :
    dirichletExecLedger = sm3bqGeneratedDirichletExecEntrySourceLedger b β p regularWeight variableWeight
  inverseHandoffLedger_eq_main :
    inverseHandoffLedger =
      sm3dbRGeneratedInverseCandidateLedger
        b β p regularWeight variableWeight regularPivot variablePivot
  regularExecSource_eq_main :
    regularExecSource = regularGeneratedInverseCandidateExecEntrySourceSM3eRq b p regularWeight
  variableExecSource_eq_main :
    variableExecSource = variableGeneratedInverseCandidateExecEntrySourceSM3eRq β p variableWeight
  regularBridgeToAccumulated : ∀ i j,
    ExecComplexBridge.toComplex (regularExecSource.candidateMatrixExec i j) =
      ((generatedInteriorAccumulatedEntryValue
        (regularGeneratedInteriorEliminationTrace b p regularWeight) i j : ℝ) : ℂ)
  variableBridgeToAccumulated : ∀ i j,
    ExecComplexBridge.toComplex (variableExecSource.candidateMatrixExec i j) =
      ((generatedInteriorAccumulatedEntryValue
        (variableGeneratedInteriorEliminationTrace β p variableWeight) i j : ℝ) : ℂ)
  regularBridgeToHandoffCandidate : ∀ i j,
    ExecComplexBridge.toComplex (regularExecSource.candidateMatrixExec i j) =
      (((regularSM3dbRToSM3eRHandoff b p regularWeight).candidateMatrix i j : ℝ) : ℂ)
  variableBridgeToHandoffCandidate : ∀ i j,
    ExecComplexBridge.toComplex (variableExecSource.candidateMatrixExec i j) =
      (((variableSM3dbRToSM3eRHandoff β p variableWeight).candidateMatrix i j : ℝ) : ℂ)
  regularNoFreeRationalTable :
    regularExecSource.noFreeRationalTableStatus = SM3eRqNoFreeRationalTableStatus.noFreeRationalTable
  variableNoFreeRationalTable :
    variableExecSource.noFreeRationalTableStatus = SM3eRqNoFreeRationalTableStatus.noFreeRationalTable
  regularNoRealToRatReverseCast :
    regularExecSource.noRealToRatReverseCastStatus = SM3eRqNoRealToRatReverseCastStatus.noRealToRatReverseCast
  variableNoRealToRatReverseCast :
    variableExecSource.noRealToRatReverseCastStatus = SM3eRqNoRealToRatReverseCastStatus.noRealToRatReverseCast
  regularNoScalarInverse :
    regularExecSource.noScalarInverseStatus = SM3eRqNoScalarInverseStatus.noScalarInverse
  variableNoScalarInverse :
    variableExecSource.noScalarInverseStatus = SM3eRqNoScalarInverseStatus.noScalarInverse
  regularNoMatrixInv :
    regularExecSource.noMatrixInvStatus = SM3eRqNoMatrixInvStatus.noMatrixInv
  variableNoMatrixInv :
    variableExecSource.noMatrixInvStatus = SM3eRqNoMatrixInvStatus.noMatrixInv
  regularNoProductProof :
    regularExecSource.noProductProofStatus = SM3eRqNoProductProofStatus.noProductProof
  variableNoProductProof :
    variableExecSource.noProductProofStatus = SM3eRqNoProductProofStatus.noProductProof
  regularNoTwoSidedInv :
    regularExecSource.noTwoSidedInvStatus = SM3eRqNoTwoSidedInvStatus.noTwoSidedInv
  variableNoTwoSidedInv :
    variableExecSource.noTwoSidedInvStatus = SM3eRqNoTwoSidedInvStatus.noTwoSidedInv
  regularNoInteriorEliminationCertificate :
    regularExecSource.noInteriorEliminationCertificateStatus =
      SM3eRqNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificate
  variableNoInteriorEliminationCertificate :
    variableExecSource.noInteriorEliminationCertificateStatus =
      SM3eRqNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificate
  regularNoSchurBoundaryOperator :
    regularExecSource.noSchurBoundaryOperatorStatus =
      SM3eRqNoSchurBoundaryOperatorStatus.noSchurBoundaryOperator
  variableNoSchurBoundaryOperator :
    variableExecSource.noSchurBoundaryOperatorStatus =
      SM3eRqNoSchurBoundaryOperatorStatus.noSchurBoundaryOperator
  regularNoDtnMultiSchur :
    regularExecSource.noDtnMultiSchurStatus =
      SM3eRqNoDtnMultiSchurStatus.noDtnGeneralizedDtnOrMultiSchur
  variableNoDtnMultiSchur :
    variableExecSource.noDtnMultiSchurStatus =
      SM3eRqNoDtnMultiSchurStatus.noDtnGeneralizedDtnOrMultiSchur
  regularNoCharpolyDiscriminantHeegner :
    regularExecSource.noCharpolyDiscriminantHeegnerStatus =
      SM3eRqNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantOrHeegner
  variableNoCharpolyDiscriminantHeegner :
    variableExecSource.noCharpolyDiscriminantHeegnerStatus =
      SM3eRqNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantOrHeegner
  regularNextPhase :
    regularExecSource.nextPhaseStatus = SM3eRqNextPhaseStatus.sm3fqPlusSchurExecCompletion
  variableNextPhase :
    variableExecSource.nextPhaseStatus = SM3eRqNextPhaseStatus.sm3fqPlusSchurExecCompletion
  status_eq_closed :
    status =
      SM3eRqGeneratedInverseCandidateExecEntrySourceLedgerStatus.generatedInverseCandidateExecEntrySourceClosed

def sm3eRqGeneratedInverseCandidateExecEntrySourceLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) :
    SM3eRqGeneratedInverseCandidateExecEntrySourceLedger
      b β p regularWeight variableWeight regularPivot variablePivot where
  status :=
    SM3eRqGeneratedInverseCandidateExecEntrySourceLedgerStatus.generatedInverseCandidateExecEntrySourceClosed
  dirichletExecLedger :=
    sm3bqGeneratedDirichletExecEntrySourceLedger b β p regularWeight variableWeight
  inverseHandoffLedger :=
    sm3dbRGeneratedInverseCandidateLedger
      b β p regularWeight variableWeight regularPivot variablePivot
  regularExecSource := regularGeneratedInverseCandidateExecEntrySourceSM3eRq b p regularWeight
  variableExecSource := variableGeneratedInverseCandidateExecEntrySourceSM3eRq β p variableWeight
  dirichletExecLedger_eq_main := by
    rfl
  inverseHandoffLedger_eq_main := by
    rfl
  regularExecSource_eq_main := by
    rfl
  variableExecSource_eq_main := by
    rfl
  regularBridgeToAccumulated := by
    intro i j
    exact
      (regularGeneratedInverseCandidateExecEntrySourceSM3eRq b p regularWeight).candidateMatrixExec_bridge_to_accumulatedValue i j
  variableBridgeToAccumulated := by
    intro i j
    exact
      (variableGeneratedInverseCandidateExecEntrySourceSM3eRq β p variableWeight).candidateMatrixExec_bridge_to_accumulatedValue i j
  regularBridgeToHandoffCandidate := by
    intro i j
    exact
      (regularGeneratedInverseCandidateExecEntrySourceSM3eRq b p regularWeight).candidateMatrixExec_bridge_to_handoffCandidate i j
  variableBridgeToHandoffCandidate := by
    intro i j
    exact
      (variableGeneratedInverseCandidateExecEntrySourceSM3eRq β p variableWeight).candidateMatrixExec_bridge_to_handoffCandidate i j
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
  regularNoProductProof := by
    rfl
  variableNoProductProof := by
    rfl
  regularNoTwoSidedInv := by
    rfl
  variableNoTwoSidedInv := by
    rfl
  regularNoInteriorEliminationCertificate := by
    rfl
  variableNoInteriorEliminationCertificate := by
    rfl
  regularNoSchurBoundaryOperator := by
    rfl
  variableNoSchurBoundaryOperator := by
    rfl
  regularNoDtnMultiSchur := by
    rfl
  variableNoDtnMultiSchur := by
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

theorem sm3eRqGeneratedInverseCandidateExecEntrySourceLedger_status
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) :
    (sm3eRqGeneratedInverseCandidateExecEntrySourceLedger
      b β p regularWeight variableWeight regularPivot variablePivot).status =
      SM3eRqGeneratedInverseCandidateExecEntrySourceLedgerStatus.generatedInverseCandidateExecEntrySourceClosed := by
  rfl

theorem sm3eRqGeneratedInverseCandidateExecEntrySourceLedger_regularNextPhase
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) :
    (sm3eRqGeneratedInverseCandidateExecEntrySourceLedger
      b β p regularWeight variableWeight regularPivot variablePivot).regularExecSource.nextPhaseStatus =
      SM3eRqNextPhaseStatus.sm3fqPlusSchurExecCompletion := by
  rfl

theorem sm3eRqGeneratedInverseCandidateExecEntrySourceLedger_variableNextPhase
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy)
    (regularPivot : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p))
    (variablePivot : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p)) :
    (sm3eRqGeneratedInverseCandidateExecEntrySourceLedger
      b β p regularWeight variableWeight regularPivot variablePivot).variableExecSource.nextPhaseStatus =
      SM3eRqNextPhaseStatus.sm3fqPlusSchurExecCompletion := by
  rfl

end Smoke

end CNNA.PillarA.Arithmetic
