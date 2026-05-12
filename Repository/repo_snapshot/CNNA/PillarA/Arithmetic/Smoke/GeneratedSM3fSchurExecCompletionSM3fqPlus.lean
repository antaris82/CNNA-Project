import CNNA.PillarA.Arithmetic.Smoke.GeneratedSM3fSchurExecEntrySourceSM3fq
import CNNA.PillarA.Arithmetic.Smoke.GeneratedInverseCandidateExecEntrySourceSM3eRq

set_option autoImplicit false
open scoped BigOperators

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.DtN

namespace Smoke

universe u

inductive SM3fqPlusCompletionStatus where
  | boundarySchurExecCompletedFromSM3bqAndSM3eRq
  deriving DecidableEq, Repr

inductive SM3fqPlusNextPhaseStatus where
  | sm4qMayRecheckBoundarySchurExecSource
  deriving DecidableEq, Repr

inductive SM3fqPlusNoFreeExecMatrixStatus where
  | noFreeExecMatrix
  deriving DecidableEq, Repr

inductive SM3fqPlusNoRealToRatReverseCastStatus where
  | noRealToRatReverseCast
  deriving DecidableEq, Repr

inductive SM3fqPlusNoScalarInverseStatus where
  | noScalarInverse
  deriving DecidableEq, Repr

inductive SM3fqPlusNoMatrixInvStatus where
  | noMatrixInv
  deriving DecidableEq, Repr

inductive SM3fqPlusNoNewInverseOracleStatus where
  | noNewInverseOracle
  deriving DecidableEq, Repr

inductive SM3fqPlusNoProductIdentityProofStatus where
  | noProductIdentityProof
  deriving DecidableEq, Repr

inductive SM3fqPlusNoTwoSidedInvStatus where
  | noTwoSidedInv
  deriving DecidableEq, Repr

inductive SM3fqPlusNoNewInteriorEliminationCertificateStatus where
  | noNewInteriorEliminationCertificate
  deriving DecidableEq, Repr

inductive SM3fqPlusNoDtnMultiSchurConsumerStatus where
  | noDtnGeneralizedDtnOrMultiSchurConsumer
  deriving DecidableEq, Repr

inductive SM3fqPlusNoCharpolyDiscriminantHeegnerStatus where
  | noCharpolyDiscriminantOrHeegner
  deriving DecidableEq, Repr

def generatedBoundaryBlockExecSM3fqPlus
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    (D : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W) :
    Matrix (GeneratedBoundaryIndex A) (GeneratedBoundaryIndex A) ExecComplex :=
  fun i j =>
    D.dirichletMatrixExec
      (GeneratedBoundaryIndex.toApproximantIndex i)
      (GeneratedBoundaryIndex.toApproximantIndex j)

theorem generatedBoundaryBlockExecSM3fqPlus_bridge
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    (D : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W)
    (i j : GeneratedBoundaryIndex A) :
    ExecComplexBridge.toComplex (generatedBoundaryBlockExecSM3fqPlus D i j) =
      ((generatedBoundaryBlockSM3fR W i j : ℝ) : ℂ) := by
  calc
    ExecComplexBridge.toComplex (generatedBoundaryBlockExecSM3fqPlus D i j) =
        ((generatedDirichletMatrix D.sourceWeight
          (GeneratedBoundaryIndex.toApproximantIndex i)
          (GeneratedBoundaryIndex.toApproximantIndex j) : ℝ) : ℂ) := by
      exact D.dirichletMatrixExec_bridge
        (GeneratedBoundaryIndex.toApproximantIndex i)
        (GeneratedBoundaryIndex.toApproximantIndex j)
    _ = ((generatedDirichletMatrix W
          (GeneratedBoundaryIndex.toApproximantIndex i)
          (GeneratedBoundaryIndex.toApproximantIndex j) : ℝ) : ℂ) := by
      rw [D.sourceWeight_eq]
    _ = ((generatedBoundaryBlockSM3fR W i j : ℝ) : ℂ) := by
      rfl

def generatedBoundaryInteriorBlockExecSM3fqPlus
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    (D : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W) :
    Matrix (GeneratedBoundaryIndex A) (GeneratedInteriorIndex A) ExecComplex :=
  fun i j =>
    D.dirichletMatrixExec
      (GeneratedBoundaryIndex.toApproximantIndex i)
      (GeneratedInteriorIndex.toApproximantIndex j)

theorem generatedBoundaryInteriorBlockExecSM3fqPlus_bridge
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    (D : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W)
    (i : GeneratedBoundaryIndex A) (j : GeneratedInteriorIndex A) :
    ExecComplexBridge.toComplex (generatedBoundaryInteriorBlockExecSM3fqPlus D i j) =
      ((generatedBoundaryInteriorBlockSM3fR W i j : ℝ) : ℂ) := by
  calc
    ExecComplexBridge.toComplex (generatedBoundaryInteriorBlockExecSM3fqPlus D i j) =
        ((generatedDirichletMatrix D.sourceWeight
          (GeneratedBoundaryIndex.toApproximantIndex i)
          (GeneratedInteriorIndex.toApproximantIndex j) : ℝ) : ℂ) := by
      exact D.dirichletMatrixExec_bridge
        (GeneratedBoundaryIndex.toApproximantIndex i)
        (GeneratedInteriorIndex.toApproximantIndex j)
    _ = ((generatedDirichletMatrix W
          (GeneratedBoundaryIndex.toApproximantIndex i)
          (GeneratedInteriorIndex.toApproximantIndex j) : ℝ) : ℂ) := by
      rw [D.sourceWeight_eq]
    _ = ((generatedBoundaryInteriorBlockSM3fR W i j : ℝ) : ℂ) := by
      rfl

def generatedInteriorBoundaryBlockExecSM3fqPlus
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    (D : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W) :
    Matrix (GeneratedInteriorIndex A) (GeneratedBoundaryIndex A) ExecComplex :=
  fun i j =>
    D.dirichletMatrixExec
      (GeneratedInteriorIndex.toApproximantIndex i)
      (GeneratedBoundaryIndex.toApproximantIndex j)

theorem generatedInteriorBoundaryBlockExecSM3fqPlus_bridge
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    (D : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W)
    (i : GeneratedInteriorIndex A) (j : GeneratedBoundaryIndex A) :
    ExecComplexBridge.toComplex (generatedInteriorBoundaryBlockExecSM3fqPlus D i j) =
      ((generatedInteriorBoundaryBlockSM3fR W i j : ℝ) : ℂ) := by
  calc
    ExecComplexBridge.toComplex (generatedInteriorBoundaryBlockExecSM3fqPlus D i j) =
        ((generatedDirichletMatrix D.sourceWeight
          (GeneratedInteriorIndex.toApproximantIndex i)
          (GeneratedBoundaryIndex.toApproximantIndex j) : ℝ) : ℂ) := by
      exact D.dirichletMatrixExec_bridge
        (GeneratedInteriorIndex.toApproximantIndex i)
        (GeneratedBoundaryIndex.toApproximantIndex j)
    _ = ((generatedDirichletMatrix W
          (GeneratedInteriorIndex.toApproximantIndex i)
          (GeneratedBoundaryIndex.toApproximantIndex j) : ℝ) : ℂ) := by
      rw [D.sourceWeight_eq]
    _ = ((generatedInteriorBoundaryBlockSM3fR W i j : ℝ) : ℂ) := by
      rfl

def generatedInverseMatrixExecSM3fqPlus
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
    {M : GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T}
    {S : GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M}
    {H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S}
    (X : GeneratedInverseCandidateExecEntrySourceSM3eRq Cell p A P wp W E K T M S H) :
    Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ExecComplex :=
  X.candidateMatrixExec

theorem generatedInverseMatrixExecSM3fqPlus_bridge
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
    {M : GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T}
    {S : GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M}
    {H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S}
    (X : GeneratedInverseCandidateExecEntrySourceSM3eRq Cell p A P wp W E K T M S H)
    (i j : GeneratedInteriorIndex A) :
    ExecComplexBridge.toComplex (generatedInverseMatrixExecSM3fqPlus X i j) =
      ((H.candidateMatrix i j : ℝ) : ℂ) := by
  exact X.candidateMatrixExec_bridge_to_handoffCandidate i j

def generatedSM3fqPlusSchurCorrectionExec
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
    {M : GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T}
    {S : GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M}
    {H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S}
    (D : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W)
    (X : GeneratedInverseCandidateExecEntrySourceSM3eRq Cell p A P wp W E K T M S H) :
    Matrix (GeneratedBoundaryIndex A) (GeneratedBoundaryIndex A) ExecComplex :=
  generatedBoundaryInteriorBlockExecSM3fqPlus D *
    generatedInverseMatrixExecSM3fqPlus X *
      generatedInteriorBoundaryBlockExecSM3fqPlus D

theorem generatedBoundaryInteriorTimesInverseExecSM3fqPlus_bridge
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
    {M : GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T}
    {S : GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M}
    {H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S}
    (D : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W)
    (X : GeneratedInverseCandidateExecEntrySourceSM3eRq Cell p A P wp W E K T M S H)
    (i : GeneratedBoundaryIndex A) (j : GeneratedInteriorIndex A) :
    ExecComplexBridge.toComplex
      ((generatedBoundaryInteriorBlockExecSM3fqPlus D * generatedInverseMatrixExecSM3fqPlus X) i j) =
      (((generatedBoundaryInteriorBlockSM3fR W * H.candidateMatrix) i j : ℝ) : ℂ) := by
  rw [Matrix.mul_apply]
  rw [ExecComplexBridge.toComplex_sum]
  calc
    (∑ k : GeneratedInteriorIndex A,
        ExecComplexBridge.toComplex
          (generatedBoundaryInteriorBlockExecSM3fqPlus D i k *
            generatedInverseMatrixExecSM3fqPlus X k j)) =
        ∑ k : GeneratedInteriorIndex A,
          ExecComplexBridge.toComplex (generatedBoundaryInteriorBlockExecSM3fqPlus D i k) *
            ExecComplexBridge.toComplex (generatedInverseMatrixExecSM3fqPlus X k j) := by
      refine Finset.sum_congr rfl ?_
      intro k _hk
      rw [ExecComplexBridge.toComplex_mul]
    _ = ∑ k : GeneratedInteriorIndex A,
          ((generatedBoundaryInteriorBlockSM3fR W i k : ℝ) : ℂ) *
            ((H.candidateMatrix k j : ℝ) : ℂ) := by
      refine Finset.sum_congr rfl ?_
      intro k _hk
      rw [generatedBoundaryInteriorBlockExecSM3fqPlus_bridge D i k]
      rw [generatedInverseMatrixExecSM3fqPlus_bridge X k j]
    _ = (((generatedBoundaryInteriorBlockSM3fR W * H.candidateMatrix) i j : ℝ) : ℂ) := by
      simp [Matrix.mul_apply]

theorem generatedSM3fqPlusSchurCorrectionExec_bridge
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
    {M : GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T}
    {S : GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M}
    {H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S}
    (D : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W)
    (X : GeneratedInverseCandidateExecEntrySourceSM3eRq Cell p A P wp W E K T M S H)
    (i j : GeneratedBoundaryIndex A) :
    ExecComplexBridge.toComplex (generatedSM3fqPlusSchurCorrectionExec D X i j) =
      (((generatedBoundaryInteriorBlockSM3fR W * H.candidateMatrix *
          generatedInteriorBoundaryBlockSM3fR W) i j : ℝ) : ℂ) := by
  unfold generatedSM3fqPlusSchurCorrectionExec
  rw [Matrix.mul_apply]
  rw [ExecComplexBridge.toComplex_sum]
  calc
    (∑ k : GeneratedInteriorIndex A,
        ExecComplexBridge.toComplex
          (((generatedBoundaryInteriorBlockExecSM3fqPlus D * generatedInverseMatrixExecSM3fqPlus X) i k) *
            generatedInteriorBoundaryBlockExecSM3fqPlus D k j)) =
        ∑ k : GeneratedInteriorIndex A,
          ExecComplexBridge.toComplex
            ((generatedBoundaryInteriorBlockExecSM3fqPlus D * generatedInverseMatrixExecSM3fqPlus X) i k) *
            ExecComplexBridge.toComplex (generatedInteriorBoundaryBlockExecSM3fqPlus D k j) := by
      refine Finset.sum_congr rfl ?_
      intro k _hk
      rw [ExecComplexBridge.toComplex_mul]
    _ = ∑ k : GeneratedInteriorIndex A,
          (((generatedBoundaryInteriorBlockSM3fR W * H.candidateMatrix) i k : ℝ) : ℂ) *
            ((generatedInteriorBoundaryBlockSM3fR W k j : ℝ) : ℂ) := by
      refine Finset.sum_congr rfl ?_
      intro k _hk
      rw [generatedBoundaryInteriorTimesInverseExecSM3fqPlus_bridge D X i k]
      rw [generatedInteriorBoundaryBlockExecSM3fqPlus_bridge D k j]
    _ = (((generatedBoundaryInteriorBlockSM3fR W * H.candidateMatrix *
          generatedInteriorBoundaryBlockSM3fR W) i j : ℝ) : ℂ) := by
      simp [Matrix.mul_apply]

def generatedSM3fqPlusBoundaryOperatorExec
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
    {M : GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T}
    {S : GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M}
    {H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S}
    (D : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W)
    (X : GeneratedInverseCandidateExecEntrySourceSM3eRq Cell p A P wp W E K T M S H) :
    Matrix (GeneratedBoundaryIndex A) (GeneratedBoundaryIndex A) ExecComplex :=
  generatedBoundaryBlockExecSM3fqPlus D - generatedSM3fqPlusSchurCorrectionExec D X

theorem generatedSM3fqPlusBoundaryOperatorExec_bridge_to_handoffSchur
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
    {M : GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T}
    {S : GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M}
    {H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S}
    (D : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W)
    (X : GeneratedInverseCandidateExecEntrySourceSM3eRq Cell p A P wp W E K T M S H)
    (i j : GeneratedBoundaryIndex A) :
    ExecComplexBridge.toComplex (generatedSM3fqPlusBoundaryOperatorExec D X i j) =
      (((generatedBoundaryBlockSM3fR W -
          generatedBoundaryInteriorBlockSM3fR W * H.candidateMatrix *
            generatedInteriorBoundaryBlockSM3fR W) i j : ℝ) : ℂ) := by
  unfold generatedSM3fqPlusBoundaryOperatorExec
  change ExecComplexBridge.toComplex
      (generatedBoundaryBlockExecSM3fqPlus D i j -
        generatedSM3fqPlusSchurCorrectionExec D X i j) =
      (((generatedBoundaryBlockSM3fR W -
          generatedBoundaryInteriorBlockSM3fR W * H.candidateMatrix *
            generatedInteriorBoundaryBlockSM3fR W) i j : ℝ) : ℂ)
  rw [ExecComplexBridge.toComplex_sub]
  rw [generatedBoundaryBlockExecSM3fqPlus_bridge D i j]
  rw [generatedSM3fqPlusSchurCorrectionExec_bridge D X i j]
  simp

theorem sourceSM3fq_boundaryOperatorReal_eq_handoffSchurSM3fqPlus
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedBoundaryIndex A)]
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
    {K : GeneratedInteriorEliminationCarrier Cell p A P wp W E}
    {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}
    {M : GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T}
    {S : GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M}
    {H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S}
    (Q : GeneratedSM3fSchurExecEntrySourceSM3fq Cell p A P wp W E K T M S H) :
    Q.boundaryOperatorReal =
      generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W * H.candidateMatrix *
          generatedInteriorBoundaryBlockSM3fR W := by
  calc
    Q.boundaryOperatorReal =
        generatedBoundaryBlockSM3fR W -
          generatedBoundaryInteriorBlockSM3fR W * Q.inverseMatrixReal *
            generatedInteriorBoundaryBlockSM3fR W :=
      Q.boundaryOperatorReal_eq_schur
    _ = generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W * H.candidateMatrix *
          generatedInteriorBoundaryBlockSM3fR W := by
      rw [Q.inverseMatrixReal_eq_handoffCandidate]

theorem generatedSM3fqPlusBoundaryOperatorExec_bridge_to_SM3fSchur
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedBoundaryIndex A)]
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
    {K : GeneratedInteriorEliminationCarrier Cell p A P wp W E}
    {T : GeneratedInteriorEliminationTrace Cell p A P wp W E K}
    {M : GeneratedInteriorInverseCandidateMatrix Cell p A P wp W E K T}
    {S : GeneratedInteriorInverseCandidateShapeSeparation Cell p A P wp W E K T M}
    {H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S}
    (Q : GeneratedSM3fSchurExecEntrySourceSM3fq Cell p A P wp W E K T M S H)
    (D : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W)
    (X : GeneratedInverseCandidateExecEntrySourceSM3eRq Cell p A P wp W E K T M S H)
    (i j : GeneratedBoundaryIndex A) :
    ExecComplexBridge.toComplex (generatedSM3fqPlusBoundaryOperatorExec D X i j) =
      ((Q.boundaryOperatorReal i j : ℝ) : ℂ) := by
  calc
    ExecComplexBridge.toComplex (generatedSM3fqPlusBoundaryOperatorExec D X i j) =
        (((generatedBoundaryBlockSM3fR W -
          generatedBoundaryInteriorBlockSM3fR W * H.candidateMatrix *
            generatedInteriorBoundaryBlockSM3fR W) i j : ℝ) : ℂ) :=
      generatedSM3fqPlusBoundaryOperatorExec_bridge_to_handoffSchur D X i j
    _ = ((Q.boundaryOperatorReal i j : ℝ) : ℂ) := by
      rw [sourceSM3fq_boundaryOperatorReal_eq_handoffSchurSM3fqPlus Q]

structure GeneratedSM3fSchurExecCompletionSM3fqPlus
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf)
    (A : GeneratedApproximantStrong Cell p)
    [Fintype (GeneratedBoundaryIndex A)]
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
  sourceSM3fq : GeneratedSM3fSchurExecEntrySourceSM3fq Cell p A P wp W E K T M S H
  sourceDirichletExec : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W
  sourceInverseExec : GeneratedInverseCandidateExecEntrySourceSM3eRq Cell p A P wp W E K T M S H
  boundaryBlockExec : Matrix (GeneratedBoundaryIndex A) (GeneratedBoundaryIndex A) ExecComplex
  boundaryBlockExec_eq : boundaryBlockExec = generatedBoundaryBlockExecSM3fqPlus sourceDirichletExec
  boundaryBlockExec_bridge : ∀ i j,
    ExecComplexBridge.toComplex (boundaryBlockExec i j) =
      ((generatedBoundaryBlockSM3fR W i j : ℝ) : ℂ)
  boundaryInteriorBlockExec : Matrix (GeneratedBoundaryIndex A) (GeneratedInteriorIndex A) ExecComplex
  boundaryInteriorBlockExec_eq :
    boundaryInteriorBlockExec = generatedBoundaryInteriorBlockExecSM3fqPlus sourceDirichletExec
  boundaryInteriorBlockExec_bridge : ∀ i j,
    ExecComplexBridge.toComplex (boundaryInteriorBlockExec i j) =
      ((generatedBoundaryInteriorBlockSM3fR W i j : ℝ) : ℂ)
  interiorBoundaryBlockExec : Matrix (GeneratedInteriorIndex A) (GeneratedBoundaryIndex A) ExecComplex
  interiorBoundaryBlockExec_eq :
    interiorBoundaryBlockExec = generatedInteriorBoundaryBlockExecSM3fqPlus sourceDirichletExec
  interiorBoundaryBlockExec_bridge : ∀ i j,
    ExecComplexBridge.toComplex (interiorBoundaryBlockExec i j) =
      ((generatedInteriorBoundaryBlockSM3fR W i j : ℝ) : ℂ)
  inverseMatrixExec : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ExecComplex
  inverseMatrixExec_eq : inverseMatrixExec = generatedInverseMatrixExecSM3fqPlus sourceInverseExec
  inverseMatrixExec_bridge : ∀ i j,
    ExecComplexBridge.toComplex (inverseMatrixExec i j) =
      ((H.candidateMatrix i j : ℝ) : ℂ)
  schurCorrectionExec : Matrix (GeneratedBoundaryIndex A) (GeneratedBoundaryIndex A) ExecComplex
  schurCorrectionExec_eq :
    schurCorrectionExec = generatedSM3fqPlusSchurCorrectionExec sourceDirichletExec sourceInverseExec
  schurCorrectionExec_bridge : ∀ i j,
    ExecComplexBridge.toComplex (schurCorrectionExec i j) =
      (((generatedBoundaryInteriorBlockSM3fR W * H.candidateMatrix *
          generatedInteriorBoundaryBlockSM3fR W) i j : ℝ) : ℂ)
  boundaryOperatorExec : Matrix (GeneratedBoundaryIndex A) (GeneratedBoundaryIndex A) ExecComplex
  boundaryOperatorExec_eq :
    boundaryOperatorExec = generatedSM3fqPlusBoundaryOperatorExec sourceDirichletExec sourceInverseExec
  boundaryOperatorExec_bridge_to_handoffSchur : ∀ i j,
    ExecComplexBridge.toComplex (boundaryOperatorExec i j) =
      (((generatedBoundaryBlockSM3fR W -
          generatedBoundaryInteriorBlockSM3fR W * H.candidateMatrix *
            generatedInteriorBoundaryBlockSM3fR W) i j : ℝ) : ℂ)
  boundaryOperatorExec_bridge_to_SM3fSchur : ∀ i j,
    ExecComplexBridge.toComplex (boundaryOperatorExec i j) =
      ((sourceSM3fq.boundaryOperatorReal i j : ℝ) : ℂ)
  sourceSM3fqBoundaryOperatorReal_eq_handoffSchur :
    sourceSM3fq.boundaryOperatorReal =
      generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W * H.candidateMatrix *
          generatedInteriorBoundaryBlockSM3fR W
  sourceDirichletReady :
    sourceDirichletExec.nextPhaseStatus = SM3bqNextPhaseStatus.sm3eRqGeneratedInverseCandidateExecEntrySource
  sourceInverseReady :
    sourceInverseExec.nextPhaseStatus = SM3eRqNextPhaseStatus.sm3fqPlusSchurExecCompletion
  completionStatus : SM3fqPlusCompletionStatus
  completionStatus_eq :
    completionStatus = SM3fqPlusCompletionStatus.boundarySchurExecCompletedFromSM3bqAndSM3eRq
  nextPhaseStatus : SM3fqPlusNextPhaseStatus
  nextPhaseStatus_eq : nextPhaseStatus = SM3fqPlusNextPhaseStatus.sm4qMayRecheckBoundarySchurExecSource
  noFreeExecMatrixStatus : SM3fqPlusNoFreeExecMatrixStatus
  noFreeExecMatrixStatus_eq : noFreeExecMatrixStatus = SM3fqPlusNoFreeExecMatrixStatus.noFreeExecMatrix
  noRealToRatReverseCastStatus : SM3fqPlusNoRealToRatReverseCastStatus
  noRealToRatReverseCastStatus_eq :
    noRealToRatReverseCastStatus = SM3fqPlusNoRealToRatReverseCastStatus.noRealToRatReverseCast
  noScalarInverseStatus : SM3fqPlusNoScalarInverseStatus
  noScalarInverseStatus_eq : noScalarInverseStatus = SM3fqPlusNoScalarInverseStatus.noScalarInverse
  noMatrixInvStatus : SM3fqPlusNoMatrixInvStatus
  noMatrixInvStatus_eq : noMatrixInvStatus = SM3fqPlusNoMatrixInvStatus.noMatrixInv
  noNewInverseOracleStatus : SM3fqPlusNoNewInverseOracleStatus
  noNewInverseOracleStatus_eq :
    noNewInverseOracleStatus = SM3fqPlusNoNewInverseOracleStatus.noNewInverseOracle
  noProductIdentityProofStatus : SM3fqPlusNoProductIdentityProofStatus
  noProductIdentityProofStatus_eq :
    noProductIdentityProofStatus = SM3fqPlusNoProductIdentityProofStatus.noProductIdentityProof
  noTwoSidedInvStatus : SM3fqPlusNoTwoSidedInvStatus
  noTwoSidedInvStatus_eq : noTwoSidedInvStatus = SM3fqPlusNoTwoSidedInvStatus.noTwoSidedInv
  noNewInteriorEliminationCertificateStatus : SM3fqPlusNoNewInteriorEliminationCertificateStatus
  noNewInteriorEliminationCertificateStatus_eq :
    noNewInteriorEliminationCertificateStatus =
      SM3fqPlusNoNewInteriorEliminationCertificateStatus.noNewInteriorEliminationCertificate
  noDtnMultiSchurConsumerStatus : SM3fqPlusNoDtnMultiSchurConsumerStatus
  noDtnMultiSchurConsumerStatus_eq :
    noDtnMultiSchurConsumerStatus =
      SM3fqPlusNoDtnMultiSchurConsumerStatus.noDtnGeneralizedDtnOrMultiSchurConsumer
  noCharpolyDiscriminantHeegnerStatus : SM3fqPlusNoCharpolyDiscriminantHeegnerStatus
  noCharpolyDiscriminantHeegnerStatus_eq :
    noCharpolyDiscriminantHeegnerStatus =
      SM3fqPlusNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantOrHeegner

namespace GeneratedSM3fSchurExecCompletionSM3fqPlus

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {p : ConcretePolicyOf}
variable {A : GeneratedApproximantStrong Cell p}
variable [Fintype (GeneratedBoundaryIndex A)]
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

def fromSources
    (Q : GeneratedSM3fSchurExecEntrySourceSM3fq Cell p A P wp W E K T M S H)
    (D : GeneratedDirichletExecEntrySourceSM3bq Cell p A P wp W)
    (X : GeneratedInverseCandidateExecEntrySourceSM3eRq Cell p A P wp W E K T M S H) :
    GeneratedSM3fSchurExecCompletionSM3fqPlus Cell p A P wp W E K T M S H where
  sourceSM3fq := Q
  sourceDirichletExec := D
  sourceInverseExec := X
  boundaryBlockExec := generatedBoundaryBlockExecSM3fqPlus D
  boundaryBlockExec_eq := by
    rfl
  boundaryBlockExec_bridge := by
    intro i j
    exact generatedBoundaryBlockExecSM3fqPlus_bridge D i j
  boundaryInteriorBlockExec := generatedBoundaryInteriorBlockExecSM3fqPlus D
  boundaryInteriorBlockExec_eq := by
    rfl
  boundaryInteriorBlockExec_bridge := by
    intro i j
    exact generatedBoundaryInteriorBlockExecSM3fqPlus_bridge D i j
  interiorBoundaryBlockExec := generatedInteriorBoundaryBlockExecSM3fqPlus D
  interiorBoundaryBlockExec_eq := by
    rfl
  interiorBoundaryBlockExec_bridge := by
    intro i j
    exact generatedInteriorBoundaryBlockExecSM3fqPlus_bridge D i j
  inverseMatrixExec := generatedInverseMatrixExecSM3fqPlus X
  inverseMatrixExec_eq := by
    rfl
  inverseMatrixExec_bridge := by
    intro i j
    exact generatedInverseMatrixExecSM3fqPlus_bridge X i j
  schurCorrectionExec := generatedSM3fqPlusSchurCorrectionExec D X
  schurCorrectionExec_eq := by
    rfl
  schurCorrectionExec_bridge := by
    intro i j
    exact generatedSM3fqPlusSchurCorrectionExec_bridge D X i j
  boundaryOperatorExec := generatedSM3fqPlusBoundaryOperatorExec D X
  boundaryOperatorExec_eq := by
    rfl
  boundaryOperatorExec_bridge_to_handoffSchur := by
    intro i j
    exact generatedSM3fqPlusBoundaryOperatorExec_bridge_to_handoffSchur D X i j
  boundaryOperatorExec_bridge_to_SM3fSchur := by
    intro i j
    exact generatedSM3fqPlusBoundaryOperatorExec_bridge_to_SM3fSchur Q D X i j
  sourceSM3fqBoundaryOperatorReal_eq_handoffSchur := by
    exact sourceSM3fq_boundaryOperatorReal_eq_handoffSchurSM3fqPlus Q
  sourceDirichletReady := D.nextPhaseStatus_eq
  sourceInverseReady := X.nextPhaseStatus_eq
  completionStatus := SM3fqPlusCompletionStatus.boundarySchurExecCompletedFromSM3bqAndSM3eRq
  completionStatus_eq := by
    rfl
  nextPhaseStatus := SM3fqPlusNextPhaseStatus.sm4qMayRecheckBoundarySchurExecSource
  nextPhaseStatus_eq := by
    rfl
  noFreeExecMatrixStatus := SM3fqPlusNoFreeExecMatrixStatus.noFreeExecMatrix
  noFreeExecMatrixStatus_eq := by
    rfl
  noRealToRatReverseCastStatus := SM3fqPlusNoRealToRatReverseCastStatus.noRealToRatReverseCast
  noRealToRatReverseCastStatus_eq := by
    rfl
  noScalarInverseStatus := SM3fqPlusNoScalarInverseStatus.noScalarInverse
  noScalarInverseStatus_eq := by
    rfl
  noMatrixInvStatus := SM3fqPlusNoMatrixInvStatus.noMatrixInv
  noMatrixInvStatus_eq := by
    rfl
  noNewInverseOracleStatus := SM3fqPlusNoNewInverseOracleStatus.noNewInverseOracle
  noNewInverseOracleStatus_eq := by
    rfl
  noProductIdentityProofStatus := SM3fqPlusNoProductIdentityProofStatus.noProductIdentityProof
  noProductIdentityProofStatus_eq := by
    rfl
  noTwoSidedInvStatus := SM3fqPlusNoTwoSidedInvStatus.noTwoSidedInv
  noTwoSidedInvStatus_eq := by
    rfl
  noNewInteriorEliminationCertificateStatus :=
    SM3fqPlusNoNewInteriorEliminationCertificateStatus.noNewInteriorEliminationCertificate
  noNewInteriorEliminationCertificateStatus_eq := by
    rfl
  noDtnMultiSchurConsumerStatus :=
    SM3fqPlusNoDtnMultiSchurConsumerStatus.noDtnGeneralizedDtnOrMultiSchurConsumer
  noDtnMultiSchurConsumerStatus_eq := by
    rfl
  noCharpolyDiscriminantHeegnerStatus :=
    SM3fqPlusNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantOrHeegner
  noCharpolyDiscriminantHeegnerStatus_eq := by
    rfl

theorem boundaryOperatorExec_bridge_to_SM3fSchur_thm
    (C : GeneratedSM3fSchurExecCompletionSM3fqPlus Cell p A P wp W E K T M S H)
    (i j : GeneratedBoundaryIndex A) :
    ExecComplexBridge.toComplex (C.boundaryOperatorExec i j) =
      ((C.sourceSM3fq.boundaryOperatorReal i j : ℝ) : ℂ) :=
  C.boundaryOperatorExec_bridge_to_SM3fSchur i j

theorem boundaryOperatorExec_bridge_to_handoffSchur_thm
    (C : GeneratedSM3fSchurExecCompletionSM3fqPlus Cell p A P wp W E K T M S H)
    (i j : GeneratedBoundaryIndex A) :
    ExecComplexBridge.toComplex (C.boundaryOperatorExec i j) =
      (((generatedBoundaryBlockSM3fR W -
          generatedBoundaryInteriorBlockSM3fR W * H.candidateMatrix *
            generatedInteriorBoundaryBlockSM3fR W) i j : ℝ) : ℂ) :=
  C.boundaryOperatorExec_bridge_to_handoffSchur i j

theorem no_forbidden_shortcuts
    (C : GeneratedSM3fSchurExecCompletionSM3fqPlus Cell p A P wp W E K T M S H) :
    C.noFreeExecMatrixStatus = SM3fqPlusNoFreeExecMatrixStatus.noFreeExecMatrix ∧
    C.noRealToRatReverseCastStatus = SM3fqPlusNoRealToRatReverseCastStatus.noRealToRatReverseCast ∧
    C.noScalarInverseStatus = SM3fqPlusNoScalarInverseStatus.noScalarInverse ∧
    C.noMatrixInvStatus = SM3fqPlusNoMatrixInvStatus.noMatrixInv ∧
    C.noNewInverseOracleStatus = SM3fqPlusNoNewInverseOracleStatus.noNewInverseOracle ∧
    C.noProductIdentityProofStatus = SM3fqPlusNoProductIdentityProofStatus.noProductIdentityProof ∧
    C.noTwoSidedInvStatus = SM3fqPlusNoTwoSidedInvStatus.noTwoSidedInv ∧
    C.noNewInteriorEliminationCertificateStatus =
      SM3fqPlusNoNewInteriorEliminationCertificateStatus.noNewInteriorEliminationCertificate ∧
    C.noDtnMultiSchurConsumerStatus =
      SM3fqPlusNoDtnMultiSchurConsumerStatus.noDtnGeneralizedDtnOrMultiSchurConsumer ∧
    C.noCharpolyDiscriminantHeegnerStatus =
      SM3fqPlusNoCharpolyDiscriminantHeegnerStatus.noCharpolyDiscriminantOrHeegner :=
  ⟨C.noFreeExecMatrixStatus_eq,
   C.noRealToRatReverseCastStatus_eq,
   C.noScalarInverseStatus_eq,
   C.noMatrixInvStatus_eq,
   C.noNewInverseOracleStatus_eq,
   C.noProductIdentityProofStatus_eq,
   C.noTwoSidedInvStatus_eq,
   C.noNewInteriorEliminationCertificateStatus_eq,
   C.noDtnMultiSchurConsumerStatus_eq,
   C.noCharpolyDiscriminantHeegnerStatus_eq⟩

theorem next_phase_is_SM4q_recheck
    (C : GeneratedSM3fSchurExecCompletionSM3fqPlus Cell p A P wp W E K T M S H) :
    C.nextPhaseStatus = SM3fqPlusNextPhaseStatus.sm4qMayRecheckBoundarySchurExecSource :=
  C.nextPhaseStatus_eq

end GeneratedSM3fSchurExecCompletionSM3fqPlus

def regularGeneratedSM3fSchurExecCompletionSM3fqPlus
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight) :
    GeneratedSM3fSchurExecCompletionSM3fqPlus
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight) :=
  GeneratedSM3fSchurExecCompletionSM3fqPlus.fromSources
    (regularGeneratedSM3fSchurExecEntrySource_from_accumulatedEntryCancellationLedgerSM3fq L)
    (regularGeneratedDirichletExecEntrySourceSM3bq b p regularWeight)
    (regularGeneratedInverseCandidateExecEntrySourceSM3eRq b p regularWeight)

def variableGeneratedSM3fSchurExecCompletionSM3fqPlus
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight) :
    GeneratedSM3fSchurExecCompletionSM3fqPlus
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight) :=
  GeneratedSM3fSchurExecCompletionSM3fqPlus.fromSources
    (variableGeneratedSM3fSchurExecEntrySource_from_accumulatedEntryCancellationLedgerSM3fq L)
    (variableGeneratedDirichletExecEntrySourceSM3bq β p variableWeight)
    (variableGeneratedInverseCandidateExecEntrySourceSM3eRq β p variableWeight)

structure SM3fqPlusGeneratedSM3fSchurExecCompletionLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  sourceSM3fqLedger : SM3fqGeneratedSM3fSchurExecEntrySourceLedger b β p regularWeight variableWeight
  regularCompletion :
    GeneratedSM3fSchurExecCompletionSM3fqPlus
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight)
  variableCompletion :
    GeneratedSM3fSchurExecCompletionSM3fqPlus
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight)
  sourceSM3fqLedger_eq_main :
    sourceSM3fqLedger = sm3fqGeneratedSM3fSchurExecEntrySourceLedger sourceSM3fqLedger.sourceSM3fLedger
  regularCompletion_eq_main :
    regularCompletion = regularGeneratedSM3fSchurExecCompletionSM3fqPlus sourceSM3fqLedger.sourceSM3fLedger
  variableCompletion_eq_main :
    variableCompletion = variableGeneratedSM3fSchurExecCompletionSM3fqPlus sourceSM3fqLedger.sourceSM3fLedger
  regularBoundaryOperatorBridge : ∀ i j,
    ExecComplexBridge.toComplex (regularCompletion.boundaryOperatorExec i j) =
      ((regularCompletion.sourceSM3fq.boundaryOperatorReal i j : ℝ) : ℂ)
  variableBoundaryOperatorBridge : ∀ i j,
    ExecComplexBridge.toComplex (variableCompletion.boundaryOperatorExec i j) =
      ((variableCompletion.sourceSM3fq.boundaryOperatorReal i j : ℝ) : ℂ)
  regularCompletionStatus : SM3fqPlusCompletionStatus
  regularCompletionStatus_eq :
    regularCompletionStatus = SM3fqPlusCompletionStatus.boundarySchurExecCompletedFromSM3bqAndSM3eRq
  variableCompletionStatus : SM3fqPlusCompletionStatus
  variableCompletionStatus_eq :
    variableCompletionStatus = SM3fqPlusCompletionStatus.boundarySchurExecCompletedFromSM3bqAndSM3eRq
  nextPhaseStatus : SM3fqPlusNextPhaseStatus
  nextPhaseStatus_eq : nextPhaseStatus = SM3fqPlusNextPhaseStatus.sm4qMayRecheckBoundarySchurExecSource

def sm3fqPlusGeneratedSM3fSchurExecCompletionLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight) :
    SM3fqPlusGeneratedSM3fSchurExecCompletionLedger b β p regularWeight variableWeight where
  sourceSM3fqLedger := sm3fqGeneratedSM3fSchurExecEntrySourceLedger L
  regularCompletion := regularGeneratedSM3fSchurExecCompletionSM3fqPlus L
  variableCompletion := variableGeneratedSM3fSchurExecCompletionSM3fqPlus L
  sourceSM3fqLedger_eq_main := by
    rfl
  regularCompletion_eq_main := by
    rfl
  variableCompletion_eq_main := by
    rfl
  regularBoundaryOperatorBridge := by
    intro i j
    exact (regularGeneratedSM3fSchurExecCompletionSM3fqPlus L).boundaryOperatorExec_bridge_to_SM3fSchur i j
  variableBoundaryOperatorBridge := by
    intro i j
    exact (variableGeneratedSM3fSchurExecCompletionSM3fqPlus L).boundaryOperatorExec_bridge_to_SM3fSchur i j
  regularCompletionStatus := SM3fqPlusCompletionStatus.boundarySchurExecCompletedFromSM3bqAndSM3eRq
  regularCompletionStatus_eq := by
    rfl
  variableCompletionStatus := SM3fqPlusCompletionStatus.boundarySchurExecCompletedFromSM3bqAndSM3eRq
  variableCompletionStatus_eq := by
    rfl
  nextPhaseStatus := SM3fqPlusNextPhaseStatus.sm4qMayRecheckBoundarySchurExecSource
  nextPhaseStatus_eq := by
    rfl

theorem sm3fqPlus_regularCompletionStatus_closed
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3fqPlusGeneratedSM3fSchurExecCompletionLedger b β p regularWeight variableWeight) :
    L.regularCompletionStatus =
      SM3fqPlusCompletionStatus.boundarySchurExecCompletedFromSM3bqAndSM3eRq :=
  L.regularCompletionStatus_eq

theorem sm3fqPlus_variableCompletionStatus_closed
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3fqPlusGeneratedSM3fSchurExecCompletionLedger b β p regularWeight variableWeight) :
    L.variableCompletionStatus =
      SM3fqPlusCompletionStatus.boundarySchurExecCompletedFromSM3bqAndSM3eRq :=
  L.variableCompletionStatus_eq

theorem sm3fqPlus_nextPhase_is_SM4q_recheck
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3fqPlusGeneratedSM3fSchurExecCompletionLedger b β p regularWeight variableWeight) :
    L.nextPhaseStatus = SM3fqPlusNextPhaseStatus.sm4qMayRecheckBoundarySchurExecSource :=
  L.nextPhaseStatus_eq

end Smoke

end CNNA.PillarA.Arithmetic
