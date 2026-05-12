import CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorProvenTwoSidedInvR5

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.DtN

namespace Smoke

universe u

open scoped BigOperators

def generatedBoundaryBlockSM3fR
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp) :
    Matrix (GeneratedBoundaryIndex A) (GeneratedBoundaryIndex A) ℝ :=
  fun i j =>
    generatedDirichletMatrix W
      (GeneratedBoundaryIndex.toApproximantIndex i)
      (GeneratedBoundaryIndex.toApproximantIndex j)

def generatedBoundaryInteriorBlockSM3fR
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp) :
    Matrix (GeneratedBoundaryIndex A) (GeneratedInteriorIndex A) ℝ :=
  fun i j =>
    generatedDirichletMatrix W
      (GeneratedBoundaryIndex.toApproximantIndex i)
      (GeneratedInteriorIndex.toApproximantIndex j)

def generatedInteriorBoundaryBlockSM3fR
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp) :
    Matrix (GeneratedInteriorIndex A) (GeneratedBoundaryIndex A) ℝ :=
  fun i j =>
    generatedDirichletMatrix W
      (GeneratedInteriorIndex.toApproximantIndex i)
      (GeneratedBoundaryIndex.toApproximantIndex j)

def generatedInteriorInverseMatrixSM3fR
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
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S) :
    Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ :=
  H.candidateMatrix

def generatedInteriorSolveSM3fR
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
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S)
    (φ : GeneratedBoundaryIndex A → ℝ) :
    GeneratedInteriorIndex A → ℝ :=
  fun i =>
    - (H.candidateMatrix.mulVec
        ((generatedInteriorBoundaryBlockSM3fR W).mulVec φ)) i

def generatedBoundaryOperatorSM3fR
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
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S) :
    Matrix (GeneratedBoundaryIndex A) (GeneratedBoundaryIndex A) ℝ :=
  generatedBoundaryBlockSM3fR W -
    generatedBoundaryInteriorBlockSM3fR W * H.candidateMatrix *
      generatedInteriorBoundaryBlockSM3fR W

theorem generatedInteriorInverseMatrix_eq_handoffCandidateSM3fR
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
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S) :
    generatedInteriorInverseMatrixSM3fR H = H.candidateMatrix := by
  rfl

theorem generatedBoundaryOperator_eq_schurSM3fR
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
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S) :
    generatedBoundaryOperatorSM3fR H =
      generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W * H.candidateMatrix *
          generatedInteriorBoundaryBlockSM3fR W := by
  rfl

theorem generatedInteriorSolve_spec_from_twoSidedInvSM3fR
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
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S)
    (w : TwoSidedInv (generatedInteriorBlock W) H.candidateMatrix)
    (φ : GeneratedBoundaryIndex A → ℝ) :
    (generatedInteriorBlock W).mulVec (generatedInteriorSolveSM3fR H φ) =
      - ((generatedInteriorBoundaryBlockSM3fR W).mulVec φ) := by
  let rhs : GeneratedInteriorIndex A → ℝ :=
    (generatedInteriorBoundaryBlockSM3fR W).mulVec φ
  have hL : generatedInteriorBlock W * H.candidateMatrix = 1 :=
    w.left_inv
  have hNeg :
      (generatedInteriorBlock W).mulVec (generatedInteriorSolveSM3fR H φ) =
        fun i =>
          - ((generatedInteriorBlock W).mulVec
              (H.candidateMatrix.mulVec rhs)) i := by
    funext i
    simp [generatedInteriorSolveSM3fR, rhs, Matrix.mulVec, dotProduct,
      Finset.sum_neg_distrib, mul_neg]
  calc
    (generatedInteriorBlock W).mulVec (generatedInteriorSolveSM3fR H φ)
        = fun i =>
            - ((generatedInteriorBlock W).mulVec
                (H.candidateMatrix.mulVec rhs)) i := hNeg
    _ = fun i =>
          - (((generatedInteriorBlock W) * H.candidateMatrix).mulVec rhs) i := by
          simp [Matrix.mulVec_mulVec]
    _ = fun i => - rhs i := by
          simp [hL]
    _ = - ((generatedInteriorBoundaryBlockSM3fR W).mulVec φ) := by
          rfl

theorem generatedBoundaryOperator_specSM3fR
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
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S)
    (φ : GeneratedBoundaryIndex A → ℝ) :
    (generatedBoundaryBlockSM3fR W).mulVec φ +
        (generatedBoundaryInteriorBlockSM3fR W).mulVec
          (generatedInteriorSolveSM3fR H φ) =
      (generatedBoundaryOperatorSM3fR H).mulVec φ := by
  let rhsI : GeneratedInteriorIndex A → ℝ :=
    (generatedInteriorBoundaryBlockSM3fR W).mulVec φ
  let wI : GeneratedInteriorIndex A → ℝ := H.candidateMatrix.mulVec rhsI
  let M : Matrix (GeneratedBoundaryIndex A) (GeneratedBoundaryIndex A) ℝ :=
    generatedBoundaryInteriorBlockSM3fR W * H.candidateMatrix *
      generatedInteriorBoundaryBlockSM3fR W
  funext b
  have hNeg :
      (generatedBoundaryInteriorBlockSM3fR W).mulVec
          (fun i : GeneratedInteriorIndex A => - wI i) b =
        - ((generatedBoundaryInteriorBlockSM3fR W).mulVec wI) b := by
    simp [Matrix.mulVec, dotProduct, Finset.sum_neg_distrib, mul_neg]
  have hComp :
      M.mulVec φ b =
        (generatedBoundaryInteriorBlockSM3fR W).mulVec wI b := by
    simp [M, wI, rhsI, Matrix.mul_assoc, Matrix.mulVec_mulVec]
  have hNegMat :
      (-M).mulVec φ b = - (M.mulVec φ b) := by
    simp [Matrix.mulVec, dotProduct, Finset.sum_neg_distrib, neg_mul]
  have hInteriorTerm :
      (generatedBoundaryInteriorBlockSM3fR W).mulVec
          (fun i : GeneratedInteriorIndex A => - wI i) b =
        (-M).mulVec φ b := by
    calc
      (generatedBoundaryInteriorBlockSM3fR W).mulVec
          (fun i : GeneratedInteriorIndex A => - wI i) b
          = - ((generatedBoundaryInteriorBlockSM3fR W).mulVec wI) b := hNeg
      _ = - (M.mulVec φ b) := by rw [hComp]
      _ = (-M).mulVec φ b := hNegMat.symm
  have hAdd :
      (generatedBoundaryBlockSM3fR W + (-M)).mulVec φ b =
        (generatedBoundaryBlockSM3fR W).mulVec φ b + (-M).mulVec φ b := by
    simp [Matrix.mulVec, dotProduct, Finset.sum_add_distrib, add_mul]
  have hw : generatedInteriorSolveSM3fR H φ =
      fun i : GeneratedInteriorIndex A => - wI i := by
    funext i
    simp [generatedInteriorSolveSM3fR, wI, rhsI]
  calc
    ((generatedBoundaryBlockSM3fR W).mulVec φ +
        (generatedBoundaryInteriorBlockSM3fR W).mulVec
          (generatedInteriorSolveSM3fR H φ)) b
        = (generatedBoundaryBlockSM3fR W).mulVec φ b +
            (generatedBoundaryInteriorBlockSM3fR W).mulVec
              (fun i : GeneratedInteriorIndex A => - wI i) b := by
              simp [hw]
    _ = (generatedBoundaryBlockSM3fR W).mulVec φ b + (-M).mulVec φ b := by
          rw [hInteriorTerm]
    _ = (generatedBoundaryBlockSM3fR W + (-M)).mulVec φ b := by
          rw [hAdd]
    _ = (generatedBoundaryOperatorSM3fR H).mulVec φ b := by
          simp [generatedBoundaryOperatorSM3fR, M, sub_eq_add_neg]

structure GeneratedInteriorEliminationCertificateSM3fR
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
  inverseMatrix : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ
  inverseMatrix_eq_handoffCandidate : inverseMatrix = H.candidateMatrix
  inverseWitness : TwoSidedInv (generatedInteriorBlock W) inverseMatrix
  boundaryOperator : Matrix (GeneratedBoundaryIndex A) (GeneratedBoundaryIndex A) ℝ
  boundaryOperator_eq_schur :
    boundaryOperator =
      generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W * inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W
  interiorSolve : (GeneratedBoundaryIndex A → ℝ) → GeneratedInteriorIndex A → ℝ
  interiorSolve_eq_inverseMul :
    ∀ φ : GeneratedBoundaryIndex A → ℝ,
      interiorSolve φ =
        fun i =>
          - (inverseMatrix.mulVec
              ((generatedInteriorBoundaryBlockSM3fR W).mulVec φ)) i
  interiorSolve_spec : ∀ φ : GeneratedBoundaryIndex A → ℝ,
    (generatedInteriorBlock W).mulVec (interiorSolve φ) =
      - ((generatedInteriorBoundaryBlockSM3fR W).mulVec φ)
  boundaryOperator_spec : ∀ φ : GeneratedBoundaryIndex A → ℝ,
    (generatedBoundaryBlockSM3fR W).mulVec φ +
        (generatedBoundaryInteriorBlockSM3fR W).mulVec (interiorSolve φ) =
      boundaryOperator.mulVec φ

namespace GeneratedInteriorEliminationCertificateSM3fR

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

def fromTwoSidedInv
    (w : TwoSidedInv (generatedInteriorBlock W) H.candidateMatrix) :
    GeneratedInteriorEliminationCertificateSM3fR Cell p A P wp W E K T M S H where
  inverseMatrix := H.candidateMatrix
  inverseMatrix_eq_handoffCandidate := by
    rfl
  inverseWitness := w
  boundaryOperator := generatedBoundaryOperatorSM3fR H
  boundaryOperator_eq_schur := by
    rfl
  interiorSolve := generatedInteriorSolveSM3fR H
  interiorSolve_eq_inverseMul := by
    intro φ
    rfl
  interiorSolve_spec := by
    intro φ
    exact generatedInteriorSolve_spec_from_twoSidedInvSM3fR H w φ
  boundaryOperator_spec := by
    intro φ
    exact generatedBoundaryOperator_specSM3fR H φ

theorem inverseMatrix_from_handoff
    (C : GeneratedInteriorEliminationCertificateSM3fR Cell p A P wp W E K T M S H) :
    C.inverseMatrix = H.candidateMatrix :=
  C.inverseMatrix_eq_handoffCandidate

theorem boundaryOperator_from_schur
    (C : GeneratedInteriorEliminationCertificateSM3fR Cell p A P wp W E K T M S H) :
    C.boundaryOperator =
      generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W * C.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W :=
  C.boundaryOperator_eq_schur

end GeneratedInteriorEliminationCertificateSM3fR

def generatedInteriorEliminationCertificate_from_productIdentityProofSM3fR
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
    (Q : GeneratedInteriorSM3db7RProductIdentityProof Cell p A P wp W E K T M S H) :
    GeneratedInteriorEliminationCertificateSM3fR Cell p A P wp W E K T M S H :=
  GeneratedInteriorEliminationCertificateSM3fR.fromTwoSidedInv
    (twoSidedInv_from_productIdentityProofR4a Q)

def generatedInteriorEliminationCertificate_from_productCancellationLedgerSM3fR
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
    (L : GeneratedInteriorSM3db7RProductCancellationLedger Cell p A P wp W E K T M S H) :
    GeneratedInteriorEliminationCertificateSM3fR Cell p A P wp W E K T M S H :=
  GeneratedInteriorEliminationCertificateSM3fR.fromTwoSidedInv
    (twoSidedInv_from_productCancellationLedger_via_r4a L)

def generatedInteriorEliminationCertificate_from_r3c2LedgerSM3fR
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
    (L : SM3eRr3c2TraceCancellationLedger Cell p A P wp W E K T M S H) :
    GeneratedInteriorEliminationCertificateSM3fR Cell p A P wp W E K T M S H :=
  GeneratedInteriorEliminationCertificateSM3fR.fromTwoSidedInv
    (twoSidedInv_from_r3c2TraceCancellationLedger_via_r4a L)

def regularGeneratedInteriorEliminationCertificate_from_reRunProductCancellationLedgerSM3fR
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRReRunGeneratedProductCancellationLedger b β p regularWeight variableWeight) :
    GeneratedInteriorEliminationCertificateSM3fR
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight) :=
  GeneratedInteriorEliminationCertificateSM3fR.fromTwoSidedInv
    (regularTwoSidedInv_from_reRunProductCancellationLedger L)

def variableGeneratedInteriorEliminationCertificate_from_reRunProductCancellationLedgerSM3fR
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRReRunGeneratedProductCancellationLedger b β p regularWeight variableWeight) :
    GeneratedInteriorEliminationCertificateSM3fR
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight) :=
  GeneratedInteriorEliminationCertificateSM3fR.fromTwoSidedInv
    (variableTwoSidedInv_from_reRunProductCancellationLedger L)

def regularGeneratedInteriorEliminationCertificate_from_accumulatedEntryCancellationLedgerSM3fR
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight) :
    GeneratedInteriorEliminationCertificateSM3fR
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight) :=
  GeneratedInteriorEliminationCertificateSM3fR.fromTwoSidedInv
    (regularTwoSidedInv_from_accumulatedEntryCancellationLedger L)

def variableGeneratedInteriorEliminationCertificate_from_accumulatedEntryCancellationLedgerSM3fR
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight) :
    GeneratedInteriorEliminationCertificateSM3fR
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight) :=
  GeneratedInteriorEliminationCertificateSM3fR.fromTwoSidedInv
    (variableTwoSidedInv_from_accumulatedEntryCancellationLedger L)

end Smoke

end CNNA.PillarA.Arithmetic
