import CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCandidateEntry
import CNNA.PillarA.DtN.DtN

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.DtN

namespace Smoke

universe u

inductive GeneratedCandidateEntryShapeAuditOutcome where
  | candidateEntryEqualsInteriorBlock
  | shapeObstruction
  deriving DecidableEq, Repr

inductive SM3eR0CandidateEntryShapeAuditStatus where
  | candidateEntryShapeAuditedFromSM3daR
  deriving DecidableEq, Repr

inductive SM3eRNoRepairStatus where
  | noRepairFormulaNoMatrixInvNoExternalOracle
  deriving DecidableEq, Repr

inductive SM3eRNoInteriorEliminationCertificateStatus where
  | noInteriorEliminationCertificateInSM3eR
  deriving DecidableEq, Repr

inductive SM3eRNoDtnDataStatus where
  | noDtnGeneralizedDtnOrMultiSchurDataInSM3eR
  deriving DecidableEq, Repr

inductive SM3eRNoArithmeticTargetStatus where
  | noCharpolyFactorDiscriminantOrL23TargetInSM3eR
  deriving DecidableEq, Repr

inductive GeneratedInteriorTwoSidedInvObstructionReason where
  | candidateEntryEqualsInteriorBlockAndSquareIdentityNotDerived
  deriving DecidableEq, Repr

inductive GeneratedInteriorTwoSidedInvReturnTarget where
  | returnToSM3daR
  | returnToSM3dR
  | returnToSM3cR
  deriving DecidableEq, Repr

inductive SM3eRGeneratedTwoSidedInvLedgerStatus where
  | shapeAuditClosedProductProofObstructed
  deriving DecidableEq, Repr

def GeneratedInteriorCandidateLeftProductEntry
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W)
    (i j : GeneratedInteriorIndex A) : ℝ :=
  (generatedInteriorBlock W * candidateMatrix_from_candidateEntry E) i j

def GeneratedInteriorCandidateRightProductEntry
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W)
    (i j : GeneratedInteriorIndex A) : ℝ :=
  (candidateMatrix_from_candidateEntry E * generatedInteriorBlock W) i j

theorem candidateEntry_eq_candidateSource
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W)
    (i j : GeneratedInteriorIndex A) :
    E.entry i j =
      generatedInteriorEliminationCandidateEntry_from_treeRecursiveProfile_value
        E.candidate i j :=
  E.entry_eq_from_treeRecursiveProfile i j

theorem candidateMatrix_entry_eq_candidateEntry
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W)
    (i j : GeneratedInteriorIndex A) :
    candidateMatrix_from_candidateEntry E i j = E.entry i j :=
  candidateMatrix_from_candidateEntry_entry E i j

theorem candidateEntry_eq_interiorBlock
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W)
    (i j : GeneratedInteriorIndex A) :
    E.entry i j = generatedInteriorBlock W i j := by
  calc
    E.entry i j =
        generatedInteriorEliminationCandidateEntry_from_treeRecursiveProfile_value
          E.candidate i j :=
      candidateEntry_eq_candidateSource E i j
    _ = generatedInteriorBlock W i j := by
      unfold generatedInteriorEliminationCandidateEntry_from_treeRecursiveProfile_value
      rw [E.candidateSource_treeRecursive]

theorem candidateMatrix_entry_eq_interiorBlock
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W)
    (i j : GeneratedInteriorIndex A) :
    candidateMatrix_from_candidateEntry E i j = generatedInteriorBlock W i j := by
  calc
    candidateMatrix_from_candidateEntry E i j = E.entry i j :=
      candidateMatrix_entry_eq_candidateEntry E i j
    _ = generatedInteriorBlock W i j :=
      candidateEntry_eq_interiorBlock E i j

theorem candidateMatrix_eq_interiorBlock
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W) :
    candidateMatrix_from_candidateEntry E = generatedInteriorBlock W := by
  funext i j
  exact candidateMatrix_entry_eq_interiorBlock E i j

theorem candidateEntry_eq_interiorBlock_or_shapeObstruction
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W) :
    (∀ i j : GeneratedInteriorIndex A, E.entry i j = generatedInteriorBlock W i j) ∨
      GeneratedCandidateEntryShapeAuditOutcome.shapeObstruction =
        GeneratedCandidateEntryShapeAuditOutcome.candidateEntryEqualsInteriorBlock := by
  exact Or.inl (fun i j => candidateEntry_eq_interiorBlock E i j)

theorem interiorBlock_square_left_entry
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W)
    (i j : GeneratedInteriorIndex A) :
    GeneratedInteriorCandidateLeftProductEntry E i j =
      (generatedInteriorBlock W * generatedInteriorBlock W) i j :=
  congrArg
    (fun M : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ =>
      (generatedInteriorBlock W * M) i j)
    (candidateMatrix_eq_interiorBlock E)

theorem interiorBlock_square_right_entry
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W)
    (i j : GeneratedInteriorIndex A) :
    GeneratedInteriorCandidateRightProductEntry E i j =
      (generatedInteriorBlock W * generatedInteriorBlock W) i j :=
  congrArg
    (fun M : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ =>
      (M * generatedInteriorBlock W) i j)
    (candidateMatrix_eq_interiorBlock E)

structure GeneratedCandidateEntryShapeAudit
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf)
    (A : GeneratedApproximantStrong Cell p)
    (P : GeneratedBoundaryInteriorPartition Cell p A)
    (wp : WeightPolicy)
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp) where
  candidateEntry : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W
  outcome : GeneratedCandidateEntryShapeAuditOutcome
  status : SM3eR0CandidateEntryShapeAuditStatus
  noRepairStatus : SM3eRNoRepairStatus
  candidateEntry_eq_candidateSource :
    ∀ i j : GeneratedInteriorIndex A,
      candidateEntry.entry i j =
        generatedInteriorEliminationCandidateEntry_from_treeRecursiveProfile_value
          candidateEntry.candidate i j
  candidateMatrix_entry_eq_candidateEntry :
    ∀ i j : GeneratedInteriorIndex A,
      candidateMatrix_from_candidateEntry candidateEntry i j = candidateEntry.entry i j
  candidateEntry_eq_interiorBlock :
    ∀ i j : GeneratedInteriorIndex A,
      candidateEntry.entry i j = generatedInteriorBlock W i j
  candidateMatrix_entry_eq_interiorBlock :
    ∀ i j : GeneratedInteriorIndex A,
      candidateMatrix_from_candidateEntry candidateEntry i j = generatedInteriorBlock W i j
  candidateMatrix_eq_interiorBlock :
    candidateMatrix_from_candidateEntry candidateEntry = generatedInteriorBlock W
  candidateEntry_eq_interiorBlock_or_shapeObstruction :
    (∀ i j : GeneratedInteriorIndex A,
      candidateEntry.entry i j = generatedInteriorBlock W i j) ∨
      GeneratedCandidateEntryShapeAuditOutcome.shapeObstruction =
        GeneratedCandidateEntryShapeAuditOutcome.candidateEntryEqualsInteriorBlock
  outcome_eq_candidateEntryEqualsInteriorBlock :
    outcome = GeneratedCandidateEntryShapeAuditOutcome.candidateEntryEqualsInteriorBlock
  status_eq_closed :
    status = SM3eR0CandidateEntryShapeAuditStatus.candidateEntryShapeAuditedFromSM3daR
  noRepairStatus_eq :
    noRepairStatus = SM3eRNoRepairStatus.noRepairFormulaNoMatrixInvNoExternalOracle

namespace GeneratedCandidateEntryShapeAudit

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {p : ConcretePolicyOf}
variable {A : GeneratedApproximantStrong Cell p}
variable {P : GeneratedBoundaryInteriorPartition Cell p A}
variable {wp : WeightPolicy}
variable {W : GeneratedWeightPolicyEntrySource Cell p A P wp}

def fromCandidateEntry
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W) :
    GeneratedCandidateEntryShapeAudit Cell p A P wp W where
  candidateEntry := E
  outcome := GeneratedCandidateEntryShapeAuditOutcome.candidateEntryEqualsInteriorBlock
  status := SM3eR0CandidateEntryShapeAuditStatus.candidateEntryShapeAuditedFromSM3daR
  noRepairStatus := SM3eRNoRepairStatus.noRepairFormulaNoMatrixInvNoExternalOracle
  candidateEntry_eq_candidateSource := by
    intro i j
    exact Smoke.candidateEntry_eq_candidateSource E i j
  candidateMatrix_entry_eq_candidateEntry := by
    intro i j
    exact Smoke.candidateMatrix_entry_eq_candidateEntry E i j
  candidateEntry_eq_interiorBlock := by
    intro i j
    exact Smoke.candidateEntry_eq_interiorBlock E i j
  candidateMatrix_entry_eq_interiorBlock := by
    intro i j
    exact Smoke.candidateMatrix_entry_eq_interiorBlock E i j
  candidateMatrix_eq_interiorBlock :=
    Smoke.candidateMatrix_eq_interiorBlock E
  candidateEntry_eq_interiorBlock_or_shapeObstruction :=
    Smoke.candidateEntry_eq_interiorBlock_or_shapeObstruction E
  outcome_eq_candidateEntryEqualsInteriorBlock := by
    rfl
  status_eq_closed := by
    rfl
  noRepairStatus_eq := by
    rfl

end GeneratedCandidateEntryShapeAudit

structure GeneratedInteriorTwoSidedInvProof
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf)
    (A : GeneratedApproximantStrong Cell p)
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    (P : GeneratedBoundaryInteriorPartition Cell p A)
    (wp : WeightPolicy)
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W) : Prop where
  left_product_entry_eq_one :
    ∀ i j : GeneratedInteriorIndex A,
      GeneratedInteriorCandidateLeftProductEntry E i j =
        (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j
  right_product_entry_eq_one :
    ∀ i j : GeneratedInteriorIndex A,
      GeneratedInteriorCandidateRightProductEntry E i j =
        (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j
  left_product_diagonal_entry :
    ∀ i : GeneratedInteriorIndex A,
      GeneratedInteriorCandidateLeftProductEntry E i i = 1
  left_product_offdiag_entry :
    ∀ i j : GeneratedInteriorIndex A,
      i ≠ j → GeneratedInteriorCandidateLeftProductEntry E i j = 0
  right_product_diagonal_entry :
    ∀ i : GeneratedInteriorIndex A,
      GeneratedInteriorCandidateRightProductEntry E i i = 1
  right_product_offdiag_entry :
    ∀ i j : GeneratedInteriorIndex A,
      i ≠ j → GeneratedInteriorCandidateRightProductEntry E i j = 0

def provenTwoSidedInv
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
    (H : GeneratedInteriorTwoSidedInvProof Cell p A P wp W E) :
    TwoSidedInv (generatedInteriorBlock W) (candidateMatrix_from_candidateEntry E) where
  left_inv := by
    funext i j
    exact H.left_product_entry_eq_one i j
  right_inv := by
    funext i j
    exact H.right_product_entry_eq_one i j

theorem left_product_diagonal_entry
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
    (H : GeneratedInteriorTwoSidedInvProof Cell p A P wp W E)
    (i : GeneratedInteriorIndex A) :
    GeneratedInteriorCandidateLeftProductEntry E i i = 1 :=
  H.left_product_diagonal_entry i

theorem left_product_offdiag_entry
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
    (H : GeneratedInteriorTwoSidedInvProof Cell p A P wp W E)
    (i j : GeneratedInteriorIndex A)
    (hij : i ≠ j) :
    GeneratedInteriorCandidateLeftProductEntry E i j = 0 :=
  H.left_product_offdiag_entry i j hij

theorem right_product_diagonal_entry
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
    (H : GeneratedInteriorTwoSidedInvProof Cell p A P wp W E)
    (i : GeneratedInteriorIndex A) :
    GeneratedInteriorCandidateRightProductEntry E i i = 1 :=
  H.right_product_diagonal_entry i

theorem right_product_offdiag_entry
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    {E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W}
    (H : GeneratedInteriorTwoSidedInvProof Cell p A P wp W E)
    (i j : GeneratedInteriorIndex A)
    (hij : i ≠ j) :
    GeneratedInteriorCandidateRightProductEntry E i j = 0 :=
  H.right_product_offdiag_entry i j hij

structure GeneratedInteriorTwoSidedInvObstruction
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf)
    (A : GeneratedApproximantStrong Cell p)
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    (P : GeneratedBoundaryInteriorPartition Cell p A)
    (wp : WeightPolicy)
    (W : GeneratedWeightPolicyEntrySource Cell p A P wp)
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W) where
  shapeAudit : GeneratedCandidateEntryShapeAudit Cell p A P wp W
  reason : GeneratedInteriorTwoSidedInvObstructionReason
  returnTarget : GeneratedInteriorTwoSidedInvReturnTarget
  noRepairStatus : SM3eRNoRepairStatus
  noCertificateStatus : SM3eRNoInteriorEliminationCertificateStatus
  noDtnDataStatus : SM3eRNoDtnDataStatus
  noArithmeticTargetStatus : SM3eRNoArithmeticTargetStatus
  shapeAudit_candidateEntry_eq : shapeAudit.candidateEntry = E
  candidateEntry_eq_interiorBlock :
    ∀ i j : GeneratedInteriorIndex A, E.entry i j = generatedInteriorBlock W i j
  leftProduct_is_interiorBlockSquare :
    ∀ i j : GeneratedInteriorIndex A,
      GeneratedInteriorCandidateLeftProductEntry E i j =
        (generatedInteriorBlock W * generatedInteriorBlock W) i j
  rightProduct_is_interiorBlockSquare :
    ∀ i j : GeneratedInteriorIndex A,
      GeneratedInteriorCandidateRightProductEntry E i j =
        (generatedInteriorBlock W * generatedInteriorBlock W) i j
  reason_eq :
    reason =
      GeneratedInteriorTwoSidedInvObstructionReason.candidateEntryEqualsInteriorBlockAndSquareIdentityNotDerived
  returnTarget_eq : returnTarget = GeneratedInteriorTwoSidedInvReturnTarget.returnToSM3dR
  noRepairStatus_eq :
    noRepairStatus = SM3eRNoRepairStatus.noRepairFormulaNoMatrixInvNoExternalOracle
  noCertificateStatus_eq :
    noCertificateStatus =
      SM3eRNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificateInSM3eR
  noDtnDataStatus_eq :
    noDtnDataStatus = SM3eRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3eR
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3eRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3eR

def generatedInteriorTwoSidedInvObstruction_fromShapeAudit
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    {A : GeneratedApproximantStrong Cell p}
    [Fintype (GeneratedInteriorIndex A)]
    [DecidableEq (GeneratedInteriorIndex A)]
    {P : GeneratedBoundaryInteriorPartition Cell p A}
    {wp : WeightPolicy}
    {W : GeneratedWeightPolicyEntrySource Cell p A P wp}
    (E : GeneratedInteriorEliminationCandidateEntry Cell p A P wp W) :
    GeneratedInteriorTwoSidedInvObstruction Cell p A P wp W E where
  shapeAudit := GeneratedCandidateEntryShapeAudit.fromCandidateEntry E
  reason :=
    GeneratedInteriorTwoSidedInvObstructionReason.candidateEntryEqualsInteriorBlockAndSquareIdentityNotDerived
  returnTarget := GeneratedInteriorTwoSidedInvReturnTarget.returnToSM3dR
  noRepairStatus := SM3eRNoRepairStatus.noRepairFormulaNoMatrixInvNoExternalOracle
  noCertificateStatus :=
    SM3eRNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificateInSM3eR
  noDtnDataStatus := SM3eRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3eR
  noArithmeticTargetStatus :=
    SM3eRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3eR
  shapeAudit_candidateEntry_eq := by
    rfl
  candidateEntry_eq_interiorBlock := by
    intro i j
    exact candidateEntry_eq_interiorBlock E i j
  leftProduct_is_interiorBlockSquare := by
    intro i j
    exact interiorBlock_square_left_entry E i j
  rightProduct_is_interiorBlockSquare := by
    intro i j
    exact interiorBlock_square_right_entry E i j
  reason_eq := by
    rfl
  returnTarget_eq := by
    rfl
  noRepairStatus_eq := by
    rfl
  noCertificateStatus_eq := by
    rfl
  noDtnDataStatus_eq := by
    rfl
  noArithmeticTargetStatus_eq := by
    rfl

def regularGeneratedCandidateEntryShapeAudit
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedCandidateEntryShapeAudit
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) wp
      (regularGeneratedWeightPolicyEntrySource b p wp) :=
  GeneratedCandidateEntryShapeAudit.fromCandidateEntry
    (regularGeneratedInteriorEliminationCandidateEntry b p wp)

def variableGeneratedCandidateEntryShapeAudit
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedCandidateEntryShapeAudit
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) wp
      (variableGeneratedWeightPolicyEntrySource β p wp) :=
  GeneratedCandidateEntryShapeAudit.fromCandidateEntry
    (variableGeneratedInteriorEliminationCandidateEntry β p wp)

def regularGeneratedInteriorTwoSidedInvObstruction
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedInteriorTwoSidedInvObstruction
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) wp
      (regularGeneratedWeightPolicyEntrySource b p wp)
      (regularGeneratedInteriorEliminationCandidateEntry b p wp) :=
  generatedInteriorTwoSidedInvObstruction_fromShapeAudit
    (regularGeneratedInteriorEliminationCandidateEntry b p wp)

def variableGeneratedInteriorTwoSidedInvObstruction
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy) :
    GeneratedInteriorTwoSidedInvObstruction
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) wp
      (variableGeneratedWeightPolicyEntrySource β p wp)
      (variableGeneratedInteriorEliminationCandidateEntry β p wp) :=
  generatedInteriorTwoSidedInvObstruction_fromShapeAudit
    (variableGeneratedInteriorEliminationCandidateEntry β p wp)

structure SM3eR0CandidateEntryShapeAuditLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  status : SM3eR0CandidateEntryShapeAuditStatus
  sm3daRLedger : SM3daRGeneratedInteriorEliminationCandidateEntryLedger b β p regularWeight variableWeight
  regularShapeAudit :
    GeneratedCandidateEntryShapeAudit
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
  variableShapeAudit :
    GeneratedCandidateEntryShapeAudit
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
  sm3daRLedger_eq_main :
    sm3daRLedger = sm3daRGeneratedInteriorEliminationCandidateEntryLedger b β p regularWeight variableWeight
  regularShapeAudit_eq_main :
    regularShapeAudit = regularGeneratedCandidateEntryShapeAudit b p regularWeight
  variableShapeAudit_eq_main :
    variableShapeAudit = variableGeneratedCandidateEntryShapeAudit β p variableWeight
  regularCandidateEntry_eq_interiorBlock :
    ∀ i j : GeneratedInteriorIndex (regularGeneratedApproximantStrong b p),
      regularShapeAudit.candidateEntry.entry i j =
        regularGeneratedInteriorBlock b p regularWeight i j
  variableCandidateEntry_eq_interiorBlock :
    ∀ i j : GeneratedInteriorIndex (variableGeneratedApproximantStrong β p),
      variableShapeAudit.candidateEntry.entry i j =
        variableGeneratedInteriorBlock β p variableWeight i j
  regularOutcome_eq_candidateEntryEqualsInteriorBlock :
    regularShapeAudit.outcome = GeneratedCandidateEntryShapeAuditOutcome.candidateEntryEqualsInteriorBlock
  variableOutcome_eq_candidateEntryEqualsInteriorBlock :
    variableShapeAudit.outcome = GeneratedCandidateEntryShapeAuditOutcome.candidateEntryEqualsInteriorBlock
  status_eq_closed :
    status = SM3eR0CandidateEntryShapeAuditStatus.candidateEntryShapeAuditedFromSM3daR

def sm3eR0CandidateEntryShapeAuditLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    SM3eR0CandidateEntryShapeAuditLedger b β p regularWeight variableWeight where
  status := SM3eR0CandidateEntryShapeAuditStatus.candidateEntryShapeAuditedFromSM3daR
  sm3daRLedger := sm3daRGeneratedInteriorEliminationCandidateEntryLedger b β p regularWeight variableWeight
  regularShapeAudit := regularGeneratedCandidateEntryShapeAudit b p regularWeight
  variableShapeAudit := variableGeneratedCandidateEntryShapeAudit β p variableWeight
  sm3daRLedger_eq_main := by
    rfl
  regularShapeAudit_eq_main := by
    rfl
  variableShapeAudit_eq_main := by
    rfl
  regularCandidateEntry_eq_interiorBlock := by
    intro i j
    exact (regularGeneratedCandidateEntryShapeAudit b p regularWeight).candidateEntry_eq_interiorBlock i j
  variableCandidateEntry_eq_interiorBlock := by
    intro i j
    exact (variableGeneratedCandidateEntryShapeAudit β p variableWeight).candidateEntry_eq_interiorBlock i j
  regularOutcome_eq_candidateEntryEqualsInteriorBlock := by
    rfl
  variableOutcome_eq_candidateEntryEqualsInteriorBlock := by
    rfl
  status_eq_closed := by
    rfl

structure SM3eRGeneratedTwoSidedInvLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) where
  status : SM3eRGeneratedTwoSidedInvLedgerStatus
  shapeLedger : SM3eR0CandidateEntryShapeAuditLedger b β p regularWeight variableWeight
  regularObstruction :
    GeneratedInteriorTwoSidedInvObstruction
      (ConcreteSubstrate.RegularCell b) p
      (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
  variableObstruction :
    GeneratedInteriorTwoSidedInvObstruction
      (LevelVariableSubstrate.LevelVariableCell β) p
      (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
  noCertificateStatus : SM3eRNoInteriorEliminationCertificateStatus
  noDtnDataStatus : SM3eRNoDtnDataStatus
  noArithmeticTargetStatus : SM3eRNoArithmeticTargetStatus
  shapeLedger_eq_main :
    shapeLedger = sm3eR0CandidateEntryShapeAuditLedger b β p regularWeight variableWeight
  regularObstruction_eq_main :
    regularObstruction = regularGeneratedInteriorTwoSidedInvObstruction b p regularWeight
  variableObstruction_eq_main :
    variableObstruction = variableGeneratedInteriorTwoSidedInvObstruction β p variableWeight
  regularReturnTarget_eq :
    regularObstruction.returnTarget = GeneratedInteriorTwoSidedInvReturnTarget.returnToSM3dR
  variableReturnTarget_eq :
    variableObstruction.returnTarget = GeneratedInteriorTwoSidedInvReturnTarget.returnToSM3dR
  noCertificateStatus_eq :
    noCertificateStatus =
      SM3eRNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificateInSM3eR
  noDtnDataStatus_eq :
    noDtnDataStatus = SM3eRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3eR
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3eRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3eR
  status_eq_obstructed :
    status = SM3eRGeneratedTwoSidedInvLedgerStatus.shapeAuditClosedProductProofObstructed

def sm3eRGeneratedTwoSidedInvLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    SM3eRGeneratedTwoSidedInvLedger b β p regularWeight variableWeight where
  status := SM3eRGeneratedTwoSidedInvLedgerStatus.shapeAuditClosedProductProofObstructed
  shapeLedger := sm3eR0CandidateEntryShapeAuditLedger b β p regularWeight variableWeight
  regularObstruction := regularGeneratedInteriorTwoSidedInvObstruction b p regularWeight
  variableObstruction := variableGeneratedInteriorTwoSidedInvObstruction β p variableWeight
  noCertificateStatus :=
    SM3eRNoInteriorEliminationCertificateStatus.noInteriorEliminationCertificateInSM3eR
  noDtnDataStatus := SM3eRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3eR
  noArithmeticTargetStatus :=
    SM3eRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantOrL23TargetInSM3eR
  shapeLedger_eq_main := by
    rfl
  regularObstruction_eq_main := by
    rfl
  variableObstruction_eq_main := by
    rfl
  regularReturnTarget_eq := by
    rfl
  variableReturnTarget_eq := by
    rfl
  noCertificateStatus_eq := by
    rfl
  noDtnDataStatus_eq := by
    rfl
  noArithmeticTargetStatus_eq := by
    rfl
  status_eq_obstructed := by
    rfl

theorem sm3eR0CandidateEntryShapeAuditLedger_status
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3eR0CandidateEntryShapeAuditLedger b β p regularWeight variableWeight).status =
      SM3eR0CandidateEntryShapeAuditStatus.candidateEntryShapeAuditedFromSM3daR := by
  rfl

theorem sm3eRGeneratedTwoSidedInvLedger_status
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3eRGeneratedTwoSidedInvLedger b β p regularWeight variableWeight).status =
      SM3eRGeneratedTwoSidedInvLedgerStatus.shapeAuditClosedProductProofObstructed := by
  rfl

theorem sm3eRGeneratedTwoSidedInvLedger_regularReturnTarget
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3eRGeneratedTwoSidedInvLedger b β p regularWeight variableWeight).regularObstruction.returnTarget =
      GeneratedInteriorTwoSidedInvReturnTarget.returnToSM3dR := by
  rfl

theorem sm3eRGeneratedTwoSidedInvLedger_variableNoDtnData
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf)
    (regularWeight variableWeight : WeightPolicy) :
    (sm3eRGeneratedTwoSidedInvLedger b β p regularWeight variableWeight).variableObstruction.noDtnDataStatus =
      SM3eRNoDtnDataStatus.noDtnGeneralizedDtnOrMultiSchurDataInSM3eR := by
  rfl

end Smoke

end CNNA.PillarA.Arithmetic
