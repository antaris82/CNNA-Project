import CNNA.PillarA.Arithmetic.Smoke.GeneratedTopBoundaryDtNSM3gR

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.DtN

namespace Smoke

universe u

inductive SM3hRGeneralizedSourceStatus where
  | generatedFromSM3gRTopBoundaryDtN
  deriving DecidableEq, Repr

inductive SM3hRSectorProvenanceStatus where
  | carriedByGeneratedMainPathNoPublicSectorSplit
  deriving DecidableEq, Repr

inductive SM3hRNoExternalDtNStatus where
  | noExternalDtNSourceInSM3hR
  deriving DecidableEq, Repr

inductive SM3hRNoMultiSchurStatus where
  | noMultiSchurDataInSM3hR
  deriving DecidableEq, Repr

inductive SM3hRNoArithmeticTargetStatus where
  | noCharpolyFactorDiscriminantDataInSM3hR
  deriving DecidableEq, Repr

def generatedGeneralizedTopBoundaryOperatorSM3hR
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
    (G : GeneratedTopBoundaryDtNSM3gR Cell p A P wp W E K T M S H) :
    Matrix (GeneratedBoundaryIndex A) (GeneratedBoundaryIndex A) ℝ :=
  G.boundaryOperator

def generatedGeneralizedTopBoundaryApplySM3hR
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
    (G : GeneratedTopBoundaryDtNSM3gR Cell p A P wp W E K T M S H)
    (φ : GeneratedBoundaryIndex A → ℝ) :
    GeneratedBoundaryIndex A → ℝ :=
  G.«apply» φ

structure GeneratedGeneralizedTopBoundaryDtNSM3hR
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
  sourceTopBoundaryDtN : GeneratedTopBoundaryDtNSM3gR Cell p A P wp W E K T M S H
  sourceStatus : SM3hRGeneralizedSourceStatus
  sourceStatus_eq_SM3gR :
    sourceStatus = SM3hRGeneralizedSourceStatus.generatedFromSM3gRTopBoundaryDtN
  mainPathProvenance : GeneratedMainPath Cell p
  source_eq_generatedMainPath : mainPathProvenance = generatedMainPath Cell p
  mainPath_family_eq_generated : mainPathProvenance.family = generatedBranchFamily Cell
  mainPath_toc_eq_generated : mainPathProvenance.toc = generatedBranchToC Cell
  policyHook_eq_generated : mainPathProvenance.policyHook = policyProvenanceHook p
  weightHook_eq_generated : mainPathProvenance.weightHook = weightProvenanceHook
  sectorProvenanceStatus : SM3hRSectorProvenanceStatus
  sectorProvenanceStatus_eq :
    sectorProvenanceStatus =
      SM3hRSectorProvenanceStatus.carriedByGeneratedMainPathNoPublicSectorSplit
  boundaryOperator : Matrix (GeneratedBoundaryIndex A) (GeneratedBoundaryIndex A) ℝ
  boundaryOperator_eq_SM3gR : boundaryOperator = sourceTopBoundaryDtN.boundaryOperator
  «apply» : (GeneratedBoundaryIndex A → ℝ) → GeneratedBoundaryIndex A → ℝ
  apply_eq_SM3gR : ∀ φ : GeneratedBoundaryIndex A → ℝ,
    «apply» φ = sourceTopBoundaryDtN.«apply» φ
  apply_eq_mulVec : ∀ φ : GeneratedBoundaryIndex A → ℝ,
    «apply» φ = boundaryOperator.mulVec φ
  noExternalDtNStatus : SM3hRNoExternalDtNStatus
  noExternalDtNStatus_eq :
    noExternalDtNStatus = SM3hRNoExternalDtNStatus.noExternalDtNSourceInSM3hR
  noMultiSchurStatus : SM3hRNoMultiSchurStatus
  noMultiSchurStatus_eq :
    noMultiSchurStatus = SM3hRNoMultiSchurStatus.noMultiSchurDataInSM3hR
  noArithmeticTargetStatus : SM3hRNoArithmeticTargetStatus
  noArithmeticTargetStatus_eq :
    noArithmeticTargetStatus =
      SM3hRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantDataInSM3hR

namespace GeneratedGeneralizedTopBoundaryDtNSM3hR

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

def fromTopBoundaryDtN
    (G : GeneratedTopBoundaryDtNSM3gR Cell p A P wp W E K T M S H) :
    GeneratedGeneralizedTopBoundaryDtNSM3hR Cell p A P wp W E K T M S H where
  sourceTopBoundaryDtN := G
  sourceStatus := SM3hRGeneralizedSourceStatus.generatedFromSM3gRTopBoundaryDtN
  sourceStatus_eq_SM3gR := by
    rfl
  mainPathProvenance := generatedMainPath Cell p
  source_eq_generatedMainPath := by
    rfl
  mainPath_family_eq_generated := by
    rfl
  mainPath_toc_eq_generated := by
    rfl
  policyHook_eq_generated := by
    rfl
  weightHook_eq_generated := by
    rfl
  sectorProvenanceStatus :=
    SM3hRSectorProvenanceStatus.carriedByGeneratedMainPathNoPublicSectorSplit
  sectorProvenanceStatus_eq := by
    rfl
  boundaryOperator := G.boundaryOperator
  boundaryOperator_eq_SM3gR := by
    rfl
  «apply» := fun φ => G.«apply» φ
  apply_eq_SM3gR := by
    intro φ
    rfl
  apply_eq_mulVec := by
    intro φ
    exact G.apply_eq_mulVec φ
  noExternalDtNStatus := SM3hRNoExternalDtNStatus.noExternalDtNSourceInSM3hR
  noExternalDtNStatus_eq := by
    rfl
  noMultiSchurStatus := SM3hRNoMultiSchurStatus.noMultiSchurDataInSM3hR
  noMultiSchurStatus_eq := by
    rfl
  noArithmeticTargetStatus :=
    SM3hRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantDataInSM3hR
  noArithmeticTargetStatus_eq := by
    rfl

theorem source_from_SM3gR
    (G : GeneratedGeneralizedTopBoundaryDtNSM3hR Cell p A P wp W E K T M S H) :
    G.sourceStatus = SM3hRGeneralizedSourceStatus.generatedFromSM3gRTopBoundaryDtN :=
  G.sourceStatus_eq_SM3gR

theorem mainPath_from_generated
    (G : GeneratedGeneralizedTopBoundaryDtNSM3hR Cell p A P wp W E K T M S H) :
    G.mainPathProvenance = generatedMainPath Cell p :=
  G.source_eq_generatedMainPath

theorem mainPath_family_from_generated
    (G : GeneratedGeneralizedTopBoundaryDtNSM3hR Cell p A P wp W E K T M S H) :
    G.mainPathProvenance.family = generatedBranchFamily Cell :=
  G.mainPath_family_eq_generated

theorem mainPath_toc_from_generated
    (G : GeneratedGeneralizedTopBoundaryDtNSM3hR Cell p A P wp W E K T M S H) :
    G.mainPathProvenance.toc = generatedBranchToC Cell :=
  G.mainPath_toc_eq_generated

theorem boundaryOperator_from_SM3gR
    (G : GeneratedGeneralizedTopBoundaryDtNSM3hR Cell p A P wp W E K T M S H) :
    G.boundaryOperator = G.sourceTopBoundaryDtN.boundaryOperator :=
  G.boundaryOperator_eq_SM3gR

theorem boundaryOperator_from_schur
    (G : GeneratedGeneralizedTopBoundaryDtNSM3hR Cell p A P wp W E K T M S H) :
    G.boundaryOperator =
      generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W *
          G.sourceTopBoundaryDtN.sourceCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W := by
  calc
    G.boundaryOperator = G.sourceTopBoundaryDtN.boundaryOperator :=
      G.boundaryOperator_eq_SM3gR
    _ = generatedBoundaryBlockSM3fR W -
          generatedBoundaryInteriorBlockSM3fR W *
            G.sourceTopBoundaryDtN.sourceCertificate.inverseMatrix *
            generatedInteriorBoundaryBlockSM3fR W :=
      G.sourceTopBoundaryDtN.boundaryOperator_eq_schur

theorem apply_from_SM3gR
    (G : GeneratedGeneralizedTopBoundaryDtNSM3hR Cell p A P wp W E K T M S H)
    (φ : GeneratedBoundaryIndex A → ℝ) :
    G.«apply» φ = G.sourceTopBoundaryDtN.«apply» φ :=
  G.apply_eq_SM3gR φ

theorem apply_from_mulVec
    (G : GeneratedGeneralizedTopBoundaryDtNSM3hR Cell p A P wp W E K T M S H)
    (φ : GeneratedBoundaryIndex A → ℝ) :
    G.«apply» φ = G.boundaryOperator.mulVec φ :=
  G.apply_eq_mulVec φ

theorem boundaryFlux_from_SM3gR
    (G : GeneratedGeneralizedTopBoundaryDtNSM3hR Cell p A P wp W E K T M S H)
    (φ : GeneratedBoundaryIndex A → ℝ) :
    (generatedBoundaryBlockSM3fR W).mulVec φ +
        (generatedBoundaryInteriorBlockSM3fR W).mulVec
          (G.sourceTopBoundaryDtN.sourceCertificate.interiorSolve φ) =
      G.«apply» φ := by
  calc
    (generatedBoundaryBlockSM3fR W).mulVec φ +
        (generatedBoundaryInteriorBlockSM3fR W).mulVec
          (G.sourceTopBoundaryDtN.sourceCertificate.interiorSolve φ)
        = G.sourceTopBoundaryDtN.«apply» φ :=
      G.sourceTopBoundaryDtN.boundaryFlux_spec φ
    _ = G.«apply» φ := by
      exact (G.apply_eq_SM3gR φ).symm

theorem noExternalDtN_from_SM3hR
    (G : GeneratedGeneralizedTopBoundaryDtNSM3hR Cell p A P wp W E K T M S H) :
    G.noExternalDtNStatus = SM3hRNoExternalDtNStatus.noExternalDtNSourceInSM3hR :=
  G.noExternalDtNStatus_eq

theorem noMultiSchur_from_SM3hR
    (G : GeneratedGeneralizedTopBoundaryDtNSM3hR Cell p A P wp W E K T M S H) :
    G.noMultiSchurStatus = SM3hRNoMultiSchurStatus.noMultiSchurDataInSM3hR :=
  G.noMultiSchurStatus_eq

theorem noArithmeticTarget_from_SM3hR
    (G : GeneratedGeneralizedTopBoundaryDtNSM3hR Cell p A P wp W E K T M S H) :
    G.noArithmeticTargetStatus =
      SM3hRNoArithmeticTargetStatus.noCharpolyFactorDiscriminantDataInSM3hR :=
  G.noArithmeticTargetStatus_eq

end GeneratedGeneralizedTopBoundaryDtNSM3hR

def generatedGeneralizedTopBoundaryDtN_from_SM3gR
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
    (G : GeneratedTopBoundaryDtNSM3gR Cell p A P wp W E K T M S H) :
    GeneratedGeneralizedTopBoundaryDtNSM3hR Cell p A P wp W E K T M S H :=
  GeneratedGeneralizedTopBoundaryDtNSM3hR.fromTopBoundaryDtN G

theorem generatedGeneralizedTopBoundaryOperator_eq_SM3gR
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
    (G : GeneratedTopBoundaryDtNSM3gR Cell p A P wp W E K T M S H) :
    generatedGeneralizedTopBoundaryOperatorSM3hR G = G.boundaryOperator := by
  rfl

theorem generatedGeneralizedTopBoundaryApply_eq_SM3gR
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
    (G : GeneratedTopBoundaryDtNSM3gR Cell p A P wp W E K T M S H)
    (φ : GeneratedBoundaryIndex A → ℝ) :
    generatedGeneralizedTopBoundaryApplySM3hR G φ = G.«apply» φ := by
  rfl

def regularGeneratedGeneralizedTopBoundaryDtN_from_reRunProductCancellationLedgerSM3hR
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRReRunGeneratedProductCancellationLedger b β p regularWeight variableWeight) :
    GeneratedGeneralizedTopBoundaryDtNSM3hR
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight) :=
  GeneratedGeneralizedTopBoundaryDtNSM3hR.fromTopBoundaryDtN
    (regularGeneratedTopBoundaryDtN_from_reRunProductCancellationLedgerSM3gR L)

def variableGeneratedGeneralizedTopBoundaryDtN_from_reRunProductCancellationLedgerSM3hR
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRReRunGeneratedProductCancellationLedger b β p regularWeight variableWeight) :
    GeneratedGeneralizedTopBoundaryDtNSM3hR
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight) :=
  GeneratedGeneralizedTopBoundaryDtNSM3hR.fromTopBoundaryDtN
    (variableGeneratedTopBoundaryDtN_from_reRunProductCancellationLedgerSM3gR L)

def regularGeneratedGeneralizedTopBoundaryDtN_from_accumulatedEntryCancellationLedgerSM3hR
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight) :
    GeneratedGeneralizedTopBoundaryDtNSM3hR
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight) :=
  GeneratedGeneralizedTopBoundaryDtNSM3hR.fromTopBoundaryDtN
    (regularGeneratedTopBoundaryDtN_from_accumulatedEntryCancellationLedgerSM3gR L)

def variableGeneratedGeneralizedTopBoundaryDtN_from_accumulatedEntryCancellationLedgerSM3hR
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight) :
    GeneratedGeneralizedTopBoundaryDtNSM3hR
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight) :=
  GeneratedGeneralizedTopBoundaryDtNSM3hR.fromTopBoundaryDtN
    (variableGeneratedTopBoundaryDtN_from_accumulatedEntryCancellationLedgerSM3gR L)

end Smoke

end CNNA.PillarA.Arithmetic
