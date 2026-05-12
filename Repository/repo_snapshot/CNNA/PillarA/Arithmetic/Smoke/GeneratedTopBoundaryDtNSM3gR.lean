import CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorEliminationCertificateSM3fR

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.DtN

namespace Smoke

universe u

def generatedTopBoundaryOperatorSM3gR
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
    (C : GeneratedInteriorEliminationCertificateSM3fR Cell p A P wp W E K T M S H) :
    Matrix (GeneratedBoundaryIndex A) (GeneratedBoundaryIndex A) ℝ :=
  C.boundaryOperator

def generatedTopBoundaryDtNApplySM3gR
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
    (C : GeneratedInteriorEliminationCertificateSM3fR Cell p A P wp W E K T M S H)
    (φ : GeneratedBoundaryIndex A → ℝ) :
    GeneratedBoundaryIndex A → ℝ :=
  C.boundaryOperator.mulVec φ

structure GeneratedTopBoundaryDtNSM3gR
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
  sourceCertificate :
    GeneratedInteriorEliminationCertificateSM3fR Cell p A P wp W E K T M S H
  boundaryOperator : Matrix (GeneratedBoundaryIndex A) (GeneratedBoundaryIndex A) ℝ
  boundaryOperator_eq_SM3fR : boundaryOperator = sourceCertificate.boundaryOperator
  boundaryOperator_eq_schur :
    boundaryOperator =
      generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W * sourceCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W
  «apply» : (GeneratedBoundaryIndex A → ℝ) → GeneratedBoundaryIndex A → ℝ
  apply_eq_mulVec : ∀ φ : GeneratedBoundaryIndex A → ℝ,
    «apply» φ = boundaryOperator.mulVec φ
  boundaryFlux_spec : ∀ φ : GeneratedBoundaryIndex A → ℝ,
    (generatedBoundaryBlockSM3fR W).mulVec φ +
        (generatedBoundaryInteriorBlockSM3fR W).mulVec (sourceCertificate.interiorSolve φ) =
      «apply» φ

namespace GeneratedTopBoundaryDtNSM3gR

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

def fromCertificate
    (C : GeneratedInteriorEliminationCertificateSM3fR Cell p A P wp W E K T M S H) :
    GeneratedTopBoundaryDtNSM3gR Cell p A P wp W E K T M S H where
  sourceCertificate := C
  boundaryOperator := C.boundaryOperator
  boundaryOperator_eq_SM3fR := by
    rfl
  boundaryOperator_eq_schur := by
    exact C.boundaryOperator_eq_schur
  «apply» := fun φ => C.boundaryOperator.mulVec φ
  apply_eq_mulVec := by
    intro φ
    rfl
  boundaryFlux_spec := by
    intro φ
    exact C.boundaryOperator_spec φ

theorem boundaryOperator_from_SM3fR
    (G : GeneratedTopBoundaryDtNSM3gR Cell p A P wp W E K T M S H) :
    G.boundaryOperator = G.sourceCertificate.boundaryOperator :=
  G.boundaryOperator_eq_SM3fR

theorem boundaryOperator_from_schur
    (G : GeneratedTopBoundaryDtNSM3gR Cell p A P wp W E K T M S H) :
    G.boundaryOperator =
      generatedBoundaryBlockSM3fR W -
        generatedBoundaryInteriorBlockSM3fR W * G.sourceCertificate.inverseMatrix *
          generatedInteriorBoundaryBlockSM3fR W :=
  G.boundaryOperator_eq_schur

theorem apply_from_mulVec
    (G : GeneratedTopBoundaryDtNSM3gR Cell p A P wp W E K T M S H)
    (φ : GeneratedBoundaryIndex A → ℝ) :
    G.«apply» φ = G.boundaryOperator.mulVec φ :=
  G.apply_eq_mulVec φ

theorem boundaryFlux_from_SM3fR
    (G : GeneratedTopBoundaryDtNSM3gR Cell p A P wp W E K T M S H)
    (φ : GeneratedBoundaryIndex A → ℝ) :
    (generatedBoundaryBlockSM3fR W).mulVec φ +
        (generatedBoundaryInteriorBlockSM3fR W).mulVec (G.sourceCertificate.interiorSolve φ) =
      G.«apply» φ :=
  G.boundaryFlux_spec φ

end GeneratedTopBoundaryDtNSM3gR

def generatedTopBoundaryDtN_from_certificateSM3gR
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
    (C : GeneratedInteriorEliminationCertificateSM3fR Cell p A P wp W E K T M S H) :
    GeneratedTopBoundaryDtNSM3gR Cell p A P wp W E K T M S H :=
  GeneratedTopBoundaryDtNSM3gR.fromCertificate C

theorem generatedTopBoundaryOperator_eq_SM3fR
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
    (C : GeneratedInteriorEliminationCertificateSM3fR Cell p A P wp W E K T M S H) :
    generatedTopBoundaryOperatorSM3gR C = C.boundaryOperator := by
  rfl

theorem generatedTopBoundaryApply_eq_mulVecSM3gR
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
    (C : GeneratedInteriorEliminationCertificateSM3fR Cell p A P wp W E K T M S H)
    (φ : GeneratedBoundaryIndex A → ℝ) :
    generatedTopBoundaryDtNApplySM3gR C φ = C.boundaryOperator.mulVec φ := by
  rfl

def regularGeneratedTopBoundaryDtN_from_reRunProductCancellationLedgerSM3gR
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRReRunGeneratedProductCancellationLedger b β p regularWeight variableWeight) :
    GeneratedTopBoundaryDtNSM3gR
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight) :=
  GeneratedTopBoundaryDtNSM3gR.fromCertificate
    (regularGeneratedInteriorEliminationCertificate_from_reRunProductCancellationLedgerSM3fR L)

def variableGeneratedTopBoundaryDtN_from_reRunProductCancellationLedgerSM3gR
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRReRunGeneratedProductCancellationLedger b β p regularWeight variableWeight) :
    GeneratedTopBoundaryDtNSM3gR
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight) :=
  GeneratedTopBoundaryDtNSM3gR.fromCertificate
    (variableGeneratedInteriorEliminationCertificate_from_reRunProductCancellationLedgerSM3fR L)

def regularGeneratedTopBoundaryDtN_from_accumulatedEntryCancellationLedgerSM3gR
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight) :
    GeneratedTopBoundaryDtNSM3gR
      (ConcreteSubstrate.RegularCell b) p (regularGeneratedApproximantStrong b p)
      (regularGeneratedBoundaryInteriorPartition b p) regularWeight
      (regularGeneratedWeightPolicyEntrySource b p regularWeight)
      (regularGeneratedInteriorEliminationCandidateEntry b p regularWeight)
      (regularGeneratedInteriorEliminationCarrier b p regularWeight)
      (regularGeneratedInteriorEliminationTrace b p regularWeight)
      (regularGeneratedInteriorInverseCandidateMatrix b p regularWeight)
      (regularGeneratedInteriorInverseCandidateShapeSeparation b p regularWeight)
      (regularSM3dbRToSM3eRHandoff b p regularWeight) :=
  GeneratedTopBoundaryDtNSM3gR.fromCertificate
    (regularGeneratedInteriorEliminationCertificate_from_accumulatedEntryCancellationLedgerSM3fR L)

def variableGeneratedTopBoundaryDtN_from_accumulatedEntryCancellationLedgerSM3gR
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight) :
    GeneratedTopBoundaryDtNSM3gR
      (LevelVariableSubstrate.LevelVariableCell β) p (variableGeneratedApproximantStrong β p)
      (variableGeneratedBoundaryInteriorPartition β p) variableWeight
      (variableGeneratedWeightPolicyEntrySource β p variableWeight)
      (variableGeneratedInteriorEliminationCandidateEntry β p variableWeight)
      (variableGeneratedInteriorEliminationCarrier β p variableWeight)
      (variableGeneratedInteriorEliminationTrace β p variableWeight)
      (variableGeneratedInteriorInverseCandidateMatrix β p variableWeight)
      (variableGeneratedInteriorInverseCandidateShapeSeparation β p variableWeight)
      (variableSM3dbRToSM3eRHandoff β p variableWeight) :=
  GeneratedTopBoundaryDtNSM3gR.fromCertificate
    (variableGeneratedInteriorEliminationCertificate_from_accumulatedEntryCancellationLedgerSM3fR L)

end Smoke

end CNNA.PillarA.Arithmetic
