import CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTraceCancellationR3c2

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

namespace Smoke

universe u

namespace GeneratedInteriorSM3db7RProductIdentityProof

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

def fromProductCancellationLedger
    (L : GeneratedInteriorSM3db7RProductCancellationLedger Cell p A P wp W E K T M S H) :
    GeneratedInteriorSM3db7RProductIdentityProof Cell p A P wp W E K T M S H where
  leftProduct_entry_eq_identity := by
    intro i j
    exact L.leftProduct_entry_eq_identity i j
  rightProduct_entry_eq_identity := by
    intro i j
    exact L.rightProduct_entry_eq_identity i j
  leftProduct_diagonal_entry := by
    intro i
    exact L.leftProduct_diagonal_entry i
  leftProduct_offdiag_entry := by
    intro i j hij
    exact L.leftProduct_offdiag_entry i j hij
  rightProduct_diagonal_entry := by
    intro i
    exact L.rightProduct_diagonal_entry i
  rightProduct_offdiag_entry := by
    intro i j hij
    exact L.rightProduct_offdiag_entry i j hij

end GeneratedInteriorSM3db7RProductIdentityProof

def productIdentityProof_from_productCancellationLedger
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
    (L : GeneratedInteriorSM3db7RProductCancellationLedger Cell p A P wp W E K T M S H) :
    GeneratedInteriorSM3db7RProductIdentityProof Cell p A P wp W E K T M S H :=
  GeneratedInteriorSM3db7RProductIdentityProof.fromProductCancellationLedger L

def productIdentityProof_from_r3c2TraceCancellationLedger
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
    (L : SM3eRr3c2TraceCancellationLedger Cell p A P wp W E K T M S H) :
    GeneratedInteriorSM3db7RProductIdentityProof Cell p A P wp W E K T M S H :=
  productIdentityProof_from_productCancellationLedger L.productCancellationLedger

def regularProductIdentityProof_from_reRunProductCancellationLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRReRunGeneratedProductCancellationLedger b β p regularWeight variableWeight) :=
  productIdentityProof_from_productCancellationLedger L.regularProductCancellationLedger

def variableProductIdentityProof_from_reRunProductCancellationLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRReRunGeneratedProductCancellationLedger b β p regularWeight variableWeight) :=
  productIdentityProof_from_productCancellationLedger L.variableProductCancellationLedger

def regularProductIdentityProof_from_accumulatedEntryCancellationLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight) :=
  regularProductIdentityProof_from_reRunProductCancellationLedger
    (sm3eRReRunGeneratedProductCancellationLedger_from_accumulatedEntryCancellationLedger L)

def variableProductIdentityProof_from_accumulatedEntryCancellationLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight) :=
  variableProductIdentityProof_from_reRunProductCancellationLedger
    (sm3eRReRunGeneratedProductCancellationLedger_from_accumulatedEntryCancellationLedger L)

end Smoke

end CNNA.PillarA.Arithmetic
