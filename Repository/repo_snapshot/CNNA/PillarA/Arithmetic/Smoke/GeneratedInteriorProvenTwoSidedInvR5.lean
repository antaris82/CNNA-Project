import CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTwoSidedInvFromSM3db7R
import CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorProductIdentityProofR4a

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.DtN

namespace Smoke

universe u

def twoSidedInv_from_productIdentityProofR4a
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
    (Q : GeneratedInteriorSM3db7RProductIdentityProof Cell p A P wp W E K T M S H) :
    TwoSidedInv (generatedInteriorBlock W) H.candidateMatrix :=
  provenTwoSidedInvFromSM3db7R Q

def twoSidedInv_from_productCancellationLedger_via_r4a
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
    TwoSidedInv (generatedInteriorBlock W) H.candidateMatrix :=
  twoSidedInv_from_productIdentityProofR4a
    (productIdentityProof_from_productCancellationLedger L)

def twoSidedInv_from_r3c2TraceCancellationLedger_via_r4a
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
    TwoSidedInv (generatedInteriorBlock W) H.candidateMatrix :=
  twoSidedInv_from_productIdentityProofR4a
    (productIdentityProof_from_r3c2TraceCancellationLedger L)

def regularTwoSidedInv_from_reRunProductCancellationLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRReRunGeneratedProductCancellationLedger b β p regularWeight variableWeight) :
    TwoSidedInv
      (generatedInteriorBlock (regularGeneratedWeightPolicyEntrySource b p regularWeight))
      (regularSM3dbRToSM3eRHandoff b p regularWeight).candidateMatrix :=
  twoSidedInv_from_productIdentityProofR4a
    (regularProductIdentityProof_from_reRunProductCancellationLedger L)

def variableTwoSidedInv_from_reRunProductCancellationLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRReRunGeneratedProductCancellationLedger b β p regularWeight variableWeight) :
    TwoSidedInv
      (generatedInteriorBlock (variableGeneratedWeightPolicyEntrySource β p variableWeight))
      (variableSM3dbRToSM3eRHandoff β p variableWeight).candidateMatrix :=
  twoSidedInv_from_productIdentityProofR4a
    (variableProductIdentityProof_from_reRunProductCancellationLedger L)

def regularTwoSidedInv_from_accumulatedEntryCancellationLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight) :
    TwoSidedInv
      (generatedInteriorBlock (regularGeneratedWeightPolicyEntrySource b p regularWeight))
      (regularSM3dbRToSM3eRHandoff b p regularWeight).candidateMatrix :=
  twoSidedInv_from_productIdentityProofR4a
    (regularProductIdentityProof_from_accumulatedEntryCancellationLedger L)

def variableTwoSidedInv_from_accumulatedEntryCancellationLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight) :
    TwoSidedInv
      (generatedInteriorBlock (variableGeneratedWeightPolicyEntrySource β p variableWeight))
      (variableSM3dbRToSM3eRHandoff β p variableWeight).candidateMatrix :=
  twoSidedInv_from_productIdentityProofR4a
    (variableProductIdentityProof_from_accumulatedEntryCancellationLedger L)

end Smoke

end CNNA.PillarA.Arithmetic
