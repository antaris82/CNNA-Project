import CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorTraceCancellationDerivation
import CNNA.PillarA.Arithmetic.Smoke.GeneratedInteriorAccumulatedEntryCancellationFromTerminalIdentityR3c1e

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

namespace Smoke

universe u

inductive SM3eRr3c2TraceCancellationDerivationStatus where
  | traceCancellationDerivationFromR3c1AccumulatedInvariant
  deriving DecidableEq, Repr

inductive SM3eRr3c2LedgerStatus where
  | productCancellationLedgerFromR3c1AccumulatedInvariant
  deriving DecidableEq, Repr

namespace GeneratedInteriorSM3db7RTraceCancellationDerivation

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

def fromAccumulatedEntryCancellationInvariant
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S)
    (C : GeneratedInteriorAccumulatedEntryCancellationInvariant Cell p A P wp W E K T) :
    GeneratedInteriorSM3db7RTraceCancellationDerivation Cell p A P wp W E K T M S H :=
  GeneratedInteriorSM3db7RTraceCancellationDerivation.fromSource
    (GeneratedInteriorSM3db7RTraceCancellationSource.fromSM3dbChain H)
    (by
      intro i j
      calc
        GeneratedInteriorSM3db7RLeftProductNormalForm T i j =
            generatedInteriorAccumulatedLeftConvolution W T i j := by
          rfl
        _ = (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j :=
          C.leftAccumulatedConvolution_eq_identity i j)
    (by
      intro i j
      calc
        GeneratedInteriorSM3db7RRightProductNormalForm T i j =
            generatedInteriorAccumulatedRightConvolution W T i j := by
          rfl
        _ = (1 : Matrix (GeneratedInteriorIndex A) (GeneratedInteriorIndex A) ℝ) i j :=
          C.rightAccumulatedConvolution_eq_identity i j)
    (by
      intro i
      calc
        GeneratedInteriorSM3db7RLeftProductNormalForm T i i =
            generatedInteriorAccumulatedLeftConvolution W T i i := by
          rfl
        _ = 1 := C.leftAccumulatedConvolution_diagonal i)
    (by
      intro i j hij
      calc
        GeneratedInteriorSM3db7RLeftProductNormalForm T i j =
            generatedInteriorAccumulatedLeftConvolution W T i j := by
          rfl
        _ = 0 := C.leftAccumulatedConvolution_offdiag i j hij)
    (by
      intro i
      calc
        GeneratedInteriorSM3db7RRightProductNormalForm T i i =
            generatedInteriorAccumulatedRightConvolution W T i i := by
          rfl
        _ = 1 := C.rightAccumulatedConvolution_diagonal i)
    (by
      intro i j hij
      calc
        GeneratedInteriorSM3db7RRightProductNormalForm T i j =
            generatedInteriorAccumulatedRightConvolution W T i j := by
          rfl
        _ = 0 := C.rightAccumulatedConvolution_offdiag i j hij)

end GeneratedInteriorSM3db7RTraceCancellationDerivation

def traceCancellationDerivation_from_accumulatedEntryCancellationInvariant
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
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S)
    (C : GeneratedInteriorAccumulatedEntryCancellationInvariant Cell p A P wp W E K T) :
    GeneratedInteriorSM3db7RTraceCancellationDerivation Cell p A P wp W E K T M S H :=
  GeneratedInteriorSM3db7RTraceCancellationDerivation.fromAccumulatedEntryCancellationInvariant H C

def traceCancellationInvariant_from_accumulatedEntryCancellationInvariant
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
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S)
    (C : GeneratedInteriorAccumulatedEntryCancellationInvariant Cell p A P wp W E K T) :
    GeneratedInteriorSM3db7RTraceCancellationInvariant Cell p A P wp W E K T M S H :=
  traceCancellationInvariant_from_SM3dbChain
    (traceCancellationDerivation_from_accumulatedEntryCancellationInvariant H C)

def productCancellationLedger_from_accumulatedEntryCancellationInvariant
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
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S)
    (C : GeneratedInteriorAccumulatedEntryCancellationInvariant Cell p A P wp W E K T) :
    GeneratedInteriorSM3db7RProductCancellationLedger Cell p A P wp W E K T M S H :=
  productCancellationLedger_from_traceCancellationDerivation
    (traceCancellationDerivation_from_accumulatedEntryCancellationInvariant H C)

structure SM3eRr3c2TraceCancellationLedger
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
  accumulatedEntryCancellation :
    GeneratedInteriorAccumulatedEntryCancellationInvariant Cell p A P wp W E K T
  traceCancellationDerivation :
    GeneratedInteriorSM3db7RTraceCancellationDerivation Cell p A P wp W E K T M S H
  traceCancellationInvariant :
    GeneratedInteriorSM3db7RTraceCancellationInvariant Cell p A P wp W E K T M S H
  productCancellationLedger :
    GeneratedInteriorSM3db7RProductCancellationLedger Cell p A P wp W E K T M S H
  derivationStatus : SM3eRr3c2TraceCancellationDerivationStatus
  ledgerStatus : SM3eRr3c2LedgerStatus
  noProductIdentityProofStatus : SM3eRReRunNoProductIdentityProofStatus
  sm3fGateStatus : SM3eRReRunSM3fGateStatus
  traceCancellationDerivation_eq :
    traceCancellationDerivation =
      traceCancellationDerivation_from_accumulatedEntryCancellationInvariant H accumulatedEntryCancellation
  traceCancellationInvariant_eq :
    traceCancellationInvariant =
      traceCancellationInvariant_from_accumulatedEntryCancellationInvariant H accumulatedEntryCancellation
  productCancellationLedger_eq :
    productCancellationLedger =
      productCancellationLedger_from_accumulatedEntryCancellationInvariant H accumulatedEntryCancellation
  derivationStatus_eq :
    derivationStatus =
      SM3eRr3c2TraceCancellationDerivationStatus.traceCancellationDerivationFromR3c1AccumulatedInvariant
  ledgerStatus_eq :
    ledgerStatus =
      SM3eRr3c2LedgerStatus.productCancellationLedgerFromR3c1AccumulatedInvariant
  noProductIdentityProofStatus_eq :
    noProductIdentityProofStatus =
      SM3eRReRunNoProductIdentityProofStatus.noProductIdentityProofConstructedInR3b
  sm3fGateStatus_eq :
    sm3fGateStatus = SM3eRReRunSM3fGateStatus.sm3fBlockedUntilHandoffTwoSidedInv

namespace SM3eRr3c2TraceCancellationLedger

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


def fromAccumulatedEntryCancellationInvariant
    (H : SM3dbRToSM3eRHandoff Cell p A P wp W E K T M S)
    (C : GeneratedInteriorAccumulatedEntryCancellationInvariant Cell p A P wp W E K T) :
    SM3eRr3c2TraceCancellationLedger Cell p A P wp W E K T M S H where
  accumulatedEntryCancellation := C
  traceCancellationDerivation :=
    traceCancellationDerivation_from_accumulatedEntryCancellationInvariant H C
  traceCancellationInvariant :=
    traceCancellationInvariant_from_accumulatedEntryCancellationInvariant H C
  productCancellationLedger :=
    productCancellationLedger_from_accumulatedEntryCancellationInvariant H C
  derivationStatus :=
    SM3eRr3c2TraceCancellationDerivationStatus.traceCancellationDerivationFromR3c1AccumulatedInvariant
  ledgerStatus :=
    SM3eRr3c2LedgerStatus.productCancellationLedgerFromR3c1AccumulatedInvariant
  noProductIdentityProofStatus :=
    SM3eRReRunNoProductIdentityProofStatus.noProductIdentityProofConstructedInR3b
  sm3fGateStatus := SM3eRReRunSM3fGateStatus.sm3fBlockedUntilHandoffTwoSidedInv
  traceCancellationDerivation_eq := by
    rfl
  traceCancellationInvariant_eq := by
    rfl
  productCancellationLedger_eq := by
    rfl
  derivationStatus_eq := by
    rfl
  ledgerStatus_eq := by
    rfl
  noProductIdentityProofStatus_eq := by
    rfl
  sm3fGateStatus_eq := by
    rfl

end SM3eRr3c2TraceCancellationLedger

def regularTraceCancellationDerivation_from_accumulatedEntryCancellationInvariant
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy)
    (C : RegularGeneratedInteriorAccumulatedEntryCancellationInvariant b p wp) :
    GeneratedInteriorSM3db7RTraceCancellationDerivation
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
  traceCancellationDerivation_from_accumulatedEntryCancellationInvariant
    (regularSM3dbRToSM3eRHandoff b p wp) C

def variableTraceCancellationDerivation_from_accumulatedEntryCancellationInvariant
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy)
    (C : VariableGeneratedInteriorAccumulatedEntryCancellationInvariant β p wp) :
    GeneratedInteriorSM3db7RTraceCancellationDerivation
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
  traceCancellationDerivation_from_accumulatedEntryCancellationInvariant
    (variableSM3dbRToSM3eRHandoff β p wp) C


def regularTraceCancellationInvariant_from_accumulatedEntryCancellationInvariant
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy)
    (C : RegularGeneratedInteriorAccumulatedEntryCancellationInvariant b p wp) :
    GeneratedInteriorSM3db7RTraceCancellationInvariant
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
  traceCancellationInvariant_from_accumulatedEntryCancellationInvariant
    (regularSM3dbRToSM3eRHandoff b p wp) C

def variableTraceCancellationInvariant_from_accumulatedEntryCancellationInvariant
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy)
    (C : VariableGeneratedInteriorAccumulatedEntryCancellationInvariant β p wp) :
    GeneratedInteriorSM3db7RTraceCancellationInvariant
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
  traceCancellationInvariant_from_accumulatedEntryCancellationInvariant
    (variableSM3dbRToSM3eRHandoff β p wp) C

def regularProductCancellationLedger_from_accumulatedEntryCancellationInvariant
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy)
    (C : RegularGeneratedInteriorAccumulatedEntryCancellationInvariant b p wp) :
    GeneratedInteriorSM3db7RProductCancellationLedger
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
  productCancellationLedger_from_accumulatedEntryCancellationInvariant
    (regularSM3dbRToSM3eRHandoff b p wp) C

def variableProductCancellationLedger_from_accumulatedEntryCancellationInvariant
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy)
    (C : VariableGeneratedInteriorAccumulatedEntryCancellationInvariant β p wp) :
    GeneratedInteriorSM3db7RProductCancellationLedger
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
  productCancellationLedger_from_accumulatedEntryCancellationInvariant
    (variableSM3dbRToSM3eRHandoff β p wp) C

def regularTraceCancellationLedger_from_accumulatedEntryCancellationInvariant
    (b : Nat) (p : ConcretePolicyOf) (wp : WeightPolicy)
    (C : RegularGeneratedInteriorAccumulatedEntryCancellationInvariant b p wp) :
    SM3eRr3c2TraceCancellationLedger
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
  SM3eRr3c2TraceCancellationLedger.fromAccumulatedEntryCancellationInvariant
    (regularSM3dbRToSM3eRHandoff b p wp) C

def variableTraceCancellationLedger_from_accumulatedEntryCancellationInvariant
    (β : Nat → Nat) (p : ConcretePolicyOf) (wp : WeightPolicy)
    (C : VariableGeneratedInteriorAccumulatedEntryCancellationInvariant β p wp) :
    SM3eRr3c2TraceCancellationLedger
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
  SM3eRr3c2TraceCancellationLedger.fromAccumulatedEntryCancellationInvariant
    (variableSM3dbRToSM3eRHandoff β p wp) C


def sm3eRReRunGeneratedProductCancellationLedger_from_accumulatedEntryCancellationLedger
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight) :
    SM3eRReRunGeneratedProductCancellationLedger b β p regularWeight variableWeight :=
  sm3eRReRunGeneratedProductCancellationLedger
    b β p regularWeight variableWeight
    (regularTraceCancellationInvariant_from_accumulatedEntryCancellationInvariant
      b p regularWeight L.regularCancellation)
    (variableTraceCancellationInvariant_from_accumulatedEntryCancellationInvariant
      β p variableWeight L.variableCancellation)

def sm3eRReRunGeneratedProductCancellationLedger_from_terminalIdentityLedgerR3c1d
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1dTerminalIdentityLedger b β p regularWeight variableWeight) :
    SM3eRReRunGeneratedProductCancellationLedger b β p regularWeight variableWeight :=
  sm3eRReRunGeneratedProductCancellationLedger_from_accumulatedEntryCancellationLedger
    (accumulatedEntryCancellationLedger_from_terminalIdentityLedgerR3c1d L)

theorem sm3eRReRunGeneratedProductCancellationLedger_from_accumulated_regular_status
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight) :
    (sm3eRReRunGeneratedProductCancellationLedger_from_accumulatedEntryCancellationLedger
      L).regularProductCancellationLedger.status =
      SM3eRReRunProductCancellationLedgerStatus.productCancellationLedgerFromTraceCancellation := by
  rfl

theorem sm3eRReRunGeneratedProductCancellationLedger_from_accumulated_variable_sm3f_blocked
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    {regularWeight variableWeight : WeightPolicy}
    (L : SM3eRr3c1AccumulatedEntryCancellationLedger b β p regularWeight variableWeight) :
    (sm3eRReRunGeneratedProductCancellationLedger_from_accumulatedEntryCancellationLedger
      L).variableProductCancellationLedger.sm3fGateStatus =
      SM3eRReRunSM3fGateStatus.sm3fBlockedUntilHandoffTwoSidedInv := by
  rfl

end Smoke

end CNNA.PillarA.Arithmetic
