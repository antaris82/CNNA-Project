import CNNA.PillarA.Arithmetic.Smoke.GeneratedSource

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

namespace Smoke

universe u

inductive SM1RGeneratedPipelineStatus where
  | generatedToCSubstratePipeline
  deriving DecidableEq, Repr

inductive SM1RGeneratedPipelineAgreement where
  | sameGeneratedToCPipeline
  deriving DecidableEq, Repr

inductive SM1RGeneratedVariationStatus where
  | noArithmeticSpecialVariation
  deriving DecidableEq, Repr

inductive SM1RPolicyProvenanceStatus where
  | concretePolicyCarriedByGeneratedMainPath
  deriving DecidableEq, Repr

inductive SM1RWeightProvenanceStatus where
  | weightDeferredToGeneratedEntryLemmas
  deriving DecidableEq, Repr

inductive SM1RFreeWeightStatus where
  | noFreeWeightFunctionInSM1R
  deriving DecidableEq, Repr

inductive SM1RCutSpecCarrierClaimStatus where
  | noCutSpecCarrierClaimInSM1R
  deriving DecidableEq, Repr

inductive SM1RMatrixDataStatus where
  | noMatrixDataYetInSM1R
  deriving DecidableEq, Repr

inductive SM1RBoundaryPortsStatus where
  | noBoundaryPortsImportInSM1R
  deriving DecidableEq, Repr

structure SM1RPolicyProvenanceHook (p : ConcretePolicyOf) where
  status : SM1RPolicyProvenanceStatus
  policy : ConcretePolicyOf
  policy_eq_input : policy = p
  cutSpecCarrierClaimStatus : SM1RCutSpecCarrierClaimStatus

structure SM1RWeightProvenanceHook where
  status : SM1RWeightProvenanceStatus
  freeWeightStatus : SM1RFreeWeightStatus
  cutSpecCarrierClaimStatus : SM1RCutSpecCarrierClaimStatus
  matrixDataStatus : SM1RMatrixDataStatus

def policyProvenanceHook (p : ConcretePolicyOf) :
    SM1RPolicyProvenanceHook p where
  status := SM1RPolicyProvenanceStatus.concretePolicyCarriedByGeneratedMainPath
  policy := p
  policy_eq_input := by
    rfl
  cutSpecCarrierClaimStatus :=
    SM1RCutSpecCarrierClaimStatus.noCutSpecCarrierClaimInSM1R

def weightProvenanceHook : SM1RWeightProvenanceHook where
  status := SM1RWeightProvenanceStatus.weightDeferredToGeneratedEntryLemmas
  freeWeightStatus := SM1RFreeWeightStatus.noFreeWeightFunctionInSM1R
  cutSpecCarrierClaimStatus :=
    SM1RCutSpecCarrierClaimStatus.noCutSpecCarrierClaimInSM1R
  matrixDataStatus := SM1RMatrixDataStatus.noMatrixDataYetInSM1R

structure GeneratedMainPath
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf) where
  family : DirectedFamily (Cell := Cell)
  toc : ToCStrongOf Cell
  family_eq_generated : family = generatedBranchFamily Cell
  toc_eq_generated : toc = generatedBranchToC Cell
  carrier_eq_univ : ∀ L : Nat, family.carrier L = Finset.univ
  approximant_carrier_eq_univ_of_le : ∀ {L : Nat}, L ≤ p.L_max →
    (toc.approximant p).carrier L = Finset.univ
  pipelineStatus : SM1RGeneratedPipelineStatus
  policyHook : SM1RPolicyProvenanceHook p
  weightHook : SM1RWeightProvenanceHook
  boundaryPortsStatus : SM1RBoundaryPortsStatus
  cutSpecCarrierClaimStatus : SM1RCutSpecCarrierClaimStatus
  matrixDataStatus : SM1RMatrixDataStatus
  pipelineStatus_eq_generated :
    pipelineStatus = SM1RGeneratedPipelineStatus.generatedToCSubstratePipeline
  policyHook_eq : policyHook = policyProvenanceHook p
  weightHook_eq : weightHook = weightProvenanceHook
  noBoundaryPortsImport :
    boundaryPortsStatus = SM1RBoundaryPortsStatus.noBoundaryPortsImportInSM1R
  noCutSpecCarrierClaim_proof :
    cutSpecCarrierClaimStatus =
      SM1RCutSpecCarrierClaimStatus.noCutSpecCarrierClaimInSM1R
  noMatrixDataYet_proof :
    matrixDataStatus = SM1RMatrixDataStatus.noMatrixDataYetInSM1R

def generatedMainPath
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf) :
    GeneratedMainPath Cell p where
  family := generatedBranchFamily Cell
  toc := generatedBranchToC Cell
  family_eq_generated := by
    rfl
  toc_eq_generated := by
    rfl
  carrier_eq_univ := by
    intro L
    exact generatedBranchFamily_carrier (Cell := Cell) L
  approximant_carrier_eq_univ_of_le := by
    intro L hL
    exact generatedBranchToC_approximant_carrier_of_le
      (Cell := Cell) (p := p) hL
  pipelineStatus := SM1RGeneratedPipelineStatus.generatedToCSubstratePipeline
  policyHook := policyProvenanceHook p
  weightHook := weightProvenanceHook
  boundaryPortsStatus := SM1RBoundaryPortsStatus.noBoundaryPortsImportInSM1R
  cutSpecCarrierClaimStatus :=
    SM1RCutSpecCarrierClaimStatus.noCutSpecCarrierClaimInSM1R
  matrixDataStatus := SM1RMatrixDataStatus.noMatrixDataYetInSM1R
  pipelineStatus_eq_generated := by
    rfl
  policyHook_eq := by
    rfl
  weightHook_eq := by
    rfl
  noBoundaryPortsImport := by
    rfl
  noCutSpecCarrierClaim_proof := by
    rfl
  noMatrixDataYet_proof := by
    rfl

def regularGeneratedMainPath (b : Nat) (p : ConcretePolicyOf) :
    GeneratedMainPath (ConcreteSubstrate.RegularCell b) p :=
  generatedMainPath (ConcreteSubstrate.RegularCell b) p

def variableGeneratedMainPath (β : Nat → Nat) (p : ConcretePolicyOf) :
    GeneratedMainPath (LevelVariableSubstrate.LevelVariableCell β) p :=
  generatedMainPath (LevelVariableSubstrate.LevelVariableCell β) p

structure RegularVariableGeneratedPathPair
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf) where
  regular : GeneratedMainPath (ConcreteSubstrate.RegularCell b) p
  variablePath : GeneratedMainPath (LevelVariableSubstrate.LevelVariableCell β) p
  regular_eq_main : regular = regularGeneratedMainPath b p
  variable_eq_main : variablePath = variableGeneratedMainPath β p
  pipelineAgreement : SM1RGeneratedPipelineAgreement
  pipelineAgreement_eq_same :
    pipelineAgreement = SM1RGeneratedPipelineAgreement.sameGeneratedToCPipeline
  variationStatus : SM1RGeneratedVariationStatus
  noArithmeticSpecialVariation_proof :
    variationStatus = SM1RGeneratedVariationStatus.noArithmeticSpecialVariation
  regularPolicyHook_eq : regular.policyHook = policyProvenanceHook p
  variablePolicyHook_eq : variablePath.policyHook = policyProvenanceHook p
  regularWeightHook_eq : regular.weightHook = weightProvenanceHook
  variableWeightHook_eq : variablePath.weightHook = weightProvenanceHook
  regularNoCutSpecCarrierClaim :
    regular.cutSpecCarrierClaimStatus =
      SM1RCutSpecCarrierClaimStatus.noCutSpecCarrierClaimInSM1R
  variableNoCutSpecCarrierClaim :
    variablePath.cutSpecCarrierClaimStatus =
      SM1RCutSpecCarrierClaimStatus.noCutSpecCarrierClaimInSM1R
  regularNoMatrixDataYet :
    regular.matrixDataStatus = SM1RMatrixDataStatus.noMatrixDataYetInSM1R
  variableNoMatrixDataYet :
    variablePath.matrixDataStatus = SM1RMatrixDataStatus.noMatrixDataYetInSM1R

def regularVariableGeneratedPathPair
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf) :
    RegularVariableGeneratedPathPair b β p where
  regular := regularGeneratedMainPath b p
  variablePath := variableGeneratedMainPath β p
  regular_eq_main := by
    rfl
  variable_eq_main := by
    rfl
  pipelineAgreement := SM1RGeneratedPipelineAgreement.sameGeneratedToCPipeline
  pipelineAgreement_eq_same := by
    rfl
  variationStatus := SM1RGeneratedVariationStatus.noArithmeticSpecialVariation
  noArithmeticSpecialVariation_proof := by
    rfl
  regularPolicyHook_eq := by
    rfl
  variablePolicyHook_eq := by
    rfl
  regularWeightHook_eq := by
    rfl
  variableWeightHook_eq := by
    rfl
  regularNoCutSpecCarrierClaim := by
    rfl
  variableNoCutSpecCarrierClaim := by
    rfl
  regularNoMatrixDataYet := by
    rfl
  variableNoMatrixDataYet := by
    rfl

theorem GeneratedMainPath.pipeline_eq_generated
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf} (P : GeneratedMainPath Cell p) :
    P.pipelineStatus =
      SM1RGeneratedPipelineStatus.generatedToCSubstratePipeline :=
  P.pipelineStatus_eq_generated

theorem GeneratedMainPath.policy_hook_eq
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf} (P : GeneratedMainPath Cell p) :
    P.policyHook = policyProvenanceHook p :=
  P.policyHook_eq

theorem GeneratedMainPath.weight_hook_eq
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf} (P : GeneratedMainPath Cell p) :
    P.weightHook = weightProvenanceHook :=
  P.weightHook_eq

theorem noCutSpecCarrierClaim
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf} (P : GeneratedMainPath Cell p) :
    P.cutSpecCarrierClaimStatus =
      SM1RCutSpecCarrierClaimStatus.noCutSpecCarrierClaimInSM1R :=
  P.noCutSpecCarrierClaim_proof

theorem noMatrixDataYet
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf} (P : GeneratedMainPath Cell p) :
    P.matrixDataStatus = SM1RMatrixDataStatus.noMatrixDataYetInSM1R :=
  P.noMatrixDataYet_proof

theorem regularGeneratedMainPath_toc
    (b : Nat) (p : ConcretePolicyOf) :
    (regularGeneratedMainPath b p).toc = regularGeneratedToC b := by
  rfl

theorem variableGeneratedMainPath_toc
    (β : Nat → Nat) (p : ConcretePolicyOf) :
    (variableGeneratedMainPath β p).toc = variableGeneratedToC β := by
  rfl

theorem regularGeneratedMainPath_family
    (b : Nat) (p : ConcretePolicyOf) :
    (regularGeneratedMainPath b p).family = regularGeneratedFamily b := by
  rfl

theorem variableGeneratedMainPath_family
    (β : Nat → Nat) (p : ConcretePolicyOf) :
    (variableGeneratedMainPath β p).family = variableGeneratedFamily β := by
  rfl

theorem regularGeneratedMainPath_carrier_eq_univ
    (b : Nat) (p : ConcretePolicyOf) (L : Nat) :
    (regularGeneratedMainPath b p).family.carrier L = Finset.univ := by
  rfl

theorem variableGeneratedMainPath_carrier_eq_univ
    (β : Nat → Nat) (p : ConcretePolicyOf) (L : Nat) :
    (variableGeneratedMainPath β p).family.carrier L = Finset.univ := by
  rfl

theorem regularGeneratedMainPath_approximant_carrier_eq_univ_of_le
    (b : Nat) {p : ConcretePolicyOf} {L : Nat} (hL : L ≤ p.L_max) :
    ((regularGeneratedMainPath b p).toc.approximant p).carrier L = Finset.univ := by
  exact regularGeneratedToC_approximant_carrier_of_le (b := b) (p := p) hL

theorem variableGeneratedMainPath_approximant_carrier_eq_univ_of_le
    (β : Nat → Nat) {p : ConcretePolicyOf} {L : Nat} (hL : L ≤ p.L_max) :
    ((variableGeneratedMainPath β p).toc.approximant p).carrier L = Finset.univ := by
  exact variableGeneratedToC_approximant_carrier_of_le (β := β) (p := p) hL

theorem sameGeneratedToCPipeline
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    (P : RegularVariableGeneratedPathPair b β p) :
    P.pipelineAgreement =
      SM1RGeneratedPipelineAgreement.sameGeneratedToCPipeline :=
  P.pipelineAgreement_eq_same

theorem noArithmeticSpecialVariation
    {b : Nat} {β : Nat → Nat} {p : ConcretePolicyOf}
    (P : RegularVariableGeneratedPathPair b β p) :
    P.variationStatus =
      SM1RGeneratedVariationStatus.noArithmeticSpecialVariation :=
  P.noArithmeticSpecialVariation_proof

inductive SM1RGeneratedVariationLedgerStatus where
  | generatedRegularVariableProvenanceClosed
  deriving DecidableEq, Repr

structure SM1RGeneratedVariationLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf) where
  status : SM1RGeneratedVariationLedgerStatus
  pair : RegularVariableGeneratedPathPair b β p
  pair_eq_main : pair = regularVariableGeneratedPathPair b β p
  samePipeline :
    pair.pipelineAgreement =
      SM1RGeneratedPipelineAgreement.sameGeneratedToCPipeline
  noSpecialVariation :
    pair.variationStatus =
      SM1RGeneratedVariationStatus.noArithmeticSpecialVariation
  regularPolicyHook : pair.regular.policyHook = policyProvenanceHook p
  variablePolicyHook : pair.variablePath.policyHook = policyProvenanceHook p
  regularWeightHook : pair.regular.weightHook = weightProvenanceHook
  variableWeightHook : pair.variablePath.weightHook = weightProvenanceHook
  regularNoCutSpecCarrierClaim :
    pair.regular.cutSpecCarrierClaimStatus =
      SM1RCutSpecCarrierClaimStatus.noCutSpecCarrierClaimInSM1R
  variableNoCutSpecCarrierClaim :
    pair.variablePath.cutSpecCarrierClaimStatus =
      SM1RCutSpecCarrierClaimStatus.noCutSpecCarrierClaimInSM1R
  regularNoMatrixDataYet :
    pair.regular.matrixDataStatus = SM1RMatrixDataStatus.noMatrixDataYetInSM1R
  variableNoMatrixDataYet :
    pair.variablePath.matrixDataStatus = SM1RMatrixDataStatus.noMatrixDataYetInSM1R

def sm1RGeneratedVariationLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf) :
    SM1RGeneratedVariationLedger b β p where
  status :=
    SM1RGeneratedVariationLedgerStatus.generatedRegularVariableProvenanceClosed
  pair := regularVariableGeneratedPathPair b β p
  pair_eq_main := by
    rfl
  samePipeline := by
    rfl
  noSpecialVariation := by
    rfl
  regularPolicyHook := by
    rfl
  variablePolicyHook := by
    rfl
  regularWeightHook := by
    rfl
  variableWeightHook := by
    rfl
  regularNoCutSpecCarrierClaim := by
    rfl
  variableNoCutSpecCarrierClaim := by
    rfl
  regularNoMatrixDataYet := by
    rfl
  variableNoMatrixDataYet := by
    rfl

theorem sm1RGeneratedVariationLedger_status
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf) :
    (sm1RGeneratedVariationLedger b β p).status =
      SM1RGeneratedVariationLedgerStatus.generatedRegularVariableProvenanceClosed := by
  rfl

theorem sm1RGeneratedVariationLedger_samePipeline
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf) :
    (sm1RGeneratedVariationLedger b β p).pair.pipelineAgreement =
      SM1RGeneratedPipelineAgreement.sameGeneratedToCPipeline := by
  rfl

theorem sm1RGeneratedVariationLedger_noSpecialVariation
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf) :
    (sm1RGeneratedVariationLedger b β p).pair.variationStatus =
      SM1RGeneratedVariationStatus.noArithmeticSpecialVariation := by
  rfl

theorem sm1RGeneratedVariationLedger_regularNoMatrixDataYet
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf) :
    (sm1RGeneratedVariationLedger b β p).pair.regular.matrixDataStatus =
      SM1RMatrixDataStatus.noMatrixDataYetInSM1R := by
  rfl

theorem sm1RGeneratedVariationLedger_variableNoMatrixDataYet
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf) :
    (sm1RGeneratedVariationLedger b β p).pair.variablePath.matrixDataStatus =
      SM1RMatrixDataStatus.noMatrixDataYetInSM1R := by
  rfl

end Smoke

end CNNA.PillarA.Arithmetic
