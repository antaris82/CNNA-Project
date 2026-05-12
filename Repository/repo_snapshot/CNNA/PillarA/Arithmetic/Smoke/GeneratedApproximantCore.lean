import CNNA.PillarA.Arithmetic.Smoke.GeneratedMainPath

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

namespace Smoke

universe u

inductive SM2RApproximantRoute where
  | generatedToCSubstrate
  deriving DecidableEq, Repr

inductive SM2RCarrierProvenanceStatus where
  | carrierFromGeneratedMainPath
  deriving DecidableEq, Repr

inductive SM2RCutoffProvenanceStatus where
  | cutoffFromConcretePolicy
  deriving DecidableEq, Repr

inductive SM2RTruncationProvenanceStatus where
  | approximantEqualsGeneratedMainPathTruncation
  deriving DecidableEq, Repr

inductive SM2RFiniteCarrierAPIStatus where
  | substrateFintypeAndDecidableEqForwarded
  deriving DecidableEq, Repr

inductive SM2RBoundaryPortsCoreStatus where
  | noBoundaryPortsInCore
  deriving DecidableEq, Repr

inductive SM2RCutSpecCoreStatus where
  | noCutSpecInCore
  deriving DecidableEq, Repr

inductive SM2RMatrixDataStatus where
  | noMatrixDataYet
  deriving DecidableEq, Repr

inductive SM2RDirichletDataStatus where
  | noDirichletDataYet
  deriving DecidableEq, Repr

inductive SM2RDtnDataStatus where
  | noDtNDataYet
  deriving DecidableEq, Repr

inductive SM2RDiscriminantDataStatus where
  | noDiscriminantOrTargetDataYet
  deriving DecidableEq, Repr

inductive SM2RGeneratedApproximantLedgerStatus where
  | generatedApproximantCoreClosed
  deriving DecidableEq, Repr

theorem GeneratedMainPath.approximant_eq_truncate
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf} (P : GeneratedMainPath Cell p) :
    P.toc.approximant p = P.family.truncate p.L_max := by
  calc
    P.toc.approximant p = (generatedBranchToC Cell).approximant p := by
      rw [P.toc_eq_generated]
    _ = (generatedBranchFamily Cell).truncate p.L_max := by
      exact ToCStrong.approximant_eq_truncate
        (T := generatedBranchToC Cell) p
    _ = P.family.truncate p.L_max := by
      rw [P.family_eq_generated]

structure GeneratedFiniteCarrierAPI
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  carrier : ∀ L : Nat, Finset (Cell L)
  carrier_eq_approximant : ∀ L : Nat, carrier L = T.carrier L
  decidableEqCarrier : ∀ L : Nat, DecidableEq (Cell L)
  fintypeCarrier : ∀ L : Nat, Fintype (Cell L)
  decidableMemCarrier : ∀ L : Nat, ∀ x : Cell L, Decidable (x ∈ T.carrier L)
  status : SM2RFiniteCarrierAPIStatus
  status_eq_forwarded :
    status = SM2RFiniteCarrierAPIStatus.substrateFintypeAndDecidableEqForwarded

namespace GeneratedFiniteCarrierAPI

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable (T : TruncatedFamily Cell)

def ofTruncatedFamily : GeneratedFiniteCarrierAPI Cell T where
  carrier := T.carrier
  carrier_eq_approximant := by
    intro L
    rfl
  decidableEqCarrier := by
    intro L
    infer_instance
  fintypeCarrier := by
    intro L
    infer_instance
  decidableMemCarrier := by
    intro L x
    infer_instance
  status := SM2RFiniteCarrierAPIStatus.substrateFintypeAndDecidableEqForwarded
  status_eq_forwarded := by
    rfl

theorem carrier_eq
    (A : GeneratedFiniteCarrierAPI Cell T) (L : Nat) :
    A.carrier L = T.carrier L :=
  A.carrier_eq_approximant L

theorem status_forwarded
    (A : GeneratedFiniteCarrierAPI Cell T) :
    A.status = SM2RFiniteCarrierAPIStatus.substrateFintypeAndDecidableEqForwarded :=
  A.status_eq_forwarded

end GeneratedFiniteCarrierAPI

structure GeneratedTruncationWitness
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {p : ConcretePolicyOf}
    (P : GeneratedMainPath Cell p)
    (T : TruncatedFamily Cell) where
  approximant_eq_mainPath : T = P.toc.approximant p
  approximant_eq_truncate : T = P.family.truncate p.L_max
  cutoff_eq_policy : T.cutoff = p.L_max
  carrier_from_mainPath : ∀ {L : Nat}, L ≤ p.L_max →
    T.carrier L = P.family.carrier L
  carrier_eq_univ_of_le : ∀ {L : Nat}, L ≤ p.L_max →
    T.carrier L = Finset.univ
  carrier_empty_of_gt : ∀ {L : Nat}, p.L_max < L →
    T.carrier L = ∅
  carrierProvenanceStatus : SM2RCarrierProvenanceStatus
  cutoffProvenanceStatus : SM2RCutoffProvenanceStatus
  truncationProvenanceStatus : SM2RTruncationProvenanceStatus
  carrierProvenanceStatus_eq :
    carrierProvenanceStatus = SM2RCarrierProvenanceStatus.carrierFromGeneratedMainPath
  cutoffProvenanceStatus_eq :
    cutoffProvenanceStatus = SM2RCutoffProvenanceStatus.cutoffFromConcretePolicy
  truncationProvenanceStatus_eq :
    truncationProvenanceStatus =
      SM2RTruncationProvenanceStatus.approximantEqualsGeneratedMainPathTruncation

namespace GeneratedTruncationWitness

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {p : ConcretePolicyOf}

def ofMainPath (P : GeneratedMainPath Cell p) :
    GeneratedTruncationWitness P (P.toc.approximant p) where
  approximant_eq_mainPath := by
    rfl
  approximant_eq_truncate := by
    exact GeneratedMainPath.approximant_eq_truncate P
  cutoff_eq_policy := by
    rw [GeneratedMainPath.approximant_eq_truncate P]
    rfl
  carrier_from_mainPath := by
    intro L hL
    rw [GeneratedMainPath.approximant_eq_truncate P]
    exact DirectedFamily.truncate_carrier_of_le (F := P.family) hL
  carrier_eq_univ_of_le := by
    intro L hL
    exact P.approximant_carrier_eq_univ_of_le hL
  carrier_empty_of_gt := by
    intro L hL
    rw [GeneratedMainPath.approximant_eq_truncate P]
    exact DirectedFamily.truncate_carrier_of_gt (F := P.family) hL
  carrierProvenanceStatus := SM2RCarrierProvenanceStatus.carrierFromGeneratedMainPath
  cutoffProvenanceStatus := SM2RCutoffProvenanceStatus.cutoffFromConcretePolicy
  truncationProvenanceStatus :=
    SM2RTruncationProvenanceStatus.approximantEqualsGeneratedMainPathTruncation
  carrierProvenanceStatus_eq := by
    rfl
  cutoffProvenanceStatus_eq := by
    rfl
  truncationProvenanceStatus_eq := by
    rfl

theorem cutoff_from_policy
    {P : GeneratedMainPath Cell p} {T : TruncatedFamily Cell}
    (W : GeneratedTruncationWitness P T) :
    T.cutoff = p.L_max :=
  W.cutoff_eq_policy

theorem carrier_eq_univ
    {P : GeneratedMainPath Cell p} {T : TruncatedFamily Cell}
    (W : GeneratedTruncationWitness P T) {L : Nat}
    (hL : L ≤ p.L_max) :
    T.carrier L = Finset.univ :=
  W.carrier_eq_univ_of_le hL

end GeneratedTruncationWitness

structure GeneratedApproximantStrong
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf) where
  mainPath : GeneratedMainPath Cell p
  approximant : TruncatedFamily Cell
  approximant_eq_mainPath : approximant = mainPath.toc.approximant p
  approximant_eq_truncate : approximant = mainPath.family.truncate p.L_max
  route : SM2RApproximantRoute
  route_eq_generated : route = SM2RApproximantRoute.generatedToCSubstrate
  truncationWitness : GeneratedTruncationWitness mainPath approximant
  finiteCarrierAPI : GeneratedFiniteCarrierAPI Cell approximant
  boundaryPortsStatus : SM2RBoundaryPortsCoreStatus
  cutSpecStatus : SM2RCutSpecCoreStatus
  matrixDataStatus : SM2RMatrixDataStatus
  dirichletDataStatus : SM2RDirichletDataStatus
  dtnDataStatus : SM2RDtnDataStatus
  discriminantDataStatus : SM2RDiscriminantDataStatus
  noBoundaryPortsInCore :
    boundaryPortsStatus = SM2RBoundaryPortsCoreStatus.noBoundaryPortsInCore
  noCutSpecInCore :
    cutSpecStatus = SM2RCutSpecCoreStatus.noCutSpecInCore
  noMatrixDataYet :
    matrixDataStatus = SM2RMatrixDataStatus.noMatrixDataYet
  noDirichletDataYet :
    dirichletDataStatus = SM2RDirichletDataStatus.noDirichletDataYet
  noDtNDataYet :
    dtnDataStatus = SM2RDtnDataStatus.noDtNDataYet
  noDiscriminantOrTargetDataYet :
    discriminantDataStatus =
      SM2RDiscriminantDataStatus.noDiscriminantOrTargetDataYet

namespace GeneratedApproximantStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {p : ConcretePolicyOf}

def fromMainPath (P : GeneratedMainPath Cell p) :
    GeneratedApproximantStrong Cell p where
  mainPath := P
  approximant := P.toc.approximant p
  approximant_eq_mainPath := by
    rfl
  approximant_eq_truncate := by
    exact GeneratedMainPath.approximant_eq_truncate P
  route := SM2RApproximantRoute.generatedToCSubstrate
  route_eq_generated := by
    rfl
  truncationWitness := GeneratedTruncationWitness.ofMainPath P
  finiteCarrierAPI := GeneratedFiniteCarrierAPI.ofTruncatedFamily (P.toc.approximant p)
  boundaryPortsStatus := SM2RBoundaryPortsCoreStatus.noBoundaryPortsInCore
  cutSpecStatus := SM2RCutSpecCoreStatus.noCutSpecInCore
  matrixDataStatus := SM2RMatrixDataStatus.noMatrixDataYet
  dirichletDataStatus := SM2RDirichletDataStatus.noDirichletDataYet
  dtnDataStatus := SM2RDtnDataStatus.noDtNDataYet
  discriminantDataStatus := SM2RDiscriminantDataStatus.noDiscriminantOrTargetDataYet
  noBoundaryPortsInCore := by
    rfl
  noCutSpecInCore := by
    rfl
  noMatrixDataYet := by
    rfl
  noDirichletDataYet := by
    rfl
  noDtNDataYet := by
    rfl
  noDiscriminantOrTargetDataYet := by
    rfl

theorem route_generated
    (A : GeneratedApproximantStrong Cell p) :
    A.route = SM2RApproximantRoute.generatedToCSubstrate :=
  A.route_eq_generated

theorem cutoff_from_policy
    (A : GeneratedApproximantStrong Cell p) :
    A.approximant.cutoff = p.L_max :=
  A.truncationWitness.cutoff_eq_policy

theorem carrier_from_mainPath
    (A : GeneratedApproximantStrong Cell p) {L : Nat}
    (hL : L ≤ p.L_max) :
    A.approximant.carrier L = A.mainPath.family.carrier L :=
  A.truncationWitness.carrier_from_mainPath hL

theorem carrier_eq_univ_of_le
    (A : GeneratedApproximantStrong Cell p) {L : Nat}
    (hL : L ≤ p.L_max) :
    A.approximant.carrier L = Finset.univ :=
  A.truncationWitness.carrier_eq_univ_of_le hL

theorem carrier_empty_of_gt
    (A : GeneratedApproximantStrong Cell p) {L : Nat}
    (hL : p.L_max < L) :
    A.approximant.carrier L = ∅ :=
  A.truncationWitness.carrier_empty_of_gt hL

theorem finiteCarrierAPI_status
    (A : GeneratedApproximantStrong Cell p) :
    A.finiteCarrierAPI.status =
      SM2RFiniteCarrierAPIStatus.substrateFintypeAndDecidableEqForwarded :=
  A.finiteCarrierAPI.status_eq_forwarded

theorem no_boundary_ports
    (A : GeneratedApproximantStrong Cell p) :
    A.boundaryPortsStatus = SM2RBoundaryPortsCoreStatus.noBoundaryPortsInCore :=
  A.noBoundaryPortsInCore

theorem no_cutSpec
    (A : GeneratedApproximantStrong Cell p) :
    A.cutSpecStatus = SM2RCutSpecCoreStatus.noCutSpecInCore :=
  A.noCutSpecInCore

theorem no_matrix_data
    (A : GeneratedApproximantStrong Cell p) :
    A.matrixDataStatus = SM2RMatrixDataStatus.noMatrixDataYet :=
  A.noMatrixDataYet

theorem no_dirichlet_data
    (A : GeneratedApproximantStrong Cell p) :
    A.dirichletDataStatus = SM2RDirichletDataStatus.noDirichletDataYet :=
  A.noDirichletDataYet

end GeneratedApproximantStrong

def generatedApproximantStrong
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (p : ConcretePolicyOf) :
    GeneratedApproximantStrong Cell p :=
  GeneratedApproximantStrong.fromMainPath (generatedMainPath Cell p)

abbrev RegularGeneratedApproximantStrong
    (b : Nat) (p : ConcretePolicyOf) :=
  GeneratedApproximantStrong (ConcreteSubstrate.RegularCell b) p

abbrev VariableGeneratedApproximantStrong
    (β : Nat → Nat) (p : ConcretePolicyOf) :=
  GeneratedApproximantStrong (LevelVariableSubstrate.LevelVariableCell β) p

def regularGeneratedApproximantStrong
    (b : Nat) (p : ConcretePolicyOf) :
    RegularGeneratedApproximantStrong b p :=
  GeneratedApproximantStrong.fromMainPath (regularGeneratedMainPath b p)

def variableGeneratedApproximantStrong
    (β : Nat → Nat) (p : ConcretePolicyOf) :
    VariableGeneratedApproximantStrong β p :=
  GeneratedApproximantStrong.fromMainPath (variableGeneratedMainPath β p)

theorem regularGeneratedApproximantStrong_mainPath
    (b : Nat) (p : ConcretePolicyOf) :
    (regularGeneratedApproximantStrong b p).mainPath =
      regularGeneratedMainPath b p := by
  rfl

theorem variableGeneratedApproximantStrong_mainPath
    (β : Nat → Nat) (p : ConcretePolicyOf) :
    (variableGeneratedApproximantStrong β p).mainPath =
      variableGeneratedMainPath β p := by
  rfl

theorem regularGeneratedApproximantStrong_route
    (b : Nat) (p : ConcretePolicyOf) :
    (regularGeneratedApproximantStrong b p).route =
      SM2RApproximantRoute.generatedToCSubstrate := by
  rfl

theorem variableGeneratedApproximantStrong_route
    (β : Nat → Nat) (p : ConcretePolicyOf) :
    (variableGeneratedApproximantStrong β p).route =
      SM2RApproximantRoute.generatedToCSubstrate := by
  rfl

theorem regularGeneratedApproximantStrong_cutoff
    (b : Nat) (p : ConcretePolicyOf) :
    (regularGeneratedApproximantStrong b p).approximant.cutoff = p.L_max := by
  exact GeneratedApproximantStrong.cutoff_from_policy
    (regularGeneratedApproximantStrong b p)

theorem variableGeneratedApproximantStrong_cutoff
    (β : Nat → Nat) (p : ConcretePolicyOf) :
    (variableGeneratedApproximantStrong β p).approximant.cutoff = p.L_max := by
  exact GeneratedApproximantStrong.cutoff_from_policy
    (variableGeneratedApproximantStrong β p)

theorem regularGeneratedApproximantStrong_carrier_eq_univ_of_le
    (b : Nat) {p : ConcretePolicyOf} {L : Nat} (hL : L ≤ p.L_max) :
    (regularGeneratedApproximantStrong b p).approximant.carrier L = Finset.univ := by
  exact GeneratedApproximantStrong.carrier_eq_univ_of_le
    (regularGeneratedApproximantStrong b p) hL

theorem variableGeneratedApproximantStrong_carrier_eq_univ_of_le
    (β : Nat → Nat) {p : ConcretePolicyOf} {L : Nat} (hL : L ≤ p.L_max) :
    (variableGeneratedApproximantStrong β p).approximant.carrier L = Finset.univ := by
  exact GeneratedApproximantStrong.carrier_eq_univ_of_le
    (variableGeneratedApproximantStrong β p) hL

theorem regularGeneratedApproximantStrong_carrier_empty_of_gt
    (b : Nat) {p : ConcretePolicyOf} {L : Nat} (hL : p.L_max < L) :
    (regularGeneratedApproximantStrong b p).approximant.carrier L = ∅ := by
  exact GeneratedApproximantStrong.carrier_empty_of_gt
    (regularGeneratedApproximantStrong b p) hL

theorem variableGeneratedApproximantStrong_carrier_empty_of_gt
    (β : Nat → Nat) {p : ConcretePolicyOf} {L : Nat} (hL : p.L_max < L) :
    (variableGeneratedApproximantStrong β p).approximant.carrier L = ∅ := by
  exact GeneratedApproximantStrong.carrier_empty_of_gt
    (variableGeneratedApproximantStrong β p) hL

structure SM2RGeneratedApproximantLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf) where
  status : SM2RGeneratedApproximantLedgerStatus
  sm1rLedger : SM1RGeneratedVariationLedger b β p
  regular : RegularGeneratedApproximantStrong b p
  variablePath : VariableGeneratedApproximantStrong β p
  sm1rLedger_eq_main : sm1rLedger = sm1RGeneratedVariationLedger b β p
  regular_eq_main : regular = regularGeneratedApproximantStrong b p
  variable_eq_main : variablePath = variableGeneratedApproximantStrong β p
  regular_mainPath_eq_sm1r : regular.mainPath = sm1rLedger.pair.regular
  variable_mainPath_eq_sm1r : variablePath.mainPath = sm1rLedger.pair.variablePath
  sameGeneratedPipeline :
    sm1rLedger.pair.pipelineAgreement =
      SM1RGeneratedPipelineAgreement.sameGeneratedToCPipeline
  noArithmeticSpecialVariation :
    sm1rLedger.pair.variationStatus =
      SM1RGeneratedVariationStatus.noArithmeticSpecialVariation
  regularRoute : regular.route = SM2RApproximantRoute.generatedToCSubstrate
  variableRoute : variablePath.route = SM2RApproximantRoute.generatedToCSubstrate
  regularCutoff : regular.approximant.cutoff = p.L_max
  variableCutoff : variablePath.approximant.cutoff = p.L_max
  regularFiniteCarrierAPI :
    regular.finiteCarrierAPI.status =
      SM2RFiniteCarrierAPIStatus.substrateFintypeAndDecidableEqForwarded
  variableFiniteCarrierAPI :
    variablePath.finiteCarrierAPI.status =
      SM2RFiniteCarrierAPIStatus.substrateFintypeAndDecidableEqForwarded
  regularNoBoundaryPorts :
    regular.boundaryPortsStatus = SM2RBoundaryPortsCoreStatus.noBoundaryPortsInCore
  variableNoBoundaryPorts :
    variablePath.boundaryPortsStatus = SM2RBoundaryPortsCoreStatus.noBoundaryPortsInCore
  regularNoCutSpec : regular.cutSpecStatus = SM2RCutSpecCoreStatus.noCutSpecInCore
  variableNoCutSpec : variablePath.cutSpecStatus = SM2RCutSpecCoreStatus.noCutSpecInCore
  regularNoMatrixData : regular.matrixDataStatus = SM2RMatrixDataStatus.noMatrixDataYet
  variableNoMatrixData : variablePath.matrixDataStatus = SM2RMatrixDataStatus.noMatrixDataYet
  regularNoDirichletData :
    regular.dirichletDataStatus = SM2RDirichletDataStatus.noDirichletDataYet
  variableNoDirichletData :
    variablePath.dirichletDataStatus = SM2RDirichletDataStatus.noDirichletDataYet
  regularNoDtNData : regular.dtnDataStatus = SM2RDtnDataStatus.noDtNDataYet
  variableNoDtNData : variablePath.dtnDataStatus = SM2RDtnDataStatus.noDtNDataYet
  regularNoDiscriminantOrTargetData :
    regular.discriminantDataStatus =
      SM2RDiscriminantDataStatus.noDiscriminantOrTargetDataYet
  variableNoDiscriminantOrTargetData :
    variablePath.discriminantDataStatus =
      SM2RDiscriminantDataStatus.noDiscriminantOrTargetDataYet
  status_eq_closed :
    status = SM2RGeneratedApproximantLedgerStatus.generatedApproximantCoreClosed

def sm2RGeneratedApproximantLedger
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf) :
    SM2RGeneratedApproximantLedger b β p where
  status := SM2RGeneratedApproximantLedgerStatus.generatedApproximantCoreClosed
  sm1rLedger := sm1RGeneratedVariationLedger b β p
  regular := regularGeneratedApproximantStrong b p
  variablePath := variableGeneratedApproximantStrong β p
  sm1rLedger_eq_main := by
    rfl
  regular_eq_main := by
    rfl
  variable_eq_main := by
    rfl
  regular_mainPath_eq_sm1r := by
    rfl
  variable_mainPath_eq_sm1r := by
    rfl
  sameGeneratedPipeline := by
    rfl
  noArithmeticSpecialVariation := by
    rfl
  regularRoute := by
    rfl
  variableRoute := by
    rfl
  regularCutoff := by
    exact GeneratedApproximantStrong.cutoff_from_policy
      (regularGeneratedApproximantStrong b p)
  variableCutoff := by
    exact GeneratedApproximantStrong.cutoff_from_policy
      (variableGeneratedApproximantStrong β p)
  regularFiniteCarrierAPI := by
    rfl
  variableFiniteCarrierAPI := by
    rfl
  regularNoBoundaryPorts := by
    rfl
  variableNoBoundaryPorts := by
    rfl
  regularNoCutSpec := by
    rfl
  variableNoCutSpec := by
    rfl
  regularNoMatrixData := by
    rfl
  variableNoMatrixData := by
    rfl
  regularNoDirichletData := by
    rfl
  variableNoDirichletData := by
    rfl
  regularNoDtNData := by
    rfl
  variableNoDtNData := by
    rfl
  regularNoDiscriminantOrTargetData := by
    rfl
  variableNoDiscriminantOrTargetData := by
    rfl
  status_eq_closed := by
    rfl

theorem sm2RGeneratedApproximantLedger_status
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf) :
    (sm2RGeneratedApproximantLedger b β p).status =
      SM2RGeneratedApproximantLedgerStatus.generatedApproximantCoreClosed := by
  rfl

theorem sm2RGeneratedApproximantLedger_regularRoute
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf) :
    (sm2RGeneratedApproximantLedger b β p).regular.route =
      SM2RApproximantRoute.generatedToCSubstrate := by
  rfl

theorem sm2RGeneratedApproximantLedger_variableRoute
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf) :
    (sm2RGeneratedApproximantLedger b β p).variablePath.route =
      SM2RApproximantRoute.generatedToCSubstrate := by
  rfl

theorem sm2RGeneratedApproximantLedger_regularNoBoundaryPorts
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf) :
    (sm2RGeneratedApproximantLedger b β p).regular.boundaryPortsStatus =
      SM2RBoundaryPortsCoreStatus.noBoundaryPortsInCore := by
  rfl

theorem sm2RGeneratedApproximantLedger_variableNoBoundaryPorts
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf) :
    (sm2RGeneratedApproximantLedger b β p).variablePath.boundaryPortsStatus =
      SM2RBoundaryPortsCoreStatus.noBoundaryPortsInCore := by
  rfl

theorem sm2RGeneratedApproximantLedger_regularNoDirichletData
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf) :
    (sm2RGeneratedApproximantLedger b β p).regular.dirichletDataStatus =
      SM2RDirichletDataStatus.noDirichletDataYet := by
  rfl

theorem sm2RGeneratedApproximantLedger_variableNoDirichletData
    (b : Nat) (β : Nat → Nat) (p : ConcretePolicyOf) :
    (sm2RGeneratedApproximantLedger b β p).variablePath.dirichletDataStatus =
      SM2RDirichletDataStatus.noDirichletDataYet := by
  rfl

theorem sm2RGeneratedApproximantLedger_regularCarrier_eq_univ_of_le
    (b : Nat) (β : Nat → Nat) {p : ConcretePolicyOf} {L : Nat}
    (hL : L ≤ p.L_max) :
    (sm2RGeneratedApproximantLedger b β p).regular.approximant.carrier L =
      Finset.univ := by
  exact regularGeneratedApproximantStrong_carrier_eq_univ_of_le (b := b) hL

theorem sm2RGeneratedApproximantLedger_variableCarrier_eq_univ_of_le
    (b : Nat) (β : Nat → Nat) {p : ConcretePolicyOf} {L : Nat}
    (hL : L ≤ p.L_max) :
    (sm2RGeneratedApproximantLedger b β p).variablePath.approximant.carrier L =
      Finset.univ := by
  exact variableGeneratedApproximantStrong_carrier_eq_univ_of_le (β := β) hL

end Smoke

end CNNA.PillarA.Arithmetic
