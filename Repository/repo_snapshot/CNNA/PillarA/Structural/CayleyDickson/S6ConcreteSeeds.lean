import CNNA.PillarA.Structural.CayleyDickson.S6StatusLayer

set_option autoImplicit false

namespace CNNA.PillarA.Structural.CayleyDickson

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.Finite
open CNNA.PillarA.DtN
open CNNA.PillarA.Sectors
open CNNA.PillarA.Closure
open CNNA.PillarA.Network
open CNNA.PillarA.Coupling

universe u

inductive PreNumericSectorRole where
  | bright
  | interface
  | dark
  deriving DecidableEq

namespace PreNumericSectorRole

def dual : PreNumericSectorRole → PreNumericSectorRole
  | bright => dark
  | interface => interface
  | dark => bright

theorem dual_bright : dual bright = dark := by
  rfl

theorem dual_interface : dual interface = interface := by
  rfl

theorem dual_dark : dual dark = bright := by
  rfl

theorem dual_involutive (ρ : PreNumericSectorRole) : dual (dual ρ) = ρ := by
  cases ρ <;> rfl

end PreNumericSectorRole

section ClosedChain

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}

structure PreNumericSectorCore where
  selectedLevel : Nat
  carrier : PreNumericSectorRole → Finset (Cell selectedLevel)
  selectedLevel_le_cutoff : selectedLevel ≤ T.cutoff
  carrier_subset : ∀ ρ, carrier ρ ⊆ T.carrier selectedLevel
  bright_interface_disjoint :
    Disjoint (carrier PreNumericSectorRole.bright)
      (carrier PreNumericSectorRole.interface)
  bright_dark_disjoint :
    Disjoint (carrier PreNumericSectorRole.bright)
      (carrier PreNumericSectorRole.dark)
  interface_dark_disjoint :
    Disjoint (carrier PreNumericSectorRole.interface)
      (carrier PreNumericSectorRole.dark)
  sectorCover :
    carrier PreNumericSectorRole.bright ∪
        carrier PreNumericSectorRole.interface ∪
        carrier PreNumericSectorRole.dark =
      T.carrier selectedLevel
  sectorCount : Nat
  sectorCount_ge_two : 2 ≤ sectorCount

namespace PreNumericSectorCore

def brightCarrier (P : PreNumericSectorCore (Cell := Cell) (T := T)) :
    Finset (Cell P.selectedLevel) :=
  P.carrier PreNumericSectorRole.bright

def interfaceCarrier (P : PreNumericSectorCore (Cell := Cell) (T := T)) :
    Finset (Cell P.selectedLevel) :=
  P.carrier PreNumericSectorRole.interface

def darkCarrier (P : PreNumericSectorCore (Cell := Cell) (T := T)) :
    Finset (Cell P.selectedLevel) :=
  P.carrier PreNumericSectorRole.dark

def selectedCarrier (P : PreNumericSectorCore (Cell := Cell) (T := T)) :
    Finset (Cell P.selectedLevel) :=
  T.carrier P.selectedLevel

theorem brightCarrier_subset (P : PreNumericSectorCore (Cell := Cell) (T := T)) :
    P.brightCarrier ⊆ P.selectedCarrier := by
  exact P.carrier_subset PreNumericSectorRole.bright

theorem interfaceCarrier_subset (P : PreNumericSectorCore (Cell := Cell) (T := T)) :
    P.interfaceCarrier ⊆ P.selectedCarrier := by
  exact P.carrier_subset PreNumericSectorRole.interface

theorem darkCarrier_subset (P : PreNumericSectorCore (Cell := Cell) (T := T)) :
    P.darkCarrier ⊆ P.selectedCarrier := by
  exact P.carrier_subset PreNumericSectorRole.dark

theorem sectorCover_eq_selectedCarrier
    (P : PreNumericSectorCore (Cell := Cell) (T := T)) :
    P.brightCarrier ∪ P.interfaceCarrier ∪ P.darkCarrier = P.selectedCarrier := by
  exact P.sectorCover

end PreNumericSectorCore

def preNumericSectorCoreOf
    (X : CayleyDicksonSource Cell T) : PreNumericSectorCore (Cell := Cell) (T := T) where
  selectedLevel := X.regularization.selectedLevel
  carrier := fun ρ =>
    match ρ with
    | PreNumericSectorRole.bright => X.regularization.selectedBrightCarrier
    | PreNumericSectorRole.interface => X.regularization.selectedBoundaryCarrier
    | PreNumericSectorRole.dark => X.regularization.selectedDarkCarrier
  selectedLevel_le_cutoff := X.regularization.selectedLevel_le_cutoff
  carrier_subset := by
    intro ρ
    cases ρ with
    | bright =>
        change X.regularization.branching.brightCarrier ⊆
          T.carrier X.regularization.branching.selectedLevel
        exact X.regularization.branching.brightCarrier_subset
    | interface =>
        exact X.regularization.selectedBoundaryCarrier_subset
    | dark =>
        change X.regularization.branching.darkCarrier ⊆
          T.carrier X.regularization.branching.selectedLevel
        exact X.regularization.branching.darkCarrier_subset
  bright_interface_disjoint := by
    change Disjoint X.regularization.branching.brightCarrier
      X.regularization.branching.interfaceCarrier
    exact X.regularization.branching.brightCarrier_disjoint_interfaceCarrier
  bright_dark_disjoint := by
    change Disjoint X.regularization.branching.brightCarrier
      X.regularization.branching.darkCarrier
    exact X.regularization.branching.brightCarrier_disjoint_darkCarrier
  interface_dark_disjoint := by
    change Disjoint X.regularization.branching.interfaceCarrier
      X.regularization.branching.darkCarrier
    exact X.regularization.branching.interfaceCarrier_disjoint_darkCarrier
  sectorCover := by
    change X.regularization.branching.brightCarrier ∪
        X.regularization.branching.interfaceCarrier ∪
        X.regularization.branching.darkCarrier =
      T.carrier X.regularization.branching.selectedLevel
    exact X.regularization.branching.sectorCover
  sectorCount := X.regularization.selectedSectorCount
  sectorCount_ge_two := X.regularization.selectedSectorCount_ge_two

structure ComplexCouplingSeed
    (X : CayleyDicksonSource Cell T) where
  prenumeric : PreNumericSectorCore (Cell := Cell) (T := T)
  prenumeric_eq : prenumeric = preNumericSectorCoreOf X
  regularizationReusesSplit : X.regularization.split = X.split
  couplingReusesSplit : X.schur.split = X.split
  regularizationPolicy : RegularizationPolicy
  regularizationPolicy_eq : regularizationPolicy = X.regularization.regularizationPolicy
  comparisonOperator :
    Matrix X.regularization.boundaryVertex X.regularization.boundaryVertex ExecComplex
  comparisonOperator_eq : comparisonOperator = X.regularization.comparisonOperator
  epsilon : ℝ
  epsilon_eq : epsilon = X.regularization.epsilon
  epsilon_pos : 0 < epsilon
  regularizationShift : ℝ
  regularizationShift_eq : regularizationShift = X.regularization.regularizationShift
  shiftFromExecComparison :
    regularizationShift = regularizationPolicy.canonicalShift comparisonOperator
  shiftDominatesEpsilon : epsilon ≤ regularizationShift
  rawBoundaryOperator :
    Matrix X.regularization.boundaryVertex X.regularization.boundaryVertex ℝ
  rawBoundaryOperator_eq : rawBoundaryOperator = X.regularization.rawBoundaryOperator
  stabilizedOperator :
    Matrix X.regularization.boundaryVertex X.regularization.boundaryVertex ℝ
  stabilizedOperator_eq : stabilizedOperator = X.regularization.stabilizedOperator
  stabilizedOperatorFormula :
    stabilizedOperator =
      rawBoundaryOperator +
        regularizationShift •
          (1 : Matrix X.regularization.boundaryVertex
              X.regularization.boundaryVertex ℝ)

def complexCouplingSeedOf
    (X : CayleyDicksonSource Cell T) : ComplexCouplingSeed X where
  prenumeric := preNumericSectorCoreOf X
  prenumeric_eq := rfl
  regularizationReusesSplit := split_is_shared_by_regularization X
  couplingReusesSplit := split_is_shared_by_coupling X
  regularizationPolicy := X.regularization.regularizationPolicy
  regularizationPolicy_eq := rfl
  comparisonOperator := X.regularization.comparisonOperator
  comparisonOperator_eq := rfl
  epsilon := X.regularization.epsilon
  epsilon_eq := rfl
  epsilon_pos := X.regularization.epsilon_pos
  regularizationShift := X.regularization.regularizationShift
  regularizationShift_eq := rfl
  shiftFromExecComparison := regularization_shift_is_exec_derived X
  shiftDominatesEpsilon := regularization_shift_dominates_epsilon X
  rawBoundaryOperator := X.regularization.rawBoundaryOperator
  rawBoundaryOperator_eq := rfl
  stabilizedOperator := X.regularization.stabilizedOperator
  stabilizedOperator_eq := rfl
  stabilizedOperatorFormula := stabilized_operator_eq_raw_plus_shift X

inductive SeedStatus where
  | closed
  | open
  deriving DecidableEq

structure StatusLedger
    (X : CayleyDicksonSource Cell T) where
  theoremLayer : S6TheoremLayer X
  prenumericSectorCore : PreNumericSectorCore (Cell := Cell) (T := T)
  prenumericSectorCoreStatus : SeedStatus
  complexCouplingSeed : ComplexCouplingSeed X
  complexCouplingSeedStatus : SeedStatus
  quaternionicSeedStatus : SeedStatus
  octonionicSeedStatus : SeedStatus
  hurwitzStopStatus : SeedStatus


def statusLedgerOf
    (X : CayleyDicksonSource Cell T) : StatusLedger X where
  theoremLayer := s6_theorem_layer X
  prenumericSectorCore := preNumericSectorCoreOf X
  prenumericSectorCoreStatus := SeedStatus.closed
  complexCouplingSeed := complexCouplingSeedOf X
  complexCouplingSeedStatus := SeedStatus.closed
  quaternionicSeedStatus := SeedStatus.open
  octonionicSeedStatus := SeedStatus.open
  hurwitzStopStatus := SeedStatus.open

end ClosedChain

end CNNA.PillarA.Structural.CayleyDickson
