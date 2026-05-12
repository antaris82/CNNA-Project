import CNNA.PillarA.Structural.CayleyDickson.Source

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

section ClosedChain

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}

 theorem ideal_approximant_is_truncation
    (X : CayleyDicksonSource Cell T) :
    T = X.ideal.truncate X.cutoff := by
  exact X.stable_eq_truncate

 theorem top_slice_recovers_ideal_carrier
    (X : CayleyDicksonSource Cell T) :
    T.topSlice.carrier = X.idealCarrier X.cutoff := by
  exact X.topSlice_carrier_eq_ideal

 theorem split_is_shared_by_regularization
    (X : CayleyDicksonSource Cell T) :
    X.regularization.split = X.split := by
  exact X.regularization_split_eq_split

 theorem split_is_shared_by_coupling
    (X : CayleyDicksonSource Cell T) :
    X.schur.split = X.split := by
  exact X.schur_split_eq_split

 theorem selected_sector_cover_at_regularization_level
    (X : CayleyDicksonSource Cell T) :
    X.regularization.selectedBrightCarrier ∪
        X.regularization.selectedBoundaryCarrier ∪
        X.regularization.selectedDarkCarrier =
      T.carrier X.regularization.selectedLevel := by
  exact X.regularization.selectedSectorCover

 theorem selected_sector_count_ge_two
    (X : CayleyDicksonSource Cell T) :
    2 ≤ X.regularization.selectedSectorCount := by
  exact X.regularization.selectedSectorCount_ge_two

 theorem regularization_shift_is_exec_derived
    (X : CayleyDicksonSource Cell T) :
    X.regularization.regularizationShift =
      X.regularization.regularizationPolicy.canonicalShift
        X.regularization.comparisonOperator := by
  exact X.regularization.regularizationShift_eq_policy_canonicalShift

 theorem regularization_shift_dominates_epsilon
    (X : CayleyDicksonSource Cell T) :
    X.regularization.epsilon ≤ X.regularization.regularizationShift := by
  exact X.regularization.regularizationShift_ge_epsilon

 theorem stabilized_operator_eq_raw_plus_shift
    (X : CayleyDicksonSource Cell T) :
    X.regularization.stabilizedOperator =
      X.regularization.rawBoundaryOperator +
        X.regularization.regularizationShift •
          (1 :
            Matrix X.regularization.boundaryVertex
              X.regularization.boundaryVertex ℝ) := by
  exact X.regularization.stabilizedOperator_eq_raw_plus_shift

 structure S6AdditionalFinding
    (X : CayleyDicksonSource Cell T) : Prop where
  idealPrimacy :
    T = X.ideal.truncate X.cutoff
  topSliceRecoversIdeal :
    T.topSlice.carrier = X.idealCarrier X.cutoff
  prenumericRegularizationReuse :
    X.regularization.split = X.split
  prenumericCouplingReuse :
    X.schur.split = X.split
  selectedSectorCountGeTwo :
    2 ≤ X.regularization.selectedSectorCount
  selectedSectorCover :
    X.regularization.selectedBrightCarrier ∪
        X.regularization.selectedBoundaryCarrier ∪
        X.regularization.selectedDarkCarrier =
      T.carrier X.regularization.selectedLevel
  shiftFromExecComparison :
    X.regularization.regularizationShift =
      X.regularization.regularizationPolicy.canonicalShift
        X.regularization.comparisonOperator
  shiftDominatesEpsilon :
    X.regularization.epsilon ≤ X.regularization.regularizationShift
  stabilizedOperatorFormula :
    X.regularization.stabilizedOperator =
      X.regularization.rawBoundaryOperator +
        X.regularization.regularizationShift •
          (1 :
            Matrix X.regularization.boundaryVertex
              X.regularization.boundaryVertex ℝ)

 theorem s6_additional_finding
    (X : CayleyDicksonSource Cell T) :
    S6AdditionalFinding X := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ideal_approximant_is_truncation X
  · exact top_slice_recovers_ideal_carrier X
  · exact split_is_shared_by_regularization X
  · exact split_is_shared_by_coupling X
  · exact selected_sector_count_ge_two X
  · exact selected_sector_cover_at_regularization_level X
  · exact regularization_shift_is_exec_derived X
  · exact regularization_shift_dominates_epsilon X
  · exact stabilized_operator_eq_raw_plus_shift X

end ClosedChain

end CNNA.PillarA.Structural.CayleyDickson
