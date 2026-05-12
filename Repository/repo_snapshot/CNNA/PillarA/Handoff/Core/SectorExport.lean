import CNNA.PillarA.Network.InfiniteCarrier
import CNNA.PillarA.Closure.RegularizationClosure
import CNNA.PillarA.Closure.Notation
import CNNA.PillarA.DtN.Notation
import CNNA.PillarA.Coupling.MultiSchur

set_option autoImplicit false

namespace CNNA.PillarA.Handoff

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.Finite
open CNNA.PillarA.DtN
open CNNA.PillarA.Sectors
open CNNA.PillarA.Closure
open CNNA.PillarA.Network
open CNNA.PillarA.Coupling

universe u

structure SectorExportStrong (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  carrier : InfiniteCarrierStrong Cell T
  regularization : RegularizationClosureStrong Cell T
  schur : MultiSchurStrong Cell T
  regularization_split : regularization.split = carrier.split
  schur_split : schur.split = carrier.split

abbrev SectorExportStrongOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  SectorExportStrong (Cell := Cell) T

namespace SectorExportStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

@[ext] theorem ext (X Y : SectorExportStrong Cell T)
    (hcarrier : X.carrier = Y.carrier)
    (hregularization : X.regularization = Y.regularization)
    (hschur : X.schur = Y.schur) :
    X = Y := by
  cases X with
  | mk carrierX regularizationX schurX regularization_splitX schur_splitX =>
    cases Y with
    | mk carrierY regularizationY schurY regularization_splitY schur_splitY =>
      cases hcarrier
      cases hregularization
      cases hschur
      have hreg : regularization_splitX = regularization_splitY := Subsingleton.elim _ _
      cases hreg
      have hschur' : schur_splitX = schur_splitY := Subsingleton.elim _ _
      cases hschur'
      rfl

def cast (h : T = U) (X : SectorExportStrong Cell T) :
    SectorExportStrong Cell U := by
  cases h
  exact X

theorem cast_rfl (X : SectorExportStrong Cell T) :
    cast (Cell := Cell) rfl X = X := by
  rfl

def ofClosedStrands
    (I : InfiniteCarrierStrong Cell T)
    (R : RegularizationClosureStrong Cell T)
    (M : MultiSchurStrong Cell T)
    (hR : R.split = I.split)
    (hM : M.split = I.split) :
    SectorExportStrong Cell T where
  carrier := I
  regularization := R
  schur := M
  regularization_split := hR
  schur_split := hM

theorem ofClosedStrands_carrier
    (I : InfiniteCarrierStrong Cell T)
    (R : RegularizationClosureStrong Cell T)
    (M : MultiSchurStrong Cell T)
    (hR : R.split = I.split)
    (hM : M.split = I.split) :
    (ofClosedStrands I R M hR hM).carrier = I := by
  rfl

theorem ofClosedStrands_regularization
    (I : InfiniteCarrierStrong Cell T)
    (R : RegularizationClosureStrong Cell T)
    (M : MultiSchurStrong Cell T)
    (hR : R.split = I.split)
    (hM : M.split = I.split) :
    (ofClosedStrands I R M hR hM).regularization = R := by
  rfl

theorem ofClosedStrands_schur
    (I : InfiniteCarrierStrong Cell T)
    (R : RegularizationClosureStrong Cell T)
    (M : MultiSchurStrong Cell T)
    (hR : R.split = I.split)
    (hM : M.split = I.split) :
    (ofClosedStrands I R M hR hM).schur = M := by
  rfl

def regionNet (X : SectorExportStrong Cell T) : RegionNetStrong Cell T :=
  X.carrier.regionNet

def split (X : SectorExportStrong Cell T) : SectorSplitStrong Cell T :=
  X.carrier.split

def approximant (X : SectorExportStrong Cell T) : ApproximantStrong Cell T :=
  X.carrier.approximant

def ideal (X : SectorExportStrong Cell T) : DirectedFamily (Cell := Cell) :=
  X.carrier.ideal

def cutoff (_ : SectorExportStrong Cell T) : Nat :=
  T.cutoff

def stableCarrier (X : SectorExportStrong Cell T) (L : Nat) : Finset (Cell L) :=
  X.carrier.stableCarrier L

def idealCarrier (X : SectorExportStrong Cell T) (L : Nat) : Finset (Cell L) :=
  X.carrier.idealCarrier L

def stableSlice (X : SectorExportStrong Cell T) (L : Nat) : LayerSlice Cell :=
  X.carrier.stableSlice L

def idealSlice (X : SectorExportStrong Cell T) (L : Nat) : LayerSlice Cell :=
  X.carrier.idealSlice L

def region (X : SectorExportStrong Cell T) (K : RegionKind) : RegionCore Cell T :=
  X.carrier.region K

def boundaryPorts (X : SectorExportStrong Cell T) (K : RegionKind) : BoundaryPorts Cell T :=
  X.carrier.boundaryPorts K

def regionCarrier (X : SectorExportStrong Cell T) (K : RegionKind) (L : Nat) : Finset (Cell L) :=
  X.carrier.regionCarrier K L

def sectorCarrier (X : SectorExportStrong Cell T) (K : RegionKind) (L : Nat) : Finset (Cell L) :=
  X.carrier.sectorCarrier K L

def ports (X : SectorExportStrong Cell T) (K : RegionKind) (L : Nat) : Finset (Cell L) :=
  X.carrier.ports K L

def interiorCarrier (X : SectorExportStrong Cell T) (K : RegionKind) (L : Nat) : Finset (Cell L) :=
  X.carrier.interiorCarrier K L

def brightRegion (X : SectorExportStrong Cell T) : RegionCore Cell T :=
  X.regionNet.brightRegion

def interfaceRegion (X : SectorExportStrong Cell T) : RegionCore Cell T :=
  X.regionNet.interfaceRegion

def darkRegion (X : SectorExportStrong Cell T) : RegionCore Cell T :=
  X.regionNet.darkRegion

def brightBoundaryPorts (X : SectorExportStrong Cell T) : BoundaryPorts Cell T :=
  X.regionNet.brightBoundaryPorts

def interfaceBoundaryPorts (X : SectorExportStrong Cell T) : BoundaryPorts Cell T :=
  X.regionNet.interfaceBoundaryPorts

def darkBoundaryPorts (X : SectorExportStrong Cell T) : BoundaryPorts Cell T :=
  X.regionNet.darkBoundaryPorts

def noOuterEnvironment (X : SectorExportStrong Cell T) : Prop :=
  X.carrier.noOuterEnvironment

def hasOuterEnvironment (X : SectorExportStrong Cell T) : Prop :=
  X.carrier.hasOuterEnvironment

def rootCentered (X : SectorExportStrong Cell T) : Prop :=
  X.carrier.rootCentered

def windowed (X : SectorExportStrong Cell T) : Prop :=
  X.carrier.windowed

def closureStabilizedBinary (X : SectorExportStrong Cell T) : StabilizedBinaryDtN Cell T :=
  X.regularization.stabilizedSource

def binary (X : SectorExportStrong Cell T) : DtNStrong Cell T :=
  X.schur.binary

def dirichlet (X : SectorExportStrong Cell T) : DirichletLaplacianStrong Cell T :=
  X.schur.dirichlet

def generalized (X : SectorExportStrong Cell T) : GeneralizedDtNStrong Cell T :=
  X.schur.generalized

def couplingStabilizedBinary (X : SectorExportStrong Cell T) : DtNStabilizedStrong Cell T :=
  X.generalized.stabilizedBinary

def selector (X : SectorExportStrong Cell T) : BranchingSelectorStrong Cell T :=
  X.regularization.selector

def witness (X : SectorExportStrong Cell T) : BranchingWitnessStrong Cell T :=
  X.regularization.witness

def branching (X : SectorExportStrong Cell T) : SelectedBranchingStrong Cell T :=
  X.regularization.branching

def uv (X : SectorExportStrong Cell T) : UVSpectralSelectorStrong Cell T :=
  X.regularization.uv

def selectedLevel (X : SectorExportStrong Cell T) : Nat :=
  X.regularization.selectedLevel

def candidateLevels (X : SectorExportStrong Cell T) : Finset Nat :=
  X.regularization.candidateLevels

def irLevels (X : SectorExportStrong Cell T) : Finset Nat :=
  X.regularization.irLevels

def uvLevels (X : SectorExportStrong Cell T) : Finset Nat :=
  X.regularization.uvLevels

def hasUVTail (X : SectorExportStrong Cell T) : Prop :=
  X.regularization.hasUVTail

def epsilon (X : SectorExportStrong Cell T) : ℝ :=
  X.regularization.epsilon

def regularizationShift (X : SectorExportStrong Cell T) : ℝ :=
  X.regularization.regularizationShift

def closureComparisonOperator (X : SectorExportStrong Cell T) :
    Matrix X.regularization.source.boundaryVertex X.regularization.source.boundaryVertex Execℂ :=
  ClosureComparisonOperator Cell X.regularization.source

def closureRegularizationShiftQ (X : SectorExportStrong Cell T) : ℚ :=
  ClosureRegularizationShiftQ Cell X.regularization.source

def stabilizationComparisonOperator (X : SectorExportStrong Cell T) :
    Matrix X.closureStabilizedBinary.boundaryVertex X.closureStabilizedBinary.boundaryVertex Execℂ :=
  RegularizationComparisonOperator Cell X.closureStabilizedBinary

def stabilizationRegularizationShiftQ (X : SectorExportStrong Cell T) : ℚ :=
  RegularizationShiftQ Cell X.closureStabilizedBinary

def rawBoundaryOperator (X : SectorExportStrong Cell T) :
    Matrix X.closureStabilizedBinary.boundaryVertex X.closureStabilizedBinary.boundaryVertex ℝ :=
  X.regularization.rawBoundaryOperator

def symmetrizedBoundaryOperator (X : SectorExportStrong Cell T) :
    Matrix X.closureStabilizedBinary.boundaryVertex X.closureStabilizedBinary.boundaryVertex ℝ :=
  X.regularization.symmetrizedBoundaryOperator

def stabilizedOperator (X : SectorExportStrong Cell T) :
    Matrix X.closureStabilizedBinary.boundaryVertex X.closureStabilizedBinary.boundaryVertex ℝ :=
  X.regularization.stabilizedOperator

def stabilizedSymmetricOperator (X : SectorExportStrong Cell T) :
    Matrix X.closureStabilizedBinary.boundaryVertex X.closureStabilizedBinary.boundaryVertex ℝ :=
  X.regularization.stabilizedSymmetricOperator

def interfaceInverse (X : SectorExportStrong Cell T) :
    Matrix X.schur.interfaceBoundaryVertex X.schur.interfaceBoundaryVertex ℝ :=
  X.schur.interfaceInverse

def restrict (X : SectorExportStrong Cell T)
    (K : CoupledSectorKind) (φ : X.schur.boundaryPotential) :
    X.schur.sectorPotential K :=
  X.schur.restrict K φ

def glue (X : SectorExportStrong Cell T)
    (K : CoupledSectorKind) (φ : X.schur.sectorPotential K) :
    X.schur.boundaryPotential :=
  X.schur.glue K φ

def block (X : SectorExportStrong Cell T)
    (src dst : CoupledSectorKind) :
    Matrix (X.schur.sectorBoundaryVertex src) (X.schur.sectorBoundaryVertex dst) ℝ :=
  X.schur.block src dst

def brightBrightSchur (X : SectorExportStrong Cell T) :
    Matrix X.schur.brightBoundaryVertex X.schur.brightBoundaryVertex ℝ :=
  X.schur.brightBrightSchur

def brightDarkSchur (X : SectorExportStrong Cell T) :
    Matrix X.schur.brightBoundaryVertex X.schur.darkBoundaryVertex ℝ :=
  X.schur.brightDarkSchur

def darkBrightSchur (X : SectorExportStrong Cell T) :
    Matrix X.schur.darkBoundaryVertex X.schur.brightBoundaryVertex ℝ :=
  X.schur.darkBrightSchur

def darkDarkSchur (X : SectorExportStrong Cell T) :
    Matrix X.schur.darkBoundaryVertex X.schur.darkBoundaryVertex ℝ :=
  X.schur.darkDarkSchur

def reducedFlux (X : SectorExportStrong Cell T)
    (φ : X.schur.reducedPotential) :
    X.schur.reducedPotential :=
  X.schur.reducedFlux φ

theorem regionNet_eq_carrier_regionNet (X : SectorExportStrong Cell T) :
    X.regionNet = X.carrier.regionNet := by
  rfl

theorem split_eq_carrier_split (X : SectorExportStrong Cell T) :
    X.split = X.carrier.split := by
  rfl

theorem approximant_eq_carrier_approximant (X : SectorExportStrong Cell T) :
    X.approximant = X.carrier.approximant := by
  rfl

theorem closureStabilizedBinary_eq_regularization_stabilizedSource
    (X : SectorExportStrong Cell T) :
    X.closureStabilizedBinary = X.regularization.stabilizedSource := by
  rfl

theorem couplingStabilizedBinary_eq_generalized_stabilizedBinary
    (X : SectorExportStrong Cell T) :
    X.couplingStabilizedBinary = X.generalized.stabilizedBinary := by
  rfl

theorem selector_eq_regularization_selector (X : SectorExportStrong Cell T) :
    X.selector = X.regularization.selector := by
  rfl

theorem witness_eq_regularization_witness (X : SectorExportStrong Cell T) :
    X.witness = X.regularization.witness := by
  rfl

theorem branching_eq_regularization_branching (X : SectorExportStrong Cell T) :
    X.branching = X.regularization.branching := by
  rfl

theorem uv_eq_regularization_uv (X : SectorExportStrong Cell T) :
    X.uv = X.regularization.uv := by
  rfl

theorem binary_eq_schur_binary (X : SectorExportStrong Cell T) :
    X.binary = X.schur.binary := by
  rfl

theorem dirichlet_eq_schur_dirichlet (X : SectorExportStrong Cell T) :
    X.dirichlet = X.schur.dirichlet := by
  rfl

theorem generalized_eq_schur_generalized (X : SectorExportStrong Cell T) :
    X.generalized = X.schur.generalized := by
  rfl

theorem regularization_split_eq_split (X : SectorExportStrong Cell T) :
    X.regularization.split = X.split := by
  exact X.regularization_split

theorem schur_split_eq_split (X : SectorExportStrong Cell T) :
    X.schur.split = X.split := by
  exact X.schur_split

theorem generalized_split_eq_split (X : SectorExportStrong Cell T) :
    X.generalized.split = X.split := by
  exact X.schur_split_eq_split

theorem binary_source_eq_dirichlet (X : SectorExportStrong Cell T) :
    X.binary.source = X.dirichlet := by
  rfl

theorem closureStabilizedBinary_source_eq_regularization_source_source
    (X : SectorExportStrong Cell T) :
    X.closureStabilizedBinary.source = X.regularization.source.source.source := by
  rfl

theorem couplingStabilizedBinary_source_eq_generalized_rawBinary
    (X : SectorExportStrong Cell T) :
    X.couplingStabilizedBinary.source = X.generalized.rawBinary := by
  simpa [SectorExportStrong.couplingStabilizedBinary] using
    GeneralizedDtNStrong.stabilizedBinary_source_eq_rawBinary X.generalized

theorem selectedLevel_eq_regularization_selectedLevel (X : SectorExportStrong Cell T) :
    X.selectedLevel = X.regularization.selectedLevel := by
  rfl

theorem candidateLevels_eq_regularization_candidateLevels (X : SectorExportStrong Cell T) :
    X.candidateLevels = X.regularization.candidateLevels := by
  rfl

theorem irLevels_eq_regularization_irLevels (X : SectorExportStrong Cell T) :
    X.irLevels = X.regularization.irLevels := by
  rfl

theorem uvLevels_eq_regularization_uvLevels (X : SectorExportStrong Cell T) :
    X.uvLevels = X.regularization.uvLevels := by
  rfl

theorem epsilon_eq_regularization_epsilon (X : SectorExportStrong Cell T) :
    X.epsilon = X.regularization.epsilon := by
  rfl

theorem regularizationShift_eq_regularization_regularizationShift
    (X : SectorExportStrong Cell T) :
    X.regularizationShift = X.regularization.regularizationShift := by
  rfl

theorem epsilon_pos (X : SectorExportStrong Cell T) :
    0 < X.epsilon := by
  exact X.regularization.epsilon_pos

theorem regularizationShift_pos (X : SectorExportStrong Cell T) :
    0 < X.regularizationShift := by
  exact X.regularization.regularizationShift_pos

theorem regularizationShift_nonneg (X : SectorExportStrong Cell T) :
    0 ≤ X.regularizationShift := by
  exact X.regularization.regularizationShift_nonneg

theorem regularizationShift_ge_epsilon (X : SectorExportStrong Cell T) :
    X.epsilon ≤ X.regularizationShift := by
  exact X.regularization.regularizationShift_ge_epsilon

theorem selectedLevelAdmissible (X : SectorExportStrong Cell T) :
    X.selectedLevel ∈ X.candidateLevels := by
  exact X.regularization.selectedLevelAdmissible

theorem selectedLevel_le_cutoff (X : SectorExportStrong Cell T) :
    X.selectedLevel ≤ X.cutoff := by
  exact X.regularization.selectedLevel_le_cutoff

theorem mem_irLevels_iff (X : SectorExportStrong Cell T) (L : Nat) :
    L ∈ X.irLevels ↔ L ≤ X.selectedLevel := by
  exact X.regularization.mem_irLevels_iff L

theorem mem_uvLevels_iff (X : SectorExportStrong Cell T) (L : Nat) :
    L ∈ X.uvLevels ↔ X.selectedLevel < L ∧ L ≤ X.cutoff := by
  exact X.regularization.mem_uvLevels_iff L

theorem hasUVTail_iff_nonempty (X : SectorExportStrong Cell T) :
    X.hasUVTail ↔ X.uvLevels.Nonempty := by
  exact X.regularization.hasUVTail_iff_nonempty

theorem noUVTail_iff (X : SectorExportStrong Cell T) :
    ¬ X.hasUVTail ↔ X.uvLevels = ∅ := by
  exact X.regularization.noUVTail_iff

theorem ir_uv_disjoint (X : SectorExportStrong Cell T) :
    Disjoint X.irLevels X.uvLevels := by
  exact X.regularization.ir_uv_disjoint

theorem ir_uv_cover (X : SectorExportStrong Cell T) :
    X.irLevels ∪ X.uvLevels = Finset.range (X.cutoff + 1) := by
  exact X.regularization.ir_uv_cover

theorem noOuterEnvironment_iff_split (X : SectorExportStrong Cell T) :
    X.noOuterEnvironment ↔ X.split.noOuterEnvironment := by
  change X.carrier.noOuterEnvironment ↔ X.carrier.network.noOuterEnvironment
  exact X.carrier.noOuterEnvironment_iff_network

theorem hasOuterEnvironment_iff_split (X : SectorExportStrong Cell T) :
    X.hasOuterEnvironment ↔ X.split.hasOuterEnvironment := by
  change X.carrier.hasOuterEnvironment ↔ X.carrier.network.hasOuterEnvironment
  exact X.carrier.hasOuterEnvironment_iff_network

theorem rootCentered_iff_split (X : SectorExportStrong Cell T) :
    X.rootCentered ↔ X.split.noOuterEnvironment := by
  change X.carrier.rootCentered ↔ X.carrier.network.rootCentered
  exact X.carrier.rootCentered_iff_network

theorem windowed_iff_split (X : SectorExportStrong Cell T) :
    X.windowed ↔ X.split.hasOuterEnvironment := by
  change X.carrier.windowed ↔ X.carrier.network.windowed
  exact X.carrier.windowed_iff_network

theorem stable_eq_truncate (X : SectorExportStrong Cell T) :
    T = X.ideal.truncate X.cutoff := by
  exact X.carrier.stable_eq_truncate

theorem stableCarrier_eq_ideal_of_le
    (X : SectorExportStrong Cell T) {L : Nat} (hL : L ≤ X.cutoff) :
    X.stableCarrier L = X.idealCarrier L := by
  exact X.carrier.stableCarrier_eq_ideal_of_le hL

theorem stableCarrier_eq_empty_of_gt
    (X : SectorExportStrong Cell T) {L : Nat} (hL : X.cutoff < L) :
    X.stableCarrier L = ∅ := by
  exact X.carrier.stableCarrier_eq_empty_of_gt hL

theorem topStableCarrier_eq_ideal (X : SectorExportStrong Cell T) :
    X.stableCarrier X.cutoff = X.idealCarrier X.cutoff := by
  exact X.carrier.topStableCarrier_eq_ideal

theorem topSlice_carrier_eq_ideal (X : SectorExportStrong Cell T) :
    T.topSlice.carrier = X.idealCarrier X.cutoff := by
  exact X.carrier.topSlice_carrier_eq_ideal

theorem brightRegion_eq_region_bright (X : SectorExportStrong Cell T) :
    X.brightRegion = X.region .bright := by
  rfl

theorem interfaceRegion_eq_region_interface (X : SectorExportStrong Cell T) :
    X.interfaceRegion = X.region .interface := by
  rfl

theorem darkRegion_eq_region_dark (X : SectorExportStrong Cell T) :
    X.darkRegion = X.region .dark := by
  rfl

theorem brightBoundaryPorts_eq_boundaryPorts_bright (X : SectorExportStrong Cell T) :
    X.brightBoundaryPorts = X.boundaryPorts .bright := by
  rfl

theorem interfaceBoundaryPorts_eq_boundaryPorts_interface (X : SectorExportStrong Cell T) :
    X.interfaceBoundaryPorts = X.boundaryPorts .interface := by
  rfl

theorem darkBoundaryPorts_eq_boundaryPorts_dark (X : SectorExportStrong Cell T) :
    X.darkBoundaryPorts = X.boundaryPorts .dark := by
  rfl

theorem regionCarrier_subset (X : SectorExportStrong Cell T)
    (K : RegionKind) (L : Nat) :
    X.regionCarrier K L ⊆ T.carrier L := by
  exact X.regionNet.regionCarrier_subset K L

theorem ports_subset_regionCarrier (X : SectorExportStrong Cell T)
    (K : RegionKind) (L : Nat) :
    X.ports K L ⊆ X.regionCarrier K L := by
  exact X.regionNet.ports_subset_regionCarrier K L

theorem sectorCover (X : SectorExportStrong Cell T) (L : Nat) :
    X.sectorCarrier .bright L ∪ X.sectorCarrier .interface L ∪ X.sectorCarrier .dark L =
      T.carrier L := by
  exact X.carrier.sectorCover L

theorem selectedCarrier_subset (X : SectorExportStrong Cell T) :
    X.regularization.selectedCarrier ⊆ T.carrier X.selectedLevel := by
  exact X.regularization.selectedCarrier_subset

theorem selectedBoundaryCarrier_subset (X : SectorExportStrong Cell T) :
    X.regularization.selectedBoundaryCarrier ⊆ T.carrier X.selectedLevel := by
  exact X.regularization.selectedBoundaryCarrier_subset

end SectorExportStrong

end CNNA.PillarA.Handoff
