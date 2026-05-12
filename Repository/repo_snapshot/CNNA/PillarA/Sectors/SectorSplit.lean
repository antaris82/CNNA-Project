import CNNA.PillarA.Sectors.ComplementSectorFamily

set_option autoImplicit false

namespace CNNA.PillarA.Sectors

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.Finite
open CNNA.PillarA.DtN

universe u

structure SectorSplitStrong (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  source : ComplementSectorFamilyStrong Cell T

abbrev SectorSplitStrongOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  SectorSplitStrong (Cell := Cell) T

namespace SectorSplitStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

@[ext] theorem ext (S R : SectorSplitStrong Cell T)
    (hsource : S.source = R.source) :
    S = R := by
  cases S with
  | mk sourceS =>
    cases R with
    | mk sourceR =>
      cases hsource
      rfl

def cast (h : T = U) (S : SectorSplitStrong Cell T) :
    SectorSplitStrong Cell U := by
  cases h
  exact S

theorem cast_rfl (S : SectorSplitStrong Cell T) :
    cast (Cell := Cell) rfl S = S := by
  rfl

def ofComplementSectorFamily (C : ComplementSectorFamilyStrong Cell T) :
    SectorSplitStrong Cell T where
  source := C

theorem ofComplementSectorFamily_source (C : ComplementSectorFamilyStrong Cell T) :
    (ofComplementSectorFamily C).source = C := by
  rfl

def darkFamily (S : SectorSplitStrong Cell T) : ComplementSectorFamilyStrong Cell T :=
  S.source

def brightPatch (S : SectorSplitStrong Cell T) : BranchPatchStrong Cell T :=
  S.darkFamily.patch

def stabilized (S : SectorSplitStrong Cell T) : DtNStabilizedStrong Cell T :=
  S.brightPatch.stabilized

def dtn (S : SectorSplitStrong Cell T) : DtNStrong Cell T :=
  S.brightPatch.dtn

def dirichlet (S : SectorSplitStrong Cell T) : DirichletLaplacianStrong Cell T :=
  S.brightPatch.dirichlet

def approximant (S : SectorSplitStrong Cell T) : ApproximantStrong Cell T :=
  S.brightPatch.approximant

def brightSupport (S : SectorSplitStrong Cell T) : CutSpec Cell T :=
  S.brightPatch.support

def darkSupport (S : SectorSplitStrong Cell T) : CutSpec Cell T :=
  S.darkFamily.support

def brightRegion (S : SectorSplitStrong Cell T) : RegionCore Cell T :=
  S.brightPatch.region

def darkRegion (S : SectorSplitStrong Cell T) : RegionCore Cell T :=
  S.darkFamily.region

def brightBoundaryPorts (S : SectorSplitStrong Cell T) : BoundaryPorts Cell T :=
  S.brightPatch.boundaryPorts

def darkBoundaryPorts (S : SectorSplitStrong Cell T) : BoundaryPorts Cell T :=
  S.darkFamily.boundaryPorts

theorem brightPatch_eq_source_patch (S : SectorSplitStrong Cell T) :
    S.brightPatch = S.source.patch := by
  rfl

theorem brightSupport_eq_patch_support (S : SectorSplitStrong Cell T) :
    S.brightSupport = S.brightPatch.support := by
  rfl

theorem darkSupport_eq_source_support (S : SectorSplitStrong Cell T) :
    S.darkSupport = S.source.support := by
  rfl

theorem brightRegion_eq_patch_region (S : SectorSplitStrong Cell T) :
    S.brightRegion = S.brightPatch.region := by
  rfl

theorem darkRegion_eq_source_region (S : SectorSplitStrong Cell T) :
    S.darkRegion = S.source.region := by
  rfl

theorem brightBoundaryPorts_eq_patch_boundaryPorts (S : SectorSplitStrong Cell T) :
    S.brightBoundaryPorts = S.brightPatch.boundaryPorts := by
  rfl

theorem darkBoundaryPorts_eq_source_boundaryPorts (S : SectorSplitStrong Cell T) :
    S.darkBoundaryPorts = S.source.boundaryPorts := by
  rfl

def brightCarrier (S : SectorSplitStrong Cell T) (L : Nat) : Finset (Cell L) :=
  S.brightPatch.carrier L

def brightBoundaryCarrier (S : SectorSplitStrong Cell T) (L : Nat) : Finset (Cell L) :=
  S.brightPatch.boundaryCarrier L

def brightInteriorCarrier (S : SectorSplitStrong Cell T) (L : Nat) : Finset (Cell L) :=
  S.brightPatch.interiorCarrier L

def darkCarrier (S : SectorSplitStrong Cell T) (L : Nat) : Finset (Cell L) :=
  S.darkFamily.carrier L

def darkBoundaryCarrier (S : SectorSplitStrong Cell T) (L : Nat) : Finset (Cell L) :=
  S.darkFamily.boundaryCarrier L

def darkInteriorCarrier (S : SectorSplitStrong Cell T) (L : Nat) : Finset (Cell L) :=
  S.darkFamily.interiorCarrier L

def interfaceCarrier (S : SectorSplitStrong Cell T) (L : Nat) : Finset (Cell L) :=
  S.brightBoundaryCarrier L ∪ S.darkBoundaryCarrier L

def brightSectorCarrier (S : SectorSplitStrong Cell T) (L : Nat) : Finset (Cell L) :=
  S.brightInteriorCarrier L

def darkSectorCarrier (S : SectorSplitStrong Cell T) (L : Nat) : Finset (Cell L) :=
  S.darkInteriorCarrier L

def brightSlice (S : SectorSplitStrong Cell T) (L : Nat) : BoundarySlice Cell :=
  S.brightPatch.slice L

def brightInteriorSlice (S : SectorSplitStrong Cell T) (L : Nat) : LayerSlice Cell :=
  S.brightPatch.interiorSlice L

def darkSlice (S : SectorSplitStrong Cell T) (L : Nat) : BoundarySlice Cell :=
  S.darkFamily.slice L

def darkInteriorSlice (S : SectorSplitStrong Cell T) (L : Nat) : LayerSlice Cell :=
  S.darkFamily.interiorSlice L

def interfaceSupport (S : SectorSplitStrong Cell T) : CutSpec Cell T where
  carrier := S.interfaceCarrier
  carrier_subset := by
    intro L x hx
    rcases Finset.mem_union.mp hx with hxBright | hxDark
    · exact S.brightPatch.carrier_subset L (S.brightPatch.boundary_subset_carrier L hxBright)
    · exact S.darkFamily.carrier_subset L (S.darkFamily.boundary_subset_carrier L hxDark)

def interfaceRegion (S : SectorSplitStrong Cell T) : RegionCore Cell T :=
  RegionCore.ofCutSpec S.interfaceSupport

def interfaceBoundaryPorts (S : SectorSplitStrong Cell T) : BoundaryPorts Cell T :=
  BoundaryPorts.ofRegion S.interfaceRegion

def interfaceSlice (S : SectorSplitStrong Cell T) (L : Nat) : LayerSlice Cell :=
  S.interfaceSupport.slice L

def cutoff (_ : SectorSplitStrong Cell T) : Nat :=
  T.cutoff

def topBrightSectorCarrier (S : SectorSplitStrong Cell T) : Finset (Cell T.cutoff) :=
  S.brightSectorCarrier T.cutoff

def topInterfaceCarrier (S : SectorSplitStrong Cell T) : Finset (Cell T.cutoff) :=
  S.interfaceCarrier T.cutoff

def topDarkSectorCarrier (S : SectorSplitStrong Cell T) : Finset (Cell T.cutoff) :=
  S.darkSectorCarrier T.cutoff

def topInterfaceSlice (S : SectorSplitStrong Cell T) : LayerSlice Cell :=
  S.interfaceSlice T.cutoff

def noOuterEnvironment (S : SectorSplitStrong Cell T) : Prop :=
  S.darkFamily.rootCentered

def hasOuterEnvironment (S : SectorSplitStrong Cell T) : Prop :=
  S.darkFamily.windowed

def rootCentered (S : SectorSplitStrong Cell T) : Prop :=
  S.noOuterEnvironment

def windowed (S : SectorSplitStrong Cell T) : Prop :=
  S.hasOuterEnvironment

theorem rootCentered_iff_noOuterEnvironment (S : SectorSplitStrong Cell T) :
    S.rootCentered ↔ S.noOuterEnvironment := by
  rfl

theorem windowed_iff_hasOuterEnvironment (S : SectorSplitStrong Cell T) :
    S.windowed ↔ S.hasOuterEnvironment := by
  rfl

theorem not_hasOuterEnvironment_of_noOuterEnvironment (S : SectorSplitStrong Cell T)
    (hroot : S.noOuterEnvironment) :
    ¬ S.hasOuterEnvironment := by
  exact S.darkFamily.not_windowed_of_rootCentered hroot

theorem not_noOuterEnvironment_of_hasOuterEnvironment (S : SectorSplitStrong Cell T)
    (hwin : S.hasOuterEnvironment) :
    ¬ S.noOuterEnvironment := by
  exact S.darkFamily.not_rootCentered_of_windowed hwin

theorem noOuterEnvironment_of_brightSupport_eq_full (S : SectorSplitStrong Cell T)
    (hfull : S.brightSupport = CutSpec.full T) :
    S.noOuterEnvironment := by
  exact S.darkFamily.rootCentered_of_patch_support_eq_full hfull

theorem noOuterEnvironment_iff_darkCarrier_empty (S : SectorSplitStrong Cell T) :
    S.noOuterEnvironment ↔ ∀ L : Nat, S.darkCarrier L = ∅ := by
  constructor
  · intro hroot L
    change S.darkFamily.carrier L = ∅
    rw [S.darkFamily.carrier_eq_patch_outerCarrier]
    exact hroot L
  · intro hdark L
    have hL : S.darkCarrier L = ∅ := hdark L
    change S.darkFamily.carrier L = ∅ at hL
    rw [S.darkFamily.carrier_eq_patch_outerCarrier] at hL
    exact hL

theorem hasOuterEnvironment_iff_exists_darkCarrier_nonempty (S : SectorSplitStrong Cell T) :
    S.hasOuterEnvironment ↔ ∃ L : Nat, (S.darkCarrier L).Nonempty := by
  constructor
  · intro hwin
    rcases hwin with ⟨L, hL⟩
    refine ⟨L, ?_⟩
    change (S.darkFamily.carrier L).Nonempty
    rw [S.darkFamily.carrier_eq_patch_outerCarrier]
    exact hL
  · intro hdark
    rcases hdark with ⟨L, hL⟩
    refine ⟨L, ?_⟩
    change (S.darkFamily.carrier L).Nonempty at hL
    rw [S.darkFamily.carrier_eq_patch_outerCarrier] at hL
    exact hL

theorem brightCarrier_disjoint_darkCarrier (S : SectorSplitStrong Cell T) (L : Nat) :
    Disjoint (S.brightCarrier L) (S.darkCarrier L) := by
  exact S.darkFamily.patchCarrier_disjoint L

theorem brightCarrier_union_darkCarrier (S : SectorSplitStrong Cell T) (L : Nat) :
    S.brightCarrier L ∪ S.darkCarrier L = T.carrier L := by
  exact S.darkFamily.patchCarrier_union L

theorem brightSector_subset_brightCarrier (S : SectorSplitStrong Cell T) (L : Nat) :
    S.brightSectorCarrier L ⊆ S.brightCarrier L := by
  exact S.brightPatch.interior_subset_carrier L

theorem darkSector_subset_darkCarrier (S : SectorSplitStrong Cell T) (L : Nat) :
    S.darkSectorCarrier L ⊆ S.darkCarrier L := by
  exact S.darkFamily.interior_subset_carrier L

theorem interface_subset_ambient (S : SectorSplitStrong Cell T) (L : Nat) :
    S.interfaceCarrier L ⊆ T.carrier L := by
  intro x hx
  rcases Finset.mem_union.mp hx with hxBright | hxDark
  · exact S.brightPatch.carrier_subset L (S.brightPatch.boundary_subset_carrier L hxBright)
  · exact S.darkFamily.carrier_subset L (S.darkFamily.boundary_subset_carrier L hxDark)

theorem brightSector_disjoint_darkSector (S : SectorSplitStrong Cell T) (L : Nat) :
    Disjoint (S.brightSectorCarrier L) (S.darkSectorCarrier L) := by
  refine Finset.disjoint_left.mpr ?_
  intro x hxBright hxDark
  have hxBright' : x ∈ S.brightCarrier L :=
    S.brightSector_subset_brightCarrier L hxBright
  have hxDark' : x ∈ S.darkCarrier L :=
    S.darkSector_subset_darkCarrier L hxDark
  exact (Finset.disjoint_left.mp (S.brightCarrier_disjoint_darkCarrier L)) hxBright' hxDark'

theorem brightSector_disjoint_interface (S : SectorSplitStrong Cell T) (L : Nat) :
    Disjoint (S.brightSectorCarrier L) (S.interfaceCarrier L) := by
  refine Finset.disjoint_left.mpr ?_
  intro x hxBright hxInterface
  rcases Finset.mem_union.mp hxInterface with hxBrightBoundary | hxDarkBoundary
  · have hdisj : Disjoint (S.brightBoundaryCarrier L) (S.brightInteriorCarrier L) :=
      S.brightPatch.boundary_disjoint_interior L
    exact (Finset.disjoint_left.mp hdisj) hxBrightBoundary hxBright
  · have hxBrightCarrier : x ∈ S.brightCarrier L :=
      S.brightSector_subset_brightCarrier L hxBright
    have hxDarkCarrier : x ∈ S.darkCarrier L :=
      S.darkFamily.boundary_subset_carrier L hxDarkBoundary
    exact (Finset.disjoint_left.mp (S.brightCarrier_disjoint_darkCarrier L))
      hxBrightCarrier hxDarkCarrier

theorem darkSector_disjoint_interface (S : SectorSplitStrong Cell T) (L : Nat) :
    Disjoint (S.darkSectorCarrier L) (S.interfaceCarrier L) := by
  refine Finset.disjoint_left.mpr ?_
  intro x hxDark hxInterface
  rcases Finset.mem_union.mp hxInterface with hxBrightBoundary | hxDarkBoundary
  · have hxBrightCarrier : x ∈ S.brightCarrier L :=
      S.brightPatch.boundary_subset_carrier L hxBrightBoundary
    have hxDarkCarrier : x ∈ S.darkCarrier L :=
      S.darkSector_subset_darkCarrier L hxDark
    exact (Finset.disjoint_left.mp (S.brightCarrier_disjoint_darkCarrier L))
      hxBrightCarrier hxDarkCarrier
  · have hdisj : Disjoint (S.darkBoundaryCarrier L) (S.darkInteriorCarrier L) :=
      S.darkFamily.boundary_disjoint_interior L
    exact (Finset.disjoint_left.mp hdisj) hxDarkBoundary hxDark

theorem sectorCover (S : SectorSplitStrong Cell T) (L : Nat) :
    S.brightSectorCarrier L ∪ S.interfaceCarrier L ∪ S.darkSectorCarrier L = T.carrier L := by
  have hbright : S.brightInteriorCarrier L ∪ S.brightBoundaryCarrier L = S.brightCarrier L := by
    calc
      S.brightInteriorCarrier L ∪ S.brightBoundaryCarrier L
          = S.brightBoundaryCarrier L ∪ S.brightInteriorCarrier L := by
              exact Finset.union_comm _ _
      _ = S.brightCarrier L := by
              exact S.brightPatch.carrier_union_boundary_interior L
  have hdark : S.darkBoundaryCarrier L ∪ S.darkInteriorCarrier L = S.darkCarrier L := by
    exact S.darkFamily.carrier_union_boundary_interior L
  calc
    S.brightSectorCarrier L ∪ S.interfaceCarrier L ∪ S.darkSectorCarrier L
        = (S.brightInteriorCarrier L ∪ S.brightBoundaryCarrier L) ∪
            (S.darkBoundaryCarrier L ∪ S.darkInteriorCarrier L) := by
              simp [SectorSplitStrong.brightSectorCarrier, SectorSplitStrong.interfaceCarrier,
                SectorSplitStrong.darkSectorCarrier, Finset.union_assoc, Finset.union_left_comm,
                Finset.union_comm]
    _ = S.brightCarrier L ∪ S.darkCarrier L := by
          rw [hbright, hdark]
    _ = T.carrier L := by
          exact S.brightCarrier_union_darkCarrier L

theorem sectorPartition (S : SectorSplitStrong Cell T) (L : Nat) :
    S.brightSectorCarrier L ∪ S.interfaceCarrier L ∪ S.darkSectorCarrier L = T.carrier L ∧
      Disjoint (S.brightSectorCarrier L) (S.interfaceCarrier L) ∧
      Disjoint (S.brightSectorCarrier L) (S.darkSectorCarrier L) ∧
      Disjoint (S.interfaceCarrier L) (S.darkSectorCarrier L) := by
  refine ⟨S.sectorCover L, S.brightSector_disjoint_interface L,
    S.brightSector_disjoint_darkSector L, ?_⟩
  exact Disjoint.symm (S.darkSector_disjoint_interface L)

theorem interfaceRegion_support (S : SectorSplitStrong Cell T) :
    S.interfaceRegion.support = S.interfaceSupport := by
  rfl

theorem interfaceBoundaryPorts_region (S : SectorSplitStrong Cell T) :
    S.interfaceBoundaryPorts.region = S.interfaceRegion := by
  rfl

theorem interfaceSlice_level (S : SectorSplitStrong Cell T) (L : Nat) :
    (S.interfaceSlice L).level = L := by
  exact S.interfaceSupport.slice_level L

theorem topInterfaceSlice_level (S : SectorSplitStrong Cell T) :
    S.topInterfaceSlice.level = T.cutoff := by
  exact S.interfaceSupport.slice_level T.cutoff

end SectorSplitStrong

end CNNA.PillarA.Sectors
