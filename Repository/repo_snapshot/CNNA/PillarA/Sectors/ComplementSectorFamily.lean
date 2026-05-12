import CNNA.PillarA.Sectors.BranchPatch

set_option autoImplicit false

namespace CNNA.PillarA.Sectors

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.Finite
open CNNA.PillarA.DtN

universe u

structure ComplementSectorFamilyStrong (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  source : BranchPatchStrong Cell T

abbrev ComplementSectorFamilyStrongOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  ComplementSectorFamilyStrong (Cell := Cell) T

namespace ComplementSectorFamilyStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

@[ext] theorem ext (C D : ComplementSectorFamilyStrong Cell T)
    (hsource : C.source = D.source) :
    C = D := by
  cases C with
  | mk sourceC =>
    cases D with
    | mk sourceD =>
      cases hsource
      rfl

def cast (h : T = U) (C : ComplementSectorFamilyStrong Cell T) :
    ComplementSectorFamilyStrong Cell U := by
  cases h
  exact C

theorem cast_rfl (C : ComplementSectorFamilyStrong Cell T) :
    cast (Cell := Cell) rfl C = C := by
  rfl

def ofBranchPatch (P : BranchPatchStrong Cell T) : ComplementSectorFamilyStrong Cell T where
  source := P

theorem ofBranchPatch_source (P : BranchPatchStrong Cell T) :
    (ofBranchPatch P).source = P := by
  rfl

def patch (C : ComplementSectorFamilyStrong Cell T) : BranchPatchStrong Cell T :=
  C.source

def stabilized (C : ComplementSectorFamilyStrong Cell T) : DtNStabilizedStrong Cell T :=
  C.patch.stabilized

def support (C : ComplementSectorFamilyStrong Cell T) : CutSpec Cell T :=
  C.patch.outerSupport

def region (C : ComplementSectorFamilyStrong Cell T) : RegionCore Cell T :=
  RegionCore.ofCutSpec C.support

def boundaryPorts (C : ComplementSectorFamilyStrong Cell T) : BoundaryPorts Cell T :=
  BoundaryPorts.ofRegion C.region

theorem support_eq_patch_outerSupport (C : ComplementSectorFamilyStrong Cell T) :
    C.support = C.patch.outerSupport := by
  rfl

theorem region_support (C : ComplementSectorFamilyStrong Cell T) :
    C.region.support = C.support := by
  rfl

theorem boundaryPorts_region (C : ComplementSectorFamilyStrong Cell T) :
    C.boundaryPorts.region = C.region := by
  rfl

def carrier (C : ComplementSectorFamilyStrong Cell T) (L : Nat) : Finset (Cell L) :=
  C.region.carrier L

def boundaryCarrier (C : ComplementSectorFamilyStrong Cell T) (L : Nat) : Finset (Cell L) :=
  C.boundaryPorts.ports L

def interiorCarrier (C : ComplementSectorFamilyStrong Cell T) (L : Nat) : Finset (Cell L) :=
  C.boundaryPorts.interiorCarrier L

def slice (C : ComplementSectorFamilyStrong Cell T) (L : Nat) : BoundarySlice Cell :=
  C.boundaryPorts.slice L

def interiorSlice (C : ComplementSectorFamilyStrong Cell T) (L : Nat) : LayerSlice Cell :=
  C.region.interiorSlice L

theorem carrier_eq_patch_outerCarrier (C : ComplementSectorFamilyStrong Cell T) (L : Nat) :
    C.carrier L = C.patch.outerCarrier L := by
  rfl

theorem carrier_subset (C : ComplementSectorFamilyStrong Cell T) (L : Nat) :
    C.carrier L ⊆ T.carrier L := by
  exact C.region.carrier_subset L

theorem boundary_subset_carrier (C : ComplementSectorFamilyStrong Cell T) (L : Nat) :
    C.boundaryCarrier L ⊆ C.carrier L := by
  exact C.boundaryPorts.ports_subset_carrier L

theorem interior_subset_carrier (C : ComplementSectorFamilyStrong Cell T) (L : Nat) :
    C.interiorCarrier L ⊆ C.carrier L := by
  exact C.boundaryPorts.interiorCarrier_subset_carrier L

theorem boundary_disjoint_interior (C : ComplementSectorFamilyStrong Cell T) (L : Nat) :
    Disjoint (C.boundaryCarrier L) (C.interiorCarrier L) := by
  exact Disjoint.symm (C.boundaryPorts.interior_boundary_disjoint L)

theorem carrier_union_boundary_interior (C : ComplementSectorFamilyStrong Cell T) (L : Nat) :
    C.boundaryCarrier L ∪ C.interiorCarrier L = C.carrier L := by
  calc
    C.boundaryCarrier L ∪ C.interiorCarrier L
        = C.interiorCarrier L ∪ C.boundaryCarrier L := by
            exact Finset.union_comm _ _
    _ = C.carrier L := by
            exact C.boundaryPorts.carrier_union_interior_ports L

theorem patchCarrier_disjoint (C : ComplementSectorFamilyStrong Cell T) (L : Nat) :
    Disjoint (C.patch.carrier L) (C.carrier L) := by
  exact C.patch.carrier_disjoint_outerCarrier L

theorem patchCarrier_union (C : ComplementSectorFamilyStrong Cell T) (L : Nat) :
    C.patch.carrier L ∪ C.carrier L = T.carrier L := by
  exact C.patch.carrier_union_outerCarrier L

def rootCentered (C : ComplementSectorFamilyStrong Cell T) : Prop :=
  C.patch.rootCentered

def windowed (C : ComplementSectorFamilyStrong Cell T) : Prop :=
  C.patch.windowed

theorem not_windowed_of_rootCentered (C : ComplementSectorFamilyStrong Cell T)
    (hroot : C.rootCentered) :
    ¬ C.windowed := by
  exact C.patch.not_windowed_of_rootCentered hroot

theorem not_rootCentered_of_windowed (C : ComplementSectorFamilyStrong Cell T)
    (hwin : C.windowed) :
    ¬ C.rootCentered := by
  exact C.patch.not_rootCentered_of_windowed hwin

theorem rootCentered_of_patch_support_eq_full (C : ComplementSectorFamilyStrong Cell T)
    (hfull : C.patch.support = CutSpec.full T) :
    C.rootCentered := by
  exact C.patch.rootCentered_of_support_eq_full hfull

def cutoff (_ : ComplementSectorFamilyStrong Cell T) : Nat :=
  T.cutoff

def topCarrier (C : ComplementSectorFamilyStrong Cell T) : Finset (Cell T.cutoff) :=
  C.carrier T.cutoff

def topBoundaryCarrier (C : ComplementSectorFamilyStrong Cell T) : Finset (Cell T.cutoff) :=
  C.boundaryCarrier T.cutoff

def topInteriorCarrier (C : ComplementSectorFamilyStrong Cell T) : Finset (Cell T.cutoff) :=
  C.interiorCarrier T.cutoff

def topSlice (C : ComplementSectorFamilyStrong Cell T) : BoundarySlice Cell :=
  C.slice T.cutoff

def topInteriorSlice (C : ComplementSectorFamilyStrong Cell T) : LayerSlice Cell :=
  C.interiorSlice T.cutoff

theorem topSlice_level (C : ComplementSectorFamilyStrong Cell T) :
    C.topSlice.level = T.cutoff := by
  exact C.boundaryPorts.slice_level T.cutoff

theorem topInteriorSlice_level (C : ComplementSectorFamilyStrong Cell T) :
    C.topInteriorSlice.level = T.cutoff := by
  exact C.region.interiorSlice_level T.cutoff

end ComplementSectorFamilyStrong

end CNNA.PillarA.Sectors
