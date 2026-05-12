import CNNA.PillarA.DtN.DtNStabilized

set_option autoImplicit false

namespace CNNA.PillarA.Sectors

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.Finite
open CNNA.PillarA.DtN

universe u

structure BranchPatchStrong (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  source : DtNStabilizedStrong Cell T

abbrev BranchPatchStrongOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  BranchPatchStrong (Cell := Cell) T

namespace BranchPatchStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

@[ext] theorem ext (P Q : BranchPatchStrong Cell T)
    (hsource : P.source = Q.source) :
    P = Q := by
  cases P with
  | mk sourceP =>
    cases Q with
    | mk sourceQ =>
      cases hsource
      rfl

def cast (h : T = U) (P : BranchPatchStrong Cell T) :
    BranchPatchStrong Cell U := by
  cases h
  exact P

theorem cast_rfl (P : BranchPatchStrong Cell T) :
    cast (Cell := Cell) rfl P = P := by
  rfl

def ofDtNStabilized (K : DtNStabilizedStrong Cell T) : BranchPatchStrong Cell T where
  source := K

theorem ofDtNStabilized_source (K : DtNStabilizedStrong Cell T) :
    (ofDtNStabilized K).source = K := by
  rfl

def stabilized (P : BranchPatchStrong Cell T) : DtNStabilizedStrong Cell T :=
  P.source

def dtn (P : BranchPatchStrong Cell T) : DtNStrong Cell T :=
  P.stabilized.source

def dirichlet (P : BranchPatchStrong Cell T) : DirichletLaplacianStrong Cell T :=
  P.dtn.source

def approximant (P : BranchPatchStrong Cell T) : ApproximantStrong Cell T :=
  P.dirichlet.source

def support (P : BranchPatchStrong Cell T) : CutSpec Cell T :=
  P.approximant.support

def region (P : BranchPatchStrong Cell T) : RegionCore Cell T :=
  P.approximant.region

def boundaryPorts (P : BranchPatchStrong Cell T) : BoundaryPorts Cell T :=
  P.approximant.box

theorem dtn_eq_source_source (P : BranchPatchStrong Cell T) :
    P.dtn = P.source.source := by
  rfl

theorem dirichlet_eq_source_source_source (P : BranchPatchStrong Cell T) :
    P.dirichlet = P.source.source.source := by
  rfl

theorem approximant_eq_source_source_source_source (P : BranchPatchStrong Cell T) :
    P.approximant = P.source.source.source.source := by
  rfl

theorem support_eq_approximant_support (P : BranchPatchStrong Cell T) :
    P.support = P.approximant.support := by
  rfl

theorem region_eq_approximant_region (P : BranchPatchStrong Cell T) :
    P.region = P.approximant.region := by
  rfl

theorem boundaryPorts_eq_approximant_box (P : BranchPatchStrong Cell T) :
    P.boundaryPorts = P.approximant.box := by
  rfl

def carrier (P : BranchPatchStrong Cell T) (L : Nat) : Finset (Cell L) :=
  P.approximant.carrier L

def boundaryCarrier (P : BranchPatchStrong Cell T) (L : Nat) : Finset (Cell L) :=
  P.approximant.ports L

def interiorCarrier (P : BranchPatchStrong Cell T) (L : Nat) : Finset (Cell L) :=
  P.approximant.interiorCarrier L

def slice (P : BranchPatchStrong Cell T) (L : Nat) : BoundarySlice Cell :=
  P.approximant.slice L

def interiorSlice (P : BranchPatchStrong Cell T) (L : Nat) : LayerSlice Cell :=
  P.approximant.interiorSlice L

theorem carrier_eq_approximant_carrier (P : BranchPatchStrong Cell T) (L : Nat) :
    P.carrier L = P.approximant.carrier L := by
  rfl

theorem boundaryCarrier_eq_approximant_ports (P : BranchPatchStrong Cell T) (L : Nat) :
    P.boundaryCarrier L = P.approximant.ports L := by
  rfl

theorem interiorCarrier_eq_approximant_interior (P : BranchPatchStrong Cell T) (L : Nat) :
    P.interiorCarrier L = P.approximant.interiorCarrier L := by
  rfl

theorem slice_eq_approximant_slice (P : BranchPatchStrong Cell T) (L : Nat) :
    P.slice L = P.approximant.slice L := by
  rfl

theorem interiorSlice_eq_approximant_interiorSlice (P : BranchPatchStrong Cell T) (L : Nat) :
    P.interiorSlice L = P.approximant.interiorSlice L := by
  rfl

theorem carrier_subset (P : BranchPatchStrong Cell T) (L : Nat) :
    P.carrier L ⊆ T.carrier L := by
  exact P.approximant.carrier_subset L

theorem boundary_subset_carrier (P : BranchPatchStrong Cell T) (L : Nat) :
    P.boundaryCarrier L ⊆ P.carrier L := by
  exact P.approximant.ports_subset_carrier L

theorem interior_subset_carrier (P : BranchPatchStrong Cell T) (L : Nat) :
    P.interiorCarrier L ⊆ P.carrier L := by
  exact P.approximant.interiorCarrier_subset_carrier L

theorem boundary_disjoint_interior (P : BranchPatchStrong Cell T) (L : Nat) :
    Disjoint (P.boundaryCarrier L) (P.interiorCarrier L) := by
  exact Disjoint.symm (P.approximant.interior_boundary_disjoint L)

theorem carrier_union_boundary_interior (P : BranchPatchStrong Cell T) (L : Nat) :
    P.boundaryCarrier L ∪ P.interiorCarrier L = P.carrier L := by
  calc
    P.boundaryCarrier L ∪ P.interiorCarrier L
        = P.interiorCarrier L ∪ P.boundaryCarrier L := by
            exact Finset.union_comm _ _
    _ = P.carrier L := by
            exact P.approximant.carrier_union_interior_ports L

def outerSupport (P : BranchPatchStrong Cell T) : CutSpec Cell T :=
  P.support.exterior

def outerCarrier (P : BranchPatchStrong Cell T) (L : Nat) : Finset (Cell L) :=
  P.outerSupport.carrier L

def outerSlice (P : BranchPatchStrong Cell T) (L : Nat) : LayerSlice Cell :=
  P.outerSupport.slice L

theorem outerCarrier_eq_exterior (P : BranchPatchStrong Cell T) (L : Nat) :
    P.outerCarrier L = (P.support.exterior).carrier L := by
  rfl

theorem outerCarrier_subset (P : BranchPatchStrong Cell T) (L : Nat) :
    P.outerCarrier L ⊆ T.carrier L := by
  exact P.outerSupport.carrier_subset L

theorem carrier_disjoint_outerCarrier (P : BranchPatchStrong Cell T) (L : Nat) :
    Disjoint (P.carrier L) (P.outerCarrier L) := by
  exact P.support.disjoint_carrier_exterior L

theorem carrier_union_outerCarrier (P : BranchPatchStrong Cell T) (L : Nat) :
    P.carrier L ∪ P.outerCarrier L = T.carrier L := by
  exact P.support.carrier_union_exterior L

def rootCentered (P : BranchPatchStrong Cell T) : Prop :=
  ∀ L : Nat, P.outerCarrier L = ∅

def windowed (P : BranchPatchStrong Cell T) : Prop :=
  ∃ L : Nat, (P.outerCarrier L).Nonempty

theorem not_windowed_of_rootCentered (P : BranchPatchStrong Cell T)
    (hroot : P.rootCentered) :
    ¬ P.windowed := by
  intro hwin
  rcases hwin with ⟨L, x, hx⟩
  have hempty : P.outerCarrier L = ∅ := hroot L
  have : x ∈ (∅ : Finset (Cell L)) := by
    rw [← hempty]
    exact hx
  exact (Finset.notMem_empty x) this

theorem not_rootCentered_of_windowed (P : BranchPatchStrong Cell T)
    (hwin : P.windowed) :
    ¬ P.rootCentered := by
  intro hroot
  exact P.not_windowed_of_rootCentered hroot hwin

theorem rootCentered_of_support_eq_full (P : BranchPatchStrong Cell T)
    (hfull : P.support = CutSpec.full T) :
    P.rootCentered := by
  intro L
  ext x
  constructor
  · intro hx
    have hxfull : x ∈ ((CutSpec.full T).exterior).carrier L := by
      rw [BranchPatchStrong.outerCarrier, BranchPatchStrong.outerSupport, hfull] at hx
      exact hx
    have hx' := (CutSpec.mem_exterior_iff (S := CutSpec.full T)).mp hxfull
    exact False.elim (hx'.2 hx'.1)
  · intro hx
    exact False.elim ((Finset.notMem_empty x) hx)

def cutoff (_ : BranchPatchStrong Cell T) : Nat :=
  T.cutoff

def topCarrier (P : BranchPatchStrong Cell T) : Finset (Cell T.cutoff) :=
  P.carrier T.cutoff

def topBoundaryCarrier (P : BranchPatchStrong Cell T) : Finset (Cell T.cutoff) :=
  P.boundaryCarrier T.cutoff

def topInteriorCarrier (P : BranchPatchStrong Cell T) : Finset (Cell T.cutoff) :=
  P.interiorCarrier T.cutoff

def topOuterCarrier (P : BranchPatchStrong Cell T) : Finset (Cell T.cutoff) :=
  P.outerCarrier T.cutoff

def topSlice (P : BranchPatchStrong Cell T) : BoundarySlice Cell :=
  P.slice T.cutoff

def topInteriorSlice (P : BranchPatchStrong Cell T) : LayerSlice Cell :=
  P.interiorSlice T.cutoff

def topOuterSlice (P : BranchPatchStrong Cell T) : LayerSlice Cell :=
  P.outerSlice T.cutoff

theorem topSlice_level (P : BranchPatchStrong Cell T) :
    P.topSlice.level = T.cutoff := by
  exact P.approximant.topSlice_level

theorem topInteriorSlice_level (P : BranchPatchStrong Cell T) :
    P.topInteriorSlice.level = T.cutoff := by
  rfl

theorem topOuterSlice_level (P : BranchPatchStrong Cell T) :
    P.topOuterSlice.level = T.cutoff := by
  exact P.outerSupport.slice_level T.cutoff

end BranchPatchStrong

end CNNA.PillarA.Sectors
