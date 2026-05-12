import CNNA.PillarA.Network.RegionNet

set_option autoImplicit false

namespace CNNA.PillarA.Network

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.Finite
open CNNA.PillarA.Sectors

universe u

structure InfiniteCarrierStrong (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  network : RegionNetStrong Cell T
  ideal : DirectedFamily (Cell := Cell)
  stable : T = ideal.truncate T.cutoff

abbrev InfiniteCarrierStrongOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  InfiniteCarrierStrong (Cell := Cell) T

namespace InfiniteCarrierStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

@[ext] theorem ext (X Y : InfiniteCarrierStrong Cell T)
    (hnetwork : X.network = Y.network)
    (hideal : X.ideal = Y.ideal) :
    X = Y := by
  cases X with
  | mk networkX idealX stableX =>
    cases Y with
    | mk networkY idealY stableY =>
      cases hnetwork
      cases hideal
      have hstable : stableX = stableY := Subsingleton.elim _ _
      cases hstable
      rfl

def cast (h : T = U) (X : InfiniteCarrierStrong Cell T) :
    InfiniteCarrierStrong Cell U := by
  cases h
  exact X

theorem cast_rfl (X : InfiniteCarrierStrong Cell T) :
    cast (Cell := Cell) rfl X = X := by
  rfl

def ofRegionNetAndIdeal
    (N : RegionNetStrong Cell T)
    (F : DirectedFamily (Cell := Cell))
    (hF : T = F.truncate T.cutoff) :
    InfiniteCarrierStrong Cell T where
  network := N
  ideal := F
  stable := hF

theorem ofRegionNetAndIdeal_network
    (N : RegionNetStrong Cell T)
    (F : DirectedFamily (Cell := Cell))
    (hF : T = F.truncate T.cutoff) :
    (ofRegionNetAndIdeal N F hF).network = N := by
  rfl

theorem ofRegionNetAndIdeal_ideal
    (N : RegionNetStrong Cell T)
    (F : DirectedFamily (Cell := Cell))
    (hF : T = F.truncate T.cutoff) :
    (ofRegionNetAndIdeal N F hF).ideal = F := by
  rfl

def regionNet (X : InfiniteCarrierStrong Cell T) : RegionNetStrong Cell T :=
  X.network

def split (X : InfiniteCarrierStrong Cell T) : SectorSplitStrong Cell T :=
  X.network.split

def approximant (X : InfiniteCarrierStrong Cell T) : ApproximantStrong Cell T :=
  X.split.approximant

def cutoff (_ : InfiniteCarrierStrong Cell T) : Nat :=
  T.cutoff

def idealCarrier (X : InfiniteCarrierStrong Cell T) (L : Nat) : Finset (Cell L) :=
  X.ideal.carrier L

def idealSlice (X : InfiniteCarrierStrong Cell T) (L : Nat) : LayerSlice Cell :=
  X.ideal.slice L

def stableCarrier (_ : InfiniteCarrierStrong Cell T) (L : Nat) : Finset (Cell L) :=
  T.carrier L

def stableSlice (_ : InfiniteCarrierStrong Cell T) (L : Nat) : LayerSlice Cell :=
  T.slice L

def stableExcerpt (X : InfiniteCarrierStrong Cell T) (N : Nat) : TruncatedFamily Cell :=
  X.ideal.truncate N

def currentExcerpt (X : InfiniteCarrierStrong Cell T) : TruncatedFamily Cell :=
  X.stableExcerpt T.cutoff

def region (X : InfiniteCarrierStrong Cell T) (K : RegionKind) : RegionCore Cell T :=
  X.network.region K

def boundaryPorts (X : InfiniteCarrierStrong Cell T) (K : RegionKind) : BoundaryPorts Cell T :=
  X.network.boundaryPorts K

def regionCarrier (X : InfiniteCarrierStrong Cell T) (K : RegionKind) (L : Nat) : Finset (Cell L) :=
  X.network.regionCarrier K L

def sectorCarrier (X : InfiniteCarrierStrong Cell T) (K : RegionKind) (L : Nat) : Finset (Cell L) :=
  X.network.sectorCarrier K L

def ports (X : InfiniteCarrierStrong Cell T) (K : RegionKind) (L : Nat) : Finset (Cell L) :=
  X.network.ports K L

def interiorCarrier (X : InfiniteCarrierStrong Cell T) (K : RegionKind) (L : Nat) : Finset (Cell L) :=
  X.network.interiorCarrier K L

def noOuterEnvironment (X : InfiniteCarrierStrong Cell T) : Prop :=
  X.network.noOuterEnvironment

def hasOuterEnvironment (X : InfiniteCarrierStrong Cell T) : Prop :=
  X.network.hasOuterEnvironment

def rootCentered (X : InfiniteCarrierStrong Cell T) : Prop :=
  X.network.rootCentered

def windowed (X : InfiniteCarrierStrong Cell T) : Prop :=
  X.network.windowed

theorem stable_eq_truncate (X : InfiniteCarrierStrong Cell T) :
    T = X.ideal.truncate T.cutoff := by
  exact X.stable

theorem stableCarrier_eq (X : InfiniteCarrierStrong Cell T) (L : Nat) :
    X.stableCarrier L = T.carrier L := by
  rfl

theorem stableSlice_level (X : InfiniteCarrierStrong Cell T) (L : Nat) :
    (X.stableSlice L).level = L := by
  rfl

theorem stableSlice_carrier (X : InfiniteCarrierStrong Cell T) (L : Nat) :
    (X.stableSlice L).carrier = X.stableCarrier L := by
  rfl

theorem stableExcerpt_cutoff (X : InfiniteCarrierStrong Cell T) (N : Nat) :
    (X.stableExcerpt N).cutoff = N := by
  exact DirectedFamily.truncate_cutoff (F := X.ideal) N

theorem currentExcerpt_eq_stable (X : InfiniteCarrierStrong Cell T) :
    X.currentExcerpt = T := by
  unfold currentExcerpt stableExcerpt
  exact X.stable_eq_truncate.symm

theorem idealSlice_level (X : InfiniteCarrierStrong Cell T) (L : Nat) :
    (X.idealSlice L).level = L := by
  exact DirectedFamily.slice_level (F := X.ideal) L

theorem idealSlice_carrier (X : InfiniteCarrierStrong Cell T) (L : Nat) :
    (X.idealSlice L).carrier = X.idealCarrier L := by
  exact DirectedFamily.slice_carrier (F := X.ideal) L

theorem stableCarrier_eq_ideal_of_le
    (X : InfiniteCarrierStrong Cell T) {L : Nat} (hL : L ≤ T.cutoff) :
    X.stableCarrier L = X.idealCarrier L := by
  rcases X with ⟨network, ideal, stable⟩
  change T.carrier L = ideal.carrier L
  rw [stable]
  exact DirectedFamily.truncate_carrier_of_le (F := ideal) (L := L) (N := T.cutoff) hL

theorem stableCarrier_eq_empty_of_gt
    (X : InfiniteCarrierStrong Cell T) {L : Nat} (hL : T.cutoff < L) :
    X.stableCarrier L = ∅ := by
  rcases X with ⟨network, ideal, stable⟩
  change T.carrier L = ∅
  rw [stable]
  exact DirectedFamily.truncate_carrier_of_gt (F := ideal) (L := L) (N := T.cutoff) hL

theorem excerptCarrier_eq_ideal_of_le
    (X : InfiniteCarrierStrong Cell T) (N : Nat) {L : Nat} (hL : L ≤ N) :
    (X.stableExcerpt N).carrier L = X.idealCarrier L := by
  exact DirectedFamily.truncate_carrier_of_le (F := X.ideal) (L := L) (N := N) hL

theorem excerptCarrier_eq_empty_of_gt
    (X : InfiniteCarrierStrong Cell T) (N : Nat) {L : Nat} (hL : N < L) :
    (X.stableExcerpt N).carrier L = ∅ := by
  exact DirectedFamily.truncate_carrier_of_gt (F := X.ideal) (L := L) (N := N) hL

theorem excerptTopSlice_carrier
    (X : InfiniteCarrierStrong Cell T) (N : Nat) :
    (X.stableExcerpt N).topSlice.carrier = X.idealCarrier N := by
  exact DirectedFamily.truncate_topSlice_carrier (F := X.ideal) N

theorem excerptCarrier_stable_under_le
    (X : InfiniteCarrierStrong Cell T) {N M L : Nat}
    (hNM : N ≤ M) (hL : L ≤ N) :
    (X.stableExcerpt N).carrier L = (X.stableExcerpt M).carrier L := by
  calc
    (X.stableExcerpt N).carrier L = X.idealCarrier L :=
      X.excerptCarrier_eq_ideal_of_le N hL
    _ = (X.stableExcerpt M).carrier L := by
      symm
      exact X.excerptCarrier_eq_ideal_of_le M (le_trans hL hNM)

theorem topStableCarrier_eq_ideal
    (X : InfiniteCarrierStrong Cell T) :
    X.stableCarrier T.cutoff = X.idealCarrier T.cutoff := by
  exact X.stableCarrier_eq_ideal_of_le le_rfl

theorem topSlice_carrier_eq_ideal
    (X : InfiniteCarrierStrong Cell T) :
    T.topSlice.carrier = X.idealCarrier T.cutoff := by
  calc
    T.topSlice.carrier = T.carrier T.cutoff := by
      exact TruncatedFamily.topSlice_carrier T
    _ = X.stableCarrier T.cutoff := by
      rfl
    _ = X.idealCarrier T.cutoff := X.topStableCarrier_eq_ideal

theorem ideal_root_mem (X : InfiniteCarrierStrong Cell T) :
    SubstrateClass.root (Cell := Cell) ∈ X.idealCarrier 0 := by
  exact DirectedFamily.root_mem (F := X.ideal)

theorem stable_root_mem (X : InfiniteCarrierStrong Cell T) :
    SubstrateClass.root (Cell := Cell) ∈ X.stableCarrier 0 := by
  change SubstrateClass.root (Cell := Cell) ∈ T.carrier 0
  exact TruncatedFamily.root_mem T

theorem ideal_forward_mem (X : InfiniteCarrierStrong Cell T) {L : Nat}
    {x : Cell (L + 1)} (hx : x ∈ X.idealCarrier (L + 1)) :
    x ∈ RefineSetOf (Cell := Cell) (X.idealCarrier L) := by
  exact DirectedFamily.forward_mem (F := X.ideal) hx

theorem excerpt_root_mem (X : InfiniteCarrierStrong Cell T) (N : Nat) :
    SubstrateClass.root (Cell := Cell) ∈ (X.stableExcerpt N).carrier 0 := by
  have hroot : SubstrateClass.root (Cell := Cell) ∈ X.idealCarrier 0 :=
    X.ideal_root_mem
  have hzero : 0 ≤ N := Nat.zero_le N
  rw [X.excerptCarrier_eq_ideal_of_le N hzero]
  exact hroot

theorem split_eq_network_split (X : InfiniteCarrierStrong Cell T) :
    X.split = X.network.split := by
  rfl

theorem approximant_eq_split_approximant (X : InfiniteCarrierStrong Cell T) :
    X.approximant = X.split.approximant := by
  rfl

theorem region_eq_network_region
    (X : InfiniteCarrierStrong Cell T) (K : RegionKind) :
    X.region K = X.network.region K := by
  rfl

theorem boundaryPorts_eq_network_boundaryPorts
    (X : InfiniteCarrierStrong Cell T) (K : RegionKind) :
    X.boundaryPorts K = X.network.boundaryPorts K := by
  rfl

theorem regionCarrier_eq_network_regionCarrier
    (X : InfiniteCarrierStrong Cell T) (K : RegionKind) (L : Nat) :
    X.regionCarrier K L = X.network.regionCarrier K L := by
  rfl

theorem sectorCarrier_eq_network_sectorCarrier
    (X : InfiniteCarrierStrong Cell T) (K : RegionKind) (L : Nat) :
    X.sectorCarrier K L = X.network.sectorCarrier K L := by
  rfl

theorem ports_eq_network_ports
    (X : InfiniteCarrierStrong Cell T) (K : RegionKind) (L : Nat) :
    X.ports K L = X.network.ports K L := by
  rfl

theorem interiorCarrier_eq_network_interiorCarrier
    (X : InfiniteCarrierStrong Cell T) (K : RegionKind) (L : Nat) :
    X.interiorCarrier K L = X.network.interiorCarrier K L := by
  rfl

theorem noOuterEnvironment_iff_network (X : InfiniteCarrierStrong Cell T) :
    X.noOuterEnvironment ↔ X.network.noOuterEnvironment := by
  rfl

theorem hasOuterEnvironment_iff_network (X : InfiniteCarrierStrong Cell T) :
    X.hasOuterEnvironment ↔ X.network.hasOuterEnvironment := by
  rfl

theorem rootCentered_iff_network (X : InfiniteCarrierStrong Cell T) :
    X.rootCentered ↔ X.network.rootCentered := by
  rfl

theorem windowed_iff_network (X : InfiniteCarrierStrong Cell T) :
    X.windowed ↔ X.network.windowed := by
  rfl

theorem sectorCover (X : InfiniteCarrierStrong Cell T) (L : Nat) :
    X.sectorCarrier .bright L ∪ X.sectorCarrier .interface L ∪ X.sectorCarrier .dark L =
      T.carrier L := by
  exact X.network.sectorCover L

theorem sectorPartition (X : InfiniteCarrierStrong Cell T) (L : Nat) :
    X.sectorCarrier .bright L ∪ X.sectorCarrier .interface L ∪ X.sectorCarrier .dark L =
        T.carrier L ∧
      Disjoint (X.sectorCarrier .bright L) (X.sectorCarrier .interface L) ∧
      Disjoint (X.sectorCarrier .bright L) (X.sectorCarrier .dark L) ∧
      Disjoint (X.sectorCarrier .interface L) (X.sectorCarrier .dark L) := by
  exact X.network.sectorPartition L


end InfiniteCarrierStrong

namespace StrengtheningS7

open CNNA.PillarA.DtN
open CNNA.PillarA.Finite.StrengtheningS5
open CNNA.PillarA.DtN.StrengtheningS5
open CNNA.PillarA.DtN.StrengtheningS6


private theorem approximant_eq_ideal_truncate_at_cutoff
    {Cell : Nat → Type u} [SubstrateClass Cell]
    (X : ToCStrongOf Cell) (p : ConcretePolicyOf) :
    X.approximant p = X.ideal.truncate (X.approximant p).cutoff := by
  have happ : X.approximant p = X.ideal.truncate p.L_max :=
    ToCStrong.approximant_eq_truncate (T := X) p
  have hcutoff : (X.approximant p).cutoff = p.L_max := by
    rw [happ]
    exact DirectedFamily.truncate_cutoff (F := X.ideal) p.L_max
  calc
    X.approximant p = X.ideal.truncate p.L_max := happ
    _ = X.ideal.truncate (X.approximant p).cutoff := by
      rw [hcutoff]

private def fullInfiniteCarrierFromToC
    {Cell : Nat → Type u} [SubstrateClass Cell]
    (X : ToCStrongOf Cell) (p : ConcretePolicyOf)
    (N : RegionNetStrong Cell (X.approximant p)) :
    InfiniteCarrierStrong Cell (X.approximant p) :=
  InfiniteCarrierStrong.ofRegionNetAndIdeal N X.ideal
    (approximant_eq_ideal_truncate_at_cutoff X p)

def referenceFullInfiniteCarrier (b : Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy := referenceDefaultWeightPolicy b)
    (rp : RegularizationPolicy := referenceDefaultRegularizationPolicy)
    [ReferenceInteriorEliminationData b p wp]
    : InfiniteCarrierStrongOf (ReferenceIdealCellOf b) ((referenceToC b).approximant p) :=
  fullInfiniteCarrierFromToC (referenceToC b) p <|
    referenceFullRegionNet b p wp rp

def variationFullInfiniteCarrier (β : Nat → Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy) (rp : RegularizationPolicy)
    [VariationInteriorEliminationData β p wp]
    : InfiniteCarrierStrongOf (VariationIdealCellOf β) ((variationToC β).approximant p) :=
  fullInfiniteCarrierFromToC (variationToC β) p <|
    variationFullRegionNet β p wp rp

end StrengtheningS7

end CNNA.PillarA.Network
