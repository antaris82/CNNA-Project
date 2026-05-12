import CNNA.PillarA.Finite.Approximant

set_option autoImplicit false

namespace CNNA.PillarA.Finite

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

structure SelectionStrong (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  source : ApproximantStrong Cell T
  carrier : ∀ L : Nat, Finset (Cell L)
  carrier_subset : ∀ L : Nat, carrier L ⊆ source.carrier L

abbrev SelectionStrongOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  SelectionStrong (Cell := Cell) T

abbrev SelectionOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  SelectionStrong (Cell := Cell) T

namespace SelectionStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

@[ext] theorem ext (S R : SelectionStrong Cell T)
    (hsource : S.source = R.source)
    (hcarrier : ∀ L : Nat, S.carrier L = R.carrier L) :
    S = R := by
  cases S with
  | mk sourceS carrierS subsetS =>
    cases R with
    | mk sourceR carrierR subsetR =>
      cases hsource
      have hcarrierFun : carrierS = carrierR := by
        funext L
        exact hcarrier L
      cases hcarrierFun
      have hsubset : subsetS = subsetR := by
        apply Subsingleton.elim
      cases hsubset
      rfl

def cast (h : T = U) (S : SelectionStrong Cell T) :
    SelectionStrong Cell U := by
  cases h
  exact S

theorem cast_rfl (S : SelectionStrong Cell T) :
    cast (Cell := Cell) rfl S = S := by
  rfl

def ofCarrier (A : ApproximantStrong Cell T)
    (s : ∀ L : Nat, Finset (Cell L))
    (hs : ∀ L : Nat, s L ⊆ A.carrier L) :
    SelectionStrong Cell T where
  source := A
  carrier := s
  carrier_subset := hs

def full (A : ApproximantStrong Cell T) : SelectionStrong Cell T where
  source := A
  carrier := A.carrier
  carrier_subset := by
    intro L x hx
    exact hx

def boundary (A : ApproximantStrong Cell T) : SelectionStrong Cell T where
  source := A
  carrier := A.ports
  carrier_subset := A.ports_subset_carrier

def interior (A : ApproximantStrong Cell T) : SelectionStrong Cell T where
  source := A
  carrier := A.interiorCarrier
  carrier_subset := A.interiorCarrier_subset_carrier

def support (S : SelectionStrong Cell T) : CutSpec Cell T :=
  S.source.support

theorem support_eq (S : SelectionStrong Cell T) :
    S.support = S.source.support := by
  rfl

def region (S : SelectionStrong Cell T) : RegionCore Cell T :=
  S.source.region

theorem region_eq (S : SelectionStrong Cell T) :
    S.region = S.source.region := by
  rfl

theorem carrier_subset_source (S : SelectionStrong Cell T) (L : Nat) :
    S.carrier L ⊆ S.source.carrier L :=
  S.carrier_subset L

def slice (S : SelectionStrong Cell T) (L : Nat) : LayerSlice Cell :=
  { level := L
    carrier := S.carrier L }

theorem slice_level (S : SelectionStrong Cell T) (L : Nat) :
    (S.slice L).level = L := by
  rfl

theorem slice_carrier (S : SelectionStrong Cell T) (L : Nat) :
    (S.slice L).carrier = S.carrier L := by
  rfl

def cutoff (S : SelectionStrong Cell T) : Nat :=
  S.source.cutoff

theorem cutoff_eq_source (S : SelectionStrong Cell T) :
    S.cutoff = S.source.cutoff := by
  rfl

def topCarrier (S : SelectionStrong Cell T) : Finset (Cell T.cutoff) :=
  S.carrier T.cutoff

def topSlice (S : SelectionStrong Cell T) : LayerSlice Cell :=
  S.slice T.cutoff

theorem topSlice_level (S : SelectionStrong Cell T) :
    S.topSlice.level = T.cutoff := by
  exact S.slice_level T.cutoff

theorem topSlice_carrier (S : SelectionStrong Cell T) :
    S.topSlice.carrier = S.topCarrier := by
  rfl

def selectedPorts (S : SelectionStrong Cell T) (L : Nat) : Finset (Cell L) :=
  (S.carrier L).filter (fun x => x ∈ S.source.ports L)

theorem selectedPorts_subset_carrier (S : SelectionStrong Cell T) (L : Nat) :
    S.selectedPorts L ⊆ S.carrier L := by
  intro x hx
  exact (Finset.mem_filter.mp hx).1

theorem selectedPorts_subset_ports (S : SelectionStrong Cell T) (L : Nat) :
    S.selectedPorts L ⊆ S.source.ports L := by
  intro x hx
  exact (Finset.mem_filter.mp hx).2

def selectedInterior (S : SelectionStrong Cell T) (L : Nat) : Finset (Cell L) :=
  (S.carrier L).filter (fun x => x ∈ S.source.interiorCarrier L)

theorem selectedInterior_subset_carrier (S : SelectionStrong Cell T) (L : Nat) :
    S.selectedInterior L ⊆ S.carrier L := by
  intro x hx
  exact (Finset.mem_filter.mp hx).1

theorem selectedInterior_subset_sourceInterior (S : SelectionStrong Cell T) (L : Nat) :
    S.selectedInterior L ⊆ S.source.interiorCarrier L := by
  intro x hx
  exact (Finset.mem_filter.mp hx).2

end SelectionStrong

namespace ApproximantStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}

def fullSelection (A : ApproximantStrong Cell T) : SelectionStrong Cell T :=
  SelectionStrong.full A

def boundarySelection (A : ApproximantStrong Cell T) : SelectionStrong Cell T :=
  SelectionStrong.boundary A

def interiorSelection (A : ApproximantStrong Cell T) : SelectionStrong Cell T :=
  SelectionStrong.interior A

end ApproximantStrong


namespace StrengtheningS4

def referenceFullSelection (b : Nat) (p : ConcretePolicyOf) :
    SelectionStrongOf (ReferenceIdealCellOf b) ((referenceToC b).approximant p) :=
  ApproximantStrong.fullSelection (StrengtheningS4.referenceFullApproximant b p)

def variationFullSelection (β : Nat → Nat) (p : ConcretePolicyOf) :
    SelectionStrongOf (VariationIdealCellOf β) ((variationToC β).approximant p) :=
  ApproximantStrong.fullSelection (StrengtheningS4.variationFullApproximant β p)

end StrengtheningS4

end CNNA.PillarA.Finite
