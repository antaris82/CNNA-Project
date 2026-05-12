import CNNA.PillarA.Arithmetic.Core.FullBoundaryAudit

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.Finite

universe u

namespace ExistingIdealThreadNoGo

variable {Cell : Nat → Type u} [SubstrateClass Cell]

abbrev SingletonCarrierAt (S : ∀ L : Nat, Finset (Cell L)) (L : Nat) (x : Cell L) : Prop :=
  S L = ({x} : Finset (Cell L))

abbrev BoundaryPortsUseOnlyCarrier
    (T : TruncatedFamily Cell) (B : BoundaryPorts Cell T) (L : Nat) : Prop :=
  B.ports L ⊆ T.carrier L

structure IdealThreadSubstrateNoGo (U : IdealThread Cell) where
  familyCarrierSingleton : ∀ L : Nat,
    U.family.carrier L = ({U.cell L} : Finset (Cell L))
  approximantCarrierSingletonOfLe : ∀ (p : ConcretePolicyOf) {L : Nat}, L ≤ p.L_max →
    (U.family.truncate p.L_max).carrier L = ({U.cell L} : Finset (Cell L))
  anyBoundaryPortsSubsetSingletonOfLe :
    ∀ (p : ConcretePolicyOf)
      (B : BoundaryPorts Cell (U.family.truncate p.L_max)) {L : Nat}, L ≤ p.L_max →
      B.ports L ⊆ ({U.cell L} : Finset (Cell L))
  noGeneratedNonSingletonCarrierFromThisRoute : True
  noCutSpecCarrierClaimForLevelHistory : True

namespace IdealThreadSubstrateNoGo

variable (U : IdealThread Cell)

theorem family_carrier_eq_singleton (L : Nat) :
    U.family.carrier L = ({U.cell L} : Finset (Cell L)) := by
  rfl

theorem approximant_carrier_eq_singleton_of_le
    (p : ConcretePolicyOf) {L : Nat} (hL : L ≤ p.L_max) :
    (U.family.truncate p.L_max).carrier L = ({U.cell L} : Finset (Cell L)) := by
  rw [DirectedFamily.truncate_carrier_of_le (F := U.family) (L := L) (N := p.L_max) hL]
  exact family_carrier_eq_singleton (Cell := Cell) U L

theorem boundaryPorts_use_only_carrier
    (T : TruncatedFamily Cell) (B : BoundaryPorts Cell T) (L : Nat) :
    BoundaryPortsUseOnlyCarrier (Cell := Cell) T B L := by
  intro x hx
  have hxRegion : x ∈ B.region.carrier L := by
    exact ((BoundaryPorts.mem_ports_iff B).mp hx).1
  exact B.region.carrier_subset L hxRegion

theorem anyBoundaryPorts_subset_singleton_of_le
    (p : ConcretePolicyOf) (B : BoundaryPorts Cell (U.family.truncate p.L_max))
    {L : Nat} (hL : L ≤ p.L_max) :
    B.ports L ⊆ ({U.cell L} : Finset (Cell L)) := by
  intro x hx
  have hxCarrier : x ∈ (U.family.truncate p.L_max).carrier L := by
    exact boundaryPorts_use_only_carrier
      (Cell := Cell) (T := U.family.truncate p.L_max) B L hx
  rw [approximant_carrier_eq_singleton_of_le (Cell := Cell) U p hL] at hxCarrier
  exact hxCarrier

def ofIdealThread : IdealThreadSubstrateNoGo U where
  familyCarrierSingleton := by
    intro L
    exact family_carrier_eq_singleton (Cell := Cell) U L
  approximantCarrierSingletonOfLe := by
    intro p L hL
    exact approximant_carrier_eq_singleton_of_le (Cell := Cell) U p hL
  anyBoundaryPortsSubsetSingletonOfLe := by
    intro p B L hL
    exact anyBoundaryPorts_subset_singleton_of_le (Cell := Cell) U p B hL
  noGeneratedNonSingletonCarrierFromThisRoute := True.intro
  noCutSpecCarrierClaimForLevelHistory := True.intro

end IdealThreadSubstrateNoGo

theorem referenceFamily_carrier_eq_singleton (b L : Nat) :
    (ConcreteIdeal.referenceFamily b).carrier L =
      ({ConcreteSubstrate.zeroCell b L} : Finset (ReferenceIdealCellOf b L)) := by
  rfl

theorem variationFamily_carrier_eq_singleton (β : Nat → Nat) (L : Nat) :
    (variationFamily β).carrier L =
      ({LevelVariableSubstrate.zeroCell β L} : Finset (VariationIdealCellOf β L)) := by
  rfl

theorem referenceApproximant_carrier_eq_singleton_of_le
    (b : Nat) (p : ConcretePolicyOf) {L : Nat} (hL : L ≤ p.L_max) :
    ((referenceToC b).approximant p).carrier L =
      ({ConcreteSubstrate.zeroCell b L} : Finset (ReferenceIdealCellOf b L)) := by
  rw [referenceToC_approximant_eq_truncate]
  rw [DirectedFamily.truncate_carrier_of_le
    (F := ConcreteIdeal.referenceFamily b) (L := L) (N := p.L_max) hL]
  exact referenceFamily_carrier_eq_singleton b L

theorem variationApproximant_carrier_eq_singleton_of_le
    (β : Nat → Nat) (p : ConcretePolicyOf) {L : Nat} (hL : L ≤ p.L_max) :
    ((variationToC β).approximant p).carrier L =
      ({LevelVariableSubstrate.zeroCell β L} : Finset (VariationIdealCellOf β L)) := by
  rw [variationToC_approximant_eq_truncate]
  rw [DirectedFamily.truncate_carrier_of_le
    (F := variationFamily β) (L := L) (N := p.L_max) hL]
  exact variationFamily_carrier_eq_singleton β L

theorem referenceBoundaryPorts_subset_singleton_of_le
    (b : Nat) (p : ConcretePolicyOf)
    (B : BoundaryPorts (ReferenceIdealCellOf b) ((referenceToC b).approximant p))
    {L : Nat} (hL : L ≤ p.L_max) :
    B.ports L ⊆ ({ConcreteSubstrate.zeroCell b L} : Finset (ReferenceIdealCellOf b L)) := by
  intro x hx
  have hxCarrier : x ∈ ((referenceToC b).approximant p).carrier L := by
    have hxRegion : x ∈ B.region.carrier L := by
      exact ((BoundaryPorts.mem_ports_iff B).mp hx).1
    exact B.region.carrier_subset L hxRegion
  rw [referenceApproximant_carrier_eq_singleton_of_le b p hL] at hxCarrier
  exact hxCarrier

theorem variationBoundaryPorts_subset_singleton_of_le
    (β : Nat → Nat) (p : ConcretePolicyOf)
    (B : BoundaryPorts (VariationIdealCellOf β) ((variationToC β).approximant p))
    {L : Nat} (hL : L ≤ p.L_max) :
    B.ports L ⊆ ({LevelVariableSubstrate.zeroCell β L} : Finset (VariationIdealCellOf β L)) := by
  intro x hx
  have hxCarrier : x ∈ ((variationToC β).approximant p).carrier L := by
    have hxRegion : x ∈ B.region.carrier L := by
      exact ((BoundaryPorts.mem_ports_iff B).mp hx).1
    exact B.region.carrier_subset L hxRegion
  rw [variationApproximant_carrier_eq_singleton_of_le β p hL] at hxCarrier
  exact hxCarrier

structure ReferenceCutSpecNoGo (b : Nat) (p : ConcretePolicyOf) where
  sourceIsOfIdeal : (referenceToC b).ideal = ConcreteIdeal.referenceFamily b
  familyCarrierSingleton : ∀ L : Nat,
    (ConcreteIdeal.referenceFamily b).carrier L =
      ({ConcreteSubstrate.zeroCell b L} : Finset (ReferenceIdealCellOf b L))
  approximantCarrierSingletonOfLe : ∀ {L : Nat}, L ≤ p.L_max →
    ((referenceToC b).approximant p).carrier L =
      ({ConcreteSubstrate.zeroCell b L} : Finset (ReferenceIdealCellOf b L))
  anyBoundaryPortsSubsetSingletonOfLe :
    ∀ (B : BoundaryPorts (ReferenceIdealCellOf b) ((referenceToC b).approximant p))
      {L : Nat}, L ≤ p.L_max →
      B.ports L ⊆ ({ConcreteSubstrate.zeroCell b L} : Finset (ReferenceIdealCellOf b L))
  noGeneratedNonSingletonCarrierFromExistingIdealThread : True
  noCutSpecCarrierClaimForLevelHistory : True

structure VariationCutSpecNoGo (β : Nat → Nat) (p : ConcretePolicyOf) where
  sourceIsOfIdeal : (variationToC β).ideal = variationFamily β
  familyCarrierSingleton : ∀ L : Nat,
    (variationFamily β).carrier L =
      ({LevelVariableSubstrate.zeroCell β L} : Finset (VariationIdealCellOf β L))
  approximantCarrierSingletonOfLe : ∀ {L : Nat}, L ≤ p.L_max →
    ((variationToC β).approximant p).carrier L =
      ({LevelVariableSubstrate.zeroCell β L} : Finset (VariationIdealCellOf β L))
  anyBoundaryPortsSubsetSingletonOfLe :
    ∀ (B : BoundaryPorts (VariationIdealCellOf β) ((variationToC β).approximant p))
      {L : Nat}, L ≤ p.L_max →
      B.ports L ⊆ ({LevelVariableSubstrate.zeroCell β L} : Finset (VariationIdealCellOf β L))
  noGeneratedNonSingletonCarrierFromExistingIdealThread : True
  noCutSpecCarrierClaimForLevelHistory : True

structure ExistingIdealThreadSubstrateNoGo (p : ConcretePolicyOf) where
  reference : ∀ b : Nat, ReferenceCutSpecNoGo b p
  variation : ∀ β : Nat → Nat, VariationCutSpecNoGo β p
  generatedRouteStillConditional : True
  recursiveHistoryRouteNotConstructedHere : True

def referenceCutSpecNoGo (b : Nat) (p : ConcretePolicyOf) :
    ReferenceCutSpecNoGo b p where
  sourceIsOfIdeal := by
    exact referenceToC_ideal b
  familyCarrierSingleton := by
    intro L
    exact referenceFamily_carrier_eq_singleton b L
  approximantCarrierSingletonOfLe := by
    intro L hL
    exact referenceApproximant_carrier_eq_singleton_of_le b p hL
  anyBoundaryPortsSubsetSingletonOfLe := by
    intro B L hL
    exact referenceBoundaryPorts_subset_singleton_of_le b p B hL
  noGeneratedNonSingletonCarrierFromExistingIdealThread := True.intro
  noCutSpecCarrierClaimForLevelHistory := True.intro

def variationCutSpecNoGo (β : Nat → Nat) (p : ConcretePolicyOf) :
    VariationCutSpecNoGo β p where
  sourceIsOfIdeal := by
    exact variationToC_ideal β
  familyCarrierSingleton := by
    intro L
    exact variationFamily_carrier_eq_singleton β L
  approximantCarrierSingletonOfLe := by
    intro L hL
    exact variationApproximant_carrier_eq_singleton_of_le β p hL
  anyBoundaryPortsSubsetSingletonOfLe := by
    intro B L hL
    exact variationBoundaryPorts_subset_singleton_of_le β p B hL
  noGeneratedNonSingletonCarrierFromExistingIdealThread := True.intro
  noCutSpecCarrierClaimForLevelHistory := True.intro

def existingIdealThreadSubstrateNoGo (p : ConcretePolicyOf) :
    ExistingIdealThreadSubstrateNoGo p where
  reference := by
    intro b
    exact referenceCutSpecNoGo b p
  variation := by
    intro β
    exact variationCutSpecNoGo β p
  generatedRouteStillConditional := True.intro
  recursiveHistoryRouteNotConstructedHere := True.intro
end ExistingIdealThreadNoGo

namespace StrengtheningAR2b0

open ExistingIdealThreadNoGo

abbrev ReferenceCutSpecNoGoOf (b : Nat) (p : ConcretePolicyOf) :=
  ReferenceCutSpecNoGo b p

abbrev VariationCutSpecNoGoOf (β : Nat → Nat) (p : ConcretePolicyOf) :=
  VariationCutSpecNoGo β p

abbrev ExistingIdealThreadSubstrateNoGoOf (p : ConcretePolicyOf) :=
  ExistingIdealThreadSubstrateNoGo p

def referenceCutSpecNoGoOf (b : Nat) (p : ConcretePolicyOf) :
    ReferenceCutSpecNoGoOf b p :=
  referenceCutSpecNoGo b p

def variationCutSpecNoGoOf (β : Nat → Nat) (p : ConcretePolicyOf) :
    VariationCutSpecNoGoOf β p :=
  variationCutSpecNoGo β p

def existingIdealThreadSubstrateNoGoOf (p : ConcretePolicyOf) :
    ExistingIdealThreadSubstrateNoGoOf p :=
  existingIdealThreadSubstrateNoGo p

end StrengtheningAR2b0

end CNNA.PillarA.Arithmetic
