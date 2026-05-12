import CNNA.PillarA.Arithmetic.Core.Source

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.Finite
open CNNA.PillarA.DtN
open CNNA.PillarA.Coupling

universe u

namespace FullBoundaryAudit

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}

def fullCut (T : TruncatedFamily Cell) : CutSpec Cell T :=
  CutSpec.full T

def fullRegion (T : TruncatedFamily Cell) : RegionCore Cell T :=
  RegionCore.ofCutSpec (fullCut (Cell := Cell) T)

def fullBoundaryPorts (T : TruncatedFamily Cell) : BoundaryPorts Cell T :=
  BoundaryPorts.ofRegion (fullRegion (Cell := Cell) T)

def fullApproximant (T : TruncatedFamily Cell) : ApproximantStrong Cell T :=
  ApproximantStrong.ofBoundaryPorts (fullBoundaryPorts (Cell := Cell) T)

theorem fullRegion_carrier_eq (L : Nat) :
    (fullRegion (Cell := Cell) T).carrier L = T.carrier L := by
  rfl

theorem fullBoundaryPorts_carrier_eq (L : Nat) :
    (fullBoundaryPorts (Cell := Cell) T).carrier L = T.carrier L := by
  rfl

theorem fullApproximant_carrier_eq (L : Nat) :
    (fullApproximant (Cell := Cell) T).carrier L = T.carrier L := by
  rfl

theorem fullRegion_noParentExposure (L : Nat) (x : Cell L) :
    ¬ (fullRegion (Cell := Cell) T).parentExposedAt L x := by
  cases L with
  | zero =>
      intro hx
      exact hx
  | succ L =>
      intro hx
      rcases hx with ⟨_p, _hpParent, hpCarrier, hpNotFull⟩
      exact hpNotFull hpCarrier

theorem fullRegion_childExposure_iff_cutoff (L : Nat) (x : Cell L) :
    (fullRegion (Cell := Cell) T).childExposedAt L x ↔ T.cutoff ≤ L := by
  constructor
  · intro hx
    cases hx with
    | inl hcut =>
        exact hcut
    | inr hchild =>
        rcases hchild with ⟨_c, _hcChild, hcCarrier, hcNotFull⟩
        exact False.elim (hcNotFull hcCarrier)
  · intro hcut
    exact Or.inl hcut

theorem fullBoundaryPorts_mem_ports_iff_cutoff
    {L : Nat} {x : Cell L} :
    x ∈ (fullBoundaryPorts (Cell := Cell) T).ports L ↔
      x ∈ T.carrier L ∧ T.cutoff ≤ L := by
  constructor
  · intro hx
    have hports :=
      (BoundaryPorts.mem_ports_iff (fullBoundaryPorts (Cell := Cell) T)).mp hx
    constructor
    · exact hports.1
    · cases hports.2 with
      | inl hparent =>
          exact False.elim (fullRegion_noParentExposure (T := T) L x hparent)
      | inr hchild =>
          exact (fullRegion_childExposure_iff_cutoff (T := T) L x).mp hchild
  · intro hx
    exact
      (BoundaryPorts.mem_ports_iff (fullBoundaryPorts (Cell := Cell) T)).mpr
        ⟨hx.1, Or.inr ((fullRegion_childExposure_iff_cutoff (T := T) L x).mpr hx.2)⟩

theorem fullBoundaryPorts_ports_eq_empty_of_lt
    {L : Nat} (hL : L < T.cutoff) :
    (fullBoundaryPorts (Cell := Cell) T).ports L = ∅ := by
  ext x
  constructor
  · intro hx
    have hcut :=
      (fullBoundaryPorts_mem_ports_iff_cutoff (T := T) (x := x)).mp hx
    exact False.elim ((Nat.not_le_of_gt hL) hcut.2)
  · intro hx
    cases hx

theorem fullBoundaryPorts_topPorts_eq_carrier :
    (fullBoundaryPorts (Cell := Cell) T).ports T.cutoff = T.carrier T.cutoff := by
  ext x
  constructor
  · intro hx
    exact ((fullBoundaryPorts_mem_ports_iff_cutoff (T := T) (x := x)).mp hx).1
  · intro hx
    exact (fullBoundaryPorts_mem_ports_iff_cutoff (T := T) (x := x)).mpr ⟨hx, le_rfl⟩

theorem fullApproximant_ports_eq_empty_of_lt
    {L : Nat} (hL : L < T.cutoff) :
    (fullApproximant (Cell := Cell) T).ports L = ∅ := by
  exact fullBoundaryPorts_ports_eq_empty_of_lt (T := T) hL

theorem fullApproximant_topPorts_eq_carrier :
    (fullApproximant (Cell := Cell) T).ports T.cutoff = T.carrier T.cutoff := by
  exact fullBoundaryPorts_topPorts_eq_carrier (T := T)

theorem fullBoundaryVertex_level_eq_cutoff
    (v : BoundaryVertex (Cell := Cell) (fullApproximant (Cell := Cell) T)) :
    v.1.1 = T.cutoff := by
  have hle : v.1.1 ≤ T.cutoff :=
    Nat.lt_succ_iff.mp v.1.2
  have hmem : v.2.1 ∈ (fullBoundaryPorts (Cell := Cell) T).ports v.1.1 := by
    exact v.2.2
  have hcut : T.cutoff ≤ v.1.1 :=
    ((fullBoundaryPorts_mem_ports_iff_cutoff (T := T) (x := v.2.1)).mp hmem).2
  exact Nat.le_antisymm hle hcut

structure FullCutSpecNegativeAudit (T : TruncatedFamily Cell) where
  belowPorts_empty : ∀ {L : Nat}, L < T.cutoff →
    (fullBoundaryPorts (Cell := Cell) T).ports L = ∅
  topPorts_eq_carrier :
    (fullBoundaryPorts (Cell := Cell) T).ports T.cutoff = T.carrier T.cutoff
  boundaryVertex_level_eq_cutoff :
    ∀ v : BoundaryVertex (Cell := Cell) (fullApproximant (Cell := Cell) T),
      v.1.1 = T.cutoff
  noLevelHistoryBoundaryClaim : True

def fullCutSpecNegativeAudit (T : TruncatedFamily Cell) :
    FullCutSpecNegativeAudit (Cell := Cell) T where
  belowPorts_empty := by
    intro L hL
    exact fullBoundaryPorts_ports_eq_empty_of_lt (T := T) hL
  topPorts_eq_carrier := by
    exact fullBoundaryPorts_topPorts_eq_carrier (T := T)
  boundaryVertex_level_eq_cutoff := by
    intro v
    exact fullBoundaryVertex_level_eq_cutoff (T := T) v
  noLevelHistoryBoundaryClaim := True.intro

end FullBoundaryAudit

namespace StrengtheningAR2a

open FullBoundaryAudit
open CNNA.PillarA.ToC.ConcreteIdeal
open CNNA.PillarA.Foundation.ConcreteSubstrate
open CNNA.PillarA.Finite.StrengtheningS4
open CNNA.PillarA.Finite.StrengtheningS5
open CNNA.PillarA.DtN.StrengtheningS5
open CNNA.PillarA.DtN.StrengtheningS6
open CNNA.PillarA.Coupling.StrengtheningS7

abbrev ReferenceFullCutSpecNegativeAudit (b : Nat) (p : ConcretePolicyOf) :=
  FullCutSpecNegativeAudit
    (Cell := ReferenceIdealCellOf b)
    ((referenceToC b).approximant p)

def referenceFullCutSpecNegativeAudit (b : Nat) (p : ConcretePolicyOf) :
    ReferenceFullCutSpecNegativeAudit b p :=
  fullCutSpecNegativeAudit
    (Cell := ReferenceIdealCellOf b)
    ((referenceToC b).approximant p)

theorem referenceFullBoundaryPorts_eq_empty_of_below
    (b : Nat) (p : ConcretePolicyOf) {L : Nat} (hL : L < p.L_max) :
    (referenceFullBoundaryPorts b p).ports L = ∅ := by
  have hcut : L < ((referenceToC b).approximant p).cutoff := by
    rw [referenceToC_approximant_eq_truncate]
    exact hL
  change
    (FullBoundaryAudit.fullBoundaryPorts
      (Cell := ReferenceIdealCellOf b) ((referenceToC b).approximant p)).ports L = ∅
  exact FullBoundaryAudit.fullBoundaryPorts_ports_eq_empty_of_lt
    (T := (referenceToC b).approximant p) hcut

theorem referenceFullApproximant_cutoff_eq
    (b : Nat) (p : ConcretePolicyOf) :
    ((referenceToC b).approximant p).cutoff = p.L_max := by
  rw [referenceToC_approximant_eq_truncate]
  rfl

theorem referenceFullBoundaryTopPorts_eq_carrier
    (b : Nat) (p : ConcretePolicyOf) :
    (referenceFullBoundaryPorts b p).ports p.L_max =
      ((referenceToC b).approximant p).carrier p.L_max := by
  rw [← referenceFullApproximant_cutoff_eq b p]
  change
    (FullBoundaryAudit.fullBoundaryPorts
      (Cell := ReferenceIdealCellOf b) ((referenceToC b).approximant p)).ports
        ((referenceToC b).approximant p).cutoff =
      ((referenceToC b).approximant p).carrier ((referenceToC b).approximant p).cutoff
  exact FullBoundaryAudit.fullBoundaryPorts_topPorts_eq_carrier
    (T := (referenceToC b).approximant p)

theorem referenceFullApproximant_topCarrier_eq_singleton
    (b : Nat) (p : ConcretePolicyOf) :
    ((referenceToC b).approximant p).carrier p.L_max =
      ({zeroCell b p.L_max} : Finset (ReferenceIdealCellOf b p.L_max)) := by
  rw [referenceToC_approximant_eq_truncate]
  rw [DirectedFamily.truncate_carrier_of_le
    (F := referenceFamily b) (L := p.L_max) (N := p.L_max) le_rfl]
  rfl

theorem referenceFullBoundaryTopPorts_card_eq_one
    (b : Nat) (p : ConcretePolicyOf) :
    ((referenceFullBoundaryPorts b p).ports p.L_max).card = 1 := by
  calc
    ((referenceFullBoundaryPorts b p).ports p.L_max).card =
        (((referenceToC b).approximant p).carrier p.L_max).card := by
          rw [referenceFullBoundaryTopPorts_eq_carrier]
    _ = ({zeroCell b p.L_max} : Finset (ReferenceIdealCellOf b p.L_max)).card := by
          rw [referenceFullApproximant_topCarrier_eq_singleton]
    _ = 1 := by
          rw [Finset.card_singleton]

structure ReferenceFullOneByOneAudit (b : Nat) (p : ConcretePolicyOf) where
  negativeAudit : ReferenceFullCutSpecNegativeAudit b p
  belowPorts_empty : ∀ {L : Nat}, L < p.L_max →
    (referenceFullBoundaryPorts b p).ports L = ∅
  topBoundaryCard_eq_one :
    ((referenceFullBoundaryPorts b p).ports p.L_max).card = 1
  noCutSpecFullConsumer : True

def referenceFullOneByOneAudit (b : Nat) (p : ConcretePolicyOf) :
    ReferenceFullOneByOneAudit b p where
  negativeAudit := referenceFullCutSpecNegativeAudit b p
  belowPorts_empty := by
    intro L hL
    exact referenceFullBoundaryPorts_eq_empty_of_below b p hL
  topBoundaryCard_eq_one := by
    exact referenceFullBoundaryTopPorts_card_eq_one b p
  noCutSpecFullConsumer := True.intro

theorem referenceArithmeticSource_fullBoundary_oneByOne
    (b : Nat) (p : ConcretePolicyOf)
    (wp : WeightPolicy := referenceDefaultWeightPolicy b)
    (rp : RegularizationPolicy := referenceDefaultRegularizationPolicy)
    [ReferenceInteriorEliminationData b p wp]
    [ReferenceInterfaceEliminationData b p wp rp] :
    ((referenceFullBoundaryPorts b p).ports p.L_max).card = 1 := by
  exact referenceFullBoundaryTopPorts_card_eq_one b p

end StrengtheningAR2a

end CNNA.PillarA.Arithmetic
