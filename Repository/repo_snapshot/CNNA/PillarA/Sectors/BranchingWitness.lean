import CNNA.PillarA.Sectors.SectorSplit

set_option autoImplicit false

namespace CNNA.PillarA.Sectors

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.Finite
open CNNA.PillarA.DtN

universe u

namespace SectorSplitStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}

def brightActiveAt (S : SectorSplitStrong Cell T) (L : Nat) : Prop :=
  0 < (S.brightSectorCarrier L).card

def interfaceActiveAt (S : SectorSplitStrong Cell T) (L : Nat) : Prop :=
  0 < (S.interfaceCarrier L).card

def darkActiveAt (S : SectorSplitStrong Cell T) (L : Nat) : Prop :=
  0 < (S.darkSectorCarrier L).card

theorem brightActiveAt_iff_nonempty (S : SectorSplitStrong Cell T) (L : Nat) :
    S.brightActiveAt L ↔ (S.brightSectorCarrier L).Nonempty := by
  exact Finset.card_pos

theorem interfaceActiveAt_iff_nonempty (S : SectorSplitStrong Cell T) (L : Nat) :
    S.interfaceActiveAt L ↔ (S.interfaceCarrier L).Nonempty := by
  exact Finset.card_pos

theorem darkActiveAt_iff_nonempty (S : SectorSplitStrong Cell T) (L : Nat) :
    S.darkActiveAt L ↔ (S.darkSectorCarrier L).Nonempty := by
  exact Finset.card_pos

instance instDecidableBrightActiveAt (S : SectorSplitStrong Cell T) (L : Nat) :
    Decidable (S.brightActiveAt L) :=
  inferInstanceAs (Decidable (0 < (S.brightSectorCarrier L).card))

instance instDecidableInterfaceActiveAt (S : SectorSplitStrong Cell T) (L : Nat) :
    Decidable (S.interfaceActiveAt L) :=
  inferInstanceAs (Decidable (0 < (S.interfaceCarrier L).card))

instance instDecidableDarkActiveAt (S : SectorSplitStrong Cell T) (L : Nat) :
    Decidable (S.darkActiveAt L) :=
  inferInstanceAs (Decidable (0 < (S.darkSectorCarrier L).card))

def sectorCountAt (S : SectorSplitStrong Cell T) (L : Nat) : Nat :=
  (if S.brightActiveAt L then 1 else 0) +
    (if S.interfaceActiveAt L then 1 else 0) +
    (if S.darkActiveAt L then 1 else 0)

def candidateLevels (S : SectorSplitStrong Cell T) : Finset Nat :=
  (Finset.range (T.cutoff + 1)).filter (fun L => 2 ≤ S.sectorCountAt L)

theorem mem_candidateLevels_iff (S : SectorSplitStrong Cell T) (L : Nat) :
    L ∈ S.candidateLevels ↔ L ≤ T.cutoff ∧ 2 ≤ S.sectorCountAt L := by
  constructor
  · intro hL
    have hmem := Finset.mem_filter.mp hL
    have hrange : L ∈ Finset.range (T.cutoff + 1) := hmem.1
    have hcount : 2 ≤ S.sectorCountAt L := hmem.2
    have hcutoff : L ≤ T.cutoff := by
      exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hrange)
    exact ⟨hcutoff, hcount⟩
  · intro hL
    refine Finset.mem_filter.mpr ?_
    refine ⟨?_, hL.2⟩
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hL.1)

end SectorSplitStrong

structure BranchingWitnessStrong (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  source : SectorSplitStrong Cell T
  level : Nat
  admissible : level ∈ source.candidateLevels

abbrev BranchingWitnessStrongOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  BranchingWitnessStrong (Cell := Cell) T

namespace BranchingWitnessStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

@[ext] theorem ext (W Z : BranchingWitnessStrong Cell T)
    (hsource : W.source = Z.source)
    (hlevel : W.level = Z.level) :
    W = Z := by
  cases W with
  | mk sourceW levelW admissibleW =>
    cases Z with
    | mk sourceZ levelZ admissibleZ =>
      cases hsource
      cases hlevel
      have hadmissible : admissibleW = admissibleZ := by
        apply Subsingleton.elim
      cases hadmissible
      rfl

def cast (h : T = U) (W : BranchingWitnessStrong Cell T) :
    BranchingWitnessStrong Cell U := by
  cases h
  exact W

theorem cast_rfl (W : BranchingWitnessStrong Cell T) :
    cast (Cell := Cell) rfl W = W := by
  rfl

def ofCandidate (S : SectorSplitStrong Cell T) (L : Nat)
    (hL : L ∈ S.candidateLevels) :
    BranchingWitnessStrong Cell T where
  source := S
  level := L
  admissible := hL


def firstCandidate (S : SectorSplitStrong Cell T)
    (hS : S.candidateLevels.Nonempty) :
    BranchingWitnessStrong Cell T where
  source := S
  level := S.candidateLevels.min' hS
  admissible := Finset.min'_mem S.candidateLevels hS

def split (W : BranchingWitnessStrong Cell T) : SectorSplitStrong Cell T :=
  W.source

def levelLeCutoff (W : BranchingWitnessStrong Cell T) : Prop :=
  W.level ≤ T.cutoff

theorem level_le_cutoff (W : BranchingWitnessStrong Cell T) :
    W.level ≤ T.cutoff := by
  exact (W.source.mem_candidateLevels_iff W.level).mp W.admissible |>.1

def sectorCount (W : BranchingWitnessStrong Cell T) : Nat :=
  W.source.sectorCountAt W.level

theorem sectorCount_ge_two (W : BranchingWitnessStrong Cell T) :
    2 ≤ W.sectorCount := by
  exact (W.source.mem_candidateLevels_iff W.level).mp W.admissible |>.2

def brightActive (W : BranchingWitnessStrong Cell T) : Prop :=
  W.source.brightActiveAt W.level

def interfaceActive (W : BranchingWitnessStrong Cell T) : Prop :=
  W.source.interfaceActiveAt W.level

def darkActive (W : BranchingWitnessStrong Cell T) : Prop :=
  W.source.darkActiveAt W.level

def brightCarrier (W : BranchingWitnessStrong Cell T) : Finset (Cell W.level) :=
  W.source.brightSectorCarrier W.level

def interfaceCarrier (W : BranchingWitnessStrong Cell T) : Finset (Cell W.level) :=
  W.source.interfaceCarrier W.level

def darkCarrier (W : BranchingWitnessStrong Cell T) : Finset (Cell W.level) :=
  W.source.darkSectorCarrier W.level

def candidateLevels (W : BranchingWitnessStrong Cell T) : Finset Nat :=
  W.source.candidateLevels

theorem level_mem_candidateLevels (W : BranchingWitnessStrong Cell T) :
    W.level ∈ W.candidateLevels := by
  exact W.admissible

theorem candidateLevels_nonempty (W : BranchingWitnessStrong Cell T) :
    W.candidateLevels.Nonempty := by
  exact ⟨W.level, W.admissible⟩

theorem brightCarrier_eq (W : BranchingWitnessStrong Cell T) :
    W.brightCarrier = W.source.brightSectorCarrier W.level := by
  rfl

theorem interfaceCarrier_eq (W : BranchingWitnessStrong Cell T) :
    W.interfaceCarrier = W.source.interfaceCarrier W.level := by
  rfl

theorem darkCarrier_eq (W : BranchingWitnessStrong Cell T) :
    W.darkCarrier = W.source.darkSectorCarrier W.level := by
  rfl

theorem bright_active_iff (W : BranchingWitnessStrong Cell T) :
    W.brightActive ↔ W.brightCarrier.Nonempty := by
  exact W.source.brightActiveAt_iff_nonempty W.level

theorem interface_active_iff (W : BranchingWitnessStrong Cell T) :
    W.interfaceActive ↔ W.interfaceCarrier.Nonempty := by
  exact W.source.interfaceActiveAt_iff_nonempty W.level

theorem dark_active_iff (W : BranchingWitnessStrong Cell T) :
    W.darkActive ↔ W.darkCarrier.Nonempty := by
  exact W.source.darkActiveAt_iff_nonempty W.level

theorem brightCarrier_subset (W : BranchingWitnessStrong Cell T) :
    W.brightCarrier ⊆ T.carrier W.level := by
  intro x hx
  have hxPatch : x ∈ W.source.brightCarrier W.level :=
    W.source.brightSector_subset_brightCarrier W.level hx
  exact W.source.brightPatch.carrier_subset W.level hxPatch

theorem interfaceCarrier_subset (W : BranchingWitnessStrong Cell T) :
    W.interfaceCarrier ⊆ T.carrier W.level := by
  exact W.source.interface_subset_ambient W.level

theorem darkCarrier_subset (W : BranchingWitnessStrong Cell T) :
    W.darkCarrier ⊆ T.carrier W.level := by
  intro x hx
  have hxDark : x ∈ W.source.darkCarrier W.level :=
    W.source.darkSector_subset_darkCarrier W.level hx
  exact W.source.darkFamily.carrier_subset W.level hxDark

theorem brightCarrier_disjoint_interfaceCarrier (W : BranchingWitnessStrong Cell T) :
    Disjoint W.brightCarrier W.interfaceCarrier := by
  exact W.source.brightSector_disjoint_interface W.level

theorem brightCarrier_disjoint_darkCarrier (W : BranchingWitnessStrong Cell T) :
    Disjoint W.brightCarrier W.darkCarrier := by
  exact W.source.brightSector_disjoint_darkSector W.level

theorem interfaceCarrier_disjoint_darkCarrier (W : BranchingWitnessStrong Cell T) :
    Disjoint W.interfaceCarrier W.darkCarrier := by
  exact Disjoint.symm (W.source.darkSector_disjoint_interface W.level)

theorem sectorCover (W : BranchingWitnessStrong Cell T) :
    W.brightCarrier ∪ W.interfaceCarrier ∪ W.darkCarrier = T.carrier W.level := by
  exact W.source.sectorCover W.level

def noOuterEnvironment (W : BranchingWitnessStrong Cell T) : Prop :=
  W.source.noOuterEnvironment

def hasOuterEnvironment (W : BranchingWitnessStrong Cell T) : Prop :=
  W.source.hasOuterEnvironment

theorem noOuterEnvironment_iff (W : BranchingWitnessStrong Cell T) :
    W.noOuterEnvironment ↔ W.source.noOuterEnvironment := by
  rfl

theorem hasOuterEnvironment_iff (W : BranchingWitnessStrong Cell T) :
    W.hasOuterEnvironment ↔ W.source.hasOuterEnvironment := by
  rfl

end BranchingWitnessStrong

end CNNA.PillarA.Sectors
