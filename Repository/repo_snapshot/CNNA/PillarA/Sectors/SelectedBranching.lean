import CNNA.PillarA.Sectors.BranchingWitness

set_option autoImplicit false

namespace CNNA.PillarA.Sectors

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.Finite
open CNNA.PillarA.DtN

universe u

structure SelectedBranchingStrong (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  source : BranchingWitnessStrong Cell T
  selectedLevel : Nat
  admissible : selectedLevel ∈ source.source.candidateLevels
  minimal : ∀ (L : Nat), L ∈ source.source.candidateLevels → selectedLevel ≤ L

abbrev SelectedBranchingStrongOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  SelectedBranchingStrong (Cell := Cell) T

namespace SelectedBranchingStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

@[ext] theorem ext (S R : SelectedBranchingStrong Cell T)
    (hsource : S.source = R.source)
    (hlevel : S.selectedLevel = R.selectedLevel) :
    S = R := by
  cases S with
  | mk sourceS levelS admissibleS minimalS =>
    cases R with
    | mk sourceR levelR admissibleR minimalR =>
      cases hsource
      cases hlevel
      have hadmissible : admissibleS = admissibleR := by
        exact Subsingleton.elim _ _
      cases hadmissible
      have hminimal : minimalS = minimalR := by
        funext L
        funext hL
        exact Subsingleton.elim (minimalS L hL) (minimalR L hL)
      cases hminimal
      rfl

def cast (h : T = U) (S : SelectedBranchingStrong Cell T) :
    SelectedBranchingStrong Cell U := by
  cases h
  exact S

theorem cast_rfl (S : SelectedBranchingStrong Cell T) :
    cast (Cell := Cell) rfl S = S := by
  rfl

def ofWitness (W : BranchingWitnessStrong Cell T) :
    SelectedBranchingStrong Cell T where
  source := W
  selectedLevel := W.candidateLevels.min' W.candidateLevels_nonempty
  admissible := Finset.min'_mem W.candidateLevels W.candidateLevels_nonempty
  minimal := by
    intro L hL
    exact Finset.min'_le W.candidateLevels L hL


def ofSectorSplit (S : SectorSplitStrong Cell T)
    (hS : S.candidateLevels.Nonempty) :
    SelectedBranchingStrong Cell T :=
  ofWitness (BranchingWitnessStrong.firstCandidate S hS)

def split (S : SelectedBranchingStrong Cell T) : SectorSplitStrong Cell T :=
  S.source.source

def witness (S : SelectedBranchingStrong Cell T) : BranchingWitnessStrong Cell T :=
  S.source

def candidateLevels (S : SelectedBranchingStrong Cell T) : Finset Nat :=
  S.source.candidateLevels

theorem selectedLevel_mem_candidateLevels (S : SelectedBranchingStrong Cell T) :
    S.selectedLevel ∈ S.candidateLevels := by
  exact S.admissible

theorem selectedLevel_le (S : SelectedBranchingStrong Cell T)
    {L : Nat} (hL : L ∈ S.candidateLevels) :
    S.selectedLevel ≤ L := by
  exact S.minimal L hL

theorem selectedLevel_le_witnessLevel (S : SelectedBranchingStrong Cell T) :
    S.selectedLevel ≤ S.source.level := by
  exact S.selectedLevel_le S.source.admissible

theorem selectedLevel_le_cutoff (S : SelectedBranchingStrong Cell T) :
    S.selectedLevel ≤ T.cutoff := by
  exact (S.split.mem_candidateLevels_iff S.selectedLevel).mp S.admissible |>.1

def sectorCount (S : SelectedBranchingStrong Cell T) : Nat :=
  S.split.sectorCountAt S.selectedLevel

theorem sectorCount_ge_two (S : SelectedBranchingStrong Cell T) :
    2 ≤ S.sectorCount := by
  exact (S.split.mem_candidateLevels_iff S.selectedLevel).mp S.admissible |>.2

def brightActive (S : SelectedBranchingStrong Cell T) : Prop :=
  S.split.brightActiveAt S.selectedLevel

def interfaceActive (S : SelectedBranchingStrong Cell T) : Prop :=
  S.split.interfaceActiveAt S.selectedLevel

def darkActive (S : SelectedBranchingStrong Cell T) : Prop :=
  S.split.darkActiveAt S.selectedLevel

def brightCarrier (S : SelectedBranchingStrong Cell T) : Finset (Cell S.selectedLevel) :=
  S.split.brightSectorCarrier S.selectedLevel

def interfaceCarrier (S : SelectedBranchingStrong Cell T) : Finset (Cell S.selectedLevel) :=
  S.split.interfaceCarrier S.selectedLevel

def darkCarrier (S : SelectedBranchingStrong Cell T) : Finset (Cell S.selectedLevel) :=
  S.split.darkSectorCarrier S.selectedLevel

theorem brightCarrier_subset (S : SelectedBranchingStrong Cell T) :
    S.brightCarrier ⊆ T.carrier S.selectedLevel := by
  intro x hx
  have hxPatch : x ∈ S.split.brightCarrier S.selectedLevel :=
    S.split.brightSector_subset_brightCarrier S.selectedLevel hx
  exact S.split.brightPatch.carrier_subset S.selectedLevel hxPatch

theorem interfaceCarrier_subset (S : SelectedBranchingStrong Cell T) :
    S.interfaceCarrier ⊆ T.carrier S.selectedLevel := by
  exact S.split.interface_subset_ambient S.selectedLevel

theorem darkCarrier_subset (S : SelectedBranchingStrong Cell T) :
    S.darkCarrier ⊆ T.carrier S.selectedLevel := by
  intro x hx
  have hxDark : x ∈ S.split.darkCarrier S.selectedLevel :=
    S.split.darkSector_subset_darkCarrier S.selectedLevel hx
  exact S.split.darkFamily.carrier_subset S.selectedLevel hxDark

theorem brightCarrier_disjoint_interfaceCarrier (S : SelectedBranchingStrong Cell T) :
    Disjoint S.brightCarrier S.interfaceCarrier := by
  exact S.split.brightSector_disjoint_interface S.selectedLevel

theorem brightCarrier_disjoint_darkCarrier (S : SelectedBranchingStrong Cell T) :
    Disjoint S.brightCarrier S.darkCarrier := by
  exact S.split.brightSector_disjoint_darkSector S.selectedLevel

theorem interfaceCarrier_disjoint_darkCarrier (S : SelectedBranchingStrong Cell T) :
    Disjoint S.interfaceCarrier S.darkCarrier := by
  exact Disjoint.symm (S.split.darkSector_disjoint_interface S.selectedLevel)

theorem sectorCover (S : SelectedBranchingStrong Cell T) :
    S.brightCarrier ∪ S.interfaceCarrier ∪ S.darkCarrier = T.carrier S.selectedLevel := by
  exact S.split.sectorCover S.selectedLevel

def noOuterEnvironment (S : SelectedBranchingStrong Cell T) : Prop :=
  S.split.noOuterEnvironment

def hasOuterEnvironment (S : SelectedBranchingStrong Cell T) : Prop :=
  S.split.hasOuterEnvironment

theorem noOuterEnvironment_iff (S : SelectedBranchingStrong Cell T) :
    S.noOuterEnvironment ↔ S.split.noOuterEnvironment := by
  rfl

theorem hasOuterEnvironment_iff (S : SelectedBranchingStrong Cell T) :
    S.hasOuterEnvironment ↔ S.split.hasOuterEnvironment := by
  rfl

end SelectedBranchingStrong

end CNNA.PillarA.Sectors
