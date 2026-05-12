import CNNA.PillarA.Sectors.UVSpectralSelector

set_option autoImplicit false

namespace CNNA.PillarA.Sectors

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.Finite
open CNNA.PillarA.DtN

universe u

structure BranchingSelectorStrong (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  branching : SelectedBranchingStrong Cell T
  uv : UVSpectralSelectorStrong Cell T
  coherent : uv.source = branching

abbrev BranchingSelectorStrongOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  BranchingSelectorStrong (Cell := Cell) T

namespace BranchingSelectorStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T T' : TruncatedFamily Cell}

@[ext] theorem ext (B C : BranchingSelectorStrong Cell T)
    (hbranching : B.branching = C.branching)
    (huv : B.uv = C.uv) :
    B = C := by
  cases B with
  | mk branchingB uvB coherentB =>
    cases C with
    | mk branchingC uvC coherentC =>
      cases hbranching
      cases huv
      have hcoherent : coherentB = coherentC := by
        exact Subsingleton.elim _ _
      cases hcoherent
      rfl

def cast (h : T = T') (B : BranchingSelectorStrong Cell T) :
    BranchingSelectorStrong Cell T' := by
  cases h
  exact B

theorem cast_rfl (B : BranchingSelectorStrong Cell T) :
    cast (Cell := Cell) rfl B = B := by
  rfl

def ofSelectedBranching (S : SelectedBranchingStrong Cell T) :
    BranchingSelectorStrong Cell T where
  branching := S
  uv := UVSpectralSelectorStrong.ofSelectedBranching S
  coherent := rfl

def ofUVSelector (U : UVSpectralSelectorStrong Cell T) :
    BranchingSelectorStrong Cell T where
  branching := U.source
  uv := U
  coherent := rfl

def selectedLevel (B : BranchingSelectorStrong Cell T) : Nat :=
  B.branching.selectedLevel

def cutoff (_ : BranchingSelectorStrong Cell T) : Nat :=
  T.cutoff

def candidateLevels (B : BranchingSelectorStrong Cell T) : Finset Nat :=
  B.branching.candidateLevels

theorem selectedLevelAdmissible (B : BranchingSelectorStrong Cell T) :
    B.selectedLevel ∈ B.candidateLevels := by
  exact B.branching.selectedLevel_mem_candidateLevels

def irLevels (B : BranchingSelectorStrong Cell T) : Finset Nat :=
  B.uv.irLevels

def uvLevels (B : BranchingSelectorStrong Cell T) : Finset Nat :=
  B.uv.uvLevels

def hasUVTail (B : BranchingSelectorStrong Cell T) : Prop :=
  B.uv.hasUVTail

def split (B : BranchingSelectorStrong Cell T) : SectorSplitStrong Cell T :=
  B.branching.split

def witness (B : BranchingSelectorStrong Cell T) : BranchingWitnessStrong Cell T :=
  B.branching.witness

def selectedCarrier (B : BranchingSelectorStrong Cell T) : Finset (Cell B.selectedLevel) :=
  T.carrier B.selectedLevel

def selectedBoundaryCarrier (B : BranchingSelectorStrong Cell T) : Finset (Cell B.selectedLevel) :=
  B.branching.interfaceCarrier

def selectedBrightCarrier (B : BranchingSelectorStrong Cell T) : Finset (Cell B.selectedLevel) :=
  B.branching.brightCarrier

def selectedDarkCarrier (B : BranchingSelectorStrong Cell T) : Finset (Cell B.selectedLevel) :=
  B.branching.darkCarrier

def selectedSectorCount (B : BranchingSelectorStrong Cell T) : Nat :=
  B.branching.sectorCount

def brightActive (B : BranchingSelectorStrong Cell T) : Prop :=
  B.branching.brightActive

def interfaceActive (B : BranchingSelectorStrong Cell T) : Prop :=
  B.branching.interfaceActive

def darkActive (B : BranchingSelectorStrong Cell T) : Prop :=
  B.branching.darkActive

def noOuterEnvironment (B : BranchingSelectorStrong Cell T) : Prop :=
  B.branching.noOuterEnvironment

def hasOuterEnvironment (B : BranchingSelectorStrong Cell T) : Prop :=
  B.branching.hasOuterEnvironment

theorem uv_source_eq_branching (B : BranchingSelectorStrong Cell T) :
    B.uv.source = B.branching := by
  exact B.coherent

theorem selectedLevel_eq_branching (B : BranchingSelectorStrong Cell T) :
    B.selectedLevel = B.branching.selectedLevel := by
  rfl

theorem uv_selectedLevel_eq (B : BranchingSelectorStrong Cell T) :
    B.uv.selectedLevel = B.selectedLevel := by
  change B.uv.source.selectedLevel = B.branching.selectedLevel
  rw [B.coherent]

theorem selectedLevel_le_cutoff (B : BranchingSelectorStrong Cell T) :
    B.selectedLevel ≤ T.cutoff := by
  exact B.branching.selectedLevel_le_cutoff

theorem mem_irLevels_iff (B : BranchingSelectorStrong Cell T) (L : Nat) :
    L ∈ B.irLevels ↔ L ≤ B.selectedLevel := by
  constructor
  · intro hL
    have h' : L ≤ B.uv.selectedLevel := (B.uv.mem_irLevels_iff L).mp hL
    rw [B.uv_selectedLevel_eq] at h'
    exact h'
  · intro hL
    have h' : L ≤ B.uv.selectedLevel := by
      rw [B.uv_selectedLevel_eq]
      exact hL
    exact (B.uv.mem_irLevels_iff L).mpr h'

theorem mem_uvLevels_iff (B : BranchingSelectorStrong Cell T) (L : Nat) :
    L ∈ B.uvLevels ↔ B.selectedLevel < L ∧ L ≤ T.cutoff := by
  constructor
  · intro hL
    have h' : B.uv.selectedLevel < L ∧ L ≤ T.cutoff := (B.uv.mem_uvLevels_iff L).mp hL
    have hleft : B.selectedLevel < L := by
      rw [← B.uv_selectedLevel_eq]
      exact h'.1
    exact ⟨hleft, h'.2⟩
  · intro hL
    have h' : B.uv.selectedLevel < L ∧ L ≤ T.cutoff := by
      constructor
      · rw [B.uv_selectedLevel_eq]
        exact hL.1
      · exact hL.2
    exact (B.uv.mem_uvLevels_iff L).mpr h'

theorem hasUVTail_iff_nonempty (B : BranchingSelectorStrong Cell T) :
    B.hasUVTail ↔ B.uvLevels.Nonempty := by
  exact B.uv.hasUVTail_iff_nonempty

theorem noUVTail_iff (B : BranchingSelectorStrong Cell T) :
    ¬ B.hasUVTail ↔ B.uvLevels = ∅ := by
  exact B.uv.noUVTail_iff

theorem ir_uv_disjoint (B : BranchingSelectorStrong Cell T) :
    Disjoint B.irLevels B.uvLevels := by
  exact B.uv.ir_uv_disjoint

theorem ir_uv_cover (B : BranchingSelectorStrong Cell T) :
    B.irLevels ∪ B.uvLevels = Finset.range (T.cutoff + 1) := by
  exact B.uv.ir_uv_cover

theorem selectedCarrier_subset (B : BranchingSelectorStrong Cell T) :
    B.selectedCarrier ⊆ T.carrier B.selectedLevel := by
  intro x hx
  exact hx

theorem selectedBoundaryCarrier_subset (B : BranchingSelectorStrong Cell T) :
    B.selectedBoundaryCarrier ⊆ T.carrier B.selectedLevel := by
  exact B.branching.interfaceCarrier_subset

theorem selectedSectorCount_ge_two (B : BranchingSelectorStrong Cell T) :
    2 ≤ B.selectedSectorCount := by
  exact B.branching.sectorCount_ge_two

theorem selectedSectorCover (B : BranchingSelectorStrong Cell T) :
    B.selectedBrightCarrier ∪ B.selectedBoundaryCarrier ∪ B.selectedDarkCarrier =
      T.carrier B.selectedLevel := by
  exact B.branching.sectorCover

theorem noOuterEnvironment_iff (B : BranchingSelectorStrong Cell T) :
    B.noOuterEnvironment ↔ B.split.noOuterEnvironment := by
  rfl

theorem hasOuterEnvironment_iff (B : BranchingSelectorStrong Cell T) :
    B.hasOuterEnvironment ↔ B.split.hasOuterEnvironment := by
  rfl

end BranchingSelectorStrong

end CNNA.PillarA.Sectors
