import CNNA.PillarA.Sectors.SelectedBranching

set_option autoImplicit false

namespace CNNA.PillarA.Sectors

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.Finite
open CNNA.PillarA.DtN

universe u

structure UVSpectralSelectorStrong (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  source : SelectedBranchingStrong Cell T

abbrev UVSpectralSelectorStrongOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  UVSpectralSelectorStrong (Cell := Cell) T

namespace UVSpectralSelectorStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T T' : TruncatedFamily Cell}

@[ext] theorem ext (U V : UVSpectralSelectorStrong Cell T)
    (hsource : U.source = V.source) :
    U = V := by
  cases U with
  | mk sourceU =>
    cases V with
    | mk sourceV =>
      cases hsource
      rfl

def cast (h : T = T') (S : UVSpectralSelectorStrong Cell T) :
    UVSpectralSelectorStrong Cell T' := by
  cases h
  exact S

theorem cast_rfl (S : UVSpectralSelectorStrong Cell T) :
    cast (Cell := Cell) rfl S = S := by
  rfl

def ofSelectedBranching (S : SelectedBranchingStrong Cell T) :
    UVSpectralSelectorStrong Cell T where
  source := S

def branching (S : UVSpectralSelectorStrong Cell T) : SelectedBranchingStrong Cell T :=
  S.source

def split (S : UVSpectralSelectorStrong Cell T) : SectorSplitStrong Cell T :=
  S.branching.split

def witness (S : UVSpectralSelectorStrong Cell T) : BranchingWitnessStrong Cell T :=
  S.branching.witness

def selectedLevel (S : UVSpectralSelectorStrong Cell T) : Nat :=
  S.branching.selectedLevel

def cutoff (_ : UVSpectralSelectorStrong Cell T) : Nat :=
  T.cutoff

def irLevels (S : UVSpectralSelectorStrong Cell T) : Finset Nat :=
  (Finset.range (T.cutoff + 1)).filter (fun L => L ≤ S.selectedLevel)

def uvLevels (S : UVSpectralSelectorStrong Cell T) : Finset Nat :=
  (Finset.range (T.cutoff + 1)).filter (fun L => S.selectedLevel < L)

def hasUVTail (S : UVSpectralSelectorStrong Cell T) : Prop :=
  S.selectedLevel < T.cutoff

def selectedSlice (S : UVSpectralSelectorStrong Cell T) : LayerSlice Cell :=
  T.slice S.selectedLevel

def selectedCarrier (S : UVSpectralSelectorStrong Cell T) : Finset (Cell S.selectedLevel) :=
  T.carrier S.selectedLevel

def selectedBoundaryCarrier (S : UVSpectralSelectorStrong Cell T) : Finset (Cell S.selectedLevel) :=
  S.split.interfaceCarrier S.selectedLevel

def selectedBrightCarrier (S : UVSpectralSelectorStrong Cell T) : Finset (Cell S.selectedLevel) :=
  S.branching.brightCarrier

def selectedDarkCarrier (S : UVSpectralSelectorStrong Cell T) : Finset (Cell S.selectedLevel) :=
  S.branching.darkCarrier

def selectedSectorCount (S : UVSpectralSelectorStrong Cell T) : Nat :=
  S.branching.sectorCount

def brightActive (S : UVSpectralSelectorStrong Cell T) : Prop :=
  S.branching.brightActive

def interfaceActive (S : UVSpectralSelectorStrong Cell T) : Prop :=
  S.branching.interfaceActive

def darkActive (S : UVSpectralSelectorStrong Cell T) : Prop :=
  S.branching.darkActive

theorem selectedLevel_eq_branching (S : UVSpectralSelectorStrong Cell T) :
    S.selectedLevel = S.branching.selectedLevel := by
  rfl

theorem selectedLevel_le_cutoff (S : UVSpectralSelectorStrong Cell T) :
    S.selectedLevel ≤ T.cutoff := by
  exact S.branching.selectedLevel_le_cutoff

theorem selectedLevel_mem_irLevels (S : UVSpectralSelectorStrong Cell T) :
    S.selectedLevel ∈ S.irLevels := by
  refine Finset.mem_filter.mpr ?_
  refine ⟨?_, le_rfl⟩
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le S.branching.selectedLevel_le_cutoff)

theorem mem_irLevels_iff (S : UVSpectralSelectorStrong Cell T) (L : Nat) :
    L ∈ S.irLevels ↔ L ≤ S.selectedLevel := by
  constructor
  · intro hL
    have hmem := Finset.mem_filter.mp hL
    exact hmem.2
  · intro hL
    refine Finset.mem_filter.mpr ?_
    refine ⟨?_, hL⟩
    have hcutoff : L ≤ T.cutoff := Nat.le_trans hL S.branching.selectedLevel_le_cutoff
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hcutoff)

theorem mem_uvLevels_iff (S : UVSpectralSelectorStrong Cell T) (L : Nat) :
    L ∈ S.uvLevels ↔ S.selectedLevel < L ∧ L ≤ T.cutoff := by
  constructor
  · intro hL
    have hmem := Finset.mem_filter.mp hL
    have hrange : L < T.cutoff + 1 := Finset.mem_range.mp hmem.1
    exact ⟨hmem.2, Nat.lt_succ_iff.mp hrange⟩
  · intro hL
    refine Finset.mem_filter.mpr ?_
    refine ⟨?_, hL.1⟩
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hL.2)

theorem not_mem_uvLevels_selectedLevel (S : UVSpectralSelectorStrong Cell T) :
    S.selectedLevel ∉ S.uvLevels := by
  intro hL
  have hlt : S.selectedLevel < S.selectedLevel :=
    (S.mem_uvLevels_iff S.selectedLevel).mp hL |>.1
  exact Nat.lt_irrefl _ hlt

theorem ir_uv_disjoint (S : UVSpectralSelectorStrong Cell T) :
    Disjoint S.irLevels S.uvLevels := by
  refine Finset.disjoint_left.mpr ?_
  intro L hIR hUV
  have hle : L ≤ S.selectedLevel := (S.mem_irLevels_iff L).mp hIR
  have hlt : S.selectedLevel < L := (S.mem_uvLevels_iff L).mp hUV |>.1
  exact (Nat.not_lt_of_ge hle) hlt

theorem ir_uv_cover (S : UVSpectralSelectorStrong Cell T) :
    S.irLevels ∪ S.uvLevels = Finset.range (T.cutoff + 1) := by
  ext L
  constructor
  · intro hL
    rcases Finset.mem_union.mp hL with hIR | hUV
    · exact (Finset.mem_filter.mp hIR).1
    · exact (Finset.mem_filter.mp hUV).1
  · intro hL
    by_cases hIR : L ≤ S.selectedLevel
    · exact Finset.mem_union.mpr <| Or.inl ((S.mem_irLevels_iff L).mpr hIR)
    · have hlt : S.selectedLevel < L := Nat.lt_of_not_ge hIR
      have hcutoff : L ≤ T.cutoff := Nat.lt_succ_iff.mp (Finset.mem_range.mp hL)
      exact Finset.mem_union.mpr <| Or.inr ((S.mem_uvLevels_iff L).mpr ⟨hlt, hcutoff⟩)

theorem hasUVTail_iff_nonempty (S : UVSpectralSelectorStrong Cell T) :
    S.hasUVTail ↔ S.uvLevels.Nonempty := by
  constructor
  · intro htail
    refine ⟨S.selectedLevel + 1, ?_⟩
    refine (S.mem_uvLevels_iff (S.selectedLevel + 1)).mpr ?_
    refine ⟨Nat.lt_succ_self S.selectedLevel, ?_⟩
    exact Nat.succ_le_of_lt htail
  · intro hnonempty
    rcases hnonempty with ⟨L, hL⟩
    exact (S.mem_uvLevels_iff L).mp hL |>.1.trans_le ((S.mem_uvLevels_iff L).mp hL |>.2)

theorem noUVTail_iff (S : UVSpectralSelectorStrong Cell T) :
    ¬ S.hasUVTail ↔ S.uvLevels = ∅ := by
  constructor
  · intro htail
    ext L
    constructor
    · intro hL
      have hmem := (S.mem_uvLevels_iff L).mp hL
      exact False.elim (htail (hmem.1.trans_le hmem.2))
    · intro hL
      exact False.elim ((Finset.notMem_empty L) hL)
  · intro huv htail
    have hnonempty : S.uvLevels.Nonempty := (S.hasUVTail_iff_nonempty).mp htail
    rcases hnonempty with ⟨L, hL⟩
    have : L ∈ (∅ : Finset Nat) := by
      rw [← huv]
      exact hL
    exact (Finset.notMem_empty L) this

theorem selectedCarrier_subset (S : UVSpectralSelectorStrong Cell T) :
    S.selectedCarrier ⊆ T.carrier S.selectedLevel := by
  intro x hx
  exact hx

theorem selectedBoundaryCarrier_subset (S : UVSpectralSelectorStrong Cell T) :
    S.selectedBoundaryCarrier ⊆ T.carrier S.selectedLevel := by
  exact S.split.interface_subset_ambient S.selectedLevel

theorem selectedSectorCount_ge_two (S : UVSpectralSelectorStrong Cell T) :
    2 ≤ S.selectedSectorCount := by
  exact S.branching.sectorCount_ge_two

theorem selectedSectorCover (S : UVSpectralSelectorStrong Cell T) :
    S.selectedBrightCarrier ∪ S.selectedBoundaryCarrier ∪ S.selectedDarkCarrier =
      T.carrier S.selectedLevel := by
  exact S.branching.sectorCover

end UVSpectralSelectorStrong

end CNNA.PillarA.Sectors
