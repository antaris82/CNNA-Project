import CNNA.PillarA.Sectors.BranchingSelector

set_option autoImplicit false

namespace CNNA.PillarA.Sectors

universe u

abbrev BranchPatch
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Sectors.BranchPatchStrong (Cell := Cell) T

abbrev ComplementSectorFamily
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Sectors.ComplementSectorFamilyStrong (Cell := Cell) T



abbrev BranchingWitness
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Sectors.BranchingWitnessStrong (Cell := Cell) T


abbrev SelectedBranching
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Sectors.SelectedBranchingStrong (Cell := Cell) T


abbrev UVSpectralSelector
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Sectors.UVSpectralSelectorStrong (Cell := Cell) T

abbrev BranchingSelector
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Sectors.BranchingSelectorStrong (Cell := Cell) T

abbrev SectorSplit
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Sectors.SectorSplitStrong (Cell := Cell) T

end CNNA.PillarA.Sectors
