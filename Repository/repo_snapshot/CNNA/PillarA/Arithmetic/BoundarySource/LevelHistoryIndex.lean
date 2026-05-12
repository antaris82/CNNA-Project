import CNNA.PillarA.Arithmetic.Core.Source

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

namespace BoundarySource

abbrev LevelHistoryIndex (L : Nat) := Fin (L + 1)

namespace LevelHistoryIndex

variable (L : Nat)

def equivFin : LevelHistoryIndex L ≃ Fin (L + 1) :=
  Equiv.refl (Fin (L + 1))

theorem equivFin_apply (k : LevelHistoryIndex L) :
    equivFin L k = k := by
  rfl

theorem equivFin_symm_apply (k : Fin (L + 1)) :
    (equivFin L).symm k = k := by
  rfl

end LevelHistoryIndex

end BoundarySource

namespace StrengtheningAR2bD

abbrev AR2bDLevelHistoryIndexOf (L : Nat) :=
  BoundarySource.LevelHistoryIndex L

def ar2bDLevelHistoryIndexEquivFin (L : Nat) :
    AR2bDLevelHistoryIndexOf L ≃ Fin (L + 1) :=
  BoundarySource.LevelHistoryIndex.equivFin L

theorem ar2bDLevelHistoryIndexEquivFin_apply
    (L : Nat) (k : AR2bDLevelHistoryIndexOf L) :
    ar2bDLevelHistoryIndexEquivFin L k = k := by
  rfl

end StrengtheningAR2bD

end CNNA.PillarA.Arithmetic
