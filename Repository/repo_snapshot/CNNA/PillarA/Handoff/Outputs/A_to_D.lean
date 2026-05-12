import CNNA.PillarA.Handoff.Core.SectorExport

set_option autoImplicit false

namespace CNNA.PillarA.Handoff

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

abbrev AToDHandoffStrong
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  SectorExportStrong (Cell := Cell) T

namespace AToDHandoffStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}

abbrev ofSectorExport (X : SectorExportStrong Cell T) : AToDHandoffStrong Cell T :=
  X

abbrev exportData (X : AToDHandoffStrong Cell T) : SectorExportStrong Cell T :=
  X

end AToDHandoffStrong

end CNNA.PillarA.Handoff
