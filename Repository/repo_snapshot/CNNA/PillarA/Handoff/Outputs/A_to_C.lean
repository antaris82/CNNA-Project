import CNNA.PillarA.Handoff.Core.SectorExport

set_option autoImplicit false

namespace CNNA.PillarA.Handoff

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

abbrev AToCHandoffStrong
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  SectorExportStrong (Cell := Cell) T

namespace AToCHandoffStrong

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}

abbrev ofSectorExport (X : SectorExportStrong Cell T) : AToCHandoffStrong Cell T :=
  X

abbrev exportData (X : AToCHandoffStrong Cell T) : SectorExportStrong Cell T :=
  X

end AToCHandoffStrong

end CNNA.PillarA.Handoff
