import CNNA.PillarA.Network.RegionNet
import CNNA.PillarA.Network.InfiniteCarrier
import CNNA.PillarA.Network.SectorChannels
import CNNA.PillarA.Network.RelativeEntropyFlow

set_option autoImplicit false

namespace CNNA.PillarA.Network

universe u

abbrev RegionNet
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Network.RegionNetStrong (Cell := Cell) T

abbrev InfiniteCarrier
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Network.InfiniteCarrierStrong (Cell := Cell) T

abbrev SectorChannels
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Network.SectorChannelsStrong (Cell := Cell) T

abbrev SectorSysEnv
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Network.SectorSysEnvStrong (Cell := Cell) T

abbrev RelativeEntropyFlow
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Network.RelativeEntropyFlowStrong (Cell := Cell) T


end CNNA.PillarA.Network
