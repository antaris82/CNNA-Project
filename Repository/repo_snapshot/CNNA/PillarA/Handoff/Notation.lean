import CNNA.PillarA.Handoff.Core.BuildAll
import CNNA.PillarA.Handoff.Outputs.BuildAll
import CNNA.PillarA.Handoff.Inputs.BuildAll
import CNNA.PillarA.Handoff.ProofObligationI.BuildAll
import CNNA.PillarA.Handoff.ProofObligationII.BuildAll
import CNNA.PillarA.Handoff.ProofObligationIII.BuildAll

set_option autoImplicit false

namespace CNNA.PillarA.Handoff

universe u v

abbrev SectorExport
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Handoff.SectorExportStrong (Cell := Cell) T

abbrev Step1MathData
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Handoff.Step1MathDataStrong (Cell := Cell) T

abbrev AToCHandoff
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Handoff.AToCHandoffStrong (Cell := Cell) T

abbrev AToDHandoff
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Handoff.AToDHandoffStrong (Cell := Cell) T

abbrev AToEHandoff
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Handoff.AToEHandoffStrong (Cell := Cell) T

abbrev AToCayleyDicksonHandoff
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell) :=
  CNNA.PillarA.Handoff.AToCayleyDicksonHandoffStrong (Cell := Cell) T

abbrev BToAFeedback
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell)
    (Feedback : Type v) :=
  CNNA.PillarA.Handoff.BToAInput (Cell := Cell) T Feedback

abbrev CToAFeedback
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell)
    (Feedback : Type v) :=
  CNNA.PillarA.Handoff.CToAInput (Cell := Cell) T Feedback

abbrev DToAFeedback
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell)
    (Feedback : Type v) :=
  CNNA.PillarA.Handoff.DToAInput (Cell := Cell) T Feedback

abbrev EToAFeedback
    (Cell : Nat → Type u) [CNNA.PillarA.Foundation.SubstrateClass Cell]
    (T : CNNA.PillarA.ToC.TruncatedFamily Cell)
    (Feedback : Type v) :=
  CNNA.PillarA.Handoff.EToAInput (Cell := Cell) T Feedback

end CNNA.PillarA.Handoff
