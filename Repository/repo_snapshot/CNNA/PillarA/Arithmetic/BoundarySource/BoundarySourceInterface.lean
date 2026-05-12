import CNNA.PillarA.Arithmetic.BoundarySource.BoundarySourceTypeDecision

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

namespace BoundarySource

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}

structure BoundarySourceInterface
    (source : ArithmeticSource Cell T) (L : Nat) where
  index : Type
  indexEquiv : index ≃ LevelHistoryIndex L
  matrix : Matrix index index ExecComplex
  provenance : BoundarySourceProvenance source L
  route : BoundarySourceRoute
  route_eq_provenance : route = provenance.route
  matrix_eq_transport :
    matrix = transportLevelHistoryMatrix indexEquiv provenance.matrixPackage.matrix

namespace BoundarySourceInterface

variable {source : ArithmeticSource Cell T} {L : Nat}

def finIndexEquiv (B : BoundarySourceInterface source L) :
    B.index ≃ Fin (L + 1) :=
  B.indexEquiv.trans (LevelHistoryIndex.equivFin L)

theorem route_is_recursiveHistory
    (B : BoundarySourceInterface source L) :
    B.route = BoundarySourceRoute.recursiveHistory :=
  Eq.trans B.route_eq_provenance B.provenance.route_eq_recursiveHistory

theorem matrix_is_transport
    (B : BoundarySourceInterface source L) :
    B.matrix = transportLevelHistoryMatrix B.indexEquiv B.provenance.matrixPackage.matrix :=
  B.matrix_eq_transport

theorem provenance_decision_closed
    (B : BoundarySourceInterface source L) :
    B.provenance.signatureDecision.status =
      RecursiveTypeDecisionStatus.recursiveTypeDecisionClosed :=
  B.provenance.signatureDecision_closed

end BoundarySourceInterface

end BoundarySource

namespace StrengtheningAR2bD

abbrev AR2bDBoundarySourceInterfaceOf
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    (source : ArithmeticSource Cell T) (L : Nat) :=
  BoundarySource.BoundarySourceInterface (Cell := Cell) (T := T) source L

end StrengtheningAR2bD

end CNNA.PillarA.Arithmetic
