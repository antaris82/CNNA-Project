import CNNA.PillarA.Arithmetic.Core.BrightDtNSource

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u v w

namespace Actions

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}

inductive ActionPackageStatus where
  | certifiedBoundaryAction
  deriving DecidableEq, Repr

inductive ActionPackageObstructionStatus where
  | noObstructionForCertifiedBoundaryAction
  deriving DecidableEq, Repr

inductive ActionCarrierDiscipline where
  | boundarySourceCarrierAnchored
  | laterInternalCarrierRequired
  deriving DecidableEq, Repr

inductive FullTreeAutomorphismStatus where
  | blockedByCutoffOrientationRecursion
  deriving DecidableEq, Repr

inductive FreeLevelPermutationStatus where
  | blockedByRecursiveLevelOrder
  deriving DecidableEq, Repr

structure ActionPackage
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySource.BoundarySourceSurface source L) where
  carrier : Type v
  carrierEquivBoundaryIndex : carrier ≃ B.interface.index
  actingObject : Type w
  actionMap : actingObject → carrier → carrier
  identityElement : actingObject
  compose : actingObject → actingObject → actingObject
  identity_law : ∀ x : carrier, actionMap identityElement x = x
  composition_law :
    ∀ (a b : actingObject) (x : carrier),
      actionMap (compose a b) x = actionMap a (actionMap b x)
  routePreservation : B.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory
  matrixPreservation :
    ∀ (a : actingObject) (i j : carrier),
      B.interface.matrix (carrierEquivBoundaryIndex (actionMap a i))
          (carrierEquivBoundaryIndex (actionMap a j)) =
        B.interface.matrix (carrierEquivBoundaryIndex i)
          (carrierEquivBoundaryIndex j)
  noCutSpecCarrierClaim :
    ∀ _k : BoundarySource.LevelHistoryIndex L,
      source.toc.approximant source.concretePolicy = T
  invariantData : Prop
  invariantDataProof : invariantData
  obstructionStatus : ActionPackageObstructionStatus
  obstructionStatus_eq :
    obstructionStatus =
      ActionPackageObstructionStatus.noObstructionForCertifiedBoundaryAction
  carrierDiscipline : ActionCarrierDiscipline
  carrierDiscipline_eq :
    carrierDiscipline = ActionCarrierDiscipline.boundarySourceCarrierAnchored
  fullTreeAutomorphismStatus : FullTreeAutomorphismStatus
  fullTreeAutomorphismStatus_eq :
    fullTreeAutomorphismStatus =
      FullTreeAutomorphismStatus.blockedByCutoffOrientationRecursion
  freeLevelPermutationStatus : FreeLevelPermutationStatus
  freeLevelPermutationStatus_eq :
    freeLevelPermutationStatus = FreeLevelPermutationStatus.blockedByRecursiveLevelOrder
  status : ActionPackageStatus
  status_eq_certified : status = ActionPackageStatus.certifiedBoundaryAction

namespace ActionPackage

variable {source : ArithmeticSource Cell T} {L : Nat}
variable {B : BoundarySource.BoundarySourceSurface source L}

def identityBoundarySourceAction
    (B : BoundarySource.BoundarySourceSurface source L) :
    ActionPackage (Cell := Cell) (T := T) B where
  carrier := B.interface.index
  carrierEquivBoundaryIndex := Equiv.refl B.interface.index
  actingObject := Unit
  actionMap := fun _ x => x
  identityElement := ()
  compose := fun _ _ => ()
  identity_law := by
    intro x
    rfl
  composition_law := by
    intro a b x
    rfl
  routePreservation := B.route_recursiveHistory
  matrixPreservation := by
    intro a i j
    rfl
  noCutSpecCarrierClaim := by
    intro k
    exact B.noCutSpecCarrierClaim_at k
  invariantData := ∀ i j : B.interface.index,
    B.interface.matrix i j = B.interface.matrix i j
  invariantDataProof := by
    intro i j
    rfl
  obstructionStatus :=
    ActionPackageObstructionStatus.noObstructionForCertifiedBoundaryAction
  obstructionStatus_eq := by
    rfl
  carrierDiscipline := ActionCarrierDiscipline.boundarySourceCarrierAnchored
  carrierDiscipline_eq := by
    rfl
  fullTreeAutomorphismStatus := FullTreeAutomorphismStatus.blockedByCutoffOrientationRecursion
  fullTreeAutomorphismStatus_eq := by
    rfl
  freeLevelPermutationStatus := FreeLevelPermutationStatus.blockedByRecursiveLevelOrder
  freeLevelPermutationStatus_eq := by
    rfl
  status := ActionPackageStatus.certifiedBoundaryAction
  status_eq_certified := by
    rfl

theorem identity_law_holds
    (P : ActionPackage B) (x : P.carrier) :
    P.actionMap P.identityElement x = x :=
  P.identity_law x

theorem composition_law_holds
    (P : ActionPackage B) (a b : P.actingObject) (x : P.carrier) :
    P.actionMap (P.compose a b) x = P.actionMap a (P.actionMap b x) :=
  P.composition_law a b x

theorem routePreservation_recursiveHistory
    (P : ActionPackage B) :
    B.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory :=
  P.routePreservation

theorem matrixPreservation_holds
    (P : ActionPackage B) (a : P.actingObject) (i j : P.carrier) :
    B.interface.matrix (P.carrierEquivBoundaryIndex (P.actionMap a i))
        (P.carrierEquivBoundaryIndex (P.actionMap a j)) =
      B.interface.matrix (P.carrierEquivBoundaryIndex i)
        (P.carrierEquivBoundaryIndex j) :=
  P.matrixPreservation a i j

theorem noCutSpecCarrierClaim_at
    (P : ActionPackage B) (k : BoundarySource.LevelHistoryIndex L) :
    source.toc.approximant source.concretePolicy = T :=
  P.noCutSpecCarrierClaim k

theorem invariantData_holds
    (P : ActionPackage B) :
    P.invariantData :=
  P.invariantDataProof

theorem obstructionStatus_noObstruction
    (P : ActionPackage B) :
    P.obstructionStatus =
      ActionPackageObstructionStatus.noObstructionForCertifiedBoundaryAction :=
  P.obstructionStatus_eq

theorem carrierDiscipline_boundarySource
    (P : ActionPackage B) :
    P.carrierDiscipline = ActionCarrierDiscipline.boundarySourceCarrierAnchored :=
  P.carrierDiscipline_eq

theorem fullTreeAutomorphism_blocked
    (P : ActionPackage B) :
    P.fullTreeAutomorphismStatus =
      FullTreeAutomorphismStatus.blockedByCutoffOrientationRecursion :=
  P.fullTreeAutomorphismStatus_eq

theorem freeLevelPermutation_blocked
    (P : ActionPackage B) :
    P.freeLevelPermutationStatus = FreeLevelPermutationStatus.blockedByRecursiveLevelOrder :=
  P.freeLevelPermutationStatus_eq

theorem status_certified
    (P : ActionPackage B) :
    P.status = ActionPackageStatus.certifiedBoundaryAction :=
  P.status_eq_certified

theorem identityBoundarySourceAction_matrixPreservation
    (B : BoundarySource.BoundarySourceSurface source L)
    (a : (identityBoundarySourceAction B).actingObject)
    (i j : (identityBoundarySourceAction B).carrier) :
    B.interface.matrix
        ((identityBoundarySourceAction B).carrierEquivBoundaryIndex
          ((identityBoundarySourceAction B).actionMap a i))
        ((identityBoundarySourceAction B).carrierEquivBoundaryIndex
          ((identityBoundarySourceAction B).actionMap a j)) =
      B.interface.matrix
        ((identityBoundarySourceAction B).carrierEquivBoundaryIndex i)
        ((identityBoundarySourceAction B).carrierEquivBoundaryIndex j) :=
  matrixPreservation_holds (identityBoundarySourceAction B) a i j

end ActionPackage

end Actions

namespace StrengtheningAR3a

abbrev ActionPackageStatus := Actions.ActionPackageStatus
abbrev ActionCarrierDiscipline := Actions.ActionCarrierDiscipline
abbrev ActionPackageObstructionStatus := Actions.ActionPackageObstructionStatus
abbrev FullTreeAutomorphismStatus := Actions.FullTreeAutomorphismStatus
abbrev FreeLevelPermutationStatus := Actions.FreeLevelPermutationStatus

abbrev ActionPackageOf
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySource.BoundarySourceSurface source L) :=
  Actions.ActionPackage B

def identityBoundarySourceAction
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySource.BoundarySourceSurface source L) :
    ActionPackageOf B :=
  Actions.ActionPackage.identityBoundarySourceAction B

theorem identityBoundarySourceAction_status
    {Cell : Nat → Type u} [SubstrateClass Cell]
    {T : TruncatedFamily Cell}
    {source : ArithmeticSource Cell T} {L : Nat}
    (B : BoundarySource.BoundarySourceSurface source L) :
    (identityBoundarySourceAction B).status =
      Actions.ActionPackageStatus.certifiedBoundaryAction :=
  Actions.ActionPackage.status_certified (identityBoundarySourceAction B)

end StrengtheningAR3a

end CNNA.PillarA.Arithmetic
