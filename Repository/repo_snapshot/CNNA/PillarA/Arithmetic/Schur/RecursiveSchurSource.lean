import CNNA.PillarA.Arithmetic.Schur.MobiusTransfer

set_option autoImplicit false

namespace CNNA.PillarA.Arithmetic

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC

universe u

namespace Schur

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T : TruncatedFamily Cell}
variable {source : ArithmeticSource Cell T} {L : Nat}

structure SchurFraction where
  numerator : ExecComplex
  denominator : ExecComplex
  sigma : ExecComplex
  denominator_mul_sigma_eq_numerator : denominator * sigma = numerator

namespace SchurFraction

def fromBoundaryDiagonal
    (B : BoundarySource.BoundarySourceSurface source L)
    (k : BoundarySource.LevelHistoryIndex L) : SchurFraction where
  numerator := boundaryMatrixAt B k k
  denominator := 1
  sigma := boundaryMatrixAt B k k
  denominator_mul_sigma_eq_numerator := by
    exact one_mul (boundaryMatrixAt B k k)

theorem numerator_eq_boundaryDiagonal
    (B : BoundarySource.BoundarySourceSurface source L)
    (k : BoundarySource.LevelHistoryIndex L) :
    (fromBoundaryDiagonal B k).numerator = boundaryMatrixAt B k k := by
  rfl

theorem denominator_eq_one
    (B : BoundarySource.BoundarySourceSurface source L)
    (k : BoundarySource.LevelHistoryIndex L) :
    (fromBoundaryDiagonal B k).denominator = 1 := by
  rfl

theorem sigma_eq_boundaryDiagonal
    (B : BoundarySource.BoundarySourceSurface source L)
    (k : BoundarySource.LevelHistoryIndex L) :
    (fromBoundaryDiagonal B k).sigma = boundaryMatrixAt B k k := by
  rfl

theorem quotient_relation
    (F : SchurFraction) :
    F.denominator * F.sigma = F.numerator :=
  F.denominator_mul_sigma_eq_numerator

end SchurFraction

structure RecursiveSchurSource
    (source : ArithmeticSource Cell T) (L : Nat) where
  boundarySource : BoundarySource.BoundarySourceSurface source L
  transferParameters : MobiusTransferParameters boundarySource
  numerator : BoundarySource.LevelHistoryIndex L → ExecComplex
  denominator : BoundarySource.LevelHistoryIndex L → ExecComplex
  sigma : BoundarySource.LevelHistoryIndex L → ExecComplex
  fraction : BoundarySource.LevelHistoryIndex L → SchurFraction
  fraction_eq_boundaryDiagonal :
    ∀ k, fraction k = SchurFraction.fromBoundaryDiagonal boundarySource k
  numerator_eq_fraction : ∀ k, numerator k = (fraction k).numerator
  denominator_eq_fraction : ∀ k, denominator k = (fraction k).denominator
  sigma_eq_fraction : ∀ k, sigma k = (fraction k).sigma
  numerator_eq_boundaryDiagonal :
    ∀ k, numerator k = boundaryMatrixAt boundarySource k k
  denominator_eq_one : ∀ k, denominator k = 1
  sigma_eq_boundaryDiagonal :
    ∀ k, sigma k = boundaryMatrixAt boundarySource k k
  denominator_mul_sigma_eq_numerator :
    ∀ k, denominator k * sigma k = numerator k
  route : boundarySource.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory
  consumptionPolicy :
    boundarySource.consumptionPolicy =
      BoundarySource.BoundarySourceConsumptionPolicy.boundarySourceOnly
  actionDataStatus :
    transferParameters.actionDataStatus =
      MobiusActionDataStatus.preservationAndFormatOnlyNoNumericData
  noCutSpecCarrierClaim :
    ∀ _k : BoundarySource.LevelHistoryIndex L,
      source.toc.approximant source.concretePolicy = T

namespace RecursiveSchurSource

def fromBoundarySource
    (B : BoundarySource.BoundarySourceSurface source L) :
    RecursiveSchurSource source L where
  boundarySource := B
  transferParameters := MobiusTransferParameters.fromBoundarySource B
  numerator := fun k => boundaryMatrixAt B k k
  denominator := fun _k => 1
  sigma := fun k => boundaryMatrixAt B k k
  fraction := fun k => SchurFraction.fromBoundaryDiagonal B k
  fraction_eq_boundaryDiagonal := by
    intro k
    rfl
  numerator_eq_fraction := by
    intro k
    rfl
  denominator_eq_fraction := by
    intro k
    rfl
  sigma_eq_fraction := by
    intro k
    rfl
  numerator_eq_boundaryDiagonal := by
    intro k
    rfl
  denominator_eq_one := by
    intro k
    rfl
  sigma_eq_boundaryDiagonal := by
    intro k
    rfl
  denominator_mul_sigma_eq_numerator := by
    intro k
    exact one_mul (boundaryMatrixAt B k k)
  route := B.route_recursiveHistory
  consumptionPolicy := B.consumptionPolicy_is_interfaceOnly
  actionDataStatus := by
    rfl
  noCutSpecCarrierClaim := by
    intro k
    exact B.noCutSpecCarrierClaim_at k

theorem fraction_is_boundaryDiagonal
    (R : RecursiveSchurSource source L)
    (k : BoundarySource.LevelHistoryIndex L) :
    R.fraction k = SchurFraction.fromBoundaryDiagonal R.boundarySource k :=
  R.fraction_eq_boundaryDiagonal k

theorem numerator_from_boundary
    (R : RecursiveSchurSource source L)
    (k : BoundarySource.LevelHistoryIndex L) :
    R.numerator k = boundaryMatrixAt R.boundarySource k k :=
  R.numerator_eq_boundaryDiagonal k

theorem denominator_from_unit
    (R : RecursiveSchurSource source L)
    (k : BoundarySource.LevelHistoryIndex L) :
    R.denominator k = 1 :=
  R.denominator_eq_one k

theorem sigma_from_boundary
    (R : RecursiveSchurSource source L)
    (k : BoundarySource.LevelHistoryIndex L) :
    R.sigma k = boundaryMatrixAt R.boundarySource k k :=
  R.sigma_eq_boundaryDiagonal k

theorem quotient_relation
    (R : RecursiveSchurSource source L)
    (k : BoundarySource.LevelHistoryIndex L) :
    R.denominator k * R.sigma k = R.numerator k :=
  R.denominator_mul_sigma_eq_numerator k

theorem route_recursiveHistory
    (R : RecursiveSchurSource source L) :
    R.boundarySource.interface.route = BoundarySource.BoundarySourceRoute.recursiveHistory :=
  R.route

theorem actionDataStatus_noNumericData
    (R : RecursiveSchurSource source L) :
    R.transferParameters.actionDataStatus =
      MobiusActionDataStatus.preservationAndFormatOnlyNoNumericData :=
  R.actionDataStatus

theorem noCutSpecCarrierClaim_at
    (R : RecursiveSchurSource source L)
    (k : BoundarySource.LevelHistoryIndex L) :
    source.toc.approximant source.concretePolicy = T :=
  R.noCutSpecCarrierClaim k

end RecursiveSchurSource

end Schur

end CNNA.PillarA.Arithmetic
