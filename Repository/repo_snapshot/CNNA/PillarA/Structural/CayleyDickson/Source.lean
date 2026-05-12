import CNNA.PillarA.Network.InfiniteCarrier
import CNNA.PillarA.Closure.RegularizationClosure
import CNNA.PillarA.Coupling.MultiSchur

set_option autoImplicit false

namespace CNNA.PillarA.Structural.CayleyDickson

open CNNA.PillarA.Foundation
open CNNA.PillarA.ToC
open CNNA.PillarA.Finite
open CNNA.PillarA.DtN
open CNNA.PillarA.Sectors
open CNNA.PillarA.Closure
open CNNA.PillarA.Network
open CNNA.PillarA.Coupling

universe u

structure CayleyDicksonSource (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) where
  carrier : InfiniteCarrierStrong Cell T
  regularization : RegularizationClosureStrong Cell T
  schur : MultiSchurStrong Cell T
  regularization_split : regularization.split = carrier.split
  schur_split : schur.split = carrier.split

abbrev CayleyDicksonSourceOf
    (Cell : Nat → Type u) [SubstrateClass Cell]
    (T : TruncatedFamily Cell) :=
  CayleyDicksonSource (Cell := Cell) T

namespace CayleyDicksonSource

variable {Cell : Nat → Type u} [SubstrateClass Cell]
variable {T U : TruncatedFamily Cell}

@[ext] theorem ext (X Y : CayleyDicksonSource Cell T)
    (hcarrier : X.carrier = Y.carrier)
    (hregularization : X.regularization = Y.regularization)
    (hschur : X.schur = Y.schur) :
    X = Y := by
  cases X with
  | mk carrierX regularizationX schurX regularization_splitX schur_splitX =>
    cases Y with
    | mk carrierY regularizationY schurY regularization_splitY schur_splitY =>
      cases hcarrier
      cases hregularization
      cases hschur
      have hreg : regularization_splitX = regularization_splitY := Subsingleton.elim _ _
      cases hreg
      have hschur' : schur_splitX = schur_splitY := Subsingleton.elim _ _
      cases hschur'
      rfl

def cast (h : T = U) (X : CayleyDicksonSource Cell T) :
    CayleyDicksonSource Cell U := by
  cases h
  exact X

theorem cast_rfl (X : CayleyDicksonSource Cell T) :
    cast (Cell := Cell) rfl X = X := by
  rfl

def ofClosedStrands
    (I : InfiniteCarrierStrong Cell T)
    (R : RegularizationClosureStrong Cell T)
    (M : MultiSchurStrong Cell T)
    (hR : R.split = I.split)
    (hM : M.split = I.split) :
    CayleyDicksonSource Cell T where
  carrier := I
  regularization := R
  schur := M
  regularization_split := hR
  schur_split := hM

theorem ofClosedStrands_carrier
    (I : InfiniteCarrierStrong Cell T)
    (R : RegularizationClosureStrong Cell T)
    (M : MultiSchurStrong Cell T)
    (hR : R.split = I.split)
    (hM : M.split = I.split) :
    (ofClosedStrands I R M hR hM).carrier = I := by
  rfl

theorem ofClosedStrands_regularization
    (I : InfiniteCarrierStrong Cell T)
    (R : RegularizationClosureStrong Cell T)
    (M : MultiSchurStrong Cell T)
    (hR : R.split = I.split)
    (hM : M.split = I.split) :
    (ofClosedStrands I R M hR hM).regularization = R := by
  rfl

theorem ofClosedStrands_schur
    (I : InfiniteCarrierStrong Cell T)
    (R : RegularizationClosureStrong Cell T)
    (M : MultiSchurStrong Cell T)
    (hR : R.split = I.split)
    (hM : M.split = I.split) :
    (ofClosedStrands I R M hR hM).schur = M := by
  rfl

def regionNet (X : CayleyDicksonSource Cell T) : RegionNetStrong Cell T :=
  X.carrier.regionNet

def split (X : CayleyDicksonSource Cell T) : SectorSplitStrong Cell T :=
  X.carrier.split

def approximant (X : CayleyDicksonSource Cell T) : ApproximantStrong Cell T :=
  X.carrier.approximant

def ideal (X : CayleyDicksonSource Cell T) : DirectedFamily (Cell := Cell) :=
  X.carrier.ideal

def cutoff (_ : CayleyDicksonSource Cell T) : Nat :=
  T.cutoff

def stableCarrier (X : CayleyDicksonSource Cell T) (L : Nat) : Finset (Cell L) :=
  X.carrier.stableCarrier L

def idealCarrier (X : CayleyDicksonSource Cell T) (L : Nat) : Finset (Cell L) :=
  X.carrier.idealCarrier L

theorem carrier_eq_self_carrier (X : CayleyDicksonSource Cell T) :
    X.carrier = X.carrier := by
  rfl

theorem regularization_split_eq_split (X : CayleyDicksonSource Cell T) :
    X.regularization.split = X.split := by
  exact X.regularization_split

theorem schur_split_eq_split (X : CayleyDicksonSource Cell T) :
    X.schur.split = X.split := by
  exact X.schur_split

theorem stable_eq_truncate (X : CayleyDicksonSource Cell T) :
    T = X.ideal.truncate X.cutoff := by
  exact X.carrier.stable_eq_truncate

theorem topSlice_carrier_eq_ideal (X : CayleyDicksonSource Cell T) :
    T.topSlice.carrier = X.idealCarrier X.cutoff := by
  exact X.carrier.topSlice_carrier_eq_ideal

theorem stableCarrier_eq_ideal_of_le
    (X : CayleyDicksonSource Cell T) {L : Nat} (hL : L ≤ X.cutoff) :
    X.stableCarrier L = X.idealCarrier L := by
  exact X.carrier.stableCarrier_eq_ideal_of_le hL

theorem stableCarrier_eq_empty_of_gt
    (X : CayleyDicksonSource Cell T) {L : Nat} (hL : X.cutoff < L) :
    X.stableCarrier L = ∅ := by
  exact X.carrier.stableCarrier_eq_empty_of_gt hL

end CayleyDicksonSource

end CNNA.PillarA.Structural.CayleyDickson
